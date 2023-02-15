--[[---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen, Ondřej Kvapil.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------]]

--var $std_core_hnd._evv_ofs = 0;
--var _evv     = [];
--var _yield   = null; -- { marker: 0, clause: null, conts: [], conts_count: 0, final: bool };

marker_unique = 1;  -- must be > 0

local function _assert(cond,msg)
  if not cond then console.error(msg) end
end

-- for internal references
local _std_core_hnd
local _evv = {}
local _yield = nil

local function _evv_get()
  return _evv
end

local function _evv_at(i)
  return _evv[i]
end

local function _evv_set(evv)
  _evv = evv
end

local function _evv_swap(evv)
  evv0 = _evv
  _evv = evv
  return evv0
end


local _evv_empty = {}

local function _evv_swap_create0()
  local evv = _evv
  if #evv ~= 0 then
    _evv = _evv_empty
  end
  return evv
end

local function _evv_swap_create1(i)
  local evv = _evv
  if #evv ~= 1 then
    local ev = evv[i]
    _evv = {ev}
    _evv._cfc = ev.cfc
  end
  return evv
end

local function _yielding()
  return _yield ~= nil
end

local function _yielding_non_final()
  return _yield ~= nil and not _yield.final
end


----------------------------------------------------
-- evidence: { evv: [forall h. ev<h>], ofs : int }
----------------------------------------------------

local function ev_none()
  return Ev(nil,0,nil,-1,{})
end

local function _cfc_lub(x,y)
  assert(x~=nil and y~=nil, "invalid argument")
  if x < 0 then return y end
  if x + y == 1 then return 2 end
  if x > y then return x end
  return y
end

local function _evv_get_cfc(evv)
  local cfc = evv._cfc
  return (cfc==nil and -1 or cfc)
end

local function _evv_cfc()
  return _evv_get_cfc(_evv)
end


local function _evv_insert(evv,ev)
  -- update ev
  if ev.marker==0 then return end -- marker zero is ev-none
  ev.hevv = evv
  local cfc = _cfc_lub(_evv_get_cfc(evv), ev.cfc)
  if ev.marker < 0 then -- negative marker is used for named evidence; this means this evidence should not be inserted into the evidence vector
    evv._cfc = cfc -- control flow context
    return -- a negative (named) marker is not in the evidence vector
  end
  -- insert in the vector
  local n    = #evv
  local evv2 = {}
  evv2._cfc = cfc
  ev.cfc = cfc -- update in-place
  local i
  for i = 1, n do
    local ev2 = evv[i]
    if ev.htag <= ev2.htag then break end
    evv2[i] = ev2
  end
  evv2[i] = ev
  for i = i, n do
    evv2[i+1] = evv[i]
  end
  return evv2
end

local function _evv_delete(evv, i, behind)
   -- delete from the vector
   if behind then i = i + 1 end
   local n = #evv
   local evv2 = {}
   if evv._cfc ~= nil then evv2._cfc = evv._cfc end
   if n == 1 then return evv2 end -- empty
   -- copy without i
   for j = 1, i do
      evv2[j] = evv[j]
   end
   for j = i + 1, n - 1 do
      evv2[j] = evv[j + 1]
   end
   -- update cfc?
   if evv[i].cfc >= _evv_get_cfc(evv) then
      local cfc = evv2[1].cfc
      for j = 2, n - 1 do
         cfc = _cfc_lub(evv2[j].cfc, cfc)
      end
      evv2._cfc = cfc
   end
   return evv2
end

local function _evv_swap_delete(i, behind)
  local w0 = _evv
  _evv = _evv_delete(w0, i, behind)
  return w0
end

local function __evv_lookup(tag)
  local evv = _evv
  for i = 0, #evv, 1 do
    if tag == evv[i].htag then return evv[i] end
  end
  console.error("cannot find " + tag + " in " + _evv_show(evv));
  return nil
end

-- Find insertion/deletion point for an effect label
local function __evv_index(tag)
  local evv = _evv
  local n = #evv
  for i = 1, n do
    if tag <= evv[i].htag then return i end  -- string compare
  end
  return n
end

local function _evv_show(evv)
  table.sort(evv, function(ev1,ev2) return ev1.marker < ev2.marker end)
  local out = ""
  for i = 1, #evv do
    local evvi = evv[i].hevv
    out = out .. ((i==1 and "{ " or "  ") .. evv[i].htag:pad(8," ") .. ": marker " .. evv[i].marker .. ", under <" ..
             table.concat(evvi, ",") .. ">" .. (i==#evv and "}" or "") .. "\n")
  end
  return out
end

local function _yield_show()
  if _yielding() then
    return "yielding to " + _yield.marker + ", final: " + _yield.final;
  else
    return "pure"
  end
end


local function _evv_expect(m,expected)
  if ((_yield == nil or _yield.marker == m) and (_evv ~= expected.evv)) then
    error("expected evidence: \n" + _evv_show(expected) + "\nbut found:\n" + _evv_show(_evv))
  end
end

local function _guard(evv)
  if _evv ~= evv then
    if #_evv == #evv then
      local equal = true
      for i = 0, #evv do
        if _evv[i].marker ~= evv[i].marker then
          equal = false
          break
        end
      end
      if equal then return end
    end
    print("trying to resume outside the (handler) scope of the original handler. \n captured under:\n" + _evv_show(evv) + "\n but resumed under:\n" + _evv_show(_evv))
    error "trying to resume outside the (handler) scope of the original handler"
  end
end

local function _throw_resume_final(f)
  error("trying to resume an unresumable resumption (from finalization)");
end


local function _evv_create( evv, indices )
  local n = #(indices)
  local evv2 = {}
  if evv._cfc ~= nil then evv2._cfc = evv._cfc end
  for i = 1, n do
    evv2[i] = evv[indices[i]]
  end
  return evv2
end

local function _evv_swap_create(indices)
  local evv = _evv
  _evv = _evv_create(evv,indices)
  return evv
end



----------------------------------------------------
-- Yielding
----------------------------------------------------

local function _kcompose(to, conts)
  return function(x)
    local acc = x
    local i = 0
    while i < to do
      acc = conts[i + 1](acc)
      if _yielding() then
        --return ((function(i){ return _yield_extend(_kcompose(i+1,to,conts)); })(i));
        i = i + 1
        while i < to do
          _yield_extend(conts[i + 1])
          i = i + 1
        end
        return -- undefined
      end
    end
    return acc
  end
end

local function yield_extend(next)
  assert(_yielding(), "yield extension while not yielding!")
  if _yield.final then return end
  -- index is ~80% faster as push (that's js, idk about lua)
  _yield.conts_count = _yield.conts_count + 1
  _yield.conts[_yield.conts_count] = next
end

local function _yield_cont(f)
  _assert(_yielding(), "yield extension while not yielding!")
  if _yield.final then return end
  local cont = _kcompose(_yield.conts_count, _yield.conts)
  _yield.conts = {}
  _yield.conts_count = 1
  _yield.conts[1] = function(x) return f(cont, x) end
end

local function _yield_prompt(m)
  if _yield == nil then
    return Pure
  elseif _yield.marker ~= m then
    return _yield.final and YieldingFinal or Yielding
  else -- _yield.marker === m
    local cont   = _yield.final and _throw_resume_final or _kcompose(_yield.conts_count,_yield.conts)
    local clause = _yield.clause
    _yield = nil
    return Yield(clause,cont)
  end
end

local function _yield_final(m,clause)
  _assert(not _yielding(),"yielding final while yielding!")
  _yield = { marker = m, clause = clause, conts = nil, conts_count = 0, final = true }
end

local function _yield_to(m,clause)
  _assert(not _yielding(),"yielding while yielding!")
  _yield = { marker = m, clause = clause, conts = {}, conts_count = 0, final = false }
end

local function _yield_capture()
  _assert(_yielding(),"can only capture a yield when yielding!")
  local yld = _yield
  _yield = nil
  return yld
end

local function _reyield(yld)
  assert(not _yielding(), "can only reyield a yield when not yielding!");
  _yield = yld
end

_std_core_hnd = {
  _evv_get            = _evv_get,
  _evv_set            = _evv_set,
  _evv_at             = _evv_at,
  _evv_swap           = _evv_swap,
  _evv_swap_create0   = _evv_swap_create0,
  _evv_swap_create1   = _evv_swap_create1,
  _yielding           = _yielding,
  _yielding_non_final = _yielding_non_final,
  _evv_cfc            = _evv_cfc,
  _yield_to           = _yield_to,
  _yield_final        = _yield_final,
}
