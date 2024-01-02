------------------------------------------------------------------------------
-- Copyright 2023, Tim Whiting, Fredrik Wieczerkowski
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- The LSP handler that provides hover tooltips
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module LanguageServer.Handler.Hover (hoverHandler, formatRangeInfoHover) where

import Control.Lens ((^.))
import Control.Monad.Cont (liftIO)
import Data.Foldable(maximumBy)
import qualified Data.Text as T
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import qualified Language.LSP.Protocol.Message as J
import Language.LSP.Server (Handlers, sendNotification, requestHandler)

import Common.Range as R
import Common.Name (nameNil)
import Common.ColorScheme (ColorScheme (colorNameQual, colorSource), Color (Gray))
import Lib.PPrint (Pretty (..), Doc, string, (<+>), (<-->),color, Color (..), (<.>), (<->), text, empty, vcat)
import Compiler.Module (loadedModule, modRangeMap, modLexemes, Loaded (loadedModules, loadedImportMap), Module (modPath, modSourcePath))
import Compiler.Options (Flags, colorSchemeFromFlags, prettyEnvFromFlags)
import Compiler.Compile (modName)
import Kind.Pretty (prettyKind)
import Kind.ImportMap (importsEmpty, ImportMap)
import Type.Pretty (ppScheme, defaultEnv, Env(..), ppName)
import Type.Type (Name)
import Syntax.RangeMap (NameInfo (..), RangeInfo (..), rangeMapFindAt)
import LanguageServer.Conversions (fromLspPos, toLspRange)
import LanguageServer.Monad (LSM, getLoaded, getLoadedModule, getHtmlPrinter, getFlags)
import Debug.Trace (trace)
import Lib.PPrint (makeMarkdown, displayS, renderCompact)
import Lib.PPrint (stringStripComments)

-- Handles hover requests
hoverHandler :: Handlers LSM
hoverHandler = requestHandler J.SMethod_TextDocumentHover $ \req responder -> do
  let J.HoverParams doc pos _ = req ^. J.params
      uri = doc ^. J.uri
      normUri = J.toNormalizedUri uri
  loadedMod <- getLoadedModule normUri
  loaded <- getLoaded normUri
  pos <- liftIO $ fromLspPos normUri pos
  let res = do -- maybe monad
        mod  <- loadedMod
        l    <- loaded
        rmap <- modRangeMap mod
        -- Find the range info at the given position
        {- let rm = rangeMapFindAt (modLexemes mod) pos rmap
        (r, rinfo) <- rangeMapBestHover rm
        -}
        (r,rinfo) <- -- trace ("hover lookup in rangemap") $
                     rangeMapFindAt (modLexemes mod) pos rmap
        return (modName mod, loadedImportMap l, r, rinfo)
  case res of
    Just (mName, imports, r, rinfo)
      -> -- trace ("hover found " ++ show rinfo) $
         do -- Get the html-printer and flags
            print <- getHtmlPrinter
            flags <- getFlags
            let env = (prettyEnvFromFlags flags){ context = mName, importsMap = imports }
                colors = colorSchemeFromFlags flags
            markdown <- liftIO $ print $ -- makeMarkdown $
                        (formatRangeInfoHover loaded env colors rinfo)
            let md = J.mkMarkdown markdown
                hc = J.InL md
                rsp = J.Hover hc $ Just $ toLspRange r
            -- trace ("hover: " ++ show markdown) $
            responder $ Right $ J.InL rsp
    Nothing
      -> -- trace "no hover info" $
         responder $ Right $ J.InR J.Null



-- Get best rangemap info for a given position
rangeMapBestHover rm =
  case rm of
    [] -> Nothing
    [r] -> Just r
    r:rst -> Just r

-- Pretty-prints type/kind information to a hover tooltip given a type pretty environment, color scheme
formatRangeInfoHover :: (Maybe Loaded) -> Env -> ColorScheme -> RangeInfo -> Doc
formatRangeInfoHover mbLoaded env colors rinfo =
  case rinfo of
  Id qname info docs isdef ->
    let signature = ppName env qname <+> text ":"
                    <+> case info of
                      NIValue tp "" _ -> ppScheme env tp
                      NIValue tp doc _ -> ppScheme env tp
                      NICon tp "" ->  ppScheme env tp
                      NICon tp doc ->  ppScheme env tp
                      NITypeCon k -> prettyKind colors k
                      NITypeVar k -> prettyKind colors k
                      NIModule -> text "module" <.>
                                  (case mbLoaded of
                                    Just loaded -> case filter (\mod -> modName mod == qname) (loadedModules loaded) of
                                                      [mod] | not (null (modSourcePath mod)) -> text (" (" ++ modSourcePath mod ++ ")")
                                                      _     -> empty
                                    _ -> empty)
                      NIKind -> text "kind"
        comment = case info of
                    NIValue tp ""  _ -> empty
                    NIValue tp doc _ -> hline <.> stringStripComments doc
                    NICon tp ""      -> empty
                    NICon tp doc     -> hline <.> stringStripComments doc
                    _                -> empty
    in asKokaCode (if null docs then signature else (signature <.> text "  " <-> color Gray (vcat docs)))
       <.> comment

  Decl s name mname -> text s <+> text " " <+> pretty name
  Block s -> text s
  Error doc -> text "Error: " <+> doc
  Warning doc -> text "Warning: " <+> doc
  Implicits implicits -> text "Implicits: " <+> text (show implicits)

asKokaCode :: Doc -> Doc
asKokaCode doc = text ("```koka\n" ++ displayS (renderCompact doc) "" ++ "\n```")

hline = text "\n* * *\n"