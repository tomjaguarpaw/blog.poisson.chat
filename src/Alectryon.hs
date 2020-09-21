{-# LANGUAGE OverloadedStrings #-}
module Alectryon where

import Control.Monad.State (State, runState, get, put)
import qualified Data.Aeson as Aeson
import Data.Text (Text)
import qualified Data.Text.IO as Text (readFile)
import qualified Data.Text as Text
import System.Process (callProcess)

import Text.Pandoc
  ( Block(CodeBlock, RawBlock), Pandoc(..), MetaValue(MetaBool),
    lookupMeta, runIOorExplode )
import Text.Pandoc.Walk (query, walkM)
import Hakyll
import Hakyll.Core.File (TmpFile(..), newTmpFile)

import Debug.Trace

-- | Do nothing if "alectryon" flag is not set
tryAlectryon :: Item Pandoc -> Compiler (Item Pandoc)
tryAlectryon idoc = do
  m <- getMetadataField (itemIdentifier idoc) "alectryon"
  case m of
    Just "true" -> withItemBody alectryon' idoc
    Just "false" -> pure idoc
    Nothing -> pure idoc
    Just _ -> error "Field 'alectryon' must be 'true' or 'false'" 

alectryon' :: Pandoc -> Compiler Pandoc
alectryon' doc = do
    snips <- runAlectryon blocks
    pure (updateBlocks snips doc)
  where
    blocks = query getCoqBlock doc
    getCoqBlock = onAlectryonBlocks [] (: [])

nextBlock :: State [Text] Block
nextBlock = do
  xs <- get
  case xs of
    [] -> error "No blocks left"
    x : xs -> do
      put xs
      pure (RawBlock "html" x)

updateBlocks :: [Text] -> Pandoc -> Pandoc
updateBlocks bs = fst . flip runState bs . walkM setCoqBlock
  where
    setCoqBlock b = onAlectryonBlocks (pure b) (\_ -> nextBlock) b

onCoqBlocks :: b -> (Text -> b) -> Block -> b
onCoqBlocks = onBlocks "coq"

onAlectryonBlocks :: b -> (Text -> b) -> Block -> b
onAlectryonBlocks = onBlocks "alectryon"

onBlocks :: Text -> b -> (Text -> b) -> Block -> b
onBlocks name _ f (CodeBlock (_, cs, _) b) | name `elem` cs = f b
onBlocks _ x _ _ = x

splitAlectryonHTML :: Text -> [Text]
splitAlectryonHTML = Text.splitOn "<!-- alectryon-block-end -->"

runAlectryon :: [Text] -> Compiler [Text]
runAlectryon blocks = do
  TmpFile json <- newTmpFile "snippets.json"
  TmpFile snippets <- newTmpFile "snippets.html"
  Hakyll.unsafeCompiler $ do
    Aeson.encodeFile json blocks
    callProcess "alectryon" ["--backend", "snippets-html", json, "-o", snippets]
    splitAlectryonHTML <$> Text.readFile snippets
