{-# LANGUAGE
    BangPatterns,
    ImplicitParams,
    OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

import Data.Char (isAlpha)
import Data.Foldable (for_)
import Data.Functor (($>))
import Data.Monoid (Any(..), mappend)
import Data.Traversable (for)
import Data.Void (Void)

import Skylighting (addSyntaxDefinition, defaultSyntaxMap, parseSyntaxDefinition)
import Text.Pandoc (Block(CodeBlock), runIOorExplode)
import Text.Pandoc.Filter (Filter(..), applyFilters)
import Text.Pandoc.Shared (headerShift)
import Text.Pandoc.Options
  ( Extension(Ext_literate_haskell)
  , ReaderOptions(..)
  , WriterOptions(..)
  , disableExtension
  , enableExtension
  )
import Text.Pandoc.Walk (query)

import Text.Megaparsec (Parsec, parse, anySingle, single, takeWhileP, eof, errorBundlePretty, optional, (<|>))

import Hakyll hiding (defaultContext)
import qualified Hakyll

import qualified Hakyll.Alectryon as Alectryon

topics :: [(String, String)]
topics =
  [ ("haskell", "The Haskell language")
  , ("haskell-tricks", "Tricks in Haskell")
  , ("coq", "The Coq language")
  , ("libraries", "Libraries")
  , ("theory", "Of theoretical interest")
  , ("testing", "Testing")
  , ("bidirectional", "Bidirectional programming")
  , ("art", "Programming of art")
  , ("combinatorics", "Combinatorics")
  , ("blogging", "Blogging")
  , ("misc", "Unusual topics")
  ]

readerOpts :: ReaderOptions
readerOpts = defaultHakyllReaderOptions
  { readerExtensions = enableExtension Ext_literate_haskell $
      readerExtensions defaultHakyllReaderOptions
  }

-- Turns off Bird-style quote rendering
writerOpts :: WriterOptions
writerOpts = defaultHakyllWriterOptions
  { writerExtensions = disableExtension Ext_literate_haskell $
      writerExtensions defaultHakyllWriterOptions
  }

myFeedConfiguration :: FeedConfiguration
myFeedConfiguration = FeedConfiguration
    { feedTitle       = "Lysxia's blog"
    , feedDescription = "A blog about functional programming and stuff"
    , feedAuthorName  = "Lysxia"
    , feedAuthorEmail = "lysxia@gmail.com"
    , feedRoot        = "https://blog.poisson.chat"
    }

--------------------------------------------------------------------------------
main :: IO ()
main = do
  f <- parseSyntaxDefinition "data/haskell.xml"
  writerOpts <- case f of
    Left e -> fail e
    Right s -> return $ writerOpts
      { writerSyntaxMap = addSyntaxDefinition s defaultSyntaxMap
      }

  let ?readerOpts = readerOpts
  let ?writerOpts = writerOpts

  Alectryon.hakyll $ \opts -> do
    match "data/favicon.png" $ do
        route   (constRoute "favicon.png")
        compile copyFileCompiler

    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match (fromList ["about.rst", "contact.markdown"]) $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "404.html" $ do
        route idRoute
        compile copyFileCompiler

    match (fromRegex "^(drafts|posts)/" .&&. fromRegex ".(md|rst|lhs)$") $ do
        route $ setExtension "html"
        compile $ myPandocCompiler opts

    {-
    create ["archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let archiveCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    constField "title" "Archives"            `mappend`
                    defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls
    -}


    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateCompiler

    for_ topics $ \(topic, desc) -> do
      create [fromFilePath ("topic/" <> topic <> ".html")] $ do
        route idRoute
        compile $ do
          posts <- filterKeyword topic =<< recentFirst =<< loadAll "posts/*"
          let indexCtx
                =  constField "title" desc
                <> defaultContext
          let topicCtx
                = listField "posts" postCtx (return posts)
          iden <- getUnderlying
          Item _ topicTmpl <- load "templates/topic.html"
          applyTemplate topicTmpl topicCtx (Item iden topicTmpl)
              >>= loadAndApplyTemplate "templates/default.html" indexCtx
              >>= relativizeUrls

    match "topics.html" $ do
      route idRoute
      compile $ do
        let topicCtx
              =  field "topic" (pure . fst . itemBody)
              <> field "desc"  (pure . snd . itemBody)
        let indexCtx
              =  listField "topics" topicCtx (traverse makeItem topics)
              <> defaultContext

        getResourceBody
            >>= applyAsTemplate indexCtx
            >>= loadAndApplyTemplate "templates/default.html" indexCtx
            >>= relativizeUrls

    createFeed Rss
    createFeed Atom

data Feed = Atom | Rss

createFeed :: Feed -> Rules ()
createFeed feed =
  let (target, templatePath, itemTemplatePath, renderWithTemplates) = case feed of
        Atom -> ("atom.xml", "templates/atom.xml", "templates/atom-item.xml", renderAtomWithTemplates)
        Rss  -> ("rss.xml",  "templates/rss.xml",  "templates/rss-item.xml",  renderRssWithTemplates)
  in create [target] $ do
    route idRoute
    compile $ do
      posts <- fmap (take 10) . recentFirst =<< loadAllSnapshots "posts/*" bodySnapshot
      let feedCtx =
            postCtx `mappend`
            -- Add full body to RSS
            field "description" (\post -> return (itemBody post))
      rssTemplate <- loadBody templatePath
      rssItemTemplate <- loadBody itemTemplatePath
      renderWithTemplates rssTemplate rssItemTemplate
        myFeedConfiguration feedCtx posts

bodySnapshot :: Snapshot
bodySnapshot = "post-body"

--------------------------------------------------------------------------------

myPandocCompiler :: (?readerOpts :: ReaderOptions, ?writerOpts :: WriterOptions) => Alectryon.Options -> Compiler (Item String)
myPandocCompiler opts = do
  doc0 <- readPandocWith ?readerOpts =<< getResourceBody
  let doc = fmap (headerShift 1) doc0
  let hasCoq = getAny (query isCoqBlock doc)
  -- Save snapshot without alectryon processing
  _ <- saveSnapshot bodySnapshot (writePandocWith ?writerOpts doc)
  doc2 <- Alectryon.tryTransform opts doc
  pure (writePandocWith ?writerOpts doc2)
    >>= loadAndApplyTemplate "templates/post.html"    postCtx
    >>= loadAndApplyTemplate "templates/default.html" (boolField "coqstyle" (\_ -> hasCoq) `mappend` postCtx)
    >>= relativizeUrls
  where
    isCoqBlock b = Any (Alectryon.onCoqBlocks       False (\_ -> True) b
                     || Alectryon.onAlectryonBlocks False (\_ -> True) b)

postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

simplTitle :: String -> String
simplTitle s =
  case parse titleParser "" s of
    Left e -> error (errorBundlePretty e)
    Right t -> t

-- Drop tags (<a> and </a>)
titleParser :: Parsec Void String String
titleParser =
  (   single '<' *> optional (single '/') *> takeWhileP Nothing isAlpha *> single '>' $> id
  <|> (:) <$> anySingle
  ) <*> titleParser <|> eof $> []

defaultContext :: Context String
defaultContext =
  field "txt-title" (\i -> do
    d <- getMetadataField (itemIdentifier i) "title"
    case d of
      Just t -> pure (simplTitle t)
      Nothing -> pure "") `mappend`
  Hakyll.defaultContext

filterKeyword :: MonadMetadata m => String -> [Item a] -> m [Item a]
filterKeyword kw is = do
  fmap concat . for is $ \i -> do
    m <- getMetadata (itemIdentifier i)
    case lookupStringList "keywords" m of
      Just kws | kw `elem` kws -> pure [i]
      _ -> pure []
