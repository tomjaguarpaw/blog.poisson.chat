{-# LANGUAGE OverloadedStrings #-}

import Data.Foldable (for_)
import Data.Monoid (mappend)
import Data.Traversable (for)

import Skylighting (addSyntaxDefinition, defaultSyntaxMap, parseSyntaxDefinition)
import Text.Pandoc.Shared (headerShift)
import Text.Pandoc.Options
  ( Extension(Ext_literate_haskell)
  , ReaderOptions(..)
  , WriterOptions(..)
  , disableExtension
  , enableExtension
  )

import Hakyll

topics :: [(String, String)]
topics =
  [ ("haskell", "The Haskell language")
  , ("haskell-tricks", "Tricks in Haskell")
  , ("coq", "The Coq language")
  , ("libraries", "Libraries")
  , ("theory", "Of theoretical interest")
  , ("testing", "Testing")
  , ("bidirectional", "Bidirectional programming")
  , ("combinatorics", "Combinatorics")
  , ("blogging", "Blogging")
  , ("misc", "Unusual topics")
  ]

readerOpts = defaultHakyllReaderOptions
  { readerExtensions = enableExtension Ext_literate_haskell $
      readerExtensions defaultHakyllReaderOptions
  }

-- Turns off Bird-style quote rendering
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

  hakyll $ do
    match "data/favicon.ico" $ do
        route   (constRoute "favicon.ico")
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

    match (fromRegex "^(drafts|posts)/") $ do
        route $ setExtension "html"
        compile $ pandocCompilerWithTransform readerOpts writerOpts (headerShift 1)
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

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

    create ["rss.xml"] $ do
      route idRoute
      compile $ do
        let feedCtx =
              postCtx `mappend`
              field "description" (\post -> do
                desc <- getMetadataField (itemIdentifier post) "description"
                return $ case desc of
                  Just description -> description
                  Nothing -> "")
        posts <- fmap (take 10) . recentFirst =<< loadAll "posts/*"
        renderRss myFeedConfiguration feedCtx posts

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

filterKeyword :: MonadMetadata m => String -> [Item a] -> m [Item a]
filterKeyword kw is = do
  fmap concat . for is $ \i -> do
    m <- getMetadata (itemIdentifier i)
    case lookupStringList "keywords" m of
      Just kws | kw `elem` kws -> pure [i]
      _ -> pure []
