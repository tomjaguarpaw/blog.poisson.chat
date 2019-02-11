--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import Data.Monoid (mappend)

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
                    constField "title" "Home"                `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateCompiler

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

