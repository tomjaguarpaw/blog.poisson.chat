---
title: Typeclasses for bidirectional serialization, an example
keywords: [haskell, bidirectional]
---

This is written in Literate Haskell.

\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Bidirectional.Serialization.Example.Stream where

import Data.Char
import Data.Foldable
import Data.Maybe
import Prelude hiding (print)
import qualified Prelude

import Bidirectional.Serialization.Classes -- previous post
\end{code}

Elementary parsers and printers
===============================

Users are invited to specify elementary parsers and printers with custom
typeclasses so that more complex ones can be obtained using the general
purpose typeclasses in the previous post.

An example: character streams
-----------------------------

Here is a typeclass for reading and writing character streams,
one ``Char`` at a time.

\begin{code}
class Profunctor p => CharStream p where
  char :: p Char Char
\end{code}

The following (inefficient) ``Parser`` and ``Printer`` types are simple
examples of parsing and printing contexts.

\begin{code}
newtype Parser a = Parser { parse :: String -> Maybe (String, a) }
newtype Printer a = Printer { print :: (String, a) }

runParser :: Parser a -> String -> Maybe a
runParser p = fmap snd . parse p

runPrinter :: Printer a -> String
runPrinter = fst . print
\end{code}

They are instances of ``Monad``, and will be lifted through
the ``Parsing`` and ``Printing`` transformers.

\begin{code}
instance Functor Parser where
  fmap f (Parser p) = Parser ((fmap . fmap . fmap) f p)

instance Functor Printer where
  fmap f (Printer p) = Printer (fmap f p)

instance Applicative Parser where
  pure x = Parser (\s -> pure (s, x))
  Parser f_ <*> Parser x_ = Parser $ \s -> do
    (s', f) <- f_ s
    (s'', x) <- x_ s'
    return (s'', f x)

instance Applicative Printer where
  pure x = Printer ("", x)
  Printer (s, f) <*> Printer (s', x) = Printer (s ++ s', f x)

instance Monad Parser where
  Parser x_ >>= f = Parser $ \s -> do
    (s', x) <- x_ s
    parse (f x) s'

instance Monad Printer where
  Printer (s, x) >>= f = Printer (s ++ s', y)
    where
      Printer (s', y) = f x
\end{code}

We implement ``TokenStream`` for parsers and printers using the
``FlexibleInstances`` extension.

\begin{code}
parseChar :: Parser Char
parseChar = Parser parseChar'
  where
    parseChar' [] = Nothing
    parseChar' (c : s) = Just (s, c)

printChar :: Char -> Printer ()
printChar c = Printer ([c], ())

instance CharStream (Parsing Parser) where
  char = Parsing parseChar

instance CharStream (Printing Printer) where
  char = Printing (\c -> c <$ printChar c)
\end{code}

Parsing S-expressions
---------------------

With one-character atoms.

\begin{code}
data SE
  = Atom Char
  | List [SE]
  deriving (Eq, Show)
\end{code}

Bidirectional specification
+++++++++++++++++++++++++++

\begin{code}
se :: forall p. (CharStream p, Monad1 p) => p SE SE
se = case monad1 @p @SE of
  Dict ->
    lmap Just se' >>= unwrap
  where
    unwrap Nothing = fail "Parse error."
    unwrap (Just e) = return e

se' :: forall p. (CharStream p, Monad1 p) => p (Maybe SE) (Maybe SE)
se' = case monad1 @p @(Maybe SE) of
  Dict -> do
    c <- firstChar =. char
    case c of
      '(' -> dimap (fromList . fromJust) (Just . List) seList
      ')' -> pure Nothing
      c | isSpace c -> se'
      c -> pure (Just (Atom c))
  where
    firstChar Nothing = ')'
    firstChar (Just (Atom a)) = a
    firstChar (Just (List _)) = '('
    fromList (List es) = es
    fromList (Atom _) = error "Impossible."

seList :: forall p. (CharStream p, Monad1 p) => p [SE] [SE]
seList = case monad1 @p @[SE] of
  Dict -> do
    e' <- lmap listToMaybe se'
    case e' of
      Nothing -> pure []
      Just e -> dimap tail (e :) seList
\end{code}

Unidirectional version for comparison
+++++++++++++++++++++++++++++++++++++

\begin{code}
parseSE :: Parser SE
parseSE = parseSE' >>= unwrap
  where
    unwrap Nothing = fail "Parse error."
    unwrap (Just e) = return e

parseSE' :: Parser (Maybe SE)
parseSE' = do
  c <- parseChar
  case c of
    '(' -> fmap (Just . List) parseSEList
    ')' -> pure Nothing
    c | isSpace c -> parseSE'
    c -> (pure . Just . Atom) c

parseSEList :: Parser [SE]
parseSEList = do
  e' <- parseSE'
  case e' of
    Nothing -> pure []
    Just e -> fmap (e :) parseSEList

printSE :: SE -> Printer ()
printSE (Atom c) = printChar c
printSE (List es) = do
  printChar '('
  traverse_ printSE es
  printChar ')'
\end{code}

Comments
++++++++

The total number of lines of code is about the same.

The unidirectional printer benefits from the use of ``traverse_``,
there might be a bidirectional combinator corresponding to this use case
(parse and accumulate until ``Nothing`` is returned).

The bidirectional program uses some lines of code to expose the ``Monad``
constraint in ``monad1 :: Dict``.
A more lightweight solution is to use three ``Monad`` constraints on ``p SE``,
``p (Maybe SE)`` and ``p [SE]`` instead of ``Monad1 p``.

The parser used here is quite simplistic. In particular, it has no lookahead
nor error recovery, both of which could help make the unidirectional
parser more concise, and support multi-character atoms.
However it is still unclear how the printer could be modified to
mirror these features in a bidirectional specification.

Executable
==========

\begin{code}
main :: IO ()
main = do
  let
    s = "(a (b c (d e)) f)"
    Just e = runParser (parsing se) s
  Prelude.print e
  putStrLn $ runPrinter (printing se e)
\end{code}
