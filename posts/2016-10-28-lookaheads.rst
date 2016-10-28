---
title: Lookaheads
---

\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Bidirectional.Serialization.Example.Lookahead where

import Control.Monad
import Data.Char
import Data.Functor
import Data.Maybe
import Prelude hiding (print)
import qualified Prelude

import Bidirectional.Serialization.Classes
\end{code}

Bidirectional lookahead
=======================

In the previous example we implemented parsers with no lookahead. A somewhat
awkward detail: when a left parenthesis is encountered, the handling of its
matching right parenthesis is done in a nested auxiliary parser, obfuscating a
little the fact that S-expressions are well-parenthesized strings.

Using lookaheads, we can avoid matching delimiters in auxiliary parsers,
so that their structure can be made more explicit in the implementation,
improving readability.

We augment the ``CharStream`` typeclass with a ``lookahead`` method.

\begin{code}
class Profunctor p => CharStream p where

  -- Consume one character.
  char :: p Char Char

  -- One-character lookahead.
  -- Also detects end of file.
  lookahead :: p (Maybe Char) (Maybe Char)
\end{code}

Typeclass law
-------------

Typeclass laws specify additional constraints that the methods ought to
satisfy. By restricting the possible interactions between typeclass methods,
they serve as a (semi-)formal form of documentation and help programmers reason
about polymorphic code involving such typeclasses.

The following sequence of actions:

- looking ahead one character;
- consuming one character;
- asserting that the lookahead and the consumed character are indeed equal;

should be the same as just consuming the character.

More formally, assuming ``MonadPlus1 p`` (i.e., ``MonadPlus (p
a)`` for all ``a``), then ``char`` should be equivalent to:

.. code:: haskell

  lmap Just lookahead >>= \c' -> case c' of
    Nothing -> mzero
    Just c -> mfilter (c ==) char

For simplicity's sake, we will not use ``MonadPlus`` here.
A more basic law, though less elegant because of partial values[#partial]_,
might be that, requiring just a ``Monad`` instance, ``char`` should be
equivalent to:

.. code:: haskell

  lmap Just lookahead >>= \c' -> char >>= \d ->
    if c' == Just d then
      return d
    else
      undefined

.. [#partial]

  This might not be a good simplification because the ``Monad`` laws are
  rather fragile in the presence of partial values.

The types
=========

Parser
------

We keep the same parser as in the previous post.

\begin{code}
newtype Parser a = Parser { parse :: String -> Maybe (String, a) }
  deriving Functor

runParser :: Parser a -> String -> Maybe a
runParser p s = case parse p s of
  Just ([], a) -> Just a
  _ -> Nothing

instance Applicative Parser where
  pure a = Parser (\s -> Just (s, a))
  Parser f_ <*> Parser a_ = Parser $ \s -> do
    (s', f) <- f_ s
    (s'', a) <- a_ s'
    return (s'', f a)

instance Monad Parser where
  Parser a_ >>= f = Parser $ \s -> do
    (s', a) <- a_ s
    (s'', b) <- parse (f a) s'
    return (s'', b)

parseChar :: Parser Char
parseChar = Parser parseChar'
  where
    parseChar' [] = Nothing
    parseChar' (c : s) = Just (s, c)
\end{code}

An additional function for lookaheads.

\begin{code}
-- Lookaheads never fail.
parseLookahead :: Parser (Maybe Char)
parseLookahead = Parser (Just . parseLookahead')
  where
    parseLookahead' [] = ([], Nothing)
    parseLookahead' s@(c : _) = (s, Just c)

instance CharStream (Parsing Parser) where
  char = Parsing parseChar
  lookahead = Parsing parseLookahead
\end{code}

Printer
-------

The printer is more surprising. It carries a ``Lookahead``,
which "announces" a character to be written (or the end of the stream).

\begin{code}
data Lookahead
  = Unknown
  | Expect Char
  | End
  deriving (Eq, Ord, Read, Show)

data Printer a
  = Printer (String, a) Lookahead
  | Failed (String, Lookahead, String, Lookahead)
  -- Reports the point of failure, useful for debugging.
  deriving Functor

runPrinter :: Printer a -> Either String String
runPrinter (Printer (s, _) (Expect c)) =
  Left $ "Incomplete printer: " ++ show (s, c)
runPrinter (Printer (s, _) _) = Right s
runPrinter (Failed u) =
  Left $ "Conflicting printer: " ++ show u
\end{code}

Whenever a character is written, we ensure that it is indeed the character
announced by the lookahead (if any).

The ``matchAhead`` function takes the current lookahead, a string to write, and
a new lookahead and checks their consistency, returning the new lookahead
after writing the string.
A faster printer would unsafely *not* perform this check.

Its complexity is largely devoted to the case where nothing is being written,
then the lookaheads are expected to match, with ``Unknown`` acting as a
wildcard.

\begin{code}
matchAhead :: Lookahead -> [Char] -> Lookahead -> Maybe Lookahead
matchAhead Unknown _ next' = Just next'
matchAhead next [] Unknown = Just next
matchAhead (Expect c) (c' : _) next' = guard (c == c') $> next'
matchAhead (Expect c) [] next'@(Expect c') = guard (c == c') $> next'
matchAhead (Expect _) [] End = Nothing
matchAhead End (_ : _) _ = Nothing
matchAhead End [] End = Just End
matchAhead End [] (Expect _) = Nothing

instance Applicative Printer where
  pure a = Printer ("", a) Unknown
  Printer (s, f) next <*> Printer (s', a) next'
    | Just next'' <- matchAhead next s' next'
      = Printer (s ++ s', f a) next''
    | otherwise
      = Failed (s, next, s', next')
  Failed u <*> _ = Failed u
  _ <*> Failed v = Failed v

instance Monad Printer where
  Printer (s, a) next >>= f = case f a of
    Printer (s', b) next'
      | Just next'' <- matchAhead next s' next'
        -> Printer (s ++ s', b) next''
      | otherwise -> Failed (s, next, s', next')
    Failed v -> Failed v
  Failed u >>= _ = Failed u

printChar :: Char -> Printer Char
printChar c = Printer ([c], c) Unknown
\end{code}

Whereas ``pure`` and ``printChar`` set the lookahead field to ``Unknown``,
non-trivial lookaheads are created via ``printLookahead``.
Note that this does not write anything, it is only a promise to write the given
character later.

\begin{code}
printLookahead :: Maybe Char -> Printer (Maybe Char)
printLookahead c' = Printer ([], c') (toLookahead c')
  where
    toLookahead Nothing = End
    toLookahead (Just c) = Expect c

instance CharStream (Printing Printer) where
  char = Printing printChar
  lookahead = Printing printLookahead
\end{code}

A simple tokenizer
==================

We will implement a conversion from a character stream to a token stream
made of alphanumerical words and parentheses, separated (or not) by spaces.

\begin{code}
data Token
  = Atom String -- Alphanumerical string
  | LPar -- '('
  | RPar -- ')'
  deriving Show
\end{code}

For example:

::

  (a(bc()(d))e f)

should be parsed as

::

  [ LPar, Atom "a", LPar, Atom "bc", LPar, RPar
  , LPar, Atom "d", RPar, RPar, Atom "e", Atom "f", RPar
  ]

We also wish to obtain a pretty-printer at the same time, separating elements
of a list (delimited by brackets) with spaces, but leaving no space after an
left parenthesis or before a right one.

::

  (a (bc (d)) e f)

Implementation
--------------

A stream of tokens starts with any number of whitespace characters, followed by
a sequence of individual tokens (each consuming whitespace after itself).

\begin{code}
tokens :: forall p. (CharStream p, Monad1 p) => p [Token] [Token]
tokens = case monad1 @p @[Token] of
  Dict -> noSpace *> many' token
\end{code}

The ``many'`` combinator iterates a parser of ``Maybe`` until it returns
``Nothing``, cumulating their results.
As a printer, the parameter ``p`` receives a list and is expected to only
print its head, but it is allowed to inspect its tail in order to prettify
the output (here, inserting spaces between certain tokens); ``many' p``
traverses the list to print it one element at a time using ``p``.

\begin{code}
many'
  :: forall p a
  .  (Profunctor p, Monad1 p)
  => p [a] (Maybe a) -> p [a] [a]
many' p = case monad1 @p @[a] of
  Dict -> do
    a' <- p
    case a' of
      Nothing -> return []
      Just a -> (a :) <$> tail =. many' p
\end{code}

Handling spaces
+++++++++++++++

We have two bidirectional parsers to consume spaces. They differ in their
behaviour as printers: ``noSpace`` prints nothing, ``postSpace`` may print one
space depending on the next token. Both still need to inspect the next token to
feed to ``lookahead``, which allows the parsers not to consume any non-space
character.

\begin{code}
-- Consume optional spaces. Print no spaces.
--
-- The printing context looks at the first token to obtain
-- a lookahead.
noSpace :: forall p. (CharStream p, Monad1 p) => p [Token] ()
noSpace = space firstTokenFirst noSpace

-- Consume spaces after a token.
--
-- As a printer, assumes that the previous token was either an atom
-- or a closing bracket, and looks at the next token to determine
-- whether to print a space or not.
postSpace :: forall p. (CharStream p, Monad1 p) => p [Token] ()
postSpace = space firstTokenPre noSpace

-- Consume spaces. Parameterized by a custom lookahead producer.
space
  :: forall p a
  .  (CharStream p, Monad1 p)
  => (a -> Maybe Char) -> p a () -> p a ()
space nextChar moreSpaces = case monad1 @p @a of
  Dict -> do
    c' <- nextChar =. lookahead
    case c' of
      Just c | isSpace c -> consume >> moreSpaces
        where consume = lmap (const c) char
      _ -> return ()

-- The first character of the first token.
firstTokenFirst :: [Token] -> Maybe Char
firstTokenFirst (t : _) = Just (tokenFirst t)
firstTokenFirst [] = Nothing

-- The first character of a token.
tokenFirst :: Token -> Char
tokenFirst (Atom a) = head a
tokenFirst LPar = '('
tokenFirst RPar = ')'

-- The first character after some implicit token followed by
-- the given list of tokens.
-- This allows to print spaces prettily between tokens.
firstTokenPre :: [Token] -> Maybe Char
firstTokenPre (RPar : _) = Just ')'
firstTokenPre (_ : _) = Just ' '
firstTokenPre [] = Nothing
\end{code}

One token at a time
-------------------

We use a lookahead to distinguish the type of the next token, deferring to
auxiliary parsers ``atom`` and ``consume`` to actually consume it, followed by
the appropriate whitespace consumer.

\begin{code}
-- Parse a token and consume following spaces.
token :: forall p. (CharStream p, Monad1 p) => p [Token] (Maybe Token)
token = case monad1 @p @[Token] of
  Dict -> do
    c' <- firstTokenFirst =. lookahead
    case c' of
      Nothing -> return Nothing
      Just c
        | isAlphaNum c -> atom <* lmap tail postSpace
        | '(' == c -> consume $> Just LPar <* lmap tail noSpace
        | ')' == c -> consume $> Just RPar <* lmap tail postSpace
        | otherwise -> fail $ "Unexpected character: " ++ show c
        where
          consume = lmap (const c) char
  where
    -- The atom parser only needs one character following
    -- the token it is parsing.
    atom = dimap
      (\(Atom a : as) -> a ++ maybeToList (firstTokenPre as))
      (Just . Atom)
      (atom' [])

-- Parse an atom (sequence of alphanumerical characters).
-- This parser carries an accumulator to enable tail calls.
atom' :: forall p. (CharStream p, Monad1 p) => [Char] -> p [Char] [Char]
atom' acc = case monad1 @p @[Char] of
  Dict -> do
    c' <- firstChar =. lookahead
    case c' of
      Just c | isAlphaNum c -> consume >> lmap tail (atom' (c : acc))
        where consume = lmap (const c) char
      _ -> (return . reverse) acc
  where
    firstChar (c : _) = Just c
    firstChar [] = Nothing
\end{code}

Executable
==========

\begin{code}
main :: IO ()
main = do
  let
    s = "(a(bc()(d))e f)"
    Just e = runParser (parsing tokens) s
  Prelude.print e
  either putStrLn putStrLn . runPrinter $ printing tokens e
\end{code}
