{-# OPTIONS_GHC -dsuppress-all -O #-}
{-# LANGUAGE CPP, FlexibleInstances, TemplateHaskell #-}

-- This module tests the "definitional lawfulness" of monads from base and transformers:
-- whether the laws are satisfied by mere inlining of definitions and
-- elementary simplifications, leveraging the GHC Core simplifier and the
-- inspection-testing library.
--
-- Summary:
--
-- - Associativity holds for virtually all of the "concrete monads" (`IO`, `Maybe`,
--   and the standard transformers applied to `Identity`).
--
-- - The identity laws hold only up to "eta-expansion".
--
-- - `[]` cheats with rewrite rules.
--
-- - Abusing CPP is super fun.

-- To build this:
--   ghc -package inspection-testing MonadLaws.hs

module MonadLaws where

import Control.Monad ((>=>))
import Data.Bifunctor (bimap)
import Data.Monoid (Endo(..))

import Data.Functor.Product (Product(..))
import Data.Functor.Identity (Identity(..))

import Control.Monad.Trans.Accum (Accum(..))
import Control.Monad.Trans.Cont (ContT(..))
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.RWS (RWS, RWST(..))
import Control.Monad.Trans.Reader (Reader, ReaderT(..))
import Control.Monad.Trans.Select (Select, SelectT(..), runSelectT)
import Control.Monad.Trans.Writer (Writer, WriterT(..))

import Test.Inspection

-- Low level utilities: force things to be inlined, and manually eta-expand IO/ST/STM
import GHC.Exts (inline)
import GHC.IO (IO(..))
import GHC.ST (ST(..))
import GHC.Conc (STM(..))

-- Associativity

assoc1, assoc2 :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
assoc1 x y z = (x  >=>  y) >=>  z
assoc2 x y z =  x  >=> (y  >=>  z)

#define TEST_ASSOC_(NAME,M,FFF,CSTR) \
assoc1'NAME, assoc2'NAME :: CSTR (a -> M b) -> (b -> M c) -> (c -> M d) -> a -> M d ; \
assoc1'NAME = assoc1 ; \
assoc2'NAME = assoc2 ; \
inspect $ 'assoc1'NAME FFF 'assoc2'NAME

#define TEST_ASSOC(NAME,M,FFF) TEST_ASSOC_(NAME,M,FFF,)

-- Examples

-- Most of the fully concrete monads are definitionally associative.
-- Unlike monad transformers with an abstract monad, with the exception of
-- ContT which doesn't care about m.
TEST_ASSOC(Identity,Identity,==-)
TEST_ASSOC(Maybe,Maybe,==-)
TEST_ASSOC(Either,Either e,==-)
TEST_ASSOC(IO,IO,==-)
TEST_ASSOC(ST,ST s,==-)
TEST_ASSOC(STM,STM,==-)
TEST_ASSOC(Reader,Reader r,==-)
TEST_ASSOC(State,Lazy.State s,==-)
TEST_ASSOC(SState,Strict.State s,==-)
TEST_ASSOC(Cont,ContT r m,==-)  -- No constraint on m
TEST_ASSOC(List,[],==-)         -- This is probably thanks to list fusion (custom rewrite rules)

-- Writer-like monads are only definitionally associative when the
-- monoid is also definitionally associative (like Endo).
TEST_ASSOC(AccumEndo,Accum (Endo w),==-)
TEST_ASSOC(WriterEndo,Writer (Endo w),==-)
TEST_ASSOC(RWSEndo,RWS r (Endo w) s,==-)
TEST_ASSOC_(Accum,Accum w,=/=,Monoid w =>)
TEST_ASSOC_(Writer,Writer w,=/=,Monoid w =>)
TEST_ASSOC_(RWS,RWS r w s,=/=,Monoid w =>)

-- Counterexamples

-- These are NOT definitionally associative
TEST_ASSOC(Select,Select r,=/=)
TEST_ASSOC(ProductMaybe,Product Maybe Maybe,=/=)  -- This almost works

-- Left identity

lid1, lid2 :: Monad m => a -> (a -> m b) -> m b
lid1 x k = k x
lid2 x k = pure x >>= k

#define TEST_LID_(NAME,M,FFF,CSTR) \
lid1'NAME, lid2'NAME :: CSTR a -> (a -> M b) -> M b ; \
lid1'NAME = lid1 ; \
lid2'NAME = lid2 ; \
inspect $ 'lid1'NAME FFF 'lid2'NAME

#define TEST_LID(NAME,M,FFF) TEST_LID_(NAME,M,FFF,)

-- Examples

TEST_LID(Identity,Identity,==-)
TEST_LID(Maybe,Maybe,==-)
TEST_LID(Either,Either e,==-)

TEST_LID(List,[],==-)  -- list fusion

-- Counterexamples

TEST_LID(AccumEndo,Accum (Endo w),=/=)
TEST_LID(WriterEndo,Writer (Endo w),=/=)
TEST_LID(RWSEndo,RWS r (Endo w) s,=/=)
TEST_LID_(Accum,Accum w,=/=,Monoid w =>)
TEST_LID_(Writer,Writer w,=/=,Monoid w =>)
TEST_LID_(RWS,RWS r w s,=/=,Monoid w =>)

TEST_LID(IO,IO,=/=)
TEST_LID(ST,ST s,=/=)
TEST_LID(STM,STM,=/=)
TEST_LID(Reader,Reader r,=/=)
TEST_LID(State,Lazy.State s,=/=)
TEST_LID(SState,Strict.State s,=/=)
TEST_LID(Cont,ContT r m,=/=)
TEST_LID(Select,Select r,=/=)
TEST_LID(ProductMaybe,Product Maybe Maybe,=/=)

-- Left identity with eta

class Eta a where
  -- Law: eta u = u
  -- Modulo laziness (do monad laws even even take strictness into account?)
  eta :: a -> a

instance Eta (Product f g a) where
  eta u = etaProduct u

-- Use @inline@ to avoid sharing
etaProduct :: Product f g a -> Product f g a
etaProduct p = Pair (pfst (inline p)) (psnd p) where
  pfst (Pair x y) = x
  psnd (Pair x y) = y

instance Eta (ReaderT e m a) where
  eta u = ReaderT (\x -> runReaderT (inline u) x)

instance Eta (a, b) where
  eta ~(x, y) = (x, y)

instance Functor m => Eta (Lazy.StateT s m a) where
  eta u = Lazy.StateT (\s -> fmap eta (Lazy.runStateT (inline u) s))

instance Eta (Strict.StateT s m a) where
  eta u = Strict.StateT (\s -> Strict.runStateT (inline u) s)

instance Eta (ContT r m a) where
  eta u = ContT (\c -> runContT (inline u) (\x -> c x))

instance Eta (SelectT r m a) where
  eta u = SelectT (\c -> runSelectT (inline u) (\x -> c x))

instance Eta (IO a) where
  eta u = IO (\s -> case u of IO f -> f s)

instance Eta (ST s a) where
  eta u = ST (\s -> case u of ST f -> f s)

instance Eta (STM a) where
  eta u = STM (\s -> case u of STM f -> f s)

instance Eta w => Eta (Writer w a) where
  eta u = WriterT (Identity (bimap id eta (eta (runIdentity (runWriterT u)))))

instance Eta (Endo a) where
  eta (Endo f) = Endo (\x -> f x)

-- For writer-like monads, we can use 'Endo' like we did for associativity,
-- or we can carefully insert a 'mappend' in the right place when expanding values.

etaWriterL :: Monoid w => Writer w a -> Writer w a
etaWriterL u = WriterT (Identity (etaTupleWL (runIdentity (runWriterT u))))

etaTupleWL :: Monoid w => (a, w) -> (a, w)
etaTupleWL ~(x, y) = (x, mempty `mappend` y)

etaWriterR :: Monoid w => Writer w a -> Writer w a
etaWriterR u = WriterT (Identity (etaTupleWR (runIdentity (runWriterT u))))

etaTupleWR :: Monoid w => (a, w) -> (a, w)
etaTupleWR ~(x, y) = (x, y `mappend` mempty)

etaRWSL :: Monoid w => RWS r w s a -> RWS r w s a
etaRWSL u = RWST (\r s -> Identity (etaTupleW3L (runIdentity (runRWST (inline u) r s))))

etaTupleW3L :: Monoid w => (a, s, w) -> (a, s, w)
etaTupleW3L ~(x, y, z) = (x, y, mempty `mappend` z)

etaRWSR :: Monoid w => RWS r w s a -> RWS r w s a
etaRWSR u = RWST (\r s -> Identity (etaTupleW3R (runIdentity (runRWST u r s))))

etaTupleW3R :: Monoid w => (a, s, w) -> (a, s, w)
etaTupleW3R ~(x, y, z) = (x, y, z `mappend` mempty)

--

#define TEST_LID_ETA_(ETA1,ETA2,NAME,M,FFF,CSTR) \
lid1eta'NAME, lid2eta'NAME :: CSTR a -> (a -> M b) -> M b ; \
lid1eta'NAME = (fmap . fmap) ETA1 lid1 ; \
lid2eta'NAME = (fmap . fmap) ETA2 lid2 ; \
inspect $ 'lid1eta'NAME FFF 'lid2eta'NAME

#define TEST_LID_ETA(NAME,M,FFF) TEST_LID_ETA_(eta,eta,NAME,M,FFF,)

TEST_LID_ETA(IO,IO,==-)
TEST_LID_ETA(ST,ST s,==-)
TEST_LID_ETA(STM,STM,==-)
TEST_LID_ETA(Reader,Reader r,==-)
TEST_LID_ETA(State,Lazy.State s,==-)
TEST_LID_ETA(SState,Strict.State s,==-)
TEST_LID_ETA(Cont,ContT r m,==-)
TEST_LID_ETA(Select,Select r,==-)
TEST_LID_ETA(ProductMaybe,Product Maybe Maybe,==-)
TEST_LID_ETA(WriterEndo,Writer (Endo w),==-)

TEST_LID_ETA_(etaWriterL,id,Writer,Writer w,==-,Monoid w =>)
TEST_LID_ETA_(etaRWSL,id,RWS,RWS r (Endo w) s,==-,)

-- Right identity

rid1, rid2 :: Monad m => m a -> m a
rid1 x = x
rid2 x = x >>= pure

#define TEST_RID_(NAME,M,FFF,CSTR) \
rid1'NAME, rid2'NAME :: CSTR M a -> M a ; \
rid1'NAME = rid1 ; \
rid2'NAME = rid2 ; \
inspect $ 'rid1'NAME FFF 'rid2'NAME

#define TEST_RID(NAME,M,FFF) TEST_RID_(NAME,M,FFF,)

-- Examples

TEST_RID(Identity,Identity,==-)
TEST_RID(Maybe,Maybe,==-)
TEST_RID(Either,Either e,==-)
TEST_RID(ProductMaybe,Product Maybe Maybe,==-)
TEST_RID(List,[],==-)         -- This is probably list fusion

-- Counterexamples

TEST_RID(AccumEndo,Accum (Endo w),=/=)
TEST_RID(WriterEndo,Writer (Endo w),=/=)
TEST_RID(RWSEndo,RWS r (Endo w) s,=/=)
TEST_RID_(Accum,Accum w,=/=,Monoid w =>)
TEST_RID_(Writer,Writer w,=/=,Monoid w =>)
TEST_RID_(RWS,RWS r w s,=/=,Monoid w =>)

TEST_RID(IO,IO,=/=)
TEST_RID(ST,ST s,=/=)
TEST_RID(STM,STM,=/=)
TEST_RID(Reader,Reader r,=/=)
TEST_RID(State,Lazy.State s,=/=)
TEST_RID(SState,Strict.State s,=/=)
TEST_RID(Cont,ContT r m,=/=)
TEST_RID(Select,Select r,=/=)

-- Right identity with eta

#define TEST_RID_ETA_(ETA1,ETA2,NAME,M,FFF,CSTR) \
rid1eta'NAME, rid2eta'NAME :: CSTR M a -> M a ; \
rid1eta'NAME = fmap ETA1 rid1 ; \
rid2eta'NAME = fmap ETA2 rid2 ; \
inspect $ 'rid1eta'NAME FFF 'rid2eta'NAME

#define TEST_RID_ETA(NAME,M,FFF) TEST_RID_ETA_(eta,eta,NAME,M,FFF,)

TEST_RID_ETA(IO,IO,==-)
TEST_RID_ETA(ST,ST s,==-)
TEST_RID_ETA(STM,STM,==-)
TEST_RID_ETA(Reader,Reader r,==-)
TEST_RID_ETA(State,Lazy.State s,==-)
TEST_RID_ETA(SState,Strict.State s,==-)
TEST_RID_ETA(Cont,ContT r m,==-)
TEST_RID_ETA(Select,Select r,==-)

TEST_RID_ETA_(etaWriterR,id,Writer,Writer w,==-,Monoid w =>)
TEST_RID_ETA_(etaRWSR,id,RWS,RWS r w s,==-,Monoid w =>)


-- Middle identity
--
-- f . id . g = f . g
-- ((x >>= pure) >>= k) = (x >>= k)

mid1, mid2 :: Monad m => m a -> (a -> m b) -> m b
mid1 x k = x >>= (\x -> k x)  -- eta-expand k to trick GHC into inlining the definition of (>>=)
                              -- inspection-testing has trouble seeing through modules
mid2 x k = (x >>= pure) >>= k

#define TEST_MID_(NAME,M,FFF,CSTR) \
mid1'NAME, mid2'NAME :: CSTR M a -> (a -> M b) -> M b ; \
mid1'NAME = mid1 ; \
mid2'NAME = mid2 ; \
inspect $ 'mid1'NAME FFF 'mid2'NAME

#define TEST_MID(NAME,M,FFF) TEST_MID_(NAME,M,FFF,)

-- Examples

TEST_MID(Identity,Identity,==-)
TEST_MID(Maybe,Maybe,==-)
TEST_MID(Either,Either e,==-)
TEST_MID(ProductMaybe,Product Maybe Maybe,==-)
TEST_MID(List,[],==-)

TEST_MID(IO,IO,==-)
TEST_MID(ST,ST s,==-)
TEST_MID(STM,STM,==-)
TEST_MID(Reader,Reader r,==-)
TEST_MID(State,Lazy.State s,==-)
TEST_MID(SState,Strict.State s,==-)
TEST_MID(Cont,ContT r m,==-)
TEST_MID(Select,Select r,==-)

TEST_MID(AccumEndo,Accum (Endo w),==-)
TEST_MID(WriterEndo,Writer (Endo w),==-)
TEST_MID(RWSEndo,RWS r (Endo w) s,==-)
TEST_MID_(Accum,Accum w,=/=,Monoid w =>)
TEST_MID_(Writer,Writer w,=/=,Monoid w =>)
TEST_MID_(RWS,RWS r w s,=/=,Monoid w =>)
