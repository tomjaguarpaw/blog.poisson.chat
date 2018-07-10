{-# LANGUAGE TypeFamilies, UndecidableInstances #-}

-- https://blog.poisson.chat/posts/2018-07-09-type-gadt.html

module UnMTL where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Data.Functor.Identity
import Data.Kind

type family   UnMTL (a :: Type) :: Type
type instance UnMTL (ReaderT r m a) = r -> UnMTL (m a)
type instance UnMTL (StateT  s m a) = s -> UnMTL (m (a, s))
type instance UnMTL (ExceptT e m a) = UnMTL (m (Either e a))
type instance UnMTL (Identity a) = a
type instance UnMTL (IO a) = IO a
