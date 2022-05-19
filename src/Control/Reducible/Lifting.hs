{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Reducible.Lifting (
      applyLifting
    , Lifting (..)
    , MonadLifting (..)
    )
where

import Control.Monad.Trans.Class
import Data.Kind
import qualified Control.Monad.Catch as Catch
import qualified Control.Monad.State.Class as State

{-| A wrapper for decomposing monad transformer applications.

    @`Lifting` m n@ can be seen as an application of an opaque monad
    transformer @`Lifting` m@ to a monad @n@.

    Normally, you wouldn't use `Lifting` in you business code. When
    generalizing a monad with t`Control.Reducible.Reducible`, @`Lifting` m n@
    is used as the the most general representation. -}
newtype Lifting (m :: Type -> Type) (n :: Type -> Type) a
    = Lifting
        { unwrapLifting :: m a
        }
    deriving newtype (Functor, Applicative, Monad)

{-| Lifting of actions in monad @n@ into @m@,

    Whereas `MonadTrans` provides lifting by exactly one transformer layer at
    a time, `MonadLifting` can lift by an arbitrary distance at once. -}
class MonadLifting m n where
    liftLong :: n a -> m a

instance {-# INCOHERENT #-} MonadLifting m m where
    liftLong = id

instance
    {-# INCOHERENT #-}
    (MonadTrans t, MonadLifting m n, Monad m) =>
    MonadLifting (t m) n
  where
    liftLong = lift . liftLong

{-| This function plays the role of `lift` for @`Lifting` m@.

    The reason we don't use `lift` proper is that the exact implementation
    depends on both parameters @m@ and @n@, but the kind of `MonadTrans`
    does not allow us that choice. -}
applyLifting :: MonadLifting m n => n a -> Lifting m n a
applyLifting m = Lifting (liftLong m)

instance
    (MonadLifting m n, Monad m, MonadFail n) =>
    MonadFail (Lifting m n)
  where
    fail msg =
        applyLifting $ fail msg

instance
    (MonadLifting m n, Monad m, Catch.MonadThrow n) =>
    Catch.MonadThrow (Lifting m n)
  where
    throwM e =
        applyLifting $ Catch.throwM e

instance
    (MonadLifting m n, Monad m, State.MonadState s n) =>
    State.MonadState s (Lifting m n)
  where
    get =
        applyLifting State.get
    put x =
        applyLifting $ State.put x
    state f =
        applyLifting $ State.state f
