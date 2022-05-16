{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-| This module contains the orphan instances for some typeclasses that
    enable them to use `Reducible` as a fallback, -}
module Control.Reducible.Orphans
where

import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Reducible
import qualified Control.Monad.Catch as Catch
import qualified Control.Monad.Error.Class as Except
import qualified Control.Monad.Reader.Class as Reader
import qualified Control.Monad.State.Class as State
import qualified Control.Monad.Writer.Class as Writer

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Applicative m, Alternative (Reduced m)) =>
    Alternative m
  where
    empty =
        fromReduced empty
    a <|> b =
        fromReduced $ toReduced a <|> toReduced b

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, MonadPlus (Reduced m)) =>
    MonadPlus m
  where
    mzero =
        fromReduced mzero
    mplus a b =
        fromReduced $ mplus (toReduced a) (toReduced b)

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, MonadFail (Reduced m)) =>
    MonadFail m
  where
    fail msg =
        fromReduced $ fail msg

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, MonadFix (Reduced m)) =>
    MonadFix m
  where
    mfix a =
        fromReduced $ mfix (toReduced . a)

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, Catch.MonadThrow (Reduced m)) =>
    Catch.MonadThrow m
  where
    throwM e =
        fromReduced $ Catch.throwM e

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, Catch.MonadCatch (Reduced m)) =>
    Catch.MonadCatch m
  where
    catch a h =
        fromReduced $ Catch.catch (toReduced a) (toReduced . h)

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, Catch.MonadMask (Reduced m)) =>
    Catch.MonadMask m
  where
    mask a =
        fromReduced $ Catch.mask $ \restoreReduced ->
            toReduced $
                a (fromReduced . restoreReduced . toReduced)
    uninterruptibleMask a =
        fromReduced $ Catch.uninterruptibleMask $ \restoreReduced ->
            toReduced $
                a (fromReduced . restoreReduced . toReduced)
    generalBracket aa ar au =
        fromReduced $ Catch.generalBracket
            (toReduced aa)
            (\r ec -> toReduced (ar r ec))
            (\r -> toReduced (au r))

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, Except.MonadError e (Reduced m)) =>
    Except.MonadError e m
  where
    throwError e =
        fromReduced $ Except.throwError e
    catchError a h =
        fromReduced $ Except.catchError (toReduced a) (toReduced . h)

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, Reader.MonadReader r (Reduced m)) =>
    Reader.MonadReader r m
  where
    ask =
        fromReduced Reader.ask
    local f a =
        fromReduced $ Reader.local f (toReduced a)
    reader f =
        fromReduced $ Reader.reader f

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, State.MonadState s (Reduced m)) =>
    State.MonadState s m
  where
    get =
        fromReduced State.get
    put x =
        fromReduced $ State.put x
    state f =
        fromReduced $ State.state f

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, Monoid w, Writer.MonadWriter w (Reduced m)) =>
    Writer.MonadWriter w m
  where
    writer aw =
        fromReduced $ Writer.writer aw
    tell w =
        fromReduced $ Writer.tell w
    listen a =
        fromReduced $ Writer.listen (toReduced a)
    pass a =
        fromReduced $ Writer.pass (toReduced a)
