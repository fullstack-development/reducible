{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Reducible (
{-* Overview -}
{-| The main purpose of this module is to solve the \( O(n^2) \)-instances
    problem of the MTL-style abstractions with minimal complexity.

    For this problem, it is an alternative to packages such as
    [fused-effects](https://hackage.haskell.org/package/fused-effects)
    and [polysemi](https://hackage.haskell.org/package/polysemy); however,
    here we use a completely different approach.

    The central concept of this package is a /reduction/: an embedding of
    a specific monad into a more general one.

    For example, we can embed any `Writer.Lazy.WriterT` into
    `State.Lazy.StateT`, by accumulating the output into the state:

    @
    reduceWriterToState ::
        (`Monad` m, `Monoid` w) =>
        `Writer.Lazy.WriterT` w m a -> `State.Lazy.StateT` w m a
    reduceWriterToState asWriter = do
        s <- `State.Lazy.get`
        (a, w) <- `Control.Monad.Trans.lift` $ `Writer.Lazy.runWriterT` asWriter
        `State.Lazy.put` (s <> w)
        `pure` a

    restoreWriterFromState ::
        (`Monad` m, `Monoid` w) =>
        `State.Lazy.StateT` w m a -> `Writer.Lazy.WriterT` w m a
    restoreWriterFromState asState = do
        (a, w) <- `Control.Monad.Trans.lift` $ `State.Lazy.runStateT` asState mempty
        `Writer.Lazy.tell` w
        `pure` a
    @

    As an embedding, this transformation has a number of properties:

    * For any given `Writer.Lazy.WriterT` action, if we first transform it
    into the corresponding `State.Lazy.StateT`, and then transform back &#8211;
    the `Writer.Lazy.WriterT` we will get in the end will behave exactly the
    same as the original: in its result, in its Writer output and even in
    the side effects in the lower @m@ monad.

    * Given two `Writer.Lazy.WriterT` actions, if we first transform them
    into `State.Lazy.StateT`-s, combine them with the State's `(>>=)` operator,
    and then transform the result back to `Writer.Lazy.WriterT` &#8211; we will
    get the same behavior, as if we just combined the original
    `Writer.Lazy.WriterT`-s with its native `(>>=)`.

    For many operations, given an implementation for `State.Lazy.StateT`,
    this embedding allows us to re-use it for `Writer.Lazy.WriterT`,
    instead of writing it from scratch. For example, let's look at lifting
    a `Control.Monad.Except.MonadExcept` instance:

    @
    instance
        (`Control.Monad.Except.MonadExcept` e m, `Monad` m) =>
        `Control.Monad.Except.MonadExcept` e (`State.Lazy.StateT` s m)
      where
        throwError e =
            `State.Lazy.StateT` $ \_state ->
                `Control.Monad.Except.throwError` e
        catchError action handler =
            `State.Lazy.StateT` $ \initialState ->
                `Control.Monad.Except.catchError`
                    (`State.Lazy.runStateT` action initialState)
                    (\e -> `State.Lazy.runStateT` (handler e) initialState)
    @

    Given a reduction of `Writer.Lazy.WriterT` to `State.Lazy.StateT`, we
    can write the instance using that:

    @
    instance
        (`Control.Monad.Except.MonadExcept` e m, `Monad` m) =>
        `Control.Monad.Except.MonadExcept` e (`Writer.Lazy.WriterT` s m)
      where
        throwError e =
            restoreWriterFromState $
                `Control.Monad.Except.throwError` e
        catchError action handler =
            restoreWriterFromState $
                `Control.Monad.Except.catchError`
                    (reduceWriterToState action)
                    (\e -> reduceWriterToState (handler e))
    @

    This code treats the `Writer.Lazy.WriterT` as a special case of the
    `State.Lazy.StateT`. In `Control.Monad.Except.catchError` of the State
    monad, if the @action@ branch throws, all of the modification to the state
    that happened in this branch get reverted before entering the @handler@.
    In our reduction, modifying the state corresponds to accumulating the
    Writer's output &#8211; thus, in `Control.Monad.Except.catchError` of the
    Writer, as defined here, throwing in the @action@ will undo all of its
    writes, as we would expect.

    Using GHC's
    [Overlapping instances](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/instances.html#overlapping-instances),
    we can automate defining new instances by reductions:

    @
    instance
        \{\-# OVERLAPPABLE #\-\}
        (`Control.Monad.Except.MonadExcept` e (`Reduced` m), `Monad` m, `Reducible` m) =>
        `Control.Monad.Except.MonadExcept` e m
      where
        throwError e =
            `fromReduced` $
                `Control.Monad.Except.throwError` e
        catchError action handler =
            `fromReduced` $
                `Control.Monad.Except.catchError`
                    (`toReduced` action)
                    (\e -> `toReduced` (handler e))
    @

    In this instance:

    * `Reducible` is the typeclass of such reductions.

        For example, since a Writer can be reduced to a State, there exists
        an instance of
        @(`Monad` m, `Monoid` w) => `Reducible` (`Writer.Lazy.WriterT` w m)@

    * @`Reduced` m@ is the resulting type after the reduction.

        For example, @`Reduced` (`Writer.Lazy.WriterT` w m)@ is
        @`State.Lazy.StateT` w m@.

    * `fromReduced` and `toReduced` are methods of `Reducible` that transform
    an action between the original and reduced forms.

        For our Writer->State example, these correspond to
        @restoreWriterFromState@ and @reduceWriterToState@.

    * @\{\-# OVERLAPPABLE #\-\}@ is a GHC pragma that makes the instance a lower
    priority than normal: when solving a constraint, if there is a matching
    normal instance, it will override the overlappable one.

        In other words, this pragma marks the instance as a /fallback/: to be
        used only if we don't have something more specific. -}
{-* Usage patterns -}
{-** When defining a class -}
{-| For typeclasses, when defining lifting instances, it should be enough to
    write these four:

    * @MonadBusiness m => MonadBusiness (`Reader.ReaderT` r m)@

    * @MonadBusiness m => MonadBusiness (`State.Lazy.StateT` s m)@

    * @MonadBusiness m => MonadBusiness (`Except.ExceptT` s m)@

    * @\{\-# OVERLAPPABLE #\-\} (`Reducible` m, MonadBusiness (`Reduced` m)) => MonadBusiness m@ -}
{-** When defining a monad -}
{-| When defining a monad, give it a `Reducible` instance.

    If it is simply a newtype over a @transformers@-stack, just reduce it to
    its representation:

    @
    newtype BusinessT m a
        = BusinessT m (ReaderT AppContext (ExceptT AppError m) a)
        deriving newtype (`Functor`, `Applicative`, `Monad`, `Control.Monad.IO.MonadIO`)

    instance `Reducible` (BusinessT m) where
        type `Reduced` (BusinessT m) = ReaderT AppContext (ExceptT AppError m)
    @

    You don't even need to write explicit implementations for `fromReduced` and
    `toReduced`, since their defaults are intended exactly for scenario.

    If it is a something more fancy, try to express it as a `Reader.ReaderT`,
    a `State.Lazy.StateT`, an `Except.ExceptT` or a combination of those. -}
{-* Reducible instance -}
      Reducible (..)
    )
where

import Control.Reducible.Internal.TH (chooseInstanceIfMatchingRepr)
import Data.Coerce
import Data.Functor.Identity
import Data.Kind
import qualified Control.Monad.Catch.Pure as Catch
import qualified Control.Monad.Trans.Accum as Accum
import qualified Control.Monad.Trans.Except as Except
import qualified Control.Monad.Trans.Maybe as Maybe
import qualified Control.Monad.Trans.Identity as Identity
import qualified Control.Monad.Trans.RWS.CPS as RWS.CPS
import qualified Control.Monad.Trans.RWS.Lazy as RWS.Lazy
import qualified Control.Monad.Trans.RWS.Strict as RWS.Strict
import qualified Control.Monad.Trans.Reader as Reader
import qualified Control.Monad.Trans.State.Lazy as State.Lazy
import qualified Control.Monad.Trans.State.Strict as State.Strict
import qualified Control.Monad.Trans.Writer.CPS as Writer.CPS
import qualified Control.Monad.Trans.Writer.Lazy as Writer.Lazy
import qualified Control.Monad.Trans.Writer.Strict as Writer.Strict
import qualified Unsafe.Coerce

{-  On `Writer.CPS.WriterT` and `RWS.CPS.RWST`.

    To avoid redundant conversions, we want to unwrap their
    newtype constructors and use their similarity to `State.Strict.StateT`.

    However, since their constructors are not exported, so we cannot use them
    directly. Similarly, `coerce` requires a constructor to be visible.

    `unsafeCoerce`, on the other hand, has no such requirements; but it also
    won't check if the types actually have the same representation.

    Thus, to be sure that the coercions are sound, we still verify
    with TH code that the internal representations really do match
    what we expect.

    If the match fails, we issue a warning and fall back to converting
    normally through the public API. -}

{-| Embedding of one monad into another.

    The default implementation is to `coerce` between the given monad and
    its reduced form.

    The laws:

    1. Reduction is lossless:

        @fromReduced . toReduced === id@

        The reverse is not required to hold: the reduced form may be a more
        general monad than the given one. For example, we reduce
        `Writer.Lazy.WriterT` to `State.Lazy.StateT`, since the Writer monad
        can be correctly emulated by the State; but not the other way around,

        Thus, we require that transforming
        @`Writer.Lazy.WriterT` -> `State.Lazy.StateT` -> `Writer.Lazy.WriterT`@
        results in exactly the same behavior as in the original monadic action;
        however, doing the same with
        @`State.Lazy.StateT` -> `Writer.Lazy.WriterT` -> `State.Lazy.StateT`@
        is plainly impossible &#8211; so, we require
        @fromReduced . toReduced === id@, but give no laws for
        @toReduced . fromReduced@.

    2. `pure` and `(>>=)` of the reduced form must match the original:

        @toReduced . pure = pure@

        @forall a b. fromReduced (toReduced a >>= toReduced . b) === a >>= b@

        Again, the reverse may not hold in general: the reduced form may
        contain additional context, that the binding operator of the original
        does not account for. For example, `State.Lazy.StateT` expects the
        effects of all previous actions to be applied to its state on input,
        but `Writer.Lazy.WriterT`'s bind operator simply has no way of
        obtaining this information.

    The overall idea is to provide a way to /reduce/ an algorithm in a
    specialized monad to functionally the same algorithm, but expressed in a
    more general monad &#8211; allowing the general monad's functions to be
    used on it &#8211; and then getting a sensible result after transforming
    back to the specialized monad it was originally in. -}
class Reducible (m :: Type -> Type) where
    type Reduced m :: Type -> Type
    fromReduced :: Reduced m a -> m a
    default fromReduced :: (Coercible (Reduced m a) (m a)) => Reduced m a -> m a
    fromReduced = coerce
    toReduced :: m a -> Reduced m a
    default toReduced :: (Coercible (m a) (Reduced m a)) => m a -> Reduced m a
    toReduced = coerce

{- Identity -}

{-| @`Identity.IdentityT` m@ to @m@ -}
instance Reducible (Identity.IdentityT m) where
    type Reduced (Identity.IdentityT m) =
        m

{- ReaderT r m -}

{-| @(->) r@ to @`Reader.ReaderT` r `Identity`@ -}
instance Reducible ((->) r) where
    type Reduced ((->) r) =
        Reader.ReaderT r Identity

{- StateT s m -}

{-| strict to lazy -}
instance Reducible (State.Strict.StateT s m) where
    type Reduced (State.Strict.StateT s m) =
        State.Lazy.StateT s m

{-| @`Writer.CPS.WriterT` w m@ to @`State.Lazy.StateT` w m@ -}
chooseInstanceIfMatchingRepr
    ''Writer.CPS.WriterT
    ''State.Lazy.StateT
    [d|
        instance Reducible (Writer.CPS.WriterT w m) where
            type Reduced (Writer.CPS.WriterT w m) =
                State.Lazy.StateT w m
            fromReduced = Unsafe.Coerce.unsafeCoerce
            toReduced = Unsafe.Coerce.unsafeCoerce
      |]
    [d|
        instance
            (Functor m, Monoid w) =>
            Reducible (Writer.CPS.WriterT w m)
          where
            type Reduced (Writer.CPS.WriterT w m) =
                State.Lazy.StateT w m
            fromReduced (State.Lazy.StateT asState) =
                Writer.CPS.writerT (asState mempty)
            toReduced asWriterAct =
                State.Lazy.StateT $ \s ->
                    fmap
                        (fmap (s <>))
                        (Writer.CPS.runWriterT asWriterAct)
      |]

{-| @`Accum.AccumT` w m@ to @`State.Lazy.StateT` w m@ -}
instance (Functor m, Monoid w) => Reducible (Accum.AccumT w m) where
    type Reduced (Accum.AccumT w m) =
        State.Lazy.StateT (w, w) m
    fromReduced (State.Lazy.StateT asState) =
        Accum.AccumT $ \total ->
            fmap
                (\(x, (_, written)) -> (x, written))
                (asState (total, mempty))
    toReduced (Accum.AccumT asAccum) =
        State.Lazy.StateT $ \(total, pending) ->
            fmap
                (\(x, local) -> (x, (total <> local, pending <> local)))
                (asAccum total)

newtype ContRWST r w s m a
    = ContRWST (r -> s -> w -> m (a, s, w))

{-| @`RWS.CPS.RWST` r w s m@ to @`Reader.ReaderT` r (`State.Lazy.StateT` (s, w) m)@ -}
chooseInstanceIfMatchingRepr
    ''RWS.CPS.RWST
    ''ContRWST
    [d|
        instance (Functor m) => Reducible (RWS.CPS.RWST r w s m) where
            type Reduced (RWS.CPS.RWST r w s m) =
                Reader.ReaderT r (State.Lazy.StateT (s, w) m)
            fromReduced red =
                Unsafe.Coerce.unsafeCoerce ContRWST $ \r s1 w1 ->
                    fmap
                        (\(a, (s2, w2)) -> (a, s2, w2))
                        (State.Lazy.runStateT
                            (Reader.runReaderT red r)
                            (s1, w1)
                        )
            toReduced rwst =
                case Unsafe.Coerce.unsafeCoerce rwst of
                    ContRWST asContRWST ->
                        Reader.ReaderT $ \r ->
                            State.Lazy.StateT $ \(s1, w1) ->
                                fmap
                                    (\(a, s2, w2) -> (a, (s2, w2)))
                                    (asContRWST r s1 w1)
      |]
    [d|
        instance
            (Functor m, Monoid w) =>
            Reducible (RWS.CPS.RWST r w s m)
          where
            type Reduced (RWS.CPS.RWST r w s m) =
                Reader.ReaderT r (State.Lazy.StateT (s, w) m)
            fromReduced red =
                RWS.CPS.rwsT $ \r s1 ->
                    fmap
                        (\(a, (s2, w2)) -> (a, s2, w2))
                        (State.Lazy.runStateT
                            (Reader.runReaderT red r)
                            (s1, mempty)
                        )
            toReduced asRWSTAct =
                Reader.ReaderT $ \r ->
                    State.Lazy.StateT $ \(s1, w1) ->
                        fmap
                            (\(a, s2, w2) -> (a, (s2, w1 <> w2)))
                            (RWS.CPS.runRWST asRWSTAct r s1)
      |]

{-| @`RWS.Lazy.RWST` r w s m@ to @`Reader.ReaderT` r (`State.Lazy.StateT` (s, w) m)@ -}
instance (Functor m, Monoid w) => Reducible (RWS.Lazy.RWST r w s m) where
    type Reduced (RWS.Lazy.RWST r w s m) =
        Reader.ReaderT r (State.Lazy.StateT (s, w) m)
    fromReduced red =
        RWS.Lazy.RWST $ \r s1 ->
            fmap
                (\(a, (s2, w2)) -> (a, s2, w2))
                (State.Lazy.runStateT
                    (Reader.runReaderT red r)
                    (s1, mempty)
                )
    toReduced (RWS.Lazy.RWST asRWST) =
        Reader.ReaderT $ \r ->
            State.Lazy.StateT $ \(s1, w1) ->
                fmap
                    (\(a, s2, w2) -> (a, (s2, w1 <> w2)))
                    (asRWST r s1)

{-| @`RWS.Strict.RWST` r w s m@ to @`Reader.ReaderT` r (`State.Strict.StateT` (s, w) m)@ -}
instance (Functor m, Monoid w) => Reducible (RWS.Strict.RWST r w s m) where
    type Reduced (RWS.Strict.RWST r w s m) =
        Reader.ReaderT r (State.Strict.StateT (s, w) m)
    fromReduced red =
        RWS.Strict.RWST $ \r s1 ->
            fmap
                (\(a, (s2, w2)) -> (a, s2, w2))
                (State.Strict.runStateT
                    (Reader.runReaderT red r)
                    (s1, mempty)
                )
    toReduced (RWS.Strict.RWST asRWST) =
        Reader.ReaderT $ \r ->
            State.Strict.StateT $ \(s1, w1) ->
                fmap
                    (\(a, s2, w2) -> (a, (s2, w1 <> w2)))
                    (asRWST r s1)

{- WriterT w m -}

{-| strict to lazy -}
instance Reducible (Writer.Strict.WriterT w m) where
    type Reduced (Writer.Strict.WriterT w m) =
        Writer.Lazy.WriterT w m

{-| @`Writer.Lazy.WriterT` w m@ to @`State.Lazy.StateT` w m@ -}
instance (Functor m, Monoid w) => Reducible (Writer.Lazy.WriterT w m) where
    type Reduced (Writer.Lazy.WriterT w m) =
        State.Lazy.StateT w m
    fromReduced (State.Lazy.StateT asState) =
        Writer.Lazy.WriterT (asState mempty)
    toReduced (Writer.Lazy.WriterT asWriter) =
        State.Lazy.StateT (\s -> fmap (fmap (s <>)) asWriter)

{-| @(,) w@ to @`Writer.Lazy.WriterT` w `Identity`@ -}
instance Reducible ((,) w) where
    type Reduced ((,) w) =
        Writer.Lazy.WriterT w Identity
    fromReduced (Writer.Lazy.WriterT (Identity (a, w))) =
        (w, a)
    toReduced (w, a) =
        Writer.Lazy.WriterT (Identity (a, w))

{-| @(,,) w1 w2@ to @`Writer.Lazy.WriterT` (w1, w2) `Identity`@ -}
instance Reducible ((,,) w1 w2) where
    type Reduced ((,,) w1 w2) =
        Writer.Lazy.WriterT (w1, w2) Identity
    fromReduced (Writer.Lazy.WriterT (Identity (a, (w1, w2)))) =
        (w1, w2, a)
    toReduced (w1, w2, a) =
        Writer.Lazy.WriterT (Identity (a, (w1, w2)))

{-| @(,,,) w1 w2 w3@ to @`Writer.Lazy.WriterT` (w1, w2, w3) `Identity`@ -}
instance Reducible ((,,,) w1 w2 w3) where
    type Reduced ((,,,) w1 w2 w3) =
        Writer.Lazy.WriterT (w1, w2, w3) Identity
    fromReduced (Writer.Lazy.WriterT (Identity (a, (w1, w2, w3)))) =
        (w1, w2, w3, a)
    toReduced (w1, w2, w3, a) =
        Writer.Lazy.WriterT (Identity (a, (w1, w2, w3)))

{- ExceptT e m -}

{-| @`Either` e@ to @`Except.ExceptT` e `Identity`@ -}
instance Reducible (Either e) where
    type Reduced (Either e) =
        Except.ExceptT e Identity

{-| @`Maybe.MaybeT` m@ to @`Except.ExceptT` () m@ -}
instance (Functor m) => Reducible (Maybe.MaybeT m) where
    type Reduced (Maybe.MaybeT m) =
        Except.ExceptT () m
    fromReduced = Maybe.exceptToMaybeT
    toReduced = Maybe.maybeToExceptT ()

{-| @`Maybe`@ to @`Maybe.MaybeT` `Identity`@ -}
instance Reducible Maybe where
    type Reduced Maybe =
        Maybe.MaybeT Identity

{-| @`Catch.CatchT` m@ to @`Except.ExceptT` Catch.SomeException m@ -}
instance Reducible (Catch.CatchT m) where
    type Reduced (Catch.CatchT m) =
        Except.ExceptT Catch.SomeException m
