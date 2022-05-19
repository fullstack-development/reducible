{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Reducible (
{-* Overview -}
{-| The main purpose of this module is to solve the \( O(n^2) \)-instances
    problem of the MTL-style abstractions with minimal complexity.

    The main idea is to provide a way to /reduce/ special-purpose monads
    into a small set of well-known general monads, such as `Reader.ReaderT`,
    `State.Lazy.StateT` and `Except.ExceptT`. Then, when defining typeclasses
    for functionality &#8211; such as @mtl:`Control.Monad.Reader.MonadReader`@,
    @exceptions:`Control.Monad.Catch.MonadMask`@,
    @beam-core:Database.Beam.MonadBeam@ &#8211; we will only need to define
    explicit instances for these general monads, and the rest will be
    created automatically by reduction.

    As a working example, let's imagine using two libraries in an application,
    one for logging and another for database access.

    In the database library, we define a database effect:

    @
    class Monad m => MonadDatabase m where
        runReturningMany ::
            DatabaseQuery r ->
            (m (Maybe r) -> m a) ->
            m a
    @

    (This is a simplified form of [@runReturningMany@ method of @MonadBeam@](https://hackage.haskell.org/package/beam-core-0.9.2.1/docs/Database-Beam.html#v:runReturningMany))

    A database monad:

    @
    newtype DatabaseT m a = DatabaseT
        { runDatabaseT :: Connection -> m a
        }
        deriving (Functor, Applicative, Monad, MonadIO)
            via (ReaderT Connection m)
        deriving (MonadTrans)
            via (ReaderT Connection)
    @

    And an implementation of the database querying:

    @
    instance MonadIO m => MonadDatabase (DatabaseT m) where
        runReturningMany query handler = DatabaseT $ \\conn -> do
            queryTag <- liftIO $ startQuery conn query
            result <- runDatabaseT
                (handler (liftIO $ getNextRecordMaybe conn queryTag))
                conn
            liftIO $ closeQuery conn queryTag
            pure result
    @

    To allow other libraries to forward their functionality through @DatabaseT@,
    we define its /reduction/:

    @
    instance `Reducible` (DatabaseT m) where
        type `Reduced` (DatabaseT m) =
            `Reader.ReaderT` Connection m
        fromReduced asReader = DatabaseT $ \\conn ->
            `Reader.runReaderT` asReader conn
        toReduced asDb = `Reader.ReaderT` $ \\conn ->
            runDatabaseT asDb conn
    @

    The purpose of `Reducible` is to represent a specialized monad in terms
    of a small number of well-known general-purpose monads, such as
    `Reader.ReaderT` or `Except.ExceptT`.

    Semantically, @`Reducible` m@ means that @m@ is a special case of some
    other monad, @`Reduced` m@, with certain properties:

    1. The general monad @`Reduced` m@ is powerful enough to subsume all of
    the specialized @m@, by using `toReduced` to make the transformation.

    2. The generalization is set up in such a way, that the monadic behavior,
    represented through `pure` and `(>>=)`, of the general monad @`Reduced` m@
    agrees with that of the specialized @m@.

    3. When we chain multiple actions in the general monad @`Reduced` m@, as
    long as all of them belong to the original specialization @m@ &#8211;
    that is, as long as we don't introduce any effects that would not be
    possible in the specialized monad @m@ &#8211; then their combination
    will also belong to the type of the original monad @m@, and we'll be able
    to reverse the reduction with `fromReduced`.

    `Reducible`'s laws make a precise definition of these properties.

    Next, we define how to forward the querying functionality through some
    general-purpose monad transformers:

    @
    instance MonadDatabase m => MonadDatabase (`Reader.ReaderT` r m) where
        runReturningMany query handler = `Reader.ReaderT` $ \\context -> do
            runReturningMany
                query
                (\\source ->
                    `Reader.runReaderT` (handler (lift source)) context
                )

    instance MonadDatabase m => MonadDatabase (`State.StateT` s m) where
        runReturningMany query handler = `State.StateT` $ \\oldState -> do
            runReturningMany
                query
                (\\source ->
                    `State.runStateT` (handler (lift source)) oldState
                )

    instance MonadDatabase m => MonadDatabase (`Except.ExceptT` e m) where
        runReturningMany query handler = `Except.ExceptT` $ do
            runReturningMany
                query
                (\\source ->
                    `Except.runExceptT` (handler (lift source))
                )
    @

    And finally, we define a fallback: when no other instances are found,
    we reduce a monad and try to find an instance for the reduced form:

    @
    instance
        \{\-# OVERLAPPABLE #\-\}
        (`Reducible` m, Monad m, MonadDatabase (Reduced m)) =>
        MonadDatabase m
      where
        runReturningMany query handler = `fromReduced` $ do
            runReturningMany
                query
                (\\source ->
                    `toReduced` (handler (`fromReduced` source))
                )
    @

    In another package, in the logging library, we write something similar
    for a logger monad and effect:

    @
    class Monad m => MonadLogger m where
        logMessage :: String -> m ()

    newtype LoggerT m a = LoggerT
        { runLoggerT :: IO.Handle -> m a
        }
        deriving (Functor, Applicative, Monad, MonadIO)
            via (ReaderT IO.Handle m)
        deriving (MonadTrans)
            via (ReaderT IO.Handle)

    instance MonadIO m => MonadLogger (LoggerT m) where
        logMessage msg = LoggerT $ \\fileHandle -> do
            liftIO $ IO.hPutStrLn fileHandle msg

    instance `Reducible` (LoggerT m) where
        type `Reduced` (LoggerT m) =
            `Reader.ReaderT` IO.Handle m
        fromReduced asReader = LoggerT $ \\fileHandle ->
            `Reader.runReaderT` asReader fileHandle
        toReduced asLogger = `Reader.ReaderT` $ \\fileHandle ->
            runLoggerT asLogger fileHandle
    @

    Reductions form a chain: after the first reduction, if the compiler cannot
    find a specific instance, it will use the fallback again, which will
    perform a second reduction, and so on. This process will repeat until we
    either find an instance for the specific form that we got, or the monad
    cannot be reduced any further.

    For most monads, this most general form will be @`Lifting` m n@, where
    @m@ is the original monad and @n@ is something lower in the stack of
    monad transformers. The only thing this monad allows is to lift from
    this base monad @n@ back to the original @m@, with `applyLifting`.

    When an effect contains only simple procedures that could be forwarded
    with a simple `Control.Monad.Trans.Class.lift`, we can implement this
    strategy by making an instance for `Lifting`, using `applyLifting`, and
    letting everything else to just reduce to `Lifting` with the repeated
    applications of the fallback:

    @
    instance
        (`MonadLifting` m n, Monad m, MonadLogger n) =>
        MonadLogger (Lifting m n)
      where
        logMessage msg = `applyLifting` $ logMessage msg

    instance
        \{\-# OVERLAPPABLE #\-\}
        (`Reducible` m, Monad m, MonadLogger (Reduced m)) =>
        MonadLogger m
      where
        logMessage msg = `fromReduced` $ logMessage msg
    @

    With this code, we can now use both the logger and the database library
    together in the same application: @MonadLogger@ will get forwarded
    through @DatabaseT@, and @MonadDatabase@ will get forwarded through
    @LoggerT@, even though we didn't code any explicit interactions
    between them. -}
{-* Substitution example -}
{-| To see the machinery in action, let's follow the compiler in the following
    example:

    @
    sayHello ::
        forall mbase.
        (MonadLogger mbase) =>
        DatabaseT (`Writer.CPS.WriterT` Text mbase) ()
    sayHello = do
        logMessage
            \@(DatabaseT (`Writer.CPS.WriterT` Text mbase))
            \"Hello\"
    @

    The @logMessage@ here requires an instance of
    @MonadLogger (DatabaseT (`Writer.CPS.WriterT` Text mbase))@.
    Since we don't have a specific instance for @MonadLogger (DatabaseT _)@,
    the compiler chooses the fallback:

    @
    logMessage \@(DatabaseT (`Writer.CPS.WriterT` Text mbase)) msg =
        `fromReduced` \@(DatabaseT (`Writer.CPS.WriterT` Text mbase)) $
            logMessage \@(`Reduced` (DatabaseT (`Writer.CPS.WriterT` Text mbase))) msg

    sayHello = do
        `fromReduced` \@(DatabaseT (`Writer.CPS.WriterT` Text mbase)) $
            logMessage \@(`Reduced` (DatabaseT (`Writer.CPS.WriterT` Text mbase)))
                \"Hello\"
    @

    Applying the instance @`Reducible` (DatabaseT m)@, with
    @m ~ `Writer.CPS.WriterT` Text mbase@, we get:

    @
    type `Reduced` (DatabaseT (`Writer.CPS.WriterT` Text mbase)) =
        `Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)

    fromReduced \@(DatabaseT (`Writer.CPS.WriterT` Text mbase)) asReader =
        DatabaseT $ \\conn ->
            `Reader.runReaderT` asReader conn

    sayHello =
        DatabaseT $ \\conn ->
            `Reader.runReaderT`
                (logMessage
                    \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
                    \"Hello\"
                )
                conn
    @

    This code now requires an instance of
    @MonadLogger (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))@
    &#8211; which is resolved by the fallback again:

    @
    logMessage \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) msg =
        `fromReduced` \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) $
            logMessage
                \@(`Reduced` (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)))
                msg

    sayHello =
        DatabaseT $ \\conn ->
            `Reader.runReaderT`
                (`fromReduced` \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) $
                    logMessage
                        \@(`Reduced` (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)))
                        \"Hello\"
                )
                conn
    @

    Substitute the instance @`Reducible` (`Reader.ReaderT` r m)@ with
    @r ~ Connection@ and @m ~ `Writer.CPS.WriterT` Text mbase@:

    @
    type `Reduced` (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) =
        `Lifting`
            (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
            (`Writer.CPS.WriterT` Text mbase)

    fromReduced \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) =
        `unwrapLifting`
            \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
            \@(`Writer.CPS.WriterT` Text mbase)

    sayHello =
        DatabaseT $ \\conn ->
            `Reader.runReaderT`
                (`unwrapLifting`
                    \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
                    \@(`Writer.CPS.WriterT` Text mbase) $
                        logMessage
                            \@(`Lifting`
                                (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
                                (`Writer.CPS.WriterT` Text mbase))
                            \"Hello\"
                )
                conn
    @

    This time, we get to use the specific instance @MonadLogger (`Lifting` m n)@
    with @m ~ `Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)@
    and @n ~ `Writer.CPS.WriterT` Text mbase@:

    @
    logMessage
        \@(`Lifting`
            (`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
            (`Writer.CPS.WriterT` Text mbase))
        msg
      =
        `applyLifting`
            \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) $
            \@(`Writer.CPS.WriterT` Text mbase) $
                logMessage
                    \@(`Writer.CPS.WriterT` Text mbase)
                    msg

    sayHello =
        DatabaseT $ \\conn ->
            `Reader.runReaderT`
                (`unwrapLifting`
                    \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
                    \@(`Writer.CPS.WriterT` Text mbase) $
                        `applyLifting`
                            \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) $
                            \@(`Writer.CPS.WriterT` Text mbase) $
                                logMessage
                                    \@(`Writer.CPS.WriterT` Text mbase)
                                    \"Hello\"
                )
                conn
    @

    Continuing the same process for `Writer.CPS.WriterT`, we get this series
    of reductions:

    @
    type `Reduced` (`Writer.CPS.WriterT` Text mbase) =
        `State.Lazy.StateT` Text mbase

    fromReduced \@(`Writer.CPS.WriterT` Text mbase) =
        restoreCPSWriterFromState


    type `Reduced` (`State.Lazy.StateT` Text mbase) =
        `Lifting`
            (`State.Lazy.StateT` Text mbase)
            mbase

    fromReduced \@(`State.Lazy.StateT` Text mbase) =
        `unwrapLifting` \@(`State.Lazy.StateT` Text mbase) \@mbase


    sayHello =
        DatabaseT $ \\conn ->
            `Reader.runReaderT`
                (`unwrapLifting`
                    \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
                    \@(`Writer.CPS.WriterT` Text mbase) $
                        `applyLifting`
                            \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) $
                            \@(`Writer.CPS.WriterT` Text mbase) $
                                restoreCPSWriterFromState $
                                    `unwrapLifting` \@(`State.Lazy.StateT` Text mbase) \@mbase $
                                        logMessage
                                            \@(Lifting
                                                (`State.Lazy.StateT` Text mbase)
                                                mbase)
                                            \"Hello\"
                )
                conn
    @

    Applying the specific instance @MonadLogger (`Lifting` m n)@ again
    with @m ~ `State.Lazy.StateT` Text mbase@
    and @n ~ mbase@:

    @
    logMessage \@(Lifting (`State.Lazy.StateT` Text mbase) mbase) msg =
        `applyLifting` \@(`State.Lazy.StateT` Text mbase) \@mbase $
            logMessage \@mbase msg

    sayHello =
        DatabaseT $ \\conn ->
            `Reader.runReaderT`
                (`unwrapLifting`
                    \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase))
                    \@(`Writer.CPS.WriterT` Text mbase) $
                        `applyLifting`
                            \@(`Reader.ReaderT` Connection (`Writer.CPS.WriterT` Text mbase)) $
                            \@(`Writer.CPS.WriterT` Text mbase) $
                                restoreCPSWriterFromState $
                                    `unwrapLifting` \@(`State.Lazy.StateT` Text mbase) \@mbase $
                                        `applyLifting` \@(`State.Lazy.StateT` Text mbase) \@mbase $
                                            logMessage \@mbase \"Hello\"
                )
                conn
    @

    The @logMessage \@mbase@ is resolved directly by @MonadLogger mbase@
    in the function's signature, so this becomes the final form of the code. -}
{-* Usage patterns -}
{-** When defining a class -}
{-| To make the class benefit from the reductions, add an overlapping instance
    of this form:

    @
    instance
        \{\-# OVERLAPPABLE #\-\}
        (`Reducible` m, MonadBusiness (`Reduced` m)) =>
        MonadBusiness m
      where
        doOneThing = `fromReduced` doOneThing
        doAnotherThing a b c = `fromReduced` $ doAnotherThing a b c
        withSomeResource a b useResource handleFailure =
            `fromReduced` $
                withSomeResource a b
                    (\\resource ->
                        `toReduced` (useResource resource)
                    )
                    (\\failReason metadata ->
                        `toReduced` (handleFailure failReason metadata)
                    )
    @

    To actually forward the functionality, you still need to write instances
    for some basic transformers.

    If the class contains only simple actions that don't take monadic inputs,
    then only a single instance for `Lifting` would suffice. For example,
    if the class above did not have @withSomeResource@:

    @
    instance MonadBusiness m => MonadBusiness (`Lifting` m n) where
        doOneThing = `applyLifting` doOneThing
        doAnotherThing a b c = `applyLifting` $ doAnotherThing a b c
    @

    Otherwise, writing instances for `Reader.ReaderT`, `State.Lazy.StateT`
    (lazy) and `Except.ExceptT` should suffice:

    @
    instance (MonadBusiness m) => MonadBusiness (`Reader.ReaderT` r m) where
        doOneThing = `Control.Monad.Trans.Class.lift` doOneThing
        doAnotherThing a b c = `Control.Monad.Trans.Class.lift` $ doAnotherThing a b c
        withSomeResource a b useResource handleFailure =
            `Reader.ReaderT` $ \\context ->
                withSomeResource a b
                    (\\resource ->
                        `Reader.runReaderT` (useResource resource) context
                    )
                    (\\failReason metadata ->
                        `Reader.runReaderT` (handleFailure failReason metadata) context
                    )

    instance (MonadBusiness m) => MonadBusiness (`State.Lazy.StateT` s m) where
        doOneThing = `Control.Monad.Trans.Class.lift` doOneThing
        doAnotherThing a b c = `Control.Monad.Trans.Class.lift` $ doAnotherThing a b c
        withSomeResource a b useResource handleFailure =
            `State.Lazy.StateT` $ \\s ->
                withSomeResource a b
                    (\\resource ->
                        `State.Lazy.runStateT` (useResource resource) s
                    )
                    (\\failReason metadata ->
                        `State.Lazy.runStateT` (handleFailure failReason metadata) s
                    )

    instance (MonadBusiness m) => MonadBusiness (`Except.ExceptT` s m) where
        doOneThing = `Control.Monad.Trans.Class.lift` doOneThing
        doAnotherThing a b c = `Control.Monad.Trans.Class.lift` $ doAnotherThing a b c
        withSomeResource a b useResource handleFailure =
            `Except.ExceptT` $
                withSomeResource a b
                    (\\resource ->
                        `Except.runExceptT` (useResource resource)
                    )
                    (\\failReason metadata ->
                        `Except.runExceptT` (handleFailure failReason metadata)
                    )
    @
-}
{-** When defining a monad -}
{-| When defining a monad, give it a `Reducible` instance.

    If it is simply a newtype over a @transformers@-stack, just reduce it to
    its representation:

    @
    newtype BusinessT m a
        = BusinessT (ReaderT AppContext (ExceptT AppError m) a)
        deriving newtype (`Functor`, `Applicative`, `Monad`, `Control.Monad.IO.MonadIO`)

    instance `Reducible` (BusinessT m) where
        type `Reduced` (BusinessT m) = ReaderT AppContext (ExceptT AppError m)
    @

    You don't even need to write explicit implementations for `fromReduced` and
    `toReduced`, since their defaults are intended exactly for scenario.

    If it is a something more fancy, try to express it as a `Reader.ReaderT`,
    a `State.Lazy.StateT`, an `Except.ExceptT` or a combination of those.

    If even that is impossible, then make a coercing instance to `Lifting`,
    so that at least functionality like @MonadLogger@ in the example above
    can be forwarded through.

    Even if your monad is not a transformer, but can still be expressed
    as such, you can use that. For example:

    @
    newtype Transaction a
        = Transaction (ReaderT Connection IO a)
        deriving newtype (`Functor`, `Applicative`, `Monad`, `Control.Monad.IO.MonadIO`)

    instance `Reducible` Transaction where
        type `Reduced` Transaction = ReaderT Connection IO
    @ -}
{-* Reduction map -}
{-|
    The built-in reductions made by this library are represented by
    the following figure:

    ![reduction diagram](https://raw.githubusercontent.com/fullstack-development/reducible/v0-1-0/doc/reduction%20diagram.drawio.png)

    Additional notes:

    * @`Identity.IdentityT` m@ is reduced directly to its parameter @m@. If
    @m@ itself is reducible, it continues the chain.

    * @`RWST.CPS.RWST` r w s m@ (CPS) and @`RWST.Lazy.RWST` r w s m@ (lazy) are
    reduced to a combination of transformers:
    @`Reader.ReaderT` r (`State.Lazy.StateT` (s, w)) m@. Since `Reader.ReaderT`
    is now at the top, the next reduction would transform it to `Lifting` of
    only the Reader layer.

    * Strict versions of Writer, State and RWST transformers are coerced to
    lazy. This is because the actual algorithm using them could rely
    on laziness, and transforming it to a strict version could break it.
    Transforming from a strict version to lazy, on the other hand, can only
    degrade performance (by allocating more thunks), but not semantics.

    * Writer (CPS) is coerced directly to State (lazy). Since the internal
    representation of the CPS Writer is already identical to State,
    transforming it through another Writer would only add
    unnesessary conversions.

    * All reduction chains should end with `Lifting`.

    * Certain pure values, which have `Monad` instances in Prelude, get
    \"unpacked\" into transformer chains. These are: @(->)@ as a Reader,
    `Either` and `Maybe` as Excepts, and tuples as Writers. Thus, when
    combining reduction with lifting instances, the instance resolution
    will not terminate at these values, but at `Identity` instead.
-}
{-* Exports -}
      Reducible (..)
    , applyLifting
    , Lifting (..)
    , MonadLifting (..)
    )
where

import Control.Reducible.Internal.TH (chooseInstanceIfMatchingRepr)
import Control.Reducible.Lifting
import Data.Coerce
import Data.Functor.Identity
import Data.Kind
import qualified Control.Monad.Catch.Pure as Catch
import qualified Control.Monad.Trans.Accum as Accum
import qualified Control.Monad.Trans.Cont as Cont
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

{-| An instance of @`Reducible` m@ means that @m@ is a special case of
    another monad @`Reduced` m@; for example, `Writer.Lazy.WriterT`
    is a special case of a `State.Lazy.StateT`.

    In a degenerate case, @m@ and @`Reduced` m@ may be isomorphic; such as
    @`Maybe.MaybeT` m@ and @`Except.ExceptT` () m@.

    The laws:

    1. Generalization is invertible:

        @fromReduced . toReduced === id@

        The reverse is not required to hold: as the generalized form is usually
        a stronger monad than the original one. For example, we generalize
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

    2. `pure` and `(>>=)` of the generalized form must match the original:

        @toReduced . pure = pure@

        @fromReduced (toReduced m >>= toReduced . f) === m >>= f@

        Again, the reverse may not hold in general: the generalized form may
        contain additional context, that the binding operator of the original
        does not account for. For example, `State.Lazy.StateT` expects to see
        the effects of all previous actions in the state on input, but
        `Writer.Lazy.WriterT` doesn't give any means to implement that.

    The default implementation is to `coerce` between the given monad and
    its reduced form. -}
class Reducible (m :: Type -> Type) where
    type Reduced m :: Type -> Type
    fromReduced :: Reduced m a -> m a
    default fromReduced :: (Coercible (Reduced m a) (m a)) => Reduced m a -> m a
    fromReduced = coerce
    toReduced :: m a -> Reduced m a
    default toReduced :: (Coercible (m a) (Reduced m a)) => m a -> Reduced m a
    toReduced = coerce

{-| to @m@ -}
instance Reducible (Identity.IdentityT m) where
    type Reduced (Identity.IdentityT m) =
        m

{-| to @`Lifting` (`Reader.ReaderT` r m) m@ -}
instance Reducible (Reader.ReaderT r m) where
    type Reduced (Reader.ReaderT r m) =
        Lifting (Reader.ReaderT r m) m

{-| to @`Reader.ReaderT` r `Identity`@ -}
instance Reducible ((->) r) where
    type Reduced ((->) r) =
        Reader.ReaderT r Identity

{-| to @`Lifting` (`State.Lazy.StateT` s m) m@ -}
instance Reducible (State.Lazy.StateT s m) where
    type Reduced (State.Lazy.StateT s m) =
        Lifting (State.Lazy.StateT s m) m

{-| strict to lazy -}
instance Reducible (State.Strict.StateT s m) where
    type Reduced (State.Strict.StateT s m) =
        State.Lazy.StateT s m

{-| to @`State.Lazy.StateT` w m@ -}
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
                    fmap (fmap (s <>)) (Writer.CPS.runWriterT asWriterAct)
      |]

{-| to @`State.Lazy.StateT` w m@ -}
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

{-| to @`Reader.ReaderT` r (`State.Lazy.StateT` (s, w) m)@ -}
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

{-| to @`Reader.ReaderT` r (`State.Lazy.StateT` (s, w) m)@ -}
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

{-| strict to lazy -}
instance (Functor m, Monoid w) => Reducible (RWS.Strict.RWST r w s m) where
    type Reduced (RWS.Strict.RWST r w s m) =
        RWS.Lazy.RWST r w s m

{-| to @`State.Lazy.StateT` w m@ -}
instance (Functor m, Monoid w) => Reducible (Writer.Lazy.WriterT w m) where
    type Reduced (Writer.Lazy.WriterT w m) =
        State.Lazy.StateT w m
    fromReduced (State.Lazy.StateT asState) =
        Writer.Lazy.WriterT (asState mempty)
    toReduced (Writer.Lazy.WriterT asWriter) =
        State.Lazy.StateT (\s -> fmap (fmap (s <>)) asWriter)

{-| strict to lazy -}
instance Reducible (Writer.Strict.WriterT w m) where
    type Reduced (Writer.Strict.WriterT w m) =
        Writer.Lazy.WriterT w m

{-| to @`Writer.Lazy.WriterT` w `Identity`@ -}
instance Reducible ((,) w) where
    type Reduced ((,) w) =
        Writer.Lazy.WriterT w Identity
    fromReduced (Writer.Lazy.WriterT (Identity (a, w))) =
        (w, a)
    toReduced (w, a) =
        Writer.Lazy.WriterT (Identity (a, w))

{-| to @(,) (w1, w2)@ -}
instance Reducible ((,,) w1 w2) where
    type Reduced ((,,) w1 w2) = (,) (w1, w2)
    fromReduced ((w1, w2), a) = (w1, w2, a)
    toReduced (w1, w2, a) = ((w1, w2), a)

{-| to @(,) (w1, w2, w3)@ -}
instance Reducible ((,,,) w1 w2 w3) where
    type Reduced ((,,,) w1 w2 w3) = (,) (w1, w2, w3)
    fromReduced ((w1, w2, w3), a) = (w1, w2, w3, a)
    toReduced (w1, w2, w3, a) = ((w1, w2, w3), a)

{-| to @`Lifting` (`Except.ExceptT` e m) m@ -}
instance Reducible (Except.ExceptT e m) where
    type Reduced (Except.ExceptT e m) =
        Lifting (Except.ExceptT e m) m

{-| to @`Except.ExceptT` e `Identity`@ -}
instance Reducible (Either e) where
    type Reduced (Either e) =
        Except.ExceptT e Identity

{-| to @`Except.ExceptT` () m@ -}
instance (Functor m) => Reducible (Maybe.MaybeT m) where
    type Reduced (Maybe.MaybeT m) =
        Except.ExceptT () m
    fromReduced = Maybe.exceptToMaybeT
    toReduced = Maybe.maybeToExceptT ()

{-| to @`Maybe.MaybeT` `Identity`@ -}
instance Reducible Maybe where
    type Reduced Maybe =
        Maybe.MaybeT Identity

{-| to @`Except.ExceptT` Catch.SomeException m@ -}
instance Reducible (Catch.CatchT m) where
    type Reduced (Catch.CatchT m) =
        Except.ExceptT Catch.SomeException m

{-------- others --------}

{-| to @`Lifting` (`Cont.ContT` q m) m@ -}
instance Reducible (Cont.ContT q m) where
    type Reduced (Cont.ContT q m) =
        Lifting (Cont.ContT q m) m
