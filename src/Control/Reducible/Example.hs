{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-| This is the logger/database example from the main module, written here
    to ensure that is actually typechecks and works.
-}
module Control.Reducible.Example
where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Writer.CPS
import Control.Reducible
import Data.IORef
import qualified System.IO as IO

data Connection = Connection

newtype DatabaseQuery r = DatabaseQuery [r]

type Text = String

startQuery ::
    Connection ->
    DatabaseQuery r ->
    IO (IORef [r])
startQuery Connection (DatabaseQuery rs) = do
    newIORef rs

getNextRecordMaybe ::
    Connection ->
    IORef [r] ->
    IO (Maybe r)
getNextRecordMaybe Connection ref = do
    rs <- readIORef ref
    case rs of
        rh : rt -> do
            writeIORef ref rt
            pure (Just rh)
        [] -> do
            pure Nothing

closeQuery ::
    Connection ->
    IORef [r] ->
    IO ()
closeQuery Connection _ref = do
    pure ()

class Monad m => MonadDatabase m where
    runReturningMany ::
        DatabaseQuery r ->
        (m (Maybe r) -> m a) ->
        m a

newtype DatabaseT m a = DatabaseT
    { runDatabaseT :: Connection -> m a
    }
    deriving (Functor, Applicative, Monad, MonadIO)
        via (ReaderT Connection m)
    deriving (MonadTrans)
        via (ReaderT Connection)

instance MonadIO m => MonadDatabase (DatabaseT m) where
    runReturningMany query handler = DatabaseT $ \conn -> do
        queryTag <- liftIO $ startQuery conn query
        result <-
            runDatabaseT
                (handler (liftIO $ getNextRecordMaybe conn queryTag))
                conn
        liftIO $ closeQuery conn queryTag
        pure result

instance Reducible (DatabaseT m) where
    type Reduced (DatabaseT m) =
        ReaderT Connection m
    fromReduced asReader = DatabaseT $ \conn ->
        runReaderT asReader conn
    toReduced asDb = ReaderT $ \conn ->
        runDatabaseT asDb conn

instance MonadDatabase m => MonadDatabase (ReaderT r m) where
    runReturningMany query handler = ReaderT $ \context -> do
        runReturningMany
            query
            (\source ->
                runReaderT (handler (lift source)) context
            )

instance MonadDatabase m => MonadDatabase (StateT s m) where
    runReturningMany query handler = StateT $ \oldState -> do
        runReturningMany
            query
            (\source ->
                runStateT (handler (lift source)) oldState
            )

instance MonadDatabase m => MonadDatabase (ExceptT e m) where
    runReturningMany query handler = ExceptT $ do
        runReturningMany
            query
            (\source ->
                runExceptT (handler (lift source))
            )

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, MonadDatabase (Reduced m)) =>
    MonadDatabase m
  where
    runReturningMany query handler = fromReduced $ do
        runReturningMany
            query
            (\source ->
                toReduced (handler (fromReduced source))
            )

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
    logMessage msg = LoggerT $ \fileHandle -> do
        liftIO $ IO.hPutStrLn fileHandle msg

instance Reducible (LoggerT m) where
    type Reduced (LoggerT m) =
        ReaderT IO.Handle m
    fromReduced asReader = LoggerT $ \fileHandle ->
        runReaderT asReader fileHandle
    toReduced asLogger = ReaderT $ \fileHandle ->
        runLoggerT asLogger fileHandle

instance
    (MonadLifting m n, Monad m, MonadLogger n) =>
    MonadLogger (Lifting m n)
  where
    logMessage msg = applyLifting $ logMessage msg

instance
    {-# OVERLAPPABLE #-}
    (Reducible m, Monad m, MonadLogger (Reduced m)) =>
    MonadLogger m
  where
    logMessage msg = fromReduced $ logMessage msg

sayHello ::
    forall mbase.
    (MonadLogger mbase) =>
    DatabaseT (WriterT Text mbase) ()
sayHello = do
    logMessage
        @(DatabaseT (WriterT Text mbase))
        "Hello"
