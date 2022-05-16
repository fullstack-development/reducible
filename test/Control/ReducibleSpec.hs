{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-do-bind  #-}

module Control.ReducibleSpec
    ( spec
    )
where

{-
:set -itest -package hspec -package QuickCheck
-}

import Control.Monad
import Control.Monad.Trans
import Control.Reducible
import Test.Hspec
import qualified Control.Monad.Catch.Pure as Catch
import qualified Control.Monad.Trans.Accum as Accum
import qualified Control.Monad.Trans.Maybe as Maybe
import qualified Control.Monad.Trans.RWS.CPS as RWS.CPS
import qualified Control.Monad.Trans.RWS.Lazy as RWS.Lazy
import qualified Control.Monad.Trans.RWS.Strict as RWS.Strict
import qualified Control.Monad.Trans.State.Strict as State.Strict
import qualified Control.Monad.Trans.Writer.CPS as Writer.CPS
import qualified Control.Monad.Trans.Writer.Lazy as Writer.Lazy
import qualified Control.Monad.Trans.Writer.Strict as Writer.Strict

newtype Logger a = Logger
    { unwrapLogger :: forall q. [String] -> (a -> [String] -> q) -> q
    }

instance Functor Logger where
    fmap = liftM

instance Applicative Logger where
    pure x = Logger $ \ws k -> k x ws
    (<*>) = ap

instance Monad Logger where
    ma >>= sel = Logger $ \ws1 k ->
        unwrapLogger  ma ws1 $ \x ws2 ->
            unwrapLogger (sel x) ws2 k

writeLog :: String -> Logger ()
writeLog w = Logger $ \ws k -> k () (w : ws)

runLogger :: Logger a -> (a, [String])
runLogger l = unwrapLogger l [] $ \x ws -> (x, reverse ws)

newtype E1 = E1 String
    deriving (Show, Eq)

instance Catch.Exception E1

newtype E2 = E2 String
    deriving (Show, Eq)

instance Catch.Exception E2

spec :: Spec
spec = do
    describe "match bind behavior" $ do
        it "(->) r" $ do
            let fn ask reader local = do
                    a <- ask
                    b <- reader (<> "b")
                    (c, d) <- local (<> "c") $ do
                        c <- ask
                        d <- reader (<> "d")
                        pure (c, d)
                    e <- ask
                    f <- reader (<> "e")
                    pure (a, b, c, d, e, f)
            shouldBe
                (($ "a") $ fromReduced $ do
                    fn
                        (toReduced id)
                        toReduced
                        (\f a -> toReduced $ flip (.) f (fromReduced a))
                )
                (($ "a") $ do
                    fn
                        id
                        id
                        (flip (.))
                )
        it "(,) w" $ do
            let fn tell writer listen pass censor = do
                    tell "a"
                    a <- writer ("b", "c")
                    (b, c) <- listen $ do
                        tell "d"
                        tell "e"
                        pure "f"
                    d <- pass $ do
                        tell "f"
                        tell "g"
                        pure ("h", (<> "i"))
                    censor (<> "j") $ do
                        tell "k"
                        censor (<> "l") $ tell "m"
                        tell "n"
                    tell "o"
                    pure (a, b, c, d)
            let pureTell w = (w, ())
            let pureWriter (a, w) = (w, a)
            let pureListen (w, a) = (w, (a, w))
            let purePass (w, (a, f)) = (f w, a)
            let pureCensor f (w, a) = (f w, a)
            shouldBe
                (fromReduced $
                    fn
                        (toReduced . pureTell)
                        (toReduced . pureWriter)
                        (toReduced . pureListen . fromReduced)
                        (toReduced . purePass . fromReduced)
                        (\f a -> toReduced $
                            pureCensor f (fromReduced a)
                        )
                )
                (fn
                    pureTell
                    pureWriter
                    pureListen
                    purePass
                    pureCensor
                )
        it "(,,) w1 w2" $ do
            let fn tell writer listen pass censor = do
                    tell "a1" "a2"
                    a <- writer ("b", "c1", "c2")
                    (b, c1, c2) <- listen $ do
                        tell "d1" "d2"
                        tell "e1" "e2"
                        pure "f"
                    d <- pass $ do
                        tell "f1" "f2"
                        tell "g1" "g2"
                        pure ("h", (<> "i1"), (<> "i2"))
                    censor (<> "j1") (<> "j2") $ do
                        tell "k1" "k2"
                        censor (<> "l1") (<> "l2") $ tell "m1" "m2"
                        tell "n1" "n2"
                    tell "o1" "o2"
                    pure (a, b, c1, c2, d)
            let pureTell w1 w2 = (w1, w2, ())
            let pureWriter (a, w1, w2) = (w1, w2, a)
            let pureListen (w1, w2, a) = (w1, w2, (a, w1, w2))
            let purePass (w1, w2, (a, f1, f2)) = (f1 w1, f2 w2, a)
            let pureCensor f1 f2 (w1, w2, a) = (f1 w1, f2 w2, a)
            shouldBe
                (fromReduced $
                    fn
                        (\w1 w2 -> toReduced $ pureTell w1 w2)
                        (toReduced . pureWriter)
                        (toReduced . pureListen . fromReduced)
                        (toReduced . purePass . fromReduced)
                        (\f1 f2 a -> toReduced $
                            pureCensor f1 f2 (fromReduced a)
                        )
                )
                (fn
                    pureTell
                    pureWriter
                    pureListen
                    purePass
                    pureCensor
                )
        it "(,,) w1 w2 w3" $ do
            let fn tell writer listen pass censor = do
                    tell "a1" "a2" "a3"
                    a <- writer ("b", "c1", "c2", "c3")
                    (b, c1, c2, c3) <- listen $ do
                        tell "d1" "d2" "d3"
                        tell "e1" "e2" "e3"
                        pure "f"
                    d <- pass $ do
                        tell "f1" "f2" "f3"
                        tell "g1" "g2" "g3"
                        pure ("h", (<> "i1"), (<> "i2"), (<> "i3"))
                    censor (<> "j1") (<> "j2") (<> "j3") $ do
                        tell "k1" "k2" "k3"
                        censor (<> "l1") (<> "l2") (<> "l3") $ do
                            tell "m1" "m2" "m3"
                        tell "n1" "n2" "n3"
                    tell "o1" "o2" "o3"
                    pure (a, b, c1, c2, c3, d)
            let pureTell w1 w2 w3 = (w1, w2, w3, ())
            let pureWriter (a, w1, w2, w3) = (w1, w2, w3, a)
            let pureListen (w1, w2, w3, a) = (w1, w2, w3, (a, w1, w2, w3))
            let purePass (w1, w2, w3, (a, f1, f2, f3)) =
                    (f1 w1, f2 w2, f3 w3, a)
            let pureCensor f1 f2 f3 (w1, w2, w3, a) =
                    (f1 w1, f2 w2, f3 w3, a)
            shouldBe
                (fromReduced $
                    fn
                        (\w1 w2 w3 -> toReduced $ pureTell w1 w2 w3)
                        (toReduced . pureWriter)
                        (toReduced . pureListen . fromReduced)
                        (toReduced . purePass . fromReduced)
                        (\f1 f2 f3 a -> toReduced $
                            pureCensor f1 f2 f3 (fromReduced a)
                        )
                )
                (fn
                    pureTell
                    pureWriter
                    pureListen
                    purePass
                    pureCensor
                )
        it "AccumT" $ do
            let fn wlog look add accum = do
                    look >>= wlog
                    add "a"
                    accum (\w -> (w, "b")) >>= wlog
                    add "c"
                    look >>= wlog
                    add "d"
            shouldBe
                (runLogger $ do
                    flip Accum.runAccumT "" $ fromReduced $
                        fn
                            (lift . writeLog)
                            (toReduced Accum.look)
                            (toReduced . Accum.add)
                            (toReduced . Accum.accum)
                )
                (runLogger $ do
                    flip Accum.runAccumT "" $
                        fn
                            (lift . writeLog)
                            Accum.look
                            Accum.add
                            Accum.accum
                )
        describe "StateT" $ do
            let fn wlog get put modify state = do
                    get >>= wlog
                    put "a"
                    get >>= wlog
                    modify (<> "b")
                    get >>= wlog
                    state (\s -> (s <> "c", s <> "d")) >>= wlog
                    get >>= wlog
            it "(Strict)" $ do
                shouldBe
                    (runLogger $ do
                        flip State.Strict.runStateT "" $ fromReduced $ do
                            fn
                                (lift . writeLog)
                                (toReduced State.Strict.get)
                                (toReduced . State.Strict.put)
                                (toReduced . State.Strict.modify)
                                (toReduced . State.Strict.state)
                    )
                    (runLogger $ do
                        flip State.Strict.runStateT "" $ do
                            fn
                                (lift . writeLog)
                                State.Strict.get
                                State.Strict.put
                                State.Strict.modify
                                State.Strict.state
                    )
        describe "WriterT" $ do
            let fn wlog tell writer listen pass censor = do
                    tell "a"
                    writer ("b", "c") >>= wlog
                    (a, b) <- listen $ do
                        tell "d"
                        tell "e"
                        pure "f"
                    wlog a
                    wlog b
                    c <- pass $ do
                        tell "f"
                        tell "g"
                        pure ("h", (<> "i"))
                    wlog c
                    censor (<> "j") $ do
                        tell "k"
                        censor (<> "l") $ tell "m"
                        tell "n"
                    tell "o"
            it "(CPS)" $ do
                shouldBe
                    (runLogger $ do
                        Writer.CPS.runWriterT $ fromReduced $
                            fn
                                (lift . writeLog)
                                (toReduced . Writer.CPS.tell)
                                (toReduced . Writer.CPS.writer)
                                (toReduced . Writer.CPS.listen . fromReduced)
                                (toReduced . Writer.CPS.pass . fromReduced)
                                (\f a -> toReduced $
                                    Writer.CPS.censor f (fromReduced a)
                                )
                    )
                    (runLogger $ do
                        Writer.CPS.runWriterT $
                            fn
                                (lift . writeLog)
                                Writer.CPS.tell
                                Writer.CPS.writer
                                Writer.CPS.listen
                                Writer.CPS.pass
                                Writer.CPS.censor
                    )
            it "(Lazy)" $ do
                shouldBe
                    (runLogger $ do
                        Writer.Lazy.runWriterT $ fromReduced $
                            fn
                                (lift . writeLog)
                                (toReduced . Writer.Lazy.tell)
                                (toReduced . Writer.Lazy.writer)
                                (toReduced . Writer.Lazy.listen . fromReduced)
                                (toReduced . Writer.Lazy.pass . fromReduced)
                                (\f a -> toReduced $
                                    Writer.Lazy.censor f (fromReduced a)
                                )
                    )
                    (runLogger $ do
                        Writer.Lazy.runWriterT $
                            fn
                                (lift . writeLog)
                                Writer.Lazy.tell
                                Writer.Lazy.writer
                                Writer.Lazy.listen
                                Writer.Lazy.pass
                                Writer.Lazy.censor
                    )
            it "(Strict)" $ do
                shouldBe
                    (runLogger $ do
                        Writer.Strict.runWriterT $ fromReduced $
                            fn
                                (lift . writeLog)
                                (toReduced . Writer.Strict.tell)
                                (toReduced . Writer.Strict.writer)
                                (toReduced . Writer.Strict.listen . fromReduced)
                                (toReduced . Writer.Strict.pass . fromReduced)
                                (\f a -> toReduced $
                                    Writer.Strict.censor f (fromReduced a)
                                )
                    )
                    (runLogger $ do
                        Writer.Strict.runWriterT $
                            fn
                                (lift . writeLog)
                                Writer.Strict.tell
                                Writer.Strict.writer
                                Writer.Strict.listen
                                Writer.Strict.pass
                                Writer.Strict.censor
                    )
        describe "RWST" $ do
            let fn
                    wlog
                    tell writer listen pass censor
                    ask reader local
                    get put modify state
                  = do
                    ask >>= wlog
                    get >>= wlog
                    tell "wa"
                    writer ("wb", "wc") >>= wlog
                    modify (<> "sa")
                    (a, b) <- listen $ do
                        tell "wd"
                        modify (<> "sb")
                        ask >>= wlog
                        tell "we"
                        c2 <- local (<> "ra") $ do
                            (a2, b2) <- do
                                ask >>= wlog
                                listen $ do
                                    tell "wd2"
                                    state (\s -> (s <> "sa2", s <> "sb2")) >>= wlog
                                    ask >>= wlog
                                    tell "we2"
                                    pure "wf2"
                            wlog a2
                            wlog b2
                            pure "wg2"
                        wlog c2
                        reader (<> "rb") >>= wlog
                        get >>= wlog
                        pure "wf"
                    wlog a
                    wlog b
                    modify (<> "sc")
                    ask >>= wlog
                    get >>= wlog
                    put "sd"
                    ask >>= wlog
                    get >>= wlog
                    c <- local (<> "rc") $ do
                        pass $ do
                            tell "wf"
                            get >>= wlog
                            tell "wg"
                            ask >>= wlog
                            pure ("wh", (<> "wi"))
                    wlog c
                    censor (<> "wj") $ do
                        tell "wk"
                        censor (<> "wl") $ do
                            modify (<> "se")
                            get >>= wlog
                            tell "wm"
                        tell "wn"
                    tell "wo"
                    ask >>= wlog
                    get >>= wlog
            it "(CPS)" $ do
                shouldBe
                    (runLogger $ do
                        (\a -> RWS.CPS.runRWST a "a" "b") $ fromReduced $
                            fn
                                (lift . lift . writeLog)
                                (toReduced . RWS.CPS.tell)
                                (toReduced . RWS.CPS.writer)
                                (toReduced . RWS.CPS.listen . fromReduced)
                                (toReduced . RWS.CPS.pass . fromReduced)
                                (\f a -> toReduced $
                                    RWS.CPS.censor f (fromReduced a)
                                )
                                (toReduced RWS.CPS.ask)
                                (toReduced . RWS.CPS.reader)
                                (\f a -> toReduced $
                                    RWS.CPS.local f (fromReduced a)
                                )
                                (toReduced RWS.CPS.get)
                                (toReduced . RWS.CPS.put)
                                (toReduced . RWS.CPS.modify)
                                (toReduced . RWS.CPS.state)
                    )
                    (runLogger $ do
                        (\a -> RWS.CPS.runRWST a "a" "b") $
                            fn
                                (lift . writeLog)
                                RWS.CPS.tell
                                RWS.CPS.writer
                                RWS.CPS.listen
                                RWS.CPS.pass
                                RWS.CPS.censor
                                RWS.CPS.ask
                                RWS.CPS.reader
                                RWS.CPS.local
                                RWS.CPS.get
                                RWS.CPS.put
                                RWS.CPS.modify
                                RWS.CPS.state
                    )
            it "(Lazy)" $ do
                shouldBe
                    (runLogger $ do
                        (\a -> RWS.Lazy.runRWST a "a" "b") $ fromReduced $
                            fn
                                (lift . lift . writeLog)
                                (toReduced . RWS.Lazy.tell)
                                (toReduced . RWS.Lazy.writer)
                                (toReduced . RWS.Lazy.listen . fromReduced)
                                (toReduced . RWS.Lazy.pass . fromReduced)
                                (\f a -> toReduced $
                                    RWS.Lazy.censor f (fromReduced a)
                                )
                                (toReduced RWS.Lazy.ask)
                                (toReduced . RWS.Lazy.reader)
                                (\f a -> toReduced $
                                    RWS.Lazy.local f (fromReduced a)
                                )
                                (toReduced RWS.Lazy.get)
                                (toReduced . RWS.Lazy.put)
                                (toReduced . RWS.Lazy.modify)
                                (toReduced . RWS.Lazy.state)
                    )
                    (runLogger $ do
                        (\a -> RWS.Lazy.runRWST a "a" "b") $
                            fn
                                (lift . writeLog)
                                RWS.Lazy.tell
                                RWS.Lazy.writer
                                RWS.Lazy.listen
                                RWS.Lazy.pass
                                RWS.Lazy.censor
                                RWS.Lazy.ask
                                RWS.Lazy.reader
                                RWS.Lazy.local
                                RWS.Lazy.get
                                RWS.Lazy.put
                                RWS.Lazy.modify
                                RWS.Lazy.state
                    )
            it "(Strict)" $ do
                shouldBe
                    (runLogger $ do
                        (\a -> RWS.Strict.runRWST a "a" "b") $ fromReduced $
                            fn
                                (lift . lift . writeLog)
                                (toReduced . RWS.Strict.tell)
                                (toReduced . RWS.Strict.writer)
                                (toReduced . RWS.Strict.listen . fromReduced)
                                (toReduced . RWS.Strict.pass . fromReduced)
                                (\f a -> toReduced $
                                    RWS.Strict.censor f (fromReduced a)
                                )
                                (toReduced RWS.Strict.ask)
                                (toReduced . RWS.Strict.reader)
                                (\f a -> toReduced $
                                    RWS.Strict.local f (fromReduced a)
                                )
                                (toReduced RWS.Strict.get)
                                (toReduced . RWS.Strict.put)
                                (toReduced . RWS.Strict.modify)
                                (toReduced . RWS.Strict.state)
                    )
                    (runLogger $ do
                        (\a -> RWS.Strict.runRWST a "a" "b") $
                            fn
                                (lift . writeLog)
                                RWS.Strict.tell
                                RWS.Strict.writer
                                RWS.Strict.listen
                                RWS.Strict.pass
                                RWS.Strict.censor
                                RWS.Strict.ask
                                RWS.Strict.reader
                                RWS.Strict.local
                                RWS.Strict.get
                                RWS.Strict.put
                                RWS.Strict.modify
                                RWS.Strict.state
                    )
        it "Maybe" $ do
            let fn throwNothing catchNothing = do
                    {- no exception -}
                    a <- catchNothing
                        (pure "b")
                        (pure "d")
                    {- simple exception -}
                    b <- catchNothing
                        (throwNothing >> pure "g")
                        (pure "i")
                    {- nested exception -}
                    c <- catchNothing
                        (do
                            catchNothing
                                (throwNothing >> pure "l")
                                (throwNothing >> pure "n")
                            pure "p"
                        )
                        (pure "r")
                    {- exception in catch block -}
                    d <- catchNothing
                        (throwNothing >> pure "s")
                        (do
                            catchNothing
                                (throwNothing >> pure "v")
                                (pure "x")
                            pure "z"
                        )
                    pure (a, b, c, d)
            let mtThrowNothing = Nothing
            let mtCatchNothing a h = do
                    case a of
                        Just x -> Just x
                        Nothing -> h
            shouldBe
                (fromReduced $
                    fn
                        (toReduced mtThrowNothing)
                        (\a h ->
                            toReduced $
                                mtCatchNothing
                                    (fromReduced a)
                                    (fromReduced h))
                )
                (fn
                    mtThrowNothing
                    mtCatchNothing
                )
        it "MaybeT" $ do
            let fn wlog throwNothing catchNothing = do
                    wlog "a"
                    {- no exception -}
                    catchNothing
                        (wlog "a" >> pure "b")
                        (wlog "c" >> pure "d")
                        >>= wlog
                    {- simple exception -}
                    catchNothing
                        (do
                            wlog "e"
                            throwNothing
                            wlog "f"
                            pure "g"
                        )
                        (wlog "h" >> pure "i")
                        >>= wlog
                    {- nested exception -}
                    catchNothing
                        (do
                            wlog "j"
                            catchNothing
                                (do
                                    wlog "k"
                                    throwNothing
                                    pure "l"
                                )
                                (do
                                    wlog "m"
                                    throwNothing
                                    pure "n"
                                )
                                >>= wlog
                            wlog "o"
                            pure "p"
                        )
                        (wlog "q" >> pure "r")
                        >>= wlog
                    {- exception in catch block -}
                    catchNothing
                        (do
                            throwNothing
                            pure "s"
                        )
                        (do
                            wlog "t"
                            catchNothing
                                (do
                                    wlog "u"
                                    throwNothing
                                    pure "v"
                                )
                                (do
                                    wlog "w"
                                    pure "x"
                                )
                                >>= wlog
                            wlog "y"
                            pure "z"
                        )
                        >>= wlog
            let mtThrowNothing = Maybe.MaybeT $ do
                    pure Nothing
            let mtCatchNothing a h = Maybe.MaybeT $ do
                    mr <- Maybe.runMaybeT a
                    case mr of
                        Just x -> pure (Just x)
                        Nothing -> Maybe.runMaybeT h
            shouldBe
                (runLogger $ do
                    Maybe.runMaybeT $ fromReduced $
                        fn
                            (lift . writeLog)
                            (toReduced mtThrowNothing)
                            (\a h ->
                                toReduced $
                                    mtCatchNothing
                                        (fromReduced a)
                                        (fromReduced h))
                )
                (runLogger $ do
                    Maybe.runMaybeT $
                        fn
                            (lift . writeLog)
                            mtThrowNothing
                            mtCatchNothing
                )
        it "CatchT" $ do
            let fn ::
                    (Monad m) =>
                    (String -> m ()) ->
                    (forall e x. (Catch.Exception e) => e -> m x) ->
                    (forall e a. (Catch.Exception e) => m a -> (e -> m a) -> m a) ->
                    m ()
                fn wlog throwM catchM = do
                    wlog "a"
                    {- no exception -}
                    catchM
                        (wlog "a" >> pure "b")
                        (\(E1 ex) -> wlog "c" >> wlog ex >> pure "d")
                        >>= wlog
                    {- simple exception -}
                    catchM
                        (do
                            wlog "e"
                            throwM (E1 "xa")
                            wlog "f"
                            pure "g"
                        )
                        (\(E1 ex) -> wlog "h" >> wlog ex >> pure "i")
                        >>= wlog
                    {- nested exception -}
                    catchM
                        (do
                            wlog "j"
                            catchM
                                (do
                                    wlog "k"
                                    throwM (E1 "xb")
                                    pure "l"
                                )
                                (\(E1 ex) -> do
                                    wlog "m"
                                    wlog ex
                                    throwM (E1 "xc")
                                    pure "n"
                                )
                                >>= wlog
                            wlog "o"
                            pure "p"
                        )
                        (\(E1 ex) -> wlog "q" >> wlog ex >> pure "r")
                        >>= wlog
                    {- exception in catch block -}
                    catchM
                        (do
                            throwM (E1 "xd")
                            pure "s"
                        )
                        (\(E1 ex) -> do
                            wlog "t"
                            wlog ex
                            catchM
                                (do
                                    wlog "u"
                                    throwM (E1 "xe")
                                    pure "v"
                                )
                                (\(E1 ex2) -> do
                                    wlog "w"
                                    wlog ex2
                                    pure "x"
                                )
                                >>= wlog
                            wlog "y"
                            pure "z"
                        )
                        >>= wlog
                    {- different types of exceptions -}
                    catchM
                        (do
                            wlog "aa"
                            catchM
                                (do
                                    wlog "ab"
                                    throwM (E2 "xf")
                                    pure "ac"
                                )
                                (\(E1 ex) -> do
                                    wlog "ad"
                                    wlog ex
                                    pure "ae"
                                )
                                >>= wlog
                            wlog "af"
                            pure "ag"
                        )
                        (\(E2 ex) -> wlog "ah" >> wlog ex >> pure "ai")
                        >>= wlog
            shouldBe
                (snd $ runLogger $ do
                    Catch.runCatchT $ fromReduced $
                        fn
                            (lift . writeLog)
                            (toReduced . Catch.throwM @(Catch.CatchT Logger))
                            (\a h ->
                                toReduced $
                                    Catch.catch @(Catch.CatchT Logger)
                                        (fromReduced a)
                                        (fromReduced . h))
                )
                (snd $ runLogger $ do
                    Catch.runCatchT $
                        fn
                            (lift . writeLog)
                            Catch.throwM
                            Catch.catch
                )
        it "Either" $ do
            let fn ::
                    (Monad m) =>
                    (forall x. String -> m x) ->
                    (forall a. m a -> (String -> m a) -> m a) ->
                    m (String, String, String, String)
                fn throwM catchM = do
                    {- no exception -}
                    a <- catchM
                        (pure "b")
                        (\ex -> pure (ex <> "-d"))
                    {- simple exception -}
                    b <- catchM
                        (do
                            throwM "xa"
                            pure "g"
                        )
                        (\ex -> pure (ex <> "-i"))
                    {- nested exception -}
                    c <- catchM
                        (do
                            d <- catchM
                                (do
                                    throwM "xb"
                                    pure "l"
                                )
                                (\ex -> do
                                    throwM (ex <> "-xc")
                                    pure (ex <> "-n")
                                )
                            pure (d <> "-p")
                        )
                        (\ex -> pure (ex <> "-r"))
                    {- exception in catch block -}
                    e <- catchM
                        (do
                            throwM "xd"
                            pure "s"
                        )
                        (\ex -> do
                            f <- catchM
                                (do
                                    throwM (ex <> "-xe")
                                    pure (ex <> "-v")
                                )
                                (\ex2 -> do
                                    pure (ex <> "|" <> ex2 <> "-x")
                                )
                            pure (f <> "-z")
                        )
                    pure (a, b, c, e)
            let pureThrowM e = Left e
            let pureCatchM a h =
                    case a of
                        Right x -> Right x
                        Left ex -> h ex
            shouldBe
                (fromReduced $
                    fn
                        (toReduced . pureThrowM)
                        (\a h ->
                            toReduced $
                                pureCatchM
                                    (fromReduced a)
                                    (fromReduced . h))
                )
                (fn
                    pureThrowM
                    pureCatchM
                )
