module Control.Reducible.Internal.TH
    ( chooseInstanceIfMatchingRepr
    )
where

import Control.Monad
import Language.Haskell.TH
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Strict as Map

zipWithStrict_ ::
    (MonadPlus m) =>
    (a -> b -> m ()) ->
    [a] ->
    [b] ->
    m ()
zipWithStrict_ fn (x : xs) (y : ys) =
    fn x y >> zipWithStrict_ fn xs ys
zipWithStrict_ _ [] [] =
    pure ()
zipWithStrict_ _ _ _ =
    mzero

isMatchingRepr :: Info -> Info -> Bool
isMatchingRepr infoA infoB = do
    case State.runStateT (goInfo infoA infoB) Map.empty of
        Nothing -> False
        Just ((), _) -> True
  where
    goInfo (TyConI declA) (TyConI declB) = do
        goDecl declA declB
    goInfo _ _ = do
        mzero
    goDecl
        (NewtypeD _ _ paramsA _ conA _)
        (NewtypeD _ _ paramsB _ conB _)
      = do
        zipWithStrict_ goParam paramsA paramsB
        goCon conA conB
    goDecl _ _ = do
        mzero
    goParam (KindedTV nameA kindA) (KindedTV nameB kindB) = do
        goType kindA kindB
        State.modify' (Map.insert nameA nameB)
    goParam _ _ = do
        mzero
    goType ArrowT ArrowT = do
        pure ()
    goType StarT StarT = do
        pure ()
    goType (AppT funA argA) (AppT funB argB) = do
        goType funA funB
        goType argA argB
    goType (VarT varA) (VarT varB) = do
        varAImage <- State.gets (Map.lookup varA)
        guard (varAImage == Just varB)
    goType (TupleT nA) (TupleT nB) = do
        guard (nA == nB)
    goType _ _ = do
        mzero
    goCon (NormalC _ fieldsA) (NormalC _ fieldsB) = do
        zipWithStrict_
            goField
            fieldsA
            fieldsB
    goCon (RecC _ recFieldsA) (NormalC _ fieldsB) = do
        zipWithStrict_
            goField
            (map stripFieldName recFieldsA)
            fieldsB
    goCon (NormalC _ fieldsA) (RecC _ recFieldsB) = do
        zipWithStrict_
            goField
            fieldsA
            (map stripFieldName recFieldsB)
    goCon (RecC _ recFieldsA) (RecC _ recFieldsB) = do
        zipWithStrict_
            goField
            (map stripFieldName recFieldsA)
            (map stripFieldName recFieldsB)
    goCon _ _ = do
        mzero
    goField (bangA, typeA) (bangB, typeB) = do
        goBang bangA bangB
        goType typeA typeB
    goBang ba bb = do
        guard (ba == bb)
    stripFieldName (_, b, t) = (b, t)

chooseInstanceIfMatchingRepr ::
    Name ->
    Name ->
    DecsQ ->
    DecsQ ->
    DecsQ
chooseInstanceIfMatchingRepr nameA nameB onMatch onDiff = do
    infoA <- reify nameA
    infoB <- reify nameB
    if isMatchingRepr infoA infoB
        then do
            onMatch
        else do
            reportWarning $
                "Internal representation for " <> show nameA <> " \
                \differs from the expected,\n\
                \falling back to a default instance implementation"
            onDiff
