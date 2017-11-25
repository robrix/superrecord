{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
module SuperRecord.Internal where

import SuperRecord.Field

import Control.DeepSeq
import Data.Aeson
import Data.Aeson.Types (Parser)
import Data.Constraint
import Data.Proxy
import GHC.Base (Int(..), Any)
import GHC.IO ( IO(..) )
import GHC.Prim
import GHC.TypeLits
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Text as T

-- | Internal record type. When manually writing an explicit type signature for
-- a record, use 'Record' instead. For abstract type signatures 'Rec' will work
-- well.
data Rec (lts :: [*])
   = Rec
   {
#ifndef JS_RECORD
       _unRec :: SmallArray# Any -- Note that the values are physically in reverse order
#else
       _unRec :: !JS.Object
#endif
   }

instance (RecApply lts lts Show) => Show (Rec lts) where
    show = show . showRec

instance RecEq lts lts => Eq (Rec lts) where
    (==) (a :: Rec lts) (b :: Rec lts) = recEq a b (Proxy :: Proxy lts)
    {-# INLINE (==) #-}

instance
    ( RecApply lts lts ToJSON
    ) => ToJSON (Rec lts) where
    toJSON = recToValue
    toEncoding = recToEncoding

instance (RecSize lts ~ s, KnownNat s, RecJsonParse lts) => FromJSON (Rec lts) where
    parseJSON = recJsonParser

instance RecNfData lts lts => NFData (Rec lts) where
    rnf = recNfData (Proxy :: Proxy lts)

-- | An empty record with an initial size for the record
unsafeRnil :: Int -> Rec '[]
#ifndef JS_RECORD
unsafeRnil (I# n#) =
    unsafePerformIO $! IO $ \s# ->
    case newSmallArray# n# (error "No Value") s# of
      (# s'#, arr# #) ->
          case unsafeFreezeSmallArray# arr# s'# of
            (# s''#, a# #) -> (# s''# , Rec a# #)
#else
unsafeRnil _ =
    unsafePerformIO $! Rec <$> JS.create
#endif
{-# INLINE unsafeRnil #-}

-- | Prepend a record entry to a record 'Rec'. Assumes that the record was created with
-- 'unsafeRnil' and still has enough free slots, mutates the original 'Rec' which should
-- not be reused after
unsafeRCons ::
    forall l t lts s.
    ( RecSize lts ~ s
    , KnownNat s
    , KeyDoesNotExist l lts
#ifdef JS_RECORD
    , ToJSVal t
#endif
    )
    => l := t -> Rec lts -> Rec (l := t ': lts)

#ifndef JS_RECORD
unsafeRCons (_ := val) (Rec vec#) =
    unsafePerformIO $! IO $ \s# ->
    case unsafeThawSmallArray# vec# s# of
      (# s'#, arr# #) ->
          case writeSmallArray# arr# size# (unsafeCoerce# val) s'# of
            s''# ->
                case unsafeFreezeSmallArray# arr# s''# of
                  (# s'''#, a# #) -> (# s'''#, Rec a# #)
    where
        !(I# size#) = fromIntegral $ natVal' (proxy# :: Proxy# s)
#else
unsafeRCons (lbl := val) (Rec obj) =
    Rec $! unsafePerformIO $!
    do val' <- toJSVal val
       JS.unsafeSetProp (JSS.pack $ symbolVal lbl) val' obj
       pure obj
#endif
{-# INLINE unsafeRCons #-}

type family KeyDoesNotExist (l :: Symbol) (lts :: [*]) :: Constraint where
    KeyDoesNotExist l '[] = 'True ~ 'True
    KeyDoesNotExist l (l := t ': lts) =
        TypeError
        ( 'Text "Duplicate key " ':<>: 'Text l
        )
    KeyDoesNotExist q (l := t ': lts) = KeyDoesNotExist q lts

type family RecSize (lts :: [*]) :: Nat where
    RecSize '[] = 0
    RecSize (l := t ': lts) = 1 + RecSize lts

type RecVecIdxPos l lts = RecSize lts - RecTyIdxH 0 l lts - 1

type family RecTyIdxH (i :: Nat) (l :: Symbol) (lts :: [*]) :: Nat where
    RecTyIdxH idx l (l := t ': lts) = idx
    RecTyIdxH idx m (l := t ': lts) = RecTyIdxH (1 + idx) m lts
    RecTyIdxH idx m '[] =
        TypeError
        ( 'Text "Could not find label "
          ':<>: 'Text m
        )

type family RecTy (l :: Symbol) (lts :: [*]) :: k where
    RecTy l (l := t ': lts) = t
    RecTy q (l := t ': lts) = RecTy q lts

-- | Require a record to contain a label
type Has l lts v =
   ( RecTy l lts ~ v
   , KnownNat (RecSize lts)
   , KnownNat (RecVecIdxPos l lts)
#ifdef JS_RECORD
   , KnownSymbol l, FromJSVal v, ToJSVal v
#endif
   )

-- | Get an existing record field
get ::
    forall l v lts.
    ( Has l lts v
    )
    => FldProxy l -> Rec lts -> v
#ifndef JS_RECORD
get _ (Rec vec#) =
    let !(I# readAt#) =
            fromIntegral (natVal' (proxy# :: Proxy# (RecVecIdxPos l lts)))
        anyVal :: Any
        anyVal =
           case indexSmallArray# vec# readAt# of
             (# a# #) -> a#
    in unsafeCoerce# anyVal
#else
get lbl (Rec obj) =
    unsafePerformIO $!
    do r <- JS.unsafeGetProp (JSS.pack $ symbolVal lbl) obj
       fromJSValUnchecked r
#endif
{-# INLINE get #-}

-- | Apply a function to each key element pair for a record
reflectRec ::
    forall c r lts. (RecApply lts lts c)
    => Proxy c
    -> (forall a. c a => String -> a -> r)
    -> Rec lts
    -> [r]
reflectRec _ f r =
    reverse $
    recApply (\(Dict :: Dict (c a)) s v xs -> (f s v : xs)) r (Proxy :: Proxy lts) []
{-# INLINE reflectRec #-}

-- | Convert all elements of a record to a 'String'
showRec :: forall lts. (RecApply lts lts Show) => Rec lts -> [(String, String)]
showRec = reflectRec @Show Proxy (\k v -> (k, show v))

recToValue :: forall lts. (RecApply lts lts ToJSON) => Rec lts -> Value
recToValue r = object $ reflectRec @ToJSON Proxy (\k v -> (T.pack k, toJSON v)) r

recToEncoding :: forall lts. (RecApply lts lts ToJSON) => Rec lts -> Encoding
recToEncoding r = pairs $ mconcat $ reflectRec @ToJSON Proxy (\k v -> (T.pack k .= v)) r

recJsonParser :: forall lts s. (RecSize lts ~ s, KnownNat s, RecJsonParse lts) => Value -> Parser (Rec lts)
recJsonParser =
    withObject "Record" $ \o ->
    recJsonParse initSize o
    where
        initSize = fromIntegral $ natVal' (proxy# :: Proxy# s)

-- | Machinery needed to implement 'reflectRec'
class RecApply (rts :: [*]) (lts :: [*]) c where
    recApply :: (forall a. Dict (c a) -> String -> a -> b -> b) -> Rec rts -> Proxy lts -> b -> b

instance RecApply rts '[] c where
    recApply _ _ _ b = b

instance
    ( KnownSymbol l
    , RecApply rts (RemoveAccessTo l lts) c
    , Has l rts v
    , c v
    ) => RecApply rts (l := t ': lts) c where
    recApply f r (_ :: Proxy (l := t ': lts)) b =
        let lbl :: FldProxy l
            lbl = FldProxy
            val = get lbl r
            res = f Dict (symbolVal lbl) val b
            pNext :: Proxy (RemoveAccessTo l (l := t ': lts))
            pNext = Proxy
        in recApply f r pNext res

-- | Machinery to implement equality
class RecEq (rts :: [*]) (lts :: [*]) where
    recEq :: Rec rts -> Rec rts -> Proxy lts -> Bool

instance RecEq rts '[] where
    recEq _ _ _ = True

instance
    ( RecEq rts (RemoveAccessTo l lts)
    , Has l rts v
    , Eq v
    ) => RecEq rts (l := t ': lts) where
    recEq r1 r2 (_ :: Proxy (l := t ': lts)) =
      let lbl :: FldProxy l
          lbl = FldProxy
          val = get lbl r1
          val2 = get lbl r2
          res = val == val2
          pNext :: Proxy (RemoveAccessTo l (l := t ': lts))
          pNext = Proxy
      in res && recEq r1 r2 pNext

type family RemoveAccessTo (l :: Symbol) (lts :: [*]) :: [*] where
    RemoveAccessTo l (l := t ': lts) = RemoveAccessTo l lts
    RemoveAccessTo q (l := t ': lts) = (l := t ': RemoveAccessTo l lts)
    RemoveAccessTo q '[] = '[]

-- | Machinery to implement parseJSON
class RecJsonParse (lts :: [*]) where
    recJsonParse :: Int -> Object -> Parser (Rec lts)

instance RecJsonParse '[] where
    recJsonParse initSize _ = pure (unsafeRnil initSize)

instance
    ( KnownSymbol l, FromJSON t, RecJsonParse lts
    , RecSize lts ~ s, KnownNat s, KeyDoesNotExist l lts
#ifdef JS_RECORD
    , ToJSVal t
#endif
    ) => RecJsonParse (l := t ': lts) where
    recJsonParse initSize obj =
        do let lbl :: FldProxy l
               lbl = FldProxy
           (v :: t) <- obj .: T.pack (symbolVal lbl)
           rest <- recJsonParse initSize obj
           pure $ unsafeRCons (lbl := v) rest

-- | Machinery for NFData
class RecNfData (lts :: [*]) (rts :: [*]) where
    recNfData :: Proxy lts -> Rec rts -> ()

instance RecNfData '[] rts where
    recNfData _ _ = ()

instance
    ( Has l rts v
    , NFData v
    , RecNfData (RemoveAccessTo l lts) rts
    ) => RecNfData (l := t ': lts) rts where
    recNfData (_ :: (Proxy (l := t ': lts))) r =
        let !v = get (FldProxy :: FldProxy l) r
            pNext :: Proxy (RemoveAccessTo l (l := t ': lts))
            pNext = Proxy
        in deepseq v (recNfData pNext r)

#ifdef JS_RECORD
instance ToJSVal (Rec x) where
    toJSVal (Rec (JS.Object obj)) = pure obj

instance FromJSVal (Rec x) where
    fromJSVal jv = pure (Just $ Rec $ JS.Object jv) -- TODO: implement checking!!
#endif
