{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
module SuperRecord.Unsorted
    ( -- * Basics
      Record, rcons, (&)
    , combine, (++:)
    , module S
    ) where

import SuperRecord as S hiding (Record, rcons, (&), combine, (++:), Sort)
import SuperRecord.Internal

import GHC.Base (Int(..))
import GHC.IO ( IO(..) )
import GHC.Prim
import GHC.TypeLits
import System.IO.Unsafe (unsafePerformIO)

-- | A synonym for the core record type, exported for consistency.
type Record = Rec

rcons, (&) ::
    forall l t lts s.
    ( RecSize lts ~ s, KnownNat s
    , KeyDoesNotExist l lts
#ifdef JS_RECORD
    , ToJSVal t
#endif
    )
    => l := t -> Rec lts -> Rec (l := t ': lts)

#ifndef JS_RECORD
rcons (_ := val) (Rec vec#) =
    unsafePerformIO $! IO $ \s# ->
    case newSmallArray# newSize# (error "No value") s# of
      (# s'#, arr# #) ->
          case copySmallArray# vec# 0# arr# 0# size# s'# of
            s''# ->
                case writeSmallArray# arr# size# (unsafeCoerce# val) s''# of
                  s'''# ->
                      case unsafeFreezeSmallArray# arr# s'''# of
                        (# s''''#, a# #) -> (# s''''#, Rec a# #)
    where
        !(I# newSize#) = size + 1
        !(I# size#) = size
        size = fromIntegral $ natVal' (proxy# :: Proxy# s)
#else
rcons (lbl := val) (Rec obj) =
    Rec $! unsafePerformIO $!
    do obj' <- copyObject obj
       val' <- toJSVal val
       JS.unsafeSetProp (JSS.pack $ symbolVal lbl) val' obj'
       pure obj'
#endif
{-# INLINE rcons #-}

(&) = rcons
{-# INLINE (&) #-}

-- | Combine two records
combine, (++:) ::
    forall lhs rhs.
    (KnownNat (RecSize lhs), KnownNat (RecSize rhs), KnownNat (RecSize lhs + RecSize rhs))
    => Rec lhs
    -> Rec rhs
    -> Rec (RecAppend lhs rhs)

#ifndef JS_RECORD
combine (Rec l#) (Rec r#) =
    let !(I# sizeL#) = fromIntegral $ natVal' (proxy# :: Proxy# (RecSize lhs))
        !(I# sizeR#) = fromIntegral $ natVal' (proxy# :: Proxy# (RecSize rhs))
        !(I# size#) = fromIntegral $ natVal' (proxy# :: Proxy# (RecSize lhs + RecSize rhs))
    in unsafePerformIO $! IO $ \s# ->
            case newSmallArray# size# (error "No value") s# of
              (# s'#, arr# #) ->
                  case copySmallArray# r# 0# arr# 0# sizeR# s'# of
                    s''# ->
                        case copySmallArray# l# 0# arr# sizeR# sizeL# s''# of
                          s'''# ->
                              case unsafeFreezeSmallArray# arr# s'''# of
                                (# s''''#, a# #) -> (# s''''#, Rec a# #)
#else
combine (Rec o1) (Rec o2) =
    unsafePerformIO $
    Rec <$> mergeObjs o1 o2
#endif
{-# INLINE combine #-}

(++:) = combine
{-# INLINE (++:) #-}
