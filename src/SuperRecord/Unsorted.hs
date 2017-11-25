{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
module SuperRecord.Unsorted
    ( -- * Basics
      rcons, (&)
    , module S
    ) where

import SuperRecord as S hiding (rcons, (&))
import SuperRecord.Internal

import GHC.Base (Int(..))
import GHC.IO ( IO(..) )
import GHC.Prim
import GHC.TypeLits
import System.IO.Unsafe (unsafePerformIO)

rcons, (&) ::
    forall l t lts s.
    (RecSize lts ~ s, KnownNat s, KeyDoesNotExist l lts)
    => l := t -> Rec lts -> Rec (l := t ': lts)
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
{-# INLINE rcons #-}

(&) = rcons
{-# INLINE (&) #-}
