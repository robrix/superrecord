{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
module SuperRecord.Internal where

import GHC.Base (Any)
import GHC.Prim


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
