
module Numeric.Word where

open import Prelude

{-# FOREIGN GHC import Data.Int  #-}
{-# FOREIGN GHC import Data.Word #-}

postulate Int64 : Set
{-# COMPILE GHC Int64 = type Int64 #-}

postulate
  i64-add : Int64 → Int64 → Int64
  i64-sub : Int64 → Int64 → Int64
  i64-mul : Int64 → Int64 → Int64
  i64-quot : Int64 → Int64 → Int64 -- !
  i64-rem  : Int64 → Int64 → Int64
  i64-fromInt : Int → Int64
  i64-toInt   : Int64 → Int

{-# COMPILE GHC i64-add  = (+)  #-}
{-# COMPILE GHC i64-sub  = (-)  #-}
{-# COMPILE GHC i64-mul  = (*)  #-}
{-# COMPILE GHC i64-quot = quot #-}
{-# COMPILE GHC i64-rem  = rem  #-}
{-# COMPILE GHC i64-fromInt = fromInteger #-}
{-# COMPILE GHC i64-toInt   = toInteger   #-}

postulate
  NonZeroInt64 : Int64 → Set
  instance
    NonZeroInt64Inst : ∀ {n} {{_ : NonZeroInt n}} → NonZeroInt64 (i64-fromInt n)

instance
  ShowInt64 : Show Int64
  showsPrec {{ShowInt64}} p x = showsPrec p (i64-toInt x)
