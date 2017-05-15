-- Manipulating bare memory. Unsafe things go here!
module Memory where

open import Prelude

{-# FOREIGN GHC

import Control.Monad
import Data.Word
import Data.Bits
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.Storable
import Foreign.Marshal.Utils
import System.Posix.Types
import Unsafe.Coerce
import System.IO.Unsafe

import qualified Data.Vector.Storable as V
import qualified Data.Vector.Storable.Mutable as VM

type Function a = a -> a -> a

loadMachineCode :: [Word8] -> IO (Function Int)
loadMachineCode code = do
  let len = length code
  mem  <- allocateMemory (fromIntegral len)
  code <- codePtr code
  withForeignPtr (vecPtr code) $ \ ptr -> do
    copyBytes mem ptr len
  return (getFunction mem)

foreign import ccall "dynamic"
  mkFun :: FunPtr (Function Int) -> Function Int

getFunction :: Ptr Word8 -> Function Int
getFunction mem = mkFun (unsafeCoerce mem)

foreign import ccall unsafe "sys/mman.h mmap"
  c_mmap :: Ptr () -> CSize -> CInt -> CInt -> Fd -> COff -> IO (Ptr a)

mmap :: Ptr () -> CSize -> CInt -> CInt -> IO (Ptr Word8)
mmap addr len prot flags = do
  ptr <- c_mmap addr len prot flags (-1) 0
  when (ptr == intPtrToPtr (-1)) $ error "mmap failed!"
  return ptr

codePtr :: [Word8] -> IO (VM.IOVector Word8)
codePtr = V.thaw . V.fromList

vecPtr :: Storable a => VM.MVector s a -> ForeignPtr a
vecPtr = fst . VM.unsafeToForeignPtr0

pWrite, pExec :: CInt
pWrite = 0x02
pExec  = 0x04

mAnon, mPriv :: CInt
mAnon = 0x1000
mPriv = 0x02

allocateMemory :: CSize -> IO (Ptr Word8)
allocateMemory size = mmap nullPtr size (pWrite .|. pExec) (mAnon .|. mPriv)

castFun :: (Num a, Integral a) => Function a -> Function Integer
castFun f x y = toInteger $ f (fromInteger x) (fromInteger y)

-- {-# NOINLINE loadMachineCode' #-}
-- loadMachineCode' :: [Integer] -> Function Integer
-- loadMachineCode' = castFun
--                   . unsafePerformIO . loadMachineCode . map fromInteger

loadMachineCode' :: [Integer] -> IO (Function Integer)
loadMachineCode' = fmap castFun . loadMachineCode . map fromInteger

#-}

Word8 = Nat

postulate
  loadMachineCode : List Word8 → IO (Int → Int → Int)

{-# COMPILE GHC loadMachineCode = loadMachineCode' #-}
