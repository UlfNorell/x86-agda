
import Data.Int
import System.Environment

m :: Int64
m = 1636102261

iter :: Int64 -> (Int64 -> Int64) -> Int64 -> Int64
iter 0 f z = z
iter n f z = iter (n - 1) f $! f z

bbs :: Int64 -> Int64
bbs x = x * x `rem` m

main = do
  args <- getArgs
  case map read args of
    [x, n] -> print (iter n bbs x)
    _ -> return ()
