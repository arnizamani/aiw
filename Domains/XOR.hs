module Domains.XOR where

import Data.Bits
import Numeric
import Instances
import Test.QuickCheck

type Decimal = Int
type Binary = [Int]

makeExpB :: Decimal -> Exp
makeExpB n = formExp $ showIntAtBase 2 (head . show) n ""

additionDec :: Int -> Gen Exp
additionDec size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
additionDec size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- additionDec (size - d1)
    y <- additionDec (size - d2)
    op <- frequency [(1,return "D+"),(1,return "#")]
    case y of
      (Binary (Oper "#") _ _) -> return (makeB "D+" x y)
      _ -> return (makeB op x y)
multiplicationDec :: Int -> Gen Exp
multiplicationDec size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
multiplicationDec size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- multiplicationDec (size - d1)
    y <- multiplicationDec (size - d2)
    op <- frequency [(1,return "D*"),(1,return "#")]
    case y of
      (Binary (Oper "#") _ _) -> return (makeB "D*" x y)
      _ -> return (makeB op x y)

xorAddDecimal :: Int -> Gen Item
xorAddDecimal s = do
    size <- randomSize
    viab <- posViability
    lhs  <- additionDec size
    let answer = solveXorDec lhs
    let rhs = makeExpD answer
    if lhs == rhs
        then xorAddDecimal s
        else return $ Item lhs rhs viab
xorMulDecimal :: Int -> Gen Item
xorMulDecimal s = do
    size <- randomSize
    viab <- posViability
    lhs  <- multiplicationDec size
    let answer = solveXorDec lhs
    let rhs = makeExpD answer
    if lhs == rhs
        then xorMulDecimal s
        else return $ Item lhs rhs viab

xorAddBinary :: Int -> Gen Item
xorAddBinary s = do
        size <- randomSize
        viab <- posViability
        lhs  <- additionBin size
        let answer = solveXorBin lhs
        let rhs = makeExpB answer
        if lhs == rhs
                then xorAddBinary s
                else return $ Item lhs rhs viab

additionBin :: Int -> Gen Exp
additionBin size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1]]
additionBin size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- additionBin (size - d1)
    y <- additionBin (size - d2)
    op <- frequency [(1,return "B+"),(1,return "#")]
    case y of
      (Binary (Oper "#") _ _) -> return (makeB "B+" x y)
      _ -> return (makeB op x y)

multiplicationExpBin :: Int -> Gen Exp
multiplicationExpBin size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1]]
multiplicationExpBin size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- multiplicationExpBin (size - d1)
    y <- multiplicationExpBin (size - d2)
    op <- frequency [(1,return "B*"),(1,return "#")]
    case y of
      (Binary (Oper "#") _ _) -> return (makeB "B*" x y)
      _ -> return (makeB op x y)

xorMulBinary :: Int -> Gen Item
xorMulBinary s = do
        size <- randomSize
        viab <- posViability
        lhs  <- multiplicationExpBin size
        let answer = solveXorBin lhs
        let rhs = makeExpB answer
        if lhs == rhs
                then xorMulBinary s
                else return $ Item lhs rhs viab

binToDecimal :: [Int] -> Int
binToDecimal [] = 0
binToDecimal [x] = x
binToDecimal xs = (binToDecimal (init xs)) * 2 + (last xs)

-- A [N], B [N]
-- A*B[k] = (sum(p+q=k) (A[p] * B[q])) % 2

-- Example: A = [a,b,c], B = [x,y,z]
--          A*B[0] = (A[0] * B[0]) % 2 = (a*x)%2
--          A*B[1] = [ (A[0] * B[1]) + (A[1] * B[0]) ] % 2 = (a*y+b*x)%2
--          A*B[2] = [ (A[0] * B[2]) + (A[2] * B[0]) + (A[1] * B[1])] % 2 = (a*y+b*x)%2

multiply :: [Int] -> [Int] -> [Int]
multiply [] _ = error "multiply in Domains.XOR"
multiply x y | length x /= length y = error "multiply in Domains.XOR"
multiply x y = [
                (sum [a * b | (i1,a) <- x',(i2,b) <- y',(i1+i2)==i]) `mod` 2
                 | i <- [0..(length x * 2 - 2)]]
         where x' = zip [0..] x
               y' = zip [0..] y

multiplyDec :: Decimal -> Decimal -> Decimal
multiplyDec x y = binToDecimal . dropWhile (==0) . (uncurry multiply) $ equalLen (decToBinary x,decToBinary y)    

decToBinary :: Decimal -> Binary
decToBinary n | n < 0 = error "decToBinary: negative numbers cannot be converted to binary."
decToBinary n | n < 2 = [n]
decToBinary n = decToBinary (n `div` 2) ++ [n `mod` 2]

equalLen :: (Binary,Binary) -> (Binary,Binary)
equalLen (x,y) | length x == length y = (x,y)
equalLen (x,y) | length x < length y = equalLen (0:x, y)
equalLen (x,y) = equalLen (x, 0:y)

equalLength :: Int -> String -> Binary
equalLength maxLength n = map toInt ((take (min maxLength (maxLength - length n)) $ repeat '0') ++ n)

toInt '0' = 0
toInt '1' = 1
toInt _   = error "toInt in xorMulBinary"

formExp :: String -> Exp
formExp [] = error "formExp in Domain XOR"
formExp [x] = Root [x]
formExp xs@(_:_) = Binary (Oper "#") (formExp (init xs)) (Root [last xs])

makeExpD :: Decimal -> Exp
makeExpD n | n < 0 = makeU "-" (makeExpD (0-n))
makeExpD n = foldl1 (\x y -> makeB "#" x y) [makeR [d] | d <- show n]

posViability = frequency [((1001 - n * n * n),return n) | n <- [1..10]]

randomSize = frequency [(900,return 3),(90,return 5),(9,return 7),(1,return 9)]

solveXorBin :: Exp -> Decimal
solveXorBin e | containsVar e = error "solveXorBin: Exp contains variable."
solveXorBin e = case e of
    (Root "0") -> 0
    (Root "1") -> 1
    (Binary (Oper "#") x (Binary (Oper "#") y z)) -> error "solveXorBin: number not normalized."
    (Binary (Oper "#") x y) -> (solveXorBin x) * 2 + (solveXorBin y)
    (Binary (Oper "B+") x y) -> solveXorBin x `xor` solveXorBin y
    (Binary (Oper "B*") x y) -> solveXorBin x `multiplyDec` solveXorBin y
    -- (Binary (Oper "B_") x y) -> solveXorBin x - solveXorBin y
    -- (Binary (Oper "B/") x y) -> solveXorBin x `div` solveXorBin y
    e -> error $ "solveXorBin: Unknown expression " ++ show e

solveXorDec :: Exp -> Decimal
solveXorDec e | containsVar e = error "solveXorDec: Exp contains variable."
solveXorDec e = case e of
    (Root "0") -> 0
    (Root "1") -> 1
    (Root "2") -> 2
    (Root "3") -> 3
    (Root "4") -> 4
    (Root "5") -> 5
    (Root "6") -> 6
    (Root "7") -> 7
    (Root "8") -> 8
    (Root "9") -> 9
    (Binary (Oper "#") x (Binary (Oper "#") y z)) -> error "solveXorDec: number not normalized."
    (Binary (Oper "#") x y) -> (solveXorDec x) * 10 + (solveXorDec y)
    (Binary (Oper "D+") x y) -> solveXorDec x `xor` solveXorDec y
    (Binary (Oper "D*") x y) -> solveXorDec x `multiplyDec` solveXorDec y
    -- (Binary (Oper "D_") x y) -> solveXorDec x - solveXorDec y
    -- (Binary (Oper "D/") x y) -> solveXorDec x `div` solveXorDec y
    e -> error $ "solveXorDec: Unknown expression " ++ show e
