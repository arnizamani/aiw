module Domains.Arithmetic (arithItem,multItem,subtItem,diviItem,additionItem,evenItem,oddItem,mod3Item,
                           addItems,lessThanItem,greaterThanItem,lessThanEqualItem,greaterThanEqualItem) where

import Instances
import Data.Maybe
import Test.QuickCheck
import System.IO
generate :: Gen a -> IO a
generate g = do
    values <- sample' g
    return $ head values

-- even 0 = T
-- even 1 = F
-- even (x # y) = even y

additionItem' = do
        size <- frequency [(800,return 3),(150,return 5),(40,return 7),(10,return 9)]
        viabP <- posViability
        lhs <- additionExp size
        diff  <- oneof $ map return $ [(-10)..(-1)] ++ [1..10]
        let answer' = solveArith lhs
        if isNothing answer'
        then additionItem'
        else do
        let answer = fromJust answer'
        let rhsP = makeExp answer
        let rhsN = makeExp (answer + diff)
        if lhs == rhsP
            then additionItem'
            else return $ Item lhs rhsP viabP

saveFile :: IO ()
saveFile = do
    items <- mapM (\x -> generate additionItem') [1..10000]
    let result = unlines $ map show items
    out <- openFile "Addition.domain" WriteMode
    hSetEncoding out utf8
    hPutStr out result
    hFlush out
    hClose out

oddItem :: Int -> Gen Item
oddItem _ = oddeven odd "odd"

evenItem :: Int -> Gen Item
evenItem _ = oddeven even "even"

mod3Item :: Int -> Gen Item
mod3Item _ = oddeven (\x -> x `mod` 3 == 0) "mod3"


oddeven :: (Int -> Bool) -> String -> Gen Item
oddeven f fname = do
        pos   <- frequency [(2,return 1),(1,return (-1))]
        viabP <- posViability
        viabN <- negViability
        size <- randomSize
        n <- frequency [((110 - n),return n) | n <- [0..100]]
        let lhs = Unary (Oper fname) (makeExp n)
        let rhsP = Root $ if f n then "1" else "0"
        let rhsN = Root $ if f n then "0" else "1"
        if pos > 0
        then return $ Item lhs rhsP viabP
        else return $ Item lhs rhsN viabN

check "0" = True
check "1" = False
check "2" = True
check "3" = False
check "4" = True
check "5" = False
check "6" = True
check "7" = False
check "8" = True
check "9" = False
check x   = error $ "check: " ++ x


    
-- random Item for arithmetic
arithItem :: Int -> Gen Item
arithItem s = do
        size <- frequency [(800,return 3),(150,return 5),(40,return 7),(10,return 9)]
        viabP <- posViability
        viabN <- negViability
        lhs <- arithExp size
        diff  <- oneof $ map return $ [2..10]
        pos   <- frequency [(9,return 1),(1,return (-1))]
        let answer' = solveArith lhs
        if isNothing answer'
        then arithItem s
        else do
        let answer = fromJust answer'
        let rhsP = makeExp answer
        let rhsN = makeExp (answer * diff + 1)
        if pos < 1
        then do
            return $ Item lhs rhsN viabN
        else do
            if lhs == rhsP
                then arithItem s
                else return $ Item lhs rhsP viabP

-- random Item for addition facts
additionItem :: Int -> Gen Item
additionItem s | s < 1 = additionItem 500
additionItem s | s <= 10 = do
        let right = Root (show (s - 1))
        return $ Item (Binary (Oper "#") (Root "0") right) right 1
additionItem s | s <= 110 = do
        let s' = s - 11
        let a = s' `div` 10
        let b = s' `mod` 10
        let lhs = (Binary (Oper "+") (Root $ show a) (Root $ show b))
        let answer = solveArith lhs
        if isNothing answer
        then additionItem s
        else do
        let rhs = makeExp $ fromJust answer
        return $ Item lhs rhs 1
additionItem s | s <= 440 = do
        additionItem $ s `mod` 110
additionItem s = do
        --size <- oneof $ map return [3,5,7,9] -- frequency [(900,return 3),(90,return 5),(9,return 7),(1,return 9)]
        size <- frequency [(900,return 3),(90,return 5),(9,return 7),(1,return 9)]
        viabP <- posViability
        viabN <- negViability
        lhs <- additionExp size
        diff  <- oneof $ map return $ [(-10)..(-1)] ++ [1..10]
        pos   <- frequency [(9,return 1),(1,return (-1))]
        let answer' = solveArith lhs
        if isNothing answer'
        then additionItem s
        else do
        let answer = fromJust answer'
        let rhsP = makeExp answer
        let rhsN = makeExp (answer + diff)
        if pos < 1
        then do
            return $ Item lhs rhsN viabN
        else do
            if lhs == rhsP
                then additionItem s
                else return $ Item lhs rhsP viabP

-- random Item for multiplication facts
multItem :: Int -> Gen Item
multItem s | s < 0 = multItem 500
multItem s | s <= 10 = do
        let right = Root (show (s - 1))
        return $ Item (Binary (Oper "#") (Root "0") right) right 1
multItem s | s <= 110 = do
        let s' = s - 11
        let a = s' `div` 10
        let b = s' `mod` 10
        let lhs = (Binary (Oper "*") (Root $ show a) (Root $ show b))
        let answer' = solveArith lhs
        if isNothing answer'
        then multItem s
        else do
        let rhs = makeExp $ fromJust answer'
        return $ Item lhs rhs 1
multItem s | s <= 440 = do
        multItem $ s `mod` 110
multItem s = do
        size <- oneof $ map return [3,5,7,9]
        viabP <- posViability
        viabN <- negViability
        lhs <- multExp size
        diff  <- oneof $ map return $ [(-10)..(-1)] ++ [1..10]
        pos   <- frequency [(9,return 1),(1,return (-1))]
        let answer' = solveArith lhs
        if isNothing answer'
        then multItem s
        else do
        let answer = fromJust answer'
        let rhsP = makeExp answer
        let rhsN = makeExp (answer + diff)
        if pos < 1
        then do
            return $ Item lhs rhsN viabN
        else do
            if lhs == rhsP
                then multItem s
                else return $ Item lhs rhsP viabP

-- random Item for subtraction facts
subtItem :: Int -> Gen Item
subtItem s | s < 0 = subtItem 500
subtItem s | s <= 10 = do
        let right = Root (show (s - 1))
        return $ Item (Binary (Oper "#") (Root "0") right) right 1
subtItem s | s <= 110 = do
        let s' = s - 11
        let a = s' `div` 10
        let b = s' `mod` 10
        let lhs = (Binary (Oper "_") (Root $ show a) (Root $ show b))
        let answer' = solveArith lhs
        if isNothing answer'
        then subtItem s
        else do
        let rhs = makeExp $ fromJust answer'
        return $ Item lhs rhs 1
subtItem s | s <= 440 = do
        subtItem $ s `mod` 110
subtItem s = do
        size <- oneof $ map return [2..9]
        viabP <- posViability
        viabN <- negViability
        lhs <- subtExp size
        diff  <- oneof $ map return $ [(-10)..(-1)] ++ [1..10]
        pos   <- frequency [(9,return 1),(1,return (-1))]
        let answer' = solveArith lhs
        if isNothing answer'
        then subtItem s
        else do
        let answer = fromJust answer'
        let rhsP = makeExp answer
        let rhsN = makeExp (answer + diff)
        if pos < 1
        then do
            return $ Item lhs rhsN viabN
        else do
            if lhs == rhsP
                then subtItem s
                else return $ Item lhs rhsP viabP

-- random Item for subtraction facts
diviItem :: Int -> Gen Item
diviItem s | s < 0 = diviItem 500
diviItem s | s <= 10 = do
        let right = Root (show (s - 1))
        return $ Item (Binary (Oper "#") (Root "0") right) right 1
diviItem s | s <= 440 && ((s `mod` 10) == 1) = diviItem (s + 1)
diviItem s | s <= 110 = do
        let s' = s - 11
        let a = s' `div` 10
        let b = s' `mod` 10
        let lhs = (Binary (Oper "/") (Root $ show a) (Root $ show b))
        let answer' = solveArith lhs
        if isNothing answer'
        then diviItem s
        else do
        let rhs = makeExp $ fromJust answer'
        return $ Item lhs rhs 1
diviItem s | s <= 440 = do
        diviItem $ s `mod` 110
diviItem s = do
        size <- oneof $ map return [3,5,7,9]
        viabP <- posViability
        viabN <- negViability
        lhs <- diviExp size
        diff  <- oneof $ map return $ [(-10)..(-1)] ++ [1..10]
        pos   <- frequency [(9,return 1),(1,return (-1))]
        let answer' = solveArith lhs
        if isNothing answer'
        then diviItem s
        else do
        let answer = fromJust answer'
        let rhsP = makeExp answer
        let rhsN = makeExp (answer + diff)
        if pos < 1
        then do
            return $ Item lhs rhsN viabN
        else do
            if lhs == rhsP
                then diviItem s
                else return $ Item lhs rhsP viabP
                
-- list of pedagogic addition facts, not complete
addItems :: IO [Item]
addItems = do
    let numbers = [0..20]
    let digits = [0..9]
    let items0 = [Item (makeB "+" (makeR $ show d1) (makeR $ show d2)) (makeExp (d1+d2)) 1 | d1 <- digits, d2 <- digits]
    let items1 = [Item (makeB "#" (makeR "0") (makeExp n)) (makeExp n) 1 | n <- numbers]
    let items2 = [Item (makeB "+" (makeR "0") (makeExp n)) (makeExp n) 1 | n <- numbers]
    
    let items3 = [Item (makeB "+" (makeB "#" (makeR $ show d1) (makeR "0")) (makeR $ show d2)) (makeExp (d1*10+d2)) 1
                        | d1 <- take 5 digits, d2 <- take 5 digits]
    let items4 = concat $ -- d1 # (d2 # d3),  (d1 + d2) # d3
                  [[Item (makeB "#" (makeR $ show d1) (makeB "#" (makeR $ show d2) (makeR $ show d3))) (makeExp ((d1+d2)*10+d3)) 1,
                    Item (makeB "#" (makeB "+" (makeR $ show d1) (makeR $ show d2)) (makeR $ show d3)) (makeExp ((d1+d2)*10+d3)) 1,
                    Item (makeB "#" (makeB "+" (makeR $ show d2) (makeR $ show d1)) (makeR $ show d3)) (makeExp ((d1+d2)*10+d3)) 1
                    ]
                        | d1 <- take 5 digits, d2 <- take 5 digits, d3 <- take 5 digits]
    let items5 = [Item (makeB "+" (makeExp n1) (makeExp n2)) (makeExp (n1+n2)) 1 | n1 <- numbers, n2 <- numbers]
    
    let items = items0 ++ items1 ++ items2 ++ items3 ++ items4 ++ items5
    return $ items

greaterThanEqualItem :: Int -> Gen Item
greaterThanEqualItem _ = do
        viabP <- posViability
        viabN <- negViability
        size1 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        size2 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        lhs <- randomNumber size1
        rhs <- randomNumber size2
        let answer = lhs >= rhs
        if answer
        then return $ Item (Binary (Oper "≥") (makeExp lhs) (makeExp rhs)) (Root "T") viabP
        else return $ Item (Binary (Oper "≥") (makeExp lhs) (makeExp rhs)) (Root "T") viabN

greaterThanItem :: Int -> Gen Item
greaterThanItem _ = do
        viabP <- posViability
        viabN <- negViability
        size1 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        size2 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        lhs <- randomNumber size1
        rhs <- randomNumber size2
        let answer = lhs > rhs
        if answer
        then return $ Item (Binary (Oper ">") (makeExp lhs) (makeExp rhs)) (Root "T") viabP
        else return $ Item (Binary (Oper ">") (makeExp lhs) (makeExp rhs)) (Root "T") viabN

lessThanEqualItem :: Int -> Gen Item
lessThanEqualItem _ = do
        viabP <- posViability
        viabN <- negViability
        size1 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        size2 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        lhs <- randomNumber size1
        rhs <- randomNumber size2
        let answer = lhs <= rhs
        if answer
        then return $ Item (Binary (Oper "≤") (makeExp lhs) (makeExp rhs)) (Root "T") viabP
        else return $ Item (Binary (Oper "≤") (makeExp lhs) (makeExp rhs)) (Root "T") viabN

lessThanItem :: Int -> Gen Item
lessThanItem _ = do
        viabP <- posViability
        viabN <- negViability
        size1 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        size2 <- frequency [(90,return 1),(9,return 2),(1,return 3)]
        lhs <- randomNumber size1
        rhs <- randomNumber size2
        let answer = lhs < rhs
        if answer
        then return $ Item (Binary (Oper "<") (makeExp lhs) (makeExp rhs)) (Root "T") viabP
        else return $ Item (Binary (Oper "<") (makeExp lhs) (makeExp rhs)) (Root "T") viabN

randomNumber :: Int -> Gen Int
randomNumber n | n < 2 = oneof $ map return [0..9]
randomNumber n = do
    n1 <- randomNumber (n - 1)
    n2 <- randomNumber 1
    return (n1 * 10 + n2)

operatorMul = frequency [(5,return "#"),(1,return "*"),(1,return "+")] -- ,(1,return "_")]
operatorAdd = frequency [(1,return "+"),(1,return "#")]

solveArith :: Exp -> Maybe Int
solveArith e | containsVar e = Nothing -- error "solveArith: Exp contains variable."
solveArith e = case e of
    (Root "0") -> Just 0
    (Root "1") -> Just 1
    (Root "2") -> Just 2
    (Root "3") -> Just 3
    (Root "4") -> Just 4
    (Root "5") -> Just 5
    (Root "6") -> Just 6
    (Root "7") -> Just 7
    (Root "8") -> Just 8
    (Root "9") -> Just 9
    (Unary (Oper "-") x) -> let x' = solveArith x in if isNothing x' then Nothing else Just (0 - fromJust x')
    (Binary (Oper "#") x y) -> let x' = (solveArith x)
                                   y' = (solveArith y)
                               in if isJust x' && isJust y'
                                  then Just ((fromJust x') * 10 + (fromJust y'))
                                  else Nothing
    (Binary (Oper "+") x y) -> let x' = solveArith x
                                   y' = solveArith y
                               in if isJust x' && isJust y'
                                  then Just (fromJust x' + fromJust y')
                                  else Nothing
    (Binary (Oper "_") x y) -> let x' = solveArith x
                                   y' = solveArith y
                               in if isJust x' && isJust y'
                                  then Just (fromJust x' - fromJust y')
                                  else Nothing
    (Binary (Oper "*") x y) -> let x' = solveArith x
                                   y' = solveArith y
                               in if isJust x' && isJust y'
                                  then Just (fromJust x' * fromJust y')
                                  else Nothing
    (Binary (Oper "/") x (Root "0")) -> Nothing
    (Binary (Oper "/") x y) -> let y' = solveArith y
                                   x' = solveArith x
                               in if isNothing y' || isNothing x'
                                  then Nothing
                                  else if y' /= (Just 0)
                                        then Just ((fromJust x') `div` (fromJust y'))
                                        else Nothing
    e -> error $ "solveArith: Unknown expression " ++ show e

makeExp :: Int -> Exp
makeExp n | n < 0 = makeU "-" (makeExp (0-n))
-- makeExp n | n < 10 = Root (show n)
makeExp n = foldl1 (\x y -> makeB "#" x y) [makeR [d] | d <- show n]

arithExp :: Int -> Gen Exp
arithExp size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
--arithExp size | size <= 4 = do
--    x <- frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
--    y <- frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
--    op <- operatorMul
--    return $ makeB op x y
arithExp size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- arithExp (size - d1)
    y <- arithExp (size - d2)
    op <- operatorMul
    exp <- oneof $ map return [makeB op x y,makeB op y x]
    return exp
{-
additionExp size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- additionExp (size - d1)
    y <- additionExp (size - d2)
    op <- operatorAdd
    exp <- oneof $ map return [makeB op x y,makeB op y x]
    return exp
-}

additionExp :: Int -> Gen Exp
additionExp size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
additionExp size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- additionExp (size - d1)
    y <- additionExp (size - d2)
    op <- operatorAdd
    exp <- oneof $ map return [makeB op x y,makeB op y x]
    return exp

multExp :: Int -> Gen Exp
multExp size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
multExp size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- multExp (size - d1)
    y <- multExp (size - d2)
    op <- return "*"
    exp <- oneof $ map return [makeB op x y,makeB op y x]
    return exp

subtExp :: Int -> Gen Exp
subtExp size | size <= 1 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
subtExp 2 = do
    exp <- subtExp 1
    return $ Unary (Oper "-") exp
subtExp size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- subtExp (size - d1)
    y <- subtExp (size - d2)
    op <- return "_"
    exp <- oneof $ map return [makeB op x y,makeB op y x]
    return exp

diviExp :: Int -> Gen Exp
diviExp size | size <= 2 = frequency [((10 - n),return (makeR $ show n)) | n <- [0,1,2,3,4,5,6,7,8,9]]
diviExp size' = do
    let size = if odd size' then size' else size' - 1
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)], odd i && odd (size-1-i)]
    x <- diviExp (size - d1)
    y <- diviExp (size - d2)
    op <- return "/"
    if x /= Root "0"
    then if y /= Root "0"
         then oneof $ map return [makeB op x y,makeB op y x]
         else oneof $ map return [makeB op y x]
    else if y /= Root "0"
         then oneof $ map return [makeB op x y]
         else diviExp size'

-- posViability = frequency [(1000,return 1),(100,return 2),(10,return 3),(1,return 4)]
posViability = frequency [((1001 - n * n * n),return n) | n <- [1..10]]
negViability = frequency [(1000,return (-1)),(100,return (-2)),(10,return (-3)),(1,return (-4))]
randomSize = frequency [(900,return 3),(90,return 5),(9,return 7),(1,return 9)] -- (3,90%), (5,31.8%), (7,21.6%), (9,8.0%) total = 91+75+51+19=236

