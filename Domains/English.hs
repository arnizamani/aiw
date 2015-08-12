module Domains.English where

import Instances
import Test.QuickCheck

nounS = ["Alice","Bob"] -- ,"John","George","Paul","David"]
nounP = ["Cars","Houses"]
verbS = ["runs","plays"] -- ,"walks","takes"]
verbP = ["move","hide"]
pronounS = ["He","She"]
pronounP = ["We","They"]
adverb = ["slowly","suddenly"]

templates2 = [  (nounS,verbS),
                (nounP,verbP),
                (pronounS,verbS),
                (pronounP,verbP) ]
templates3 = [  (nounS,verbS,adverb),
                (nounP,verbP,adverb),
                (pronounS,verbS,adverb),
                (pronounP,verbP,adverb)
                ]

words' = nounS ++ nounP ++ verbS ++ verbP ++ pronounS ++ pronounP ++ adverb

sentence2 = do
    template <- oneof $ map return templates2
    x <- oneof . map return $ fst template
    y <- oneof . map return $ snd template
    let sentence = Binary (Oper "#") (Root x) (Root y)
    return sentence

sentence3 = do
    template <- oneof $ map return templates3
    x <- oneof . map return $ fst' template
    y <- oneof . map return $ snd' template
    z <- oneof . map return $ thd' template
    let sentence = Binary (Oper "#") (Binary (Oper "#") (Root x) (Root y)) (Root z)
    return sentence
    
nonSentences = 
    [Root w | w <- words']
    ++
    [Binary (Oper "#") (Root v) (Root n) | n <- nounS, v <- verbS]
    ++
    [Binary (Oper "#") (Root v) (Root p) | p <- pronounS, v <- verbS]
    ++
    [Binary (Oper "#") (Root v) (Root p) | p <- pronounP, v <- verbP]
    ++
    [Binary (Oper "#") (Root v) (Root p) | p <- pronounP, v <- pronounS]
    ++
    [Binary (Oper "#") (Root v) (Root p) | p <- verbP, v <- verbS]

-- random Item for addition facts
langItem :: Int -> Gen Item
langItem s = do
        positive <- oneof [return True, return False]
        correct  <- oneof [return True , return False]
        -- ok <- frequency [(9,return (Root "OK")),(1,return (Binary "#" (Root "OK") (Root "OK")))]
        let ok = Root "OK"
        size' <- oneof [return 2,return 3]
        correctLhs <- case size' of
                        2 -> sentence2
                        3 -> sentence3
        wrongLhs <- elements nonSentences
        if positive
        then do
            if correct -- correct item with positive viability
            then do
                let item = Item correctLhs ok (size correctLhs)
                return item
            else do    -- wrong item with positive viability
                let item = Item wrongLhs (Root "*OK") (size wrongLhs)
                return item
        else do
            if correct -- correct item with negative viability
            then do
                let item = Item correctLhs (Root "*OK") (0 - (size correctLhs))
                return item
            else do
                let item = Item wrongLhs ok (0 - size wrongLhs)
                return item
