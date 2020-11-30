----------------- Q.4 ----------------
----- With do notation ------
main :: IO ()
main = addNonNegativeNumbersDo 0

addNonNegativeNumbersDo :: Integer -> IO ()
addNonNegativeNumbersDo initVal = do
    nextNumberString <- getLine
    if null nextNumberString 
        then addNonNegativeNumbersDo initVal
        else do
        let nextNumber = read nextNumberString :: Integer
        if nextNumber == -1 
            then print initVal 
            else do addNonNegativeNumbersDo $ initVal+nextNumber
