----------------- Q.4 -----------------
---- Without do notation -----
main :: IO ()
main = addNonNegativeNumbers 0


addNonNegativeNumbers :: Integer -> IO ()
addNonNegativeNumbers initVal = 
    getLine >>= \nextNumber -> continueAdding nextNumber initVal
    

continueAdding :: String -> Integer -> IO ()
continueAdding nextNumber initVal
    | null nextNumber = addNonNegativeNumbers initVal
    | stringToInteger nextNumber == -1 = print initVal
    | otherwise = addNonNegativeNumbers (initVal + stringToInteger nextNumber)

stringToInteger :: String -> Integer
stringToInteger s = read s :: Integer