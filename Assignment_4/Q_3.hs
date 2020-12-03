import Control.Monad.State

--------------- Q.3 -------------------
--- Written both Function call and Interactive style by writing the main function

type FibState = ([Int], Int, Int)

fibStep :: State ([Int], Int, Int) ()
fibStep = state (\(l, i, n) -> ((), (l ++ [takeIth l (i-1) + takeIth l (i-2)], i+1, n)))


fibSequence = do
    (l,i,n) <- get
    if i <= n
        then
        do
            fibStep
            fibSequence
        else return (takeIth l i)


takeIth :: (Num p, Num t, Ord t) => [p] -> t -> p
takeIth [] _ = 0
takeIth (x:xs) i 
    | i==0 = x
    | i>0 = takeIth xs (i-1)


listLast :: [p] -> p
listLast [x] = x 
listLast (_:xs) = listLast xs 
listLast [] = error "Can't do last of an empty list!"

-- Function call to get the nth fibonacci number
runFibSequence :: Int -> Int
runFibSequence n 
    | n==0 = 0
    | n==1 = 1
    | n>1 = takeOnly (runState fibSequence ([0,1], 2, n))

takeOnly :: (a, ([p], b, c)) -> p
takeOnly (_, (l, _, _)) = listLast l


-- Main function (interactive implementation)
main :: IO ()
main = do
    putStrLn "Which Fibonacci Number you want (Starting from 1)"
    num_string <- getLine
    let num = read num_string :: Int
    let (_, (l, _, _)) = runState fibSequence ([0,1], 2, num)
    print (listLast l)






