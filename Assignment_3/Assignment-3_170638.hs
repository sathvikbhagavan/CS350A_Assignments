--------------- Q1 ------------------
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = quicksort [i | i <- xs, i<=x] ++ [x] ++ quicksort [i | i <- xs, i>x]

--------------- Q2 -------------------
uniq :: Eq a => [a] -> [a]
uniq [] = []
uniq [x] = [x]
uniq (x:xs) = x:[i | i<-uniq xs, i/=x]

--------------- Q3 ------------------
neighbors :: (Ord a1, Ord a2, Num a1, Num a2) => a1 -> a2 -> [(a1, a2)]
neighbors i j = [(k,l) | k <- [0,1,2,3,4,5,6,7,8,9], l <- [0,1,2,3,4,5,6,7,8,9], abs(i-k)<=1 && abs(j-l)<=1 && (i/=k || j/=l)]


--------------- Q4 -------------------
countWords :: String -> Int
countWords s = sum (map (length . words) (lines s))

---------------- Q5 ------------------
composeMultiple :: [b -> b] -> b -> b
composeMultiple y x = foldl (\x f -> f x) x (reverse y)

---------------- Q6 ------------------
data BinaryTree a = Nil | Node a (BinaryTree a) (BinaryTree a) deriving (Show, Eq)

maptree :: (a->b) -> BinaryTree a -> BinaryTree b
maptree _ Nil = Nil
maptree f (Node x tl tr) = Node (f x) (maptree f tl) (maptree f tr)

foldTree :: (a -> b -> b -> b) -> b -> BinaryTree a -> b
foldTree _ i Nil = i
foldTree f i (Node x tl tr) = f x (foldTree f i tl) (foldTree f i tr)

add3 x y z = x+y+z