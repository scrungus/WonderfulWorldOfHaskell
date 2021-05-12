data Tree = None Int | First Int Tree | Second Int Tree | Both Int Tree Tree

s :: Tree
s = Both 3 (First 2 (None 0)) (Both 6 (None 5) (Second 8 (None 9)))

t :: Tree
t = Both 0 (Both 5 (None 1) (None 4)) (Second 7 (Both 2 (None 0) (None 0)))

total :: Tree -> Int
total (None   x)     = x
total (First  x l)   = x + total l
total (Second x r)   = x + total r
total (Both   x l r) = x + total l + total r

treefold:: (Int -> a) -> (a -> a -> a) -> Tree -> a
treefold i f (None x) = i x
treefold i f (First x l) = f (i x) (treefold i f l) 
treefold i f (Second x r) = f (i x) (treefold i f r)
treefold i f (Both   x l r) = f (i x) (f (treefold i f l) (treefold i f r))

treemax:: Tree -> Int
treemax t = treefold id (max) t

treesize:: Tree -> Int
treesize t = treefold acc (+) t where
    acc:: Int -> Int
    acc i = 1