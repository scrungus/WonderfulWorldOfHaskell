import Control.Exception
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs x (At y) = x==y
occurs x (At y :-> ys) = if x/=y then occurs x ys else x==y
occurs x (y :-> At ys) = if x==ys then x==ys else occurs x y
occurs x (y :-> ys) = occurs x y || occurs x ys

findAtoms :: Type -> [Atom]
findAtoms (At x) = [x]
findAtoms (At x :-> At y) = if x<=y then [x,y] else [y,x]
findAtoms (x :-> xs) = merge (findAtoms x) (findAtoms xs)

------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub s (At t) = if fst s == t then snd s else (At t)
sub s (At t :-> ts) = if fst s == t then snd s :-> sub s ts else At t :-> sub s ts
sub s (ts :-> At t) = if fst s == t then sub s ts :-> snd s  else sub s ts :-> At t
sub s (t :-> ts) = sub s t :-> sub s ts

subs :: [Sub] -> Type -> Type
subs [s] t = sub s t
subs (s:ss) t = sub s (subs ss t)


------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s [] = []
sub_u s [(u,u2)] = [(sub s u, sub s u2)]
sub_u s ((u,u2):us) = (sub s u, sub s u2) : sub_u s us


step :: State -> State
step (s, (At u, u2):us) = if (At u) == u2 then (s, us)
else
  if occurs u u2 then error "Cannot be Unified." 
  else ((u, u2):s, sub_u (u,u2) us)

step (s, (u, At u2):us) = if (At u2) == u then (s, (u, At u2):us)
else
  if occurs u2 u then error "Cannot be Unified." 
  else ((u2, u):s, sub_u (u2,u) us)

step (s, (u :-> u2, u3 :-> u4):us) = (s, (u, u3):(u2, u4):us)


unify :: [Upair] -> [Sub]
unify u = unifyHelper ([],u)

unifyHelper :: State -> [Sub]
unifyHelper (s,[]) = s
unifyHelper (s,u) = unifyHelper (step (s,u))
------------------------- Assignment 4

type Context   = [(Var,Type)]

c1 :: Context 
c1 = [("a",t1),("b",t2),("c",t3)]

type Judgement = (Context, Term, Type)

data Derivation = 
  Axiom Judgement 
  | Abstraction Judgement Derivation 
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom j) = j
conclusion (Abstraction j d) = j 
conclusion (Application j d d2) = j


subs_ctx :: [Sub] -> Context -> Context
subs_ctx s [] = []
subs_ctx s [(u,u2)] = [(u, subs s u2)]
subs_ctx s ((u,u2):us) = (u, subs s u2) : subs_ctx s us

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg s (j,j2,j3) = (subs_ctx s j, j2, subs s j3)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der s (Axiom j) = Axiom (subs_jdg s j)
subs_der s (Abstraction j d) = Abstraction (subs_jdg s j) (subs_der s d)
subs_der s (Application j d d2) = Application (subs_jdg s j) (subs_der s d) (subs_der s d2)


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])


{- c1 = [("a",t1),("b",t2),("c",t3)] -}
------------------------- Assignment 5
genContext :: [Var] -> [Type] -> Context -> Context
genContext [v] [t] [] = [(v,t)]
genContext (v:vs) [t] [] = [(v,t)] ++ genContext vs [t] []
genContext (v:vs) (t:ts) [] = [(v,t)] ++ genContext vs ts []

genContext [] t c = []

genContext [v] [t] [(v1,t1)] = if v==v1 then [] else [(v,t)]
genContext (v:vs) [t] [(v1,t1)] = if v==v1 then genContext vs [t] [(v1,t1)] else  [(v,t)] ++ genContext vs [t] [(v1,t1)]
genContext (v:vs) (t:ts) [(v1,t1)] = if v==v1 then genContext vs ts [(v1,t1)] else [(v,t)] ++ genContext vs ts [(v1,t1)]

genContext [v] [t] ((v1,t1):cs) = if v==v1 then [] else  genContext [v] [t] cs
genContext (v:vs) [t] ((v1,t1):cs) = if v==v1 then genContext vs [t] cs else genContext [v] [t] cs ++ genContext vs [t] ((v1,t1):cs)
genContext (v:vs) (t:ts) ((v1,t1):cs) =  if v==v1 then genContext vs ts ((v1,t1):cs) else genContext [v] [t] cs ++ genContext vs ts ((v1,t1):cs)

dropa :: Int -> [a] -> [a]
dropa _ [] = []
dropa 0 y = y
dropa x (y:ys) = drop (x-1) ys

{- n1 = Apply (Lambda "x" (Variable "x")) (Variable "y") -}

derive0 :: Term -> Derivation
derive0 t = aux ((genContext (free (t)) [(At "")] []), t, At "") where
  aux :: Judgement -> Derivation
  aux (c,Variable v,ty) = Axiom (c ,Variable v,ty)
  aux (c,Lambda v t, ty) = Abstraction (c ,Lambda v t, ty) (aux ((genContext (free t) [ty] c) ++ c, t, ty))
  aux (c, Apply t t2, ty) = Application (c, Apply t t2, ty) (aux ((genContext (free t) [ty] c) ++ c, t, ty)) (aux ((genContext (free t2) [ty] c) ++ c, t2, ty))


derive1 :: Term -> Derivation
derive1 t = aux (tail atoms) ((genContext (free (t)) [At a | a <- atoms] []), t, At (head atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux a (c,Variable v,ty) = Axiom (c ,Variable v, At (head a))

    aux a (c,Lambda v t, ty) = Abstraction (c ,Lambda v t, At (head a))
     (aux (dropa (length (free t)+1) a)
      ((genContext (free t) [At a | a <- (tail a)] c) ++ c, t, ty))

    aux a (c, Apply t t2, ty) = Application 
    
     (c, Apply t t2, At (head a))

     (aux (dropa (length (free t)+1) [x | (x,i) <- zip a [0..], even i])
       ((genContext (free t) (tail [At x | (x,i) <- zip a [0..], even i] ) c) ++ c, t, ty))

     (aux (dropa (length (free t2)+1) [x | (x,i) <- zip a [0..], odd i] )
       ((genContext (free t2) (tail [At x | (x,i) <- zip a [0..], odd i]) c) ++ c, t2, ty))

extractType :: Judgement -> Type
extractType (_,_,ty) = ty

extractContext :: Judgement -> Context
extractContext (c,_,_) = c

upairs :: Derivation -> [Upair]
upairs (Axiom (c, Variable v,ty)) = [(find v c,ty)]
upairs (Abstraction (c,Lambda v t,ty) d) = [(ty, (find v (extractContext (conclusion d))):-> extractType (conclusion d))]++ upairs d
upairs (Application (c,Apply t t2,ty) d d2)=[(extractType (conclusion d),extractType (conclusion d2):->ty)]++ upairs d ++ upairs d2


derive :: Term -> Derivation
derive t =  subs_der (unify (upairs (derive1 t))) (derive1 t)

