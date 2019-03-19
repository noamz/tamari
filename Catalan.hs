-- code for generating/manipulating binary trees and related Catalan objects

module Catalan where

import Data.List
import Data.Maybe
import Data.Typeable
import System.Random

import Bijections

data Bin = L | B Bin Bin
  deriving (Show,Eq,Ord,Typeable)

foldBin :: a -> (a -> a -> a) -> Bin -> a
foldBin l b L = l
foldBin l b (B t1 t2) = b (foldBin l b t1) (foldBin l b t2)

-- dualization (mirror image) operation on binary trees

dualbin :: Bin -> Bin
dualbin L = L
dualbin (B t1 t2) = B (dualbin t2) (dualbin t1)

-- graft product: lgraft t1 t2 grafts t1 onto the leftmost leaf of t2

lgraft t1 t2 = foldr (\x y -> B y x) t1 (bin2spine t2)

-- rgraft t1 t2 grafts t2 onto the rightmost leaf of t1
rgraft t1 t2 = dualbin (lgraft (dualbin t2) (dualbin t1))

-- factoring a binary tree along its left-branching spine

bin2spine :: Bin -> [Bin]
bin2spine L = []
bin2spine (B t1 t2) = t2 : bin2spine t1

spine2bin :: [Bin] -> Bin
spine2bin s = foldr (\y x -> B x y) L s

-- statistics
nodes :: Bin -> Int
nodes L = 0
nodes (B t1 t2) = 1 + nodes t1 + nodes t2

leaves :: Bin -> Int
leaves L = 1
leaves (B t1 t2) = leaves t1 + leaves t2

-- generate all binary trees with n nodes
binary_trees :: Int -> [Bin]
binary_trees 0 = [L]
binary_trees n = [B t1 t2 | i <- [0..n-1], t1 <- binary_trees i, t2 <- binary_trees (n-1-i)]

-- procedure for sprouting a leaf off to the left or right (used in Rémy's algorithm)
sprout :: Bin -> Bool -> Int -> Bin
sprout t dir n = sprout_cps t dir n id (error "sprout: index out of bounds")
  where
    -- written in continuation passing style using success and failure continuations
    sprout_cps :: Bin -> Bool -> Int -> (Bin -> r) -> (Int -> r) -> r
    sprout_cps t dir 0 ks kf = ks (if dir then B L t else B t L)
    sprout_cps (B t1 t2) dir n ks kf = sprout_cps t1 dir (n-1) (\t1' -> ks (B t1' t2))
                                       (\n' -> sprout_cps t2 dir n' (\t2' -> ks (B t1 t2')) kf)
    sprout_cps L dir n ks kf = kf (n-1)

-- generate a uniformly random binary tree with n nodes via Rémy's algorithm
remy_bin :: RandomGen g => Int -> g -> (Bin,g)
remy_bin 0 g = (L, g)
remy_bin n g =
  let (t,g') = remy_bin (n-1) g in
  let (i,g'') = randomR (0,2*n-2) g' in
  let (d,g''') = randomR (False,True) g'' in
  (sprout t d i, g''')

remy_bin' :: Int -> IO Bin
remy_bin' n = getStdRandom (remy_bin n)

-- three different ways of converting binary trees to matching parentheses
showBinL :: Bin -> String
showBinL L = "*"
showBinL (B t1 t2) = "(" ++ showBinL t1 ++ ")" ++ showBinL t2

showBinU :: Bin -> String
showBinU L = "*"
showBinU (B t1 t2) = "(" ++ showBinU t1 ++ showBinU t2 ++ ")"

showBinR :: Bin -> String
showBinR L = "*"
showBinR (B t1 t2) = showBinR t1 ++ "(" ++ showBinR t2 ++ ")"

-- conversion between binary trees and arc diagrams/double-occurrence words
data Arc = U Int | D Int
  deriving (Show,Eq,Ord,Typeable)
type Arcs = [Arc]

isup (U _) = True
isup (D _) = False
isdown (U _) = False
isdown (D _) = True

arcs2bin_cps :: Int -> Arcs -> (String -> r) -> (Arcs -> Bin -> r) -> r
arcs2bin_cps x (D y:w) fail k = if x == y then k w L else fail "not a planar arc diagram"
arcs2bin_cps x (U y:w) fail k = arcs2bin_cps y w fail $ \w' t1 -> arcs2bin_cps x w' fail $ \w'' t2 -> k w'' (B t1 t2)
arcs2bin_cps x [] fail k = fail "not a closed arc diagram"

arcs2bin :: Arcs -> Bin
arcs2bin [] = L
arcs2bin (U x:xs) = arcs2bin_cps x xs (\s -> error s) (\w' t -> B t (arcs2bin w'))
arcs2bin (D x:xs) = error "not a closed arc diagram"

isDyck :: Arcs -> Bool
isDyck [] = True
isDyck (U x:xs) = arcs2bin_cps x xs (\_ -> False) (\_ _ -> True)
isDyck (D _:_) = False

isClosed :: Arcs -> Bool
isClosed [] = True
isClosed (U x:xs) =
  let (pre,post) = span (/=D x) xs in
  if null post then False else isClosed (pre ++ tail post)
isClosed (D x:xs) = False

bin2arcs_st :: Bin -> Int -> (Int,Arcs)
bin2arcs_st L n = (n,[])
bin2arcs_st (B t1 t2) n =
  let (n',w1) = bin2arcs_st t1 (n+1) in
  let (n'',w2) = bin2arcs_st t2 n' in
  (n'',U n : w1 ++ D n : w2)

bin2arcs :: Bin -> Arcs
bin2arcs t = let (n,w) = bin2arcs_st t 0 in w

normalizeArcs :: Arcs -> Arcs
normalizeArcs w =
  scan 0 [] w
  where
    scan :: Int -> [(Int,Int)] -> Arcs -> Arcs
    scan n sigma [] = []
    scan n sigma (U x:w) = U n:scan (n+1) ((x,n):sigma) w
    scan n sigma (D x:w) = D (fromJust $ lookup x sigma):scan n sigma w

maparcs :: (Int -> Int) -> (Int -> Int) -> Arcs -> Arcs
maparcs f g [] = []
maparcs f g (U x:w) = U (f x) : maparcs f g w
maparcs f g (D x:w) = D (g x) : maparcs f g w

arcs2dow :: Arcs -> [Int]
arcs2dow [] = []
arcs2dow (U x:w) = x:arcs2dow w
arcs2dow (D x:w) = x:arcs2dow w

dow2arcs :: [Int] -> Arcs
dow2arcs w = marked w []
  where
    marked :: [Int] -> [Int] -> Arcs
    marked [] seen = []
    marked (x:xs) seen = if elem x seen then D x:marked xs seen else U x:marked xs (x:seen)

arcs2signs :: Arcs -> [Bool]
arcs2signs [] = []
arcs2signs (U _:w) = False:arcs2signs w
arcs2signs (D _:w) = True:arcs2signs w

fliparcs :: Arcs -> Arcs
fliparcs [] = []
fliparcs (U x:w) = D x:fliparcs w
fliparcs (D x:w) = U x:fliparcs w

-- generate an arc diagram from an involution
inv2arcs :: [(Int,Int)] -> Arcs
inv2arcs f = map (\i -> let j = act f i in if i < j then U i else D j)
             (sort $ dom f)

-- generate an involution from an arc diagram
arcs2inv :: Arcs -> [(Int,Int)]
arcs2inv p =
  let n = length p in
  let act i = case p !! i of
        U x -> fromJust (findIndex (== D x) p)
        D x -> fromJust (findIndex (== U x) p) in
  [(i,act i) | i <- [0..n-1]]

-- coercions checking that a binary tree has a special form

rightleaf :: Bin -> Bin
rightleaf (B t L) = t
rightleaf _ = error "binary tree not of form (B t L)"

leftleaf :: Bin -> Bin
leftleaf (B L t) = t
leftleaf _ = error "binary tree not of form (B L t)"


type BinPath =  [Either () ()]
  
paths :: Bin -> [BinPath]
paths L = [[]]
paths (B t1 t2) = [Left () : p1 | p1 <- paths t1] ++ [Right () : p2 | p2 <- paths t2]

ldepth :: BinPath -> Int
ldepth (Left ():p) = 1 + ldepth p
ldepth _ = 0

rdepth :: BinPath -> Int
rdepth (Right ():p) = 1 + rdepth p
rdepth _ = 0

-- evaluate a binary tree in left-to-right order, given interpretations for the leaves and
-- interpretations for the internal nodes as binary operations
evalLR :: Bin -> ([a],[a -> a -> a]) -> ([a],[a -> a -> a])
evalLR L (stk,ctl) = (stk,ctl)
evalLR (B t1 t2) (stk,f:ctl) =
  let (x:stk',ctl') = evalLR t1 (stk,ctl) in
  let (y:stk'',ctl'') = evalLR t2 (stk',ctl') in
  (f x y:stk'',ctl'')

-- for a given binary tree, returns all binary trees which match it from the root
matchroot :: Bin -> [Bin]
matchroot L = [L]
matchroot (B t1 t2) = L : [B u1 u2 | u1 <- matchroot t1, u2 <- matchroot t2]

-- for a given binary tree, returns all occurrences of subtrees
subtrees :: Bin -> [Bin]
subtrees L = [L]
subtrees (B t1 t2) = subtrees t1 ++ subtrees t2  ++ matchroot (B t1 t2)

patternseries :: Bin -> [[Int]]
patternseries p =
  let n = nodes p in
  [[length $ filter (==i) [length $ filter (==p) (subtrees t) | t <- binary_trees m] | i <- [0..m]] | m <- [0..]]

-- [length $ filter (==i) [length $ filter (== B L (B L (B L L))) (subtrees t) | t <- binary_trees 5] | i <- [0..5]]
