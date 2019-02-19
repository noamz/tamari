-- Some routines on partial bijections and permutations

module Bijections where

import Control.Monad
import Control.Monad.State
import Data.Maybe
import Data.List

-- generate all 2^n possible splittings of a list of length n
split :: [a] -> [([a],[a])]
split [] = return ([],[])
split (a:as) = do
  (l,r) <- split as
  return (a:l,r) ++ return (l,a:r)

-- generate all n+1 possible splittings of a list of length n into
-- two contiguous pieces
-- satisfies: splitC g == [splitAt i g | i <- [0..length g]]
splitC :: [a] -> [([a],[a])]
splitC [] = [([],[])]
splitC (a:as) = ([],a:as) : [(a:l,r) | (l,r) <- splitC as]

-- generate all n-1 possible splittings of a list of length n into
-- two contiguous non-empty pieces
-- satisfies: splitCN g == [splitAt i g | i <- [1..length g-1]]
splitCN :: [a] -> [([a],[a])]
splitCN [] = []
splitCN [a] = []
splitCN [a,b] = [([a],[b])]
splitCN (a1:a2:as) = ([a1],a2:as) : ([a1,a2],as) : [(a1:a2:l,r) | (l,r) <- splitCN as]

-- generate all n ways of removing an element from a list of length n
remove :: [a] -> [(a,[a])]
remove [] = []
remove (a:as) = (a,as) : [(a',a:as') | (a',as') <- remove as]

-- generate all (k)_n injective mappings of a list of length k into a
-- list of length n
inject :: [a] -> [b] -> [[(a,b)]]
inject [] _ = return []
inject (a:as) bs = do
  (b,rest) <- remove bs
  f <- inject as rest
  return ((a,b):f)

-- generate all binom (m+n-1) m monotone mappings of a list of length
-- m into a list of length n
monotone :: [a] -> [b] -> [[(a,b)]]
monotone [] _ = [[]]
monotone (a:as) [] = []
monotone (a:as) (b:bs) = map ((a,b):) (monotone as (b:bs)) ++ monotone (a:as) bs

-- generate all (k)_n ways of removing k elements from a list of length n, where order matters
choose :: Int -> [a] -> [([a],[a])]
choose 0 as = return ([],as)
choose k as = do
  (a,rest) <- remove as
  (as',rest') <- choose (k-1) rest
  return (a:as',rest')

-- generate all binom n k ways of removing k elements from a list of length n, where order doesn't matter
choosek :: Int -> [a] -> [([a],[a])]
choosek 0 as = [([],as)]
choosek k [] = []
choosek k (a:as) = [(a:as',bs) | (as',bs) <- choosek (k-1) as] ++
                   [(as',a:bs) | (as',bs) <- choosek k as]

-- generate all binom (n+k) k shuffles of a list of length k into a
-- list of length n
shuffle :: [a] -> [a] -> [[a]]
shuffle [] bs = [bs]
shuffle as [] = [as]
shuffle (a:as) (b:bs) = [a:x | x <- shuffle as (b:bs)] ++
                        [b:x | x <- shuffle (a:as) bs]

-- generate all n! permutations of a list of length n
permute :: [a] -> [[(a,a)]]
permute as = inject as as

-- generate all n! permutations of a list of length n, but representing
-- each permutation as an array rather than as a mapping.
permutation :: [a] -> [[a]]
permutation as = [map snd p | p <- permute as]

-- generate injections fixing the first element
injectFF :: [a] -> [b] -> [[(a,b)]]
injectFF (a:as) (b:bs) = [(a,b):f | f <- inject as bs]

-- generate all (2*n-1)!! fixed-point free involutions of a list of length 2*n
involute :: [a] -> [[(a,a)]]
involute [] = return []
involute (a:as) = do
  (b,rest) <- remove as
  f <- involute rest
  return ((a,b):(b,a):f)

-- generate partial involutions, fixing all but 2*n elements of the list
pinvolute :: Int -> [a] -> [[(a,a)]]
pinvolute 0 as = return [(a,a) | a <- as]
pinvolute n [] = []
pinvolute n (a:as) = do
  (b,rest) <- remove as
  f <- pinvolute (n-1) rest
  return ((a,b):(b,a):f)

-- generate all n cyclic permutations of a list of length n
cycleonce :: [a] -> [[a]]
cycleonce xs = cycle' xs []
  where
    cycle' :: [a] -> [a] -> [[a]]
    cycle' [] acc = []
    cycle' (x:xs) acc = [x:xs ++ reverse acc] ++ cycle' xs (x:acc)

-- generate all n choose k ways of splitting a list of length n into k+1 contiguous non-empty pieces
stirling0 :: Int -> [a] -> [[[a]]]
stirling0 1 as = return [as]
stirling0 n as = do
  i <- [1..length as-1]
  let (x,rest) = splitAt i as
  map (x:) $ stirling0 (n-1) rest

-- generate all s(n,k) ways of partitioning a list of length n into k+1 non-empty cycles
stirling1 :: Int -> [a] -> [[[a]]]
stirling1 1 as = return [as]
stirling1 n as = do
  i <- [1..length as-1]
  (x,rest) <- choose i as
  map (x:) $ stirling1 (n-1) rest

-- partial bijections/injections on finite sets of integers

type Bij = [(Int,Int)]
type Perm = Bij

perm2 :: Int -> Int -> Perm
perm2 a b = [(a,b),(b,a)]

perm3 :: Int -> Int -> Int -> Perm
perm3 a b c = [(a,b),(b,c),(c,a)]

dom :: Bij {-a-} {-b-} -> [Int {-a-}]
dom p = map fst p

cod :: Bij {-a-} {-b-} -> [Int {-b-}]
cod p = map snd p

act :: Bij {-a-} {-b-} -> Int {-a-} -> Int {-b-}
act p i =
  case lookup i p of
    Just j -> j
    Nothing -> error ("could not find " ++ show i ++ " in " ++ show p)

act_partial :: Bij {-a-} {-b-} -> Int {-a-} -> Int {-b-}
act_partial p i =
  case lookup i p of
    Just j -> j
    Nothing -> i

inv :: Bij {-a-} {-b-} -> Bij {-b-} {-a-}
inv p = map (\(x,y) -> (y,x)) p

-- compose in sequential order
comp :: Bij {-a-} {-b-} -> Bij {-b-} {-c-} -> Bij {-a-} {-c-}
comp p q = [(i,act q (act p i)) | i <- dom p]

comps :: [Bij] -> Bij
comps [p] = p
comps (p:ps) = comp p (comps ps)

conjugate :: Bij {-a-} {-b-} -> Perm {-a-} -> Perm {-b-}
conjugate p alpha = [(i, act p $ act_partial alpha $ act (inv p) $ i) | i <- cod p]

eqperm :: Perm -> Perm -> Bool
eqperm p q = sort p == sort q

-- orbits, cyclic decomposition, etc.

-- gpaths f d1 d2 x computes the set of f-paths from d1 to d2 avoiding x
gpaths :: Eq d => (d -> [d]) -> d -> d -> [d] -> [[d]]
gpaths f d1 d2 visited =
  [[] | d1 == d2] ++
  [d1:p | d' <- f d1, not (elem d' visited), p <- gpaths f d' d2 (d1:visited)]

-- orbit f d computes the (reversed) orbit of d under f, using an accumulator
orbit_acc :: Eq d => (d -> d) -> d -> [d] -> [d]
orbit_acc f d acc = 
  let d' = f (head acc) in
  if d' == d then acc else orbit_acc f d (d' : acc)

orbit :: Eq d => (d -> d) -> d -> [d]
orbit f d = reverse (orbit_acc f d [d])

orbits :: Eq d => (d -> d) -> [d] -> [[d]] -> [[d]]
orbits f [] acc = acc
orbits f (d:ds) acc = 
  let o = orbit f d in
  orbits f (filter (\d' -> not (elem d' o)) ds) (o : acc)

permToCycles :: Perm -> [[Int]]
permToCycles p = orbits (act p) (dom p) []

cyclesToPerm :: [[Int]] -> Perm
cyclesToPerm cs = concat [zip c (tail c ++ [head c]) | c <- cs]

-- generate all 2^{n-1} partitions of a non-empty list into non-empty consecutive regions
parts :: [a] -> [[[a]]]
parts [x] = return [[x]]
parts (x:xs) = do
  (p:ps) <- parts xs
  [[x]:(p:ps),(x:p):ps]

-- given two permutations alpha and beta, "residual alpha beta"
-- computes a list of permutations p such that
-- eqperm (conjugate p alpha) beta.
residual :: Perm -> Perm -> [Perm]
residual alpha beta =
  -- compute cyclic decompositions of alpha and beta
  let calpha = map (\c -> (length c, c)) (orbits (act alpha) (dom alpha) []) in
  let cbeta = map (\c -> (length c, c)) (orbits (act beta) (dom beta) []) in
  match_cycles calpha cbeta
  where
    match_cycles :: [(Int,[Int])] -> [(Int,[Int])] -> [Perm]
    match_cycles [] [] = return []
    match_cycles ((n,c):cs) mds = do
      let (d's, mds') = partition (\ (m,d) -> m == n) mds
      (d, d''s) <- remove (map snd d's)
      p <- match_cycles cs ((map (\d -> (n,d)) d''s) ++ mds')
      q <- match_cycle c d
      return (p ++ q)
    match_cycle :: [Int] -> [Int] -> [Perm]
    match_cycle c d = do
      d' <- cycleonce d
      return (zip c d')

-- compute the cycle decomposition lengths of a permutation, in descending order
clengths :: Perm -> [Int]
clengths p = sortBy (flip compare) $ map length (orbits (act p) (dom p) [])

passport :: (Perm,Perm,Perm) -> ([Int],[Int],[Int])
passport (x,y,z) = (clengths x,clengths y,clengths z)

isCyclic :: Perm -> Bool
isCyclic p = length (orbits (act p) (dom p) []) == 1

-- routines for talking about fixpoints

fixpoints :: Perm -> [Int]
fixpoints p = [i | i <- dom p, act p i == i]

roots :: Perm -> [Int]
roots p = fixpoints (comp p p)

pathToFixed :: Perm -> Int -> [Int] -> [Int]
pathToFixed p x acc =
  let px = act_partial p x in
  if px == x then x : acc else pathToFixed p px (x : acc)

-- gtrans f d computes the transitive closure of a set of elements under a non-deterministic function f
gtrans :: Eq d => (d -> [d]) -> [d] -> [d] -> [d]
gtrans f [] acc = acc
gtrans f (d:ds) acc = if elem d acc then gtrans f ds acc
                      else gtrans f ((nub (f d) \\ (d:acc)) ++ ds) (d:acc)

transClosure :: [Perm] -> [Int] -> [Int]
transClosure ps src =
  let gact i = foldr (\p ys -> union [act_partial p i] ys) [] ps in
  sort (gtrans gact src [])
  
-- isTransitive ps src dst checks that dst is the transitive closure of src under ps
isTransitive :: [Perm] -> [Int] -> [Int] -> Bool
isTransitive ps src dst = transClosure ps src == sort dst


isInvolution :: (Int -> Int) -> [Int] -> Bool
isInvolution f xs = all (\i -> f (f i) == i) xs

fpfreeInvolution :: Perm -> Bool
fpfreeInvolution p = all (\i -> act p i /= i && act p (act p i) == i) (dom p)

isCubic :: (Int -> Int) -> [Int] -> Bool
isCubic f xs = all (\i -> f (f (f i)) == i) xs

isQuartic :: (Int -> Int) -> [Int] -> Bool
isQuartic f xs = all (\i -> f (f (f (f i))) == i) xs

-- basic swap and 3-cycle
swap x y = \a -> if a == x then y else if a == y then x else a
trip x y z = \a -> if a == x then y else if a == y then z else if a == z then x else a

-- determinize a non-deterministic mapping
determine :: Eq a => [(a,b)] -> [[(a,b)]]
determine [] = return []
determine ((a,b):f) =
  if isNothing (lookup a f) then [(a,b):f' | f' <- determine f]
  else [(a,b):f1 | f1 <- determine (filter (\ (a',_) -> a' /= a) f)] ++
       determine f

-- compute equivalence classes
equivClassesBy :: (a -> a -> Bool) -> [a] -> [[a]] -> [[a]]
equivClassesBy eq [] acc = acc
equivClassesBy eq (a:as) acc =
  equivClassesBy eq as (insert eq a acc)
  where
    insert :: (a -> a -> Bool) -> a -> [[a]] -> [[a]]
    insert eq a [] = [[a]]
    insert eq a ((b:bs):as) = if eq a b then (a:b:bs):as else (b:bs) : insert eq a as

-- turn a permutation into a fixed-point free involution on twice as many elements
permToInvol :: Perm -> Perm
permToInvol p =
  let f = [(2*i,2*j+1) | (i,j) <- p] in
  f ++ map (\(i,j) -> (j,i)) f

-- standardize a sequence of distinct integers
stdize :: [Int] -> [Int]
stdize w =
  let n = length w in
  let w' = sortBy (\(x,i) (y,j) -> compare x y) (zip w [1..n]) in
  let p = zip (map snd w') [1..n] in
  map (act p) [1..n]

-- interpret a standard sequence as a permutation
stdToPerm :: [Int] -> Perm
stdToPerm w = zip [1..length w] w

-- operadic structure of permutations-as-arrays
data PermA = PA { src :: [Int], tgt :: [Int] }
  deriving Show

fromPerm :: Perm -> PermA
fromPerm p = PA { src = dom p, tgt = map (act p) (dom p) }

canonPermA :: PermA -> PermA
canonPermA p =
  PA { src = [1..length (src p)],
       tgt = map (act (zip (src p) [1..])) (tgt p) }

pcomp :: Int -> PermA -> PermA -> PermA
pcomp i p q =
  let in1 = map (2*) in
  let in2 = map ((1+) . (2*)) in
  let (srcp1,xi:srcp2) = splitAt i (src p) in
  let pi = fromJust (elemIndex xi (tgt p)) in
  let (tgtp1,_:tgtp2) = splitAt pi (tgt p) in
  PA { src = in1 srcp1 ++ in2 (src q) ++ in1 srcp2,
       tgt = in1 tgtp1 ++ in2 (tgt q) ++ in1 tgtp2 }

decomp :: Int -> [PermA]
decomp n = nubBy (\p q -> tgt p == tgt q) [canonPermA $ pcomp i (fromPerm p) (fromPerm q) | k <- [2..n-1], p <- permute [1..k], q <- permute [1..n-k+1], i <- [0..k-1]]

-- unordered partitions of a natural number n whose largest part is k
uparts :: Integer -> Integer -> [[Integer]]
uparts n k = if k > n then [] else if k == n then [[k]] else [k : p | j <- reverse [1..k], p <- uparts (n-k) j]

up :: Integer -> [[Integer]]
up 0 = [[]]
up n = [p | k <- reverse [1..n], p <- uparts n k]

