-- experiments with the Tamari order and Tamari lattices
-- see paper "A sequent calculus for a semi-associative law" (LMCS)

module Tamari where

import Data.List
import Data.Maybe
import Catalan
import Control.Monad

rotR1 :: Bin -> [Bin]
rotR1 (B (t1 @ (B t11 t12)) t2) =
  B t11 (B t12 t2) : [B t1' t2 | t1' <- rotR1 t1] ++ [B t1 t2' | t2' <- rotR1 t2]
rotR1 (B L t2) = [B L t2' | t2' <- rotR1 t2]
rotR1 _ = []

rotL1 :: Bin -> [Bin]
rotL1 (B t1 (t2 @ (B t21 t22))) =
  B (B t1 t21) t22 : [B t1' t2 | t1' <- rotL1 t1] ++ [B t1 t2' | t2' <- rotL1 t2]
rotL1 (B t1 L) = [B t1' L | t1' <- rotL1 t1]
rotL1 _ = []

tamari_up :: Bin -> [Bin]
tamari_up t = t : foldr union [] [tamari_up t' | t' <- rotR1 t]

tamari_down :: Bin -> [Bin]
tamari_down t = t : foldr union [] [tamari_down t' | t' <- rotL1 t]

tamari_order :: Bin -> Bin -> Bool
tamari_order t1 t2 = elem t2 (tamari_up t1)

kreweras_order :: Bin -> Bin -> Bool
kreweras_order L L = True
kreweras_order (B t1 t2) (B t1' t2') =
  (kreweras_order t1 t1' && kreweras_order t2 t2') ||
  case t1 of
    B t11 t12 -> kreweras_order (B t11 (B t12 t2)) (B t1' t2')
    L -> False
kreweras_order _ _ = False

tamari :: Int -> [(Bin,Bin)]
tamari n = [(t1,t2) | t1 <- binary_trees n, t2 <- tamari_up t1]
-- [length $ tamari n | n <- [0..]] == [1,1,3,13,68,399,2530,...]

kreweras :: Int -> [(Bin,Bin)]
kreweras n = [(t1,t2) | t1 <- binary_trees n, t2 <- binary_trees n, kreweras_order t1 t2]

tamari_parts :: Int -> [Int]
tamari_parts n = [length $ tamari_down t | t <- binary_trees n]

-- some properties of the Tamari lattice

-- If t<=u in the Tamari order, then the left-branching spine of t is at
-- least as long as the left-branching spine of u.
prop1 :: Int -> Bool
prop1 n =
  flip all (tamari n) $ \(t1,t2) ->
  length (bin2spine t1) >= length (bin2spine t2)

-- sequent-style decision procedure for Tamari order
tamari_seq :: [Bin] -> Bin -> Bin -> Bool
tamari_seq g (B t1 t2) u = tamari_seq (t2:g) t1 u
tamari_seq g L L = g == []
tamari_seq g L (B u1 u2) =
  let k = leaves u1 in
  let grab k g acc =
        if k == 0 then Just (acc,g)
        else if g == [] then Nothing
        else
          let (t:g') = g in
          let i = leaves t in
          if i > k then Nothing
          else grab (k - i) g' (t:acc) in
  case grab (k-1) g [] of
    Nothing -> False
    Just (g1,t2:g2) -> tamari_seq (reverse g1) L u1 && tamari_seq g2 t2 u2
    Just (g1,[]) -> False

-- soundness & completeness of the sequent calculus
prop2 :: Int -> Bool
prop2 n =
  flip all (binary_trees n) $ \t1 ->
  flip all (binary_trees n) $ \t2 ->
  tamari_order t1 t2 == tamari_seq [] t1 t2

-- focused sequent calculus
tamari_linv :: Bin -> [Bin] -> Bin -> Bool
tamari_neu :: [Bin] -> Bin -> Bool
tamari_linv t g u = let ts = bin2spine t in tamari_neu (reverse ts ++ g) u
tamari_neu g L = g == []
tamari_neu g (B u1 u2) =
  let k = leaves u1 in
  let grab k g acc =
        if k == 0 then Just (acc,g)
        else if g == [] then Nothing
        else
          let (t:g') = g in
          let i = leaves t in
          if i > k then Nothing
          else grab (k - i) g' (t:acc) in
  case grab (k-1) g [] of
    Nothing -> False
    Just (g1,t2:g2) -> tamari_neu (reverse g1) u1 && tamari_linv t2 g2 u2
    Just (g1,[]) -> False

-- faster generation of intervals
tamari' :: Int -> [(Bin,Bin)]
tamari' n = [(t1,t2) | t1 <- binary_trees n, t2 <- binary_trees n, tamari_linv t1 [] t2]

-- soundness and completeness of the focused sequent calculus
prop3 :: Int -> Bool
prop3 n =
  flip all (binary_trees n) $ \t1 ->
  flip all (binary_trees n) $ \t2 ->
  tamari_linv t1 [] t2 == tamari_seq [] t1 t2

-- lattice structure
max_decomp :: Bin -> [Bin] -> [Bin]
max_decomp L acc = L : acc
max_decomp (B t1 t2) acc = max_decomp t1 (t2 : acc)

max_recomp :: [Bin] -> Bin
max_recomp (t:ts) = foldl B t ts

tamari_bot :: Int -> Bin
tamari_bot n = iterate (\x -> B x L) L !! n

tamari_top :: Int -> Bin
tamari_top n = iterate (\x -> B L x) L !! n

tamari_join :: Bin -> Bin -> Bin
tamari_join L L = L
tamari_join t1 t2 =
  let (L:g1) = max_decomp t1 [] in
  let (L:g2) = max_decomp t2 [] in
  max_recomp (L:tamari_seqjoin g1 g2)

tamari_seqjoin :: [Bin] -> [Bin] -> [Bin]
tamari_seqjoin [] [] = []
tamari_seqjoin [] (a2:g2) = error "tamari_seqjoin : |g1| < |g2|"
tamari_seqjoin (a1:g1) [] = error "tamari_seqjoin : |g1| > |g2|"
tamari_seqjoin (a1:g1) (a2:g2) =
  let k1 = leaves a1 in
  let k2 = leaves a2 in
  if k1 < k2 then
    tamari_seqjoin (B a1 (head g1) : (tail g1)) (a2:g2)
  else if k1 > k2 then
    tamari_seqjoin (a1:g1) (B a2 (head g2) : (tail g2))
  else tamari_join a1 a2 : tamari_seqjoin g1 g2

tamari_meet :: Bin -> Bin -> Bin
tamari_meet t1 t2 =
  let n = nodes t1 in
  foldr tamari_join (tamari_bot n) [t | t <- binary_trees n, tamari_linv t [] t1, tamari_linv t [] t2]

tamari_meet' :: Bin -> Bin -> Bin
tamari_meet' t1 t2 = dualbin (tamari_join (dualbin t1) (dualbin t2))

prop4 :: Int -> Bool
prop4 n =
  flip all (binary_trees n) $ \t1 ->
  flip all (binary_trees n) $ \t2 ->
  tamari_linv t1 [] t2 == (tamari_join t1 t2 == t2)

prop5 :: Int -> Bool
prop5 n =
  flip all (binary_trees n) $ \t1 ->
  flip all (binary_trees n) $ \t2 ->
  tamari_linv t1 [] t2 == (tamari_meet t1 t2 == t1)

prop6 :: Int -> Bool
prop6 n =
  flip all (binary_trees n) $ \t1 ->
  flip all (binary_trees n) $ \t2 ->
  tamari_linv t1 [] t2 == (tamari_meet' t1 t2 == t1)

bin_type :: Bin -> [Bool]
bin_type t = pol False t
  where
    pol :: Bool -> Bin -> [Bool]
    pol b L = [b]
    pol b (B t1 t2) = pol False t1 ++ pol True t2

tamari_meetIrr :: Bin -> Bool
tamari_meetIrr t =
  let n = nodes t in
  let ts = binary_trees n \\ [tamari_top n,t] in
  t /= tamari_top n && all id [tamari_meet' t1 t2 /= t | t1 <- ts, t2 <- ts]

tamari_joinIrr :: Bin -> Bool
tamari_joinIrr t =
  let n = nodes t in
  let ts = binary_trees n \\ [tamari_bot n,t] in
  t /= tamari_bot n && all id [tamari_join t1 t2 /= t | t1 <- ts, t2 <- ts]

{-
> [length [(t1,t2) | let ts = filter tamari_joinIrr (binary_trees n), t1 <- ts, t2 <- ts, tamari_linv t1 [] t2] | n <- [1..]]
[0,1,4,10,20,35,  C-c C-cInterrupted.
-- A000292?
> [length [(t1,t2) | t1 <- filter tamari_joinIrr (binary_trees n), t2 <- filter tamari_meetIrr (binary_trees n), tamari_linv t1 [] t2] | n <- [1..]]
[0,0,4,21,65,155,  C-c C-cInterrupted.
-- A212246?
-}

-- canopy intervals
ntamari_linv :: Bin -> [Bin] -> Bin -> Bool
ntamari_neu :: [Bin] -> Bin -> Bool
ntamari_linv L [] L = True
ntamari_linv L g _ = False
ntamari_linv t g u = let ts = bin2spine t in ntamari_neu (reverse ts ++ g) u
ntamari_neu g L = g == []
ntamari_neu g (B u1 u2) =
  let k = leaves u1 in
  let grab k g acc =
        if k == 0 then Just (acc,g)
        else if g == [] then Nothing
        else
          let (t:g') = g in
          let i = leaves t in
          if i > k then Nothing
          else grab (k - i) g' (t:acc) in
  case grab (k-1) g [] of
    Nothing -> False
    Just (g1,t2:g2) -> ntamari_neu (reverse g1) u1 && ntamari_linv t2 g2 u2
    Just (g1,[]) -> False

-- > [length [(t1,t2) | t1 <- binary_trees n, t2 <- binary_trees n, ntamari_linv t1 [] t2] | n <- [1..]]
-- [1,2,6,22,91,408,1938,  C-c C-cInterrupted.
-- https://oeis.org/A000139 == rooted non-separable planar maps with n edges == canopy intervals in the Tamari lattices

-- question: what is the probability that a random pair of trees (t1,t2) with n nodes are related by the Tamari order t1 <= t2?
-- answer: # intervals in Yn / (Cn * Cn) = 2 * (4*n+1)! * n!^2 * (n+1)! / ((3*n+2)!*(2*n)!^2)
-- here we test this formula experimentally
tamintprob :: Int -> Int -> IO Int
tamintprob n samples = do
  tests <- replicateM samples experiment
  let total = foldr (\b total -> if b then 1+total else total) 0 tests
  return total 
  where
    experiment :: IO Bool
    experiment = do
      t1 <- remy_bin' n
      t2 <- remy_bin' n
      return $ tamari_linv t1 [] t2
{-
> tamintprob 5 1000000
226166
-- compare to expected probability = 19/84 = 0.226190...
> tamintprob 12 1000000
8515
-- compare to expected probability = 82861/9598268 = 0.00863291...
> tamintprob 20 100000
19
-- compare to expected probability = 82300857/491762021465 = 0.000167359...
-}
