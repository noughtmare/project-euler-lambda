{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Main where

import Debug.Trace

import Prelude hiding (Bool, or, and, not)

--------------------------------------------------------------------------------
-- Problem 1
--------------------------------------------------------------------------------

newtype SNat = SNat { unSNat :: forall x. (SNat -> x) -> x -> x }
newtype CNat = CNat { unCNat :: forall x. (x -> x) -> x -> x }
newtype Quad a b c d = Quad { unQuad :: forall x. (a -> b -> c -> d -> x) -> x }
newtype BNat = BNat { unBNat :: forall x. (BNat -> x) -> (BNat -> x) -> x -> x}

instance (Show a, Show b, Show c, Show d) => Show (Quad a b c d) where
  show q = unQuad q (\a b c d -> show (a,b,c,d))
instance Show CNat where
  show cn = show (unCNat cn (+ 1) 0 :: Integer)
instance Show SNat where
  show sn = show (go 0 sn :: Integer) where
    go s sn = unSNat sn (go (1 + s)) s
instance Show BNat where
  show bn = show (go 0 0 bn) where
    go :: Integer -> Integer -> BNat -> Integer
    go i s bn = unBNat bn (go (i + 1) s) (go (i + 1) ((2 :: Integer) ^ i + s)) s

newtype Fix a = In { out :: Fix a -> a }

-- GHC's inliner will blow up if this is allowed to inline
{-# NOINLINE diag #-}
diag = \x -> out x x

omega = diag (In diag)

fix = \f -> diag (In (\x -> f (out x x)))

ssuc = \x -> SNat (\s _ -> s x)
s0 = SNat (\_ z -> z)
s2 = ssuc (ssuc s0)
s4 = ssuc (ssuc s2)
ctimes = \x y -> CNat (\s z -> unCNat x (unCNat y s) z)
c10 = CNat (\s z -> s (s (s (s (s (s (s (s (s (s z))))))))))
c1000 = ctimes c10 (ctimes c10 c10)
quad = \a b c d -> Quad (\f -> f a b c d)
b0 = BNat (\_ _ z -> z)
b1 = BNat (\_ o _ -> o b0)
b2n = \x -> BNat (\e _ _ -> e x)
b2n1 = \x -> BNat (\_ o _ -> o x)
badd = fix (\badd x y ->
  let
    bsuc = \x -> badd x b1
    badd1 = fix (\badd1 x y -> unBNat x
      (\x' -> unBNat y
        (\y' -> b2n1 (badd x' y'))
        (\y' -> b2n (badd1 x' y'))
        (b2n1 x'))
      (\x' -> unBNat y
        (\y' -> b2n (badd1 x' y'))
        (\y' -> b2n1 (badd1 x' y'))
        (b2n (bsuc x')))
      (bsuc y))
  in
    unBNat x
      (\x' -> unBNat y
        (\y' -> b2n (badd x' y'))
        (\y' -> b2n1 (badd x' y'))
        (b2n x'))
      (\x' -> unBNat y
        (\y' -> b2n1 (badd x' y'))
        (\y' -> b2n (badd1 x' y'))
        (b2n1 x'))
      y)
bsuc = \x -> badd x b1

pe1 =
  unCNat c1000
    (\x -> unQuad x (\i r t f ->
      let
        i' = bsuc i
        r' = badd i r
      in unSNat t
        (\t' -> unSNat f
          (\f' -> quad i' r t' f')
          (quad i' r' t' s4))
        (unSNat f (\f' -> quad i' r' s2 f') (quad i' r' s2 s4))))
    (quad b0 b0 (ssuc s2) (ssuc s4))

-- >>> pe1
-- (1000,233168,2,0)

--------------------------------------------------------------------------------
-- Problem 2
--------------------------------------------------------------------------------

b2 = bsuc b1
b2e0 = b1
b2e1 = BNat (\e _ _ -> e b2e0)
b2e2 = BNat (\e _ _ -> e b2e1)
b2e3 = BNat (\e _ _ -> e b2e2)
b2e4 = BNat (\e _ _ -> e b2e3)
b2e5 = BNat (\e _ _ -> e b2e4)
b2e6 = BNat (\e _ _ -> e b2e5)
b2e7 = BNat (\e _ _ -> e b2e6)
b2e8 = BNat (\e _ _ -> e b2e7)
b2e9 = BNat (\e _ _ -> e b2e8)
b2e10 = BNat (\e _ _ -> e b2e9)
b2e11 = BNat (\e _ _ -> e b2e10)
b2e12 = BNat (\e _ _ -> e b2e11)
b2e13 = BNat (\e _ _ -> e b2e12)
b2e14 = BNat (\e _ _ -> e b2e13)
b2e15 = BNat (\e _ _ -> e b2e14)
b2e16 = BNat (\e _ _ -> e b2e15)
b2e17 = BNat (\e _ _ -> e b2e16)
b2e18 = BNat (\e _ _ -> e b2e17)
b2e19 = BNat (\e _ _ -> e b2e18)
b2e20 = BNat (\e _ _ -> e b2e19)
b2e21 = BNat (\e _ _ -> e b2e20)
b4000000 = badd b2e21 (badd b2e20 (badd b2e19 (badd b2e18 (badd b2e16 (badd b2e11 b2e8)))))
bcmp = fix (\bcmp x y lt eq gt -> unBNat x
  (\x' -> unBNat y
    (\y' -> bcmp x' y' lt eq gt)
    (\y' -> bcmp x' y' lt lt gt)
    (bcmp x' b0 lt eq gt))
  (\x' -> unBNat y
    (\y' -> bcmp x' y' lt gt gt)
    (\y' -> bcmp x' y' lt eq gt)
    gt)
  (unBNat y
    (\y' -> bcmp b0 y' lt eq gt)
    (\_ -> lt)
    eq))

pe2 = fix
  (\f s x y ->
    let
      s' = unBNat x (\_ -> badd s x) (\_ -> s) s
      r = f s' y (badd x y)
    in
      bcmp x b4000000 r r s)
  b0
  b1
  b2

-- >>> pe2
-- 4613732

--------------------------------------------------------------------------------
-- Problem 3
--------------------------------------------------------------------------------

b3 = bsuc b2
b4 = bsuc b3
b5 = bsuc b4
b6 = bsuc b5
b7 = bsuc b6
b8 = bsuc b7
b9 = bsuc b8

newtype Pair a b = Pair { unPair :: forall x. (a -> b -> x) -> x }

instance (Show a, Show b) => Show (Pair a b) where
  show p = unPair p (\x y -> show (x, y))

pair = \x y -> Pair (\f -> f x y)
p1 = \p -> unPair p (\x _ -> x)
p2 = \p -> unPair p (\_ x -> x)

btimes2 = \x -> BNat (\e _ _ -> e x)
btimes2plus1 = \x -> BNat (\_ o _ -> o x)

-- Uses continuation passing style
bsubk = fix (\bsubk x y ifneg k ->
  let
    -- sub with carry x - y - 1
    bsub1k = fix (\bsub1k x y ifneg k ->
      unBNat x
        (\x' -> unBNat y
          (\y' -> bsub1k x' y' ifneg (\z -> k (btimes2plus1 z)))
          (\y' -> bsub1k x' y' ifneg (\z -> k (btimes2 z)))
          (bsubk x b1 ifneg k))
        (\x' -> unBNat y
          (\y' -> bsubk x' y' ifneg (\z -> k (btimes2 z)))
          (\y' -> bsub1k x' y' ifneg (\z -> k (btimes2plus1 z)))
          (k b0))
        ifneg)
  in
    unBNat x
      (\x' -> unBNat y
        (\y' -> bsubk x' y' ifneg (\z -> k (btimes2 z)))
        (\y' -> bsub1k x' y' ifneg (\z -> k (btimes2plus1 z)))
        (k x))
      (\x' -> unBNat y
        (\y' -> bsubk x' y' ifneg (\z -> k (btimes2plus1 z)))
        (\y' -> bsubk x' y' ifneg (\z -> k (btimes2 z)))
        (k x))
      (unBNat y
        (\y' -> bsubk b0 y' ifneg k)
        (\_ -> ifneg)
        (k b0)))

-- >>> bsubk b1 b0 b2e10 (\x -> x)
-- 1
-- >>> bsubk b1 b1 b2e10 (\x -> x)
-- 0
-- >>> bsubk b0 b1 b2e10 (\x -> x)
-- 1024
-- >>> bsubk b2 b1 b2e10 (\x -> x)
-- 1
-- >>> bsubk b6 b3 b2e10 (\x -> x)
-- 3
-- >>> bsubk b4 b1 b2e10 (\x -> x)
-- 3
-- >>> bsubk b4 b3 b2e10 (\x -> x)
-- 1

bdiv = fix (\bdiv n d ->
  let
    r = unBNat n
      (\n' -> unPair (bdiv n' d) (\q r ->
        let
          r' = btimes2 r
        in
          bsubk r' d (pair (btimes2 q) r') (\r'' -> pair (btimes2plus1 q) r'')))
      (\n' -> unPair (bdiv n' d) (\q r ->
        let
          r' = btimes2plus1 r
        in
          bsubk r' d (pair (btimes2 q) r') (\r'' -> pair (btimes2plus1 q) r'')))
      (pair b0 b0)
  in
    bcmp n d (pair b0 n) r r)

-- >>> bdiv b5 b6
-- (0,5)

newtype Bool = Bool { unBool :: forall x. x -> x -> x }
instance Show Bool where
  show b = show (unBool b True False)
false = Bool (\_ y -> y)
true = Bool (\x _ -> x)

biszero = \x -> unBNat x biszero (\_ -> false) true

or = \x y -> unBool x true y
and = \x y -> unBool x y false
not = \x -> unBool x false true

bprime = \x -> fix (\go i ->
  bcmp i x
    (unPair (bdiv x i) (\_ r -> and (not (biszero r)) (go (badd i b1))))
    true
    false) -- this false is for the case that our starting i is already larger than x, which happens with b0 and b1
    b2

bLargestPrimeFactor = \x0 -> fix (\go x i s ->
  bcmp i x
    (unBool (bprime i)
      (unPair (bdiv x i) (\q r ->
        unBool (biszero r) (go q i i) (go x (badd i b1) s)))
      (go x (badd i b1) s))
    (unBool (bprime x) x s)
    s
  )
  x0
  b2
  b0

-- >>> bLargestPrimeFactor b6
-- 3

-- >>> bLargestPrimeFactor b2e10
-- 2

btimes10 = \x -> let x' = btimes2 x in badd (btimes2 (btimes2 x')) x'

d0 = btimes10
d1 = \x -> badd b1 (btimes10 x)
d2 = \x -> badd b2 (btimes10 x)
d3 = \x -> badd b3 (btimes10 x)
d4 = \x -> badd b4 (btimes10 x)
d5 = \x -> badd b5 (btimes10 x)
d6 = \x -> badd b6 (btimes10 x)
d7 = \x -> badd b7 (btimes10 x)
d8 = \x -> badd b8 (btimes10 x)
d9 = \x -> badd b9 (btimes10 x)

b13195 = d5 (d9 (d1 (d3 (d1 b0))))

-- >>> bLargestPrimeFactor b13195
-- 29

b600851475143 = d3 (d4 (d1 (d5 (d7 (d4 (d1 (d5 (d8 (d0 (d0 (d6 b0)))))))))))

-- >>> b600851475143
-- 600851475143

pe3 = bLargestPrimeFactor b600851475143

-- This one takes a while...
-- >>> pe3
-- 6857

-- Running this with optmizations takes about 4 seconds on my machine
main :: IO ()
main = print pe3
