module Int2 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

-- given i, return i + 1.
isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

-- given i, return i - 1.
ipred : Int → Int
ipred (+ (suc n)) = + n
ipred (+ zero) = - (suc zero)
ipred (- n) = - (suc n)

-- given i, return -i.
ineg : Int → Int
ineg (+ n) = - n
ineg (- n) = + n

-- given i & j, return i + j.
iplus : Int → Int → Int
iplus (+ zero) n = n
iplus (- zero) n = n
iplus (+ (suc m)) n = isuc (iplus (+ m) n)
iplus (- (suc m)) n = ipred (iplus (- m) n)

-- given i & j, return i - j.
iminus : Int → Int → Int
iminus (+ zero) n = ineg n
iminus (- zero) n = ineg n
iminus (+ (suc m)) n = isuc (iminus (+ m) n)
iminus (- (suc m)) n = ipred (iminus (- m) n)

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (+ zero) n = + zero
itimes (- zero) n = - zero 
itimes (+ (suc m)) n = iplus n (itimes (+ m) n)
itimes (- (suc m)) n = ineg (iminus n (itimes (- m) n))
