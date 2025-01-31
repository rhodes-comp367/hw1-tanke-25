module Int1 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- int a b represents (a - b).
  int : Nat → Nat → Int

-- given i, return i + 1.
isuc : Int → Int
isuc (int a b) = int (suc a) b

-- given i, return i - 1.
ipred : Int → Int
ipred (int a b) = int a (suc b)

-- given i, return -i.
ineg : Int → Int
ineg (int a b) = int b a

-- given i & j, return i + j.
iplus : Int → Int → Int
iplus (int zero zero) x = x
iplus (int (suc a) zero) x = isuc (iplus (int a zero) x)
iplus (int a (suc b)) x = ipred (iplus (int a b) x)


-- given i & j, return i - j.
iminus : Int → Int → Int
iminus (int zero zero) x = ineg (x)
iminus (int (suc a) zero) x = isuc (iminus (int a zero) x)
iminus (int a (suc b)) x = ipred (iminus (int a b) x)

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (int zero zero) x = int zero zero
itimes (int (suc a) zero) x = iplus x (itimes (int a zero) x)
itimes (int a (suc b)) x = ineg (iminus x (itimes (int a b) x))

