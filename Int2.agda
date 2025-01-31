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
ipred (+ n) =  - n
ipred (- zero) = - (suc zero)
ipred (- n) = - (suc n)

-- given i, return -i.
ineg : Int → Int
ineg (+ n) = zero (- n)
ineg (- zero) = (suc(- zero))
ineg (- n) = - (n)

-- given i & j, return i + j.
iplus : Int → Int → Int
iplus (- zero) n = n
iplus (+ zero) n = n
iplus (- n) (- m) = - (n + m)
iplus (- n) (m) = m (- (n))
iplus (n) (- m) = n (- m)
iplus (n) (m) = n (+ m)

-- given i & j, return i - j.
iminus : Int → Int → Int
iminus (- zero) n = - n
iminus (+ zero) n = - n
iminus (- n) (- m) = - n (+ m)
iminus (- n) m = - (n + m)
iminus n (- m) = n + m
iminus n m = n - m

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (- zero) n = zero
itimes (+ zero) n = zero
itimes (- n) (- m) = n (times m)
itimes (- n) m = - (n (times m))
itimes n (- m) = - (n (times m))
itimes n m = n (times m)


