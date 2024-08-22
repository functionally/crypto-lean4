import Crypto.Field.Fp
import LSpec

open Crypto.Field
open LSpec

namespace Crypto.Field.Fp.Test


def F (p : Nat) : Nat → Fp p := Fp.mk


#lspec check "mk"
  $ ∀ p x  : Nat,
    p = 0 ∨ F p x = F p (x + p)

#lspec check "val"
  $ ∀ p x : Nat,
    (F p x).val = x % p

#lspec check "add"
  $ ∀ p x y : Nat,
    (F p x + F p y).val = (x + y) % p

#lspec check "sub"
  $ ∀ p x y : Nat,
    p = 0 ∨ Int.ofNat (F p x - F p y).val = (Int.ofNat x - Int.ofNat y) % Int.ofNat p

#lspec check "mul"
  $ ∀ p x y : Nat,
    (F p x * F p y).val = x * y % p

#lspec check "pow"
  $ ∀ p x n : Nat,
    (F p x ^ n).val = x ^ n % p

#lspec group "inverse"
  $ check "left" (
      ∀ p y : Nat,
      Nat.gcd p y ≠  1 ∨ Div.div 1 (F p y) * F p y = 1
    )
  $ check "right" (
      ∀ p y : Nat,
      Nat.gcd p y ≠  1 ∨ F p y * Div.div 1 (F p y) = 1
    )

#lspec check "div"
  $ ∀ p x y : Nat,
    Nat.gcd p y ≠  1 ∨ (Div.div (F p x) (F p y)) * F p y = F p x

#lspec check "div by zero"
  $ ∀ p x : Nat,
    p = 0 ∨ (Div.div (F p x) (F p 0)) = 0


end Crypto.Field.Fp.Test
