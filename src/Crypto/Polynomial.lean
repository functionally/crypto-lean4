import Mathlib.Control.Random

namespace Crypto


structure Polynomial (n : Nat) (F : Type) where
  private mk ::
  f : F → F

def randomPolynomial [RandomGen g] [Monad m] [Random m F] [Add F] [Mul F] (a₀ : F) (t : Nat) : RandGT g m (Polynomial t F) :=
  match t with
  | Nat.zero => pure $ Polynomial.mk (fun _ => a₀)
  | Nat.succ t' => do
                     let a₁ ← Random.random
                     let p ← randomPolynomial a₁ t'
                     let g x := a₀ + x * p.f x
                     pure $ Polynomial.mk g


end Crypto
