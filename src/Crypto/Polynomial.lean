import Mathlib.Control.Random

namespace Crypto


structure Polynomial (n : Nat) (F : Type) where
  private mk ::
  aᵢ : List F
deriving Repr, DecidableEq, BEq

instance [Monad m] [Random m F] : Random m (Polynomial n F) where
  random := Polynomial.mk <$> Monad.sequence (List.replicate n Random.random)

def randomPolynomial [RandomGen g] [Monad m] [Random m F] (a₀ : F) : RandGT g m (Polynomial t F) :=
  match t with
  | 0 => pure $ Polynomial.mk [a₀]
  | Nat.succ n => do
                    let as ← Monad.sequence (List.replicate n Random.random)
                    pure ∘ Polynomial.mk $ List.cons a₀ as

namespace Polynomial

  variable {F : Type}

  [OfNat F 0]
  [Add F]
  [Mul F]

  private def eval (x : F) : List F → F
  | [] => 0
  | a :: as => a + x * eval x as

  def f (x : F) : Polynomial n F → F :=
    eval x ∘ Polynomial.aᵢ

end Polynomial


end Crypto
