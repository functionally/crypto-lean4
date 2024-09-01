
import Mathlib.Control.Random
import Mathlib.Data.Vector


namespace Crypto.SSS


private def randVector [Monad m] {a : Type} [Random m a] [RandomGen g] : RandGT g m (Vector a n) :=
  match n with
  | Nat.zero => pure Vector.nil
  | Nat.succ _ => Vector.cons <$> Random.random <*> randVector

instance {a : Type} [Random m a] [Monad m] : Random m (Vector a n) where
  random := randVector


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


structure Share (F : Type) where
  x : F
  y : F
deriving Repr, DecidableEq, BEq


def sharePolynomial [∀ i, OfNat F i] [Add F] [Mul F] (parties : Nat) (poly : Polynomial trust F) : List (Share F) :=
  let sample i :=
    let j := OfNat.ofNat i + OfNat.ofNat 1
    Share.mk j (poly.f j)
  (List.range parties).map sample

def share [Monad m] [RandomGen g] [Random m F] [∀ i, OfNat F i] [Add F] [Mul F] (secret : F) (trust : Nat) (parties : Nat) : RandGT g m (List (Share F)) :=
  sharePolynomial parties <$> randomPolynomial secret (trust - 1)

def coefficients [BEq F] [Add F] [Sub F] [Mul F] [Div F] [∀ i, OfNat F i] (shares : List (Share F)) : List F :=
  let xs := shares.map Share.x
  let term (x : F) : F :=
    let oth := xs.filter (fun x' => x' != x)
    let num := List.foldl Mul.mul 1 oth
    let den := List.foldl Mul.mul 1 $ oth.map (fun x' => x' - x)
    num / den
  shares.map $ term ∘ Share.x

def interpolate [OfNat F 0] [Add F] [Mul F] (lagranges : List F) (ys : List F) : F :=
  (List.zipWith Mul.mul lagranges ys).foldl Add.add 0

def recover [BEq F] [Add F] [Sub F] [Mul F] [Div F] [∀ i, OfNat F i] (shares : List (Share F)) : F :=
  interpolate (coefficients shares) (shares.map Share.y)


end Crypto.SSS
