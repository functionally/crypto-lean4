
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


def publicShares (shares : List (Share F)) : List F :=
  shares.map Share.x

def sharePolynomial [∀ i, OfNat F i] [Add F] [Mul F] (parties : Nat) (poly : Polynomial threshold F) : List (Share F) :=
  let sample i :=
    let j := OfNat.ofNat i + OfNat.ofNat 1
    Share.mk j (poly.f j)
  (List.range parties).map sample

def share [Monad m] [RandomGen g] [Random m F] [∀ i, OfNat F i] [Add F] [Mul F] (secret : F) (threshold : Nat) (parties : Nat) : RandGT g m (List (Share F)) :=
  sharePolynomial parties <$> randomPolynomial secret (threshold - 1)

def coefficients [BEq F] [Add F] [Sub F] [Mul F] [Div F] [∀ i, OfNat F i] (xs : List F) : List F :=
  let term (x : F) : F :=
    let oth := xs.filter (fun x' => x' != x)
    let num := List.foldl Mul.mul 1 oth
    let den := List.foldl Mul.mul 1 $ oth.map (fun x' => x' - x)
    num / den
  xs.map term

def interpolate [OfNat G 0] [Add G] [HMul F G G] (lagranges : List F) (vals : List G) : G :=
  (List.zipWith HMul.hMul lagranges vals).foldl Add.add 0

def reconstruct [OfNat G 0] [BEq F] [Add F] [Mul F] [Sub F] [Add G] [HMul F G G] [Div F] [∀ i, OfNat F i] (xs : List F) (vals : List G) : G :=
  interpolate (coefficients xs) vals

def recover [BEq F] [Add F] [Sub F] [Mul F] [Div F] [∀ i, OfNat F i] (shares : List (Share F)) : F :=
  reconstruct (shares.map Share.x) (shares.map Share.y)


end Crypto.SSS
