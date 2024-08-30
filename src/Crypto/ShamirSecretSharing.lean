
import Mathlib.Control.Random
import Mathlib.Data.Vector


namespace Crypto.ShamirSecretSharing


private def randVector [Monad m] {a : Type} [Random m a] [RandomGen g] : RandGT g m (Vector a n) :=
  match n with
  | Nat.zero => pure Vector.nil
  | Nat.succ _ => Vector.cons <$> Random.random <*> randVector

instance {a : Type} [Random m a] [Monad m] : Random m (Vector a n) where
  random := randVector


def randomPolynomial [RandomGen g] [Monad m] [Random m F] [Add F] [Mul F] (a₀ : F) (t : Nat) : RandGT g m (F → F) :=
  match t with
  | Nat.zero => pure (fun _ => a₀)
  | Nat.succ t' => do
                     let a₁ ← Random.random
                     let f ← randomPolynomial a₁ t'
                     let g x := a₀ + x * f x
                     pure g


structure Share (F : Type) where
  x : F
  y : F
deriving Repr, DecidableEq, BEq


def share [Monad m] [RandomGen g] [Random m F] [∀ i, OfNat F i] [Add F] [Mul F] (secret : F) (trust : Nat) (parties : Nat) : RandGT g m (List (Share F)) :=
  do
    let f ← randomPolynomial secret (trust - 1)
    let sample i :=
      let j := OfNat.ofNat i + OfNat.ofNat 1
      Share.mk j (f j)
    pure $ (List.range parties).map sample


def recover [BEq F] [Add F] [Sub F] [Mul F] [Div F] [∀ i, OfNat F i] (shares : List (Share F)) : F :=
  let xs := shares.map Share.x
  let term (x y : F) : F :=
    let oth := xs.filter (fun x' => x' != x)
    let num := y * List.foldl Mul.mul 1 oth
    let den := List.foldl Mul.mul 1 $ oth.map (fun x' => x' - x)
    num / den
  List.foldl (fun acc share => acc + term share.x share.y) 0 shares


end Crypto.ShamirSecretSharing
