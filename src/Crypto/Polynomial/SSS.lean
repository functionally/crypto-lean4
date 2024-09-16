import Crypto.Polynomial
import Mathlib.Control.Random
import Mathlib.Data.Vector


namespace Crypto.Polynomial.SSS


structure PrivShares (F : Type) (n : Nat) where
  ys : Vector F n

structure Share (F : Type) (G : Type) where
  x : F
  y : G
deriving Repr, DecidableEq, BEq

instance : Functor (Share F) where
  map f s := Share.mk s.x $ f s.y

abbrev PrivShare F := Share F F

-- TODO: Consider implementing this as a `HashMap`.
structure Shares (F : Type) (G : Type) where
  xys : List (Share F G)
deriving Repr, DecidableEq, BEq

instance : Functor (Shares F) where
  map f := Shares.mk ∘ List.map (Functor.map f) ∘ Shares.xys

instance : Bifunctor Shares where
  bimap f g := Shares.mk ∘ List.map (fun s => ⟨ f s.x , g s.y ⟩) ∘ Shares.xys

instance [BEq F] : Mul (Shares F G) where
  mul
  | ⟨ us ⟩ , ⟨ vs ⟩ => ⟨ List.append (us.filter ((vs.map Share.x).notElem ∘ Share.x)) vs ⟩

-- TODO: Consider making `Shares` an instance of `Monoid`.
-- TODO: Use `Add` for piecewise addition of `Shares`.

variable {F : Type}

[∀ i, OfNat F i]
[Inhabited F]
[BEq F]
[Add F]
[Sub F]
[Mul F]
[Div F]

namespace Shares

  def coefficients (pubs : Shares F G) : Shares F F :=
    let term (xy : Share F G) : Share F F:=
      let x := xy.x
      let oth := (pubs.xys.map Share.x).filter (fun x' => x' != x)
      let num := List.foldl Mul.mul 1 oth
      let den := List.foldl Mul.mul 1 $ oth.map (fun x' => x' - x)
      Share.mk x $ num / den
    Shares.mk $ pubs.xys.map term

  def count : Shares F G → Nat :=
    List.length ∘ Shares.xys

end Shares

namespace PrivShares

  def pubShares (_ : PrivShares F n) : Shares F Unit :=
    Shares.mk $ (List.range n).map (fun i => Share.mk (OfNat.ofNat $ Add.add 1 i) ())

  def toShares (privs : PrivShares F n) : Shares F F :=
    Shares.mk $ List.zipWith Share.mk ((List.range n).map (fun i => OfNat.ofNat $ Add.add 1 i)) privs.ys.toList

  def coefficients : PrivShares F n → Shares F F :=
    Shares.coefficients ∘ PrivShares.pubShares

  def confirm [HPow F Nat F] [Inhabited G] [BEq G] [HMul F G G] [Add G] (i : F) (s : G) (comms : List G) : Bool :=
    let s' :=
      List.foldl (fun acc xy => acc + (i ^ xy.fst) * (xy.snd : G)) Inhabited.default
        $ List.zip (List.range $ comms.length) comms
    s == s'

end PrivShares

namespace Polynomial

  def toShares [Inhabited F] {parties : Nat} (poly : Polynomial threshold F) : PrivShares F parties :=
    PrivShares.mk $ Vector.ofFn (fun i => poly.f $ OfNat.ofNat $ i.val + 1)

  def commitments [HMul F G G] (g : G) : Polynomial n F → List G :=
    List.map (flip HMul.hMul g) ∘ Polynomial.aᵢ

end Polynomial

def share [Monad m] [RandomGen gen] [Random m F] [Inhabited F] {parties : Nat} (secret : F) (threshold : Nat) : RandGT gen m (PrivShares F parties) :=
  Polynomial.toShares <$> (randomPolynomial secret : RandGT gen m (Polynomial (threshold - 1) F))

variable {G : Type}

[Inhabited G]
[Add G]
[HMul F G G]

def shareWithCommitments [Monad m] [RandomGen gen] [Random m F] {parties : Nat} (secret : F) (threshold : Nat) (g : G): RandGT gen m (PrivShares F parties × List G) :=
  do
    let poly : Polynomial (threshold - 1) F ← randomPolynomial secret
    pure $ ⟨ Polynomial.toShares poly , Polynomial.commitments g poly ⟩

def interpolate (lagranges : List F) (vals : List G) : G :=
  (List.zipWith HMul.hMul lagranges vals).foldl Add.add Inhabited.default

def assemble (shares : Shares F G) : G :=
  let coefs := shares.coefficients.xys.map Share.y
  let vals := shares.xys.map Share.y
  interpolate coefs vals


end Crypto.Polynomial.SSS
