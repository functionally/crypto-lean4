import Crypto.Field.Fp
import Mathlib.Control.Random

open Crypto.Field


namespace Crypto


structure EllipticCurve (F : Type) where
  a : F
  b : F
deriving Repr, DecidableEq, BEq


namespace EllipticCurve

  variable {F : Type}

  [∀ i, OfNat F i]
  [DecidableEq F]
  [BEq F]
  [Add F]
  [Sub F]
  [Neg F]
  [Mul F]
  [Div F]
  [Pow F Nat]

  def wellFormed (ec : EllipticCurve F) : Prop :=
    ¬ 4 * ec.a^3 + 27 * ec.b^2 = 0

  def wellFormed' (ec : EllipticCurve F) : Bool :=
    4 * ec.a^3 + 27 * ec.b^2 != 0


  inductive Point (ec : EllipticCurve F) where
  | mk : F → F → Point ec
  | infinity : Point ec
  deriving Repr, DecidableEq, BEq

  instance : OfNat (Point ec) 0 where
    ofNat := Point.infinity

  namespace Point

    def x {ec : EllipticCurve F} : Point ec → F
    | Point.mk x' _ => x'
    | Point.infinity => 0

    def y {ec : EllipticCurve F} : Point ec → F
    | Point.mk _ y' => y'
    | Point.infinity => 0

    def onCurve : Point (ec : EllipticCurve F) → Prop
    | Point.infinity => True
    | Point.mk x y => y^2 = x^3 + ec.a * x + ec.b

    def onCurve' : Point (ec : EllipticCurve F) → Bool
    | Point.infinity => true
    | Point.mk x y => y^2 == x^3 + ec.a * x + ec.b

  end Point

  -- https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
  instance {ec : EllipticCurve F} : Add (Point ec) where
    add
    | p, Point.infinity => p
    | Point.infinity, q => q
    | Point.mk px py, Point.mk qx qy =>
        let mkPoint (m : F) : Point ec :=
              let rx := m^2 - px - qx
              let ry := m * (px - rx) - py
              Point.mk rx ry
        if px = qx ∧ py = qy
          then if px = 0
                 then Point.infinity
                 else mkPoint $ (3 * px^2 + ec.a) / (2 * py)
          else if px = qx
                 then Point.infinity
                 else mkPoint $ (qy - py) / (qx - px)

  instance {ec : EllipticCurve F} : Neg (Point ec) where
    neg
    | Point.infinity => Point.infinity
    | Point.mk x y => Point.mk x (- y)

  instance {ec : EllipticCurve F} : Sub (Point ec) where
    sub x y := x + (- y)

  def mulPoint {ec : EllipticCurve F} (n : Nat) (x : Point ec) : Point ec :=
    if n = 0
      then Point.infinity
      else if n = 1
        then x
        else let y := mulPoint (n / 2) (x + x)
             if n % 2 = 1
               then y + x
               else y
  termination_by n
  decreasing_by
    simp_wf
    apply Nat.div_lt_self
    apply Nat.zero_lt_of_ne_zero
    assumption
    apply Nat.one_lt_two

  instance {ec : EllipticCurve F} : HMul Nat (Point ec) (Point ec) where
    hMul := mulPoint

  instance {p : Nat} {q : Nat} {ec : EllipticCurve (Fp p)} [Add (Point ec)] : HMul (Fp q) (Point ec) (Point ec) where
    hMul := mulPoint ∘ Fp.val


  structure Group (ec : EllipticCurve F) where
    G : EllipticCurve.Point ec
    n : Nat
    h : Nat
  deriving Repr, DecidableEq, BEq

  namespace Group

    variable {ec : EllipticCurve F}

    abbrev point (_ : EllipticCurve.Group ec) : Type := EllipticCurve.Point ec

    def mkGroup (x : F) (y : F) (n : Nat) (h : Nat) : Group ec :=
      {
        G := EllipticCurve.Point.mk x y
      , n := n
      , h := h
      }

    structure KeyPair (g : EllipticCurve.Group ec) where
      prv : Fp g.n
      pub : EllipticCurve.Point ec
    deriving Repr, DecidableEq, BEq

    variable {g : EllipticCurve.Group ec}

    def keyPair (prv : Nat) : KeyPair g :=
      KeyPair.mk (OfNat.ofNat prv) (prv * g.G)

    def randKeyPair [RandomGen gen] [Monad m] : RandGT gen m (KeyPair g) :=
      do
        let prv ← Random.random
        pure $ KeyPair.mk prv (prv.val * g.G)

    instance [Monad m] [Random m (Fp g.n)] : Random m (KeyPair g) where
      random := randKeyPair

    structure PubKey (g : EllipticCurve.Group ec) where
      pub : EllipticCurve.Point ec
    deriving Repr, DecidableEq, BEq

    namespace KeyPair

      def pubKey : KeyPair (g : EllipticCurve.Group ec) → PubKey g :=
        PubKey.mk ∘ KeyPair.pub

    end KeyPair

  end Group


end EllipticCurve


end Crypto
