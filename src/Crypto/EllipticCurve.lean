namespace Crypto


structure EllipticCurve (F : Type) where
  a : F
  b : F
deriving Repr, DecidableEq, BEq


namespace EllipticCurve

  variable {F : Type}


  def wellFormed [∀ i, OfNat F i] [Add F] [Mul F] [Pow F Nat] (ec : EllipticCurve F) : Prop :=
    ¬ 4 * ec.a^3 + 27 * ec.b^2 = 0

  def wellFormed' [∀ i, OfNat F i] [BEq F] [Add F] [Mul F] [Pow F Nat] (ec : EllipticCurve F) : Bool :=
    4 * ec.a^3 + 27 * ec.b^2 != 0


  inductive Point (ec : EllipticCurve F) where
  | mk : F → F → Point ec
  | infinity : Point ec
  deriving Repr, DecidableEq, BEq

  instance : OfNat (Point ec) 0 where
    ofNat := Point.infinity

  namespace Point

    def onCurve [DecidableEq F] [Add F] [Mul F] [Pow F Nat] : Point (ec : EllipticCurve F) → Prop
    | Point.infinity => True
    | Point.mk x y => y^2 = x^3 + ec.a * x + ec.b

    def onCurve' [DecidableEq F] [Add F] [Mul F] [Pow F Nat] : Point (ec : EllipticCurve F) → Bool
    | Point.infinity => true
    | Point.mk x y => y^2 == x^3 + ec.a * x + ec.b

  end Point

  -- https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
  instance {ec : EllipticCurve F} [∀ i, OfNat F i] [BEq F] [Add F] [Sub F] [Mul F] [Div F] [Pow F Nat] [DecidableEq F] : Add (Point ec) where
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

  instance {ec : EllipticCurve F} [Neg F] : Neg (Point ec) where
    neg
    | Point.infinity => Point.infinity
    | Point.mk x y => Point.mk x (- y)

  instance {ec : EllipticCurve F} [Add (Point ec)] [Neg (Point ec)] : Sub (Point ec) where
    sub x y := x + (- y)

  def mulPoint {ec : EllipticCurve F} [Add (Point ec)] (n : Nat) (x : Point ec) : Point ec :=
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

  instance {ec : EllipticCurve F} [Add (Point ec)] : HMul Nat (Point ec) (Point ec) where
    hMul := mulPoint


  structure Group (ec : EllipticCurve F) where
    G : EllipticCurve.Point ec
    n : Nat
    h : Nat
  deriving Repr, DecidableEq, BEq

  namespace Group

    variable {ec : EllipticCurve F}

    def mkGroup (x : F) (y : F) (n : Nat) (h : Nat) : Group ec :=
      {
        G := EllipticCurve.Point.mk x y
      , n := n
      , h := h
      }

    structure KeyPair (g : EllipticCurve.Group ec) where
      prv : Nat
      pub : EllipticCurve.Point ec
    deriving Repr, DecidableEq, BEq

    variable {g : EllipticCurve.Group ec}

    def keyPair [HMul Nat (Point ec) (Point ec)] (prv : Nat) : KeyPair g :=
      KeyPair.mk prv (prv * g.G)

  end Group


end EllipticCurve


end Crypto
