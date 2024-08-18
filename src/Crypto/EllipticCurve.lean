namespace Crypto


structure EllipticCurve (F : Type) where
  a : F
  b : F
deriving Repr, BEq


namespace EllipticCurve


  def wellFormed [OfNat F 0] [OfNat F 4] [OfNat F 27] [Add F] [Mul F] [Pow F Nat] (ec : EllipticCurve F) : Prop :=
    ¬ 4 * ec.a^3 + 27 * ec.b^2 = 0

  def wellFormed' [BEq F] [OfNat F 0] [OfNat F 4] [OfNat F 27] [Add F] [Mul F] [Pow F Nat] (ec : EllipticCurve F) : Bool :=
    4 * ec.a^3 + 27 * ec.b^2 != 0

  inductive Point (F : Type) (ec : EllipticCurve F) where
  | mk : F → F → Point F ec
  | infinity : Point F ec
  deriving Repr, DecidableEq, BEq

  namespace Point

    def onCurve [DecidableEq F] [Add F] [Mul F] [Pow F Nat] : Point (F : Type) (ec : EllipticCurve F) → Prop
    | Point.infinity => True
    | Point.mk x y => y^2 = x^3 + ec.a * x + ec.b

    def onCurve' [DecidableEq F] [Add F] [Mul F] [Pow F Nat] : Point (F : Type) (ec : EllipticCurve F) → Bool
    | Point.infinity => true
    | Point.mk x y => y^2 == x^3 + ec.a * x + ec.b

  end Point

  -- https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
  instance [OfNat F 0] [OfNat F 2] [OfNat F 3] [BEq F] [Add F] [Sub F] [Mul F] [Div F] [Pow F Nat] [DecidableEq F] : Add (Point F ec) where
    add
    | p, Point.infinity => p
    | Point.infinity, q => q
    | Point.mk px py, Point.mk qx qy =>
        let mkPoint (m : F) : Point F ec :=
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

  instance [Neg F] : Neg (Point F ec) where
    neg
    | Point.infinity => Point.infinity
    | Point.mk x y => Point.mk x (- y)

  instance [Add (Point F ec)] [Neg (Point F ec)] : Sub (Point F ec) where
    sub x y := x + (- y)

  def mulPoint [Add (Point F ec)] (n : Nat) (x : Point F ec) : Point F ec :=
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

  instance [Add (Point F ec)]: HMul Nat (Point F ec) (Point F ec) where
    hMul := mulPoint


end EllipticCurve


end Crypto
