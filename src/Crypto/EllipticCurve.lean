namespace Crypto


structure EllipticCurve (F : Type) where
  a : F
  b : F
deriving Repr, BEq

namespace EllipticCurve


  def wellFormed [OfNat F 0] [OfNat F 4] [OfNat F 27] [Add F] [Mul F] [Pow F Nat] (ec : EllipticCurve F) : Prop :=
    ¬ 4 * ec.a^3 + 27 * ec.b^2 = 0


  structure Point (F : Type) (ec : EllipticCurve F) where
    x : F
    y : F
  deriving Repr, BEq

  instance [OfNat F 2] [OfNat F 3] [BEq F] [Add F] [Sub F] [Mul F] [Div F] [Pow F Nat] : Add (Point F ec) where
    add p q :=
      let m :=
        if p == q
          then (3 * p.x^2 + ec.a) / (2 * p.y)
          else (p.y - q.y) / (p.x - q.x)
      let x := m^2 - p.x - q.x
      let y := p.y + m * (x - p.x)
      ⟨ x, y ⟩


end EllipticCurve


end Crypto
