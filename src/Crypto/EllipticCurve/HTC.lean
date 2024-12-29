import Crypto.EllipticCurve
import Crypto.Field

open Crypto.Field


namespace Crypto.EllipticCurve.HTC


variable {ec : EllipticCurve F}

[∀ i, OfNat F i]
[DecidableEq F]
[Add F]
[Mul F]
[Pow F Nat]
[Sqrt F]


namespace MapToCurve

  partial def tryAndIncrement (x : F) : Point ec :=
    let y2 : F := residue ec x
    let y : F := Sqrt.sqrt y2
    if y^2 = y2
      then Point.mk x y
      else tryAndIncrement (x + 1)

end MapToCurve


end Crypto.EllipticCurve.HTC
