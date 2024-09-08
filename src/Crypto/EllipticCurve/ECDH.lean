import Crypto.EllipticCurve

open Crypto
open Crypto.EllipticCurve


namespace Crypto.EllipticCurve.ECDH


variable {F : Type}
variable {ec : EllipticCurve F}

[HMul Nat (Point ec) (Point ec)]

def sharedSecret  (prv : Nat) (pub : Point ec) : Point ec :=
  prv * pub


end Crypto.EllipticCurve.ECDH
