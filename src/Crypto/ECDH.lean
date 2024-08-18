import Crypto.EllipticCurve

open Crypto
open Crypto.EllipticCurve


namespace Crypto.ECDH


variable {F : Type}
variable {ec : EllipticCurve F}


def sharedSecret  [HMul Nat (Point ec) (Point ec)] (prv : Nat) (pub : Point ec) : Point ec :=
  prv * pub


end Crypto.ECDH
