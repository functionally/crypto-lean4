import Crypto.EllipticCurve

open Crypto
open Crypto.EllipticCurve


namespace Crypto.ECDH


variable {F : Type}
variable {ec : EllipticCurve F}


def sharedSecret  [HMul F (Point ec) (Point ec)] (prv : F) (pub : Point ec) : Point ec :=
  prv * pub


end Crypto.ECDH
