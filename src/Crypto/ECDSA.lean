import Crypto.Field.Fp
import Crypto.EllipticCurve
import Crypto.Hash

open Crypto
open Crypto.Field
open Crypto.EllipticCurve


namespace Crypto.ECDSA

variable {F : Type}
variable {ec : EllipticCurve F}

def sign : Nat → ByteArray → EllipticCurve.Point ec :=
  sorry
#check sign

def verify : EllipticCurve.Point ec → ByteArray → EllipticCurve.Point ec → Bool :=
  sorry
#check verify


end Crypto.ECDSA
