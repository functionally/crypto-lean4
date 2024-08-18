import Crypto.Field.Fp
import Crypto.EllipticCurve

open Crypto
open Crypto.Field
open Crypto.EllipticCurve


namespace Crypto.ECDH


variable {F : Type}
variable {ec : EllipticCurve F}

structure KeyPair {ec : EllipticCurve F} (g : EllipticCurve.Group ec) where
  prv : Nat
  pub : EllipticCurve.Point ec
deriving Repr, DecidableEq, BEq

variable {g : EllipticCurve.Group ec}

def keyPair [HMul Nat (Point ec) (Point ec)] (prv : Nat) : KeyPair g :=
  KeyPair.mk prv (prv * g.G)

def SharedSecret  [HMul Nat (Point ec) (Point ec)] (prv : Nat) (pub : Point ec) : Point ec :=
  prv * pub


end Crypto.ECDH
