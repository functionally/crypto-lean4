
import Crypto.EllipticCurve
import Crypto.Field.Fp
import Crypto.SSS
import Mathlib.Control.Random

open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.TSS


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}
variable {G : Type}

[OfNat G 0]
[Add G]
[HMul (Fp p) G G]

abbrev field (g : EllipticCurve.Group ec) : Type := Fp g.n

def share [Monad m] [RandomGen gen] {parties : Nat} (g : EllipticCurve.Group ec) (secret : field g) (threshold : Nat) : RandGT gen m (SSS.PrivShares (field g) parties) :=
  SSS.share secret threshold

def assemble (shares : SSS.Shares (Fp p) G) : G :=
  let coefs := shares.coefficients.xys.map SSS.Share.y
  let vals := shares.xys.map SSS.Share.y
  SSS.interpolate coefs vals

-- TODO: Add functions for merging shares.

-- TODO: Add functions for signing and verifying.


end Crypto.TSS
