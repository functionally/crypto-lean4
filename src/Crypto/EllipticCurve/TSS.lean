import Crypto.EllipticCurve
import Crypto.Field.Fp
import Crypto.Polynomial.SSS

open Crypto
open Crypto.EllipticCurve
open Crypto.Field
open Crypto.Polynomial


namespace Crypto.EllipticCurve.TSS


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


abbrev field (g : EllipticCurve.Group ec) : Type := Fp g.n


def share [Monad m] [RandomGen gen] {parties : Nat} (g : EllipticCurve.Group ec) (secret : field g) (threshold : Nat) : RandGT gen m (SSS.PrivShares (field g) parties) :=
  SSS.share secret threshold

def assemble [OfNat G 0] [Add G] [HMul (Fp q) G G] (shares : SSS.Shares (Fp q) G) : G :=
  let coefs := shares.coefficients.xys.map SSS.Share.y
  let vals := shares.xys.map SSS.Share.y
  SSS.interpolate coefs vals


-- TODO: Work in progress.


end Crypto.EllipticCurve.TSS
