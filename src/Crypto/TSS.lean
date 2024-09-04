
import Crypto.EllipticCurve
import Crypto.Field.Fp
import Crypto.SSS
import Mathlib.Control.Random

open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.TSS


abbrev field (g : EllipticCurve.Group ec) : Type := Fp g.n

def share [Monad m] [RandomGen g'] {parties : Nat} (g : EllipticCurve.Group ec) (secret : field g) (threshold : Nat) : RandGT g' m (SSS.PrivShares (field g) parties) :=
  SSS.share secret threshold

def aggregate [OfNat G 0] [Add G] [HMul Nat G G] (shares : SSS.Shares (Fp p) G) : G :=
  let coefs := shares.coefficients.xys.map $ Fp.val ∘ SSS.Share.y
  let vals := shares.xys.map SSS.Share.y
  SSS.interpolate coefs vals

-- TODO: Add functions for merging shares.

-- TODO: Add functions for signing and verifying.


end Crypto.TSS
