
import Crypto.EllipticCurve
import Crypto.Field.Fp
import Crypto.SSS
import Mathlib.Control.Random

open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.TSS


abbrev field (g : EllipticCurve.Group ec) : Type := Fp g.n

def share (g : EllipticCurve.Group ec) [Monad m] [RandomGen g'] (secret : field g) (threshold : Nat) (parties : Nat) : RandGT g' m (List (SSS.Share (field g))) :=
  SSS.share secret threshold parties

def aggregate [OfNat G 0] [Add G] [HMul Nat G G] (xs : List (Fp p)) (vals : List G) : G :=
  SSS.interpolate ((SSS.coefficients xs).map Fp.val) vals


end Crypto.TSS
