import Crypto.EllipticCurve
import Crypto.EllipticCurve.ECDSA
import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp
import Crypto.SSS
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.TSS


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


abbrev field (g : EllipticCurve.Group ec) : Type := Fp g.n


def share [Monad m] [RandomGen gen] {parties : Nat} (g : EllipticCurve.Group ec) (secret : field g) (threshold : Nat) : RandGT gen m (SSS.PrivShares (field g) parties) :=
  SSS.share secret threshold

def assemble [OfNat G 0] [Add G] [HMul (Fp q) G G] (shares : SSS.Shares (Fp q) G) : G :=
  let coefs := shares.coefficients.xys.map SSS.Share.y
  let vals := shares.xys.map SSS.Share.y
  SSS.interpolate coefs vals


-- TODO: Add functions for merging shares.


variable {g : EllipticCurve.Group ec}


def localNonce [RandomGen gen] [Monad m] : RandGT gen m (field g) :=
  Random.random

def localPoint (xy : SSS.PrivShare (Fp p)) (k : field g): SSS.Share (Fp p) (Point ec) :=
  SSS.Share.mk xy.x $ k.val * g.G

def sharedPoint : SSS.Shares (Fp p) (Point ec) → Point ec :=
  List.foldl Add.add 0 ∘ List.map SSS.Share.y ∘ SSS.Shares.xys

def sign (xy : SSS.PrivShare (Fp p)) (k : field g) (R : Point ec) (z : Fp g.n) : SSS.Share (field g) (ECDSA.Signature g) :=
  let kp : Group.KeyPair g := Group.keyPair xy.y.val
  SSS.Share.mk xy.x.castFp $ ECDSA.rawSign kp z k R

def verify (pk : EllipticCurve.Group.PubKey g) (sigs : SSS.Shares (field g) (ECDSA.Signature g)) (z : Fp g.n) : Bool :=
  let point := List.foldl Add.add 0 ∘ List.map (ECDSA.Signature.point ∘ SSS.Share.y) $ SSS.Shares.xys sigs
  let proof := assemble $ Functor.map (fun y => y.proof) sigs
  ECDSA.verify pk z ⟨ point , proof ⟩


end Crypto.TSS
