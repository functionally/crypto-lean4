
import LSpec

import Crypto.EllipticCurve.Secp256k1
import Crypto.SSS
import Crypto.TSS
import Mathlib.Control.Random

open Crypto.EllipticCurve
open Crypto.TSS
open LSpec


namespace Crypto.TSS.Test


private def g := Secp256k1


private def randSeedIO (g : EllipticCurve.Group ec) : BaseIO (field g) :=
  IO.runRand $ Random.random

private def seed : field g := 51438802849734075488955803770868331647095276798316212438271497709937095496092

private def kp : Group.KeyPair g := Group.keyPair seed.val

private def parties : Nat := 3
private def threshold : Nat := 2

private def rpoly : BaseIO (List (SSS.Share (field g))) := IO.runRand $ share g seed threshold parties

private def share1 : SSS.Share (field g) := SSS.Share.mk 1 64629393137957246869056654757565593965123883613554000791282733172384117873221
private def share2 : SSS.Share (field g) := SSS.Share.mk 2 77819983426180418249157505744262856283152490428791789144293968634831140250350
private def share3 : SSS.Share (field g) := SSS.Share.mk 3 91010573714403589629258356730960118601181097244029577497305204097278162627479
private def shares : List (SSS.Share (field g)) := [share1, share2, share3]

private def cs : List (field g) := SSS.coefficients $ SSS.publicShares shares

private def pks := shares.map (fun s => s.y.val * g.G)

#lspec group "reconstruction"
  $ test "private key" (SSS.recover shares == seed)
  $ test "public key" (reconstruct (SSS.publicShares shares) pks == kp.pub)


end Crypto.TSS.Test
