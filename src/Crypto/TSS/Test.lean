
import LSpec

import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp
import Crypto.SSS
import Crypto.TSS
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.Field
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

private def rpoly : BaseIO (SSS.PrivShares (field g) parties) := IO.runRand $ share g seed threshold

private def share1 : SSS.Share (field g) (field g) := SSS.Share.mk 1 64629393137957246869056654757565593965123883613554000791282733172384117873221
private def share2 : SSS.Share (field g) (field g) := SSS.Share.mk 2 77819983426180418249157505744262856283152490428791789144293968634831140250350
private def share3 : SSS.Share (field g) (field g) := SSS.Share.mk 3 91010573714403589629258356730960118601181097244029577497305204097278162627479
private def shares : SSS.Shares (field g) (field g) := SSS.Shares.mk [share1, share2, share3]

private def pks := Functor.map (fun y => y * g.G) shares

#lspec group "assemble"
  $ test "private key" (SSS.assemble shares == seed)
  $ test "public key" (assemble pks == kp.pub)

-- TODO: Automate test with generators.


end Crypto.TSS.Test
