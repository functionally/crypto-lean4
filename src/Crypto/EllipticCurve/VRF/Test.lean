import Crypto.EllipticCurve.HTC
import Crypto.EllipticCurve.SECG.Secp256k1
import Crypto.EllipticCurve.VRF
import Crypto.Field.Fp
import Crypto.Hash
import Crypto.Serial
import LSpec

open Crypto.EllipticCurve
open Crypto.Field
open Crypto.CHash
open LSpec


namespace Crypto.EllipticCurve.VRF.Test

abbrev p := Secp256k1.p
abbrev F := Secp256k1.F
theorem hasSqrt : Fp.Is3Mod4 p := rfl
instance iSqrt : Sqrt F := Fp.instSqrt3Mod4 hasSqrt
def g := Secp256k1
def ec := Secp256k1.curve

def pointToBytes : Point ec → ByteArray := Serial.natToBytes ∘ Fp.val ∘ Point.x

def htc (X : Point ec) (m : Nat) : Point ec :=
  let bs : ByteArray := (pointToBytes X).append (Serial.natToBytes m)
  let bh : ByteArray := (Algorithm.SHA2_256.chash bs).data
  let i := Serial.bytesToNat bh
  let i' : F := Fp.mk i
  HTC.MapToCurve.tryAndIncrement i'

def commit (H Z RB RH : Point ec) : Fp Secp256k1.n :=
  let bs : ByteArray :=
    [H, Z, RB, RH].foldl
      (fun acc x => acc.append $ pointToBytes x)
      ByteArray.empty
  let bh : ByteArray := (Algorithm.SHA2_256.chash bs).data
  let i := Serial.bytesToNat bh
  Fp.mk i

structure TestCase where
  message : Nat
  pk : Group.PubKey g
  proof : Proof g
deriving Repr

instance : SlimCheck.Shrinkable TestCase where
  shrink _ := []

instance : SlimCheck.SampleableExt TestCase :=
  SlimCheck.SampleableExt.mkSelfContained
    $ do
      let kp ← (Random.random : Rand (Group.KeyPair g))
      let m ← (Random.randBound Nat 0 1000000 ((Nat.zero_le 1000000)) : Rand Nat)
      let proof ← (VRF.prove htc commit kp m : Rand (Proof g))
      pure $ ⟨ m , kp.pubKey, proof ⟩

#lspec check "ECVRF" (∀ tc : TestCase, verify htc commit tc.pk tc.message tc.proof)


end Crypto.EllipticCurve.VRF.Test
