import Crypto.EllipticCurve
import Crypto.EllipticCurve.Schnorr
import Crypto.EllipticCurve.SECG.Secp256k1
import Crypto.Field.Fp
import Crypto.Polynomial.SSS
import Crypto.Hash.SHA2
import Mathlib.Control.Random
import LSpec

open Crypto.EllipticCurve
open Crypto.Polynomial
open Crypto.EllipticCurve.Schnorr
open Crypto.Field
open LSpec


namespace Crypto.EllipticCurve.Schnorr.Test


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


instance : Repr (ByteArray) where
  reprPrec
  | ⟨ x ⟩ , n => Repr.reprPrec x n

def h : ByteArray → Nat := Hash.SHA2.sha256


namespace Signature

  structure TestCase (g : Group ec) where
    key : Group.KeyPair g
    message : ByteArray
    signature : Signature g
  deriving Repr

  instance : SlimCheck.Shrinkable (TestCase g) where
    shrink _ := []

  instance {g : Group ec} : SlimCheck.SampleableExt (TestCase g) :=
    SlimCheck.SampleableExt.mkSelfContained $
      do
        let key ← (Random.random : Rand (Group.KeyPair g))
        let message' ← (Random.random : Rand (Fp g.n))
        let message := Serial.natToBytes message'.val
        let sig ← (sign h key message : Rand (Signature g))
        pure ⟨ key , message , sig ⟩

  #lspec check "verify ∘ sign" (∀ tc : TestCase Secp256k1, verify h tc.key.pubKey tc.message tc.signature)

end Signature


namespace Protocol

  structure TestCase (g : Group ec) where
    commitment : Group.PubKey g
    chal : Fp g.n
    response : Response g
  deriving Repr

  instance : SlimCheck.Shrinkable (TestCase g) where
    shrink _ := []

  instance {g : Group ec} : SlimCheck.SampleableExt (TestCase g) :=
    SlimCheck.SampleableExt.mkSelfContained $
      do
        let rnd ← (commit : Rand (Group.KeyPair g))
        let secret := rnd.prv
        let commitment := rnd.pubKey
        let chal ← (Random.random : Rand (Fp g.n))
        let response := challenge rnd secret chal
        pure ⟨ commitment , chal , response ⟩

  #lspec check "confirm ∘ challenge ∘ commit" (∀ tc : TestCase Secp256k1, confirm tc.commitment tc.chal tc.response)

end Protocol


namespace Multsig

  structure TestCase (g : Group ec) where
    keys : List (Group.KeyPair g)
    nonces : List (Group.KeyPair g)
    message : ByteArray
    pub : Group.PubKey g
    signature : Option (Signature g)
  deriving Repr

  instance : SlimCheck.Shrinkable (TestCase g) where
    shrink _ := []

  instance {g : Group ec} : SlimCheck.SampleableExt (TestCase g) :=
    SlimCheck.SampleableExt.mkSelfContained $
      do
        let n ← SlimCheck.Gen.choose Nat 2 5
        let keys ←
          (
            Monad.sequence $ List.replicate n Random.random
            : Rand (List (Group.KeyPair g))
          )
        let pub := combinePubKeys $ keys.map Group.KeyPair.pubKey
        let nonces ←
          (
            Monad.sequence $ List.replicate n Random.random
            : Rand (List (Group.KeyPair g))
          )
        let nonce := combinePubKeys $ nonces.map Group.KeyPair.pubKey
        let message' ← (Random.random : Rand (Fp g.n))
        let message := Serial.natToBytes message'.val
        let sigs :=
          List.zipWith
            (fun k n => partialsign h k n.prv nonce.pub message)
            keys
            nonces
        let sig := multisig sigs
        pure ⟨ keys , nonces , message , pub , sig ⟩

  #lspec check "multisig" (∀ tc : TestCase Secp256k1, (verify h tc.pub tc.message <$> tc.signature) = some true)

end Multsig


namespace Thresholdsig

  def sublist (n : Nat) (xs : List t) : SlimCheck.Gen (List t) :=
    List.drop (xs.length - n) <$> SlimCheck.Gen.permutationOf xs

  structure TestCase (g : Group ec) where
    secret : Fp g.n
    parties : Nat
    threshold : Nat
    shares : SSS.Shares (Fp g.n) (Fp g.n)
    pub : Group.PubKey g
    message : ByteArray
    signature : Option (Signature g)
  deriving Repr

  instance : SlimCheck.Shrinkable (TestCase g) where
    shrink _ := []

  instance {g : Group ec} : SlimCheck.SampleableExt (TestCase g) :=
    SlimCheck.SampleableExt.mkSelfContained
      $ do
        let secret ← (Fp.randFp : Rand (Fp g.n))
        let parties ← SlimCheck.Gen.choose Nat 1 10
        let threshold ← SlimCheck.Gen.choose Nat 1 parties
        let shares ← (SSS.share secret threshold : Rand (SSS.PrivShares (Fp g.n) parties))
        let parties' ← SlimCheck.Gen.choose Nat threshold parties
        let shares' ← SSS.Shares.mk <$> sublist parties' shares.toShares.xys
        let pub := Group.PubKey.mk ∘ SSS.assemble $ Functor.map (fun prv => prv * g.G) shares'
        let nonces ← (Monad.sequence $ List.replicate parties' Random.random : Rand (List (Group.KeyPair g)))
        let nonce : EllipticCurve.Point ec :=
          SSS.assemble
            $ SSS.Shares.mk
            $ List.zipWith
              SSS.Share.mk
              (shares'.xys.map SSS.Share.x)
              (nonces.map Group.KeyPair.pub)
        let message' ← (Random.random : Rand (Fp g.n))
        let message := Serial.natToBytes message'.val
        let sigs :=
          List.zipWith
            (fun k n => partialsign h k n.prv nonce message)
            (shares'.xys.map (fun s => Group.keyPair s.y.val))
            nonces
        let sig :=
          thresholdsig
            $ SSS.Shares.mk
            $ List.zipWith SSS.Share.mk (shares'.xys.map SSS.Share.x) sigs
        pure $ TestCase.mk secret parties threshold shares' pub message sig

  #lspec check "thresholdsig" (∀ tc : TestCase Secp256k1, (verify h tc.pub tc.message <$> tc.signature) = some true)

end Thresholdsig


end Crypto.EllipticCurve.Schnorr.Test
