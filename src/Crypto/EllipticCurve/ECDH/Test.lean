import Crypto.EllipticCurve
import Crypto.EllipticCurve.ECDH
import Crypto.EllipticCurve.SECG.Secp256k1
import LSpec

open Crypto.EllipticCurve.ECDH
open Crypto.EllipticCurve.Group
open LSpec


namespace Crypto.EllipticCurve.ECDH.Test


-- https://andrea.corbellini.name/2015/05/30/elliptic-curve-cryptography-ecdh-and-ecdsa/

def alice : KeyPair Secp256k1 := keyPair 0xe32868331fa8ef0138de0de85478346aec5e3912b6029ae71691c384237a3eeb
def bob : KeyPair Secp256k1 := keyPair 0xcef147652aa90162e1fff9cf07f2605ea05529ca215a04350a98ecc24aa34342

def aliceBob := sharedSecret alice.prv.val bob.pub
def bobAlice := sharedSecret bob.prv.val alice.pub

#lspec group "Alice and Bob"
  $ group "Public key matches expectation"
    (
      test "Alice" (
        alice.pub =
          EllipticCurve.Point.mk
            0x86b1aa5120f079594348c67647679e7ac4c365b2c01330db782b0ba611c1d677
            0x5f4376a23eed633657a90f385ba21068ed7e29859a7fab09e953cc5b3e89beba
        )
    $ test "Bob" (
        bob.pub =
          EllipticCurve.Point.mk
            0x4034127647bb7fdab7f1526c7d10be8b28174e2bba35b06ffd8a26fc2c20134a
            0x9e773199edc1ea792b150270ea3317689286c9fe239dd5b9c5cfd9e81b4b632
        )
    )
  $ group "Shared secret"
    (
      test "Commutes" (
        aliceBob = bobAlice
      )
    $ test "Matches expectation" (
      aliceBob =
        EllipticCurve.Point.mk
          0x3e2ffbc3aa8a2836c1689e55cd169ba638b58a3a18803fcf7de153525b28c3cd
          0x43ca148c92af58ebdb525542488a4fe6397809200fe8c61b41a105449507083
      )
    )


structure TestCase (g : EllipticCurve.Group ec) where
  alice : Group.KeyPair g
  bob : Group.KeyPair g
deriving Repr

instance : SlimCheck.Shrinkable Testcase where
  shrink _ := []

instance [Repr (TestCase g)] [Random Id (KeyPair g)] : SlimCheck.SampleableExt (TestCase g) :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let alice ← (Random.random : Rand (KeyPair g))
      let bob ← (Random.random : Rand (KeyPair g))
      pure $ ⟨ alice , bob ⟩

#lspec group "Shared secret"
  $ check "commutes" (∀ tc : TestCase Secp256k1, sharedSecret tc.alice.prv.val tc.bob.pub = sharedSecret tc.bob.prv.val tc.alice.pub)


end Crypto.EllipticCurve.ECDH.Test
