import LSpec

import Crypto.ECDH
import Crypto.EllipticCurve
import Crypto.EllipticCurve.Secp256k1

open Crypto.ECDH
open Crypto.EllipticCurve.Group
open LSpec


namespace Crypto.EllipticCurve.ECDH.Test


-- https://andrea.corbellini.name/2015/05/30/elliptic-curve-cryptography-ecdh-and-ecdsa/

abbrev g := Secp256k1


def alice : KeyPair g := keyPair 0xe32868331fa8ef0138de0de85478346aec5e3912b6029ae71691c384237a3eeb
def bob : KeyPair g := keyPair 0xcef147652aa90162e1fff9cf07f2605ea05529ca215a04350a98ecc24aa34342

#lspec group "Public key matches expectation"
  $ test "Alice" (
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


def aliceBob := sharedSecret alice.prv bob.pub
def bobAlice := sharedSecret bob.prv alice.pub

#lspec group "Shared secret"
  $ test "Commutes" (
      aliceBob = bobAlice
    )
  $ test "Matches expectation" (
      aliceBob =
        EllipticCurve.Point.mk
          0x3e2ffbc3aa8a2836c1689e55cd169ba638b58a3a18803fcf7de153525b28c3cd
          0x43ca148c92af58ebdb525542488a4fe6397809200fe8c61b41a105449507083
    )


end Crypto.EllipticCurve.ECDH.Test
