import LSpec

import Crypto.ECDH
import Crypto.EllipticCurve
import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp

open Crypto.EllipticCurve
open Crypto.EllipticCurve.Group
open Crypto.ECDH
open Crypto.Field
open LSpec


namespace Crypto.ECIES

-- https://medium.com/@francomangone18/cryptography-101-encryption-and-digital-signatures-210960778765

abbrev g := Secp256k1

def alice : KeyPair Secp256k1 := keyPair 0xe32868331fa8ef0138de0de85478346aec5e3912b6029ae71691c384237a3eeb
def bob : KeyPair Secp256k1 := keyPair 0xcef147652aa90162e1fff9cf07f2605ea05529ca215a04350a98ecc24aa34342

def aliceBob := sharedSecret alice.prv.val bob.pub

def nonce : Fp g.n := 12335

def mask := nonce * alice.pub
#eval mask

def message := 42042

def cipher := mask.x.val.xor message
#eval cipher

def proof := nonce * g.G

def result := Prod.mk proof cipher

def mask' := alice.prv * proof
#eval mask'

def plain := mask'.x.val.xor cipher
#eval plain
#eval message = plain


end Crypto.ECIES
