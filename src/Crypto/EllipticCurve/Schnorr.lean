import Crypto.EllipticCurve
import Crypto.EllipticCurve.ECDH
import Crypto.EllipticCurve.Secp256k1
import Crypto.Field.Fp
import Crypto.Hash.SHA2
import LSpec

open Crypto
open Crypto.EllipticCurve
open Crypto.EllipticCurve.ECDH
open Crypto.EllipticCurve.Group
open Crypto.Field
open Crypto.Hash.SHA2
open LSpec


namespace Crypto.EllipticCurve.Schnorr

-- https://medium.com/@francomangone18/cryptography-101-protocols-galore-7b858e6a38bf

abbrev g := Secp256k1

def alice : KeyPair Secp256k1 := keyPair 0xe32868331fa8ef0138de0de85478346aec5e3912b6029ae71691c384237a3eeb

def r : Fp g.n := 2342211

def R := r * g.G
#eval R
-- signature

def message : ByteArray := Serializable.encode "abdde"
#eval message

def rby : ByteArray := Serial.Words.fromWords (Serial.Words.toWords R.x.val : Array UInt32)
#eval rby


def e : Fp g.n := Fp.mk $ sha256 $ rby.append message
#eval e

def s := r - e * alice.prv

def deliver := Prod.mk s e

def R' := s * g.G + e * alice.pub
#eval R'
#eval R = R'


-- protocol

-- alice : prover
def prv := 59174
def pub := prv * g.G
def commitment := 2324811
def Rc := commitment * g.G

--bob : verifier
def challenge := 48191

--alice
def ss := commitment + challenge * prv

--bob
#eval ss * g.G = Rc + challenge * pub


-- *** Use for TSS because of linearity


end Crypto.EllipticCurve.Schnorr
