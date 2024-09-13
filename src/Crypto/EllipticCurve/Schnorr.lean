import Crypto.EllipticCurve
import Crypto.Field.Fp
import Crypto.Serial
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.EllipticCurve.Group
open Crypto.Field


namespace Crypto.EllipticCurve.Schnorr


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


-- https://medium.com/@francomangone18/cryptography-101-protocols-galore-7b858e6a38bf

structure Signature (g : Group ec) where
  hash : Fp g.n
  proof : Fp g.n
deriving Repr, DecidableEq, BEq

def sign [RandomGen gen] [Monad m] {g : Group ec} (h : ByteArray → Nat) (key : Group.KeyPair g) (message : ByteArray) : RandGT gen m (Signature g) :=
  do
    let r : Fp g.n ← Random.random
    let R := r * g.G
    let e := Fp.mk ∘ h $ ByteArray.append (Serial.natToBytes R.x.val) message
    let s := r - e * key.prv
    pure ⟨ e , s ⟩

def verify (h : ByteArray → Nat) (key : Group.PubKey g) (message : ByteArray) : Signature g → Bool
| ⟨ e , s ⟩ =>
    let R := s * g.G + e * key.pub
    let e' := Fp.mk ∘ h $ ByteArray.append (Serial.natToBytes R.x.val) message
    e = e'


structure Response (g : Group ec) where
  public : Point ec
  proof : Fp g.n
deriving Repr, DecidableEq, BEq

def commit [RandomGen gen] [Monad m] {g : Group ec} : RandGT gen m (Group.KeyPair g) :=
  Random.random

def challenge {g : Group ec} (r : Group.KeyPair g) (secret : Fp g.n) (chal : Fp g.n) : Response g :=
  let pub := secret * g.G
  let s := r.prv + chal * secret
  ⟨ pub , s ⟩

def confirm {g : Group ec} (r : Group.PubKey g) (chal : Fp g.n) : Response g → Bool
| ⟨ pub , s ⟩ =>
    s * g.G = r.pub + chal * pub


def combinePubKeys {g : Group ec} : List (Group.PubKey g) → Group.PubKey g :=
  Group.PubKey.mk ∘ List.foldl (fun acc => Add.add acc ∘ Group.PubKey.pub) Point.infinity

def partialsign [RandomGen gen] [Monad m] {g : Group ec} (h : ByteArray → Nat) (key : Group.KeyPair g) (k : Fp g.n) (R : Point ec) (message : ByteArray) : RandGT gen m (Signature g) :=
  do
    let e := Fp.mk ∘ h $ ByteArray.append (Serial.natToBytes R.x.val) message
    let s := k - e * key.prv
    pure ⟨ e , s ⟩

def multisig {g : Group ec} (ss :List (Signature g)) (h : ss ≠ []): Signature g :=
  ⟨
    (ss.head h).hash
  , ss.foldl (fun acc x => acc + x.proof) 0
  ⟩


end Crypto.EllipticCurve.Schnorr
