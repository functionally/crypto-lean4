import Crypto.EllipticCurve
import Crypto.Field.Fp
import Crypto.Serial
import Crypto.Polynomial.SSS
import Mathlib.Control.Random

open Crypto
open Crypto.EllipticCurve
open Crypto.EllipticCurve.Group
open Crypto.Polynomial
open Crypto.Field


namespace Crypto.EllipticCurve.Schnorr


variable {p : Nat}
variable {ec : EllipticCurve (Fp p)}


-- https://medium.com/@francomangone18/cryptography-101-protocols-galore-7b858e6a38bf

structure Signature (g : Group ec) where
  challenge : Fp g.n
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

def partialsign {g : Group ec} (h : ByteArray → Nat) (key : Group.KeyPair g) (k : Fp g.n) (R : Point ec) (message : ByteArray) : Signature g :=
  let e := Fp.mk ∘ h $ ByteArray.append (Serial.natToBytes R.x.val) message
  let s := k - e * key.prv
  ⟨ e , s ⟩

def multisig {g : Group ec} (shares : List (Signature g)) : Option (Signature g) :=
  match shares with
  | [] => none
  | s :: ss => if ss.all (fun s' => s.challenge == s'.challenge)
               then some
                    ⟨
                      s.challenge
                    , ss.foldl (fun acc x => acc + x.proof) s.proof
                    ⟩
               else none


def thresholdsig {g : Group ec} (shares : SSS.Shares (Fp g.n) (Signature g)) : Option (Signature g) :=
  match shares.xys with
  | [] => none
  | s :: ss => if ss.all (fun s' => s.y.challenge == s'.y.challenge)
                 then some
                        ⟨
                          s.y.challenge
                        , SSS.assemble $ Functor.map Signature.proof shares
                        ⟩
                 else none


end Crypto.EllipticCurve.Schnorr
