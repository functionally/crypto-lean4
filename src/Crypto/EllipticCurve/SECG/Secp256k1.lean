import Crypto.EllipticCurve
import Crypto.Field.Fp

open Crypto
open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.EllipticCurve


-- https://neuromancer.sk/std/secg/secp256k1

namespace Secp256k1

  abbrev p := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
  abbrev F := Fp p

  def curve : EllipticCurve F :=
    ⟨
      0x0000000000000000000000000000000000000000000000000000000000000000
    , 0x0000000000000000000000000000000000000000000000000000000000000007
    ⟩

end Secp256k1

def Secp256k1 : EllipticCurve.Group Secp256k1.curve :=
    EllipticCurve.Group.mkGroup
      0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
      0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
      0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
      0x1


end Crypto.EllipticCurve
