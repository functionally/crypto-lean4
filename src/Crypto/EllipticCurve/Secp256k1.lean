import Crypto.Field.Fp
import Crypto.EllipticCurve

open Crypto
open Crypto.Field
open Crypto.EllipticCurve


namespace Crypto.EllipticCurve


namespace Secp256k1

  abbrev F := Fp 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

  def curve : EllipticCurve F := ⟨ 0 , 7 ⟩

end Secp256k1

def Secp256k1 : EllipticCurve.Group Secp256k1.curve :=
    EllipticCurve.Group.mkGroup
      0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
      0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
      0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
      1


end Crypto.EllipticCurve
