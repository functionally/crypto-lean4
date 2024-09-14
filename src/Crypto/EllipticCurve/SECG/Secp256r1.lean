import Crypto.EllipticCurve
import Crypto.Field.Fp

open Crypto
open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.EllipticCurve


-- https://neuromancer.sk/std/secg/secp256r1

namespace Secp256r1

  abbrev p := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  abbrev F := Fp p

  def curve : EllipticCurve F :=
    ⟨
      0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
    , 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
    ⟩

end Secp256r1

def Secp256r1 : EllipticCurve.Group Secp256r1.curve :=
    EllipticCurve.Group.mkGroup
      0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
      0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
      0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
      0x1


end Crypto.EllipticCurve
