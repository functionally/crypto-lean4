import Crypto.EllipticCurve
import Crypto.Field.Fp

open Crypto
open Crypto.EllipticCurve
open Crypto.Field


namespace Crypto.EllipticCurve


-- https://neuromancer.sk/std/secg/secp384r1#

namespace Secp384r1

  abbrev p := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
  abbrev F := Fp p

  def curve : EllipticCurve F :=
    ⟨
      0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc
    , 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
    ⟩

end Secp384r1

def Secp384r1 : EllipticCurve.Group Secp384r1.curve :=
    EllipticCurve.Group.mkGroup
      0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
      0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
      0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
      0x1


end Crypto.EllipticCurve
