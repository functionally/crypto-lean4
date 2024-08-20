import Crypto.Hash.SHA2
import Crypto.Serial

open Crypto.Hash.SHA2
open Crypto.Serial

open Bits

namespace Crypto.Hash.SHA2.Test


def x0 : Array UInt32 := pad SHA_224 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def x1 : Array UInt32 := #[0x61626364, 0x65800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
#eval x0
#eval x1
#eval x0 == x1

def y0 : Array UInt64 := pad SHA_512 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def y1 : Array UInt64 := #[0x6162636465800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
#eval y0
#eval y1
#eval y0 == y1

def t1 : Array UInt32 := #[0xd14a028c, 0x2a3a2bc9, 0x476102bb, 0x288234c4, 0x15a2b01f, 0x828ea62a, 0xc5b3e42f]


def s0 := hashBytes SHA_224 $ ByteArray.empty
#eval s0.pop
#eval t1

def z : ByteArray := sha224 $ ByteArray.mk #[]
#eval z

def w : Nat := sha224 $ ByteArray.mk #[]
#eval w


end Crypto.Hash.SHA2.Test
