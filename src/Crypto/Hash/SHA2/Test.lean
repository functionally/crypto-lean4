import LSpec

import Crypto.Hash.SHA2
import Crypto.Serial

open Crypto.Hash.SHA2
open Crypto.Serial

open Bits

open LSpec


namespace Crypto.Hash.SHA2.Test


def x0 : Array UInt32 := pad SHA_224 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def x1 : Array UInt32 := #[0x61626364, 0x65800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
#lspec test "SHA2_224 test vector #1." (x0 = x1)


def y0 : Array UInt32 := pad SHA_224 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def y1 : Array UInt32 := #[0x61626364, 0x65800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
#lspec test "SHA2 224 test vector #2." (x0 = x1)


def z0 : Array UInt64 := pad SHA_512 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def z1 : Array UInt64 := #[0x6162636465800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
#lspec test "SHA2 512 test vector #1." (y0 = y1)


def w0 : Array UInt32 := Array.pop $ hashBytes SHA_224 $ ByteArray.empty
def w1 : Array UInt32 := #[0xd14a028c, 0x2a3a2bc9, 0x476102bb, 0x288234c4, 0x15a2b01f, 0x828ea62a, 0xc5b3e42f]
#lspec test "SHA2 224 test vector #3." (w0 == w1)

-- FIXME: Convert to test.
def z : ByteArray := sha224 $ ByteArray.mk #[]

-- FIXME: Convert to test.
def w : Nat := sha224 $ ByteArray.mk #[]


end Crypto.Hash.SHA2.Test
