import LSpec

import Crypto.Hash.SHA2
import Crypto.Serial

open Crypto.Hash.SHA2
open Crypto.Serial

open Bits
open LSpec


namespace Crypto.Hash.SHA2.Test


-- https://datatracker.ietf.org/doc/html/rfc6234#section-4

def x0 : Array UInt32 := pad SHA_224 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def x1 : Array UInt32 := #[0x61626364, 0x65800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]

def y0 : Array UInt32 := pad SHA_224 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def y1 : Array UInt32 := #[0x61626364, 0x65800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]

def z0 : Array UInt64 := pad SHA_512 $ ByteArray.mk #[0x61, 0x62, 0x63, 0x64, 0x65]
def z1 : Array UInt64 := #[0x6162636465800000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]

def w0 : Array UInt32 := Array.pop $ hashBytes SHA_224 $ ByteArray.empty
def w1 : Array UInt32 := #[0xd14a028c, 0x2a3a2bc9, 0x476102bb, 0x288234c4, 0x15a2b01f, 0x828ea62a, 0xc5b3e42f]

#lspec
  group "RFC6234 message padding"
    $ test "SHA2_224 test vector #1." (x0 = x1)
    $ test "SHA2 224 test vector #2." (x0 = x1)
    $ test "SHA2 512 test vector #1." (y0 = y1)
    $ test "SHA2 224 test vector #3." (w0 == w1)


-- https://datatracker.ietf.org/doc/html/rfc6234#section-8.5

def TEST1 := "abc"
def TEST2_1 := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
def TEST2_2a := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn"
def TEST2_2b := "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
def TEST2_2 := TEST2_2a ++ TEST2_2b
def TEST3 := "".intercalate $ List.replicate 1000000 "a"
def TEST4a := "01234567012345670123456701234567"
def TEST4b := "01234567012345670123456701234567"
def TEST4 := "".intercalate $ List.replicate 10 $ TEST4a ++ TEST4b
def TEST7_1 := "\x49\xb2\xae\xc2\x59\x4b\xbe\x3a\x3b\x11\x75\x42\xd9\x4a\xc8"
def TEST8_1 := "\x9a\x7d\xfd\xf1\xec\xea\xd0\x6e\xd6\x46\xaa\x55\xfe\x75\x71\x46"
def TEST9_1 :=
         "\x65\xf9\x32\x99\x5b\xa4\xce\x2c\xb1\xb4\xa2\xe7\x1a\xe7\x02\x20"
      ++ "\xaa\xce\xc8\x96\x2d\xd4\x49\x9c\xbd\x7c\x88\x7a\x94\xea\xaa\x10"
      ++ "\x1e\xa5\xaa\xbc\x52\x9b\x4e\x7e\x43\x66\x5a\x5a\xf2\xcd\x03\xfe"
      ++ "\x67\x8e\xa6\xa5\x00\x5b\xba\x3b\x08\x22\x04\xc2\x8b\x91\x09\xf4"
      ++ "\x69\xda\xc9\x2a\xaa\xb3\xaa\x7c\x11\xa1\xb3\x2a"
def TEST10_1 :=
         "\xf7\x8f\x92\x14\x1b\xcd\x17\x0a\xe8\x9b\x4f\xba\x15\xa1\xd5\x9f"
      ++ "\x3f\xd8\x4d\x22\x3c\x92\x51\xbd\xac\xbb\xae\x61\xd0\x5e\xd1\x15"
      ++ "\xa0\x6a\x7c\xe1\x17\xb7\xbe\xea\xd2\x44\x21\xde\xd9\xc3\x25\x92"
      ++ "\xbd\x57\xed\xea\xe3\x9c\x39\xfa\x1f\xe8\x94\x6a\x84\xd0\xcf\x1f"
      ++ "\x7b\xee\xad\x17\x13\xe2\xe0\x95\x98\x97\x34\x7f\x67\xc8\x0b\x04"
      ++ "\x00\xc2\x09\x81\x5d\x6b\x10\xa6\x83\x83\x6f\xd5\x56\x2a\x56\xca"
      ++ "\xb1\xa2\x8e\x81\xb6\x57\x66\x54\x63\x1c\xf1\x65\x66\xb8\x6e\x3b"
      ++ "\x33\xa1\x08\xb0\x53\x07\xc0\x0a\xff\x14\xa7\x68\xed\x73\x50\x60"
      ++ "\x6a\x0f\x85\xe6\xa9\x1d\x39\x6f\x5b\x5c\xbe\x57\x7f\x9b\x38\x80"
      ++ "\x7c\x7d\x52\x3d\x6d\x79\x2f\x6e\xbc\x24\xa4\xec\xf2\xb3\xa4\x27"
      ++ "\xcd\xbb\xfb"
def TEST7_224 := "\xf0\x70\x06\xf2\x5a\x0b\xea\x68\xcd\x76\xa2\x95\x87\xc2\x8d"
def TEST8_224 := "\x18\x80\x40\x05\xdd\x4f\xbd\x15\x56\x29\x9d\x6f\x9d\x93\xdf\x62"
def TEST9_224 :=
         "\xa2\xbe\x6e\x46\x32\x81\x09\x02\x94\xd9\xce\x94\x82\x65\x69\x42"
      ++ "\x3a\x3a\x30\x5e\xd5\xe2\x11\x6c\xd4\xa4\xc9\x87\xfc\x06\x57\x00"
      ++ "\x64\x91\xb1\x49\xcc\xd4\xb5\x11\x30\xac\x62\xb1\x9d\xc2\x48\xc7"
      ++ "\x44\x54\x3d\x20\xcd\x39\x52\xdc\xed\x1f\x06\xcc\x3b\x18\xb9\x1f"
      ++ "\x3f\x55\x63\x3e\xcc\x30\x85\xf4\x90\x70\x60\xd2"
def TEST10_224 :=
         "\x55\xb2\x10\x07\x9c\x61\xb5\x3a\xdd\x52\x06\x22\xd1\xac\x97\xd5"
      ++ "\xcd\xbe\x8c\xb3\x3a\xa0\xae\x34\x45\x17\xbe\xe4\xd7\xba\x09\xab"
      ++ "\xc8\x53\x3c\x52\x50\x88\x7a\x43\xbe\xbb\xac\x90\x6c\x2e\x18\x37"
      ++ "\xf2\x6b\x36\xa5\x9a\xe3\xbe\x78\x14\xd5\x06\x89\x6b\x71\x8b\x2a"
      ++ "\x38\x3e\xcd\xac\x16\xb9\x61\x25\x55\x3f\x41\x6f\xf3\x2c\x66\x74"
      ++ "\xc7\x45\x99\xa9\x00\x53\x86\xd9\xce\x11\x12\x24\x5f\x48\xee\x47"
      ++ "\x0d\x39\x6c\x1e\xd6\x3b\x92\x67\x0c\xa5\x6e\xc8\x4d\xee\xa8\x14"
      ++ "\xb6\x13\x5e\xca\x54\x39\x2b\xde\xdb\x94\x89\xbc\x9b\x87\x5a\x8b"
      ++ "\xaf\x0d\xc1\xae\x78\x57\x36\x91\x4a\xb7\xda\xa2\x64\xbc\x07\x9d"
      ++ "\x26\x9f\x2c\x0d\x7e\xdd\xd8\x10\xa4\x26\x14\x5a\x07\x76\xf6\x7c"
      ++ "\x87\x82\x73"
def TEST7_256 := "\xbe\x27\x46\xc6\xdb\x52\x76\x5f\xdb\x2f\x88\x70\x0f\x9a\x73"
def TEST8_256 := "\xe3\xd7\x25\x70\xdc\xdd\x78\x7c\xe3\x88\x7a\xb2\xcd\x68\x46\x52"
def TEST9_256 :=
         "\x3e\x74\x03\x71\xc8\x10\xc2\xb9\x9f\xc0\x4e\x80\x49\x07\xef\x7c"
      ++ "\xf2\x6b\xe2\x8b\x57\xcb\x58\xa3\xe2\xf3\xc0\x07\x16\x6e\x49\xc1"
      ++ "\x2e\x9b\xa3\x4c\x01\x04\x06\x91\x29\xea\x76\x15\x64\x25\x45\x70"
      ++ "\x3a\x2b\xd9\x01\xe1\x6e\xb0\xe0\x5d\xeb\xa0\x14\xeb\xff\x64\x06"
      ++ "\xa0\x7d\x54\x36\x4e\xff\x74\x2d\xa7\x79\xb0\xb3"
def TEST10_256 :=
         "\x83\x26\x75\x4e\x22\x77\x37\x2f\x4f\xc1\x2b\x20\x52\x7a\xfe\xf0"
      ++ "\x4d\x8a\x05\x69\x71\xb1\x1a\xd5\x71\x23\xa7\xc1\x37\x76\x00\x00"
      ++ "\xd7\xbe\xf6\xf3\xc1\xf7\xa9\x08\x3a\xa3\x9d\x81\x0d\xb3\x10\x77"
      ++ "\x7d\xab\x8b\x1e\x7f\x02\xb8\x4a\x26\xc7\x73\x32\x5f\x8b\x23\x74"
      ++ "\xde\x7a\x4b\x5a\x58\xcb\x5c\x5c\xf3\x5b\xce\xe6\xfb\x94\x6e\x5b"
      ++ "\xd6\x94\xfa\x59\x3a\x8b\xeb\x3f\x9d\x65\x92\xec\xed\xaa\x66\xca"
      ++ "\x82\xa2\x9d\x0c\x51\xbc\xf9\x33\x62\x30\xe5\xd7\x84\xe4\xc0\xa4"
      ++ "\x3f\x8d\x79\xa3\x0a\x16\x5c\xba\xbe\x45\x2b\x77\x4b\x9c\x71\x09"
      ++ "\xa9\x7d\x13\x8f\x12\x92\x28\x96\x6f\x6c\x0a\xdc\x10\x6a\xad\x5a"
      ++ "\x9f\xdd\x30\x82\x57\x69\xb2\xc6\x71\xaf\x67\x59\xdf\x28\xeb\x39"
      ++ "\x3d\x54\xd6"
def TEST7_384 := "\x8b\xc5\x00\xc7\x7c\xee\xd9\x87\x9d\xa9\x89\x10\x7c\xe0\xaa"
def TEST8_384 := "\xa4\x1c\x49\x77\x79\xc0\x37\x5f\xf1\x0a\x7f\x4e\x08\x59\x17\x39"
def TEST9_384 :=
         "\x68\xf5\x01\x79\x2d\xea\x97\x96\x76\x70\x22\xd9\x3d\xa7\x16\x79"
      ++ "\x30\x99\x20\xfa\x10\x12\xae\xa3\x57\xb2\xb1\x33\x1d\x40\xa1\xd0"
      ++ "\x3c\x41\xc2\x40\xb3\xc9\xa7\x5b\x48\x92\xf4\xc0\x72\x4b\x68\xc8"
      ++ "\x75\x32\x1a\xb8\xcf\xe5\x02\x3b\xd3\x75\xbc\x0f\x94\xbd\x89\xfe"
      ++ "\x04\xf2\x97\x10\x5d\x7b\x82\xff\xc0\x02\x1a\xeb\x1c\xcb\x67\x4f"
      ++ "\x52\x44\xea\x34\x97\xde\x26\xa4\x19\x1c\x5f\x62\xe5\xe9\xa2\xd8"
      ++ "\x08\x2f\x05\x51\xf4\xa5\x30\x68\x26\xe9\x1c\xc0\x06\xce\x1b\xf6"
      ++ "\x0f\xf7\x19\xd4\x2f\xa5\x21\xc8\x71\xcd\x23\x94\xd9\x6e\xf4\x46"
      ++ "\x8f\x21\x96\x6b\x41\xf2\xba\x80\xc2\x6e\x83\xa9"
def TEST10_384 :=
         "\x39\x96\x69\xe2\x8f\x6b\x9c\x6d\xbc\xbb\x69\x12\xec\x10\xff\xcf"
      ++ "\x74\x79\x03\x49\xb7\xdc\x8f\xbe\x4a\x8e\x7b\x3b\x56\x21\xdb\x0f"
      ++ "\x3e\x7d\xc8\x7f\x82\x32\x64\xbb\xe4\x0d\x18\x11\xc9\xea\x20\x61"
      ++ "\xe1\xc8\x4a\xd1\x0a\x23\xfa\xc1\x72\x7e\x72\x02\xfc\x3f\x50\x42"
      ++ "\xe6\xbf\x58\xcb\xa8\xa2\x74\x6e\x1f\x64\xf9\xb9\xea\x35\x2c\x71"
      ++ "\x15\x07\x05\x3c\xf4\xe5\x33\x9d\x52\x86\x5f\x25\xcc\x22\xb5\xe8"
      ++ "\x77\x84\xa1\x2f\xc9\x61\xd6\x6c\xb6\xe8\x95\x73\x19\x9a\x2c\xe6"
      ++ "\x56\x5c\xbd\xf1\x3d\xca\x40\x38\x32\xcf\xcb\x0e\x8b\x72\x11\xe8"
      ++ "\x3a\xf3\x2a\x11\xac\x17\x92\x9f\xf1\xc0\x73\xa5\x1c\xc0\x27\xaa"
      ++ "\xed\xef\xf8\x5a\xad\x7c\x2b\x7c\x5a\x80\x3e\x24\x04\xd9\x6d\x2a"
      ++ "\x77\x35\x7b\xda\x1a\x6d\xae\xed\x17\x15\x1c\xb9\xbc\x51\x25\xa4"
      ++ "\x22\xe9\x41\xde\x0c\xa0\xfc\x50\x11\xc2\x3e\xcf\xfe\xfd\xd0\x96"
      ++ "\x76\x71\x1c\xf3\xdb\x0a\x34\x40\x72\x0e\x16\x15\xc1\xf2\x2f\xbc"
      ++ "\x3c\x72\x1d\xe5\x21\xe1\xb9\x9b\xa1\xbd\x55\x77\x40\x86\x42\x14"
      ++ "\x7e\xd0\x96"
def TEST7_512 := "\x08\xec\xb5\x2e\xba\xe1\xf7\x42\x2d\xb6\x2b\xcd\x54\x26\x70"
def TEST8_512 := "\x8d\x4e\x3c\x0e\x38\x89\x19\x14\x91\x81\x6e\x9d\x98\xbf\xf0\xa0"
def TEST9_512 :=
         "\x3a\xdd\xec\x85\x59\x32\x16\xd1\x61\x9a\xa0\x2d\x97\x56\x97\x0b"
      ++ "\xfc\x70\xac\xe2\x74\x4f\x7c\x6b\x27\x88\x15\x10\x28\xf7\xb6\xa2"
      ++ "\x55\x0f\xd7\x4a\x7e\x6e\x69\xc2\xc9\xb4\x5f\xc4\x54\x96\x6d\xc3"
      ++ "\x1d\x2e\x10\xda\x1f\x95\xce\x02\xbe\xb4\xbf\x87\x65\x57\x4c\xbd"
      ++ "\x6e\x83\x37\xef\x42\x0a\xdc\x98\xc1\x5c\xb6\xd5\xe4\xa0\x24\x1b"
      ++ "\xa0\x04\x6d\x25\x0e\x51\x02\x31\xca\xc2\x04\x6c\x99\x16\x06\xab"
      ++ "\x4e\xe4\x14\x5b\xee\x2f\xf4\xbb\x12\x3a\xab\x49\x8d\x9d\x44\x79"
      ++ "\x4f\x99\xcc\xad\x89\xa9\xa1\x62\x12\x59\xed\xa7\x0a\x5b\x6d\xd4"
      ++ "\xbd\xd8\x77\x78\xc9\x04\x3b\x93\x84\xf5\x49\x06"
def TEST10_512 :=
         "\xa5\x5f\x20\xc4\x11\xaa\xd1\x32\x80\x7a\x50\x2d\x65\x82\x4e\x31"
      ++ "\xa2\x30\x54\x32\xaa\x3d\x06\xd3\xe2\x82\xa8\xd8\x4e\x0d\xe1\xde"
      ++ "\x69\x74\xbf\x49\x54\x69\xfc\x7f\x33\x8f\x80\x54\xd5\x8c\x26\xc4"
      ++ "\x93\x60\xc3\xe8\x7a\xf5\x65\x23\xac\xf6\xd8\x9d\x03\xe5\x6f\xf2"
      ++ "\xf8\x68\x00\x2b\xc3\xe4\x31\xed\xc4\x4d\xf2\xf0\x22\x3d\x4b\xb3"
      ++ "\xb2\x43\x58\x6e\x1a\x7d\x92\x49\x36\x69\x4f\xcb\xba\xf8\x8d\x95"
      ++ "\x19\xe4\xeb\x50\xa6\x44\xf8\xe4\xf9\x5e\xb0\xea\x95\xbc\x44\x65"
      ++ "\xc8\x82\x1a\xac\xd2\xfe\x15\xab\x49\x81\x16\x4b\xbb\x6d\xc3\x2f"
      ++ "\x96\x90\x87\xa1\x45\xb0\xd9\xcc\x9c\x67\xc2\x2b\x76\x32\x99\x41"
      ++ "\x9c\xc4\x12\x8b\xe9\xa0\x77\xb3\xac\xe6\x34\x06\x4e\x6d\x99\x28"
      ++ "\x35\x13\xdc\x06\xe7\x51\x5d\x0d\x73\x13\x2e\x9a\x0d\xc6\xd3\xb1"
      ++ "\xf8\xb2\x46\xf1\xa9\x8a\x3f\xc7\x29\x41\xb1\xe3\xbb\x20\x98\xe8"
      ++ "\xbf\x16\xf2\x68\xd6\x4f\x0b\x0f\x47\x07\xfe\x1e\xa1\xa1\x79\x1b"
      ++ "\xa2\xf3\xc0\xc7\x58\xe5\xf5\x51\x86\x3a\x96\xc9\x49\xad\x47\xd7"
      ++ "\xfb\x40\xd2"


def testCase (b : Bits) (message : String) (expected : String) : Bool :=
  bytesToHex (sha b $ Serializable.encode message) == expected.toLower

#lspec
  group "RFC6234 test driver"
    $ (
      group "SHA2 224"
        $ test "RFC6234 test 1" (testCase SHA_224 TEST1 "23097D223405D8228642A477BDA255B32AADBCE4BDA0B3F7E36C9DA7")
        $ test "RFC6234 test 2" (testCase SHA_224 TEST2_1 "75388B16512776CC5DBA5DA1FD890150B0C6455CB4F58B1952522525")
        $ test "RFC6234 test 4" (testCase SHA_224 TEST4 "567F69F168CD7844E65259CE658FE7AADFA25216E68ECA0EB7AB8262")
        $ test "RFC6234 test 8" (testCase SHA_224 TEST8_224 "DF90D78AA78821C99B40BA4C966921ACCD8FFB1E98AC388E56191DB1")
        $ test "RFC6234 test 10" (testCase SHA_224 TEST10_224 "0B31894EC8937AD9B91BDFBCBA294D9ADEFAA18E09305E9F20D5C3A4")
    ) ++ (
      group "SHA2 256"
        $ test "RFC6234 test 1" (testCase SHA_256 TEST1 "BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD")
        $ test "RFC6234 test 2" (testCase SHA_256 TEST2_1 "248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1")
        $ test "RFC6234 test 4" (testCase SHA_256 TEST4 "594847328451BDFA85056225462CC1D867D877FB388DF0CE35F25AB5562BFBB5")
        $ test "RFC6234 test 8" (testCase SHA_256 TEST8_256 "175EE69B02BA9B58E2B0A5FD13819CEA573F3940A94F825128CF4209BEABB4E8")
        $ test "RFC6234 test 10" (testCase SHA_256 TEST10_256 "97DBCA7DF46D62C8A422C941DD7E835B8AD3361763F7E9B2D95F4F0DA6E1CCBC")
    ) ++ (
      group "SHA2 384"
        $ test "RFC6234 test 1" (testCase SHA_384 TEST1 "CB00753F45A35E8BB5A03D699AC65007272C32AB0EDED1631A8B605A43FF5BED8086072BA1E7CC2358BAECA134C825A7")
        $ test "RFC6234 test 2" (testCase SHA_384 TEST2_2 "09330C33F71147E83D192FC782CD1B4753111B173B3B05D22FA08086E3B0F712FCC7C71A557E2DB966C3E9FA91746039")
        $ test "RFC6234 test 4" (testCase SHA_384 TEST4 "2FC64A4F500DDB6828F6A3430B8DD72A368EB7F3A8322A70BC84275B9C0B3AB00D27A5CC3C2D224AA6B61A0D79FB4596")
        $ test "RFC6234 test 8" (testCase SHA_384 TEST8_384 "C9A68443A005812256B8EC76B00516F0DBB74FAB26D665913F194B6FFB0E91EA9967566B58109CBC675CC208E4C823F7")
        $ test "RFC6234 test 10" (testCase SHA_384 TEST10_384 "4F440DB1E6EDD2899FA335F09515AA025EE177A79F4B4AAF38E42B5C4DE660F5DE8FB2A5B2FBD2A3CBFFD20CFF1288C0")
    ) ++ (
      group "SHA2 512"
        $ test "RFC6234 test 1" (testCase SHA_512 TEST1 "DDAF35A193617ABACC417349AE20413112E6FA4E89A97EA20A9EEEE64B55D39A2192992A274FC1A836BA3C23A3FEEBBD454D4423643CE80E2A9AC94FA54CA49F")
        $ test "RFC6234 test 2" (testCase SHA_512 TEST2_2 "8E959B75DAE313DA8CF4F72814FC143F8F7779C6EB9F7FA17299AEADB6889018501D289E4900F7E4331B99DEC4B5433AC7D329EEB6DD26545E96E55B874BE909")
        $ test "RFC6234 test 4" (testCase SHA_512 TEST4 "89D05BA632C699C31231DED4FFC127D5A894DAD412C0E024DB872D1ABD2BA8141A0F85072A9BE1E2AA04CF33C765CB510813A39CD5A84C4ACAA64D3F3FB7BAE9")
        $ test "RFC6234 test 8" (testCase SHA_512 TEST8_512 "CB0B67A4B8712CD73C9AABC0B199E9269B20844AFB75ACBDD1C153C9828924C3DDEDAAFE669C5FDD0BC66F630F6773988213EB1B16F517AD0DE4B2F0C95C90F8")
        $ test "RFC6234 test 10" (testCase SHA_512 TEST10_512 "C665BEFB36DA189D78822D10528CBF3B12B3EEF726039909C1A16A270D48719377966B957A878E720584779A62825C18DA26415E49A7176A894E7510FD1451F5")
    )


-- https://en.wikipedia.org/wiki/SHA-2#Test_vectors

#lspec
  group "Wikipedia SHA2 test vectors"
    $ test "SHA 224 on empty string." (testCase SHA_224 "" "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f")
    $ test "SHA 256 on empty string." (testCase SHA_256 "" "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    $ test "SHA 384 on empty string." (testCase SHA_384 "" "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b")
    $ test "SHA 512 on empty string." (testCase SHA_512 "" "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
    $ test "SHA 224 on sentence." (testCase SHA_224 "The quick brown fox jumps over the lazy dog" "730e109bd7a8a32b1cb9d9a09aa2325d2430587ddbc0c38bad911525")
    $ test "SHA 224 on variant sentence." (testCase SHA_224 "The quick brown fox jumps over the lazy dog." "619cba8e8e05826e9b8c519c0a5c68f4fb653e8a3d8aa04bb2c8cd4c")


end Crypto.Hash.SHA2.Test
