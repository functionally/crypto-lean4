import Crypto.Hash
import LSpec

open Crypto.CHash
open LSpec


namespace Crypto.Hash.Test


#lspec
  group "Wikipedia SHA2 test vectors"
    $ test "SHA2 224 on empty string." (Serial.bytesToHex (CHash.data $ Algorithm.SHA2_224.chash ByteArray.empty) = "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f")
    $ test "SHA2 256 on empty string." (Serial.bytesToHex (CHash.data $ Algorithm.SHA2_256.chash ByteArray.empty) = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    $ test "SHA2 384 on empty string." (Serial.bytesToHex (CHash.data $ Algorithm.SHA2_384.chash ByteArray.empty) = "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b")
    $ test "SHA2 512 on empty string." (Serial.bytesToHex (CHash.data $ Algorithm.SHA2_512.chash ByteArray.empty) = "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")


end Crypto.Hash.Test
