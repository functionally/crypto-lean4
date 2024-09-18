
import Crypto.Hash
import Crypto.Serial

open Crypto


namespace Crypto.API


def bytesToHex (inFile : System.FilePath) (outFile : System.FilePath) : IO Unit :=
  do
    let src ← IO.FS.readBinFile inFile
    let dst := Serial.bytesToHex src
    IO.FS.writeFile outFile $ dst ++ "\n"


def bytesToNat (inFile : System.FilePath) (outFile : System.FilePath) : IO Unit :=
  do
    let src ← IO.FS.readBinFile inFile
    let dst : Nat := Serial.Words.fromWords src.toList.toArray
    IO.FS.writeFile outFile $ toString dst ++ "\n"


def parseHashAlgorithm : String → Option (CHash.Algorithm)
| "SHA2_224" => some CHash.Algorithm.SHA2_224
| "SHA2_256" => some CHash.Algorithm.SHA2_256
| "SHA2_384" => some CHash.Algorithm.SHA2_384
| "SHA2_512" => some CHash.Algorithm.SHA2_512
| _ => none

def hash (alg : CHash.Algorithm) (inFile : System.FilePath) (outFile : System.FilePath) : IO Unit :=
  do
    let src ← IO.FS.readBinFile inFile
    let dst :=
      Serial.bytesToHex
        ∘ CHash.data
        ∘ alg.chash
        $ src
    IO.FS.writeFile outFile $ dst ++ "\n"


end Crypto.API
