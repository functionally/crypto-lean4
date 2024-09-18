
import Crypto.Hash
import Crypto.Serial

open Crypto


namespace Crypto.API


def bytesToHex (inFile : System.FilePath) (outFile : System.FilePath) : IO Unit :=
  IO.FS.writeFile outFile
    ∘ Serial.bytesToHex
    =<< IO.FS.readBinFile inFile


def parseHashAlgorithm : String → Option (CHash.Algorithm)
| "SHA2_224" => some CHash.Algorithm.SHA2_224
| "SHA2_256" => some CHash.Algorithm.SHA2_256
| "SHA2_384" => some CHash.Algorithm.SHA2_384
| "SHA2_512" => some CHash.Algorithm.SHA2_512
| _ => none

def hash (alg : CHash.Algorithm) (inFile : System.FilePath) (outFile : System.FilePath) : IO Unit :=
  IO.FS.writeFile outFile
    ∘ Serial.bytesToHex
    ∘ CHash.data
    ∘ alg.chash
    =<< IO.FS.readBinFile inFile


end Crypto.API
