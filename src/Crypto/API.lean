
import Crypto.Serial

open Crypto


namespace Crypto.API


def BytesToHex (inFile : System.FilePath) (outFile : System.FilePath) : IO Unit :=
  IO.FS.writeFile outFile
    ∘ Serial.bytesToHex
    =<< IO.FS.readBinFile inFile


end Crypto.API
