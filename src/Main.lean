import Cli
import Crypto.API

open Cli
open Crypto


def getInFile (p : Parsed) : System.FilePath :=
  if p.hasFlag "input" then (p.flag! "input").value else "/dev/stdin"

def getOutFile (p : Parsed) : System.FilePath :=
  if p.hasFlag "output" then (p.flag! "output").value else "/dev/stdout"


def bytesToHexExec (p : Parsed) : IO UInt32 :=
  do
    API.bytesToHex (getInFile p) (getOutFile p)
    pure 0

def bytesToHex : Cmd := `[Cli|
  bytesToHex VIA bytesToHexExec;
  "Convert bytes to hexadecimal."
  FLAGS:
    i, input  : String ; "Input file."
    o, output : String ; "Output file."
]


def HashAlg : ParamType :=
  ParamType.mk
    "Hash algorithm"
    $ not ∘ BEq.beq none ∘ API.parseHashAlgorithm

def hashExec (p : Parsed) : IO UInt32 :=
  match API.parseHashAlgorithm (p.positionalArg! "alg").value with
  | some alg =>
      do
        API.hash alg (getInFile p) (getOutFile p)
        pure 0
  | none => pure 0

def hash : Cmd := `[Cli|
  hash VIA hashExec;
  "Hash bytes."
  FLAGS:
    i, input  : String ; "Input file."
    o, output : String ; "Output file."
  ARGS:
    alg : HashAlg; "SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512"
]


def crypto : Cmd := `[Cli|
  crypto NOOP;
  "Cryptographic operations."
  SUBCOMMANDS:
    bytesToHex;
    hash
]


def main (args : List String) : IO UInt32 :=
  crypto.validate args
