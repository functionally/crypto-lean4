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
    API.BytesToHex (getInFile p) (getOutFile p)
    pure 0

def bytesToHex : Cmd := `[Cli|
  bytesToHex VIA bytesToHexExec;
  "Convert bytes to hexadecimal."
  FLAGS:
    i, input  : String ; "Input file."
    o, output : String ; "Output file."
]


def crypto : Cmd := `[Cli|
  crypto NOOP;
  "Cryptographic operations."
  SUBCOMMANDS:
    bytesToHex
]


def main (args : List String) : IO UInt32 :=
  crypto.validate args
