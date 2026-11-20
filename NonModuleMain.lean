import Agitate


open Agitate

def main (argv : List String) : IO UInt32 :=
  cliMain .nonModule (fun args sp => NonModule.run args sp) argv
