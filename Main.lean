import Agitate

open Agitate

def main (argv : List String) : IO UInt32 :=
  cliMain .module (fun args sp => Shake.run args sp) argv
