/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

import Agitate


open Agitate

def main (argv : List String) : IO UInt32 :=
  cliMain .nonModule (fun args sp => NonModule.run args sp) argv
