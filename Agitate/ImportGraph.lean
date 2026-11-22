/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
`Agitate.ImportGraph`: dependency graphs at scale (generic reachability, strongly connected
components and label propagation, plus ImportGraph's constant-dependency functions on top). It
depends only on Lean, so that it can move upstream to ImportGraph by dropping the `Agitate.` prefix
from its module and namespace names.
-/
module

public import Agitate.ImportGraph.Bitset
public import Agitate.ImportGraph.Graph
public import Agitate.ImportGraph.Environment
