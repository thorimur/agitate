/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
`Percolate`: dependency graphs at scale (generic reachability, strongly connected components and
label propagation, plus ImportGraph's constant-dependency functions on top). It depends only on
Lean, so that it can move upstream (to ImportGraph) as it is.
-/
module

public import Percolate.Bitset
public import Percolate.Graph
public import Percolate.Environment
