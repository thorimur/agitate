/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
`Agitate.ImportGraph`: code meant for upstream ImportGraph: graphs at scale (`Graph`), kinds of need
between declarations (`NeedKinds`), source items (`SourceItems`) and a `ByteArray` bitset. It depends only on Lean, so that it can move
upstream by dropping the `Agitate.` prefix from its module and namespace names.
-/
module

public import Agitate.ImportGraph.Bitset
public import Agitate.ImportGraph.Graph
public import Agitate.ImportGraph.NeedKinds
public import Agitate.ImportGraph.SourceItems
