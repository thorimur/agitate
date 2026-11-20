module

-- Instance resolution finds `natWidget` only through `Fixture.InstAttr`, and records no extra
-- module use for it: only the indirect use (kind `instance`) keeps this import.
public import Fixture.InstAttr

public def instUse : Widget := HasWidget.w (α := Nat)
