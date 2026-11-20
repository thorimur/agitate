-- Instance resolution finds `natWidget` only through `Fixture.InstAttr` and records nothing:
-- only the indirect use (kind `instance`) keeps this import.
import Fixture.InstAttr

def instUse : Widget := HasWidget.w (α := Nat)
