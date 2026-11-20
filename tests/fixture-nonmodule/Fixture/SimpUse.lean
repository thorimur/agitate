-- `simp` finds `a_eq` only through `Fixture.SimpAttr`, and records that itself.
import Fixture.SimpAttr

theorem simpUse : a + 0 = 1 := by simp
