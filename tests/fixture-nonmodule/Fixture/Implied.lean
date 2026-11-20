-- `Fixture.A` is implied by `Fixture.B` (imports re-export), so it is removed
-- unless `--keep-implied`.
import Fixture.A
import Fixture.B

def implied : Nat := a + b
