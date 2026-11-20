module

-- The exposed body needs `Fixture.A` publicly; `Fixture.B` is only used privately.
public import Fixture.A
public import Fixture.B

@[expose] public def exposed : Nat := a
public def notExposed : Nat := b
