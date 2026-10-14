module

@[expose] public section

/-! Lossless native module catalogue records. These are finite data,
not actual Ext modules or assertions that unrecorded degrees vanish. -/
namespace KIP126.LinModule.RawData

structure GeneratorRow where
  id : Nat
  name : Option String
  repr : Nat
  s : Nat
  t : Nat
  cell : Option Nat
  cellCoeff : Option String
  deriving Repr, DecidableEq, Inhabited

structure RelationRow where
  sqliteRowid : Nat
  code : String
  s : Nat
  t : Nat
  deriving Repr, DecidableEq, Inhabited

end KIP126.LinModule.RawData
