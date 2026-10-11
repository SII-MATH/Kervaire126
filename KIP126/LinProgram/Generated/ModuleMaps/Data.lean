module

@[expose] public section

/-! Lossless complete native map graph rows. An empty image is the
recorded zero string; absent and SQL NULL images are rejected by the exporter.
These records do not assert that the graph descends to any quotient module. -/
namespace KIP126.LinModule.RawData.Maps

structure ImageRow where
  id : Nat
  image : String
  deriving Repr, DecidableEq, Inhabited

end KIP126.LinModule.RawData.Maps
