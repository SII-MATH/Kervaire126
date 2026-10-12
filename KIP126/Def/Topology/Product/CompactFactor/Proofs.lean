module

public import KIP126.Def.Topology.Product.CompactFactor.Data
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

/-- Product with an actual locally compact space commutes with arbitrary
existing colimits; this is proved from the compact-open adjunction. -/
theorem tensorLeft_preservesColimits_of_locallyCompact (K : TopCat.{u}) [LocallyCompactSpace K] :
    PreservesColimitsOfSize.{v,w} (tensorLeft K) := by
  letI : (tensorLeft K).IsLeftAdjoint := (tensorLeftContinuousMapAdjunction K).isLeftAdjoint
  infer_instance

end KIP126.Topology
