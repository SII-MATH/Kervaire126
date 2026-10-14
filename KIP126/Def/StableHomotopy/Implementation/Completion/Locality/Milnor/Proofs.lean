module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Data
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Limit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Triangle.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

/-- The actually constructed source product of local objects is local. -/
theorem SourceIsHF2Local.product {J : Type} (X : J → SourceCategory.{0})
    (hX : ∀ j, SourceIsHF2Local (X j)) : SourceIsHF2Local (∏ᶜ X) :=
  SourceIsHF2Local.of_isLimit (limit.cone (Discrete.functor X))
    (limit.isLimit _) (fun j => hX j.as)

/-- The actual source Milnor construction retains coefficient locality. -/
theorem SourceIsHF2Local.sourceHomotopyLimit (D : InverseSequence SourceCategory.{0})
    (hD : ∀ k, SourceIsHF2Local (D.obj k)) : SourceIsHF2Local (sourceHomotopyLimit D) := by
  let H := sourceHomotopyLimitWitness D
  have hP : SourceIsHF2Local (∏ᶜ D.obj) := SourceIsHF2Local.product D.obj hD
  intro A B f hf
  exact SourceIsHF2Local.triangle_first
    (Pretriangulated.Triangle.mk H.toProduct D.oneSubShift H.boundary)
    H.distinguished hP hP f hf

end KIP126.StableHomotopy.Implementation
