module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Stable.Proofs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The full category of actual prespectra with T₁ levels. -/
abbrev T1Prespectrum :=
  ObjectProperty.FullSubcategory (fun X : Prespectrum.{u} => ∀ n, T1Space (X.level n))

instance T1Prespectrum.level_t1Space (X : T1Prespectrum.{u}) (n : ℕ) :
    T1Space (X.obj.level n) := X.property n

/-- The actual full inclusion, retaining the original levels and bonds. -/
def t1Inclusion : T1Prespectrum.{u} ⥤ Prespectrum.{u} := ObjectProperty.ι _

/-- Actual stable equivalences restricted to the T₁ full subcategory. -/
def t1StableEquivalences : MorphismProperty T1Prespectrum.{u} :=
  stableEquivalences.inverseImage t1Inclusion

/-- The concrete free-cubical construction as a functor into T₁ prespectra. -/
noncomputable def cubicalT1Replacement : Prespectrum.{u} ⥤ T1Prespectrum.{u} where
  obj X := ⟨cubicalReplacementFunctor.obj X, fun _ => inferInstance⟩
  map f := ObjectProperty.homMk (cubicalReplacementFunctor.map f)
  map_id X := ObjectProperty.hom_ext _ (cubicalReplacementFunctor.map_id X)
  map_comp f g := ObjectProperty.hom_ext _ (cubicalReplacementFunctor.map_comp f g)

/-- The actual comparison, restricted to the full subcategory. -/
noncomputable def cubicalT1Comparison :
    t1Inclusion.{u} ⋙ cubicalT1Replacement ⟶ 𝟭 _ where
  app X := ObjectProperty.homMk (cubicalReplacementComparison.app X.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ (cubicalReplacementComparison.naturality f.hom)

end KIP126.StableHomotopy.Implementation.Prespectrum
