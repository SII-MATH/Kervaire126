module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive.Hom.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

attribute [local instance] sourceHomGroup

/-- The transported addition is exactly actual loop concatenation after
applying the fully faithful source loop functor. -/
theorem sourceHomGroup_map_add {A B : SourceCategory.{u}} (f g : A ⟶ B) :
    sourceLoopFunctor.map (f + g) = sourceLoopAdd B.as.obj
      (sourceLoopFunctor.map f) (sourceLoopFunctor.map g) := by
  change (Functor.FullyFaithful.ofFullyFaithful sourceLoopFunctor).homEquiv
    ((Functor.FullyFaithful.ofFullyFaithful sourceLoopFunctor).homEquiv.symm
      (sourceLoopAdd B.as.obj (sourceLoopFunctor.map f) (sourceLoopFunctor.map g))) = _
  exact Equiv.apply_symm_apply _ _

theorem sourceHomGroup_add_comp {A B C : SourceCategory.{u}}
    (f g : A ⟶ B) (h : B ⟶ C) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  apply sourceLoopFunctor.map_injective
  rw [Functor.map_comp, sourceHomGroup_map_add, sourceHomGroup_map_add,
    Functor.map_comp, Functor.map_comp]
  exact sourceLoopAdd_postcomp _ _ h

theorem sourceHomGroup_comp_add {A B C : SourceCategory.{u}}
    (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  apply sourceLoopFunctor.map_injective
  rw [Functor.map_comp, sourceHomGroup_map_add, sourceHomGroup_map_add,
    Functor.map_comp, Functor.map_comp]
  exact comp_sourceLoopAdd _ _ _ _

end KIP126.StableHomotopy.Implementation.Prespectrum
