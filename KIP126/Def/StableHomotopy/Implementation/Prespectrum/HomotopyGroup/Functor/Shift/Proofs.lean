module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Shift.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

private theorem represented_map {X Y : SourceCategory.{0}} (f : X ⟶ Y) (d : ℤ)
    (x : (sourceStableHomotopyAddFunctor d).obj X) :
    Prespectrum.sourceStableHomotopyEquiv Y.as.obj d
        ((sourceStableHomotopyAddFunctor d).map f x) =
      Prespectrum.sourceStableHomotopyEquiv X.as.obj d x ≫ f := by
  change Prespectrum.sourceStableHomotopyEquiv Y.as.obj d
      ((forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor d).map f) x) = _
  rw [sourceStableHomotopyAddFunctor_forget_map]
  exact Prespectrum.sourceStableHomotopyEquiv_natural f d x

/-- The actual integer suspension comparison retains every original map. -/
theorem sourceStableHomotopyShiftEquiv_natural {X Y : SourceCategory.{0}} (f : X ⟶ Y)
    (d k : ℤ) (x : (sourceStableHomotopyAddFunctor (d-k)).obj X) :
    sourceStableHomotopyShiftEquiv Y d k ((sourceStableHomotopyAddFunctor (d-k)).map f x) =
      (sourceStableHomotopyAddFunctor d).map (f⟦k⟧') (sourceStableHomotopyShiftEquiv X d k x) := by
  apply (Prespectrum.sourceStableHomotopyEquiv (Y⟦k⟧).as.obj d).injective
  rw [represented_map]
  simp only [sourceStableHomotopyShiftEquiv, Equiv.trans_apply]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  erw [represented_map]
  change _ ≫ (shiftFunctor SourceCategory k).map (_ ≫ f) ≫ 𝟙 _ =
    (_ ≫ (shiftFunctor SourceCategory k).map _ ≫ 𝟙 _) ≫ (shiftFunctor SourceCategory k).map f
  simp only [Functor.map_comp, Category.comp_id, Category.assoc]
  rfl

/-- Surjectivity in the original degree transports through an actual integer shift. -/
theorem sourceStableHomotopy_map_shift_surjective {X Y : SourceCategory.{0}} (f : X ⟶ Y)
    (d k : ℤ) (hf : Function.Surjective ((sourceStableHomotopyAddFunctor (d-k)).map f)) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map (f⟦k⟧')) := by
  intro y
  obtain ⟨x,hx⟩ := hf ((sourceStableHomotopyShiftEquiv Y d k).symm y)
  refine ⟨sourceStableHomotopyShiftEquiv X d k x, ?_⟩
  rw [← sourceStableHomotopyShiftEquiv_natural, hx, Equiv.apply_symm_apply]

/-- Injectivity in the original degree transports through an actual integer shift. -/
theorem sourceStableHomotopy_map_shift_injective {X Y : SourceCategory.{0}} (f : X ⟶ Y)
    (d k : ℤ) (hf : Function.Injective ((sourceStableHomotopyAddFunctor (d-k)).map f)) :
    Function.Injective ((sourceStableHomotopyAddFunctor d).map (f⟦k⟧')) := by
  intro x y h
  obtain ⟨a,rfl⟩ := (sourceStableHomotopyShiftEquiv X d k).surjective x
  obtain ⟨b,rfl⟩ := (sourceStableHomotopyShiftEquiv X d k).surjective y
  rw [← sourceStableHomotopyShiftEquiv_natural, ← sourceStableHomotopyShiftEquiv_natural] at h
  exact congrArg _ (hf ((sourceStableHomotopyShiftEquiv Y d k).injective h))

end KIP126.StableHomotopy.Implementation
