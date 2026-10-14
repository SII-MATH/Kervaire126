module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Connectivity.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Proofs

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

/-- A surjection on the actual next-degree stable classes is precisely
what is needed for maps from the shifted representing sphere. -/
theorem sourceSphere_shifted_postcomp_surjective
    {X Y : SourceCategory.{0}} (f : X ⟶ Y) (d : ℤ)
    (hf : Function.Surjective ((sourceStableHomotopyAddFunctor (d+1)).map f)) :
    Function.Surjective (fun a : (Prespectrum.sourceSphere d)⟦(1 : ℤ)⟧ ⟶ X => a ≫ f) := by
  intro b
  let e := Prespectrum.sourceSphere_succShiftIso d
  let eX := Prespectrum.sourceStableHomotopyEquiv X.as.obj (d+1)
  let eY := Prespectrum.sourceStableHomotopyEquiv Y.as.obj (d+1)
  obtain ⟨x,hx⟩ := hf (eY.symm (e.inv ≫ b))
  refine ⟨e.hom ≫ eX x, ?_⟩
  calc
    (e.hom ≫ eX x) ≫ f = e.hom ≫ (eX x ≫ f) := Category.assoc _ _ _
    _ = e.hom ≫ eY ((sourceStableHomotopyAddFunctor (d+1)).map f x) :=
      congrArg (fun q => e.hom ≫ q) (represented_map f (d+1) x).symm
    _ = e.hom ≫ (e.inv ≫ b) := congrArg (fun q => e.hom ≫ q)
      ((congrArg eY hx).trans (eY.apply_symm_apply (e.inv ≫ b)))
    _ = b := e.hom_inv_id_assoc b

/-- Surjective next-degree transitions eliminate the actual Milnor
ambiguity, without any finiteness requirement. -/
theorem sourceHomotopyLimitComparison_injective_of_surjective
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    (hD : ∀ k, Function.Surjective ((sourceStableHomotopyAddFunctor (d+1)).map (D.step k))) :
    Function.Injective (sourceHomotopyLimitComparison D d) := by
  intro x y h
  apply (Prespectrum.sourceStableHomotopyEquiv (sourceHomotopyLimit D).as.obj d).injective
  apply (sourceHomotopyLimitWitness D).hom_ext_of_surjective
    (D.postcomp_oneSubShift_surjective_of_surjective _
      (fun k => sourceSphere_shifted_postcomp_surjective (D.step k) d (hD k)))
  intro k
  rw [← represented_map, ← represented_map]
  apply congrArg (Prespectrum.sourceStableHomotopyEquiv (D.obj k).as.obj d)
  exact congrArg (fun z : sourceHomotopyCompatible D d => z.val k) h

theorem sourceHomotopyLimitComparison_bijective_of_surjective
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    (hD : ∀ k, Function.Surjective ((sourceStableHomotopyAddFunctor (d+1)).map (D.step k))) :
    Function.Bijective (sourceHomotopyLimitComparison D d) :=
  ⟨sourceHomotopyLimitComparison_injective_of_surjective D d hD,
    sourceHomotopyLimitComparison_surjective D d⟩

/-- Actual vanishing at the stages and surjectivity in the next degree
imply vanishing at the constructed homotopy limit. -/
theorem sourceHomotopyLimit_homotopy_subsingleton_of_surjective
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    [∀ k, Subsingleton ((sourceStableHomotopyAddFunctor d).obj (D.obj k))]
    (hD : ∀ k, Function.Surjective ((sourceStableHomotopyAddFunctor (d+1)).map (D.step k))) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceHomotopyLimit D)) :=
  (sourceHomotopyLimitComparison_injective_of_surjective D d hD).subsingleton

/-- A uniform lower bound is retained by the actual Milnor limit if only
the transition maps at the boundary degree are surjective. -/
theorem sourceHomotopyLimit_boundedBelow_of_surjective
    (D : InverseSequence SourceCategory.{0}) (N : ℤ)
    (hD : ∀ k d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (D.obj k)))
    (hN : ∀ k, Function.Surjective ((sourceStableHomotopyAddFunctor N).map (D.step k))) :
    ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceHomotopyLimit D)) := by
  intro d hd
  letI (k : ℕ) := hD k d hd
  apply sourceHomotopyLimit_homotopy_subsingleton_of_surjective D d
  intro k
  by_cases h : d+1 < N
  · letI := hD k (d+1) h
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · have he : d+1 = N := by omega
    subst N
    exact hN k

end KIP126.StableHomotopy.Implementation
