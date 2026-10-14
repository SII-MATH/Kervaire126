module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Sphere.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Data
public import Mathlib.CategoryTheory.HomCongr

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

/-- Every compatible family of actual stable classes lifts through the
constructed source Milnor triangle. -/
theorem sourceHomotopyLimitComparison_surjective
    (D : InverseSequence SourceCategory.{0}) (d : ℤ) :
    Function.Surjective (sourceHomotopyLimitComparison D d) := by
  intro a
  let H := sourceHomotopyLimitWitness D
  let e (X : SourceCategory.{0}) := Prespectrum.sourceStableHomotopyEquiv X.as.obj d
  have ha : ∀ k, e (D.obj (k+1)) (a.val (k+1)) ≫ D.step k = e (D.obj k) (a.val k) := by
    intro k
    exact (represented_map (D.step k) d (a.val (k+1))).symm.trans
      (congrArg (e (D.obj k)) (a.property k))
  obtain ⟨b,hb⟩ := H.exists_lift (fun k => e (D.obj k) (a.val k)) ha
  refine ⟨(e (sourceHomotopyLimit D)).symm b, Subtype.ext (funext fun k => ?_)⟩
  apply (e (D.obj k)).injective
  change e (D.obj k) ((sourceStableHomotopyAddFunctor d).map (H.π k)
    ((e (sourceHomotopyLimit D)).symm b)) = e (D.obj k) (a.val k)
  rw [represented_map, Equiv.apply_symm_apply]
  exact hb k

/-- The finite next-degree groups are exactly the represented finiteness
required by the actual Milnor uniqueness argument. -/
theorem sourceSphere_shifted_hom_finite (X : SourceCategory.{0}) (d : ℤ)
    [Finite ((sourceStableHomotopyAddFunctor (d+1)).obj X)] :
    Finite ((Prespectrum.sourceSphere d)⟦(1 : ℤ)⟧ ⟶ X) := by
  letI : Finite (X.as.obj.StableHomotopy (d+1)) :=
    inferInstanceAs (Finite ((sourceStableHomotopyAddFunctor (d+1)).obj X))
  let e := (Iso.homCongr (Prespectrum.sourceSphere_succShiftIso d) (Iso.refl X)).trans
    (Prespectrum.sourceStableHomotopyEquiv X.as.obj (d+1)).symm
  exact Finite.of_injective e e.injective

/-- Finiteness in the next actual degree removes all ambiguity in the
stable classes with prescribed Milnor projections. -/
theorem sourceHomotopyLimitComparison_injective_of_finite
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    [∀ k, Finite ((sourceStableHomotopyAddFunctor (d+1)).obj (D.obj k))] :
    Function.Injective (sourceHomotopyLimitComparison D d) := by
  letI (k : ℕ) : Finite ((Prespectrum.sourceSphere d)⟦(1 : ℤ)⟧ ⟶ D.obj k) :=
    sourceSphere_shifted_hom_finite (D.obj k) d
  intro x y h
  apply (Prespectrum.sourceStableHomotopyEquiv (sourceHomotopyLimit D).as.obj d).injective
  apply (sourceHomotopyLimitWitness D).hom_ext_of_finite
  intro k
  rw [← represented_map, ← represented_map]
  apply congrArg (Prespectrum.sourceStableHomotopyEquiv (D.obj k).as.obj d)
  exact congrArg (fun z : sourceHomotopyCompatible D d => z.val k) h

theorem sourceHomotopyLimitComparison_bijective_of_finite
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    [∀ k, Finite ((sourceStableHomotopyAddFunctor (d+1)).obj (D.obj k))] :
    Function.Bijective (sourceHomotopyLimitComparison D d) :=
  ⟨sourceHomotopyLimitComparison_injective_of_finite D d,
    sourceHomotopyLimitComparison_surjective D d⟩

end KIP126.StableHomotopy.Implementation
