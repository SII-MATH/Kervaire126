module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Surjective.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated

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

/-- Vanishing in the preceding actual stable degree is vanishing of maps
from the specified representing sphere into the actual suspension. -/
theorem sourceSphere_hom_shift_subsingleton (X : SourceCategory.{0}) (d : ℤ)
    [Subsingleton ((sourceStableHomotopyAddFunctor (d-1)).obj X)] :
    Subsingleton (Prespectrum.sourceSphere d ⟶ X⟦(1 : ℤ)⟧) := by
  letI : Subsingleton (X.as.obj.StableHomotopy (d-1)) :=
    inferInstanceAs (Subsingleton ((sourceStableHomotopyAddFunctor (d-1)).obj X))
  letI : Subsingleton (Prespectrum.sourceSphere (d-1) ⟶ X) :=
    (Prespectrum.sourceStableHomotopyEquiv X.as.obj (d-1)).symm.injective.subsingleton
  let F := shiftFunctor SourceCategory (1 : ℤ)
  letI : Subsingleton (F.obj (Prespectrum.sourceSphere (d-1)) ⟶ F.obj X) :=
    (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.injective.subsingleton
  let e : (Prespectrum.sourceSphere (d-1))⟦(1 : ℤ)⟧ ≅ Prespectrum.sourceSphere d :=
    Prespectrum.sourceSphere_succShiftIso (d-1) ≪≫
      eqToIso (congrArg Prespectrum.sourceSphere (by omega))
  exact (Iso.homCongr e.symm (Iso.refl (X⟦(1 : ℤ)⟧))).injective.subsingleton

/-- Each actual Moore cofiber retains the lower homotopy bound of the
original source object. -/
theorem sourceMoorePowerSequence_homotopy_subsingleton (p : ℕ) (X : SourceCategory.{0})
    (N : ℤ) (hX : ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (k : ℕ) (d : ℤ) (hd : d < N) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj ((moorePowerSequence p X).obj k)) := by
  letI : Subsingleton (X.as.obj.StableHomotopy d) := hX d hd
  letI : Subsingleton (Prespectrum.sourceSphere d ⟶ X) :=
    (Prespectrum.sourceStableHomotopyEquiv X.as.obj d).symm.injective.subsingleton
  letI := hX (d-1) (by omega)
  letI := sourceSphere_hom_shift_subsingleton X d
  let Z := (moorePowerSequence p X).obj k
  let T := Triangle.mk (moorePowerMap p X k)
    (HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (HasFunctorialCofiber.cofibδ (moorePowerMap p X k))
  have hz (a : Prespectrum.sourceSphere d ⟶ Z) : a = 0 := by
    obtain ⟨b,hb⟩ := T.coyoneda_exact₃
      (HasFunctorialCofiber.cofib_distinguished (moorePowerMap p X k)) a
      (by exact @Subsingleton.elim (Prespectrum.sourceSphere d ⟶ X⟦(1 : ℤ)⟧) _ _ _)
    change Prespectrum.sourceSphere d ⟶ X at b
    rw [show b = 0 from Subsingleton.elim _ _] at hb
    exact hb.trans Limits.zero_comp
  letI : Subsingleton (Prespectrum.sourceSphere d ⟶ Z) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  let e : (sourceStableHomotopyAddFunctor d).obj Z ≃ (Prespectrum.sourceSphere d ⟶ Z) :=
    Prespectrum.sourceStableHomotopyEquiv Z.as.obj d
  exact e.injective.subsingleton

/-- In the first possible nonzero degree, the actual Moore inclusion is
surjective on the original stable homotopy groups. -/
theorem sourceMoorePowerSequence_inclusion_surjective (p : ℕ) (X : SourceCategory.{0})
    (N : ℤ) (hX : ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (k : ℕ) :
    Function.Surjective ((sourceStableHomotopyAddFunctor N).map
      (HasFunctorialCofiber.cofibι (moorePowerMap p X k))) := by
  letI := hX (N-1) (by omega)
  letI := sourceSphere_hom_shift_subsingleton X N
  let Z := (moorePowerSequence p X).obj k
  let T := Triangle.mk (moorePowerMap p X k)
    (HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (HasFunctorialCofiber.cofibδ (moorePowerMap p X k))
  intro z
  obtain ⟨b,hb⟩ := T.coyoneda_exact₃
    (HasFunctorialCofiber.cofib_distinguished (moorePowerMap p X k))
    (Prespectrum.sourceStableHomotopyEquiv Z.as.obj N z)
    (by exact @Subsingleton.elim (Prespectrum.sourceSphere N ⟶ X⟦(1 : ℤ)⟧) _ _ _)
  change Prespectrum.sourceSphere N ⟶ X at b
  refine ⟨(Prespectrum.sourceStableHomotopyEquiv X.as.obj N).symm b, ?_⟩
  apply (Prespectrum.sourceStableHomotopyEquiv Z.as.obj N).injective
  exact (represented_map (X := X) (Y := Z)
    (HasFunctorialCofiber.cofibι (moorePowerMap p X k)) N
    ((Prespectrum.sourceStableHomotopyEquiv X.as.obj N).symm b)).trans
      ((congrArg (fun a => a ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k))
        ((Prespectrum.sourceStableHomotopyEquiv X.as.obj N).apply_symm_apply b)).trans hb.symm)

/-- The actual tower reductions are surjective at the lower bound; no
finiteness hypothesis is imposed on that stable group. -/
theorem sourceMoorePowerSequence_step_surjective (p : ℕ) (X : SourceCategory.{0})
    (N : ℤ) (hX : ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (k : ℕ) :
    Function.Surjective ((sourceStableHomotopyAddFunctor N).map ((moorePowerSequence p X).step k)) := by
  intro z
  obtain ⟨x,hx⟩ := sourceMoorePowerSequence_inclusion_surjective p X N hX k z
  refine ⟨(sourceStableHomotopyAddFunctor N).map
    (HasFunctorialCofiber.cofibι (moorePowerMap p X (k+1))) x, ?_⟩
  change ((sourceStableHomotopyAddFunctor N).map
    (HasFunctorialCofiber.cofibι (moorePowerMap p X (k+1))) ≫
    (sourceStableHomotopyAddFunctor N).map ((moorePowerSequence p X).step k)) x = z
  rw [← CategoryTheory.Functor.map_comp, moorePowerSequence_inclusion_step]
  exact hx

/-- The actual Moore limit preserves the exact lower homotopy bound,
including the critical degree of the Milnor derived-limit term. -/
theorem sourceMooreCompletion_boundedBelow (p : ℕ) (X : SourceCategory.{0}) (N : ℤ)
    (hX : ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X)) :
    ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (sourceMooreCompletion p X)) :=
  sourceHomotopyLimit_boundedBelow_of_surjective (moorePowerSequence p X) N
    (sourceMoorePowerSequence_homotopy_subsingleton p X N hX)
    (sourceMoorePowerSequence_step_surjective p X N hX)

/-- In particular, the actual Moore completion candidate of the original
sphere is connective, for every scalar. -/
theorem sourceMooreCompletion_sphere_connective (p : ℕ) (d : ℤ) (hd : d < 0) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (sourceMooreCompletion p (sourceLocalization.obj Prespectrum.sphere))) := by
  apply sourceMooreCompletion_boundedBelow p _ 0 _ d hd
  intro i hi
  exact Prespectrum.sphere_stableHomotopy_subsingleton_of_neg i hi

end KIP126.StableHomotopy.Implementation
