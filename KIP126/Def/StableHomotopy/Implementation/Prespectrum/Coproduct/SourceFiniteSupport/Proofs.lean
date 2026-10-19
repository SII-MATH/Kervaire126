module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Derived.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.FiniteSupport.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Stable homotopy classes in the actual source coproduct come from
finite subfamilies, via the original source coproduct inclusions. -/
theorem sourceStableHomotopy_coproduct_finite_support {J : Type u}
    (X : J → SourceCategory.{u}) (d : ℤ)
    (a : (sourceStableHomotopyAddFunctor d).obj (∐ X)) :
    ∃ (s : Finset J)
      (b : (sourceStableHomotopyAddFunctor d).obj (∐ fun j : (s : Set J) => X j.val)),
      (sourceStableHomotopyAddFunctor d).map
        (Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val)) b = a := by
  classical
  let F := sourceStableHomotopyAddFunctor d
  let Q (j : J) := cubicalReplacementFunctor.obj (X j).as.obj
  let e := (sourceDerivedSigmaCofan_isColimit X).coconePointUniqueUpToIso
    (coproductIsCoproduct X)
  obtain ⟨s,b,hb⟩ := stableHomotopy_coproduct_finite_support Q d (F.map e.inv a)
  let Y (j : (s : Set J)) := X j.val
  let e' := (sourceDerivedSigmaCofan_isColimit Y).coconePointUniqueUpToIso
    (coproductIsCoproduct Y)
  refine ⟨s,F.map e'.hom b,?_⟩
  have h : e'.hom ≫ Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val) =
      sourceLocalization.map (coproductSubfamilyMap Q (s : Set J)) ≫ e.hom := by
    apply (sourceDerivedSigmaCofan_isColimit Y).hom_ext
    rintro ⟨j⟩
    have he' : (sourceDerivedSigmaCofan Y).inj j ≫ e'.hom = Sigma.ι Y j :=
      (sourceDerivedSigmaCofan_isColimit Y).fac _ ⟨j⟩
    have he : (sourceDerivedSigmaCofan X).inj j.val ≫ e.hom = Sigma.ι X j.val :=
      (sourceDerivedSigmaCofan_isColimit X).fac _ ⟨j.val⟩
    change (sourceDerivedSigmaCofan Y).inj j ≫ (e'.hom ≫ _) =
      (sourceDerivedSigmaCofan Y).inj j ≫ _
    rw [← Category.assoc, he', Sigma.ι_desc]
    letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app (Y j).as.obj)
      (cubicalReplacementComparison_stableEquivalence (Y j).as.obj)
    apply (cancel_epi (sourceLocalization.map (cubicalReplacementComparison.app (Y j).as.obj))).mp
    rw [sourceDerivedSigmaCofan_inclusion_comparison_assoc,
      ← Category.assoc, ← sourceLocalization.map_comp]
    simp only [coproductSubfamilyMap, Sigma.ι_desc]
    rw [← sourceDerivedSigmaCofan_inclusion_comparison X j.val, Category.assoc, he]
  change (F.map e'.hom ≫ F.map _) b = a
  rw [← F.map_comp, h, F.map_comp]
  change F.map e.hom ((sourceStableHomotopyAddFunctor d).map
    (sourceLocalization.map (coproductSubfamilyMap Q (s : Set J))) b) = a
  rw [sourceStableHomotopyAddFunctor_map]
  change F.map e.hom (stableHomotopyMap (coproductSubfamilyMap Q (s : Set J)) d b) = a
  rw [hb]
  change (F.map e.inv ≫ F.map e.hom) a = a
  simp only [← F.map_comp, Iso.inv_hom_id, F.map_id]
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
