module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Compact.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem evaluation_inclusion_coproductLevelIso {J : Type u}
    (X : J → Prespectrum.{u}) (n : ℕ) (j : J) :
    (evaluationFunctor n).map (Sigma.ι X j) ≫ (coproductLevelIso X n).hom =
      Sigma.ι (fun j => (X j).level n) j :=
  (isColimitOfHasCoproductOfPreservesColimit (evaluationFunctor n) X).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct _) ⟨j⟩

/-- The actual coproduct-level comparison respects inclusion of the
same subfamily, without choosing a new interpretation of its summands. -/
theorem coproductLevelIso_subfamily {J : Type u} (X : J → Prespectrum.{u})
    (n : ℕ) (s : Set J) :
    (evaluationFunctor n).map (coproductSubfamilyMap X s) ≫ (coproductLevelIso X n).hom =
      (coproductLevelIso (fun j : s => X j.val) n).hom ≫
        BasedSpace.coproductSubfamilyMap (fun j => (X j).level n) s := by
  apply (isColimitOfHasCoproductOfPreservesColimit (evaluationFunctor n)
    (fun j : s => X j.val)).hom_ext
  intro j
  change (evaluationFunctor n).map (Sigma.ι (fun j : s => X j.val) j.as) ≫ _ =
    (evaluationFunctor n).map (Sigma.ι (fun j : s => X j.val) j.as) ≫ _
  rw [← Category.assoc,← Functor.map_comp]
  change (evaluationFunctor n).map
    (Sigma.ι (fun j : s => X j.val) j.as ≫ Sigma.desc (fun j : s => Sigma.ι X j.val)) ≫ _ = _
  rw [Sigma.ι_desc,evaluation_inclusion_coproductLevelIso,← Category.assoc,
    evaluation_inclusion_coproductLevelIso]
  exact (Sigma.ι_desc (fun j : s => Sigma.ι (fun j => (X j).level n) j.val) j.as).symm

/-- Each compact-domain map into one level of the actual strict coproduct
factors continuously through finitely many of those same prespectrum
summands. -/
theorem continuousMap_coproduct_level_factor_finite {J : Type u}
    (X : J → Prespectrum.{u}) (n : ℕ) [∀ j, T1Space ((X j).level n)]
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : C(A,(∐ X : Prespectrum.{u}).level n)) :
    ∃ (s : Finset J) (g : C(A,(∐ fun j : (s : Set J) => X j.val : Prespectrum.{u}).level n)),
      ((coproductSubfamilyMap X (s : Set J)).level n).comp g = f := by
  let e := coproductLevelIso X n
  obtain ⟨s,g,hg⟩ := BasedSpace.continuousMap_coproduct_factor_finite
    (fun j => (X j).level n) (e.hom.map.comp f)
  let e' := coproductLevelIso (fun j : (s : Set J) => X j.val) n
  refine ⟨s,e'.inv.map.comp g,?_⟩
  have he := coproductLevelIso_subfamily X n (s : Set J)
  apply ContinuousMap.ext
  intro a
  have h := congrArg (fun k => k.map (e'.inv.map (g a))) he
  have hi : e'.hom.map (e'.inv.map (g a)) = g a :=
    congrArg (fun k => k.map (g a)) e'.inv_hom_id
  have hfac := congrArg (fun k => k a) hg
  change e.hom.map ((coproductSubfamilyMap X (s : Set J)).level n (e'.inv.map (g a))) =
    (BasedSpace.coproductSubfamilyMap (fun j => (X j).level n) (s : Set J)).map
      (e'.hom.map (e'.inv.map (g a))) at h
  rw [hi] at h
  have h' := congrArg e.inv.map (h.trans hfac)
  have heq (z : (∐ X : Prespectrum.{u}).level n) : e.inv.map (e.hom.map z) = z :=
    congrArg (fun k => k.map z) e.hom_inv_id
  simpa only [ContinuousMap.comp_apply,heq] using h'

end KIP126.StableHomotopy.Implementation.Prespectrum
