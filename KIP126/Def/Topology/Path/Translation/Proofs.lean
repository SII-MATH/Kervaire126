module

public import KIP126.Def.Topology.Path.Translation.Data

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

variable {X : Type u} [TopologicalSpace X] {a : X}

/-- Actual associativity gives a homotopy between composed translations
and translation by the concatenation. -/
theorem loopLeftTranslate_comp_homotopic (p q : Path a a) :
    ((loopLeftTranslate p).comp (loopLeftTranslate q)).Homotopic (loopLeftTranslate (p.trans q)) := by
  refine ⟨{
    toFun z := (Path.Homotopy.transAssoc p q z.2).eval (unitInterval.symm z.1)
    continuous_toFun := ?_
    map_zero_left := fun r => by
      rw [unitInterval.symm_zero]
      exact (Path.Homotopy.transAssoc p q r).eval_one
    map_one_left := fun r => by
      rw [unitInterval.symm_one]
      exact (Path.Homotopy.transAssoc p q r).eval_zero }⟩
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : (I × Path a a) × I => (p.trans (q.trans z.1.2)) _)
  fun_prop

/-- A path homotopy gives a jointly continuous homotopy of its left
translations on all loops. -/
theorem loopLeftTranslate_homotopic {p q : Path a a} (H : p.Homotopy q) :
    (loopLeftTranslate p).Homotopic (loopLeftTranslate q) := by
  have hH : Continuous (fun t : I => H.eval t) := by
    apply Path.continuous_uncurry_iff.mp
    exact H.continuous
  exact ⟨{
    toFun z := (H.eval z.1).trans z.2
    continuous_toFun := Path.continuous_trans.comp ((hH.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := fun p => by rw [H.eval_zero]; rfl
    map_one_left := fun p => by rw [H.eval_one]; rfl }⟩

theorem loopLeftTranslate_refl_homotopic :
    (loopLeftTranslate (Path.refl a)).Homotopic (ContinuousMap.id (Path a a)) :=
  ⟨{
    toFun z := Path.delayReflLeft z.1 z.2
    continuous_toFun := Path.continuous_delayReflLeft
    map_zero_left := Path.delayReflLeft_zero
    map_one_left := Path.delayReflLeft_one }⟩

/-- The original reversed loop supplies a genuine homotopy inverse to
left translation; this concerns every component of the loop space. -/
theorem loopLeftTranslate_symm_comp_homotopic (p : Path a a) :
    ((loopLeftTranslate p.symm).comp (loopLeftTranslate p)).Homotopic
      (ContinuousMap.id (Path a a)) :=
  (loopLeftTranslate_comp_homotopic p.symm p).trans
    ((loopLeftTranslate_homotopic (Path.Homotopy.reflSymmTrans p).symm).trans
      loopLeftTranslate_refl_homotopic)

theorem loopLeftTranslate_comp_symm_homotopic (p : Path a a) :
    ((loopLeftTranslate p).comp (loopLeftTranslate p.symm)).Homotopic
      (ContinuousMap.id (Path a a)) :=
  (loopLeftTranslate_comp_homotopic p p.symm).trans
    ((loopLeftTranslate_homotopic (Path.Homotopy.reflTransSymm p).symm).trans
      loopLeftTranslate_refl_homotopic)

/-- Translation commutes exactly with applying a continuous map to loops. -/
theorem continuousLoopMap_translate {Y : Type v} [TopologicalSpace Y]
    (f : C(X,Y)) (p : Path a a) :
    (continuousLoopMap f a).comp (loopLeftTranslate p) =
      (loopLeftTranslate (p.map f.continuous)).comp (continuousLoopMap f a) := by
  apply ContinuousMap.ext
  intro q
  exact Path.map_trans p q f.continuous

end KIP126.Topology
