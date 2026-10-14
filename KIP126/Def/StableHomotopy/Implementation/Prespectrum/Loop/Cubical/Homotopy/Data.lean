module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Cubical.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
open scoped unitInterval
universe u

/-- Last-coordinate uncurrying transports actual relative cubical homotopies. -/
def loopUncurryLastHomotopy (A : BasedSpace.{u}) (r : ℕ)
    {p q : GenLoop (Fin r) (loopLevel A) (loopLevel A).point}
    (H : ContinuousMap.HomotopyRel p.val q.val (Cube.boundary (Fin r))) :
    ContinuousMap.HomotopyRel (loopUncurryLast A r p).val (loopUncurryLast A r q).val
      (Cube.boundary (Fin (r+1))) where
  toFun z := H (z.1,fun i => z.2 i.castSucc) (z.2 (Fin.last r))
  continuous_toFun := continuous_eval.comp
    ((H.continuous.comp (continuous_fst.prodMk
      (continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_snd))).prodMk
        ((continuous_apply (Fin.last r)).comp continuous_snd))
  map_zero_left t := congrArg (fun a : Path A.point A.point => a (t (Fin.last r))) (H.apply_zero _)
  map_one_left t := congrArg (fun a : Path A.point A.point => a (t (Fin.last r))) (H.apply_one _)
  prop' s t ht := by
    change H (s,fun i => t i.castSucc) (t (Fin.last r)) = loopUncurryLast A r p t
    refine Eq.trans ?_ ((loopUncurryLast A r p).property t ht).symm
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.lastCases with
    | last => rcases hi with h | h <;> simp only [h,Path.source,Path.target]
    | cast j =>
      exact congrArg (fun a : Path A.point A.point => a (t (Fin.last r)))
        ((H.eq_fst s ⟨j,hi⟩).trans (p.property _ ⟨j,hi⟩))

/-- Last-coordinate currying transports actual relative cubical homotopies. -/
def loopCurryLastHomotopy (A : BasedSpace.{u}) (r : ℕ)
    {p q : GenLoop (Fin (r+1)) A A.point}
    (H : ContinuousMap.HomotopyRel p.val q.val (Cube.boundary (Fin (r+1)))) :
    ContinuousMap.HomotopyRel (loopCurryLast A r p).val (loopCurryLast A r q).val
      (Cube.boundary (Fin r)) where
  toFun z :=
    { toFun s := H (z.1,Fin.snoc z.2 s)
      continuous_toFun := H.continuous.comp
        (continuous_const.prodMk ((continuous_cube_snoc r).comp
          (continuous_const.prodMk continuous_id)))
      source' := (H.eq_fst z.1 ⟨Fin.last r,Or.inl (Fin.snoc_last _ _)⟩).trans
        (p.property _ ⟨Fin.last r,Or.inl (Fin.snoc_last _ _)⟩)
      target' := (H.eq_fst z.1 ⟨Fin.last r,Or.inr (Fin.snoc_last _ _)⟩).trans
        (p.property _ ⟨Fin.last r,Or.inr (Fin.snoc_last _ _)⟩) }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (H.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_cube_snoc r).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))
  map_zero_left t := by
    apply Path.ext
    funext s
    exact H.apply_zero (Fin.snoc t s)
  map_one_left t := by
    apply Path.ext
    funext s
    exact H.apply_one (Fin.snoc t s)
  prop' s t ht := by
    apply Path.ext
    funext z
    obtain ⟨i,hi⟩ := ht
    exact H.eq_fst s ⟨i.castSucc,by simpa only [Fin.snoc_castSucc] using hi⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
