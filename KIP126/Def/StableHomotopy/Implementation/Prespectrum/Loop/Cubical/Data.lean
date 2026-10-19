module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Cube.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Uncurry the loop parameter as the last coordinate. Stabilization adds
its coordinate at the front, so the two operations commute strictly. -/
def loopUncurryLast (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    GenLoop (Fin (r+1)) A A.point := by
  refine ⟨⟨fun t => p (fun i => t i.castSucc) (t (Fin.last r)), ?_⟩, ?_⟩
  · exact continuous_eval.comp ((p.val.continuous.comp
      (continuous_pi fun i => continuous_apply i.castSucc)).prodMk (continuous_apply (Fin.last r)))
  · rintro t ⟨i,hi⟩
    change p (fun j => t j.castSucc) (t (Fin.last r)) = A.point
    induction i using Fin.lastCases with
    | last => rcases hi with h | h <;> simp only [h,Path.source,Path.target]
    | cast j =>
      exact congrArg (fun q : Path A.point A.point => q (t (Fin.last r)))
        (p.property (fun i => t i.castSucc) ⟨j,hi⟩)

/-- Curry the last coordinate into the actual based loop space. -/
def loopCurryLast (A : BasedSpace.{u}) (r : ℕ) (p : GenLoop (Fin (r+1)) A A.point) :
    GenLoop (Fin r) (loopLevel A) (loopLevel A).point := by
  let f (t : Fin r → I) : Path A.point A.point :=
    { toFun s := p (Fin.snoc t s)
      continuous_toFun := p.val.continuous.comp
        ((continuous_cube_snoc r).comp (continuous_const.prodMk continuous_id))
      source' := p.property _ ⟨Fin.last r,Or.inl (Fin.snoc_last _ _)⟩
      target' := p.property _ ⟨Fin.last r,Or.inr (Fin.snoc_last _ _)⟩ }
  refine ⟨⟨f,Path.continuous_uncurry_iff.mp
    (p.val.continuous.comp (continuous_cube_snoc r))⟩,?_⟩
  rintro t ⟨i,hi⟩
  apply Path.ext
  funext s
  apply p.property
  exact ⟨i.castSucc,by simpa only [Fin.snoc_castSucc] using hi⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
