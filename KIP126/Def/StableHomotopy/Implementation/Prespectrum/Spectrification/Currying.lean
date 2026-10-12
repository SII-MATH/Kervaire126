module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

/-- Curry the first cubical coordinate into an actual based path. -/
def loopCurryFirst (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin (r+1)) A A.point) :
    GenLoop (Fin r) (loopLevel A) (loopLevel A).point := by
  refine ⟨⟨fun t =>
    { toFun := fun s => p (Fin.cases s t)
      continuous_toFun := p.val.continuous.comp
        (continuous_pi fun i => Fin.cases continuous_id (fun j => continuous_const) i)
      source' := p.property _ ⟨0,Or.inl rfl⟩
      target' := p.property _ ⟨0,Or.inr rfl⟩ }, ?_⟩, ?_⟩
  · apply Path.continuous_uncurry_iff.mp
    exact p.val.continuous.comp (continuous_pi fun i =>
      Fin.cases continuous_snd (fun j => (continuous_apply j).comp continuous_fst) i)
  · rintro t ⟨j,hj⟩
    apply Path.ext
    funext s
    exact p.property _ ⟨j.succ,hj⟩

/-- Currying the first coordinate retains the full relative cubical homotopy. -/
def loopCurryFirstHomotopy (A : BasedSpace.{u}) (r : ℕ)
    {p q : GenLoop (Fin (r+1)) A A.point}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin (r+1)))) :
    (loopCurryFirst A r p).val.HomotopyRel (loopCurryFirst A r q).val
      (Cube.boundary (Fin r)) where
  toFun z :=
    { toFun s := H (z.1,Fin.cases s z.2)
      continuous_toFun := H.continuous.comp
        (continuous_const.prodMk (continuous_pi fun i =>
          Fin.cases continuous_id (fun j => continuous_const) i))
      source' := (H.eq_fst z.1 ⟨0,Or.inl rfl⟩).trans (p.property _ ⟨0,Or.inl rfl⟩)
      target' := (H.eq_fst z.1 ⟨0,Or.inr rfl⟩).trans (p.property _ ⟨0,Or.inr rfl⟩) }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (H.continuous.comp (continuous_fst.fst.prodMk (continuous_pi fun i =>
      Fin.cases continuous_snd (fun j => (continuous_apply j).comp continuous_fst.snd) i)))
  map_zero_left t := by
    apply Path.ext
    funext s
    exact H.apply_zero _
  map_one_left t := by
    apply Path.ext
    funext s
    exact H.apply_one _
  prop' v t ht := by
    obtain ⟨j,hj⟩ := ht
    apply Path.ext
    funext s
    exact H.eq_fst v ⟨j.succ,hj⟩

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem loopCurryFirst_uncurry (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    loopCurryFirst A r (loopUncurryFirst A r p) = p := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  rfl

@[simp] theorem loopUncurryFirst_curry (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin (r+1)) A A.point) :
    loopUncurryFirst A r (loopCurryFirst A r p) = p := by
  apply GenLoop.ext
  intro t
  change p (Fin.cases (t 0) (fun j => t j.succ)) = p t
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end KIP126.StableHomotopy.Implementation.Prespectrum

end
