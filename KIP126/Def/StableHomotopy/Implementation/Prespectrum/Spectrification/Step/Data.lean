module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- One actual spectrification step. Its bonds first evaluate a loop and
then apply the next adjoint bond, so the adjoint bonds define a strict unit. -/
def spectrificationStep (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := loopLevel (X.level (n+1))
  bond n :=
    { toFun z :=
        { toFun s := X.bond (n+1) (z.1 z.2, s)
          continuous_toFun := (X.bond (n+1)).continuous.comp
            (continuous_const.prodMk continuous_id)
          source' := X.bond_zero (n+1) _
          target' := X.bond_one (n+1) _ }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        ((X.bond (n+1)).continuous.comp
          ((continuous_eval.comp continuous_fst).prodMk continuous_snd)) }
  bond_point n t := by
    apply Path.ext
    funext s
    exact X.bond_point (n+1) s
  bond_zero n p := by
    apply Path.ext
    funext s
    change X.bond (n+1) (p 0, s) = _
    rw [Path.source, X.bond_point]
    rfl
  bond_one n p := by
    apply Path.ext
    funext s
    change X.bond (n+1) (p 1, s) = _
    rw [Path.target, X.bond_point]
    rfl

/-- Apply an actual strict prespectrum map to the shifted loop levels. -/
def spectrificationStepMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    spectrificationStep X ⟶ spectrificationStep Y where
  level n := (loopMap f).level (n+1)
  point n := (loopMap f).point (n+1)
  bond n p t := by
    change Path (X.level (n+1)).point (X.level (n+1)).point at p
    apply Path.ext
    funext s
    exact f.bond (n+1) (p t) s

/-- The actual spectrification step is a functor of strict prespectra. -/
def spectrificationStepFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj := spectrificationStep
  map := spectrificationStepMap
  map_id X := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro p
    apply Path.ext
    rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro p
    apply Path.ext
    rfl

/-- The original adjoint bonds form a genuine strict map into the step. -/
def spectrificationStepUnit (X : Prespectrum.{u}) : X ⟶ spectrificationStep X where
  level n :=
    { toFun x :=
        { toFun t := X.bond n (x, t)
          continuous_toFun := (X.bond n).continuous.comp
            (continuous_const.prodMk continuous_id)
          source' := X.bond_zero n x
          target' := X.bond_one n x }
      continuous_toFun := Path.continuous_uncurry_iff.mp (X.bond n).continuous }
  point n := by
    apply Path.ext
    funext t
    exact X.bond_point n t
  bond n x t := by
    apply Path.ext
    rfl

/-- First-coordinate uncurrying matches the actual spectrification-step bonds. -/
def loopUncurryFirst (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    GenLoop (Fin (r+1)) A A.point := by
  refine ⟨⟨fun t => p (fun i => t i.succ) (t 0), ?_⟩, ?_⟩
  · exact continuous_eval.comp ((p.val.continuous.comp
      (continuous_pi fun i => continuous_apply i.succ)).prodMk (continuous_apply 0))
  · rintro t ⟨i, hi⟩
    change p (fun j => t j.succ) (t 0) = A.point
    induction i using Fin.cases with
    | zero => rcases hi with h | h <;> simp only [h, Path.source, Path.target]
    | succ j =>
        exact congrArg (fun q : Path A.point A.point => q (t 0))
          (p.property (fun i => t i.succ) ⟨j, hi⟩)

/-- First-coordinate uncurrying preserves the actual relative cubical homotopy. -/
def loopUncurryFirstHomotopy (A : BasedSpace.{u}) (r : ℕ)
    {p q : GenLoop (Fin r) (loopLevel A) (loopLevel A).point}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin r))) :
    (loopUncurryFirst A r p).val.HomotopyRel (loopUncurryFirst A r q).val
      (Cube.boundary (Fin (r+1))) where
  toFun z := H (z.1, fun i => z.2 i.succ) (z.2 0)
  continuous_toFun := continuous_eval.comp
    ((H.continuous.comp (continuous_fst.prodMk
      (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
        ((continuous_apply 0).comp continuous_snd))
  map_zero_left t := congrArg (fun a : Path A.point A.point => a (t 0)) (H.apply_zero _)
  map_one_left t := congrArg (fun a : Path A.point A.point => a (t 0)) (H.apply_one _)
  prop' s t ht := by
    change H (s, fun i => t i.succ) (t 0) = loopUncurryFirst A r p t
    refine Eq.trans ?_ ((loopUncurryFirst A r p).property t ht).symm
    obtain ⟨i, hi⟩ := ht
    induction i using Fin.cases with
    | zero => rcases hi with h | h <;> simp only [h, Path.source, Path.target]
    | succ j =>
        exact congrArg (fun a : Path A.point A.point => a (t 0))
          ((H.eq_fst s ⟨j, hi⟩).trans (p.property _ ⟨j, hi⟩))

/-- A step representative uncurries into the original prespectrum one level later. -/
def Representative.fromSpectrificationStep {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (spectrificationStep X) d) : Representative X d where
  stage := a.stage + 1
  dimension := a.dimension + 1
  degree := by have := a.degree; omega
  loop := loopUncurryFirst (X.level (a.stage+1)) a.dimension a.loop

end KIP126.StableHomotopy.Implementation.Prespectrum
