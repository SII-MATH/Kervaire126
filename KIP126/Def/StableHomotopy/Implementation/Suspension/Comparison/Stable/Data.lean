module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open Topology
open scoped unitInterval Topology.Homotopy

universe u
variable (X : Prespectrum.{u})

/-- Suspend a cubical loop with the orientation prescribed by its stage. -/
def suspensionDesuspensionInverseLoop (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop (Fin (r + 1)) (X.level n).suspension (X.level n).suspension.point := by
  refine ⟨⟨fun t => BasedSpace.suspensionProjection _
    (p (fun i => t i.succ), suspensionDesuspensionSign n (t 0)),
    (BasedSpace.suspensionProjection _).continuous.comp
      ((p.val.continuous.comp (continuous_pi fun i => continuous_apply i.succ)).prodMk
        ((suspensionDesuspensionSign n).continuous.comp (continuous_apply 0)))⟩, ?_⟩
  intro t ht
  apply BasedSpace.suspensionProjection_collapsed
  obtain ⟨i, hi⟩ := ht
  induction i using Fin.cases with
  | zero => exact Or.inr (suspensionDesuspensionSign_boundary n (t 0) hi)
  | succ i => exact Or.inl (p.property _ ⟨i, hi⟩)

/-- The inverse comparison advances the stage and suspends the displayed
loop, rather than selecting an abstract inverse on homotopy sets. -/
def Representative.suspensionDesuspensionInverse {d : ℤ} (a : Representative X d) :
    Representative (desuspension X).suspension d where
  stage := a.stage + 1
  dimension := a.dimension + 1
  degree := by have := a.degree; omega
  loop := suspensionDesuspensionInverseLoop X a.stage a.dimension a.loop

end KIP126.StableHomotopy.Implementation.Prespectrum
