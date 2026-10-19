module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Slide a source loop towards its endpoint, retaining the image of its
remaining tail in the target. -/
def fiberLoopNullLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(I × (Prespectrum.loop X).level n,(fiber f).level n) := by
  let paths : C((I × (Prespectrum.loop X).level n) × I,Y.level n) :=
    ⟨fun z => f.level n (z.1.2 (Set.Icc.convexComb z.1.1 1 z.2)),by fun_prop⟩
  refine ⟨fun z => ⟨(z.2 z.1,paths.curry z),⟨?_,?_⟩⟩,
    (((continuous_snd).eval continuous_fst).prodMk paths.curry.continuous).subtype_mk _⟩
  · exact congrArg (fun s => f.level n (z.2 s)) (Set.Icc.convexComb_zero z.1 1)
  · exact (congrArg (fun s => f.level n (z.2 s)) (Set.Icc.convexComb_one z.1 1)).trans
      ((congrArg (f.level n) z.2.target).trans (f.point n))

/-- The sliding nullhomotopy is an actual strict map of prespectra. -/
def fiberLoopNullPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Prespectrum.loop X ⟶ pathPrespectrum (fiber f) where
  level n := ((fiberLoopNullLevel f n).comp ⟨Prod.swap,continuous_swap⟩).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro v
      exact f.point n
  bond n p t := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro v
      exact f.bond n _ t

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem fiberLoopNullPath_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberLoopNullPath f ≫ pathEvaluation _ 0 = loopMap f ≫ fiberConnecting f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact p.source
  · apply ContinuousMap.ext
    intro v
    change f.level n (p (Set.Icc.convexComb 0 1 v)) = f.level n (p v)
    congr 2
    ext
    simp [Set.Icc.convexComb]

@[simp] theorem fiberLoopNullPath_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberLoopNullPath f ≫ pathEvaluation _ 1 = zeroMap _ _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact p.target
  · apply ContinuousMap.ext
    intro v
    change f.level n (p (Set.Icc.convexComb 1 1 v)) = (Y.level n).point
    rw [Set.Icc.convexComb_eq,p.target,f.point]

end KIP126.StableHomotopy.Implementation.Prespectrum

end
