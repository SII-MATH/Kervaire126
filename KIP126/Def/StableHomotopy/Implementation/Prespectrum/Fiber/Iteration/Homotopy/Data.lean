module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Reverse the retained source path, apply f, and concatenate with the
retained target path to obtain an actual based target loop. -/
noncomputable def fiberIterationRetraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (fiberProjection f) ⟶ Prespectrum.loop Y where
  level n :=
    { toFun z :=
        { toContinuousMap := (fiberIterationMoveFamily f n).curry (1,z)
          source' := (fiberIterationMovePath f n (1,z)).source.trans
            ((congrArg (f.level n) z.property.2).trans (f.point n))
          target' := (fiberIterationMovePath f n (1,z)).target }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        ((fiberIterationMoveFamily f n).continuous.comp
          ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)) }
  point n := by
    apply Path.ext
    funext v
    exact fiberIterationMoveFamily_point f n 1 v
  bond n z t := by
    apply Path.ext
    funext v
    exact fiberIterationMoveFamily_bond f n z t 1 v

/-- Move the source to the end of its retained null-path, retaining the
remaining tail as the new second null-path. -/
noncomputable def fiberIterationMoveLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(I × (fiber (fiberProjection f)).level n,(fiber (fiberProjection f)).level n) := by
  let first : C(I × (fiber (fiberProjection f)).level n,(fiber f).level n) :=
    ⟨fun z => ⟨(z.2.val.2 z.1,(fiberIterationMoveFamily f n).curry z),
      ⟨(fiberIterationMovePath f n z).source,(fiberIterationMovePath f n z).target⟩⟩,
      (((continuous_snd.subtype_val.snd).eval continuous_fst).prodMk
        (fiberIterationMoveFamily f n).curry.continuous).subtype_mk _⟩
  let tail : C((I × (fiber (fiberProjection f)).level n) × I,X.level n) :=
    ⟨fun z => z.1.2.val.2 (Set.Icc.convexComb z.1.1 1 z.2),by fun_prop⟩
  refine ⟨fun z => ⟨(first z,tail.curry z),⟨?_,?_⟩⟩,
    (first.continuous.prodMk tail.curry.continuous).subtype_mk _⟩
  · exact congrArg z.2.val.2 (Set.Icc.convexComb_zero z.1 1)
  · exact (congrArg z.2.val.2 (Set.Icc.convexComb_one z.1 1)).trans z.2.property.2

/-- The moved family is based and commutes strictly with every bond. -/
noncomputable def fiberIterationMoveHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (fiberProjection f) ⟶ pathPrespectrum (fiber (fiberProjection f)) where
  level n := ((fiberIterationMoveLevel f n).comp ⟨Prod.swap,continuous_swap⟩).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro v
        exact fiberIterationMoveFamily_point f n s v
    · rfl
  bond n z t := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro v
        exact fiberIterationMoveFamily_bond f n z t s v
    · rfl

/-- Continuously remove the constant prefix from the first retained path,
leaving the source and its entire null-path unchanged. -/
noncomputable def fiberIterationPaddingLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(I × (fiber (fiberProjection f)).level n,(fiber (fiberProjection f)).level n) := by
  let paths : C((I × (fiber (fiberProjection f)).level n) × I,Y.level n) :=
    ⟨fun z => Path.delayReflLeft z.1.1 (fiberCarriedPath f n z.1.2.val.1) z.2,by
      change Continuous (fun z : (I × (fiber (fiberProjection f)).level n) × I =>
        z.1.2.val.1.val.2 _)
      fun_prop⟩
  let first : C(I × (fiber (fiberProjection f)).level n,(fiber f).level n) :=
    ⟨fun z => ⟨(z.2.val.1.val.1,paths.curry z),
      ⟨(Path.delayReflLeft z.1 (fiberCarriedPath f n z.2.val.1)).source,
        (Path.delayReflLeft z.1 (fiberCarriedPath f n z.2.val.1)).target⟩⟩,
      (continuous_snd.subtype_val.fst.subtype_val.fst.prodMk paths.curry.continuous).subtype_mk _⟩
  exact ⟨fun z => ⟨(first z,z.2.val.2),z.2.property⟩,
    (first.continuous.prodMk continuous_snd.subtype_val.snd).subtype_mk _⟩

/-- Padding removal is an actual strict prespectrum homotopy. -/
noncomputable def fiberIterationPaddingHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (fiberProjection f) ⟶ pathPrespectrum (fiber (fiberProjection f)) where
  level n := ((fiberIterationPaddingLevel f n).comp ⟨Prod.swap,continuous_swap⟩).curry
  point _ := by
    apply ContinuousMap.ext
    intro s
    rfl
  bond _ _ _ := by
    apply ContinuousMap.ext
    intro s
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
