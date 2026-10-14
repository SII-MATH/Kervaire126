module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {A B : Prespectrum.{u}} (p : A ⟶ B)
  (L : fiber p ⟶ pathPrespectrum A)
  (hp : ∀ s : I, L ≫ pathEvaluation A s ≫ p = fiberNullPath p ≫ pathEvaluation B s)

/-- Move along the actual lifted path and retain its remaining tail. -/
def strictFiberTailFamily (n : ℕ) : C(fiberLevel p n × I,fiberLevel p n) := by
  let paths : C((fiberLevel p n × I) × I,B.level n) :=
    ⟨fun z => z.1.1.val.2 (Set.Icc.convexComb z.1.2 1 z.2),
      continuous_fst.fst.subtype_val.snd.eval (by fun_prop)⟩
  refine ⟨fun z => ⟨((L.level n z.1 : C(I,A.level n)).toFun z.2,paths.curry z),⟨?_,?_⟩⟩,?_⟩
  · change z.1.val.2 (Set.Icc.convexComb z.2 1 0) =
      p.level n ((L.level n z.1 : C(I,A.level n)).toFun z.2)
    rw [Set.Icc.convexComb_zero]
    exact (congrArg (fun k : fiber p ⟶ B => k.level n z.1) (hp z.2)).symm
  · change z.1.val.2 (Set.Icc.convexComb z.2 1 1) = (B.level n).point
    rw [Set.Icc.convexComb_one]
    exact z.1.property.2
  · exact (((show C(fiberLevel p n,C(I,A.level n)) from L.level n).continuous.comp
      continuous_fst).eval continuous_snd |>.prodMk paths.curry.continuous).subtype_mk _

/-- The tail construction is a genuine strict homotopy on the path fiber. -/
def strictFiberTailHomotopy : fiber p ⟶ pathPrespectrum (fiber p) where
  level n := (strictFiberTailFamily p L hp n).curry
  point n := by
    apply ContinuousMap.ext; intro s
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q : C(I,A.level n) => q s) (L.point n)
    · rfl
  bond n z t := by
    apply ContinuousMap.ext; intro s
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q : C(I,A.level (n+1)) => q s) (L.bond n z t)
    · rfl

/-- Restrict the actual lifted paths to the strict fiber. -/
def strictFiberKernelFamily (n : ℕ) : C((strictFiber p).level n × I,(strictFiber p).level n) := by
  refine ⟨fun z => ⟨((L.level n ((strictFiberInclusion p).level n z.1) : C(I,A.level n)).toFun z.2,
    z.1.val.2),?_⟩,?_⟩
  · exact congrArg (fun k : fiber p ⟶ B => k.level n ((strictFiberInclusion p).level n z.1))
      (hp z.2)
  · exact ((((show C((strictFiber p).level n,C(I,A.level n)) from
      ((strictFiberInclusion p) ≫ L).level n).continuous.comp continuous_fst).eval
        continuous_snd).prodMk continuous_fst.subtype_val.snd).subtype_mk _

/-- On the strict fiber the same actual lifted path stays in the strict
fiber because its projected path is constant, without regularity assumptions. -/
def strictFiberKernelHomotopy : strictFiber p ⟶ pathPrespectrum (strictFiber p) where
  level n := (strictFiberKernelFamily p L hp n).curry
  point n := by
    apply ContinuousMap.ext; intro s
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q : C(I,A.level n) => q s) (((strictFiberInclusion p) ≫ L).point n)
    · rfl
  bond n z t := by
    apply ContinuousMap.ext; intro s
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q : C(I,A.level (n+1)) => q s) (((strictFiberInclusion p) ≫ L).bond n z t)
    · rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
