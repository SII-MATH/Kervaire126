module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Hom.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum.StrictHomotopy
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual suspension-loop adjunction carries a strict homotopy of
loop-valued maps to a strict homotopy of their suspension adjoints. -/
def suspensionUncurry {X Y : Prespectrum.{u}} {f g : X ⟶ loop Y}
    (H : StrictHomotopy f g) :
    StrictHomotopy (suspensionLoopUncurry f) (suspensionLoopUncurry g) := by
  let a : X ⟶ loop (pathPrespectrum Y) := {
    level n := {
      toFun x := {
        toFun s := ⟨fun t => (show C(I,(loop Y).level n) from H.hom.level n x) t s,
          continuous_eval.comp ((show C(I,(loop Y).level n) from H.hom.level n x).continuous.prodMk
            continuous_const)⟩
        continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
          (continuous_eval.comp
            (((show C(I,(loop Y).level n) from H.hom.level n x).continuous.comp continuous_snd).prodMk
              continuous_fst))
        source' := by apply ContinuousMap.ext; intro t; exact Path.source _
        target' := by apply ContinuousMap.ext; intro t; exact Path.target _ }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact continuous_eval.comp
          ((continuous_eval.comp (((show C(X.level n,C(I,(loop Y).level n)) from H.hom.level n).continuous.comp
            continuous_fst.fst).prodMk continuous_snd)).prodMk continuous_fst.snd) }
    point n := by
      apply Path.ext; funext s
      apply ContinuousMap.ext; intro t
      exact congrArg (fun p : C(I,(loop Y).level n) => p t s) (H.hom.point n)
    bond n x t := by
      apply Path.ext; funext s
      apply ContinuousMap.ext; intro v
      exact congrArg (fun p : C(I,(loop Y).level (n+1)) => p v s) (H.hom.bond n x t) }
  refine { hom := suspensionLoopUncurry a, zero := ?_, one := ?_ }
  · apply Hom.ext; funext n
    apply ContinuousMap.ext; intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,s⟩
    exact congrArg (fun k : X ⟶ loop Y => k.level n x s) H.zero
  · apply Hom.ext; funext n
    apply ContinuousMap.ext; intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,s⟩
    exact congrArg (fun k : X ⟶ loop Y => k.level n x s) H.one

end KIP126.StableHomotopy.Implementation.Prespectrum.StrictHomotopy
