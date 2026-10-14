module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.Shift
public import KIP126.Def.Topology.SimplicialRealization.Product.Weak.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Opposite Simplicial
open HF2Bond
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The actual pair simplicial set of coefficient simplices. -/
noncomputable abbrev pairSet (n : ℕ) : SSet.{0} :=
  hf2SimplicialSet n ⊗ hf2SimplicialSet n

/-- Its realization with the specified pair of zero vertices. -/
noncomputable def pairLevel (n : ℕ) : BasedSpace.{0} where
  space := |pairSet n|
  point := realizeSimplex (pairSet n)
    ((0 : (hf2SimplicialModule n).obj (op ⦋0⦌)),
      (0 : (hf2SimplicialModule n).obj (op ⦋0⦌))) default

/-- The original coefficient-to-decalage map in both coordinates. -/
noncomputable def pairConeMap (n : ℕ) : pairSet n ⟶ decalage (pairSet (n+1)) :=
  (coefficientToLoopSet n ≫ loopSetInclusion n) ⊗ₘ
    (coefficientToLoopSet n ≫ loopSetInclusion n)

/-- The actual cone evaluation bond on the realized simplicial pair. -/
noncomputable def pairBond (n : ℕ) : C(pairLevel n × I,pairLevel (n+1)) :=
  (coneEvaluation (pairSet (n+1))).comp
    (((SSet.toTop.map (pairConeMap n)).hom.comp ContinuousMap.fst).prodMk
      ContinuousMap.snd)

end KIP126.StableHomotopy.Implementation.HF2Scalar
