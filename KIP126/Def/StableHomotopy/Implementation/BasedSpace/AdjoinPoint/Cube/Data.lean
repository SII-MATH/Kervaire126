module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Iso.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval

/-- The actual zero-dimensional cube with a disjoint basepoint is the
fixed original zero sphere, with its specified basepoint. -/
def adjoinPointCubeZeroIso : adjoinPoint (cubeObject.{0} 0) ≅ zeroSphere where
  hom := {
    map := ⟨Sum.elim (fun _ => (1 : Fin 2)) (fun _ => (0 : Fin 2)),
      continuous_const.sumElim continuous_const⟩
    point := rfl }
  inv := {
    map := ⟨fun x : Fin 2 => if x = 0 then Sum.inr PUnit.unit else
      Sum.inl (ULift.up (Fin.elim0 : Fin 0 → I)),by
        letI : DiscreteTopology zeroSphere := inferInstanceAs (DiscreteTopology (Fin 2))
        exact continuous_of_discreteTopology⟩
    point := rfl }
  hom_inv_id := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro x
    cases x with
    | inl x =>
      change Sum.inl (ULift.up (Fin.elim0 : Fin 0 → I)) = Sum.inl x
      congr 1
      apply ULift.ext
      funext j
      exact Fin.elim0 j
    | inr x => cases x; rfl
  inv_hom_id := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro x
    change Fin 2 at x
    fin_cases x <;> rfl

/-- The actual based cube successor splits as a compact product
parameter, through the displayed coordinate homeomorphism. -/
def adjoinPointCubeSuccIso (n : ℕ) :
    adjoinPoint (cubeObject.{0} (n+1)) ≅
      adjoinPoint (TopCat.of (I × cubeObject.{0} n)) :=
  adjoinPointIso (TopCat.isoOfHomeo (cubeObjectSuccHomeomorph n))

end KIP126.StableHomotopy.Implementation.BasedSpace
