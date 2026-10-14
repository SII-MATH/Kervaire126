module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Associativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Insert the nonbasepoint of the actual zero sphere inside an existing
k-smash. Compact tests give continuity without a hypothesis on either input. -/
noncomputable def spaceSmashUnitInsertionLevel (A B : BasedSpace.{0}) :
    A.smash B ⟶ A.smash (BasedSpace.zeroSphere.smash B) := by
  let s := (show BasedSpace.zeroSphere from (1 : Fin 2))
  let raw (q : A × B) := BasedSpace.smashPoint A (BasedSpace.zeroSphere.smash B) q.1
    (BasedSpace.smashPoint BasedSpace.zeroSphere B s q.2)
  have hraw : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × B),inferInstance] raw := by
    apply continuous_from_compactlyGenerated
    intro K g
    exact BasedSpace.continuous_smashPoint_compact A (BasedSpace.zeroSphere.smash B)
      ⟨fun k => (g k).1,g.continuous.fst⟩
      ⟨fun k => BasedSpace.smashPoint BasedSpace.zeroSphere B s (g k).2,
        BasedSpace.continuous_smashPoint_compact BasedSpace.zeroSphere B
          (ContinuousMap.const _ s) ⟨fun k => (g k).2,g.continuous.snd⟩⟩
  have hbase (q : A × B) (h : q.1 = A.point ∨ q.2 = B.point) :
      raw q = (A.smash (BasedSpace.zeroSphere.smash B)).point := by
    rcases h with h | h
    · dsimp only [raw]
      rw [h,BasedSpace.smashPoint_base_left]
    · dsimp only [raw]
      rw [h,BasedSpace.smashPoint_base_right,BasedSpace.smashPoint_base_right]
  have hr (q q' : A × B) (h : BasedSpace.SmashRelation A B q q') : raw q = raw q' :=
    (hbase q h.1).trans (hbase q' h.2).symm
  exact {
    map := ⟨Quot.lift raw hr,by
      letI : TopologicalSpace (A × B) := TopologicalSpace.compactlyGenerated.{0} (A × B)
      exact continuous_quot_lift hr hraw⟩
    point := hbase (A.point,B.point) (Or.inl rfl) }

/-- The same actual insertion is strict with respect to the original
spectrum bond coordinate. -/
noncomputable def spaceSmashUnitInsertion (A : BasedSpace.{0}) (X : Prespectrum.{0}) :
    spaceSmash A X ⟶ spaceSmash A (spaceSmash BasedSpace.zeroSphere X) where
  level n := (spaceSmashUnitInsertionLevel A (X.level n)).map
  point n := (spaceSmashUnitInsertionLevel A (X.level n)).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change (spaceSmashUnitInsertionLevel A (X.level (n+1))).map
      ((spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t)) = _
    rw [spaceSmash_bond]
    change BasedSpace.smashPoint A _ a (BasedSpace.smashPoint BasedSpace.zeroSphere _
      (show BasedSpace.zeroSphere from (1 : Fin 2)) (X.bond n (x,t))) =
      (spaceSmash A (spaceSmash BasedSpace.zeroSphere X)).bond n
        (BasedSpace.smashPoint A _ a (BasedSpace.smashPoint BasedSpace.zeroSphere _
          (show BasedSpace.zeroSphere from (1 : Fin 2)) x),t)
    rw [spaceSmash_bond,spaceSmash_bond]
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
