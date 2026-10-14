module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Endpoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.HomotopyLifting
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The actual inclusion of the two interval endpoints. -/
def intervalBoundaryInclusion : intervalBoundaryObject ⟶ TopCat.of I :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual endpoint parameter acts on the original smash. -/
noncomputable def spaceSmashIntervalBoundaryMap (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X ⟶
      spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X :=
  spaceSmashMap (BasedSpace.adjoinPointMap intervalBoundaryInclusion) (𝟙 X)

/-- The two actual endpoint representatives map to the two strict coproduct
summands; the disjoint basepoint maps to the coproduct basepoint. -/
noncomputable def spaceSmashIntervalBoundaryComparisonLevel (X : Prespectrum.{0}) (n : ℕ) :
    (BasedSpace.adjoinPoint intervalBoundaryObject).smash (X.level n) ⟶ (X ⨿ X).level n := by
  classical
  let A := BasedSpace.adjoinPoint intervalBoundaryObject
  let l : X ⟶ X ⨿ X := coprod.inl
  let r : X ⟶ X ⨿ X := coprod.inr
  let raw : A × X.level n → (X ⨿ X).level n := fun p =>
    match p.1 with
    | .inl e => if e.val = 0 then l.level n p.2 else r.level n p.2
    | .inr _ => ((X ⨿ X).level n).point
  have hc : Continuous raw := by
    letI : Finite intervalBoundaryObject :=
      (show Set.Finite {t : I | t = 0 ∨ t = 1} from
        (Set.finite_singleton (0 : I)).union (Set.finite_singleton (1 : I))).to_subtype
    letI : T1Space intervalBoundaryObject :=
      inferInstanceAs (T1Space {t : I // t = 0 ∨ t = 1})
    have he : Continuous (fun p : intervalBoundaryObject × X.level n =>
        if p.1.val = 0 then l.level n p.2 else r.level n p.2) := by
      apply continuous_prod_of_discrete_left.mpr
      intro e
      dsimp
      split_ifs
      · exact (l.level n).continuous
      · exact (r.level n).continuous
    have h := he.sumElim (continuous_const (y := ((X ⨿ X).level n).point)
      (X := PUnit × X.level n))
    convert h.comp (Homeomorph.sumProdDistrib (X := intervalBoundaryObject)
      (Y := PUnit) (Z := X.level n)).continuous using 1
    all_goals first | rfl | (funext p; rcases p with ⟨e | e,x⟩ <;> rfl)
  have hp (p : A × X.level n)
      (h : p.1 = A.point ∨ p.2 = (X.level n).point) :
      raw p = ((X ⨿ X).level n).point := by
    rcases h with h | h
    · change p.1 = Sum.inr PUnit.unit at h
      simp only [raw,h]
    · rcases p with ⟨e | e,x⟩
      · dsimp [raw]
        split_ifs
        · exact (congrArg (l.level n) h).trans (l.point n)
        · exact (congrArg (r.level n) h).trans (r.point n)
      · rfl
  have hr : ∀ p q, BasedSpace.SmashRelation A (X.level n) p q → raw p = raw q :=
    fun p q h => (hp p h.1).trans (hp q h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × X.level n),
      inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (A × X.level n) :=
    TopologicalSpace.compactlyGenerated.{0} (A × X.level n)
  exact { map := ⟨Quot.lift raw hr,continuous_quot_lift hr hck⟩, point := rfl }

/-- The actual endpoint-smash comparison is a strict prespectrum morphism. -/
noncomputable def spaceSmashIntervalBoundaryComparison (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X ⟶ X ⨿ X where
  level n := (spaceSmashIntervalBoundaryComparisonLevel X n).map
  point n := (spaceSmashIntervalBoundaryComparisonLevel X n).point
  bond n z t := by
    classical
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change (spaceSmashIntervalBoundaryComparisonLevel X (n+1)).map
      ((spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X).bond n
        (BasedSpace.smashPoint _ (X.level n) a x,t)) = _
    rw [spaceSmash_bond]
    cases a with
    | inl e =>
      change (if e.val = 0 then (coprod.inl : X ⟶ X ⨿ X).level (n+1) (X.bond n (x,t))
          else (coprod.inr : X ⟶ X ⨿ X).level (n+1) (X.bond n (x,t))) =
        (X ⨿ X).bond n ((if e.val = 0 then (coprod.inl : X ⟶ X ⨿ X).level n x
          else (coprod.inr : X ⟶ X ⨿ X).level n x),t)
      split_ifs
      · exact (coprod.inl : X ⟶ X ⨿ X).bond n x t
      · exact (coprod.inr : X ⟶ X ⨿ X).bond n x t
    | inr _ => exact ((X ⨿ X).bond_point n t).symm

/-- Insert a specified actual endpoint into the endpoint smash. -/
def spaceSmashIntervalBoundaryAt (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (e : intervalBoundaryObject) :
    X ⟶ spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X where
  level n := ⟨fun x => BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject)
      (X.level n) (.inl e) x,
    BasedSpace.continuous_smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n)
      (ContinuousMap.const _ (.inl e)) (ContinuousMap.id _)⟩
  point n := BasedSpace.smashPoint_base_right _ _ _
  bond n x t := (spaceSmash_bond (BasedSpace.adjoinPoint intervalBoundaryObject) X n (.inl e) x t).symm

/-- The inverse uses the actual coproduct universal property and inserts
its left and right summands at zero and one respectively. -/
noncomputable def spaceSmashIntervalBoundaryInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    X ⨿ X ⟶ spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X :=
  coprod.desc (spaceSmashIntervalBoundaryAt X ⟨0,Or.inl rfl⟩)
    (spaceSmashIntervalBoundaryAt X ⟨1,Or.inr rfl⟩)

end KIP126.StableHomotopy.Implementation.Prespectrum
