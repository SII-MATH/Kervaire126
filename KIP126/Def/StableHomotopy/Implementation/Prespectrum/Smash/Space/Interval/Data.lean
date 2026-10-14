module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Continuity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Universal.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- Send an actual interval-smash representative to the corresponding
point of the original reduced mapping cylinder, before localization. -/
noncomputable def spaceSmashIntervalComparisonLevel (X : Prespectrum.{0}) (n : ℕ) :
    (BasedSpace.adjoinPoint (TopCat.of I)).smash (X.level n) ⟶
      (mappingCylinder (𝟙 X)).level n := by
  let A := BasedSpace.adjoinPoint (TopCat.of I)
  let raw : A × X.level n → (mappingCylinder (𝟙 X)).level n := fun p =>
    match p.1 with
    | .inl t => mappingCylinderMk (𝟙 X) n (.inl (p.2, t))
    | .inr _ => ((mappingCylinder (𝟙 X)).level n).point
  have hc : Continuous raw := by
    have h : Continuous (Sum.elim
        (fun p : I × X.level n => mappingCylinderMk (𝟙 X) n (.inl (p.2, p.1)))
        (fun _ : PUnit × X.level n => ((mappingCylinder (𝟙 X)).level n).point)) :=
      ((mappingCylinderMk (𝟙 X) n).continuous.comp
        (continuous_inl.comp (continuous_snd.prodMk continuous_fst))).sumElim continuous_const
    convert h.comp
      (Homeomorph.sumProdDistrib (X := I) (Y := PUnit) (Z := X.level n)).continuous using 1
    all_goals first | rfl | (funext p; rcases p with ⟨s | s, x⟩ <;> rfl)
  have hp (p : A × X.level n)
      (h : p.1 = A.point ∨ p.2 = (X.level n).point) :
      raw p = ((mappingCylinder (𝟙 X)).level n).point := by
    rcases h with h | h
    · change p.1 = Sum.inr PUnit.unit at h
      simp only [raw, h]
    · rcases p with ⟨t | t, x⟩
      · exact (congrArg (fun x => mappingCylinderMk (𝟙 X) n (.inl (x, t))) h).trans
          (mappingCylinderMk_point (𝟙 X) n t)
      · rfl
  have hr : ∀ p q, BasedSpace.SmashRelation A (X.level n) p q → raw p = raw q :=
    fun p q h => (hp p h.1).trans (hp q h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × X.level n),
      inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (A × X.level n) :=
    TopologicalSpace.compactlyGenerated.{0} (A × X.level n)
  exact {
    map := ⟨Quot.lift raw hr, continuous_quot_lift hr hck⟩
    point := rfl }

/-- The interval-smash comparison commutes with the original spectrum
bonds and collapses only the specified disjoint basepoint. -/
noncomputable def spaceSmashIntervalComparison (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X ⟶ mappingCylinder (𝟙 X) where
  level n := (spaceSmashIntervalComparisonLevel X n).map
  point n := (spaceSmashIntervalComparisonLevel X n).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro ⟨a, x⟩
    change (spaceSmashIntervalComparisonLevel X (n+1)).map
      ((spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X).bond n
        (BasedSpace.smashPoint _ (X.level n) a x, t)) = _
    rw [spaceSmash_bond]
    cases a with
    | inl s => rfl
    | inr s => exact ((mappingCylinder (𝟙 X)).bond_point n t).symm

/-- The actual interval coordinate gives a strict retained path into
the original smash quotient. Compact generation supplies continuity on
the original product with the compact interval. -/
noncomputable def spaceSmashIntervalPath (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    X ⟶ pathPrespectrum (spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X) := by
  let A := BasedSpace.adjoinPoint (TopCat.of I)
  let H (n : ℕ) : C(X.level n × I, A.smash (X.level n)) := by
    letI : UCompactlyGeneratedSpace.{0} (X.level n × I) :=
      BasedSpace.compactlyGenerated_prod_compHaus (X.level n) (CompHaus.of I)
    let a : C(X.level n × I, A) :=
      ⟨fun p => (Sum.inl p.2 : I ⊕ PUnit), continuous_inl.comp continuous_snd⟩
    exact ⟨fun p => BasedSpace.smashPoint A (X.level n) (.inl p.2) p.1,
      BasedSpace.continuous_smashPoint A (X.level n) a ContinuousMap.fst⟩
  refine {
    level n := (H n).curry
    point := ?_
    bond := ?_ }
  · intro n
    apply ContinuousMap.ext
    intro t
    change BasedSpace.smashPoint A (X.level n) (.inl t) (X.level n).point = _
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro n x t
    apply ContinuousMap.ext
    intro s
    change BasedSpace.smashPoint A (X.level (n+1)) (.inl s) (X.bond n (x, t)) = _
    exact (spaceSmash_bond A X n (.inl s) x t).symm

/-- A fixed actual interval coordinate includes the original spectrum
into its interval smash. -/
noncomputable def spaceSmashIntervalAt (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (t : I) :
    X ⟶ spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X :=
  spaceSmashIntervalPath X ≫ pathEvaluation _ t

/-- The inverse sends the cylinder to its interval-smash representative
and the attached end to interval coordinate one. -/
noncomputable def spaceSmashIntervalInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    mappingCylinder (𝟙 X) ⟶ spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X :=
  mappingCylinderDesc (𝟙 X) (spaceSmashIntervalAt X 1) (spaceSmashIntervalPath X)
    (by change spaceSmashIntervalAt X 1 = 𝟙 X ≫ spaceSmashIntervalAt X 1; rw [Category.id_comp])

end KIP126.StableHomotopy.Implementation.Prespectrum
