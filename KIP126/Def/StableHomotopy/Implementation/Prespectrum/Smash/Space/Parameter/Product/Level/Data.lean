module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Associativity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.CompactlyGenerated.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Continuity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology

set_option backward.isDefEq.respectTransparency false

/-- Pair the two ordinary parameter coordinates and retain their
specified disjoint basepoint after the actual smash quotient. -/
noncomputable def parameterSmashProductComparison (S T : TopCat.{0}) :
    (BasedSpace.adjoinPoint S).smash (BasedSpace.adjoinPoint T) ⟶
      BasedSpace.adjoinPoint (TopCat.of (S × T)) := by
  let A := BasedSpace.adjoinPoint S
  let B := BasedSpace.adjoinPoint T
  let C := BasedSpace.adjoinPoint (TopCat.of (S × T))
  let raw : A × B → C := fun p =>
    match p.1, p.2 with
    | .inl s, .inl t => .inl (s, t)
    | _, _ => C.point
  have hleft : Continuous (fun p : S × B =>
      match p.2 with
      | .inl t => (Sum.inl (p.1, t) : C)
      | .inr _ => C.point) := by
    have h : Continuous (Sum.elim (fun p : S × T => (Sum.inl p : C))
        (fun _ : S × PUnit => C.point)) := continuous_inl.sumElim continuous_const
    convert h.comp
      (Homeomorph.prodSumDistrib (X := S) (Y := T) (Z := PUnit)).continuous using 1
    all_goals first | rfl | (funext p; rcases p with ⟨s, t | t⟩ <;> rfl)
  have hc : Continuous raw := by
    have h := hleft.sumElim (show Continuous (fun _ : PUnit × B => C.point) from continuous_const)
    convert h.comp
      (Homeomorph.sumProdDistrib (X := S) (Y := PUnit) (Z := B)).continuous using 1
    all_goals first | rfl | (funext p; rcases p with ⟨s | s, t | t⟩ <;> rfl)
  have hp (p : A × B) (h : p.1 = A.point ∨ p.2 = B.point) : raw p = C.point := by
    rcases h with h | h
    · change p.1 = Sum.inr PUnit.unit at h
      simp only [raw, h]
    · change p.2 = Sum.inr PUnit.unit at h
      rcases p with ⟨s, t⟩
      change t = Sum.inr PUnit.unit at h
      subst t
      cases s <;> rfl
  have hr : ∀ p q, BasedSpace.SmashRelation A B p q → raw p = raw q :=
    fun p q h => (hp p h.1).trans (hp q h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × B), inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (A × B) := TopologicalSpace.compactlyGenerated.{0} (A × B)
  exact {
    map := ⟨Quot.lift raw hr, continuous_quot_lift hr hck⟩
    point := rfl }

/-- Compact Hausdorff parameters continuously supply the inverse
representatives in the original quotient k-smash. -/
noncomputable def parameterSmashProductInverse (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] :
    BasedSpace.adjoinPoint (TopCat.of (S × T)) ⟶
      (BasedSpace.adjoinPoint S).smash (BasedSpace.adjoinPoint T) := by
  let A := BasedSpace.adjoinPoint S
  let B := BasedSpace.adjoinPoint T
  let c : C(S × T, A.smash B) :=
    ⟨fun p => BasedSpace.smashPoint A B (.inl p.1) (.inl p.2),
      BasedSpace.continuous_smashPoint A B
        ⟨fun p : S × T => (Sum.inl p.1 : S ⊕ PUnit), continuous_inl.comp continuous_fst⟩
        ⟨fun p : S × T => (Sum.inl p.2 : T ⊕ PUnit), continuous_inl.comp continuous_snd⟩⟩
  exact {
    map := ⟨Sum.elim c (fun _ => (A.smash B).point), c.continuous.sumElim continuous_const⟩
    point := rfl }

/-- The level comparison reassociates the actual k-smash and then
pairs its parameter coordinates. -/
noncomputable def spaceSmashParameterProductLevel (S T : TopCat.{0}) (A : BasedSpace.{0}) :
    (BasedSpace.adjoinPoint S).smash ((BasedSpace.adjoinPoint T).smash A) ⟶
      (BasedSpace.adjoinPoint (TopCat.of (S × T))).smash A :=
  BasedSpace.smashAssocInverse _ _ _ ≫
    BasedSpace.smashMap (parameterSmashProductComparison S T) (𝟙 A)

/-- The reverse level map uses the continuous actual parameter
representatives and the original forward smash associator. -/
noncomputable def spaceSmashParameterProductInverseLevel (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (A : BasedSpace.{0}) :
    (BasedSpace.adjoinPoint (TopCat.of (S × T))).smash A ⟶
      (BasedSpace.adjoinPoint S).smash ((BasedSpace.adjoinPoint T).smash A) :=
  BasedSpace.smashMap (parameterSmashProductInverse S T) (𝟙 A) ≫
    BasedSpace.smashAssoc _ _ _

end KIP126.StableHomotopy.Implementation.Prespectrum
