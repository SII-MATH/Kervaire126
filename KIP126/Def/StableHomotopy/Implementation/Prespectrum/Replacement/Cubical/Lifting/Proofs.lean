module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Proofs
public import KIP126.Def.Topology.SmallObject.Sequence.Lifting.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
open KIP126.Topology.SmallObject KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual boundary lifting at every level supplies lifting against each
actual free cubical boundary generator. -/
theorem cubicalCellBoundary_hasLiftingProperty_of_level
    {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hq : ∀ n, HasCubeBoundaryLifting (q.level n)) (i : ℕ × ℕ) :
    HasLiftingProperty (cubicalCellBoundary i) q := by
  apply (freeMap_hasLiftingProperty_iff i.1 _ q).mpr
  constructor
  intro t b sq
  let t' : C(↥(_root_.Cube.boundary (Fin i.2)), E.level i.1) :=
    (BasedSpace.adjoinPointEquiv _ _ t).comp ⟨ULift.up, continuous_uliftUp⟩
  let b' : C(Fin i.2 → I, B.level i.1) :=
    (BasedSpace.adjoinPointEquiv _ _ b).comp ⟨ULift.up, continuous_uliftUp⟩
  obtain ⟨l, hl, hb⟩ := hq i.1 i.2 t' b' (fun z =>
    congrArg (fun f => f.map (Sum.inl (ULift.up z))) sq.w)
  refine CommSq.HasLift.mk' {
    l := (BasedSpace.adjoinPointEquiv _ _).symm
      (l.comp ⟨ULift.down, continuous_uliftDown⟩)
    fac_left := ?_
    fac_right := ?_ }
  · apply (BasedSpace.adjoinPointEquiv _ _).injective
    rw [BasedSpace.adjoinPointEquiv_precomp, Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro z
    exact hb z.down
  · apply (BasedSpace.adjoinPointEquiv _ _).injective
    rw [BasedSpace.adjoinPointEquiv_postcomp, Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro z
    exact hl z.down

/-- The actual countable free-cell replacement is cofibrant with respect
to the original free cubical generators. -/
theorem cubicalReplacement_initial_hasLiftingProperty (X : Prespectrum.{u})
    {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hq : ∀ i, HasLiftingProperty (cubicalCellBoundary i) q) :
    HasLiftingProperty (zeroMap zeroPrespectrum (cubicalReplacementFunctor.obj X)) q := by
  have h := cellularReplacement_initial_hasLiftingProperty cubicalCellBoundary
    (Over.mk (zeroMap zeroPrespectrum X)) q hq
  have he : zeroMap zeroPrespectrum (cubicalReplacementFunctor.obj X) =
      colimit.ι (cellularSequence cubicalCellBoundary
        (Over.mk (zeroMap zeroPrespectrum X))) 0 :=
    zeroPrespectrum_isZero.eq_of_src _ _
  rw [he]
  exact h

/-- In particular the same actual initial inclusion lifts against every
strict map with genuine full-boundary lifting on all its levels. -/
theorem cubicalReplacement_initial_hasLiftingProperty_of_level
    (X : Prespectrum.{u}) {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hq : ∀ n, HasCubeBoundaryLifting (q.level n)) :
    HasLiftingProperty (zeroMap zeroPrespectrum (cubicalReplacementFunctor.obj X)) q :=
  cubicalReplacement_initial_hasLiftingProperty X q
    (cubicalCellBoundary_hasLiftingProperty_of_level q hq)

/-- Every actual strict map out of the constructed replacement lifts
strictly through a levelwise cubical trivial fibration. -/
theorem cubicalReplacement_lift_of_level_cubeBoundary (X : Prespectrum.{u})
    {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hq : ∀ n, HasCubeBoundaryLifting (q.level n))
    (b : cubicalReplacementFunctor.obj X ⟶ B) :
    ∃ l : cubicalReplacementFunctor.obj X ⟶ E, l ≫ q = b := by
  letI := cubicalReplacement_initial_hasLiftingProperty_of_level X q hq
  let sq : CommSq (zeroMap zeroPrespectrum E)
      (zeroMap zeroPrespectrum (cubicalReplacementFunctor.obj X)) q b :=
    ⟨zeroPrespectrum_isZero.eq_of_src _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
