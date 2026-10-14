module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Proofs
public import Mathlib.CategoryTheory.LiftingProperties.Limits

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open KIP126.Topology.SmallObject
universe u
set_option backward.isDefEq.respectTransparency false

/-- The stated object property is precisely the same actual initial-arrow
lifting property. -/
theorem isCubicallyCofibrant_iff_initial (X : Prespectrum.{u}) :
    IsCubicallyCofibrant X ↔ IsCubicalCofibration (zeroMap zeroPrespectrum X) := Iff.rfl

/-- The original free cubical generators have the actual lifting property. -/
theorem cubicalCellBoundary_isCubicalCofibration (i : ℕ × ℕ) :
    IsCubicalCofibration (cubicalCellBoundary.{u} i) :=
  fun p hp => cubicalCellBoundary_hasLiftingProperty_of_level p hp i

theorem IsCubicalCofibration.comp {X Y Z : Prespectrum.{u}} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : IsCubicalCofibration i) (hj : IsCubicalCofibration j) :
    IsCubicalCofibration (i ≫ j) := by
  intro E B p hp
  letI := hi p hp
  letI := hj p hp
  infer_instance

/-- Actual pushouts preserve the actual left lifting property. -/
theorem IsCubicalCofibration.pushout {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : IsCubicalCofibration f) (h : IsPushout f g i j) :
    IsCubicalCofibration j := by
  intro E T p hp
  letI := hf p hp
  exact h.flip.hasLiftingProperty p

/-- Attaching an actual cofibration to a cofibrant source retains the
same genuine lifting property. -/
theorem IsCubicallyCofibrant.of_cubicalCofibration {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) {i : X ⟶ Y} (hi : IsCubicalCofibration i) :
    IsCubicallyCofibrant Y := by
  have he : zeroMap zeroPrespectrum X ≫ i = zeroMap zeroPrespectrum Y :=
    zeroPrespectrum_isZero.eq_of_src _ _
  change IsCubicalCofibration (zeroMap zeroPrespectrum Y)
  rw [← he]
  exact IsCubicalCofibration.comp hX hi

/-- The actual free-cell attachment maps, including all simultaneous
cells in the original replacement sequence, have this lifting property. -/
theorem cubicalCellularStageMap_isCubicalCofibration {S : Prespectrum.{u}}
    (X : Over S) (n : ℕ) :
    IsCubicalCofibration (cellularStageMap cubicalCellBoundary X n) := by
  intro E B p hp
  exact cellularStageMap_hasLiftingProperty cubicalCellBoundary X p
    (fun i => cubicalCellBoundary_hasLiftingProperty_of_level p hp i) n

/-- The entire countable actual free-cell inclusion has the lifting
property, including when its initial object is not the zero spectrum. -/
theorem cubicalCellularReplacement_initial_isCubicalCofibration {S : Prespectrum.{u}}
    (X : Over S) :
    IsCubicalCofibration (colimit.ι (cellularSequence cubicalCellBoundary X) 0) := by
  intro E B p hp
  exact cellularReplacement_initial_hasLiftingProperty cubicalCellBoundary X p
    (fun i => cubicalCellBoundary_hasLiftingProperty_of_level p hp i)

/-- A genuine cell pushout retains cofibrancy of its initial target. -/
theorem IsCubicallyCofibrant.pushout {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hC : IsCubicallyCofibrant C) (hf : IsCubicalCofibration f)
    (h : IsPushout f g i j) : IsCubicallyCofibrant D :=
  hC.of_cubicalCofibration (hf.pushout h)

/-- Every actual finite simultaneous-attachment stage is cofibrant
when its actual starting object is. -/
theorem cubicalCellularStage_isCubicallyCofibrant {S : Prespectrum.{u}}
    (X : Over S) (hX : IsCubicallyCofibrant X.left) (n : ℕ) :
    IsCubicallyCofibrant (cellularStage cubicalCellBoundary X n).left := by
  induction n with
  | zero => exact hX
  | succ n ih =>
    exact ih.of_cubicalCofibration (cubicalCellularStageMap_isCubicalCofibration X n)

/-- The actual countable attachment also retains its starting object's
cofibrancy, by the previously proved compatible transfinite lifts. -/
theorem cubicalCellularReplacement_isCubicallyCofibrant {S : Prespectrum.{u}}
    (X : Over S) (hX : IsCubicallyCofibrant X.left) :
    IsCubicallyCofibrant (cellularReplacement cubicalCellBoundary X) :=
  hX.of_cubicalCofibration (cubicalCellularReplacement_initial_isCubicalCofibration X)

end KIP126.StableHomotopy.Implementation.Prespectrum
