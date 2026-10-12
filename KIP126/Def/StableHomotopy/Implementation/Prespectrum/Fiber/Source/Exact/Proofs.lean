module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Fractions.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Localization.Roofs.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Lift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Equivalence
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Equivalence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual homotopy fiber represents the kernel of postcomposition
on maps out of every original source object. -/
theorem source_fiberProjection_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) (h : A ⟶ sourceLocalization.obj X) :
    h ≫ sourceLocalization.map f = 0 ↔
      ∃ k : A ⟶ sourceLocalization.obj (fiber f),
        k ≫ sourceLocalization.map (fiberProjection f) = h := by
  constructor
  · intro hh
    have hroof : sourceHasRoof h := by rw [sourceHasRoof_all]; trivial
    obtain ⟨B, s, t, hs, hst⟩ := hroof
    have htf : sourceLocalization.map (t ≫ f) = sourceLocalization.map (zeroMap B Y) := by
      rw [CategoryTheory.Functor.map_comp, ← hst, Category.assoc, hh, comp_zero]
      exact (sourceLocalization.map_zero B Y).symm
    obtain ⟨C, w, hw, ⟨H⟩⟩ := (source_map_eq_iff_exists_homotopy_precomp
      (t ≫ f) (zeroMap B Y)).mp htf
    let l := fiberLift f (w ≫ t) H.hom
      (by simpa only [Category.assoc] using H.zero)
      (by simpa only [show w ≫ zeroMap B Y = zeroMap C Y from rfl] using H.one)
    letI := stableEquivalences.Q_inverts s hs
    letI := stableEquivalences.Q_inverts w hw
    let e := sourceLocalization.map w ≫ sourceLocalization.map s
    refine ⟨inv e ≫ sourceLocalization.map l, ?_⟩
    calc
      (inv e ≫ sourceLocalization.map l) ≫ sourceLocalization.map (fiberProjection f) =
          inv e ≫ sourceLocalization.map (w ≫ t) := by
        rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
        rfl
      _ = inv e ≫ (e ≫ h) := by
        congr 1
        dsimp only [e]
        rw [CategoryTheory.Functor.map_comp, Category.assoc, hst]
      _ = h := by simp
  · rintro ⟨k, rfl⟩
    rw [Category.assoc, source_fiberProjection_comp]
    change k ≫ sourceLocalization.map (0 : fiber f ⟶ Y) = 0
    rw [sourceLocalization.map_zero, comp_zero]

/-- Exactness of the actual fiber sequence on all represented source hom
groups, using the already constructed original additive structures. -/
theorem source_fiberProjection_hom_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map (fiberProjection f)))
      (Preadditive.rightComp A (sourceLocalization.map f)) :=
  source_fiberProjection_exact f A

/-- The actual connecting map represents the kernel of the fiber projection
on maps out of every original source object. -/
theorem source_fiberConnecting_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) (h : A ⟶ sourceLocalization.obj (fiber f)) :
    h ≫ sourceLocalization.map (fiberProjection f) = 0 ↔
      ∃ k : A ⟶ sourceLocalization.obj (Prespectrum.loop Y),
        k ≫ sourceLocalization.map (fiberConnecting f) = h := by
  rw [source_fiberProjection_exact (fiberProjection f) A h]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k ≫ (sourceFiberIterationIso f).inv, ?_⟩
    rw [← sourceFiberIterationIso_projection f]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hk
  · rintro ⟨k, hk⟩
    exact ⟨k ≫ (sourceFiberIterationIso f).hom,
      by simpa only [Category.assoc, sourceFiberIterationIso_projection] using hk⟩

/-- Exactness at the actual fiber in every represented source hom group. -/
theorem source_fiberConnecting_hom_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting f)))
      (Preadditive.rightComp A (sourceLocalization.map (fiberProjection f))) :=
  source_fiberConnecting_exact f A

/-- Exactness at the actual target loop object for every represented
source hom group, using the constructed rotation equivalence. -/
theorem source_loopMap_fiberConnecting_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) (h : A ⟶ sourceLocalization.obj (Prespectrum.loop Y)) :
    h ≫ sourceLocalization.map (fiberConnecting f) = 0 ↔
      ∃ k : A ⟶ sourceLocalization.obj (Prespectrum.loop X),
        k ≫ sourceLocalization.map (loopMap f) = h := by
  rw [source_fiberProjection_exact (fiberConnecting f) A h]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k ≫ (sourceFiberRotationIso f).inv, ?_⟩
    rw [← sourceFiberRotationIso_projection f]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hk
  · rintro ⟨k, hk⟩
    exact ⟨k ≫ (sourceFiberRotationIso f).hom,
      by simpa only [Category.assoc, sourceFiberRotationIso_projection] using hk⟩

theorem source_loopMap_fiberConnecting_hom_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map (loopMap f)))
      (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting f))) :=
  source_loopMap_fiberConnecting_exact f A

/-- The actual fiber sequence is exact at all three middle terms on maps
out of every object of the original ordinary stable localization. -/
theorem source_fiber_hom_longExact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map (loopMap f)))
      (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting f))) ∧
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting f)))
      (Preadditive.rightComp A (sourceLocalization.map (fiberProjection f))) ∧
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map (fiberProjection f)))
      (Preadditive.rightComp A (sourceLocalization.map f)) :=
  ⟨source_loopMap_fiberConnecting_hom_exact f A, source_fiberConnecting_hom_exact f A,
    source_fiberProjection_hom_exact f A⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
