module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Gluing.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The full original cube boundary tensor preserves stable equivalences
between cubically cofibrant spectra. The induction glues the actual end and
side faces along their original intersection, including the empty base case. -/
theorem spaceSmashMap_cubeBoundary_stableEquivalence (n : ℕ) {X Y : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeBoundaryObject n))) f) := by
  letI (k : ℕ) := hX.level_uCompactlyGeneratedSpace k
  letI (k : ℕ) := hY.level_uCompactlyGeneratedSpace k
  letI : T2Space intervalBoundaryObject :=
    inferInstanceAs (T2Space {t : I // t = 0 ∨ t = 1})
  have hnat {P Q : TopCat.{0}} (a : P ⟶ Q) :
      spaceSmashMap (BasedSpace.adjoinPointMap a) (𝟙 X) ≫
          spaceSmashMap (𝟙 (BasedSpace.adjoinPoint Q)) f =
        spaceSmashMap (𝟙 (BasedSpace.adjoinPoint P)) f ≫
          spaceSmashMap (BasedSpace.adjoinPointMap a) (𝟙 Y) := by
    rw [← spaceSmashMap_comp,← spaceSmashMap_comp]
    simp only [Category.id_comp,Category.comp_id]
  have hprod (P Q : TopCat.{0}) [CompactSpace P] [T2Space P] [CompactSpace Q] [T2Space Q]
      (hh : stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint P))
        (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint Q)) f))) :
      stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of (P × Q)))) f) := by
    apply (stableEquivalence_iff_source_isIso _).mpr
    letI := stableEquivalences.Q_inverts _ hh
    haveI (Z : Prespectrum.{0}) : IsIso (sourceLocalization.map (spaceSmashParameterProduct P Q Z)) := by
      change IsIso (sourceLocalization.map (spaceSmashParameterProductIso P Q Z).hom)
      infer_instance
    have e := congrArg sourceLocalization.map (spaceSmashParameterProduct_natural P Q f)
    simp only [Functor.map_comp] at e
    exact IsIso.of_isIso_fac_left e.symm
  induction n with
  | zero =>
    letI : IsEmpty (cubeBoundaryObject.{0} 0) := ⟨fun z => by
      obtain ⟨j,hj⟩ := z.down.property
      exact Fin.elim0 j⟩
    let a := spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeBoundaryObject 0))) f
    haveI : IsIso a := (spaceSmash_adjoinPoint_isZero (cubeBoundaryObject 0) X).isIso
      (spaceSmash_adjoinPoint_isZero (cubeBoundaryObject 0) Y) a
    exact (stableEquivalence_iff_source_isIso a).mpr inferInstance
  | succ n ih =>
    letI : T2Space (cubeBoundaryObject.{0} n) :=
      inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))
    have hAX : IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryProductCorner n)) X) :=
      by
        intro E B p hp
        exact IsCubicallyCofibrant.of_iso
          (IsCubicallyCofibrant.spaceSmash_intervalBoundary (hX.spaceSmash_cubeBoundary n))
          (spaceSmashParameterProductIso intervalBoundaryObject (cubeBoundaryObject n) X) p hp
    have hAY : IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryProductCorner n)) Y) :=
      by
        intro E B p hp
        exact IsCubicallyCofibrant.of_iso
          (IsCubicallyCofibrant.spaceSmash_intervalBoundary (hY.spaceSmash_cubeBoundary n))
          (spaceSmashParameterProductIso intervalBoundaryObject (cubeBoundaryObject n) Y) p hp
    have hCX : IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) X) :=
      by
        intro E B p hp
        exact IsCubicallyCofibrant.of_iso
          (IsCubicallyCofibrant.spaceSmash_interval (hX.spaceSmash_cubeBoundary n))
          (spaceSmashParameterProductIso (TopCat.of I) (cubeBoundaryObject n) X) p hp
    have hCY : IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) Y) :=
      by
        intro E B p hp
        exact IsCubicallyCofibrant.of_iso
          (IsCubicallyCofibrant.spaceSmash_interval (hY.spaceSmash_cubeBoundary n))
          (spaceSmashParameterProductIso (TopCat.of I) (cubeBoundaryObject n) Y) p hp
    refine isPushout_stableEquivalence_gluing_of_cubicalCofibration hAX hCX hAY hCY
      (spaceSmashCubeBoundaryProductTop_isCubicalCofibration hX n)
      (spaceSmashCubeBoundaryProductTop_isCubicalCofibration hY n)
      (spaceSmashCubeBoundaryProduct_isPushout n X) (spaceSmashCubeBoundaryProduct_isPushout n Y)
      (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeBoundaryProductCorner n))) f)
      (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n))) f)
      (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeBoundaryProductSide n))) f)
      (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1)))) f)
      (hnat (cubeBoundaryProductTop n)) (hnat (cubeBoundaryProductLeft n))
      (hnat (cubeBoundaryProductEndInclusion n)) (hnat (cubeBoundaryProductSideInclusion n)) ?_ ?_ ?_
    · exact hprod intervalBoundaryObject (cubeBoundaryObject n)
        (spaceSmashMap_intervalBoundary_stableEquivalence (hX.spaceSmash_cubeBoundary n)
          (hY.spaceSmash_cubeBoundary n) _ ih)
    · exact hprod intervalBoundaryObject (cubeObject n)
        (spaceSmashMap_intervalBoundary_stableEquivalence (hX.spaceSmash_cube n)
          (hY.spaceSmash_cube n) _ (spaceSmashMap_cube_stableEquivalence n f hf))
    · exact hprod (TopCat.of I) (cubeBoundaryObject n)
        (spaceSmashMap_interval_stableEquivalence _ ih)

end KIP126.StableHomotopy.Implementation.Prespectrum
