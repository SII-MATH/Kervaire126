module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Cubical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Representation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual cone's retained nullhomotopy makes its displayed two
arrows compose to zero in the specified ordinary localization. -/
theorem source_coneInclusion_comp {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.map f ≫ sourceLocalization.map (coneInclusion f) = 0 := by
  rw [← sourceLocalization.map_comp, ← sourceLocalization.map_zero X (cone f)]
  exact source_map_eq_of_pathHomotopic
    ⟨⟨coneNullPath f, coneNullPath_zero f, coneNullPath_one f⟩⟩

/-- For actual cubically cofibrant source and target, the literal cone
represents the kernel on maps into the constructed loop target. -/
theorem source_coneInclusion_exact_to_loopSpectrification
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y)
    (Z : Prespectrum.{u}) [∀ n, T1Space (Z.level n)]
    (a : sourceLocalization.obj Y ⟶ sourceLocalization.obj (loopSpectrificationFunctor.obj Z)) :
    sourceLocalization.map f ≫ a = 0 ↔
      ∃ b : sourceLocalization.obj (cone f) ⟶
          sourceLocalization.obj (loopSpectrificationFunctor.obj Z),
        sourceLocalization.map (coneInclusion f) ≫ b = a := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := source_map_surjective_of_isCubicallyCofibrant hY Z a
    change sourceLocalization.map g = a at hg
    have he : sourceLocalization.map (f ≫ g) =
        sourceLocalization.map (zeroMap X (loopSpectrificationFunctor.obj Z)) := by
      rw [sourceLocalization.map_comp, hg, h]
      exact (sourceLocalization.map_zero X (loopSpectrificationFunctor.obj Z)).symm
    obtain ⟨H⟩ := (source_map_eq_iff_pathHomotopic_of_isCubicallyCofibrant hX Z _ _).mp he
    refine ⟨sourceLocalization.map (coneLift f g H.hom H.zero H.one), ?_⟩
    rw [← sourceLocalization.map_comp, coneInclusion_lift, hg]
  · rintro ⟨b, rfl⟩
    rw [← Category.assoc, source_coneInclusion_comp, zero_comp]

/-- The actual cone gives contravariant exactness for every object of
the original source category, without a model-category assumption. -/
theorem source_coneInclusion_exact
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y)
    (A : SourceCategory.{u}) (a : sourceLocalization.obj Y ⟶ A) :
    sourceLocalization.map f ≫ a = 0 ↔
      ∃ b : sourceLocalization.obj (cone f) ⟶ A,
        sourceLocalization.map (coneInclusion f) ≫ b = a := by
  let Z := cubicalReplacementFunctor.obj A.as.obj
  letI := stableEquivalences.Q_inverts (loopSpectrificationUnit Z)
    (loopSpectrificationUnit_stableEquivalence Z)
  letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app A.as.obj)
    (cubicalReplacementComparison_stableEquivalence A.as.obj)
  let e : sourceLocalization.obj (loopSpectrificationFunctor.obj Z) ≅ A :=
    (asIso (sourceLocalization.map (loopSpectrificationUnit Z))).symm ≪≫
      asIso (sourceLocalization.map (cubicalReplacementComparison.app A.as.obj))
  constructor
  · intro h
    have he : sourceLocalization.map f ≫ (a ≫ e.inv) = 0 := by
      rw [← Category.assoc, h, zero_comp]
    obtain ⟨b, hb⟩ := (source_coneInclusion_exact_to_loopSpectrification hX hY f Z _).mp he
    refine ⟨b ≫ e.hom, ?_⟩
    rw [← Category.assoc, hb, Category.assoc, e.inv_hom_id, Category.comp_id]
  · rintro ⟨b, rfl⟩
    rw [← Category.assoc, source_coneInclusion_comp, zero_comp]

/-- Exactness of precomposition on the actual source abelian hom groups. -/
theorem source_coneInclusion_hom_exact
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.leftComp A (sourceLocalization.map (coneInclusion f)))
      (Preadditive.leftComp A (sourceLocalization.map f)) :=
  source_coneInclusion_exact hX hY f A

end KIP126.StableHomotopy.Implementation.Prespectrum
