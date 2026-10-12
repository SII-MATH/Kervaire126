module

public import KIP126.Def.StableHomotopy.Implementation.Comparison.Suspension.Desuspension.Data
public import KIP126.Def.StableHomotopy.Cohomology.Conservativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory MonoidalCategory KIP126.StableHomotopy.Cohomology
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)}
  (S : SourceComparison H) (R : Mod2RingStructure H)
  [(tensorLeft H.HF2).CommShift ℤ]

include R in
/-- For an actual local source test spectrum whose completed image is a
shift of HF₂, coefficient-smash equivalence gives source cohomology
invariance. The source reflection unit supplies the required Hom comparison. -/
theorem SourceComparison.precomp_source_bijective_of_shift_iso
    (T : Prespectrum.{0}) (hT : T.IsHF2Local) (d : ℤ)
    (eT : S.equivalence.functor.obj (completedLocalization.obj T) ≅ H.HF2⟦d⟧)
    {A B : CompletedSpectrum} (f : A ⟶ B)
    [IsIso (H.HF2 ◁ S.equivalence.functor.map f)] :
    Function.Bijective (fun a : sourceLocalization.obj B.spectrum ⟶ sourceLocalization.obj T =>
      (show sourceLocalization.obj A.spectrum ⟶ sourceLocalization.obj B.spectrum from f) ≫ a) := by
  let uT := sourceLocalization.map (completionModel.unit.app T)
  letI : IsIso uT := completionModel.unit_isIso_of_local T hT
  let e (Z : CompletedSpectrum) :
      (sourceLocalization.obj Z.spectrum ⟶ sourceLocalization.obj T) ≃
      (S.equivalence.functor.obj Z ⟶ H.HF2⟦d⟧) :=
    ((Iso.homCongr (Iso.refl _) (asIso uT)).trans (S.equivalence.fullyFaithfulFunctor.homEquiv (X := Z) (Y := completedLocalization.obj T))).trans
      (Iso.homCongr (Iso.refl _) eT)
  have he (a : sourceLocalization.obj B.spectrum ⟶ sourceLocalization.obj T) :
      e A ((show sourceLocalization.obj A.spectrum ⟶ sourceLocalization.obj B.spectrum from f) ≫ a) = S.equivalence.functor.map f ≫ e B a := by
    change 𝟙 _ ≫ S.equivalence.functor.map
        ((𝟙 (sourceLocalization.obj A.spectrum) ≫
            ((show sourceLocalization.obj A.spectrum ⟶ sourceLocalization.obj B.spectrum from f) ≫ a) ≫ uT) :
          sourceLocalization.obj A.spectrum ⟶ sourceLocalization.obj (completionModel.replacement.obj T)) ≫ eT.hom =
      S.equivalence.functor.map f ≫ 𝟙 _ ≫ S.equivalence.functor.map
        ((𝟙 (sourceLocalization.obj B.spectrum) ≫ a ≫ uT) :
          sourceLocalization.obj B.spectrum ⟶ sourceLocalization.obj (completionModel.replacement.obj T)) ≫ eT.hom
    simp only [Category.id_comp, Category.assoc]
    change S.equivalence.functor.map
        (f ≫ ((a ≫ uT) : sourceLocalization.obj B.spectrum ⟶ sourceLocalization.obj (completionModel.replacement.obj T))) ≫ eT.hom = _
    rw [Functor.map_comp, Category.assoc]
  have h := precomp_hf2_shift_bijective_of_tensor_isIso H R (S.equivalence.functor.map f) d
  constructor
  · intro a b hab
    apply (e B).injective
    apply h.injective
    change S.equivalence.functor.map f ≫ e B a = S.equivalence.functor.map f ≫ e B b
    rw [← he a, ← he b]
    exact congrArg (e A) hab
  · intro a
    obtain ⟨b, hb⟩ := h.surjective (e A a)
    obtain ⟨b, rfl⟩ := (e B).surjective b
    refine ⟨b, (e A).injective ?_⟩
    rw [he]
    exact hb

include R in
/-- Coefficient-smash equivalences induce cohomology bijections for all
nonnegative shifts of the actual source HF₂. Their recognition is derived from the supplied
single-suspension comparison and the source spectrum's good levels. -/
theorem SourceComparison.precomp_sourceHF2Shift_nat_bijective
    {A B : CompletedSpectrum} (f : A ⟶ B)
    [IsIso (H.HF2 ◁ S.equivalence.functor.map f)] (k : ℕ) :
    Function.Bijective (fun a : sourceLocalization.obj B.spectrum ⟶ sourceHF2Shift (k : ℤ) =>
      (show sourceLocalization.obj A.spectrum ⟶ sourceLocalization.obj B.spectrum from f) ≫ a) := by
  have hlocal : ((Prespectrum.suspension^[k]) sourceHF2.spectrum).IsHF2Local := by
    intro X Y g hg
    simpa [sourceHF2Shift] using hg (k : ℤ)
  simpa [sourceHF2Shift] using
    S.precomp_source_bijective_of_shift_iso R _ hlocal (k : ℤ)
      (S.hf2_iterateSuspensionIso k) f

include R in
/-- An equivalence after coefficient smash induces a genuine source
HF₂-cohomology equivalence in every integer degree. -/
theorem SourceComparison.source_hf2Equivalence_of_tensor_isIso
    {A B : CompletedSpectrum} (f : A ⟶ B)
    [IsIso (H.HF2 ◁ S.equivalence.functor.map f)] :
    HF2Equivalences
      (show sourceLocalization.obj A.spectrum ⟶ sourceLocalization.obj B.spectrum from f) := by
  intro d
  let T : Prespectrum.{0} :=
    if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
    else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum
  have hT : T.IsHF2Local := fun g hg => hg d
  exact S.precomp_source_bijective_of_shift_iso R T hT d (S.hf2_sourceShiftIso d) f

include S R in
/-- Coefficient smash reflects isomorphisms in a category recognized by
actual HF₂-local source spectra. All integer test-object comparisons are
constructed from the supplied suspension recognition and geometric zigzag. -/
theorem SourceComparison.tensorLeft_hf2_reflectsIsomorphisms : (tensorLeft H.HF2).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    let g : S.equivalence.inverse.obj A ⟶ S.equivalence.inverse.obj B := S.equivalence.inverse.map f
    have hnat := S.equivalence.counitIso.hom.naturality f
    letI : IsIso ((tensorLeft H.HF2).map (S.equivalence.functor.map g)) := by
      have he := congrArg (tensorLeft H.HF2).map hnat
      simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at he
      exact IsIso.of_isIso_fac_right he
    letI : IsIso (H.HF2 ◁ S.equivalence.functor.map g) :=
      inferInstanceAs (IsIso ((tensorLeft H.HF2).map (S.equivalence.functor.map g)))
    have hlocal := Prespectrum.IsHF2Local.isIso_of_hf2Equivalence
      (S.equivalence.inverse.obj A).isLocal (S.equivalence.inverse.obj B).isLocal
      (show sourceLocalization.obj (S.equivalence.inverse.obj A).spectrum ⟶
        sourceLocalization.obj (S.equivalence.inverse.obj B).spectrum from g)
      (S.source_hf2Equivalence_of_tensor_isIso R g)
    letI : IsIso g := by
      obtain ⟨q,hq,hq'⟩ := hlocal.out
      exact ⟨⟨q,hq,hq'⟩⟩
    exact isIso_of_reflects_iso f S.equivalence.inverse

end KIP126.StableHomotopy.Implementation
