import KIP126.Def.StableHomotopy.Implementation.Generators
import Mathlib.Data.ZMod.Basic

/-! A concrete HF₂-local source. Ordinary sequential spectra and stable
weak equivalences are already fixed. An Eilenberg–Mac Lane spectrum is
specified by its actual stable homotopy groups, including loop addition.
Equivalences detected by all its integer cohomology groups define the
HF₂ localization. The auxiliary S[1/2] construction separately specifies
Moore(2)-completion; their agreement is asserted only for the sphere used
here, not for arbitrary unbounded spectra. -/
namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Topology
open scoped unitInterval

namespace BasedSpace

/-- Traverse the suspension coordinate twice. It is deliberately a raw
function: the jump from 1 to 0 is continuous only after reduced suspension. -/
noncomputable def doubleInterval (t : I) : I :=
  if h : (t : ℝ) ≤ 1/2 then
    ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  else
    ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

/-- This is the degree-two pinch/fold map, fixed on quotient representatives.
Its source is a reduced suspension, so the two traversals add in homotopy. -/
theorem doubleSuspension_exists (A : BasedSpace.{0}) :
    ∃! f : A.suspension ⟶ A.suspension, ∀ a t,
      f.map (suspensionProjection A (a,t)) =
        suspensionProjection A (a,doubleInterval t) := by sorry

noncomputable def doubleSuspension (A : BasedSpace.{0}) :
    A.suspension ⟶ A.suspension := (doubleSuspension_exists A).exists.choose

end BasedSpace
namespace Prespectrum

/-- The prespectrum with sphere levels and doubled bonding maps. Its stable
homotopy groups are the sequential colimit under multiplication by 2; it is
therefore the ordinary sphere with 2 inverted, not the mod-2 Moore spectrum. -/
noncomputable def sphereInvertTwo : Prespectrum.{0} where
  level := sphereLevel
  bond n := (BasedSpace.doubleSuspension (sphereLevel n)).map.comp (sphere.bond n)
  bond_point n t := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (_,t)) = _
    exact (congrArg (BasedSpace.doubleSuspension (sphereLevel n)).map
      (sphere.bond_point n t)).trans (BasedSpace.doubleSuspension _).point
  bond_zero n x := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (x,0)) = _
    rw [sphere.bond_zero]
    exact (BasedSpace.doubleSuspension _).point
  bond_one n x := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (x,1)) = _
    rw [sphere.bond_one]
    exact (BasedSpace.doubleSuspension _).point

/-- Orthogonality to every shift of S[1/2], expressed in the already defined
ordinary stable localization. Both nonnegative and nonpositive shifts occur. -/
def IsTwoComplete (X : Prespectrum.{0}) : Prop :=
  ∀ n : ℕ,
    Subsingleton (sourceLocalization.obj ((suspension^[n]) sphereInvertTwo) ⟶
      sourceLocalization.obj X) ∧
    Subsingleton (sourceLocalization.obj ((desuspension^[n]) sphereInvertTwo) ⟶
      sourceLocalization.obj X)

end Prespectrum

/-- Exact Eilenberg–Mac Lane characterization in the ordinary source.
The equivalence respects the actual cubical concatenation and zero, so it
is not an arbitrary two-element set identified with F₂. -/
structure SourceHF2Model where
  spectrum : Prespectrum.{0}
  good : ∀ n, (spectrum.level n).IsGood
  pi0 : Prespectrum.StableHomotopy spectrum 0 ≃ ZMod 2
  pi0_zero : pi0 (Prespectrum.loopClass spectrum 0 0 0 (by simp) GenLoop.const) = 0
  pi0_add : ∀ (n : ℕ)
      (p q : GenLoop (Fin (n+1)) (spectrum.level (n+1)) (spectrum.level (n+1)).point),
    pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega)
        (GenLoop.transAt 0 p q)) =
      pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega) p) +
      pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega) q)
  vanishes : ∀ d : ℤ, d ≠ 0 → Subsingleton (Prespectrum.StableHomotopy spectrum d)

theorem sourceHF2Model_exists : Nonempty SourceHF2Model := by sorry

noncomputable def sourceHF2 : SourceHF2Model := Classical.choice sourceHF2Model_exists

noncomputable def sourceHF2Shift (d : ℤ) : SourceCategory.{0} :=
  sourceLocalization.obj
    (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
     else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum)

/-- Mod-2 cohomology equivalences in all integer degrees. Over the field F₂,
cohomology detects exactly HF₂-homology equivalences, without a boundedness
restriction. The target HF₂ here was fixed before choosing any implementation. -/
def HF2Equivalences : MorphismProperty SourceCategory.{0} :=
  fun X Y f => ∀ d : ℤ,
    Function.Bijective (fun a : Y ⟶ sourceHF2Shift d => f ≫ a)

namespace Prespectrum
/-- The actual right lifting/orthogonality property defining HF₂-local
objects in the ordinary stable category. This is not Moore-locality. -/
def IsHF2Local (X : Prespectrum.{0}) : Prop :=
  ∀ {A B : SourceCategory.{0}} (f : A ⟶ B), HF2Equivalences f →
    Function.Bijective (fun a : B ⟶ sourceLocalization.obj X => f ≫ a)
end Prespectrum

/-- The full subcategory of local objects, represented by point-set spectra. -/
structure CompletedSpectrum where
  spectrum : Prespectrum.{0}
  isLocal : spectrum.IsHF2Local

noncomputable instance : Category CompletedSpectrum where
  Hom X Y := sourceLocalization.obj X.spectrum ⟶ sourceLocalization.obj Y.spectrum
  id X := 𝟙 _
  comp f g := f ≫ g
  id_comp := by intros; apply Category.id_comp
  comp_id := by intros; apply Category.comp_id
  assoc := by intros; apply Category.assoc

/-- A functorial local replacement, including its reflection universal
property in the ordinary stable category. The unit is an actual point-set
map. This pins the completion and all induced maps up to unique isomorphism. -/
structure CompletionModel where
  replacement : Prespectrum.{0} ⥤ Prespectrum.{0}
  unit : 𝟭 _ ⟶ replacement
  isLocal : ∀ X, (replacement.obj X).IsHF2Local
  universal : ∀ (X : Prespectrum.{0}) (Y : CompletedSpectrum),
    Function.Bijective (fun f : sourceLocalization.obj (replacement.obj X) ⟶
        sourceLocalization.obj Y.spectrum => sourceLocalization.map (unit.app X) ≫ f)

/-- Construction of the reflection in the explicitly specified local objects.
No Adams differential, vanishing line, or stable stem is an input. -/
theorem completionModel_exists : Nonempty CompletionModel := by sorry

noncomputable def completionModel : CompletionModel := Classical.choice completionModel_exists

noncomputable def completedLocalization : Prespectrum.{0} ⥤ CompletedSpectrum where
  obj X := ⟨completionModel.replacement.obj X, completionModel.isLocal X⟩
  map f := sourceLocalization.map (completionModel.replacement.map f)
  map_id X := by
    change sourceLocalization.map (completionModel.replacement.map (𝟙 X)) = 𝟙 _
    simp
  map_comp f g := by
    change sourceLocalization.map (completionModel.replacement.map (f ≫ g)) =
      sourceLocalization.map (completionModel.replacement.map f) ≫
      sourceLocalization.map (completionModel.replacement.map g)
    simp

/-- On the ordinary sphere, HF₂ localization is the paper's 2-completion.
These two exact statements identify the SAME unit by its Moore-local
reflection property; no such identification is asserted for all spectra. -/
theorem completedSphere_twoComplete :
    (completionModel.replacement.obj Prespectrum.sphere).IsTwoComplete := by sorry

theorem completedSphere_moore_universal (Y : Prespectrum.{0}) (hY : Y.IsTwoComplete) :
    Function.Bijective (fun f :
      sourceLocalization.obj (completionModel.replacement.obj Prespectrum.sphere) ⟶
          sourceLocalization.obj Y =>
      sourceLocalization.map (completionModel.unit.app Prespectrum.sphere) ≫ f) := by sorry

end KIP126.StableHomotopy.Implementation
