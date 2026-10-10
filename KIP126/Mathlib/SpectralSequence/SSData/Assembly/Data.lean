import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Adapting nested-subobject spectral sequences to Mathlib

The source of every page object and differential is the internal `SSData`
presentation. This module packages them as Mathlib homological complexes;
it does not redefine cycles or boundaries.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- The Mathlib complex shape corresponding to the internal differential degree. -/
def MathlibAdapter.pageShape (E : SpectralSequence C ι)
    (r : ℤ) : ComplexShape ι :=
  ComplexShape.up' (E.diffDeg r)

/-- An internal `Z/B` page, packaged as a Mathlib homological complex. -/
noncomputable def MathlibAdapter.pageComplex
    (E : SpectralSequence C ι) (r : ℤ) :
    HomologicalComplex C (MathlibAdapter.pageShape E r) := by
  classical
  refine {
  X k := E.Page r k
  d k l := if h : (MathlibAdapter.pageShape E r).Rel k l then
      E.d r k ≫ eqToHom (by
        change k + E.diffDeg r = l at h
        rw [← h])
    else 0
  shape k l h := by
    simp only [dif_neg h]
  d_comp_d' k l m hkl hlm := by
    simp only [dif_pos hkl, dif_pos hlm]
    change k + E.diffDeg r = l at hkl
    change l + E.diffDeg r = m at hlm
    subst l
    subst m
    simp only [eqToHom_refl, Category.comp_id]
    exact E.d_comp_d r k }

/-- Assemble an internal nested-subobject spectral sequence as a Mathlib
spectral sequence, with the same finite quotient pages and differentials. -/
noncomputable def MathlibAdapter.toMathlib
    (E : SpectralSequence C ι) :
    CategoryTheory.SpectralSequence C (MathlibAdapter.pageShape E) E.r₀ where
  page r _ := MathlibAdapter.pageComplex E r
  iso r r' k hrr' hr := by
    subst r'
    let δ := E.diffDeg r
    let source : ι := k - δ
    let mid : ι := source + δ
    let target : ι := mid + δ
    let K := MathlibAdapter.pageComplex E r
    have hm : mid = k := sub_add_cancel k δ
    have hs : (MathlibAdapter.pageShape E r).Rel source mid := by
      change source + δ = mid
      rfl
    have ht : (MathlibAdapter.pageShape E r).Rel mid target := by
      change mid + δ = target
      rfl
    have hsc : K.sc' source mid target = E.pageShortComplex r source := by
      change ShortComplex.mk (K.d source mid) (K.d mid target) _ =
        ShortComplex.mk (E.d r source) (E.d r (source + E.diffDeg r)) _
      simp only [K, MathlibAdapter.pageComplex, dif_pos hs, dif_pos ht,
        mid, target, eqToHom_refl, Category.comp_id]
      rfl
    have hhom : (K.sc' source mid target).homology =
        (E.pageShortComplex r (k - E.diffDeg r)).homology := by
      exact congrArg (fun (S : ShortComplex C) => S.homology) hsc
    exact eqToIso (congrArg (fun j : ι => K.homology j) hm.symm) ≪≫
      K.homologyIsoSc' source mid target
        ((MathlibAdapter.pageShape E r).prev_eq' hs)
        ((MathlibAdapter.pageShape E r).next_eq' ht) ≪≫
      eqToIso hhom ≪≫
      (E.pageHomologyIso r k hr).symm

end KIP126.Core.SpectralSequence
