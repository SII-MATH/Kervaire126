/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.UnboundedExtension

/-!
# Initial page and abutment of an extension spectral sequence

This file packages the two comparisons which characterize the extension
spectral sequence attached to a filtered map `A₁ ⟶ A₂`:

* its zeroth page is the pair of limiting pages of the two input spectral
  sequences; and
* the homology of its two-term abutment complex is `ker(f)` in complex degree
  `1` and `coker(f)` in complex degree `0`.

The first comparison uses the unbounded finite-page construction and therefore
does not impose boundedness on the two filtrations.  Boundedness occurs only in
`BoundedExtensionSS.abutmentComparison`, where it supplies the existing weak
convergence witness.
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w w₀

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## The zeroth page of a filtered complex -/

/-- The zeroth boundary subobject of an arbitrary filtered complex is zero.

At page zero an incoming representative lies in `F^(s+1)`, so its image dies
in `F^s/F^(s+1)`.  This fact does not require a bounded filtration. -/
theorem FilteredComplex.boundarySubobject_zero_eq_bot
    (FC : FilteredComplex C) (s k : ℤ) :
    FC.boundarySubobject s k (0 : WithTop ℕ) = ⊥ := by
  let q : ℤ := s - (↑(0 : ℕ) : ℤ) + 1
  let eDeg : (k + 1) - 1 = k := by omega
  let eSub := congr_arg
    (fun j => Subobject.underlying.obj (FC.fil q j)) eDeg
  let eA := congr_arg FC.A eDeg
  let φ := FC.filDiff q (k + 1) ≫ eqToHom eSub
  have htransport : eqToHom eSub ≫ (FC.fil q k).arrow =
      (FC.fil q ((k + 1) - 1)).arrow ≫ eqToHom eA := by
    have hgeneral : ∀ (a b : ℤ) (h : a = b),
        eqToHom (congr_arg
            (fun j => Subobject.underlying.obj (FC.fil q j)) h) ≫
            (FC.fil q b).arrow =
          (FC.fil q a).arrow ≫ eqToHom (congr_arg FC.A h) := by
      intro a b h
      subst h
      simp
    exact hgeneral ((k + 1) - 1) k eDeg
  have hφ : φ ≫ (FC.fil q k).arrow =
      (FC.fil q (k + 1)).arrow ≫ FC.dToK k := by
    unfold φ FilteredComplex.dToK
    rw [Category.assoc, htransport, ← Category.assoc,
      FC.filDiff_comp_arrow]
    simp only [Category.assoc]
  let J := imageSubobject
    ((FC.fil q (k + 1)).arrow ≫ FC.dToK k)
  let I := J ⊓ FC.fil s k
  have hJ : J ≤ FC.fil q k :=
    imageSubobject_le _ φ hφ
  have hI : I ≤ FC.fil q k := le_trans inf_le_left hJ
  have hq : FC.fil q k ≤ FC.fil (s + 1) k := by
    apply le_of_eq
    congr 1
    dsimp only [q]
    omega
  have hI' : I ≤ FC.fil (s + 1) k := le_trans hI hq
  have hinc : Subobject.ofLE I (FC.fil s k) inf_le_right =
      Subobject.ofLE I (FC.fil (s + 1) k) hI' ≫
        Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
          (FC.fil_anti s k) := by
    apply (cancel_mono (FC.fil s k).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow]
  have hzero : Subobject.ofLE I (FC.fil s k) inf_le_right ≫
      FC.filToAssocGraded s k = 0 := by
    rw [hinc, Category.assoc]
    change Subobject.ofLE I (FC.fil (s + 1) k) hI' ≫
      (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
        (FC.fil_anti s k) ≫
        cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
          (FC.fil_anti s k))) = 0
    rw [cokernel.condition, comp_zero]
  simp only [FilteredComplex.boundarySubobject]
  change imageSubobject
      (Subobject.ofLE I (FC.fil s k) inf_le_right ≫
        FC.filToAssocGraded s k) = ⊥
  apply le_antisymm
  · exact imageSubobject_le (X := ⊥)
      (Subobject.ofLE I (FC.fil s k) inf_le_right ≫
        FC.filToAssocGraded s k)
      (0 : Subobject.underlying.obj I ⟶
        Subobject.underlying.obj (⊥ : Subobject (FC.assocGraded s k)))
      (by simpa using hzero.symm)
  · exact bot_le

/-- The zeroth finite page of a filtered complex is its associated graded
object.  No boundedness hypothesis is needed. -/
noncomputable def FilteredComplex.finitePageZeroIso
    (FC : FilteredComplex C) (s k : ℤ) :
    FC.finitePage s k 0 ≅ FC.assocGraded s k := by
  unfold FilteredComplex.finitePage
  let B := FC.boundarySubobject s k ((0 : ℕ) : WithTop ℕ)
  let Z := FC.cycleSubobject s k ((0 : ℕ) : WithTop ℕ)
  have hB : B = ⊥ := FC.boundarySubobject_zero_eq_bot s k
  have hZ : Z = ⊤ := FC.cycleSubobject_zero_eq_top s k
  have hBZ : B ≤ Z := by rw [hB, hZ]; exact bot_le
  change cokernel (Subobject.ofLE B Z hBZ) ≅ FC.assocGraded s k
  let p : Subobject.underlying.obj B ≅
      Subobject.underlying.obj (⊥ : Subobject (FC.assocGraded s k)) :=
    eqToIso (congr_arg Subobject.underlying.obj hB)
  let q : Subobject.underlying.obj Z ≅
      Subobject.underlying.obj (⊤ : Subobject (FC.assocGraded s k)) :=
    eqToIso (congr_arg Subobject.underlying.obj hZ)
  have hp : p.hom ≫ (⊥ : Subobject (FC.assocGraded s k)).arrow = B.arrow := by
    change eqToHom (congr_arg Subobject.underlying.obj hB) ≫
      (⊥ : Subobject (FC.assocGraded s k)).arrow = B.arrow
    exact Subobject.arrow_congr B ⊥ hB
  have hq : q.hom ≫ (⊤ : Subobject (FC.assocGraded s k)).arrow = Z.arrow := by
    change eqToHom (congr_arg Subobject.underlying.obj hZ) ≫
      (⊤ : Subobject (FC.assocGraded s k)).arrow = Z.arrow
    exact Subobject.arrow_congr Z ⊤ hZ
  have hsquare : Subobject.ofLE B Z hBZ ≫ q.hom =
      p.hom ≫ Subobject.ofLE
        (⊥ : Subobject (FC.assocGraded s k)) ⊤ bot_le := by
    apply (cancel_mono (⊤ : Subobject (FC.assocGraded s k)).arrow).1
    simp only [Category.assoc, hq, Subobject.ofLE_arrow, hp]
  have hzero : Subobject.ofLE
      (⊥ : Subobject (FC.assocGraded s k)) ⊤ bot_le = 0 := by
    apply (cancel_mono (⊤ : Subobject (FC.assocGraded s k)).arrow).1
    rw [Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]
  exact cokernel.mapIso (Subobject.ofLE B Z hBZ)
      (Subobject.ofLE (⊥ : Subobject (FC.assocGraded s k)) ⊤ bot_le)
      p q hsquare ≪≫ cokernelIsoOfEq hzero ≪≫
    cokernelZeroIsoTarget ≪≫
    asIso (⊤ : Subobject (FC.assocGraded s k)).arrow

/-! ## The zeroth page of the unbounded extension spectral sequence -/

section InitialPage

variable {w' : Type w} [AddCommGroup w'] [DecidableEq w']
variable {E₁ E₂ : SpectralSequence C w'}
variable {τ : Type w}
variable {A₁ A₂ : τ → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
variable {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
variable [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
variable [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]

/-- The actual page zero of the unbounded extension spectral sequence is the
associated graded of its underlying filtered two-term complex. -/
noncomputable def extensionE0IsoAssociatedGraded
    (cm : ConvergenceMorphism conv₁ conv₂) (t : τ) (s k : ℤ) :
    (ExtensionSpectralSequence cm t).Page 0 (s, k) ≅
      (unboundedUnderlyingComplex cm t).assocGraded s k :=
  unboundedExtensionPageIso cm t (s, k) 0 ≪≫
    (unboundedUnderlyingComplex cm t).finitePageZeroIso s k

/-- Source-column form of the `E₀` comparison. -/
noncomputable def extensionE0SourceIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : τ) (s : ℤ) :
    (ExtensionSpectralSequence cm t).Page 0 (s, 1) ≅
      unboundedExtensionV conv₁ conv₂ t (s, 1) :=
  extensionE0IsoAssociatedGraded cm t s 1 ≪≫
    (unboundedExtensionVOneComplexIso cm t s).symm

/-- Target-column form of the `E₀` comparison. -/
noncomputable def extensionE0TargetIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : τ) (s : ℤ) :
    (ExtensionSpectralSequence cm t).Page 0 (s, 0) ≅
      unboundedExtensionV conv₁ conv₂ t (s, 0) :=
  extensionE0IsoAssociatedGraded cm t s 0 ≪≫
    (unboundedExtensionVZeroComplexIso cm t s).symm

/-- The total zeroth page, with the two complex columns displayed as a
biproduct, is the direct sum of the two input `E∞` objects. -/
noncomputable def extensionE0TotalIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : τ) (s : ℤ) :
    ((ExtensionSpectralSequence cm t).Page 0 (s, 1) ⊞
      (ExtensionSpectralSequence cm t).Page 0 (s, 0)) ≅
      (unboundedExtensionV conv₁ conv₂ t (s, 1) ⊞
        unboundedExtensionV conv₁ conv₂ t (s, 0)) :=
  biprod.mapIso (extensionE0SourceIso cm t s)
    (extensionE0TargetIso cm t s)

end InitialPage

/-! ## Homology of a two-term complex -/

section TwoTermAbutment

variable {τ : Type w}
variable {A₁ A₂ : τ → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}

/-- Degree-one homology of the filtered two-term complex is the kernel of its
defining map. -/
noncomputable def underlyingComplexHomologyOneIsoKernel
    (aMap : ∀ t, A₁ t ⟶ A₂ t)
    (hcompat : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (F₂.F s t).arrow = (F₁.F s t).arrow ≫ aMap t)
    (t : τ) :
    (underlyingComplex aMap hcompat t).homologyObj 1 ≅ kernel (aMap t) := by
  let FC := underlyingComplex aMap hcompat t
  let S := ShortComplex.mk (FC.d 2) (FC.d 1) (FC.d_comp_d 2)
  have hprev : FC.d 2 = 0 := by
    simp [FC, underlyingComplex, twoTermDiff]
  have hout : FC.d 1 = aMap t := by
    simp [FC, underlyingComplex, twoTermDiff, twoTermObj]
  change S.homology ≅ kernel (aMap t)
  exact (S.asIsoHomologyπ hprev).symm ≪≫ S.cyclesIsoKernel ≪≫
    kernelIsoOfEq hout

/-- Degree-zero homology of the filtered two-term complex is the cokernel of
its defining map. -/
noncomputable def underlyingComplexHomologyZeroIsoCokernel
    (aMap : ∀ t, A₁ t ⟶ A₂ t)
    (hcompat : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (F₂.F s t).arrow = (F₁.F s t).arrow ≫ aMap t)
    (t : τ) :
    (underlyingComplex aMap hcompat t).homologyObj 0 ≅ cokernel (aMap t) := by
  let FC := underlyingComplex aMap hcompat t
  let S := ShortComplex.mk (FC.d 1) (FC.d 0) (FC.d_comp_d 1)
  have hnext : FC.d 0 = 0 := by
    simp [FC, underlyingComplex, twoTermDiff]
  have hin : FC.d 1 = aMap t := by
    simp [FC, underlyingComplex, twoTermDiff, twoTermObj]
  change S.homology ≅ cokernel (aMap t)
  exact S.asIsoHomologyι hnext ≪≫ S.opcyclesIsoCokernel ≪≫
    cokernelIsoOfEq hin

/-- Total homology of the two-term complex, displayed as the direct sum of
its two nonzero homological degrees. -/
noncomputable def underlyingComplexHomologyIsoKernelCokernel
    (aMap : ∀ t, A₁ t ⟶ A₂ t)
    (hcompat : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (F₂.F s t).arrow = (F₁.F s t).arrow ≫ aMap t)
    (t : τ) :
    ((underlyingComplex aMap hcompat t).homologyObj 1 ⊞
      (underlyingComplex aMap hcompat t).homologyObj 0) ≅
      (kernel (aMap t) ⊞ cokernel (aMap t)) :=
  biprod.mapIso
    (underlyingComplexHomologyOneIsoKernel aMap hcompat t)
    (underlyingComplexHomologyZeroIsoCokernel aMap hcompat t)

end TwoTermAbutment

/-! ## Bounded ESS convergence packaged with the abutment formula -/

section Bounded

variable {w' : Type w} [AddCommGroup w'] [DecidableEq w']
variable {E₁ E₂ : SpectralSequence C w'}
variable {τ : Type w}
variable {A₁ A₂ : τ → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
variable {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
variable {cm : ConvergenceMorphism conv₁ conv₂}
variable {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}

/-- The complete bounded abutment package for an extension spectral sequence:
the existing convergence witness together with the source, target, and total
kernel/cokernel identifications. -/
structure BoundedExtensionAbutmentComparison
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : τ) where
  convergence : Convergence (ext.ess t)
    (ext.complex t).homologyObj (ext.complex t).homologyFiltration
  sourceIso : (ext.complex t).homologyObj 1 ≅ kernel (cm.aMap t)
  targetIso : (ext.complex t).homologyObj 0 ≅ cokernel (cm.aMap t)
  totalIso :
    ((ext.complex t).homologyObj 1 ⊞ (ext.complex t).homologyObj 0) ≅
      (kernel (cm.aMap t) ⊞ cokernel (cm.aMap t))

/-- Canonical initial-page/abutment comparison for the bounded extension
spectral sequence. -/
noncomputable def BoundedExtensionSS.abutmentComparison
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : τ) :
    BoundedExtensionAbutmentComparison ext t where
  convergence := ext.weakConvergence t
  sourceIso := underlyingComplexHomologyOneIsoKernel
    cm.aMap cm.filtration_compat t
  targetIso := underlyingComplexHomologyZeroIsoCokernel
    cm.aMap cm.filtration_compat t
  totalIso := underlyingComplexHomologyIsoKernelCokernel
    cm.aMap cm.filtration_compat t

end Bounded

end KIPBase.SpectralSequence
