import KIP126.Def.SpectralSequence.FilteredComplex.SSDataConstruction.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import KIP126.Mathlib.SpectralSequence.FilteredComplex.Assembly.Data
import KIP126.Def.SpectralSequence.Crossing.Predicates

/-!
# Finite-page comparison with Mathlib's spectral sequence

The nested-subobject `PreSS` and the Mathlib spectral sequence are both built
from the same canonical quotient pages of a filtered complex. These facts
make that shared finite-page object and differential explicit. They do not
claim an adapter for an arbitrary `PreSS`, or a limiting-page comparison.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The historical construction and the Mathlib construction use the same
finite quotient page at each bidegree. -/
theorem toPreSS_page_eq_canonicalPage (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    ((FC.toPreSS bnd).ssData (s, k)).page (n : WithTop ℕ) =
      ((FC.canonicalPageSpectralSequence).page (n : ℤ)
        (Int.natCast_nonneg n)).X (s, k) := by
  rfl

/-- On those common pages, the old `PreSS` differential is the Mathlib
spectral-sequence page differential. -/
theorem toPreSS_d_eq_canonicalPage_d (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    (FC.toPreSS bnd).d (n : ℤ) (s, k) =
      ((FC.canonicalPageSpectralSequence).page (n : ℤ)
        (Int.natCast_nonneg n)).d (s, k) (s + (n : ℤ), k - 1) := by
  rw [FC.toPreSS_d_nat]
  change FC.pageDifferential s k n =
    FC.pageDifferentialHom n (s, k) (s + (n : ℤ), k - 1)
  have hrel : (pageShape n).Rel (s, k) (s + (n : ℤ), k - 1) := by
    change (s, k) + ((n : ℤ), -1) = (s + (n : ℤ), k - 1)
    simp [Int.sub_eq_add_neg]
  rw [FC.pageDifferentialHom_of_rel n (s, k) (s + (n : ℤ), k - 1) hrel]
  simp

/-- The fully assembled nested-subobject spectral sequence retains exactly
the finite-page objects already compared for `toPreSS`. -/
theorem toSpectralSequence_page_eq_canonicalPage (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    ((FC.toSpectralSequence bnd).ssData (s, k)).page (n : WithTop ℕ) =
      ((FC.canonicalPageSpectralSequence).page (n : ℤ)
        (Int.natCast_nonneg n)).X (s, k) := by
  change ((FC.toPreSS bnd).ssData (s, k)).page (n : WithTop ℕ) = _
  exact FC.toPreSS_page_eq_canonicalPage bnd s k n

/-- The assembled nested-subobject differential is the Mathlib differential
on the common finite quotient page. -/
theorem toSpectralSequence_d_eq_canonicalPage_d (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    (FC.toSpectralSequence bnd).d (n : ℤ) (s, k) =
      ((FC.canonicalPageSpectralSequence).page (n : ℤ)
        (Int.natCast_nonneg n)).d (s, k) (s + (n : ℤ), k - 1) := by
  change (FC.toPreSS bnd).d (n : ℤ) (s, k) = _
  exact FC.toPreSS_d_eq_canonicalPage_d bnd s k n

private theorem toSpectralSequence_source_pageπ (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    ((FC.toSpectralSequence bnd).ssData (s, k)).pageπ
        (↑((n : ℤ) - (FC.toSpectralSequence bnd).r₀).toNat : WithTop ℕ) =
      FC.pageπ s k (n : WithTop ℕ) := by
  change (FC.toSSData bnd s k).pageπ
    (↑((n : ℤ) - 0).toNat : WithTop ℕ) = FC.pageπ s k (n : WithTop ℕ)
  rfl

private theorem toSpectralSequence_target_pageπ (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    ((FC.toSpectralSequence bnd).ssData
        ((s, k) + (FC.toSpectralSequence bnd).diffDeg (n : ℤ))).pageπ
        (↑((n : ℤ) - (FC.toSpectralSequence bnd).r₀).toNat : WithTop ℕ) =
      FC.pageπ (s + (n : ℤ)) (k - 1) (n : WithTop ℕ) := by
  change (FC.toSSData bnd (s + (n : ℤ)) (k + -1)).pageπ
    (↑((n : ℤ) - 0).toNat : WithTop ℕ) =
    FC.pageπ (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)
  rfl

private theorem toSpectralSequence_relation_of_eq (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) {T : C}
    (x : T ⟶ FC.filtration.associatedGraded s k)
    (y : T ⟶ FC.filtration.associatedGraded (s + (n : ℤ)) (k - 1))
    (xZ : T ⟶ Subobject.underlying.obj (FC.cycleSubobject s k (n : WithTop ℕ)))
    (yZ : T ⟶ Subobject.underlying.obj
      (FC.cycleSubobject (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)))
    (hx : xZ ≫ (FC.cycleSubobject s k (n : WithTop ℕ)).arrow = x)
    (hy : yZ ≫ (FC.cycleSubobject (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)).arrow = y)
    (δ : ((FC.toSpectralSequence bnd).ssData (s, k)).page (n : WithTop ℕ) ⟶
      ((FC.toSpectralSequence bnd).ssData
        ((s, k) + (FC.toSpectralSequence bnd).diffDeg (n : ℤ))).page (n : WithTop ℕ))
    (hδ : (FC.toSpectralSequence bnd).d (n : ℤ) (s, k) = δ)
    (hd : xZ ≫ FC.pageπ s k (n : WithTop ℕ) ≫ δ =
      yZ ≫ FC.pageπ (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)) :
    DifferentialRelation (FC.toSpectralSequence bnd) (n : ℤ) (s, k) x y := by
  refine ⟨xZ, hx, yZ, hy, ?_⟩
  rw [FC.toSpectralSequence_source_pageπ bnd s k n]
  rw [FC.toSpectralSequence_target_pageπ bnd s k n]
  rw [hδ]
  exact hd

/-- The multivalued relation on associated-graded representatives in the
nested-subobject construction is precisely equality of their classes after
applying the Mathlib page differential. The target representative itself need
not be unique; only its quotient-page class is fixed. -/
theorem toSpectralSequence_relation_iff (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) {T : C}
    (x : T ⟶ FC.filtration.associatedGraded s k)
    (y : T ⟶ FC.filtration.associatedGraded (s + (n : ℤ)) (k - 1)) :
    DifferentialRelation (FC.toSpectralSequence bnd) (n : ℤ) (s, k) x y ↔
      ∃ (xZ : T ⟶ Subobject.underlying.obj (FC.cycleSubobject s k (n : WithTop ℕ)))
        (yZ : T ⟶ Subobject.underlying.obj
          (FC.cycleSubobject (s + (n : ℤ)) (k - 1) (n : WithTop ℕ))),
        xZ ≫ (FC.cycleSubobject s k (n : WithTop ℕ)).arrow = x ∧
        yZ ≫ (FC.cycleSubobject (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)).arrow = y ∧
        xZ ≫ FC.pageπ s k (n : WithTop ℕ) ≫
          ((FC.canonicalPageSpectralSequence).page (n : ℤ)
            (Int.natCast_nonneg n)).d (s, k) (s + (n : ℤ), k - 1) =
          yZ ≫ FC.pageπ (s + (n : ℤ)) (k - 1) (n : WithTop ℕ) := by
  constructor
  · rintro ⟨xZ, hx, yZ, hy, hd⟩
    refine ⟨xZ, yZ, hx, hy, ?_⟩
    change xZ ≫ FC.pageπ s k (n : WithTop ℕ) ≫
      (FC.toSpectralSequence bnd).d (n : ℤ) (s, k) =
      yZ ≫ FC.pageπ (s + (n : ℤ)) (k - 1) (n : WithTop ℕ) at hd
    rw [FC.toSpectralSequence_d_eq_canonicalPage_d bnd s k n] at hd
    exact hd
  · rintro ⟨xZ, yZ, hx, hy, hd⟩
    exact FC.toSpectralSequence_relation_of_eq bnd s k n x y xZ yZ hx hy
      _ (FC.toSpectralSequence_d_eq_canonicalPage_d bnd s k n) hd

end KIP126.Core.SpectralSequence.FilteredComplex
