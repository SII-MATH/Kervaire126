import KIP126.Mathlib.SpectralSequence.FilteredComplex.FinitePage.Proofs

/-! Assemble the proved internal `Z/B` pages as a Mathlib spectral sequence. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical quotient pages of a filtered complex, assembled as a
Mathlib spectral sequence. -/
noncomputable def canonicalPageSpectralSequence (FC : FilteredComplex C) :
    CategoryTheory.SpectralSequence C (fun r : ℤ => pageShape r.toNat) 0 where
  page r hr := FC.pageComplex r.toNat
  iso r r' p hrr' hr := by
    subst r'
    exact FC.pageHomologyIso r.toNat p ≪≫ eqToIso (by
      change FC.pageObj p.1 p.2 (↑(r.toNat + 1) : WithTop ℕ) =
        FC.pageObj p.1 p.2 (↑((r + 1).toNat) : WithTop ℕ)
      congr 2
      omega)

end KIP126.Core.SpectralSequence.FilteredComplex
