import KIP126.Mathlib.SpectralSequence.SSData.Assembly.Data

/-!
# Finite-page comparison for the generic SSData adapter

The Mathlib-facing spectral sequence retains the internal quotient page and
its differential, rather than introducing a second cycle/boundary model.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- The adapted page object is the internal `SSData` quotient page. -/
theorem MathlibAdapter.toMathlib_page_X (E : SpectralSequence C ι)
    (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    ((MathlibAdapter.toMathlib E).page r hr).X k = E.Page r k := by
  rfl

/-- The adapted page differential is the internal `SSData` differential. -/
theorem MathlibAdapter.toMathlib_page_d (E : SpectralSequence C ι)
    (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    ((MathlibAdapter.toMathlib E).page r hr).d k (k + E.diffDeg r) = E.d r k := by
  simp [MathlibAdapter.toMathlib, MathlibAdapter.pageComplex,
    MathlibAdapter.pageShape]

end KIP126.Core.SpectralSequence
