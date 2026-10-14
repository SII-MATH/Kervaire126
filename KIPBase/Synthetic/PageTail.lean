import KIPBase.SpectralSequence.Basic

/-!
# Starting the nested-subobject data at a later page

At page `k`, the new ambient object is exactly `Z_k / B_k`.  The later
cycles and boundaries are their images in this quotient.  The index `n`
below measures the distance from page `k`; in particular `n = 0` refers
to the new starting page.
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

/-- The three object/subobject components of the data starting at page `k`.
This records the rebasing operation itself; it does not assert the
`SSData` continuity or differential laws. -/
structure PageTailData (C : Type u) [Category.{v} C] [Abelian C] where
  V : C
  Z : WithTop ℕ → Subobject V
  B : WithTop ℕ → Subobject V

namespace SSData

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pageTail_index_le (k : ℕ) (n : WithTop ℕ) :
    (k : WithTop ℕ) ≤ (k : WithTop ℕ) + n := by
  calc
    (k : WithTop ℕ) = (k : WithTop ℕ) + 0 := by simp
    _ ≤ (k : WithTop ℕ) + n := by
      simpa [add_comm] using
        (add_le_add_left (show (0 : WithTop ℕ) ≤ n from bot_le)
          (k : WithTop ℕ))

/-- The old page `k`, used as the ambient object for the new sequence. -/
noncomputable def pageTailV (D : SSData C) (k : ℕ) : C :=
  D.page (k : WithTop ℕ)

/-- The image of `Z_(k+n)` in `Z_k / B_k`. -/
noncomputable def pageTailZ (D : SSData C) (k : ℕ) (n : WithTop ℕ) :
    Subobject (D.pageTailV k) :=
  imageSubobject
    (Subobject.ofLE (D.Z ((k : WithTop ℕ) + n)) (D.Z k)
      (D.Z_anti (pageTail_index_le k n)) ≫ D.pageπ k)

/-- The image of `B_(k+n)` in `Z_k / B_k`. -/
noncomputable def pageTailB (D : SSData C) (k : ℕ) (n : WithTop ℕ) :
    Subobject (D.pageTailV k) :=
  imageSubobject
    (Subobject.ofLE (D.B ((k : WithTop ℕ) + n)) (D.Z k)
      (le_trans (D.B_le_Z _) (D.Z_anti (pageTail_index_le k n))) ≫ D.pageπ k)

/-- Rebase the object and its cycle/boundary towers at page `k`.
The resulting ambient object is definitionally the old `Z_k / B_k`. -/
noncomputable def pageTail (D : SSData C) (k : ℕ) : PageTailData C where
  V := D.pageTailV k
  Z := D.pageTailZ k
  B := D.pageTailB k

@[simp] theorem pageTail_V (D : SSData C) (k : ℕ) :
    (D.pageTail k).V = D.page (k : WithTop ℕ) := rfl

end SSData

namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type*} [AddCommGroup ι] [DecidableEq ι]

/-- At every grading index, start the spectral-sequence data at page `k`.
Its ambient object is the original `E_k` at that index. -/
noncomputable def pageTailData (E : SpectralSequence C ι) (k : ℤ) (i : ι) :
    PageTailData C :=
  (E.ssData i).pageTail (k - E.r₀).toNat

@[simp] theorem pageTailData_V (E : SpectralSequence C ι) (k : ℤ) (i : ι) :
    (E.pageTailData k i).V = E.Page k i := rfl

end SpectralSequence

end KIPBase.SpectralSequence
