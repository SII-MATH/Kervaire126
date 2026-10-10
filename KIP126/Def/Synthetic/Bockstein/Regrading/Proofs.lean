import KIP126.Def.Synthetic.Bockstein.Regrading.Data
import KIP126.Def.Synthetic.Bockstein.Tower.Proofs

/-!
# Laws and page checkpoints for the actual λ regrading

The square-zero and successor statements concern the constructed maps.
Their proofs are separated from the data; none is an extra model
input or an independently chosen spectral sequence.
-/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence

set_option backward.isDefEq.respectTransparency false

universe u v

@[simp] theorem gradingEquiv_apply (k n w : ℤ) :
    gradingEquiv (k, n, w) = (w + k - n, w + k, w) := rfl

@[simp] theorem gradingEquiv_symm_apply (s t w : ℤ) :
    gradingEquiv.symm (s, t, w) = (t - w, t - s, w) := rfl

/-- Raw differential degree `(q,-1,0)` becomes the synthetic degree of
page `q+1`. -/
theorem gradingEquiv_differentialDegree (q : ℤ) :
    gradingEquiv (q, -1, 0) = syntheticAdamsRawShift (q + 1) := by
  apply Prod.ext
  · simp [gradingEquiv, syntheticAdamsRawShift]
  · apply Prod.ext <;> simp [gradingEquiv, syntheticAdamsRawShift]

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

@[simp] theorem normalizedPreSS_firstPage (A : Syn) :
    (normalizedPreSS A).r₀ = 2 := rfl

@[simp] theorem normalizedPreSS_diffDeg (A : Syn) (r : ℤ) :
    (normalizedPreSS A).diffDeg r = syntheticAdamsRawShift r := rfl

/-- The ambient and all nested subobjects are unchanged under regrading. -/
theorem normalizedSSData_eq_weightwise (A : Syn) (i : Tridegree) :
    normalizedSSData A i =
      (weightwiseSequence A i.2.2).ssData (i.2.1 - i.2.2, i.2.1 - i.1) := rfl

/-- Normalized page `r` is precisely raw page `r-1`, including both the
initial `E₂ = raw E₁` and the next `E₃ = raw E₂` checkpoints. -/
theorem normalizedPage_eq_weightwisePage (A : Syn) (r : ℤ) (i : Tridegree) :
    (normalizedPreSS A).Page r i =
      (weightwiseSequence A i.2.2).Page (r - 1)
        (i.2.1 - i.2.2, i.2.1 - i.1) := by
  change (normalizedSSData A i).page ((r - 2).toNat : WithTop ℕ) =
    (normalizedSSData A i).page (((r - 1) - 1).toNat : WithTop ℕ)
  exact congrArg (fun z : ℤ => (normalizedSSData A i).page (z.toNat : WithTop ℕ))
    (by omega : r - 2 = (r - 1) - 1)

/-- The infinity quotient is also that of the very same actual tower. -/
theorem normalizedInfinity_eq_weightwiseInfinity (A : Syn) (i : Tridegree) :
    (normalizedSSData A i).eInfty =
      ((weightwiseSequence A i.2.2).ssData
        (i.2.1 - i.2.2, i.2.1 - i.1)).eInfty := rfl

theorem normalizedPreSS_d_comp_d (A : Syn) (r : ℤ) (i : Tridegree) :
    (normalizedPreSS A).d r i ≫
      (normalizedPreSS A).d r (i + (normalizedPreSS A).diffDeg r) = 0 := by
  by_cases hr : 2 ≤ r
  · dsimp only [normalizedPreSS]
    simp only [dif_pos hr, syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add]
    rw [Category.assoc]
    rw [TowerSpectralSequence.internalD_transport_assoc (lambdaTower A) (Smn 0 i.2.2)
      (Smn 0 (i.2.2 + 0)) (by rw [add_zero]) (r - 2).toNat
      (i.2.1 - i.2.2 + ((r - 2).toNat + 1 : ℕ)) (i.2.1 - i.1 - 1)
      (i.2.1 + (r - 1) - (i.2.2 + 0)) (i.2.1 + (r - 1) - (i.1 + r))
      (by omega) (by omega)]
    rw [← Category.assoc, TowerSpectralSequence.internalD_comp, zero_comp]
  · simp only [normalizedPreSS, dif_neg hr, zero_comp]

theorem normalizedPreSS_Z_succ (A : Syn) (r : ℤ) (i : Tridegree) (hr : 2 ≤ r) :
    let m := (r - 2).toNat
    kernelSubobject ((normalizedPreSS A).d r i) =
      imageSubobject (Subobject.ofLE
        (((normalizedPreSS A).ssData i).Z ((m + 1 : ℕ) : WithTop ℕ))
        (((normalizedPreSS A).ssData i).Z (m : WithTop ℕ))
        (((normalizedPreSS A).ssData i).Z_anti
          (by exact_mod_cast Nat.le_succ m)) ≫
        ((normalizedPreSS A).ssData i).pageπ (m : WithTop ℕ)) := by
  simp only [normalizedPreSS, dif_pos hr, kernelSubobject_comp_mono]
  exact TowerSpectralSequence.internalD_kernel (lambdaTower A) (Smn 0 i.2.2)
    (i.2.1 - i.2.2) (i.2.1 - i.1) (r - 2).toNat

theorem normalizedPreSS_B_succ (A : Syn) (r : ℤ) (i : Tridegree) (hr : 2 ≤ r) :
    let m := (r - 2).toNat
    let D := (normalizedPreSS A).ssData (i + (normalizedPreSS A).diffDeg r)
    imageSubobject ((normalizedPreSS A).d r i) =
      imageSubobject (Subobject.ofLE (D.B ((m + 1 : ℕ) : WithTop ℕ))
        (D.Z (m : WithTop ℕ))
        (le_trans (D.B_le_Z ((m + 1 : ℕ) : WithTop ℕ))
          (D.Z_anti (by exact_mod_cast Nat.le_succ m))) ≫
        D.pageπ (m : WithTop ℕ)) := by
  simp only [normalizedPreSS, dif_pos hr]
  apply TowerSpectralSequence.internalD_image_of_target_eq
  simp only [normalizedSSData, syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add, add_zero]
  congr 1 <;> omega

end KIP126.Synthetic.Bockstein
