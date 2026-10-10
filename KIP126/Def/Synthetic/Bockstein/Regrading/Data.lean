import KIP126.Def.Synthetic.Bockstein.Tower.Data
import KIP126.Def.Synthetic.AdamsSequence.Data

/-!
# Regrading the actual λ tower into synthetic Adams conventions

The intrinsic coordinates `(k,n,w)` become `(s,t,w)=(w+k-n,w+k,w)`.
Raw page `q` is normalized page `q+1`; the initial differential is retained
as `d₂`.  The nested subobjects and maps are the actual tower construction,
with the displayed grading and target transports made explicit.
-/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence

universe u v

/-- The additive change from tower index, stem and weight to synthetic
Adams filtration, internal degree and weight. -/
def gradingEquiv : (ℤ × ℤ × ℤ) ≃+ Tridegree where
  toFun p := (p.2.2 + p.1 - p.2.1, p.2.2 + p.1, p.2.2)
  invFun i := (i.2.1 - i.2.2, i.2.1 - i.1, i.2.2)
  left_inv p := by
    rcases p with ⟨k, n, w⟩
    apply Prod.ext
    · dsimp; omega
    · apply Prod.ext <;> dsimp <;> omega
  right_inv i := by
    rcases i with ⟨s, t, w⟩
    apply Prod.ext
    · dsimp; omega
    · apply Prod.ext <;> dsimp <;> omega
  map_add' p q := by
    rcases p with ⟨k, n, w⟩
    rcases q with ⟨k', n', w'⟩
    apply Prod.ext
    · dsimp; omega
    · apply Prod.ext <;> dsimp <;> omega

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The same actual cycle and boundary subobjects at the inverse-regraded
tower degree.  The ambient remains the raw `E₁` group. -/
noncomputable def normalizedSSData (A : Syn) (i : Tridegree) :
    SSData (ModuleCat.{v} ℤ) :=
  TowerSpectralSequence.ssData (lambdaTower A) (Smn 0 i.2.2)
    (i.2.1 - i.2.2) (i.2.1 - i.1)

/-- The actual λ tower data with synthetic Adams page and degree conventions.
For `r ≥ 2` its differential is raw `d_(r-1)` at internal stage `r-2`.
For earlier displayed page numbers the differential is zero, following the
internal `PreSS` convention. -/
noncomputable def normalizedPreSS (A : Syn) :
    PreSS (ModuleCat.{v} ℤ) Tridegree where
  r₀ := 2
  ssData := normalizedSSData A
  diffDeg := syntheticAdamsRawShift
  d r i := if hr : 2 ≤ r then
    TowerSpectralSequence.internalD (lambdaTower A) (Smn 0 i.2.2)
      (r - 2).toNat (i.2.1 - i.2.2) (i.2.1 - i.1) ≫ eqToHom (by
        have hq : (((r - 2).toNat + 1 : ℕ) : ℤ) = r - 1 := by omega
        have hk : i.2.1 - i.2.2 + (((r - 2).toNat + 1 : ℕ) : ℤ) =
            (i.2.1 + (r - 1)) - i.2.2 := by omega
        have hn : i.2.1 - i.1 - 1 = (i.2.1 + (r - 1)) - (i.1 + r) := by omega
        change (TowerSpectralSequence.ssData (lambdaTower A) (Smn 0 i.2.2)
          (i.2.1 - i.2.2 + (((r - 2).toNat + 1 : ℕ) : ℤ)) (i.2.1 - i.1 - 1)).page
            ((r - 2).toNat : WithTop ℕ) =
              (normalizedSSData A (i + syntheticAdamsRawShift r)).page
                ((r - 2).toNat : WithTop ℕ)
        simp only [normalizedSSData, syntheticAdamsRawShift, Prod.fst_add,
          Prod.snd_add, add_zero]
        rw [hk, hn])
    else 0

end KIP126.Synthetic.Bockstein
