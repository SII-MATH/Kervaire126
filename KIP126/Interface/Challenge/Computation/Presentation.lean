module

public import KIP126.Def.StageInput.StandardSphere.Algebra.Proofs
public import KIP126.LinProgram.Model.Classes.Data
public import KIP126.LinProgram.Model.E2.Native.Grading
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section


/-! One global graded algebra map, bijective in internal degrees at most 261.
The legacy truncated quotient is only a bounded coordinate compatibility view.
No raw differential row or certification result is supplied by this object. -/

namespace KIP126.Classical.Adams
open KIP126.Core.Algebra KIP126.LinE2 Sphere.Internal

noncomputable section

/-- Restrict one global map to a homogeneous component, using the injective
inclusion of the *same* actual page into its total direct sum. -/
def linE2ComponentMap (f : NativeAlgebra →ₐ[F2] ActualE2Total)
    (hf : ∀ s t (x : NativeAt s t),
      f x.val ∈ LinearMap.range (embed (s, t))) (s t : ℕ) :
    NativeAt s t →ₗ[F2] ActualE2At (s, t) :=
  LinearMap.codRestrictOfInjective
    (f.toLinearMap.comp (nativeHomogeneousPart s t).subtype)
    (embed (s, t)) (embed_injective (s, t)) (hf s t)

/-- The original-relation quotient maps globally to the fixed actual sphere E₂.
All natural bidegrees are retained. Only bijectivity has the bound t ≤ 261.
In particular, the actual multiplication is fixed in Def before this object. -/
structure LinE2Presentation where
  toActual : NativeAlgebra →ₐ[F2] ActualE2Total
  preservesDegree : ∀ s t (x : NativeAt s t),
    toActual x.val ∈ LinearMap.range (embed (s, t))
  component_bijective : ∀ (s t : ℕ), t ≤ 261 →
    Function.Bijective (linE2ComponentMap toActual preservesDegree s t)

namespace LinE2Presentation

/-- The component map is derived from the single global algebra map. -/
abbrev component (P : LinE2Presentation) (s t : ℕ) :=
  linE2ComponentMap P.toActual P.preservesDegree s t

@[simp] theorem embed_component (P : LinE2Presentation) (s t : ℕ)
    (x : NativeAt s t) :
    embed (s, t) (P.component s t x) = P.toActual x.val :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- The new native comparison, bijective throughout the original full bound. -/
def nativeComparison (P : LinE2Presentation) (s t : ℕ) (ht : t ≤ 261) :
    NativeAt s t ≃ₗ[F2] ActualE2At (s, t) :=
  LinearEquiv.ofBijective (P.component s t) (P.component_bijective s t ht)

/-- Compatibility API on the old truncated model; there is no global map
from that truncated model to the untruncated actual page algebra. -/
def comparison (P : LinE2Presentation) (s t : ℕ) (ht : t ≤ 261) :
    E2At s t ≃ₗ[ℤ] sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) :=
  ((truncateAtEquiv s t ht).symm.trans (P.nativeComparison s t ht)).restrictScalars ℤ

/-- Compatibility name for the fixed actual product. It does not select an
operation and is independent of the presentation. -/
def product (_P : LinE2Presentation) (s t s' t' : ℕ) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) →ₗ[ℤ]
    sphereAdamsData.Page 2 ((s' : ℤ), (t' : ℤ)) →ₗ[ℤ]
      sphereAdamsData.Page 2 (((s + s' : ℕ) : ℤ), ((t + t' : ℕ) : ℤ)) :=
  by
    let f := (actualE2Product (s, t) (s', t')).restrictScalars₁₂ ℤ ℤ
    exact { f.toAddMonoidHom with
      map_smul' := fun n x => map_intCast_smul f.toAddMonoidHom ℤ ℤ n x }

@[simp] theorem embed_comparison (P : LinE2Presentation) (s t : ℕ)
    (ht : t ≤ 261) (x : E2At s t) :
    embed (s, t) (P.comparison s t ht x) =
      P.toActual ((truncateAtEquiv s t ht).symm x).val :=
  P.embed_component s t _

/-- Transport of legacy bounded products is a theorem derived from global
multiplicativity and the proved low-degree truncation equivalence. -/
theorem comparison_mul (P : LinE2Presentation) (s t s' t' : ℕ)
    (h : t + t' ≤ 261) (x : E2At s t) (y : E2At s' t')
    (z : E2At (s + s') (t + t')) (hz : x.val * y.val = z.val) :
    P.comparison (s + s') (t + t') h z =
      P.product s t s' t' (P.comparison s t (by omega) x)
        (P.comparison s' t' (by omega) y) := by
  let a := (truncateAtEquiv s t (by omega)).symm x
  let b := (truncateAtEquiv s' t' (by omega)).symm y
  let c := (truncateAtEquiv (s + s') (t + t') h).symm z
  have ha : truncate a.val = x.val := truncateAtEquiv_symm_apply s t (by omega) x
  have hb : truncate b.val = y.val := truncateAtEquiv_symm_apply s' t' (by omega) y
  have hc : truncate c.val = z.val := truncateAtEquiv_symm_apply (s + s') (t + t') h z
  have hab : nativeMultiply a b = c := by
    apply (truncateAtEquiv (s + s') (t + t') h).injective
    apply Subtype.ext
    rw [truncateAtEquiv_apply_val, truncateAtEquiv_apply_val]
    change truncate (a.val * b.val) = truncate c.val
    rw [map_mul, ha, hb, hc, hz]
  apply embed_injective (s + s', t + t')
  change embed (s + s', t + t') (P.comparison (s + s') (t + t') h z) =
    embed ((s, t) + (s', t'))
      (actualE2Product (s, t) (s', t')
        (P.comparison s t (by omega) x) (P.comparison s' t' (by omega) y))
  rw [embed_product, P.embed_comparison, P.embed_comparison, P.embed_comparison]
  change P.toActual c.val = P.toActual a.val * P.toActual b.val
  rw [← map_mul]
  exact congrArg P.toActual (congrArg Subtype.val hab).symm

end LinE2Presentation
end
end KIP126.Classical.Adams
