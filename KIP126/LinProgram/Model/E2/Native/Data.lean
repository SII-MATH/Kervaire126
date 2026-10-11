import KIP126.LinProgram.Model.E2.Proofs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! The untruncated algebra on exactly the fixed native generators and relations.
The old `LinE2.E2` keeps its original meaning and is a quotient of this algebra. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace KIP126.LinE2
open KIP126.Core.Algebra
noncomputable section

/-- Only the original CSV relations, with no artificial high-degree zeros. -/
def nativeIdeal : Ideal Poly :=
  Ideal.span {p | ∃ code ∈ RawData.relations, p = relationPolynomial code}

abbrev NativeAlgebra := Poly ⧸ nativeIdeal

def nativeProjection : Poly →ₐ[F2] NativeAlgebra := Ideal.Quotient.mkₐ F2 nativeIdeal

def nativeGenerator (i : Generator) : NativeAlgebra := nativeProjection (MvPolynomial.X i)

/-- The image of the weighted homogeneous polynomial component. -/
def nativeHomogeneousPart (s t : ℕ) : Submodule F2 NativeAlgebra :=
  (MvPolynomial.weightedHomogeneousSubmodule F2 generatorDegree (s,t)).map
    nativeProjection.toLinearMap

abbrev NativeAt (s t : ℕ) := ↥(nativeHomogeneousPart s t)

theorem nativeIdeal_le_definingIdeal : nativeIdeal ≤ definingIdeal :=
  Ideal.span_mono (fun _ h => Or.inl h)

/-- Compatibility with the historical truncated quotient; this is not an Ext comparison. -/
def truncate : NativeAlgebra →ₐ[F2] E2 :=
  Ideal.Quotient.factorₐ F2 nativeIdeal_le_definingIdeal

@[simp] theorem truncate_projection (p : Poly) : truncate (nativeProjection p) = projection p := rfl
@[simp] theorem truncate_generator (i : Generator) : truncate (nativeGenerator i) = generator i := rfl

/-- Every original relation vanishes in the untruncated algebra. -/
theorem native_csv_relation_zero (code : String) (h : code ∈ RawData.relations) :
    nativeProjection (relationPolynomial code) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨code, h, rfl⟩)

theorem native_multiply_mem {s t s' t' : ℕ} {x y : NativeAlgebra}
    (hx : x ∈ nativeHomogeneousPart s t) (hy : y ∈ nativeHomogeneousPart s' t') :
    x * y ∈ nativeHomogeneousPart (s+s') (t+t') := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨p*q, MvPolynomial.IsWeightedHomogeneous.mul hp hq, map_mul nativeProjection p q⟩

def nativeMultiply {s t s' t' : ℕ} (x : NativeAt s t) (y : NativeAt s' t') :
    NativeAt (s+s') (t+t') := ⟨x.val*y.val, native_multiply_mem x.property y.property⟩

@[simp] theorem nativeMultiply_val {s t s' t' : ℕ} (x : NativeAt s t) (y : NativeAt s' t') :
    (nativeMultiply x y).val = x.val*y.val := rfl

theorem native_generator_mem (i : Generator) :
    nativeGenerator i ∈ nativeHomogeneousPart (generatorDegree i).1 (generatorDegree i).2 := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.X i, ?_, rfl⟩
  change MvPolynomial.IsWeightedHomogeneous generatorDegree (MvPolynomial.X i) _
  simpa only [Prod.mk.eta] using MvPolynomial.isWeightedHomogeneous_X F2 generatorDegree i

end
end KIP126.LinE2
