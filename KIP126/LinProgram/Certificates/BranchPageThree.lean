module

public import KIP126.LinProgram.Certificates.BranchD2Coordinates
public import KIP126.Def.SpectralSequence.Computation.PageThree.Proofs

@[expose] public section


/-! Conditional transport of the complete fixed 5 → 4 → 4 native matrix
certificate to the existing third page of an arbitrary module spectral
sequence. The inputs are full actual E₂ coordinate isomorphisms and full
actual d₂ commutation equations. They are not supplied by the database.
No actual CW object, source continuation, coverage, or total delivery is
constructed or assumed here. -/
namespace KIP126.LinProgram.BranchPageThree

open CategoryTheory KIP126.Core KIP126.Core.SpectralSequence
open BranchD2Coordinates
universe v

/-- Every third-page class has exactly one of the four fixed native quotient
representatives, provided the complete incoming, middle, and outgoing E₂
coordinates compare with this spectral sequence and both d₂ squares commute
on all vectors. As `p` varies the middle degree ranges over every degree.
For the native CW target, the remaining application must establish the actual
sequence, its d₂ shift `(2,1)`, and these comparisons at `(16,145)`, `(18,146)`,
and `(20,147)`. This theorem supplies none of those actual comparisons. -/
theorem representatives
    (E : SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)) (hstart : E.r₀ ≤ 2)
    (p : ℤ × ℤ)
    (eIncoming : Coordinates 5 ≃ₗ[ℤ] E.Page 2 p)
    (eMiddle : Coordinates 4 ≃ₗ[ℤ] E.Page 2 (p + E.diffDeg 2))
    (eOutgoing : Coordinates 4 ≃ₗ[ℤ] E.Page 2 ((p + E.diffDeg 2) + E.diffDeg 2))
    (incoming_commutes : ∀ v : Coordinates 5,
      E.d 2 p (eIncoming v) = eMiddle (incoming v))
    (outgoing_commutes : ∀ v : Coordinates 4,
      E.d 2 (p + E.diffDeg 2) (eMiddle v) = eOutgoing (outgoing v))
    (y : E.Page 3 (p + E.diffDeg 2)) :
    ∃! i : Fin 4,
      RepresentsOnPage E 3 (p + E.diffDeg 2) (eMiddle (representative i)) y := by
  have range_iff (v : Coordinates 4) :
      eMiddle v ∈ LinearMap.range (E.d 2 p).hom ↔ v ∈ LinearMap.range incoming := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨eIncoming.symm z, eMiddle.injective ?_⟩
      rw [← incoming_commutes, eIncoming.apply_symm_apply]
      exact hz
    · rintro ⟨z, rfl⟩
      exact ⟨eIncoming z, incoming_commutes z⟩
  obtain ⟨x, hx⟩ := PageThree.exists_representative (p + E.diffDeg 2) y
  let v := eMiddle.symm x
  have hv : eMiddle v = x := eMiddle.apply_symm_apply x
  have hcycle : v ∈ LinearMap.ker outgoing := by
    apply eOutgoing.injective
    rw [map_zero, ← outgoing_commutes, hv]
    exact (PageThree.reachesPage_iff_d2_eq_zero hstart (p + E.diffDeg 2) x).mp ⟨y, hx⟩
  have representative_iff (i : Fin 4) :
      RepresentsOnPage E 3 (p + E.diffDeg 2) (eMiddle (representative i)) y ↔
        v - representative i ∈ LinearMap.range incoming := by
    rw [PageThree.represents_iff_sub_mem_d2_range hstart p hx, ← hv, ← map_sub, range_iff]
    simpa only [neg_sub] using
      (Submodule.neg_mem_iff (LinearMap.range incoming) (x := v - representative i))
  obtain ⟨i, hi, huniq⟩ := (kernel_mod_image_representatives v).mp hcycle
  exact ⟨i, (representative_iff i).mpr hi,
    fun j hj => huniq j ((representative_iff j).mp hj)⟩

end KIP126.LinProgram.BranchPageThree
