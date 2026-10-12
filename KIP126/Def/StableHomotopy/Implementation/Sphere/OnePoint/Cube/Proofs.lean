module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Cube.Data
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Interior.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Reflection

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open scoped unitInterval

/-- Reflection about the interval midpoint is literal negation in
the specified real coordinate on the interval interior. -/
theorem intervalInteriorHomeomorphReal_symm
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    intervalInteriorHomeomorphReal
      ⟨unitInterval.symm t.val, by
        constructor
        · simpa using t.property.2
        · simpa using t.property.1⟩ = -intervalInteriorHomeomorphReal t := by
  unfold intervalInteriorHomeomorphReal orderIsoIooNegOneOne
  change (2 * (1 - (t.val : ℝ)) - 1) / (1 - |2 * (1 - (t.val : ℝ)) - 1|) =
    -((2 * (t.val : ℝ) - 1) / (1 - |2 * (t.val : ℝ) - 1|))
  have he : 2 * (1 - (t.val : ℝ)) - 1 = -(2 * (t.val : ℝ) - 1) := by ring
  rw [he, abs_neg, neg_div]

end KIP126.StableHomotopy.Implementation.BasedSpace

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Set BasedSpace
open scoped unitInterval OnePoint
set_option backward.isDefEq.respectTransparency false

/-- The original sphere has an actual one-point compactification chart
whose values on the original cube are exactly the specified coordinatewise
real coordinates. This retains coordinate reflections literally. -/
theorem exists_sphereLevel_onePoint_cube_homeomorph (n : ℕ) :
    ∃ e : sphereLevel (n + 1) ≃ₜ OnePoint (Fin (n + 1) → ℝ),
      e (sphereLevel (n + 1)).point = ∞ ∧
      ∀ t : ((_root_.Cube.boundary (Fin (n + 1)))ᶜ : Set (Fin (n + 1) → I)),
        e (sphereCube (n + 1) t.val) =
          (cubeInteriorHomeomorphReal (Fin (n + 1)) t : OnePoint (Fin (n + 1) → ℝ)) := by
  letI := sphereLevel_compactSpace (n + 1)
  letI := (exists_sphereLevel_homeomorph_onePoint (n + 1)).choose.isEmbedding.t2Space
  obtain ⟨c, hc⟩ := exists_sphereCube_interior_homeomorph n
  let q := (cubeInteriorHomeomorphReal (Fin (n + 1))).symm.trans c
  let f : (Fin (n + 1) → ℝ) → sphereLevel (n + 1) := fun x => (q x).val
  have hf : _root_.Topology.IsEmbedding f :=
    _root_.Topology.IsEmbedding.subtypeVal.comp q.isEmbedding
  have hr : Set.range f = {(sphereLevel (n + 1)).point}ᶜ := by
    rw [show f = Subtype.val ∘ q from rfl, Set.range_comp, q.surjective.range_eq,
      Set.image_univ, Subtype.range_coe_subtype]
    rfl
  let e := OnePoint.equivOfIsEmbeddingOfRangeEq (sphereLevel (n + 1)).point f hf hr
  refine ⟨e.symm, ?_, ?_⟩
  · apply e.injective
    rw [e.apply_symm_apply]
    rfl
  · intro t
    apply e.injective
    rw [e.apply_symm_apply]
    change sphereCube (n + 1) t.val =
      (q (cubeInteriorHomeomorphReal (Fin (n + 1)) t)).val
    dsimp [q]
    rw [Homeomorph.symm_apply_apply, hc]
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
