module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Fibers.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- In positive dimension the original canonical cube is a genuine
quotient map onto the fixed sphere, with no change of its representative. -/
theorem sphereCube_isQuotientMap (n : ℕ) :
    _root_.Topology.IsQuotientMap (sphereCube (n + 1)) := by
  letI := (exists_sphereLevel_homeomorph_onePoint (n + 1)).choose.isEmbedding.t2Space
  have hs : Function.Surjective (sphereCube (n + 1)) := by
    intro x
    rcases sphereLevel_eq_point_or_sphereCube (n + 1) x with rfl | ⟨t, ht⟩
    · exact ⟨fun _ => 0, (sphereCube (n + 1)).property _ ⟨0, Or.inl rfl⟩⟩
    · exact ⟨t, ht.symm⟩
  exact (sphereCube (n + 1)).val.continuous.isClosedMap.isQuotientMap
    (sphereCube (n + 1)).val.continuous hs

/-- The open interior of the original canonical cube is homeomorphic to
the fixed sphere minus its original point. The forward map is exactly
`sphereCube`, so local coordinates retain the original sphere class. -/
theorem exists_sphereCube_interior_homeomorph (n : ℕ) :
    ∃ e : ((_root_.Cube.boundary (Fin (n + 1)))ᶜ : Set (Fin (n + 1) → I)) ≃ₜ
        ({(sphereLevel (n + 1)).point}ᶜ : Set (sphereLevel (n + 1))),
      ∀ t, (e t).val = sphereCube (n + 1) t.val := by
  letI := (exists_sphereLevel_homeomorph_onePoint (n + 1)).choose.isEmbedding.t2Space
  let S : Set (sphereLevel (n + 1)) := {(sphereLevel (n + 1)).point}ᶜ
  let r := S.restrictPreimage (sphereCube (n + 1))
  have hq : _root_.Topology.IsQuotientMap r :=
    (sphereCube_isQuotientMap n).restrictPreimage_isOpen isClosed_singleton.isOpen_compl
  have hi : Function.Injective r := by
    intro x z h
    apply Subtype.ext
    apply sphereCube_injOn_interior (n + 1)
    · intro hb
      exact x.property ((sphereCube_eq_point_iff_boundary (n + 1) x.val).mpr hb)
    · intro hb
      exact z.property ((sphereCube_eq_point_iff_boundary (n + 1) z.val).mpr hb)
    · exact congrArg Subtype.val h
  have he : (sphereCube (n + 1)) ⁻¹' S = (_root_.Cube.boundary (Fin (n + 1)))ᶜ := by
    ext t
    simp only [Set.mem_preimage, S, Set.mem_compl_iff, Set.mem_singleton_iff,
      sphereCube_eq_point_iff_boundary]
  let h := (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hi⟩).homeomorph r
  exact ⟨(Homeomorph.setCongr he.symm).trans h, fun _ => rfl⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
