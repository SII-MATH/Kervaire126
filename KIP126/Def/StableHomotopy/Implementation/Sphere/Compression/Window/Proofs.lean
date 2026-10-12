module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Window.Data
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Fibers.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Proofs
public import KIP126.Def.Topology.Cube.Compression.Window.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Set KIP126.Topology.Cube
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

private theorem open_window_not_boundary {N : Type*} (a b t : N → I)
    (ht : ∀ i, a i < t i ∧ t i < b i) : t ∉ _root_.Cube.boundary N := by
  rintro ⟨i, hi | hi⟩
  · have h : (0 : I) < t i := lt_of_le_of_lt bot_le (ht i).1
    exact (ne_of_gt h) hi
  · have h : t i < (1 : I) := lt_of_lt_of_le (ht i).2 le_top
    exact (ne_of_lt h) hi

/-- The original basepoint is outside every strict coordinate window. -/
theorem sphereLevel_point_not_mem_window (n : ℕ) (a b : Fin n → I) :
    (sphereLevel n).point ∉ sphereWindow n a b := by
  rintro ⟨t, ht, he⟩
  exact open_window_not_boundary a b t ht ((sphereCube_eq_point_iff_boundary n t).mp he)

/-- Membership in the spherical window is detected by the original
cube coordinates, even on the collapsed cube boundary. -/
theorem sphereCube_mem_window_iff (n : ℕ) (a b : Fin n → I) (t : Fin n → I) :
    sphereCube n t ∈ sphereWindow n a b ↔ ∀ i, a i < t i ∧ t i < b i := by
  constructor
  · rintro ⟨u, hu, he⟩
    rcases (sphereCube_eq_iff n u t).mp he with rfl | ⟨hb, _⟩
    · exact hu
    · exact False.elim (open_window_not_boundary a b u hu hb)
  · exact fun ht => ⟨t, ht, rfl⟩

/-- The exact fiber over the original basepoint consists of the whole
complement of the chosen window, and no point of its interior. -/
theorem sphereWindowCompression_eq_point_iff (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) (x : sphereLevel n) :
    (sphereWindowCompression n a b hab).map x = (sphereLevel n).point ↔
      x ∉ sphereWindow n a b := by
  rcases sphereLevel_eq_point_or_sphereCube n x with rfl | ⟨t, rfl⟩
  · exact iff_of_true (sphereWindowCompression n a b hab).point
      (sphereLevel_point_not_mem_window n a b)
  · rw [sphereWindowCompression_cube, sphereCube_eq_point_iff_boundary,
      sphereCube_mem_window_iff]
    simpa only [not_not] using not_congr (windowCompression_mem_interior_iff a b hab t)

/-- The same fixed-sphere compression is surjective; an explicit
preimage of a canonical cube point is its affine window expansion. -/
theorem sphereWindowCompression_surjective (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    Function.Surjective (sphereWindowCompression n a b hab).map := by
  intro x
  rcases sphereLevel_eq_point_or_sphereCube n x with rfl | ⟨t, rfl⟩
  · exact ⟨(sphereLevel n).point, (sphereWindowCompression n a b hab).point⟩
  · refine ⟨sphereCube n (windowExpansion a b t), ?_⟩
    rw [sphereWindowCompression_cube, windowCompression_expansion a b hab]

/-- Distinct window points have distinct images under the original
sphere compression. -/
theorem sphereWindowCompression_injOn_window (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    Set.InjOn (sphereWindowCompression n a b hab).map (sphereWindow n a b) := by
  rintro x ⟨t, ht, rfl⟩ y ⟨u, hu, rfl⟩ he
  rw [sphereWindowCompression_cube, sphereWindowCompression_cube] at he
  have hc := sphereCube_injOn_interior n
    ((windowCompression_mem_interior_iff a b hab t).mpr ht)
    ((windowCompression_mem_interior_iff a b hab u).mpr hu) he
  have h := congrArg (windowExpansion a b) hc
  rw [windowExpansion_compression a b hab t (fun i => ⟨(ht i).1.le, (ht i).2.le⟩),
    windowExpansion_compression a b hab u (fun i => ⟨(hu i).1.le, (hu i).2.le⟩)] at h
  exact congrArg (sphereCube n) h

/-- These are all fibers of the actual fixed-sphere compression. -/
theorem sphereWindowCompression_eq_iff (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) (x y : sphereLevel n) :
    (sphereWindowCompression n a b hab).map x =
        (sphereWindowCompression n a b hab).map y ↔
      x = y ∨ (x ∉ sphereWindow n a b ∧ y ∉ sphereWindow n a b) := by
  constructor
  · intro he
    by_cases hx : x ∈ sphereWindow n a b
    · have hy : y ∈ sphereWindow n a b := by
        by_contra hy
        exact (sphereWindowCompression_eq_point_iff n a b hab x).mp
          (he.trans ((sphereWindowCompression_eq_point_iff n a b hab y).mpr hy)) hx
      exact Or.inl (sphereWindowCompression_injOn_window n a b hab hx hy he)
    · exact Or.inr ⟨hx, (sphereWindowCompression_eq_point_iff n a b hab y).mp
        (he.symm.trans ((sphereWindowCompression_eq_point_iff n a b hab x).mpr hx))⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [(sphereWindowCompression_eq_point_iff n a b hab x).mpr hx,
        (sphereWindowCompression_eq_point_iff n a b hab y).mpr hy]

/-- The actual spherical coordinate window is open. -/
theorem sphereWindow_isOpen (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) : IsOpen (sphereWindow n a b) := by
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  have he : sphereWindow n a b = (sphereWindowCompression n a b hab).map ⁻¹'
      ({(sphereLevel n).point}ᶜ : Set (sphereLevel n)) := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff,
      sphereWindowCompression_eq_point_iff, not_not]
  rw [he]
  exact isClosed_singleton.isOpen_compl.preimage
    (sphereWindowCompression n a b hab).map.continuous

/-- The original compression induces an actual homeomorphism from the
complement quotient to the original fixed sphere. The forward map is
exactly the original compression on every quotient representative. -/
theorem exists_sphereWindow_collapse_homeomorph (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    ∃ e : Quot (fun x y : sphereLevel n =>
        x ∉ sphereWindow n a b ∧ y ∉ sphereWindow n a b) ≃ₜ sphereLevel n,
      ∀ x, e (Quot.mk _ x) = (sphereWindowCompression n a b hab).map x := by
  letI := sphereLevel_compactSpace n
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  let q := (sphereWindowCompression n a b hab).map
  have hr : ∀ x y : sphereLevel n,
      (x ∉ sphereWindow n a b ∧ y ∉ sphereWindow n a b) → q x = q y := by
    intro x y h
    exact (sphereWindowCompression_eq_iff n a b hab x y).mpr (Or.inr h)
  let g : Quot (fun x y : sphereLevel n =>
      x ∉ sphereWindow n a b ∧ y ∉ sphereWindow n a b) → sphereLevel n := Quot.lift q hr
  have hg : Function.Bijective g := by
    constructor
    · intro x y he
      induction x using Quot.inductionOn with
      | h x =>
        induction y using Quot.inductionOn with
        | h y =>
          rcases (sphereWindowCompression_eq_iff n a b hab x y).mp he with rfl | h
          · rfl
          · exact Quot.sound h
    · intro y
      obtain ⟨x, hx⟩ := sphereWindowCompression_surjective n a b hab y
      exact ⟨Quot.mk _ x, hx⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg)
    (continuous_quot_lift hr q.continuous), fun _ => rfl⟩

/-- On the actual window, the original sphere compression is a
homeomorphism onto the original sphere with its basepoint removed. -/
theorem exists_sphereWindowCompression_homeomorph (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    ∃ e : sphereWindow n a b ≃ₜ
        ({(sphereLevel n).point}ᶜ : Set (sphereLevel n)),
      ∀ x, (e x).val = (sphereWindowCompression n a b hab).map x.val := by
  letI := sphereLevel_compactSpace n
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  let S : Set (sphereLevel n) := {(sphereLevel n).point}ᶜ
  let q := (sphereWindowCompression n a b hab).map
  have hq : _root_.Topology.IsQuotientMap q :=
    q.continuous.isClosedMap.isQuotientMap q.continuous
      (sphereWindowCompression_surjective n a b hab)
  have hs : q ⁻¹' S = sphereWindow n a b := by
    ext x
    simp only [mem_preimage, S, mem_compl_iff, mem_singleton_iff, q,
      sphereWindowCompression_eq_point_iff, not_not]
  let r := S.restrictPreimage q
  have hr : _root_.Topology.IsQuotientMap r :=
    hq.restrictPreimage_isOpen isClosed_singleton.isOpen_compl
  have hi : Function.Injective r := by
    intro x y h
    apply Subtype.ext
    apply sphereWindowCompression_injOn_window n a b hab
    · exact hs ▸ x.property
    · exact hs ▸ y.property
    · exact congrArg Subtype.val h
  let e := (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hr, hi⟩).homeomorph r
  exact ⟨(Homeomorph.setCongr hs.symm).trans e, fun _ => rfl⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
