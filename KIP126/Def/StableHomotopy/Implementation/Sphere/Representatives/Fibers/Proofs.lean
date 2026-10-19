module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Compact.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The canonical cube of the original iterated-suspension sphere maps
exactly its cubical boundary to the original basepoint. -/
theorem sphereCube_eq_point_iff_boundary (n : ℕ) (t : Fin n → I) :
    sphereCube n t = (sphereLevel n).point ↔ t ∈ _root_.Cube.boundary (Fin n) := by
  constructor
  · intro h
    induction n with
    | zero =>
      have h' : (1 : Fin 2) = 0 := h
      exact False.elim (by simpa using h')
    | succ n ih =>
      change BasedSpace.suspensionProjection (sphereLevel n)
        (sphereCube n (fun i => t i.succ), t 0) =
        BasedSpace.suspensionProjection (sphereLevel n) ((sphereLevel n).point, 0) at h
      rcases (BasedSpace.suspensionProjection_eq_iff _ _ _).mp h with hp | hp
      · exact ⟨0, Or.inl (congrArg Prod.snd hp)⟩
      · rcases hp.1 with ht | ht | ht
        · obtain ⟨i, hi⟩ := ih (fun i => t i.succ) ht
          exact ⟨i.succ, hi⟩
        · exact ⟨0, Or.inl ht⟩
        · exact ⟨0, Or.inr ht⟩
  · exact (sphereCube n).property t

/-- The original sphere cube identifies no interior points: its exact
fibers are singleton interior points and the entire original boundary. -/
theorem sphereCube_eq_iff (n : ℕ) (t u : Fin n → I) :
    sphereCube n t = sphereCube n u ↔
      t = u ∨ (t ∈ _root_.Cube.boundary (Fin n) ∧ u ∈ _root_.Cube.boundary (Fin n)) := by
  induction n with
  | zero =>
    have he : t = u := Subsingleton.elim _ _
    exact ⟨fun _ => Or.inl he, fun _ => congrArg (sphereCube 0) he⟩
  | succ n ih =>
    constructor
    · intro h
      change BasedSpace.suspensionProjection (sphereLevel n)
        (sphereCube n (fun i => t i.succ), t 0) =
        BasedSpace.suspensionProjection (sphereLevel n)
          (sphereCube n (fun i => u i.succ), u 0) at h
      rcases (BasedSpace.suspensionProjection_eq_iff _ _ _).mp h with hp | hp
      · rcases (ih (fun i => t i.succ) (fun i => u i.succ)).mp
          (congrArg Prod.fst hp) with he | he
        · left
          funext i
          induction i using Fin.cases with
          | zero => exact congrArg Prod.snd hp
          | succ i => exact congrFun he i
        · obtain ⟨i, hi⟩ := he.1
          obtain ⟨j, hj⟩ := he.2
          exact Or.inr ⟨⟨i.succ, hi⟩, ⟨j.succ, hj⟩⟩
      · right
        exact ⟨(sphereCube_eq_point_iff_boundary (n + 1) t).mp
          (BasedSpace.suspensionProjection_collapsed _ _ hp.1),
          (sphereCube_eq_point_iff_boundary (n + 1) u).mp
          (BasedSpace.suspensionProjection_collapsed _ _ hp.2)⟩
    · rintro (rfl | ⟨ht, hu⟩)
      · rfl
      · exact ((sphereCube (n + 1)).property t ht).trans
          ((sphereCube (n + 1)).property u hu).symm

/-- The actual canonical sphere cube is injective on its open interior. -/
theorem sphereCube_injOn_interior (n : ℕ) :
    Set.InjOn (sphereCube n) (_root_.Cube.boundary (Fin n))ᶜ := by
  intro t ht u _ h
  exact ((sphereCube_eq_iff n t u).mp h).resolve_right (fun hb => ht hb.1)

end KIP126.StableHomotopy.Implementation.Prespectrum
