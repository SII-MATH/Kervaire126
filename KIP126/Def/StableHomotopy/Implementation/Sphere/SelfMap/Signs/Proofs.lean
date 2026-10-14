module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Precomposing any original sphere self-map by the specified coordinate
reflection negates its original stable class. -/
theorem sphereSelfMapClass_reflection_precomp (n : ℕ) (i : Fin n)
    (f : sphereLevel n ⟶ sphereLevel n) :
    sphereSelfMapClass n (sphereCoordinateReflection n i ≫ f) =
      -sphereSelfMapClass n f := by
  let p := continuousGenLoopMap f.map (sphereLevel n).point
    (sphereLevel n).point f.point n (sphereCube n)
  have he : continuousGenLoopMap (sphereCoordinateReflection n i ≫ f).map
      (sphereLevel n).point (sphereLevel n).point (sphereCoordinateReflection n i ≫ f).point n
      (sphereCube n) = GenLoop.symmAt i p := by
    apply GenLoop.ext
    intro t
    change f.map ((sphereCoordinateReflection n i).map (sphereCube n t)) =
      f.map (sphereCube n (fun j => if j = i then unitInterval.symm (t i) else t j))
    rw [sphereCoordinateReflection_cube]
    rfl
  unfold sphereSelfMapClass
  rw [he]
  exact loopClass_symmAt sphere 0 n n (by omega) i p

/-- A map with the actual coordinate-reflection formula on the original
sphere cube represents precisely one of the two signed original generators. -/
theorem sphereSelfMapClass_eq_signed_generator_of_cube_signs
    (n : ℕ) (s : Finset (Fin n)) (f : sphereLevel n ⟶ sphereLevel n)
    (hf : ∀ t, f.map (sphereCube n t) =
      sphereCube n (fun i => if i ∈ s then unitInterval.symm (t i) else t i)) :
    sphereSelfMapClass n f = sphereGenerator ∨
      sphereSelfMapClass n f = -sphereGenerator := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have he : f = 𝟙 (sphereLevel n) := by
      apply sphereLevel_map_ext n
      intro t
      change f.map (sphereCube n t) = sphereCube n t
      simpa using hf t
    exact Or.inl (he ▸ sphereSelfMapClass_id n)
  | @insert i s hi ih =>
    let g := sphereCoordinateReflection n i ≫ f
    have hg : ∀ t, g.map (sphereCube n t) =
        sphereCube n (fun j => if j ∈ s then unitInterval.symm (t j) else t j) := by
      intro t
      change f.map ((sphereCoordinateReflection n i).map (sphereCube n t)) = _
      rw [sphereCoordinateReflection_cube]
      change f.map (sphereCube n (fun j => if j = i then unitInterval.symm (t i) else t j)) = _
      rw [hf]
      apply congrArg (sphereCube n)
      funext j
      by_cases hji : j = i
      · subst j
        simp [hi]
      · simp [hji]
    have hneg := sphereSelfMapClass_reflection_precomp n i f
    rcases ih g hg with h | h
    · right
      exact neg_injective ((hneg.symm.trans h).trans (neg_neg sphereGenerator).symm)
    · left
      exact neg_injective (hneg.symm.trans h)

end KIP126.StableHomotopy.Implementation.Prespectrum
