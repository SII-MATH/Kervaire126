module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.Data
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Reflection
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Every original canonical sphere cube is the original positive
sphere generator, by its actual structure-map stabilizations. -/
theorem sphereCube_loopClass (n : ℕ) :
    loopClass sphere 0 n n (by omega) (sphereCube n) = sphereGenerator := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : loopClass sphere 0 n n (by omega) (sphereCube n) =
        loopClass sphere 0 (n + 1) (n + 1) (by omega) (sphereCube (n + 1)) :=
      Quot.sound (StableRelation.stabilization
        (⟨n, n, by omega, sphereCube n⟩ : Representative sphere 0))
    exact hs.symm.trans ih

/-- An actual based homotopy of the original self-maps preserves their
class in the original stable quotient. -/
theorem sphereSelfMapClass_homotopic (n : ℕ) (f g : sphereLevel n ⟶ sphereLevel n)
    (H : Nonempty (ContinuousMap.HomotopyRel f.map g.map {(sphereLevel n).point})) :
    sphereSelfMapClass n f = sphereSelfMapClass n g := by
  let p := continuousGenLoopMap f.map (sphereLevel n).point (sphereLevel n).point f.point n
    (sphereCube n)
  let q := continuousGenLoopMap g.map (sphereLevel n).point (sphereLevel n).point g.point n
    (sphereCube n)
  have h := (genLoop_homotopic_iff_sphereLevel_maps_homotopic n (sphereLevel n)
    p q f g (fun _ => rfl) (fun _ => rfl)).mpr H
  exact Quot.sound (StableRelation.homotopy (⟨n, n, by omega, p⟩ : Representative sphere 0) q h)

@[simp] theorem sphereSelfMapClass_id (n : ℕ) :
    sphereSelfMapClass n (𝟙 (sphereLevel n)) = sphereGenerator :=
  sphereCube_loopClass n

/-- The actual single-coordinate reflection represents the negative
of the specified original sphere generator. -/
theorem sphereSelfMapClass_reflection (n : ℕ) (i : Fin n) :
    sphereSelfMapClass n (sphereCoordinateReflection n i) = -sphereGenerator := by
  exact (sphereCoordinateReflection_loopClass n i).trans
    (congrArg Neg.neg (sphereCube_loopClass n))

/-- The local window compression has positive original stable class,
because its constructed based homotopy is to the original identity. -/
theorem sphereSelfMapClass_windowCompression (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    sphereSelfMapClass n (sphereWindowCompression n a b hab) = sphereGenerator :=
  (sphereSelfMapClass_homotopic n _ _ (sphereWindowCompression_homotopic_id n a b hab)).trans
    (sphereSelfMapClass_id n)

/-- Every original stable class in degree zero is represented by an
actual based self-map of a positive-dimensional original sphere. This
links the finite geometric decomposition to every class of the fixed
stable quotient without presupposing any degree calculation. -/
theorem exists_positive_sphereSelfMapClass (x : StableHomotopy sphere 0) :
    ∃ (n : ℕ), 0 < n ∧ ∃ f : sphereLevel n ⟶ sphereLevel n,
      sphereSelfMapClass n f = x := by
  refine Quot.inductionOn x ?_
  rintro ⟨n, r, hr, p⟩
  have he : r = n := by omega
  subst r
  let p' := stabilizeLoop sphere n n p
  obtain ⟨f, hf, _⟩ := genLoop_sphereLevel_map_exists_unique (n + 1) (sphereLevel (n + 1)) p'
  have hp : continuousGenLoopMap f.map (sphereLevel (n + 1)).point
      (sphereLevel (n + 1)).point f.point (n + 1) (sphereCube (n + 1)) = p' := by
    apply Subtype.ext
    apply ContinuousMap.ext
    exact hf
  refine ⟨n + 1, by omega, f, ?_⟩
  unfold sphereSelfMapClass
  rw [hp]
  exact (Quot.sound (StableRelation.stabilization ⟨n, n, hr, p⟩)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
