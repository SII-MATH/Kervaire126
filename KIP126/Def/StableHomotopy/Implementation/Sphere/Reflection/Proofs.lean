module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Reflection.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Abelian.Reversal.Proofs
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sphereCoordinateReflection_cube (n : ℕ) (i : Fin n) (t : Fin n → I) :
    (sphereCoordinateReflection n i).map (sphereCube n t) =
      (GenLoop.symmAt i (sphereCube n)) t :=
  (genLoop_sphereLevel_map_exists_unique n (sphereLevel n)
    (GenLoop.symmAt i (sphereCube n))).choose_spec.1 t

/-- Reflection twice is exactly the identity of the original based
sphere, before passing to homotopy or stable classes. -/
theorem sphereCoordinateReflection_comp_self (n : ℕ) (i : Fin n) :
    sphereCoordinateReflection n i ≫ sphereCoordinateReflection n i = 𝟙 (sphereLevel n) := by
  apply sphereLevel_map_ext n
  intro t
  change (sphereCoordinateReflection n i).map
    ((sphereCoordinateReflection n i).map (sphereCube n t)) = sphereCube n t
  rw [sphereCoordinateReflection_cube]
  change (sphereCoordinateReflection n i).map
    (sphereCube n (fun j => if j = i then unitInterval.symm (t i) else t j)) = sphereCube n t
  rw [sphereCoordinateReflection_cube]
  change sphereCube n (fun j => if j = i then
    unitInterval.symm ((fun j => if j = i then unitInterval.symm (t i) else t j) i)
    else (if j = i then unitInterval.symm (t i) else t j)) = sphereCube n t
  apply congrArg (sphereCube n)
  funext j
  by_cases hji : j = i <;> simp [hji]

/-- The specified original reflection represents the negative original
sphere class, for the actual stable-group addition. -/
theorem sphereCoordinateReflection_loopClass (n : ℕ) (i : Fin n) :
    loopClass sphere 0 n n (by omega)
      (KIP126.Topology.continuousGenLoopMap (sphereCoordinateReflection n i).map
        (sphereLevel n).point (sphereLevel n).point (sphereCoordinateReflection n i).point n
        (sphereCube n)) =
      -loopClass sphere 0 n n (by omega) (sphereCube n) := by
  have he : KIP126.Topology.continuousGenLoopMap (sphereCoordinateReflection n i).map
      (sphereLevel n).point (sphereLevel n).point (sphereCoordinateReflection n i).point n
      (sphereCube n) = GenLoop.symmAt i (sphereCube n) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    exact sphereCoordinateReflection_cube n i
  rw [he]
  exact loopClass_symmAt sphere 0 n n (by omega) i (sphereCube n)

end KIP126.StableHomotopy.Implementation.Prespectrum
