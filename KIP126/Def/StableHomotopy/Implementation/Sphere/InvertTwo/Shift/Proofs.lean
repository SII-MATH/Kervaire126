module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Additive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The actual positive suspension iterates of the fixed 2-inverted sphere
retain invertible multiplication by two. -/
theorem sphereInvertTwo_suspension_two_id_isIso (n : ℕ) :
    IsIso ((2 : ℕ) • 𝟙 (sourceLocalization.obj ((suspension^[n]) sphereInvertTwo))) := by
  induction n with
  | zero => exact sphereInvertTwo_two_id_isIso
  | succ n ih =>
    letI := ih
    rw [Function.iterate_succ_apply']
    change IsIso ((2 : ℕ) • 𝟙 (sourceSuspensionFunctor.obj
      (sourceLocalization.obj ((suspension^[n]) sphereInvertTwo))))
    rw [← sourceSuspensionFunctor.map_id, ← Functor.map_nsmul]
    infer_instance

/-- The actual negative suspension iterates of the fixed 2-inverted sphere
retain invertible multiplication by two. -/
theorem sphereInvertTwo_desuspension_two_id_isIso (n : ℕ) :
    IsIso ((2 : ℕ) • 𝟙 (sourceLocalization.obj ((desuspension^[n]) sphereInvertTwo))) := by
  induction n with
  | zero => exact sphereInvertTwo_two_id_isIso
  | succ n ih =>
    letI := ih
    rw [Function.iterate_succ_apply']
    change IsIso ((2 : ℕ) • 𝟙 (sourceDesuspensionFunctor.obj
      (sourceLocalization.obj ((desuspension^[n]) sphereInvertTwo))))
    rw [← sourceDesuspensionFunctor.map_id, ← Functor.map_nsmul]
    infer_instance

end KIP126.StableHomotopy.Implementation.Prespectrum
