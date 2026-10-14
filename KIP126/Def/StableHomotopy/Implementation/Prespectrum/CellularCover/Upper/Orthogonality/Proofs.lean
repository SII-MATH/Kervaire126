module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Shift.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The actual upper sphere cover has only the zero map into an object
whose original stable groups vanish in all of those degrees. -/
theorem sourceUpperSphereCover_hom_subsingleton (X : SourceCategory.{0}) (n : ℤ)
    (Y : SourceCategory.{0})
    (hY : ∀ d, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Subsingleton (sourceUpperSphereCover X n ⟶ Y) := by
  let A (a : SourceUpperSphereIndex X n) := Prespectrum.sourceSphere a.1.val
  refine ⟨fun f g => ?_⟩
  apply Sigma.hom_ext
  intro a
  letI : Subsingleton (Y.as.obj.StableHomotopy a.1.val) := hY a.1.val a.1.property
  letI : Subsingleton (A a ⟶ Y) :=
    (Prespectrum.sourceStableHomotopyEquiv Y.as.obj a.1.val).symm.injective.subsingleton
  exact Subsingleton.elim _ _

/-- The same actual orthogonality holds for every nonnegative integer shift
of the upper sphere cover, using the actual shifted coproduct. -/
theorem sourceUpperSphereCover_shift_hom_subsingleton (X : SourceCategory.{0}) (n k : ℤ)
    (hk : 0 ≤ k) (Y : SourceCategory.{0})
    (hY : ∀ d, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Subsingleton ((sourceUpperSphereCover X n)⟦k⟧ ⟶ Y) := by
  let A (a : SourceUpperSphereIndex X n) := Prespectrum.sourceSphere a.1.val
  let F := shiftFunctor SourceCategory k
  have hc := isColimitOfHasCoproductOfPreservesColimit F A
  refine ⟨fun f g => ?_⟩
  apply Cofan.IsColimit.hom_ext hc
  intro a
  letI := hY (a.1.val+k) (by have := a.1.property; omega)
  let e : ((A a)⟦k⟧ ⟶ Y) ≃ ((sourceStableHomotopyAddFunctor (a.1.val+k)).obj Y) :=
    (Iso.homCongr (Prespectrum.sourceSphere_addShiftIso a.1.val k) (Iso.refl Y)).trans
      (Prespectrum.sourceStableHomotopyEquiv Y.as.obj (a.1.val+k)).symm
  letI : Subsingleton ((A a)⟦k⟧ ⟶ Y) := e.injective.subsingleton
  exact Subsingleton.elim _ _

end KIP126.StableHomotopy.Implementation
