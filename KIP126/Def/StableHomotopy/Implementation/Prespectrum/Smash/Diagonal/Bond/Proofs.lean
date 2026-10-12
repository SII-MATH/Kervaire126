module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Bond.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

theorem diagonalBond_laws (X Y : Prespectrum.{0}) (n : ℕ) :
    (∀ t, diagonalBond X Y n ((diagonalLevel X Y n).point,t) =
      (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,0) = (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,1) = (diagonalLevel X Y (n+1)).point) := by
  induction n using Nat.twoStepInduction generalizing X Y with
  | zero =>
    exact ⟨fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl)),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))⟩
  | one => exact (pairedBond_exists X Y).exists.choose_spec.2
  | more n ih _ => exact ih X.tail Y.tail

end Prespectrum
end KIP126.StableHomotopy.Implementation
