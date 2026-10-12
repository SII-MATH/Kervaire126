module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Map.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- An annihilator of the original stable group annihilates the actual
Postnikov layer identity, through its original additive group comparison. -/
theorem sourcePostnikovLayer_nsmul_id_eq_zero_of_homotopy (X : SourceCategory.{0})
    (n : ℤ) (p : ℕ) (hp : ∀ x : (sourceStableHomotopyAddFunctor n).obj X, p • x = 0) :
    p • 𝟙 (sourcePostnikovLayer X n) = 0 := by
  apply source_nsmul_id_eq_zero_of_homotopy_nsmul_eq_zero _ n p
    (sourcePostnikovLayer_homotopy_subsingleton X n)
  intro x
  apply (sourcePostnikovLayerHomotopyEquiv X n).injective
  let e := (sourcePostnikovLayerHomotopyEquiv X n).toAddMonoidHom
  change e (p • x) = e 0
  rw [map_nsmul e p x, e.map_zero, hp]

/-- Scalar annihilation of an actual object passes to every actual layer. -/
theorem sourcePostnikovLayer_nsmul_id_eq_zero (X : SourceCategory.{0}) (n : ℤ)
    (p : ℕ) (hp : p • 𝟙 X = 0) : p • 𝟙 (sourcePostnikovLayer X n) = 0 := by
  apply sourcePostnikovLayer_nsmul_id_eq_zero_of_homotopy X n p
  intro x
  have h := congrArg (fun f => (sourceStableHomotopyAddFunctor n).map f) hp
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  exact congrArg (fun f : (sourceStableHomotopyAddFunctor n).obj X ⟶
    (sourceStableHomotopyAddFunctor n).obj X => f x) h

end KIP126.StableHomotopy.Implementation
