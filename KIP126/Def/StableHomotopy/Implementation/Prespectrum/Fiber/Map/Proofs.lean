module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Sequence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp] theorem fiberMap_projection {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    fiberMap f g a b h ≫ fiberProjection g = fiberProjection f ≫ a := rfl

@[simp] theorem fiberConnecting_map {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    fiberConnecting f ≫ fiberMap f g a b h = loopMap b ≫ fiberConnecting g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact Prod.ext (a.point n) rfl

@[simp] theorem fiberMap_id {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberMap f f (𝟙 X) (𝟙 Y) (by simp) = 𝟙 (fiber f) := rfl

theorem fiberMap_comp {X Y X' Y' X'' Y'' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (k : X'' ⟶ Y'')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : X' ⟶ X'') (e : Y' ⟶ Y'')
    (h : f ≫ b = a ≫ g) (j : g ≫ e = c ≫ k) :
    fiberMap f g a b h ≫ fiberMap g k c e j =
      fiberMap f k (a ≫ c) (b ≫ e) (by rw [← Category.assoc,h,Category.assoc,j,Category.assoc]) := rfl

/-- Naturality of the actual additive boundary under a commuting square. -/
theorem fiberBoundary_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (d : ℤ) (y : StableHomotopy Y (d+1)) :
    stableHomotopyMap (fiberMap f g a b h) d (fiberBoundary f d y) =
      fiberBoundary g d (stableHomotopyMap b (d+1) y) := by
  have hi : stableHomotopyMap (loopMap b) d ((stableLoopHomotopyEquiv Y d).symm y) =
      (stableLoopHomotopyEquiv Y' d).symm (stableHomotopyMap b (d+1) y) := by
    apply (stableLoopHomotopyEquiv Y' d).injective
    exact (stableLoopHomotopyMap_natural b d ((stableLoopHomotopyEquiv Y d).symm y)).trans
      ((congrArg (stableHomotopyMap b (d+1)) ((stableLoopHomotopyEquiv Y d).apply_symm_apply y)).trans
        ((stableLoopHomotopyEquiv Y' d).apply_symm_apply _).symm)
  have hn := congrArg (fun k => stableHomotopyMap k d ((stableLoopHomotopyEquiv Y d).symm y))
    (fiberConnecting_map f g a b h)
  change (stableHomotopyFunctor d).map (fiberConnecting f ≫ fiberMap f g a b h) _ =
    (stableHomotopyFunctor d).map (loopMap b ≫ fiberConnecting g) _ at hn
  simp only [Functor.map_comp_apply] at hn
  exact hn.trans (congrArg (stableHomotopyMap (fiberConnecting g) d) hi)

end KIP126.StableHomotopy.Implementation.Prespectrum
