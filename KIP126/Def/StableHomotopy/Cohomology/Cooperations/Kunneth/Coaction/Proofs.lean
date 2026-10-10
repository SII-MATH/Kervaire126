import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Coaction.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Suspension.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Coaction.Connecting.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

theorem mod2TensorCoaction_apply (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    mod2TensorCoaction H R K X n x = K.comparison X n (mod2CoactionMap H X n x) := rfl

/-- Tensor augmentation retracts the actual tensor-coordinate coaction. -/
theorem mod2TensorCoaction_counit (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n
      (mod2TensorCoaction H R K X n x) = x := by
  rw [mod2TensorCoaction_apply, K.action_comparison]
  change (x ≫ mod2Coaction H X) ≫ mod2FreeAction H R X = x
  rw [Category.assoc, mod2Coaction_counit, Category.comp_id]

theorem mod2TensorCoaction_injective (X : C) (n : ℤ) :
    Function.Injective (mod2TensorCoaction H R K X n) :=
  Function.LeftInverse.injective (mod2TensorCoaction_counit H R K X n)

/-- Naturality in degree-preserving spectrum maps is inherited from the
actual unit and the homology Künneth comparison. -/
theorem mod2TensorCoaction_naturality {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (x : Mod2Homology H n X) :
    mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
      cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
        (fun i => (mod2HomologyF2Map H R f i).hom) n (mod2TensorCoaction H R K X n x) := by
  rw [mod2TensorCoaction_apply, ← mod2CoactionMap_naturality, K.naturality]
  rfl

variable [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The tensor coaction is compatible with the boundary of every
distinguished triangle, with its genuine degree shift. -/
theorem mod2TensorCoaction_connecting (hK : Mod2KunnethSuspensionCompatible H R K)
    (T : HoCofiberSequence (C := C)) (n : ℤ) (x : Mod2Homology H n T.Z) :
    mod2TensorCoaction H R K T.X (n - 1) (mod2HomologyConnecting H T n x) =
      cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i T.Z)
        (fun i => mod2HomologyF2 H R i T.X) (mod2HomologyConnectingF2 H R T) n
        (mod2TensorCoaction H R K T.Z n x) := by
  rw [mod2TensorCoaction_apply, ← mod2CoactionMap_connecting,
    mod2Kunneth_connecting H R K hK]
  rfl

end KIP126.StableHomotopy.Cohomology
