import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Coaction.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The tensor diagonal is the original cooperation diagonal followed by
Künneth, with no replacement of its underlying spectrum map. -/
theorem cooperationTensorDiagonal_apply (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorDiagonal H R K n a =
      K.comparison H.HF2 n (cooperationDiagonalMap H n a) := rfl

theorem cooperationTensorDiagonal_counit (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i H.HF2) n
      (cooperationTensorDiagonal H R K n a) = a :=
  mod2TensorCoaction_counit H R K H.HF2 n a

/-- Coassociativity of every actual tensor coaction is derived from
below-page Künneth coherence and the actual unit, not postulated per object. -/
theorem mod2TensorCoaction_coassoc (hD : Mod2KunnethDiagonalCompatible H R K)
    (X : C) (n : ℤ) (x : mod2HomologyF2 H R n X) :
    cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i X) n
      (mod2TensorCoaction H R K X n x) =
      cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
        (mod2TensorCoaction H R K X) n (mod2TensorCoaction H R K X n x) := by
  rw [mod2TensorCoaction_apply, ← hD]
  change cooperationTensorMap H R _ (fun i => (K.comparison X i).toLinearMap) n
    (mod2TensorCoaction H R K (H.HF2 ⊗ X) n
      (Mod2Homology.pushforward H (adamsUnit H.unit X) n x)) = _
  rw [mod2TensorCoaction_naturality, ← LinearMap.comp_apply, cooperationTensorMap_comp]
  rfl

/-- Specializing the coaction theorem to `H` proves coassociativity of the
actual cooperation coproduct, under the same explicit coherence premise. -/
theorem cooperationTensorDiagonal_coassoc (hD : Mod2KunnethDiagonalCompatible H R K)
    (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i H.HF2) n
      (cooperationTensorDiagonal H R K n a) =
      cooperationTensorMap H R (fun i => mod2HomologyF2 H R i H.HF2)
        (cooperationTensorDiagonal H R K) n (cooperationTensorDiagonal H R K n a) :=
  mod2TensorCoaction_coassoc H R K hD H.HF2 n a

end KIP126.StableHomotopy.Cohomology
