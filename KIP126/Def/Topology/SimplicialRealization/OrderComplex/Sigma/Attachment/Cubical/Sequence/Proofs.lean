module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory HomotopicalAlgebra Simplicial
open KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ TopCat.{u})
  (hc : ∀ n, Nonempty (AttachCells.{u} cubeBoundaryInclusion.{u}
    (F.map (homOfLE (Nat.le_succ n)))))
  (M₀ : OrderRealizationModel (F.obj 0))

@[simp] theorem cubicalOrderStageModel_zero :
    cubicalOrderStageModel F hc M₀ 0 = M₀ := rfl

/-- The chosen embedding is the actual successor map in the order sequence. -/
@[simp] theorem cubicalOrderSequence_map_succ (n : ℕ) :
    (cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ n)) =
      PartOrd.ofHom (cubicalOrderStageEmbedding F hc M₀ n).toOrderHom :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The realized successor map is the realization of that same embedding. -/
@[simp] theorem cubicalOrderRealizationSequence_map_succ (n : ℕ) :
    (cubicalOrderRealizationSequence F hc M₀).map (homOfLE (Nat.le_succ n)) =
      SSet.toTop.map (nerveMap (cubicalOrderStageEmbedding F hc M₀ n).monotone.functor) := by
  change (PartOrd.nerveFunctor ⋙ SSet.toTop).map
    ((cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ n))) = _
  rw [cubicalOrderSequence_map_succ]
  rfl

@[simp] theorem cubicalOrderSequenceComparison_app (n : ℕ) :
    (cubicalOrderSequenceComparison F hc M₀).app n =
      TopCat.ofHom (cubicalOrderStageModel F hc M₀ n).equivalence.toFun := rfl

@[simp] theorem cubicalOrderSequenceInverseComparison_app (n : ℕ) :
    (cubicalOrderSequenceInverseComparison F hc M₀).app n =
      TopCat.ofHom (cubicalOrderStageModel F hc M₀ n).equivalence.invFun := rfl

/-- Forward compatibility holds for every original transition, not only
adjacent stages. -/
theorem cubicalOrderSequenceComparison_transition {m n : ℕ} (h : m ≤ n)
    (x : |nerve (cubicalOrderStageModel F hc M₀ m).order|) :
    (cubicalOrderStageModel F hc M₀ n).equivalence
      ((cubicalOrderRealizationSequence F hc M₀).map (homOfLE h) x) =
    F.map (homOfLE h) ((cubicalOrderStageModel F hc M₀ m).equivalence x) :=
  congrArg (fun f => f x) ((cubicalOrderSequenceComparison F hc M₀).naturality (homOfLE h))

/-- The inverse comparison retains every original transition strictly. -/
theorem cubicalOrderSequenceInverseComparison_transition {m n : ℕ} (h : m ≤ n)
    (x : F.obj m) :
    (cubicalOrderStageModel F hc M₀ n).equivalence.invFun (F.map (homOfLE h) x) =
    (cubicalOrderRealizationSequence F hc M₀).map (homOfLE h)
      ((cubicalOrderStageModel F hc M₀ m).equivalence.invFun x) :=
  congrArg (fun f => f x)
    ((cubicalOrderSequenceInverseComparison F hc M₀).naturality (homOfLE h))

/-- In particular, every point of the specified initial model is carried
to the prescribed image of its initial-space point. -/
theorem cubicalOrderSequenceComparison_initial (n : ℕ) (x : |nerve M₀.order|) :
    (cubicalOrderStageModel F hc M₀ n).equivalence
      ((cubicalOrderRealizationSequence F hc M₀).map (homOfLE (Nat.zero_le n)) x) =
    F.map (homOfLE (Nat.zero_le n)) (M₀.equivalence x) :=
  cubicalOrderSequenceComparison_transition F hc M₀ (Nat.zero_le n) x

/-- The backward comparison likewise preserves the image of every
initial-space point, and hence any basepoint chosen there. -/
theorem cubicalOrderSequenceInverseComparison_initial (n : ℕ) (x : F.obj 0) :
    (cubicalOrderStageModel F hc M₀ n).equivalence.invFun
      (F.map (homOfLE (Nat.zero_le n)) x) =
    (cubicalOrderRealizationSequence F hc M₀).map (homOfLE (Nat.zero_le n))
      (M₀.equivalence.invFun x) :=
  cubicalOrderSequenceInverseComparison_transition F hc M₀ (Nat.zero_le n) x

end KIP126.Topology.SimplicialRealization
