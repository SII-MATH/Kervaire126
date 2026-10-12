module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Closed.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each closed-cylinder step retains the proved stable equivalence of the
actual adjoint-bond unit. -/
theorem spectrificationCylinderUnit_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (spectrificationCylinderUnit X) :=
  mappingCylinderInclusion_stableEquivalence (spectrificationStepUnit X)
    (spectrificationStepUnit_stableEquivalence X)

instance spectrificationStep_level_t1Space (X : Prespectrum.{u}) (n : ℕ)
    [T1Space (X.level (n+1))] : T1Space ((spectrificationStep X).level n) := by
  change T1Space (Path (X.level (n+1)).point (X.level (n+1)).point)
  exact t1Space_of_injective_of_continuous (f := fun p :
      Path (X.level (n+1)).point (X.level (n+1)).point => (fun t => p t))
    DFunLike.coe_injective (continuous_pi fun t => continuous_id.eval continuous_const)

instance spectrificationCylinderStep_level_t1Space (X : Prespectrum.{u}) (n : ℕ)
    [T1Space (X.level n)] [T1Space (X.level (n+1))] :
    T1Space ((spectrificationCylinderStep X).level n) :=
  inferInstanceAs (T1Space (mappingCylinderLevel (spectrificationStepUnit X) n))

instance spectrificationStages_level_t1Space (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] (k n : ℕ) : T1Space ((spectrificationStages X k).level n) := by
  induction k generalizing n with
  | zero => exact inferInstanceAs (T1Space (X.level n))
  | succ k ih =>
    letI (n : ℕ) : T1Space ((spectrificationStages X k).level n) := ih n
    exact inferInstanceAs (T1Space ((spectrificationCylinderStep (spectrificationStages X k)).level n))

theorem spectrificationCylinderUnit_isClosedEmbedding (X : Prespectrum.{u}) (n : ℕ)
    [T1Space (X.level n)] [T1Space (X.level (n+1))] :
    IsClosedEmbedding ((spectrificationCylinderUnit X).level n) :=
  mappingCylinderInclusion_isClosedEmbedding (spectrificationStepUnit X) n

theorem spectrificationDiagram_successor_closed (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] (k n : ℕ) :
    IsClosedEmbedding (((spectrificationDiagram X).map (homOfLE (Nat.le_succ k))).level n) := by
  change IsClosedEmbedding (((Functor.ofSequence
    (fun j => spectrificationCylinderUnit (spectrificationStages X j))).map
      (homOfLE (Nat.le_succ k))).level n)
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact spectrificationCylinderUnit_isClosedEmbedding (spectrificationStages X k) n

/-- Every finite transition out of the original stage is a stable equivalence. -/
theorem spectrificationDiagram_initial_stableEquivalence (X : Prespectrum.{u}) (k : ℕ) :
    stableEquivalences ((spectrificationDiagram X).map (homOfLE (Nat.zero_le k))) := by
  induction k with
  | zero =>
    intro d
    rw [show homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) from rfl,(spectrificationDiagram X).map_id 0]
    have he : stableHomotopyMap (𝟙 ((spectrificationDiagram X).obj 0)) d = id := by
      funext x
      induction x using Quot.inductionOn with
      | h p => rfl
    rw [he]
    exact Function.bijective_id
  | succ k ih =>
    have hc : (spectrificationDiagram X).map (homOfLE (Nat.zero_le (k+1))) =
        (spectrificationDiagram X).map (homOfLE (Nat.zero_le k)) ≫
          spectrificationCylinderUnit (spectrificationStages X k) := by
      rw [← Functor.ofSequence_map_homOfLE_succ
        (fun j => spectrificationCylinderUnit (spectrificationStages X j)) k]
      exact (spectrificationDiagram X).map_comp (homOfLE (Nat.zero_le k))
        (homOfLE (Nat.le_succ k))
    intro d
    rw [hc]
    have he := (stableHomotopyFunctor d).map_comp
      ((spectrificationDiagram X).map (homOfLE (Nat.zero_le k)))
      (spectrificationCylinderUnit (spectrificationStages X k))
    have he' : stableHomotopyMap
        ((spectrificationDiagram X).map (homOfLE (Nat.zero_le k)) ≫
          spectrificationCylinderUnit (spectrificationStages X k)) d =
        stableHomotopyMap (spectrificationCylinderUnit (spectrificationStages X k)) d ∘
          stableHomotopyMap ((spectrificationDiagram X).map (homOfLE (Nat.zero_le k))) d := by
      funext x
      exact ConcreteCategory.congr_hom he x
    rw [he']
    exact (spectrificationCylinderUnit_stableEquivalence (spectrificationStages X k) d).comp (ih d)

/-- For actual T₁ levels, the constructed infinite telescope is stably equivalent
to the original prespectrum. This uses the proved compact-stage factorization. -/
theorem spectrificationTelescopeUnit_stableEquivalence (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] : stableEquivalences (spectrificationTelescopeUnit X) := by
  letI (k n : ℕ) : T1Space (((spectrificationDiagram X).obj k).level n) :=
    inferInstanceAs (T1Space ((spectrificationStages X k).level n))
  exact sequentialColimitInclusion_zero_stableEquivalence (spectrificationDiagram X)
    (spectrificationDiagram_successor_closed X) (spectrificationDiagram_initial_stableEquivalence X)

end KIP126.StableHomotopy.Implementation.Prespectrum
