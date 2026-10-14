module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Currying
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Stabilized.Map.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

/-- First-coordinate currying is an actual equivalence of the based
cubical homotopy quotients, including the zero-dimensional quotient. -/
def loopFirstHomotopyEquiv (A : BasedSpace.{u}) (r : ℕ) :
    _root_.HomotopyGroup (Fin r) (loopLevel A) (loopLevel A).point ≃
      _root_.HomotopyGroup (Fin (r+1)) A A.point where
  toFun := Quotient.map (loopUncurryFirst A r)
    (fun _ _ h => ⟨loopUncurryFirstHomotopy A r h.some⟩)
  invFun := Quotient.map (loopCurryFirst A r)
    (fun _ _ h => ⟨loopCurryFirstHomotopy A r h.some⟩)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p => exact congrArg Quotient.mk' (loopCurryFirst_uncurry A r p)
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p => exact congrArg Quotient.mk' (loopUncurryFirst_curry A r p)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual adjoint-bond unit becomes exactly the original
stabilization after first-coordinate uncurrying. -/
theorem loopFirstHomotopyEquiv_stepUnit (X : Prespectrum.{u}) (n r : ℕ)
    (x : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) :
    loopFirstHomotopyEquiv (X.level (n+1)) r
      ((spectrificationStepUnit X).levelHomotopy n r x) = stabilizeHomotopy X n r x := by
  induction x using Quotient.inductionOn with
  | h p => rfl

theorem spectrificationStepUnit_levelHomotopy_bijective (X : Prespectrum.{u})
    (hX : HasBijectiveStabilization X) (n r : ℕ) :
    Function.Bijective ((spectrificationStepUnit X).levelHomotopy n r) := by
  apply (Function.Bijective.of_comp_iff' (loopFirstHomotopyEquiv (X.level (n+1)) r).bijective _).mp
  rw [show loopFirstHomotopyEquiv (X.level (n+1)) r ∘
      (spectrificationStepUnit X).levelHomotopy n r = stabilizeHomotopy X n r from
    funext (loopFirstHomotopyEquiv_stepUnit X n r)]
  exact hX n r

/-- Level homotopy bijections transport the actual stabilization property. -/
theorem hasBijectiveStabilization_of_levelHomotopy_bijective
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (hX : HasBijectiveStabilization X)
    (hf : ∀ n r, Function.Bijective (f.levelHomotopy n r)) : HasBijectiveStabilization Y := by
  intro n r
  apply (Function.Bijective.of_comp_iff _ (hf n r)).mp
  rw [show stabilizeHomotopy Y n r ∘ f.levelHomotopy n r =
      f.levelHomotopy (n+1) (r+1) ∘ stabilizeHomotopy X n r from
    funext (fun x => (f.levelHomotopy_stabilize n r x).symm)]
  exact (hf (n+1) (r+1)).comp (hX n r)

/-- Applying the actual step preserves bijective stabilization. -/
theorem spectrificationStep_hasBijectiveStabilization (X : Prespectrum.{u})
    (hX : HasBijectiveStabilization X) : HasBijectiveStabilization (spectrificationStep X) :=
  hasBijectiveStabilization_of_levelHomotopy_bijective (spectrificationStepUnit X) hX
    (spectrificationStepUnit_levelHomotopy_bijective X hX)

/-- Naturality of the actual stable unit proves that the strict step
functor preserves stable equivalences for all prespectra. -/
theorem spectrificationStepMap_stableEquivalence {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (hf : stableEquivalences f) : stableEquivalences (spectrificationStepMap f) := by
  intro d
  have hc : stableHomotopyMap (spectrificationStepMap f) d ∘
      stableHomotopyMap (spectrificationStepUnit X) d =
      stableHomotopyMap (spectrificationStepUnit Y) d ∘ stableHomotopyMap f d := by
    ext x
    have hn := congrArg ((stableHomotopyFunctor d).map) (spectrificationStepUnit_natural f)
    rw [(stableHomotopyFunctor d).map_comp,(stableHomotopyFunctor d).map_comp] at hn
    exact (ConcreteCategory.congr_hom hn x).symm
  apply (Function.Bijective.of_comp_iff _ (spectrificationStepUnit_stableEquivalence X d)).mp
  rw [hc]
  exact (spectrificationStepUnit_stableEquivalence Y d).comp (hf d)

end KIP126.StableHomotopy.Implementation.Prespectrum

end
