module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type}

@[simp] theorem piLift_projection {A : Prespectrum.{u}} {X : J → Prespectrum.{u}}
    (f : ∀ j, A ⟶ X j) (j : J) : piLift f ≫ piProjection X j = f j := rfl

theorem piHom_ext {A : Prespectrum.{u}} {X : J → Prespectrum.{u}}
    (f g : A ⟶ piPrespectrum X) (h : ∀ j, f ≫ piProjection X j = g ≫ piProjection X j) : f = g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  funext j
  exact congrArg (fun k : A ⟶ X j => k.level n x) (h j)

def piFan_isLimit (X : J → Prespectrum.{u}) : IsLimit (piFan X) :=
  Fan.IsLimit.mk _ (fun s => piLift s.proj) (fun _ _ => rfl)
    (fun s m hm => piHom_ext m _ fun j => (hm j).trans (piLift_projection _ j).symm)

/-- Actual based homotopies can be taken coordinatewise in any product. -/
theorem piLoop_homotopic (X : J → Prespectrum.{u}) (n r : ℕ)
    (p q : ∀ j, GenLoop (Fin r) (X j |>.level n) (X j |>.level n).point)
    (h : ∀ j, GenLoop.Homotopic (p j) (q j)) :
    GenLoop.Homotopic (piLoop X n r p) (piLoop X n r q) := by
  let H j := Classical.choice (h j)
  exact ⟨ContinuousMap.HomotopyRel.pi H⟩

theorem levelPiComparison_injective (X : J → Prespectrum.{u}) (n r : ℕ) :
    Function.Injective (levelPiComparison X n r) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      have hh : ∀ j, GenLoop.Homotopic ((piProjection X j).levelLoop n r p)
          ((piProjection X j).levelLoop n r q) := fun j => Quotient.exact (congrFun h j)
      have hp : piLoop X n r (fun j => (piProjection X j).levelLoop n r p) = p := rfl
      have hq : piLoop X n r (fun j => (piProjection X j).levelLoop n r q) = q := rfl
      apply Quotient.sound
      change GenLoop.Homotopic p q
      simpa only [hp,hq] using piLoop_homotopic X n r _ _ hh

theorem levelPiComparison_surjective (X : J → Prespectrum.{u}) (n r : ℕ) :
    Function.Surjective (levelPiComparison X n r) := by
  intro x
  refine ⟨⟦piLoop X n r (fun j => (x j).out)⟧, funext fun j => ?_⟩
  exact Quotient.out_eq (x j)

theorem levelPiComparison_bijective (X : J → Prespectrum.{u}) (n r : ℕ) :
    Function.Bijective (levelPiComparison X n r) :=
  ⟨levelPiComparison_injective X n r, levelPiComparison_surjective X n r⟩

theorem levelPiComparison_stabilize (X : J → Prespectrum.{u}) (n r : ℕ)
    (x : _root_.HomotopyGroup (Fin r) ((piPrespectrum X).level n) ((piPrespectrum X).level n).point) :
    levelPiComparison X (n + 1) (r + 1) (stabilizeHomotopy (piPrespectrum X) n r x) =
      fun j => stabilizeHomotopy (X j) n r (levelPiComparison X n r x j) := by
  induction x using Quotient.inductionOn with
  | h p => rfl

theorem stableLevelPiComparison_transition (X : J → Prespectrum.{u}) (d : ℤ)
    (i k : ℕ) (h : i ≤ k) (x : stableLevelGroup (piPrespectrum X) d i) (j : J) :
    levelPiComparison X (stableGroupStage d k) (stableGroupDimension d k)
        (stableLevelTransition (piPrespectrum X) d i k h x) j =
      stableLevelTransition (X j) d i k h
        (levelPiComparison X (stableGroupStage d i) (stableGroupDimension d i) x j) := by
  induction h with
  | refl => rw [stableLevelTransition_self, stableLevelTransition_self]; rfl
  | @step k h ih =>
    rw [stableLevelTransition_succ (piPrespectrum X) d h, stableLevelTransition_succ (X j) d h]
    exact (congrFun (levelPiComparison_stabilize X (stableGroupStage d k) (stableGroupDimension d k)
      (stableLevelTransition (piPrespectrum X) d i k h x)) j).trans
      (congrArg (stabilizeHomotopy (X j) (stableGroupStage d k) (stableGroupDimension d k)) ih)

end KIP126.StableHomotopy.Implementation.Prespectrum
