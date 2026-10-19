module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Comparison.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.Predicates

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology
open scoped unitInterval

universe u

/-- Based homotopy extension is enough to construct the original
cone-to-quotient comparison's based inverse at a level. -/
theorem coneToCofiber_level_homotopyInverse_of_based_homotopyExtension
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (hf : BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map f)) :
    ∃ r : C(cofiberLevel f n,coneLevel f n),
      r (cofiberLevel f n).point = (coneLevel f n).point ∧
      (r.comp ((coneToCofiber f).level n)).HomotopicRel (ContinuousMap.id _) {(coneLevel f n).point} ∧
      (((coneToCofiber f).level n).comp r).HomotopicRel (ContinuousMap.id _) {(cofiberLevel f n).point} := by
  let c : C(X.level n × I,coneLevel f n) :=
    ⟨fun p => Quot.mk _ (.inr p),continuous_quot_mk.comp continuous_inr⟩
  obtain ⟨H,_,hH0,hHf⟩ := hf (coneLevel f n)
    ((evaluationFunctor n).map (coneInclusion f)) c
    (fun t => Quot.sound (ConeRelation.point t))
    (fun x => Quot.sound (ConeRelation.start x))
  exact coneToCofiber_level_homotopyInverse_of_extension f n H hH0 hHf

/-- The canonical comparison from the original literal cone to the original
quotient cofiber is a stable equivalence under levelwise based homotopy extension. -/
theorem coneToCofiber_stableEquivalence_of_based_homotopyExtension
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map f)) :
    stableEquivalences (coneToCofiber f) :=
  stableEquivalence_of_level_basedHomotopyInverse _
    (fun n => coneToCofiber_level_homotopyInverse_of_based_homotopyExtension f n (hf n))

end KIP126.StableHomotopy.Implementation.Prespectrum
