module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Comparison.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.HomotopyEquivalence.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- For level maps with genuine homotopy extension, the canonical
literal-cone collapse is an actual stable equivalence. -/
theorem coneToCofiber_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension (TopCat.ofHom (f.level n))) :
    stableEquivalences (coneToCofiber f) :=
  stableEquivalence_of_level_basedHomotopyInverse _
    (fun n => coneToCofiber_level_homotopyInverse_exists f n (hf n))
end KIP126.StableHomotopy.Implementation.Prespectrum
