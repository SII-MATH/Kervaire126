module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Stabilized.Map.Proofs
public import KIP126.Def.Topology.Path.Translation.Pointed.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- A bijection at the constant loop for an actual prespectrum loop
map propagates to every point of that whole level loop space. -/
theorem loopMap_level_homotopy_bijective_at_all_points
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (hf : Function.Bijective ((loopMap f).levelHomotopy n r)) (p : (loop X).level n) :
    Function.Bijective (KIP126.Topology.continuousHomotopyMap ((loopMap f).level n)
      p ((loopMap f).level n p) rfl r) :=
  KIP126.Topology.continuousBasedLoopMap_homotopy_bijective_at_all_points
    (f.level n) (X.level n).point (Y.level n).point (f.point n) r hf p

/-- The same all-basepoint propagation applies to the actual
spectrification step, whose specified level maps are literal loop maps. -/
theorem spectrificationStepMap_level_homotopy_bijective_at_all_points
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (hf : Function.Bijective ((spectrificationStepMap f).levelHomotopy n r))
    (p : (spectrificationStep X).level n) :
    Function.Bijective (KIP126.Topology.continuousHomotopyMap ((spectrificationStepMap f).level n)
      p ((spectrificationStepMap f).level n p) rfl r) :=
  KIP126.Topology.continuousBasedLoopMap_homotopy_bijective_at_all_points
    (f.level (n+1)) (X.level (n+1)).point (Y.level (n+1)).point (f.point (n+1)) r hf p

end KIP126.StableHomotopy.Implementation.Prespectrum
