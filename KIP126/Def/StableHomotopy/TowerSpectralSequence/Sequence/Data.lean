import KIP126.Def.StableHomotopy.TowerSpectralSequence.PreSS.Proofs

/-! Assemble the actual tower spectral sequence from its constructed
kernel/image pages and quotient differential, using the separately stated
proved laws. No convergence condition is asserted here. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

noncomputable def sequence : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  toPreSS := preSS T P
  d_comp_d := preSS_d_comp_d T P
  Z_succ := preSS_Z_succ T P
  B_succ := preSS_B_succ T P

end KIP126.StableHomotopy.TowerSpectralSequence
