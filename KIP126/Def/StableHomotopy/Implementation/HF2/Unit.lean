module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Additive.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Zero.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The normalized ordinary source sphere map representing the coefficient
one. Its source is the specified sphere, identified with the point-set sphere
by `Prespectrum.sourceSphere_zero`. -/
noncomputable def SourceHF2Model.sourceUnit (M : SourceHF2Model) :
    Prespectrum.sourceSphere 0 ⟶ sourceLocalization.obj M.spectrum :=
  Prespectrum.sourceStableHomotopyEquiv M.spectrum 0 (M.pi0.symm 1)

/-- The normalized coefficient unit for the fully constructed fixed source. -/
noncomputable def sourceHF2Unit :
    Prespectrum.sourceSphere 0 ⟶ sourceLocalization.obj sourceHF2.spectrum :=
  sourceHF2.sourceUnit

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The unit sends the represented source-sphere generator to the normalized coefficient one. -/
theorem SourceHF2Model.sourceUnit_coefficient (M : SourceHF2Model) :
    M.pi0 ((sourceStableHomotopyFunctor 0).map M.sourceUnit
      (Prespectrum.sourceSphereGenerator 0)) = 1 := by
  rw [← Prespectrum.sourceStableHomotopyEquiv_symm_apply]
  change M.pi0 ((Prespectrum.sourceStableHomotopyEquiv M.spectrum 0).symm
    (Prespectrum.sourceStableHomotopyEquiv M.spectrum 0 (M.pi0.symm 1))) = 1
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem SourceHF2Model.sourceUnit_unique (M : SourceHF2Model)
    (f : Prespectrum.sourceSphere 0 ⟶ sourceLocalization.obj M.spectrum)
    (hf : M.pi0 ((sourceStableHomotopyFunctor 0).map f
      (Prespectrum.sourceSphereGenerator 0)) = 1) : f = M.sourceUnit := by
  apply (Prespectrum.sourceStableHomotopyEquiv M.spectrum 0).symm.injective
  apply M.pi0.injective
  rw [Prespectrum.sourceStableHomotopyEquiv_symm_apply,
    Prespectrum.sourceStableHomotopyEquiv_symm_apply, hf, M.sourceUnit_coefficient]

theorem SourceHF2Model.sourceUnit_ne_zero (M : SourceHF2Model) : M.sourceUnit ≠ 0 := by
  intro h
  have hz : M.pi0.symm 1 = 0 :=
    (Prespectrum.sourceStableHomotopyEquiv M.spectrum 0).injective
      (h.trans (Prespectrum.sourceStableHomotopyEquiv_zero M.spectrum 0).symm)
  have h' := congrArg M.pi0 hz
  rw [Equiv.apply_symm_apply, M.pi0_map_zero] at h'
  exact one_ne_zero h'

end KIP126.StableHomotopy.Implementation

end
