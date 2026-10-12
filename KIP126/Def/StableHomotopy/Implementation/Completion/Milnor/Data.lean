module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Product.Small.Instances
public import KIP126.Def.StableHomotopy.Implementation.Completion.Triangulated.Instances
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Existence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

/-- Every actual sequence of local spectra has a Milnor homotopy limit,
using the constructed products and the proved local triangulated structure. -/
noncomputable def homotopyLimit (D : InverseSequence CompletedSpectrum) :
    CompletedSpectrum := Classical.choose D.exists_homotopyLimit

noncomputable def homotopyLimitWitness (D : InverseSequence CompletedSpectrum) :
    SequentialHomotopyLimit D (homotopyLimit D) :=
  Classical.choice (Classical.choose_spec D.exists_homotopyLimit)

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
