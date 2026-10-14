module

public import KIP126.Interface.Challenge.Challenge2
public import KIP126.LinProgram.Certificates.BasisCertification.Proofs
public import KIP126.Interface.Solution.LinProgram.Basis.Certification

@[expose] public section


/-!
# Interface/Solution/LinProgram/Basis/Comparison

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

namespace KIP126.Interface.Solution

open KIP126.LinE2

/-- Transport the same certified CSV basis through the specified comparison.
The only certification debt is the Interface helper; no Main consumer axiom
or Challenge placeholder is used. -/
theorem sphereBasis (P : KIP126.Classical.Adams.LinE2Presentation) :
    Nonempty (KIP126.Challenge2.SphereBasisInterface P) := by
  refine ⟨{
    coordinates := fun s t ht => (P.comparison s t ht).symm.trans
      ((coordinatesOfCertification s t
        (LinE2.basisTable_correct s t ht)).restrictScalars ℤ)
    csv_values := ?_ }⟩
  intro s t ht i
  change ((P.comparison s t ht).symm
    ((P.comparison s t ht)
      ((coordinatesOfCertification s t (LinE2.basisTable_correct s t ht)).symm
        (Finsupp.single i 1)))).val = basisValue (basisRowAt s t i)
  rw [LinearEquiv.symm_apply_apply,
    ← coordinatesOfCertification_basis s t (LinE2.basisTable_correct s t ht) i,
    LinearEquiv.symm_apply_apply]
  exact basisOfCertification_val s t (LinE2.basisTable_correct s t ht) i

end KIP126.Interface.Solution
