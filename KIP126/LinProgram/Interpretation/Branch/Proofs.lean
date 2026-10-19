module

public import KIP126.LinProgram.Interpretation.Branch.Predicates
public import KIP126.Def.SpectralSequence.Computation.State.Proofs

@[expose] public section


/-! Sound inference rules for the existing actual-equation interpretation.
Coverage and refutations are mathematical proof obligations, not log fields.
These rules do not certify any retained database trial by themselves. -/
namespace KIP126.Computation.LinProofs.Branch
open CategoryTheory KIP126.Core KIP126.Core.SpectralSequence
universe u v w
variable {R : Type u} [Ring R] {ι : Type w}
  {E : ι → SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}

theorem contextHolds_nil : ContextHolds (E := E) [] := by
  intro e he
  simp at he

/-- Exhaustiveness and refutation of all alternatives justify the selected
actual differential equation in the same enclosing context. -/
theorem CandidateElimination.sound {context : List (FiniteEquation E)}
    {window : CandidateWindow E} {selected : FiniteEquation E}
    (h : CandidateElimination context window selected) :
    ConditionalFact context selected := by
  intro hc
  obtain ⟨_, hcoverage, hrefute⟩ := h
  obtain ⟨e, he, hstatement⟩ := hcoverage hc
  by_cases hes : e = selected
  · simpa only [hes] using hstatement
  · exact False.elim (hrefute e he hes hc hstatement)

/-- An empty outer context produces an actual equation, provided the whole
candidate-elimination obligation has been proved. -/
theorem CandidateElimination.sound_nil {window : CandidateWindow E}
    {selected : FiniteEquation E}
    (h : CandidateElimination [] window selected) : selected.Statement :=
  h.sound contextHolds_nil

/-- Exhausting a proved covering window refutes the entire actual context. -/
theorem CandidateExhaustion.sound {context : List (FiniteEquation E)}
    {window : CandidateWindow E} (h : CandidateExhaustion context window) :
    Contradiction context := by
  intro hc
  obtain ⟨hcoverage, hrefute⟩ := h
  obtain ⟨e, he, hstatement⟩ := hcoverage hc
  exact hrefute e he hc hstatement

theorem EquationConflict.sound {context : List (FiniteEquation E)}
    {e : FiniteEquation E} (h : EquationConflict context e) :
    Contradiction context := by
  intro hc
  exact h.2 hc (h.1 hc)

/-- A zero-source equation is refuted by an actual earlier-boundary exclusion
under the same complete context. This is the mathematical contradiction at
the end of diagnostics such as log 152097; obtaining its zero-source equation
from the nonzero-source trial still requires the actual Leibniz calculation. -/
theorem TrialRefuted.of_zero_source {context : List (FiniteEquation E)}
    {trial : FiniteEquation E} (hr : 3 ≤ trial.r) (hx : trial.source = 0)
    (hy : ContextHolds context →
      ¬ IsBoundaryBy (E trial.object) (trial.r - 1) trial.targetDegree trial.target) :
    TrialRefuted context trial := by
  intro hc ht
  apply hy hc
  have h : HasDifferential (E trial.object) trial.r trial.sourceDegree
      trial.targetDegree 0 trial.target := by
    simpa only [FiniteEquation.Statement, hx] using ht
  exact h.isBoundaryBy_of_source_zero hr

/-- Refute a trial by a contradiction in the context that includes it. -/
theorem TrialRefuted.of_contradiction_cons {context : List (FiniteEquation E)}
    {trial : FiniteEquation E} (h : Contradiction (trial :: context)) :
    TrialRefuted context trial := by
  intro hc ht
  apply h
  intro e he
  obtain rfl | he := List.mem_cons.mp he
  · exact ht
  · exact hc e he

end KIP126.Computation.LinProofs.Branch
