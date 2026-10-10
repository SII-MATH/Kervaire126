import KIP126.Def.ClassicalAdams.Tmf.CsvE2.Proofs

/-! Typed classes from the fixed tmf coordinate algebra, without fresh choices. -/
namespace KIP126.Classical.Adams.Tmf.CsvE2

noncomputable def v2Sixteen : E2At 16 112 := ⟨v2SixteenValue, v2SixteenValue_mem⟩

noncomputable def betaFiveG : E2At 19 114 := ⟨betaFiveGValue, betaFiveGValue_mem⟩

/-- The target in the notation of BR21 Table 5.4. -/
noncomputable def betaGFour : E2At 19 114 := ⟨betaGFourValue, betaGFourValue_mem⟩

theorem betaGFour_eq_betaFiveG : betaGFour = betaFiveG :=
  Subtype.ext betaGFourValue_eq_betaFiveGValue

end KIP126.Classical.Adams.Tmf.CsvE2
