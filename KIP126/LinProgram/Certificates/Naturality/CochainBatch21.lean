import KIP126.LinProgram.Generated.Naturality.CochainBatch21

/-! A complete finite batch on the recovered native generator families.
The two omitted cochain requests have t<2; both generators remain in the full
84-generator family. No omitted database row is interpreted as an actual zero
space. No native-to-archived or native-to-actual comparison is inferred. -/
namespace KIP126.LinModule.NaturalityCochainBatch21
open CochainMapCertificate RawData.NaturalityCochainBatch21

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def batchCheck : Bool :=
  (List.finRange 82).all (fun i => check mapColumns (entries i))

theorem batch_checked : batchCheck = true := by decide +kernel

theorem entry_checked (i : Fin 82) : check mapColumns (entries i) = true :=
  (List.all_eq_true.mp batch_checked) i (List.mem_finRange i)

/-- All 82 requested cochains are evaluated by this same 48-column map. -/
theorem entry_pullback (i : Fin 82) :
    pullback mapColumns (basis (entries i).source) =
      targetValue (entries i).targets :=
  check_sound mapColumns (entries i) (entry_checked i)

/-- The complete column equations are equalities of precomposed linear functionals. -/
theorem entry_precomposition (i : Fin 82) :
    (functional (basis (entries i).source)).comp (augmentedMap mapColumns) =
      functional (targetValue (entries i).targets) :=
  check_sound_precomposition mapColumns (entries i) (entry_checked i)

theorem sphere_minimal_checked : minimalCheck sphereDifferentials = true := by
  decide +kernel

theorem ceta_minimal_checked : minimalCheck cetaDifferentials = true := by
  decide +kernel

/-- Every coefficient in all 48 retained sphere differential columns has positive degree. -/
theorem sphere_positive (i : Fin 48) (t : Term 48)
    (ht : t ∈ sphereDifferentials i) : 0 < t.degree :=
  minimalCheck_sound sphereDifferentials sphere_minimal_checked i t ht

/-- Every coefficient in all 84 retained Ceta differential columns has positive degree. -/
theorem ceta_positive (i : Fin 84) (t : Term 84)
    (ht : t ∈ cetaDifferentials i) : 0 < t.degree :=
  minimalCheck_sound cetaDifferentials ceta_minimal_checked i t ht

/-- The full finite native sphere cochain differential is zero. -/
theorem sphere_cochain_differential_zero : pullback sphereDifferentials = 0 :=
  pullback_eq_zero_of_minimalCheck sphereDifferentials sphere_minimal_checked

/-- The full finite native Ceta cochain differential is zero. -/
theorem ceta_cochain_differential_zero : pullback cetaDifferentials = 0 :=
  pullback_eq_zero_of_minimalCheck cetaDifferentials ceta_minimal_checked

/-- Every retained Ceta generator with t>=2 occurs among the requests, and conversely.
The universe is the complete fixed 84-generator family, not the actual infinite resolution. -/
theorem entries_cover : ∀ j : Fin 84,
    (2 ≤ (cetaGenerators j).t ↔ ∃ i : Fin 82, (entries i).source = j) := by
  decide +kernel

theorem requests_in_range : ∀ i : Fin 82,
    2 ≤ (cetaGenerators (entries i).source).t ∧
      (cetaGenerators (entries i).source).t ≤ 21 := by
  decide +kernel

theorem family_bounds :
    (∀ i : Fin 48, (sphereGenerators i).t ≤ 19) ∧
    (∀ i : Fin 84, (cetaGenerators i).t ≤ 21) := by
  decide +kernel


/-- The retained native differential columns have the expected bidegree. -/
theorem sphere_differentials_graded : ∀ i : Fin 48, ∀ t ∈ sphereDifferentials i,
    (sphereGenerators t.generator).s + 1 = (sphereGenerators i).s ∧
      (sphereGenerators t.generator).t + t.degree = (sphereGenerators i).t := by
  decide +kernel

/-- Every retained Ceta differential term lands one filtration lower. -/
theorem ceta_differentials_graded : ∀ i : Fin 84, ∀ t ∈ cetaDifferentials i,
    (cetaGenerators t.generator).s + 1 = (cetaGenerators i).s ∧
      (cetaGenerators t.generator).t + t.degree = (cetaGenerators i).t := by
  decide +kernel

/-- The full native map preserves filtration and raises internal degree by two. -/
theorem map_columns_graded : ∀ i : Fin 48, ∀ t ∈ mapColumns i,
    (cetaGenerators t.generator).s = (sphereGenerators i).s ∧
      (cetaGenerators t.generator).t + t.degree = (sphereGenerators i).t + 2 := by
  decide +kernel

end KIP126.LinModule.NaturalityCochainBatch21
