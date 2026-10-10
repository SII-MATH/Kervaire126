import KIP126.LinProgram.Generated.Naturality.CochainBatch40

/-! Complete finite cochain equations for all 259 original Ceta basis records
with 2 <= t <= 40. Sources and targets may be sums of dual generators. The
full 261/155 chain-generator families are retained; these finite data neither
prove that the archived representatives form a basis nor identify actual Ext. -/
namespace KIP126.LinModule.NaturalityCochainBatch40
open CochainMapCertificate RawData.NaturalityCochainBatch40

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def batchCheck : Bool :=
  (List.finRange 259).all (fun i => checkCombinationSupport augmentationColumns (entries i))

theorem augmentation_columns_match : ∀ j : Fin 155,
    augmentationSupport (mapColumns j) = augmentationColumns j := by decide +kernel

theorem batch_checked : batchCheck = true := by decide +kernel

theorem entry_checked (i : Fin 259) : checkCombination mapColumns (entries i) = true :=
  checkCombination_of_support mapColumns augmentationColumns (entries i)
    augmentation_columns_match ((List.all_eq_true.mp batch_checked) i (List.mem_finRange i))

/-- All requested combinations are evaluated on all columns of this one map. -/
theorem entry_pullback (i : Fin 259) :
    pullback mapColumns (targetValue (entries i).sources) =
      targetValue (entries i).targets :=
  checkCombination_sound mapColumns (entries i) (entry_checked i)

/-- Equality of precomposed linear functionals on the complete finite family. -/
theorem entry_precomposition (i : Fin 259) :
    (functional (targetValue (entries i).sources)).comp (augmentedMap mapColumns) =
      functional (targetValue (entries i).targets) :=
  checkCombination_sound_precomposition mapColumns (entries i) (entry_checked i)

theorem sphere_minimal_checked : minimalCheck sphereDifferentials = true := by
  decide +kernel

theorem ceta_minimal_checked : minimalCheck cetaDifferentials = true := by
  decide +kernel

theorem sphere_positive (i : Fin 155) (t : Term 155)
    (ht : t ∈ sphereDifferentials i) : 0 < t.degree :=
  minimalCheck_sound sphereDifferentials sphere_minimal_checked i t ht

theorem ceta_positive (i : Fin 261) (t : Term 261)
    (ht : t ∈ cetaDifferentials i) : 0 < t.degree :=
  minimalCheck_sound cetaDifferentials ceta_minimal_checked i t ht

theorem sphere_cochain_differential_zero : pullback sphereDifferentials = 0 :=
  pullback_eq_zero_of_minimalCheck sphereDifferentials sphere_minimal_checked

theorem ceta_cochain_differential_zero : pullback cetaDifferentials = 0 :=
  pullback_eq_zero_of_minimalCheck cetaDifferentials ceta_minimal_checked

/-- Every selected original native record ID occurs once. This is a data
coverage theorem, not an assertion that these cochains form a basis. -/
theorem native_record_coverage : ∀ i : Fin 259,
    (entries i).nativeBasisId = i.val + 2 := by
  decide +kernel

theorem requests_in_range : ∀ i : Fin 259, ∀ j ∈ (entries i).sources,
    2 ≤ (cetaGenerators j).t ∧ (cetaGenerators j).t ≤ 40 := by
  decide +kernel

theorem family_bounds :
    (∀ i : Fin 155, (sphereGenerators i).t ≤ 38) ∧
    (∀ i : Fin 261, (cetaGenerators i).t ≤ 40) := by
  decide +kernel

theorem sphere_differentials_graded : ∀ i : Fin 155, ∀ t ∈ sphereDifferentials i,
    (sphereGenerators t.generator).s + 1 = (sphereGenerators i).s ∧
      (sphereGenerators t.generator).t + t.degree = (sphereGenerators i).t := by
  decide +kernel

theorem ceta_differentials_graded : ∀ i : Fin 261, ∀ t ∈ cetaDifferentials i,
    (cetaGenerators t.generator).s + 1 = (cetaGenerators i).s ∧
      (cetaGenerators t.generator).t + t.degree = (cetaGenerators i).t := by
  decide +kernel

theorem map_columns_graded : ∀ i : Fin 155, ∀ t ∈ mapColumns i,
    (cetaGenerators t.generator).s = (sphereGenerators i).s ∧
      (cetaGenerators t.generator).t + t.degree = (sphereGenerators i).t + 2 := by
  decide +kernel

end KIP126.LinModule.NaturalityCochainBatch40
