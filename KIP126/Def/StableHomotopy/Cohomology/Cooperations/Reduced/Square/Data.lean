import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The existing reduced tensor construction, with a reduced cooperation
in its remaining factor as well. No new quotient or page is introduced. -/
abbrev reducedCooperationSquare (n : ℤ) :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  reducedCooperationTensor H R (fun i => LinearMap.ker (cooperationCounitF2 H R i)) n

/-- Include both reduced factors into the original cooperation tensor square. -/
def reducedCooperationSquareInclusion (n : ℤ) :
    reducedCooperationSquare H R n →ₗ[ZMod 2]
      cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  exact (cooperationTensorMap H R (fun i => LinearMap.ker (cooperationCounitF2 H R i))
    (fun i => (LinearMap.ker (cooperationCounitF2 H R i)).subtype) n).comp
      (reducedCooperationTensorInclusion H R
        (fun i => LinearMap.ker (cooperationCounitF2 H R i)) n)

end
end KIP126.StableHomotopy.Cohomology
