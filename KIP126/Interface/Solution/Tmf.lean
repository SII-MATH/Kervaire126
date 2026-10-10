import KIP126.Def.SpectralSequence.Computation.Predicates
import KIP126.Def.ClassicalAdams.Tmf.Model.Binding.Data
import KIP126.Def.StageInput.StandardSphere.Tmf.Predicates
import KIP126.Def.ClassicalAdams.Tmf.Model.Predicates
import KIP126.Interface.Challenge.Challenge2
import KIP126.Def.ClassicalAdams.Tmf.Br21.Data
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
import KIP126.Interface.Solution.Challenge2

/-! Coordinate-bound tmf comparison contracts and compatibility views of the
same Challenge2 delivery. These views make no additional object or coordinate
choice; their existence still depends on the unfinished Interface producer. -/

namespace KIP126.Challenge2
open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams Core.SpectralSequence
universe u v w

/-- am14 的 BR21 微分切片。同一代数对象的单位定义实际 Hurewicz，
固定 CSV 商中的 w₂² 与 β⁵g 经同一个坐标比较进入该对象的实际 Adams 塔。
这项只交付微分等式，不从它增加非零或存活。
来源：BR21 Table 5.4 / Theorem 5.18，印刷页196 / PDF第213页。
原书写 βg⁴；`CsvE2.betaGFourValue_eq_betaFiveGValue` 从同一商环关系证明
βg⁴ = β⁵g。固定坐标源为 v126.3.cw49；到实际 tmf E₂ 的比较另列。
本组尚不包含 tmf 的几何构造、乘法比较、θ₅ 像零或 125-stem 检测。 -/
structure TmfDifferentialInterface {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)) where
  target : Mon C
  coordinates : Tmf.E2Presentation H target
  br21 : HasDifferential (adamsTowerInternalSpectralSequence H.unit target.X) 3
    (16, 112) (19, 114) coordinates.v2Sixteen coordinates.betaFiveG

/-- Project the same target and coordinates from the compatibility interface. -/
def TmfDifferentialInterface.toModel {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    {H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)}
    (input : TmfDifferentialInterface H) : TmfModel H where
  target := input.target
  coordinates := input.coordinates

/-- BR21's differential on this exact algebra object and coordinate comparison. -/
def TmfModel.Br21Statement {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    {H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)}
    (model : TmfModel H) : Prop :=
  HasDifferential (adamsTowerInternalSpectralSequence H.unit model.target.X) 3
    (16, 112) (19, 114) model.coordinates.v2Sixteen model.coordinates.betaFiveG

/-- Reassemble the original tmf interface without a fresh choice. -/
def TmfModel.withDifferential {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    {H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)}
    (model : TmfModel H) (proof : model.Br21Statement) : TmfDifferentialInterface H where
  target := model.target
  coordinates := model.coordinates
  br21 := proof

/-- Original comparison API, definitionally the property of the same tmf model. -/
def StandardTmfMultiplicativeInterface
    (T : TmfDifferentialInterface standardFoundation.hf2) : Prop :=
  StandardTmfModelMultiplicativeInterface T.toModel

end KIP126.Challenge2


namespace KIP126.Interface.Solution

/-- The fixed tmf target with the coordinates from this exact delivery. -/
noncomputable def tmfModelOfDelivery (input : KIP126.Challenge2) :
    KIP126.Challenge2.TmfModel KIP126.Classical.Adams.standardFoundation.hf2 where
  target := KIP126.Def.standardTmfTarget
  coordinates := input.computation.bindings.tmfCoordinates

/-- Transport the source differential along this delivery's actual detector
comparison and identify both endpoints using its computation bindings. -/
theorem tmfBookDifferentialInterface_of_delivery (input : KIP126.Challenge2) :
    (tmfModelOfDelivery input).Br21BookStatement := by
  have transported := KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential
    KIP126.Classical.Adams.standardFoundation.hf2.unit
    input.literature.bindings.route.tmfBinding.detectorIso.inv
    input.literature.results.br21
  rw [← input.computation.bindings.tmf_v2Sixteen,
    ← input.computation.bindings.tmf_betaGFour] at transported
  exact transported

/-- Compatibility existence API retaining BR21's exact βg⁴ target. The model,
source comparison and coordinates all come from the one Interface producer;
this adapter does not prove that producer's remaining obligations. -/
theorem tmfBookDifferentialInterface :
    ∃ model : KIP126.Challenge2.TmfModel KIP126.Classical.Adams.standardFoundation.hf2,
      model.Br21BookStatement := by
  exact ⟨tmfModelOfDelivery challenge2, tmfBookDifferentialInterface_of_delivery challenge2⟩

/-- Pure transport through the proved equality in the SAME CSV quotient. -/
theorem br21Statement_of_book {C : Type*}
    [KIP126.StableHomotopy.StableHomotopyCategory C]
    [KIP126.StableHomotopy.HasFunctorialCofiber (C := C)]
    {H : KIP126.StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)}
    (model : KIP126.Challenge2.TmfModel H) (source : model.Br21BookStatement) :
    model.Br21Statement := by
  simpa only [KIP126.Challenge2.TmfModel.Br21BookStatement,
    KIP126.Challenge2.TmfModel.Br21Statement,
    KIP126.Classical.Adams.Tmf.E2Presentation.betaGFour_eq_betaFiveG] using source

/-- Repackage the same target and coordinates with the transported BR21
equation, using the equality in their fixed CSV quotient. -/
noncomputable def tmfDifferentialInterfaceOfDelivery (input : KIP126.Challenge2) :
    KIP126.Challenge2.TmfDifferentialInterface
      KIP126.Classical.Adams.standardFoundation.hf2 :=
  (tmfModelOfDelivery input).withDifferential
    (br21Statement_of_book (tmfModelOfDelivery input)
      (tmfBookDifferentialInterface_of_delivery input))

/-- am14: one algebra-object realization of the fixed coordinate algebra
and the BR21 d₃ equation, all on the same internal Adams tower.
This is a compatibility view of the producer's delivery. The Hurewicz
detection part of am14 is a further obligation. -/
theorem tmfDifferentialInterface :
    Nonempty (KIP126.Challenge2.TmfDifferentialInterface
      KIP126.Classical.Adams.standardFoundation.hf2) := by
  exact ⟨tmfDifferentialInterfaceOfDelivery challenge2⟩

/-- The multiplicative property uses the same delivered coordinates as the
BR21 equation, with no independently chosen differential interface. -/
theorem tmfMultiplicativeInterface_of_delivery (input : KIP126.Challenge2) :
    KIP126.Challenge2.StandardTmfMultiplicativeInterface
      (tmfDifferentialInterfaceOfDelivery input) := by
  exact input.computation.bindings.tmfMultiplicative

/-- The same BR21 realization and comparison preserve the actual
algebra-object unit and the actual Adams second-cycle product. This compatibility
existence API projects that property from the one Interface producer. -/
theorem tmfMultiplicativeInterface :
    ∃ T : KIP126.Challenge2.TmfDifferentialInterface
      KIP126.Classical.Adams.standardFoundation.hf2,
      KIP126.Challenge2.StandardTmfMultiplicativeInterface T := by
  exact ⟨tmfDifferentialInterfaceOfDelivery challenge2,
    tmfMultiplicativeInterface_of_delivery challenge2⟩

end KIP126.Interface.Solution
