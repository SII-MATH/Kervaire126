import KIPBase.StableHomotopy.Category
import KIPBase.StableHomotopy.StableModelCategory
import KIPBase.StableHomotopy.DerivedTensor

/-!
# The chosen model for the stable homotopy category

The project develops the stable homotopy category through an abstract
interface. This package records one chosen model category of spectra and
identifies its localization with the category used by that interface.
The assumption is kept in one explicit axiom so downstream statements can
depend on the model realization transparently.
-/

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace KIPBase.StableHomotopy

/-- A model category of spectra together with the stable homotopy category
structure on its homotopy category. -/
structure SpectrumModelRealization where
  /-- Objects of the chosen point-set category of spectra. -/
  Spectra : Type u
  /-- The category structure on spectra. -/
  spectraCategory : Category.{v} Spectra
  /-- The monoidal structure on spectra. -/
  spectraMonoidalCategory : MonoidalCategory Spectra
  /-- The symmetric structure on spectra. -/
  spectraSymmetricCategory : SymmetricCategory Spectra
  /-- Closedness of the monoidal structure. -/
  spectraMonoidalClosed : MonoidalClosed Spectra
  /-- The limits and colimits needed for the model and tensor axioms. -/
  spectraHasLimits : HasLimits.{v, u} Spectra
  spectraHasColimits : HasColimits.{v, u} Spectra
  spectraHasPushouts : HasPushouts.{v, u} Spectra
  spectraHasInitial : HasInitial.{v, u} Spectra
  /-- Pointed-category structures on spectra. -/
  spectraHasZeroMorphisms : HasZeroMorphisms.{v, u} Spectra
  spectraHasZeroObject : HasZeroObject.{v, u} Spectra
  /-- The underlying model structure. -/
  spectraModelCategory : ModelCategory Spectra
  /-- The chosen spectra model is cofibrantly generated. This provides the
  functorial factorizations needed for derived tensor and homotopy cofiber
  constructions. -/
  spectraCofibrantlyGenerated :
    letI := spectraCategory
    letI := spectraModelCategory
    CofibrantlyGeneratedModelCategory Spectra
  /-- The stable symmetric monoidal model structure on spectra. -/
  stableSymmetricMonoidalModelCategory :
    letI := spectraCategory
    letI := spectraMonoidalCategory
    letI := spectraSymmetricCategory
    letI := spectraMonoidalClosed
    letI := spectraHasLimits
    letI := spectraHasColimits
    letI := spectraHasPushouts
    letI := spectraHasInitial
    letI := spectraHasZeroMorphisms
    letI := spectraHasZeroObject
    letI := spectraModelCategory
    StableMonoidalCategory Spectra
  /-- The existing stable homotopy category structure on the localization. -/
  stableHomotopyCategoryStructure :
    letI := spectraCategory
    letI := spectraModelCategory
    letI := stableSymmetricMonoidalModelCategory
    StableHomotopyCategory.{u, max u v} (Ho Spectra)

/-- The chosen spectra model and its homotopy category are part of the
foundational model input. In particular, this asserts both that spectra form
a stable symmetric monoidal model category and that its `Ho` is the stable
homotopy category used throughout this library. -/
axiom standardSpectrumModel : SpectrumModelRealization.{u, v}

/-- The category of spectra selected by the model input. -/
abbrev Spectra : Type u := standardSpectrumModel.{u, v}.Spectra

noncomputable instance spectraCategory : Category.{v} Spectra :=
  standardSpectrumModel.{u, v}.spectraCategory

noncomputable instance spectraMonoidalCategory : MonoidalCategory Spectra :=
  standardSpectrumModel.{u, v}.spectraMonoidalCategory

noncomputable instance spectraSymmetricCategory : SymmetricCategory Spectra :=
  standardSpectrumModel.{u, v}.spectraSymmetricCategory

noncomputable instance spectraMonoidalClosed : MonoidalClosed Spectra :=
  standardSpectrumModel.{u, v}.spectraMonoidalClosed

noncomputable instance spectraHasLimits : HasLimits.{v, u} Spectra :=
  standardSpectrumModel.{u, v}.spectraHasLimits

noncomputable instance spectraHasColimits : HasColimits.{v, u} Spectra :=
  standardSpectrumModel.{u, v}.spectraHasColimits

noncomputable instance spectraHasPushouts : HasPushouts.{v, u} Spectra :=
  standardSpectrumModel.{u, v}.spectraHasPushouts

noncomputable instance spectraHasInitial : HasInitial.{v, u} Spectra :=
  standardSpectrumModel.{u, v}.spectraHasInitial

noncomputable instance spectraHasZeroMorphisms : HasZeroMorphisms.{v, u} Spectra :=
  standardSpectrumModel.{u, v}.spectraHasZeroMorphisms

noncomputable instance spectraHasZeroObject : HasZeroObject.{v, u} Spectra :=
  standardSpectrumModel.{u, v}.spectraHasZeroObject

noncomputable instance spectraModelCategory : ModelCategory Spectra :=
  standardSpectrumModel.{u, v}.spectraModelCategory

noncomputable instance spectraCofibrantlyGenerated :
    CofibrantlyGeneratedModelCategory Spectra := by
  letI : Category.{v} Spectra := standardSpectrumModel.{u, v}.spectraCategory
  letI : ModelCategory Spectra := standardSpectrumModel.{u, v}.spectraModelCategory
  exact standardSpectrumModel.{u, v}.spectraCofibrantlyGenerated

noncomputable instance spectraStableMonoidalModelCategory :
    StableMonoidalCategory Spectra := by
  letI : Category.{v} Spectra := standardSpectrumModel.{u, v}.spectraCategory
  letI : MonoidalCategory Spectra := standardSpectrumModel.{u, v}.spectraMonoidalCategory
  letI : SymmetricCategory Spectra := standardSpectrumModel.{u, v}.spectraSymmetricCategory
  letI : MonoidalClosed Spectra := standardSpectrumModel.{u, v}.spectraMonoidalClosed
  letI : HasLimits Spectra := standardSpectrumModel.{u, v}.spectraHasLimits
  letI : HasColimits Spectra := standardSpectrumModel.{u, v}.spectraHasColimits
  letI : HasPushouts Spectra := standardSpectrumModel.{u, v}.spectraHasPushouts
  letI : HasInitial Spectra := standardSpectrumModel.{u, v}.spectraHasInitial
  letI : HasZeroMorphisms Spectra := standardSpectrumModel.{u, v}.spectraHasZeroMorphisms
  letI : HasZeroObject Spectra := standardSpectrumModel.{u, v}.spectraHasZeroObject
  letI : ModelCategory Spectra := standardSpectrumModel.{u, v}.spectraModelCategory
  exact standardSpectrumModel.{u, v}.stableSymmetricMonoidalModelCategory

/-- The stable homotopy category is definitionally the homotopy category of
the selected category of spectra. -/
abbrev StableHomotopyCat : Type u := Ho.{v, u} Spectra

noncomputable instance stableHomotopyCatCategory :
    StableHomotopyCategory.{u, max u v} StableHomotopyCat := by
  letI : Category.{v} Spectra := standardSpectrumModel.{u, v}.spectraCategory
  letI : ModelCategory Spectra := standardSpectrumModel.{u, v}.spectraModelCategory
  letI : MonoidalCategory Spectra := standardSpectrumModel.{u, v}.spectraMonoidalCategory
  letI : SymmetricCategory Spectra := standardSpectrumModel.{u, v}.spectraSymmetricCategory
  letI : MonoidalClosed Spectra := standardSpectrumModel.{u, v}.spectraMonoidalClosed
  letI : HasLimits Spectra := standardSpectrumModel.{u, v}.spectraHasLimits
  letI : HasColimits Spectra := standardSpectrumModel.{u, v}.spectraHasColimits
  letI : HasPushouts Spectra := standardSpectrumModel.{u, v}.spectraHasPushouts
  letI : HasInitial Spectra := standardSpectrumModel.{u, v}.spectraHasInitial
  letI : HasZeroMorphisms Spectra := standardSpectrumModel.{u, v}.spectraHasZeroMorphisms
  letI : HasZeroObject Spectra := standardSpectrumModel.{u, v}.spectraHasZeroObject
  letI : StableMonoidalCategory Spectra :=
    standardSpectrumModel.{u, v}.stableSymmetricMonoidalModelCategory
  exact standardSpectrumModel.{u, v}.stableHomotopyCategoryStructure

noncomputable instance (priority := 1000) stableHomotopyCatUnderlyingCategory :
    Category StableHomotopyCat :=
  stableHomotopyCatCategory.toCategory

/-- The tensor bifunctor on the stable homotopy category, constructed by
cofibrantly replacing both spectrum inputs before smashing. -/
noncomputable def stableHomotopyDerivedTensor :
    @CategoryTheory.Functor (Ho Spectra)
      (weakEquivalences Spectra).instCategoryLocalization
      (@CategoryTheory.Functor (Ho Spectra)
        (weakEquivalences Spectra).instCategoryLocalization (Ho Spectra)
        (weakEquivalences Spectra).instCategoryLocalization)
      (@CategoryTheory.Functor.category (Ho Spectra)
        (weakEquivalences Spectra).instCategoryLocalization (Ho Spectra)
        (weakEquivalences Spectra).instCategoryLocalization) := by
  letI : Category.{v} Spectra := standardSpectrumModel.{u, v}.spectraCategory
  letI : ModelCategory Spectra := standardSpectrumModel.{u, v}.spectraModelCategory
  letI : MonoidalCategory Spectra :=
    standardSpectrumModel.{u, v}.spectraMonoidalCategory
  letI : SymmetricCategory Spectra :=
    standardSpectrumModel.{u, v}.spectraSymmetricCategory
  letI : MonoidalClosed Spectra :=
    standardSpectrumModel.{u, v}.spectraMonoidalClosed
  letI : HasLimits Spectra := standardSpectrumModel.{u, v}.spectraHasLimits
  letI : HasColimits Spectra := standardSpectrumModel.{u, v}.spectraHasColimits
  letI : HasPushouts Spectra := standardSpectrumModel.{u, v}.spectraHasPushouts
  letI : HasInitial Spectra := standardSpectrumModel.{u, v}.spectraHasInitial
  letI : SymMonoidalModelCategory Spectra := inferInstance
  letI : CofibrantlyGeneratedModelCategory Spectra :=
    standardSpectrumModel.{u, v}.spectraCofibrantlyGenerated
  exact derivedTensorBifunctor Spectra

/-! The additional structure assumptions are attached only to the chosen
homotopy category of spectra, not to every abstract stable homotopy category. -/

/-- The homotopy category of the selected spectra model is closed symmetric
tensor triangulated. This assumption is specific to `StableHomotopyCat`. -/
axiom sh_closedSymmetricTT :
    ClosedSymmetricTensorTriangulated.{u, max u v} StableHomotopyCat

/-- The homotopy category of the selected spectra model has tensor-compatible
functorial cofibers. This assumption is specific to `StableHomotopyCat`. -/
axiom sh_tensor_functorial_cofiber :
    TensorTriangulatedCatWithFunctorialCofiber.{u, max u v} StableHomotopyCat

noncomputable instance stableHomotopyCatEnhancement :
    StableHomotopyCategoryEnhancement StableHomotopyCat where
  closedSymmetricTensorTriangulated := sh_closedSymmetricTT
  tensorTriangulatedFunctorialCofiber := sh_tensor_functorial_cofiber

end KIPBase.StableHomotopy
