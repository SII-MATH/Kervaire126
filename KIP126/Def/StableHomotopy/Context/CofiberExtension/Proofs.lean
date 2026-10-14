module

public import KIP126.Def.StableHomotopy.Context.CofiberExtension.Data
public import KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section


/-! Extending a map along the shifted inclusion of the already specified
cofiber, with the signs of the actual shifted triangle. The vanishing composite stays explicit;
no nullhomotopy, actual CW object, or independent triangle is postulated. -/
namespace KIP126.StableHomotopy.CofiberExtension

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v
section ThirdObjectTransport

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

private theorem replace_third_object {X Y Z Z' : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) (e : Z ≅ Z') :
    Triangle.mk f (g ≫ e.hom) (e.inv ≫ h) ∈ distTriang C := by
  exact isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by simp [Triangle.mk]) (by simp [Triangle.mk]) (by simp [Triangle.mk]))

end ThirdObjectTransport

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The signed third arrow is compatible with positive shifted first and
second arrows, in every integer shift. -/
theorem shiftedCofiberTriangle_distinguished {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    shiftedCofiberTriangle f n ∈ distTriang C := by
  let U := (Triangle.shiftFunctor C n).obj
    (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
  have hU : U ∈ distTriang C :=
    Triangle.shift_distinguished _ (HasFunctorialCofiber.cofib_distinguished f) n
  let V := Triangle.mk (f⟦n⟧') ((HasFunctorialCofiber.cofibι f)⟦n⟧') U.mor₃
  let e : V ≅ U := Triangle.isoMk _ _ (Iso.refl _)
    (n.negOnePow • Iso.refl _) (Iso.refl _)
    (by
      change f⟦n⟧' ≫ (n.negOnePow • 𝟙 _) = 𝟙 _ ≫ (n.negOnePow • f⟦n⟧')
      simp only [Linear.comp_units_smul, Category.comp_id, Category.id_comp])
    (by
      change (HasFunctorialCofiber.cofibι f)⟦n⟧' ≫ 𝟙 _ =
        (n.negOnePow • 𝟙 _) ≫ (n.negOnePow • (HasFunctorialCofiber.cofibι f)⟦n⟧')
      simp only [Linear.units_smul_comp, Linear.comp_units_smul,
        Category.comp_id, Category.id_comp, smul_smul, Int.units_mul_self, one_smul])
    (by
      change U.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 U.obj₁) = 𝟙 U.obj₃ ≫ U.mor₃
      exact ((congrArg (fun k => U.mor₃ ≫ k)
        ((shiftFunctor C (1 : ℤ)).map_id U.obj₁)).trans
          (Category.comp_id U.mor₃)).trans (Category.id_comp U.mor₃).symm)
  exact isomorphic_distinguished _ hU _ e

/-- Exactness of the actual shifted cofiber triangle, for every integer
shift and every target object. The normalized distinguished triangle uses
the positive shifted inclusion and retains the signed connecting map. -/
theorem exists_extension_of_shift_comp_zero {X Y Z : C}
    (f : X ⟶ Y) (n : ℤ) (a : Y⟦n⟧ ⟶ Z)
    (hzero : f⟦n⟧' ≫ a = 0) :
    ∃ g : (HasFunctorialCofiber.cofib f)⟦n⟧ ⟶ Z,
      (HasFunctorialCofiber.cofibι f)⟦n⟧' ≫ g = a := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ (shiftedCofiberTriangle f n)
    (shiftedCofiberTriangle_distinguished f n) a hzero
  exact ⟨g, hg.symm⟩

/-- The same-category η/ν extension at shift three. It assumes exactly the
specified suspended composite is zero; it does not prove that premise. -/
theorem exists_eta_nu_extension
    (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
    (ν : Sphere (C := C) 3 ⟶ SphereSpectrum)
    (hzero : (shiftFunctor C (3 : ℤ)).map η ≫ ν = 0) :
    ∃ g : (HasFunctorialCofiber.cofib η)⟦(3 : ℤ)⟧ ⟶ SphereSpectrum,
      (HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧' ≫ g = ν :=
  exists_extension_of_shift_comp_zero η 3 ν hzero

/-- The same octahedron compares the cofiber of an extension with the
cofiber of its prescribed restriction. The resulting distinguished triangle
and all four compatibility squares use that single choice of octahedron. -/
theorem cofiber_triangle_of_extension [IsTriangulated C] {X Y Z : C}
    (f : X ⟶ Y) (n : ℤ) (a : Y⟦n⟧ ⟶ Z)
    (g : (HasFunctorialCofiber.cofib f)⟦n⟧ ⟶ Z)
    (hg : (HasFunctorialCofiber.cofibι f)⟦n⟧' ≫ g = a) :
    ∃ m : (X⟦n⟧)⟦(1 : ℤ)⟧ ⟶ HasFunctorialCofiber.cofib a,
    ∃ j : HasFunctorialCofiber.cofib a ⟶ HasFunctorialCofiber.cofib g,
      Triangle.mk j
        (HasFunctorialCofiber.cofibδ g ≫ ((shiftedCofiberTriangle f n).mor₃)⟦(1 : ℤ)⟧')
        (-m⟦(1 : ℤ)⟧') ∈ distTriang C ∧
      (shiftedCofiberTriangle f n).mor₃ ≫ m = g ≫ HasFunctorialCofiber.cofibι a ∧
      m ≫ HasFunctorialCofiber.cofibδ a = -(f⟦n⟧')⟦(1 : ℤ)⟧' ∧
      HasFunctorialCofiber.cofibι a ≫ j = HasFunctorialCofiber.cofibι g ∧
      j ≫ HasFunctorialCofiber.cofibδ g =
        HasFunctorialCofiber.cofibδ a ≫ ((HasFunctorialCofiber.cofibι f)⟦n⟧')⟦(1 : ℤ)⟧' := by
  let V := Triangle.mk (f⟦n⟧') ((HasFunctorialCofiber.cofibι f)⟦n⟧') (shiftedCofiberTriangle f n).mor₃
  have hV : V ∈ distTriang C := shiftedCofiberTriangle_distinguished f n
  let O := CategoryTheory.Triangulated.someOctahedron hg (rot_of_distTriang V hV)
    (HasFunctorialCofiber.cofib_distinguished g) (HasFunctorialCofiber.cofib_distinguished a)
  dsimp only [V, Triangle.mk, Triangle.rotate] at O
  refine ⟨O.m₁, O.m₃, ?_, O.comm₁, O.comm₂, O.comm₃, O.comm₄.symm⟩
  exact rot_of_distTriang _ O.mem

/-- A single extension and a single octahedron give both three-cell
triangles, with the precise six-sphere and fourfold-cofiber shifts. The only
vanishing hypothesis remains explicit, and all four comparison squares are
retained for these same maps. This supplies no native coordinate comparison. -/
theorem exists_eta_nu_cofiber_triangles [IsTriangulated C]
    (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
    (ν : Sphere (C := C) 3 ⟶ SphereSpectrum)
    (hzero : (shiftFunctor C (3 : ℤ)).map η ≫ ν = 0) :
    ∃ g : (HasFunctorialCofiber.cofib η)⟦(3 : ℤ)⟧ ⟶ SphereSpectrum,
    ∃ m : ((Sphere (C := C) 1)⟦(3 : ℤ)⟧)⟦(1 : ℤ)⟧ ⟶
      HasFunctorialCofiber.cofib ν,
    ∃ j : HasFunctorialCofiber.cofib ν ⟶ HasFunctorialCofiber.cofib g,
      (HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧' ≫ g = ν ∧
      Triangle.mk (HasFunctorialCofiber.cofibι g)
        (HasFunctorialCofiber.cofibδ g ≫
          (shiftFourIso (HasFunctorialCofiber.cofib η)).hom)
        ((shiftFourIso (HasFunctorialCofiber.cofib η)).inv ≫ (-g⟦(1 : ℤ)⟧'))
          ∈ distTriang C ∧
      Triangle.mk j
        ((HasFunctorialCofiber.cofibδ g ≫
          ((shiftedCofiberTriangle η 3).mor₃)⟦(1 : ℤ)⟧') ≫
          (sphereSixIso (C := C)).hom)
        ((sphereSixIso (C := C)).inv ≫ (-m⟦(1 : ℤ)⟧')) ∈ distTriang C ∧
      (shiftedCofiberTriangle η 3).mor₃ ≫ m =
        g ≫ HasFunctorialCofiber.cofibι ν ∧
      m ≫ HasFunctorialCofiber.cofibδ ν = -(η⟦(3 : ℤ)⟧')⟦(1 : ℤ)⟧' ∧
      HasFunctorialCofiber.cofibι ν ≫ j = HasFunctorialCofiber.cofibι g ∧
      j ≫ HasFunctorialCofiber.cofibδ g =
        HasFunctorialCofiber.cofibδ ν ≫
          ((HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧')⟦(1 : ℤ)⟧' := by
  obtain ⟨g, hg⟩ := exists_eta_nu_extension η ν hzero
  obtain ⟨m, j, hT, hm₁, hm₂, hj₁, hj₂⟩ :=
    cofiber_triangle_of_extension η 3 ν g hg
  refine ⟨g, m, j, hg, ?_, ?_, hm₁, hm₂, hj₁, hj₂⟩
  · exact replace_third_object _ _ _
      (rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished g))
      (shiftFourIso (HasFunctorialCofiber.cofib η))
  · exact replace_third_object _ _ _ hT (sphereSixIso (C := C))

end KIP126.StableHomotopy.CofiberExtension
