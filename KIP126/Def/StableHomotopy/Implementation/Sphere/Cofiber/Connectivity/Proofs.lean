module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Connectivity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Connectivity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Triangle.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Locality.BoundedBelow.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

private theorem shift_homotopy_subsingleton (X : SourceCategory.{0}) (d : ℤ)
    (hX : Subsingleton ((sourceStableHomotopyAddFunctor (d - 1)).obj X)) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (X⟦(1 : ℤ)⟧)) := by
  letI := hX
  letI : Subsingleton (Prespectrum.sourceSphere d ⟶
      sourceLocalization.obj (X⟦(1 : ℤ)⟧).as.obj) := by
    change Subsingleton (Prespectrum.sourceSphere d ⟶ X⟦(1 : ℤ)⟧)
    exact sourceSphere_hom_shift_subsingleton X d
  exact (Prespectrum.sourceStableHomotopyEquiv (X⟦(1 : ℤ)⟧).as.obj d).injective.subsingleton

private theorem triangle_second_surjective (T : Triangle SourceCategory.{0})
    (hT : T ∈ distTriang SourceCategory) (d : ℤ)
    (hX : Subsingleton ((sourceStableHomotopyAddFunctor (d - 1)).obj T.obj₁)) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map T.mor₂) := by
  let F := sourceStableHomotopyAddFunctor d
  letI := shift_homotopy_subsingleton T.obj₁ d hX
  have hz₃ : F.map T.mor₃ = 0 :=
    (AddCommGrpCat.isZero_of_subsingleton (F.obj (T.obj₁⟦(1 : ℤ)⟧))).eq_of_tgt _ _
  haveI : Epi (F.map T.mor₂) :=
    (F.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).epi_f hz₃
  exact (AddCommGrpCat.epi_iff_surjective (F.map T.mor₂)).mp inferInstance

private theorem triangle_second_bijective (T : Triangle SourceCategory.{0})
    (hT : T ∈ distTriang SourceCategory) (d : ℤ)
    (hX : Subsingleton ((sourceStableHomotopyAddFunctor d).obj T.obj₁))
    (hX' : Subsingleton ((sourceStableHomotopyAddFunctor (d - 1)).obj T.obj₁)) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map T.mor₂) := by
  let F := sourceStableHomotopyAddFunctor d
  letI := hX
  have hz₁ : F.map T.mor₁ = 0 :=
    (AddCommGrpCat.isZero_of_subsingleton (F.obj T.obj₁)).eq_of_src _ _
  haveI : Mono (F.map T.mor₂) := (F.map_distinguished_exact T hT).mono_g hz₁
  exact ⟨(AddCommGrpCat.mono_iff_injective (F.map T.mor₂)).mp inferInstance,
    triangle_second_surjective T hT d hX'⟩

/-- The chosen cofiber of any actual map between the specified source spheres
has the expected lower bound. In particular every map S³ → S⁰ has a connective
cofiber; no identification of that map with the classical ν is asserted. -/
theorem sourceSphereCofiber_homotopy_subsingleton {m n : ℤ}
    (f : Prespectrum.sourceSphere m ⟶ Prespectrum.sourceSphere n) (d : ℤ)
    (hd : d < min n (m + 1)) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (HasFunctorialCofiber.cofib f)) := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang SourceCategory := HasFunctorialCofiber.cofib_distinguished f
  have hsurj := triangle_second_surjective T hT d
    (Prespectrum.sourceSphere_homotopy_subsingleton m (d - 1) (by omega))
  letI : Subsingleton ((sourceStableHomotopyAddFunctor d).obj T.obj₂) :=
    Prespectrum.sourceSphere_homotopy_subsingleton n d (by omega)
  exact hsurj.subsingleton

/-- Below the attaching sphere's degree, the original cofiber inclusion is
bijective on the unchanged stable homotopy groups. For S³ → S⁰ this includes
all degrees at most two, without a sphere degree computation. -/
theorem sourceSphereCofiber_inclusion_bijective {m n : ℤ}
    (f : Prespectrum.sourceSphere m ⟶ Prespectrum.sourceSphere n) (d : ℤ) (hd : d < m) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map
      (HasFunctorialCofiber.cofibι f)) := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  exact triangle_second_bijective T (HasFunctorialCofiber.cofib_distinguished f) d
    (Prespectrum.sourceSphere_homotopy_subsingleton m d hd)
    (Prespectrum.sourceSphere_homotopy_subsingleton m (d - 1) (by omega))

/-- The original inclusion remains surjective in the attaching degree. -/
theorem sourceSphereCofiber_inclusion_surjective {m n : ℤ}
    (f : Prespectrum.sourceSphere m ⟶ Prespectrum.sourceSphere n) (d : ℤ) (hd : d ≤ m) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map
      (HasFunctorialCofiber.cofibι f)) := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  exact triangle_second_surjective T (HasFunctorialCofiber.cofib_distinguished f) d
    (Prespectrum.sourceSphere_homotopy_subsingleton m (d - 1) (by omega))

/-- The actual Moore limit of this same cofiber retains its exact lower
bound, for every scalar. This applies to the actual Cν once its attaching map
has been constructed and identified. -/
theorem sourceMooreCompletion_sphereCofiber_homotopy_subsingleton (p : ℕ) {m n : ℤ}
    (f : Prespectrum.sourceSphere m ⟶ Prespectrum.sourceSphere n) (d : ℤ)
    (hd : d < min n (m + 1)) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (sourceMooreCompletion p (HasFunctorialCofiber.cofib f))) :=
  sourceMooreCompletion_boundedBelow p _ (min n (m + 1))
    (sourceSphereCofiber_homotopy_subsingleton f) d hd

/-- Applying the original Moore functor to the original cofiber inclusion
preserves its low-degree bijections. The target is the Moore completion of
the actual cofiber, with the actual functorial map, rather than a replacement
cofiber chosen only to have the desired homotopy groups. -/
theorem sourceMooreCompletion_sphereCofiber_inclusion_bijective (p : ℕ) {m n : ℤ}
    (f : Prespectrum.sourceSphere m ⟶ Prespectrum.sourceSphere n) (d : ℤ) (hd : d < m) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map
      (sourceMooreCompletionMap p (HasFunctorialCofiber.cofibι f))) := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang SourceCategory := HasFunctorialCofiber.cofib_distinguished f
  let S := (sourceMooreCompletionFunctor p).mapTriangle.obj T
  have hS : S ∈ distTriang SourceCategory := sourceMooreCompletionFunctor_map_distinguished p T hT
  exact triangle_second_bijective S hS d
    (sourceMooreCompletion_boundedBelow p _ m
      (Prespectrum.sourceSphere_homotopy_subsingleton m) d hd)
    (sourceMooreCompletion_boundedBelow p _ m
      (Prespectrum.sourceSphere_homotopy_subsingleton m) (d - 1) (by omega))

/-- Conditional only on the specified Moore-heart comparison, the original
dyadic Moore completion of any source sphere attachment is HF2-local. This
neither identifies the attaching map as ν nor constructs or recognizes tmf. -/
theorem sourceMooreCompletion_sphereCofiber_isHF2Local
    [IsIso sourceModTwoMooreHeartToHF2] {m n : ℤ}
    (f : Prespectrum.sourceSphere m ⟶ Prespectrum.sourceSphere n) :
    SourceIsHF2Local (sourceMooreCompletion 2 (HasFunctorialCofiber.cofib f)) :=
  sourceMooreCompletion_isHF2Local_of_boundedBelow _ (min n (m + 1))
    (sourceSphereCofiber_homotopy_subsingleton f)

end KIP126.StableHomotopy.Implementation
