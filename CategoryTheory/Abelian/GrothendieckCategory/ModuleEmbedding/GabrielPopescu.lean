/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# The Gabriel-Popescu theorem

We prove the following Gabriel-Popescu theorem: if `C` is a Grothendieck abelian category and
`G` is a separator, then the functor `preadditiveCoyonedaObj G : C ⥤ ModuleCat (End G)ᵐᵒᵖ` sending
`X` to `Hom(G, X)` is fully faithful and has an exact left adjoint.

We closely follow the elementary proof given by Barry Mitchell.

## Future work

The left adjoint `tensorObj G` actually exists as soon as `C` is cocomplete and additive, so the
construction could be generalized.

The theorem as stated here implies that `C` is a Serre quotient of `ModuleCat (End G)ᵐᵒᵖ`.

## References

* [Barry Mitchell, *A quick proof of the Gabriel-Popesco theorem*][mitchell1981]
-/

@[expose] public section

universe v u

open CategoryTheory Limits Abelian

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

instance {G : C} : (preadditiveCoyonedaObj G).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating.{v} (isCoseparator_coseparator _) _

/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
definition tensorObj
  signature: (G : C)
  body: (preadditiveCoyonedaObj G).leftAdjoint

中文:
定义 tensorObj
  签名: (G : C)
  定义体: (preadditiveCoyonedaObj G).leftAdjoint

Depends on / 依赖: leftAdjoint, preadditiveCoyonedaObj
-/
noncomputable def tensorObj (G : C) : ModuleCat (End G)ᵐᵒᵖ ⥤ C :=
  (preadditiveCoyonedaObj G).leftAdjoint

/--
Definition of `tensorObjPreadditiveCoyonedaObjAdjunction` / `tensorObjPreadditiveCoyonedaObjAdjunction` 的定义

English:
definition tensorObjPreadditiveCoyonedaObjAdjunction
  signature: (G : C)
  body: Adjunction.ofIsRightAdjoint _

中文:
定义 tensorObjPreadditiveCoyonedaObjAdjunction
  签名: (G : C)
  定义体: Adjunction.ofIsRightAdjoint _

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint
-/
noncomputable def tensorObjPreadditiveCoyonedaObjAdjunction (G : C) :
    tensorObj G ⊣ preadditiveCoyonedaObj G :=
  Adjunction.ofIsRightAdjoint _

instance {G : C} : (tensorObj G).IsLeftAdjoint :=
  (tensorObjPreadditiveCoyonedaObjAdjunction G).isLeftAdjoint

namespace GabrielPopescuAux

open CoproductsFromFiniteFiltered

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ}
  body: Sigma.desc fun (m : M) => g m

中文:
定义 d
  签名: {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ}
  定义体: Sigma.desc fun (m : M) => g m

Depends on / 依赖: Sigma.desc
-/
noncomputable def d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) : ∐ (fun (_ : M) => G) ⟶ A :=
  Sigma.desc fun (m : M) => g m

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `ι_d` / 定理 `ι_d`

English:
theorem ι_d
  given: {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (m : M)
  proof: by
  simp [d]

中文:
定理 ι_d
  条件: {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (m : M)
  证明: by
  simp [d]
-/
theorem ι_d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (m : M) :
    Sigma.ι _ m ≫ d g = g.hom m := by
  simp [d]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] IsFiltered.isConnected in
/--
theorem `kernel_ι_d_comp_d` / 定理 `kernel_ι_d_comp_d`

English:
theorem kernel_ι_d_comp_d
  statement: {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G)ᵐᵒᵖ}
  proof: by
  refine (isColimitFiniteSubproductsCocone (fun (_ : M) => G)).pullback_zero_ext (fun F => ?_)
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj]
  classical
  rw [finiteSubcoproductsCocone_ι_app_eq_sum]; rw [← pullback.conditio

中文:
定理 kernel_ι_d_comp_d
  结论: {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G)ᵐᵒᵖ}
  证明: by
  refine (isColimitFiniteSubproductsCocone (fun (_ : M) => G)).pullback_zero_ext (fun F => ?_)
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj]
  classical
  rw [finiteSubcoproductsCocone_ι_app_eq_sum]; rw [← pullback.conditio

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.functor_obj_eq_as, Functor, Functor.const_obj_obj, Preadditive, Preadditive.comp_sum_assoc, Preadditive.isSeparator_iff, Preadditive.sum_comp, classical, comp_sum_assoc, condition_assoc, const_obj_obj, finiteSubcoproductsCocone_pt, functor_obj_eq_as, isColimitFiniteSubproductsCocone, isSeparator_iff, liftToFinsetObj_obj, pullback
-/
theorem kernel_ι_d_comp_d {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g)
    (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) :
    kernel.ι (d g) ≫ d f = 0 := by
  refine (isColimitFiniteSubproductsCocone (fun (_ : M) => G)).pullback_zero_ext (fun F => ?_)
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj]
  classical
  rw [finiteSubcoproductsCocone_ι_app_eq_sum]; rw [← pullback.condition_assoc]
  refine (Preadditive.isSeparator_iff G).1 hG _ (fun h => ?_)
  rw [Preadditive.comp_sum_assoc]; rw [Preadditive.comp_sum_assoc]; rw [Preadditive.sum_comp]
  simp only [Category.assoc, ι_d]
  let r (x : F) : (End G)ᵐᵒᵖ := MulOpposite.op (h ≫ pullback.fst _ _ ≫ Sigma.π _ x)
  suffices ∑ x in F.attach, r x • f.hom x.1.as = 0 by simpa [End.smul_left, r] using this
  simp only [← map_smul, ← map_sum]
  suffices ∑ x in F.attach, r x • x.1.as = 0 by simp [this]
  simp only [← g.hom.map_eq_zero_iff ((ModuleCat.mono_iff_injective _).1 hg), map_sum, map_smul]
  simp only [← ι_d g, End.smul_left, MulOpposite.unop_op, Category.assoc, r]
  simp [← Preadditive.comp_sum, ← Preadditive.sum_comp', pullback.condition_assoc]

/--
theorem `exists_d_comp_eq_d` / 定理 `exists_d_comp_eq_d`

English:
theorem exists_d_comp_eq_d
  statement: {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B]
  proof: by
  let l₁ : image (d g) ⟶ B := epiDesc (factorThruImage (d g)) (d f) (by
    rw [← kernelFactorThruImage_hom_comp_ι]; rw [Category.assoc]; rw [kernel_ι_d_comp_d hG _ hg]; rw [comp_zero])
  let l₂ : A ⟶ B := Injective.factorThru l₁ (Limits.image.ι (d g))
  refine ⟨l₂, ?_⟩
  simp only [l₂, l₁]
  con

中文:
定理 exists_d_comp_eq_d
  结论: {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B]
  证明: by
  let l₁ : image (d g) ⟶ B := epiDesc (factorThruImage (d g)) (d f) (by
    rw [← kernelFactorThruImage_hom_comp_ι]; rw [Category.assoc]; rw [kernel_ι_d_comp_d hG _ hg]; rw [comp_zero])
  let l₂ : A ⟶ B := Injective.factorThru l₁ (Limits.image.ι (d g))
  refine ⟨l₂, ?_⟩
  simp only [l₂, l₁]
  con

Depends on / 依赖: Category, Category.assoc, Injective, Injective.factorThru, Limits, Limits.image, Limits.image.fac, comp_zero, conv_lhs, epiDesc, factorThru, factorThruImage
-/
theorem exists_d_comp_eq_d {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B]
    {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g)
    (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) : exists (l : A ⟶ B), d g ≫ l = d f := by
  let l₁ : image (d g) ⟶ B := epiDesc (factorThruImage (d g)) (d f) (by
    rw [← kernelFactorThruImage_hom_comp_ι]; rw [Category.assoc]; rw [kernel_ι_d_comp_d hG _ hg]; rw [comp_zero])
  let l₂ : A ⟶ B := Injective.factorThru l₁ (Limits.image.ι (d g))
  refine ⟨l₂, ?_⟩
  simp only [l₂, l₁]
  conv_lhs => congr; rw [← Limits.image.fac (d g)]
  simp [-Limits.image.fac]

end GabrielPopescuAux

open GabrielPopescuAux

set_option backward.isDefEq.respectTransparency false in
/--
theorem `GabrielPopescu.full` / 定理 `GabrielPopescu.full`

English:
theorem GabrielPopescu.full
  given: (G : C) (hG : IsSeparator G)
  statement: (preadditiveCoyonedaObj G).Full where
  proof: by
    have := (isSeparator_iff_epi G).1 hG A
    have h := kernel_ι_d_comp_d hG (𝟙 _) inferInstance f
    simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq, d] at h
    refine ⟨epiDesc _ _ h, ?_⟩
    ext q
    simpa [-comp_epiDesc] using! Sigma.ι _ q ≫= comp_epiDesc _ _ h

中文:
定理 GabrielPopescu.full
  条件: (G : C) (hG : IsSeparator G)
  结论: (preadditiveCoyonedaObj G).Full where
  证明: by
    have := (isSeparator_iff_epi G).1 hG A
    have h := kernel_ι_d_comp_d hG (𝟙 _) inferInstance f
    simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq, d] at h
    refine ⟨epiDesc _ _ h, ?_⟩
    ext q
    simpa [-comp_epiDesc] using! Sigma.ι _ q ≫= comp_epiDesc _ _ h

Depends on / 依赖: LinearMap, LinearMap.id_coe, ModuleCat, ModuleCat.hom_id, comp_epiDesc, epiDesc, hom_id, id_coe, id_eq, isSeparator_iff_epi
-/
theorem GabrielPopescu.full (G : C) (hG : IsSeparator G) : (preadditiveCoyonedaObj G).Full where
  map_surjective {A B} f := by
    have := (isSeparator_iff_epi G).1 hG A
    have h := kernel_ι_d_comp_d hG (𝟙 _) inferInstance f
    simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq, d] at h
    refine ⟨epiDesc _ _ h, ?_⟩
    ext q
    simpa [-comp_epiDesc] using! Sigma.ι _ q ≫= comp_epiDesc _ _ h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `GabrielPopescu.preservesInjectiveObjects` / 定理 `GabrielPopescu.preservesInjectiveObjects`

English:
theorem GabrielPopescu.preservesInjectiveObjects
  given: (G : C) (hG : IsSeparator G)
  proof: by
    rw [← Module.injective_iff_injective_object]
    simp only [preadditiveCoyonedaObj_obj_carrier]
    refine Module.Baer.injective (fun M g => ?_)
    have h := exists_d_comp_eq_d hG B (ModuleCat.ofHom
      ⟨⟨fun i => i.1.unop, by cat_disch⟩, by cat_disch⟩) ?_ (ModuleCat.ofHom g)
    · obtain 

中文:
定理 GabrielPopescu.preservesInjectiveObjects
  条件: (G : C) (hG : IsSeparator G)
  证明: by
    rw [← Module.injective_iff_injective_object]
    simp only [preadditiveCoyonedaObj_obj_carrier]
    refine Module.Baer.injective (fun M g => ?_)
    have h := exists_d_comp_eq_d hG B (ModuleCat.ofHom
      ⟨⟨fun i => i.1.unop, by cat_disch⟩, by cat_disch⟩) ?_ (ModuleCat.ofHom g)
    · obtain 

Depends on / 依赖: Module, Module.Baer.injective, Module.injective_iff_injective_object, ModuleCat, ModuleCat.mono_iff_injective, ModuleCat.ofHom, Preadditive, Preadditive.homSelfLinearEquivEndMulOpposite, cat_, cat_disch, exists_d_comp_eq_d, homSelfLinearEquivEndMulOpposite, injective, injective_iff_injective_object, mono_iff_injective, preadditiveCoyonedaObj, preadditiveCoyonedaObj_obj_carrier, symm.toLinearMap, toLinearMap
-/
theorem GabrielPopescu.preservesInjectiveObjects (G : C) (hG : IsSeparator G) :
    (preadditiveCoyonedaObj G).PreservesInjectiveObjects where
  injective_obj {B} hB := by
    rw [← Module.injective_iff_injective_object]
    simp only [preadditiveCoyonedaObj_obj_carrier]
    refine Module.Baer.injective (fun M g => ?_)
    have h := exists_d_comp_eq_d hG B (ModuleCat.ofHom
      ⟨⟨fun i => i.1.unop, by cat_disch⟩, by cat_disch⟩) ?_ (ModuleCat.ofHom g)
    · obtain ⟨l, hl⟩ := h
      refine ⟨((preadditiveCoyonedaObj G).map l).hom ∘ₗ
        (Preadditive.homSelfLinearEquivEndMulOpposite G).symm.toLinearMap, ?_⟩
      intro f hf
      simpa [d] using! Sigma.ι _ ⟨f, hf⟩ ≫= hl
    · rw [ModuleCat.mono_iff_injective]
      cat_disch

/--
theorem `GabrielPopescu.preservesFiniteLimits` / 定理 `GabrielPopescu.preservesFiniteLimits`

English:
theorem GabrielPopescu.preservesFiniteLimits
  given: (G : C) (hG : IsSeparator G)
  proof: by
  have := preservesInjectiveObjects G hG
  have : (tensorObj G).PreservesMonomorphisms :=
    (tensorObj G).preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (tensorObjPreadditiveCoyonedaObjAdjunction G)
  have : PreservesBinaryBiproducts (tensorObj G) :=
    preservesBinary

中文:
定理 GabrielPopescu.preservesFiniteLimits
  条件: (G : C) (hG : IsSeparator G)
  证明: by
  have := preservesInjectiveObjects G hG
  have : (tensorObj G).PreservesMonomorphisms :=
    (tensorObj G).preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (tensorObjPreadditiveCoyonedaObjAdjunction G)
  have : PreservesBinaryBiproducts (tensorObj G) :=
    preservesBinary

Depends on / 依赖: Additive, Functor, Functor.additive_of_preservesBinaryBiproducts, PreservesBinaryBiproducts, PreservesHomology, PreservesMonomorphisms, additive_of_preservesBinaryBiproducts, preservesBinaryBiproducts_of_preservesBinaryCoproducts, preservesHomology_of_preservesMonos_and_c, preservesInjectiveObjects, preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects, tensorObj, tensorObjPreadditiveCoyonedaObjAdjunction
-/
theorem GabrielPopescu.preservesFiniteLimits (G : C) (hG : IsSeparator G) :
    PreservesFiniteLimits (tensorObj G) := by
  have := preservesInjectiveObjects G hG
  have : (tensorObj G).PreservesMonomorphisms :=
    (tensorObj G).preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (tensorObjPreadditiveCoyonedaObjAdjunction G)
  have : PreservesBinaryBiproducts (tensorObj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorObj G).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : (tensorObj G).PreservesHomology :=
    (tensorObj G).preservesHomology_of_preservesMonos_and_cokernels
  exact (tensorObj G).preservesFiniteLimits_of_preservesHomology

end CategoryTheory.IsGrothendieckAbelian
