/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

section

variable {M N P : ModuleCat.{v} R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
/-
**ModuleCat.kernelCone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：kernelCone : KernelFork f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel cone induced by the concrete kernel.
-/
def kernelCone : KernelFork f :=
  KernelFork.ofι (ofHom (LinearMap.ker f.hom).subtype) <| by aesop

/-- The kernel of a linear map is a kernel in the categorical sense. -/
/-
**ModuleCat.kernelIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：kernelIsLimit : IsLimit (kernelCone f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a linear map is a kernel in the categorical sense.
-/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s => ofHom <|
      LinearMap.codRestrict f.hom.ker (Fork.ι s).hom fun c =>
        LinearMap.mem_ker.2 <| by simp [← ConcreteCategory.comp_apply])
    (fun _ => hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
      hom_ext <| LinearMap.ext fun x => Subtype.ext_iff.2 (by simp [← h]; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construct an `IsLimit` structure of kernels given `Function.Exact`. -/
noncomputable
/-
**ModuleCat.isLimitKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：isLimitKernelFork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
 (H₂ : Function.Injective f.hom) : IsLimit (KernelFork.ofι (f
参数：f : M ⟶ N；g : N ⟶ P；H : Function.Exact f.hom g.hom；H₂ : Function.Injective f.
hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isLimitKernelFork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
    (H₂ : Function.Injective f.hom) :
    IsLimit (KernelFork.ofι (f := g) f (by ext; exact H.apply_apply_eq_zero _)) := by
  refine IsLimit.ofIsoLimit (kernelIsLimit g) <|
    Cone.ext ((LinearEquiv.ofInjective _ H₂).trans
        (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp H).symm)).toModuleIso.symm ?_
  · rintro ⟨⟩ <;> ext x <;> simp [kernelCone]

/-- The cokernel cocone induced by the projection onto the quotient. -/
/-
**ModuleCat.cokernelCocone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：cokernelCocone : CokernelCofork f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel cocone induced by the projection onto the quotient.
-/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (ofHom (LinearMap.range f.hom).mkQ) <| hom_ext <| LinearMap.range_mkQ_comp _

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
/-
**ModuleCat.cokernelIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：cokernelIsColimit : IsColimit (cokernelCocone f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection onto the quotient is a cokernel in the categorical sense.
-/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s => ofHom <| (LinearMap.range f.hom).liftQ (Cofork.π s).hom <|
      LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.mp <| CokernelCofork.condition s)
    (fun s => hom_ext <| (LinearMap.range f.hom).liftQ_mkQ (Cofork.π s).hom _) fun s m h => by
    have : Epi (ofHom f.hom.range.mkQ) :=
      (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    apply (cancel_epi (ofHom f.hom.range.mkQ)).1
    exact h

/-- Construct an `IsColimit` structure of cokernels given `Function.Exact`. -/
noncomputable
/-
**ModuleCat.isColimitCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：isColimitCokernelCofork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom 
g.hom) (H₂ : Function.Surjective g.hom) : IsColimit (CokernelCofork.ofπ (f
参数：f : M ⟶ N；g : N ⟶ P；H : Function.Exact f.hom g.hom；H₂ : Function.Surjective g
.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isColimitCokernelCofork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
    (H₂ : Function.Surjective g.hom) :
    IsColimit (CokernelCofork.ofπ (f := f) g (by ext; exact H.apply_apply_eq_zero _)) := by
  refine IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit f) <|
    Cocone.ext (((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp H)).toModuleIso).symm
    ≪≫ ((LinearMap.quotKerEquivOfSurjective _ H₂).toModuleIso)) ?_
  · rintro ⟨⟩ <;> ext x
    · simpa using! (Function.Exact.apply_apply_eq_zero H x).symm
    · rfl

end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
/-
**ModuleCat.hasKernels_moduleCat** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hasKernels_moduleCat : HasKernels (ModuleCat R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
The category of R-modules has kernels, given by the inclusion of the kernel subm
odule.
-/
theorem hasKernels_moduleCat : HasKernels (ModuleCat R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- The category of R-modules has cokernels, given by the projection onto the quotient. -/
/-
**ModuleCat.hasCokernels_moduleCat** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hasCokernels_moduleCat : HasCokernels (ModuleCat R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
The category of R-modules has cokernels, given by the projection onto the quotie
nt.
-/
theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

open ModuleCat

attribute [local instance] hasKernels_moduleCat

attribute [local instance] hasCokernels_moduleCat

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

/-- The categorical kernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical kernel.
-/
/-
**ModuleCat.kernelIsoKer** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) : kernel f ≅ ModuleCat.of
 R f.hom.ker
参数：f : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical kernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical kernel.
-/
noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    kernel f ≅ ModuleCat.of R f.hom.ker :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
/-
**ModuleCat.kernelIsoKer_inv_kernel_** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f = ofHom f.hom.ker.subtype :=
  limit.isoLimitCone_inv_π _ _

@[simp, elementwise]
/-
**ModuleCat.kernelIsoKer_hom_ker_subtype** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：kernelIsoKer_hom_ker_subtype : (kernelIsoKer f).hom ≫ ofHom f.hom.ker.subt
ype = kernel.ι f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem kernelIsoKer_hom_ker_subtype :
    (kernelIsoKer f).hom ≫ ofHom f.hom.ker.subtype = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

/-- The categorical cokernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical quotient.
-/
/-
**ModuleCat.cokernelIsoRangeQuotient** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) : cokernel f 
≅ ModuleCat.of R (H ⧸ f.hom.range)
参数：f : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical cokernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    cokernel f ≅ ModuleCat.of R (H ⧸ f.hom.range) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
/-
**ModuleCat.cokernel_** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = ofHom (LinearMap.range f.hom).mkQ :=
  colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]
/-
**ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv** 是 Mathlib 中的一个定理，位于命名空间 `Mo
duleCat`。
形式化陈述：range_mkQ_cokernelIsoRangeQuotient_inv : ofHom (LinearMap.range f.hom).mkQ
 ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `ModuleCat.hasCokernels_moduleCat`：hasCokernels_moduleCat : HasCokernels 
(ModuleCat R)
-/
theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ofHom (LinearMap.range f.hom).mkQ ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one
/-
**ModuleCat.cokernel_** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simpa only [map_add, add_eq_left] using! cokernel.condition_apply f m

end ModuleCat

