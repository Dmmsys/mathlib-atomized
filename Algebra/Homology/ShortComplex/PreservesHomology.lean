/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Functors which preserves homology

If `F : C ⥤ D` is a functor between categories with zero morphisms, we shall
say that `F` preserves homology when `F` preserves both kernels and cokernels.
This typeclass is named `[F.PreservesHomology]`, and is automatically
satisfied when `F` preserves both finite limits and finite colimits.

If `S : ShortComplex C` and `[F.PreservesHomology]`, then there is an
isomorphism `S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology`, which
is part of the natural isomorphism `homologyFunctorIso F` between the functors
`F.mapShortComplex ⋙ homologyFunctor D` and `homologyFunctor C ⋙ F`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

variable (F : C ⥤ D)

/-- A functor preserves homology when it preserves both kernels and cokernels. -/
/-
**CategoryTheory.Functor.PreservesHomology** 是 Mathlib 中的一个类，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：PreservesHomology (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where /-- 
the functor preserves kernels -/ preservesKernels ⦃X Y : C⦄ (f : X ⟶ Y) : Preser
vesLimit (parallelPair f 0) F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves homology when it preserves both kernels and cokernels.
-/
class PreservesHomology (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  /-- the functor preserves kernels -/
  preservesKernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F := by
    infer_instance
  /-- the functor preserves cokernels -/
  preservesCokernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) F := by
    infer_instance

variable [PreservesZeroMorphisms F]

/-- A functor which preserves homology preserves kernels. -/
/-
**CategoryTheory.Functor.PreservesHomology.preservesKernel** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.PreservesHomology`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] [F.Preser
vesHomology] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Limits.PreservesLimit (Cate
goryTheory.Limits.parallelPair f 0) F
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.parallelPair f
 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesKernels`：∀ {C : Type u
_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
A functor which preserves homology preserves kernels.
-/
lemma PreservesHomology.preservesKernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) F :=
  PreservesHomology.preservesKernels _

/-- A functor which preserves homology preserves cokernels. -/
/-
**CategoryTheory.Functor.PreservesHomology.preservesCokernel** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.PreservesHomology`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] [F.Preser
vesHomology] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Limits.PreservesColimit (Ca
tegoryTheory.Limits.parallelPair f 0) F
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.parallelPair f
 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesCokernels`：∀ {C : Type
 u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : C
ategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
A functor which preserves homology preserves cokernels.
-/
lemma PreservesHomology.preservesCokernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F :=
  PreservesHomology.preservesCokernels _
/-
**CategoryTheory.Functor.preservesHomologyOfExact** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] [Category
Theory.Limits.PreservesFiniteLimits F]   [CategoryTheory.Limits.PreservesFiniteC
olimits F], F.PreservesHomology
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable instance preservesHomologyOfExact
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : F.PreservesHomology where

end Functor

namespace ShortComplex

variable {S S₁ S₂ : ShortComplex C}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) (F : C ⥤ D)

/-- A left homology data `h` of a short complex `S` is preserved by a functor `F` is
`F` preserves the kernel of `S.g : S.X₂ ⟶ S.X₃` and the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy** 是 Mathlib 中的一个归纳类
型，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S : CategoryTheory.ShortComplex
 C} →               S.LeftHomologyData → (F : CategoryTheory.Functor C D) → [F.P
reservesZeroMorphisms] → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left homology data `h` of a short complex `S` is preserved by a functor `F` is
`F` preserves the kernel of `S.g : S.X₂ ⟶ S.X₃` and the cokernel of `h.f' : S.X₁
 ⟶ h.K`.
-/
class IsPreservedBy [F.PreservesZeroMorphisms] : Prop where
  /-- the functor preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
  g : PreservesLimit (parallelPair S.g 0) F
  /-- the functor preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
  f' : PreservesColimit (parallelPair h.f' 0) F

variable [F.PreservesZeroMorphisms]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preservesHomolog
y** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：isPreservedBy_of_preservesHomology [F.PreservesHomology] : h.IsPreservedBy
 F where g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesKernel`：∀ {C : Type u_
1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesCokernel`：∀ {C : Type 
u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
noncomputable instance isPreservedBy_of_preservesHomology [F.PreservesHomology] :
    h.IsPreservedBy F where
  g := Functor.PreservesHomology.preservesKernel _ _
  f' := Functor.PreservesHomology.preservesCokernel _ _

variable [h.IsPreservedBy F]

include h in
/-- When a left homology data is preserved by a functor `F`, this functor
preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.hg** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h : S.LeftHomologyData)   (F : CategoryTheo
ry.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [h.IsPreservedBy F],   Categ
oryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair S.g 0) F
参数：h : S.LeftHomologyData；F : CategoryTheory.Functor C D；CategoryTheory.Limits.p
arallelPair S.g 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.g`：∀ {C : Typ
e u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : 
CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
When a left homology data is preserved by a functor `F`, this functor
preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`.
-/
lemma IsPreservedBy.hg : PreservesLimit (parallelPair S.g 0) F :=
  @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

/-- When a left homology data `h` is preserved by a functor `F`, this functor
preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.hf'** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h : S.LeftHomologyData)   (F : CategoryTheo
ry.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [h.IsPreservedBy F],   Categ
oryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair h.f' 0) F
参数：h : S.LeftHomologyData；F : CategoryTheory.Functor C D；CategoryTheory.Limits.p
arallelPair h.f' 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.f'`：∀ {C : Ty
pe u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 :
 CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
When a left homology data `h` is preserved by a functor `F`, this functor
preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`.
-/
lemma IsPreservedBy.hf' : PreservesColimit (parallelPair h.f' 0) F := IsPreservedBy.f'

set_option backward.isDefEq.respectTransparency false in
/-- When a left homology data `h` of a short complex `S` is preserved by a functor `F`,
this is the induced left homology data `h.map F` for the short complex `S.map F`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.map** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：map : (S.map F).LeftHomologyData
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.hg`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.hf'`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_π`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
When a left homology data `h` of a short complex `S` is preserved by a functor `
F`,
this is the induced left homology data `h.map F` for the short complex `S.map F`
.
-/
noncomputable def map : (S.map F).LeftHomologyData := by
  have := IsPreservedBy.hg h F
  have := IsPreservedBy.hf' h F
  have wi : F.map h.i ≫ F.map S.g = 0 := by rw [← F.map_comp, h.wi, F.map_zero]
  have hi := KernelFork.mapIsLimit _ h.hi F
  let f' : F.obj S.X₁ ⟶ F.obj h.K := hi.lift (KernelFork.ofι (S.map F).f (S.map F).zero)
  have hf' : f' = F.map h.f' := Fork.IsLimit.hom_ext hi (by
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, map_f, ← F.map_comp, f'_i])
  have wπ : f' ≫ F.map h.π = 0 := by rw [hf', ← F.map_comp, f'_π, F.map_zero]
  have hπ : IsColimit (CokernelCofork.ofπ (F.map h.π) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair (F.map h.f') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf') (by simp)
    refine IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ h.hπ' F) ?_)
    exact Cofork.ext (Iso.refl _) (by simp [e])
  exact
    { K := F.obj h.K
      H := F.obj h.H
      i := F.map h.i
      π := F.map h.π
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.map_f'** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：map_f' : (h.map F).f' = F.map h.f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.map_f`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.map_i`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma map_f' : (h.map F).f' = F.map h.f' := by
  rw [← cancel_mono (h.map F).i, f'_i, map_f, map_i, ← F.map_comp, f'_i]

end LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- Given a left homology map data `ψ : LeftHomologyMapData φ h₁ h₂` such that
both left homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced left homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.map** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S₁ S₂ : CategoryTheory.ShortCom
plex C} →               {φ : S₁ ⟶ S₂} →                 {h₁ : S₁.LeftHomologyDat
a} →                   {h₂ : S₂.LeftHomologyData} →                     Category
Theory.ShortComplex.LeftHomologyMapData φ h₁ h₂ →                       (F : Cat
egoryTheory.Functor C D) →                         [inst_4 : F.PreservesZeroMorp
hisms] →                           [inst_5 : h₁.IsPreservedBy F] →              
               [inst_6 : h₂.IsPreservedBy F] →                               Cat
egoryTheory.ShortComplex.LeftHomologyMapData (F.mapShortComplex.map φ) (h₁.map F
)                                 (h₂.map F)
参数：F : CategoryTheory.Functor C D；F.mapShortComplex.map φ；h₁.map F；h₂.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a left homology map data `ψ : LeftHomologyMapData φ h₁ h₂` such that
both left homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced left homology map data for the morphism `F.mapShortComplex.map φ`.
-/
noncomputable def LeftHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (ψ : LeftHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    LeftHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φK := F.map ψ.φK
  φH := F.map ψ.φH
  commi := by simpa only [F.map_comp] using! F.congr_map ψ.commi
  commf' := by simpa only [LeftHomologyData.map_f', F.map_comp] using! F.congr_map ψ.commf'
  commπ := by simpa only [F.map_comp] using! F.congr_map ψ.commπ

namespace RightHomologyData

variable (h : S.RightHomologyData) (F : C ⥤ D)

/-- A right homology data `h` of a short complex `S` is preserved by a functor `F` is
`F` preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂` and the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy** 是 Mathlib 中的一个归纳
类型，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S : CategoryTheory.ShortComplex
 C} →               S.RightHomologyData → (F : CategoryTheory.Functor C D) → [F.
PreservesZeroMorphisms] → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right homology data `h` of a short complex `S` is preserved by a functor `F` i
s
`F` preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂` and the kernel of `h.g' : h.Q 
⟶ S.X₃`.
-/
class IsPreservedBy [F.PreservesZeroMorphisms] : Prop where
  /-- the functor preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
  f : PreservesColimit (parallelPair S.f 0) F
  /-- the functor preserves the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
  g' : PreservesLimit (parallelPair h.g' 0) F

variable [F.PreservesZeroMorphisms]
/-
**CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preservesHomolo
gy** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：isPreservedBy_of_preservesHomology [F.PreservesHomology] : h.IsPreservedBy
 F where f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesCokernel`：∀ {C : Type 
u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesKernel`：∀ {C : Type u_
1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
noncomputable instance isPreservedBy_of_preservesHomology [F.PreservesHomology] :
    h.IsPreservedBy F where
  f := Functor.PreservesHomology.preservesCokernel F _
  g' := Functor.PreservesHomology.preservesKernel F _

variable [h.IsPreservedBy F]

include h in
/-- When a right homology data is preserved by a functor `F`, this functor
preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
/-
**CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.hf** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h : S.RightHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [h.IsPreservedBy F],   Cate
goryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair S.f 0) F
参数：h : S.RightHomologyData；F : CategoryTheory.Functor C D；CategoryTheory.Limits.
parallelPair S.f 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.f`：∀ {C : Ty
pe u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 :
 CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
When a right homology data is preserved by a functor `F`, this functor
preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂`.
-/
lemma IsPreservedBy.hf : PreservesColimit (parallelPair S.f 0) F :=
  @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

/-- When a right homology data `h` is preserved by a functor `F`, this functor
preserves the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.hg'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h : S.RightHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [h.IsPreservedBy F],   Cate
goryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair h.g' 0) F
参数：h : S.RightHomologyData；F : CategoryTheory.Functor C D；CategoryTheory.Limits.
parallelPair h.g' 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.g'`：∀ {C : T
ype u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 
: CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
When a right homology data `h` is preserved by a functor `F`, this functor
preserves the kernel of `h.g' : h.Q ⟶ S.X₃`.
-/
lemma IsPreservedBy.hg' : PreservesLimit (parallelPair h.g' 0) F :=
  @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

set_option backward.isDefEq.respectTransparency false in
/-- When a right homology data `h` of a short complex `S` is preserved by a functor `F`,
this is the induced right homology data `h.map F` for the short complex `S.map F`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.RightHomologyData.map** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：map : (S.map F).RightHomologyData
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.hf`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.hg'`：∀ {C : 
Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.wp`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.ι_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
When a right homology data `h` of a short complex `S` is preserved by a functor 
`F`,
this is the induced right homology data `h.map F` for the short complex `S.map F
`.
-/
noncomputable def map : (S.map F).RightHomologyData := by
  have := IsPreservedBy.hf h F
  have := IsPreservedBy.hg' h F
  have wp : F.map S.f ≫ F.map h.p = 0 := by rw [← F.map_comp, h.wp, F.map_zero]
  have hp := CokernelCofork.mapIsColimit _ h.hp F
  let g' : F.obj h.Q ⟶ F.obj S.X₃ := hp.desc (CokernelCofork.ofπ (S.map F).g (S.map F).zero)
  have hg' : g' = F.map h.g' := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc hp]
    simp only [Cofork.π_ofπ, CokernelCofork.map_π, map_g, ← F.map_comp, p_g']
  have wι : F.map h.ι ≫ g' = 0 := by rw [hg', ← F.map_comp, ι_g', F.map_zero]
  have hι : IsLimit (KernelFork.ofι (F.map h.ι) wι) := by
    let e : parallelPair g' 0 ≅ parallelPair (F.map h.g') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hg') (by simp)
    refine IsLimit.postcomposeHomEquiv e _
      (IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ h.hι' F) ?_)
    exact Fork.ext (Iso.refl _) (by simp [e])
  exact
    { Q := F.obj h.Q
      H := F.obj h.H
      p := F.map h.p
      ι := F.map h.ι
      wp := wp
      hp := hp
      wι := wι
      hι := hι }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.RightHomologyData.map_g'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：map_g' : (h.map F).g' = F.map h.g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instEpiP`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.map_g`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.map_p`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma map_g' : (h.map F).g' = F.map h.g' := by
  rw [← cancel_epi (h.map F).p, p_g', map_g, map_p, ← F.map_comp, p_g']

end RightHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- Given a right homology map data `ψ : RightHomologyMapData φ h₁ h₂` such that
both right homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced right homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.map** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S₁ S₂ : CategoryTheory.ShortCom
plex C} →               {φ : S₁ ⟶ S₂} →                 {h₁ : S₁.RightHomologyDa
ta} →                   {h₂ : S₂.RightHomologyData} →                     Catego
ryTheory.ShortComplex.RightHomologyMapData φ h₁ h₂ →                       (F : 
CategoryTheory.Functor C D) →                         [inst_4 : F.PreservesZeroM
orphisms] →                           [inst_5 : h₁.IsPreservedBy F] →           
                  [inst_6 : h₂.IsPreservedBy F] →                               
CategoryTheory.ShortComplex.RightHomologyMapData (F.mapShortComplex.map φ) (h₁.m
ap F)                                 (h₂.map F)
参数：F : CategoryTheory.Functor C D；F.mapShortComplex.map φ；h₁.map F；h₂.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right homology map data `ψ : RightHomologyMapData φ h₁ h₂` such that
both right homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced right homology map data for the morphism `F.mapShortComplex.map φ`.
-/
noncomputable def RightHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (ψ : RightHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    RightHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φQ := F.map ψ.φQ
  φH := F.map ψ.φH
  commp := by simpa only [F.map_comp] using! F.congr_map ψ.commp
  commg' := by simpa only [RightHomologyData.map_g', F.map_comp] using! F.congr_map ψ.commg'
  commι := by simpa only [F.map_comp] using! F.congr_map ψ.commι

/-- When a homology data `h` of a short complex `S` is such that both `h.left` and
`h.right` are preserved by a functor `F`, this is the induced homology data
`h.map F` for the short complex `S.map F`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.map** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex.HomologyData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S : CategoryTheory.ShortComplex
 C} →               (h : S.HomologyData) →                 (F : CategoryTheory.F
unctor C D) →                   [inst_4 : F.PreservesZeroMorphisms] →           
          [h.left.IsPreservedBy F] → [h.right.IsPreservedBy F] → (S.map F).Homol
ogyData
参数：h : S.HomologyData；F : CategoryTheory.Functor C D；S.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a homology data `h` of a short complex `S` is such that both `h.left` and
`h.right` are preserved by a functor `F`, this is the induced homology data
`h.map F` for the short complex `S.map F`.
-/
noncomputable def HomologyData.map (h : S.HomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.left.IsPreservedBy F] [h.right.IsPreservedBy F] :
    (S.map F).HomologyData where
  left := h.left.map F
  right := h.right.map F
  iso := F.mapIso h.iso
  comm := by simpa only [F.map_comp] using! F.congr_map h.comm

/-- Given a homology map data `ψ : HomologyMapData φ h₁ h₂` such that
`h₁.left`, `h₁.right`, `h₂.left` and `h₂.right` are all preserved by a functor `F`, this is
the induced homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.map** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S₁ S₂ : CategoryTheory.ShortCom
plex C} →               {φ : S₁ ⟶ S₂} →                 {h₁ : S₁.HomologyData} →
                   {h₂ : S₂.HomologyData} →                     CategoryTheory.S
hortComplex.HomologyMapData φ h₁ h₂ →                       (F : CategoryTheory.
Functor C D) →                         [inst_4 : F.PreservesZeroMorphisms] →    
                       [inst_5 : h₁.left.IsPreservedBy F] →                     
        [inst_6 : h₁.right.IsPreservedBy F] →                               [ins
t_7 : h₂.left.IsPreservedBy F] →                                 [inst_8 : h₂.ri
ght.IsPreservedBy F] →                                   CategoryTheory.ShortCom
plex.HomologyMapData (F.mapShortComplex.map φ) (h₁.map F)                       
              (h₂.map F)
参数：F : CategoryTheory.Functor C D；F.mapShortComplex.map φ；h₁.map F；h₂.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a homology map data `ψ : HomologyMapData φ h₁ h₂` such that
`h₁.left`, `h₁.right`, `h₂.left` and `h₂.right` are all preserved by a functor `
F`, this is
the induced homology map data for the morphism `F.mapShortComplex.map φ`.
-/
noncomputable def HomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    HomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  left := ψ.left.map F
  right := ψ.right.map F

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.map_leftRightHomologyComparison'** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：map_leftRightHomologyComparison' (F : C ⥤ D) [F.PreservesZeroMorphisms] (h
ₗ : S.LeftHomologyData) (hᵣ : S.RightHomologyData) [hₗ.IsPreservedBy F] [hᵣ.IsPr
eservedBy F] : F.map (leftRightHomologyComparison' hₗ hᵣ) = leftRightHomologyCom
parison' (hₗ.map F) (hᵣ.map F)
参数：F : C ⥤ D；hₗ : S.LeftHomologyData；hᵣ : S.RightHomologyData。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wπ`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.wp`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.wι`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.map_π`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.map_ι`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.map_i`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.map_p`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma map_leftRightHomologyComparison' (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hₗ : S.LeftHomologyData) (hᵣ : S.RightHomologyData) [hₗ.IsPreservedBy F] [hᵣ.IsPreservedBy F] :
    F.map (leftRightHomologyComparison' hₗ hᵣ) =
      leftRightHomologyComparison' (hₗ.map F) (hᵣ.map F) := by
  apply Cofork.IsColimit.hom_ext (hₗ.map F).hπ
  apply Fork.IsLimit.hom_ext (hᵣ.map F).hι
  trans F.map (hₗ.i ≫ hᵣ.p)
  · simp [← Functor.map_comp]
  trans (hₗ.map F).π ≫ ShortComplex.leftRightHomologyComparison'
    (hₗ.map F) (hᵣ.map F) ≫ (hᵣ.map F).ι
  · rw [ShortComplex.π_leftRightHomologyComparison'_ι]; simp
  · simp

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [PreservesZeroMorphisms F] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- A functor preserves the left homology of a short complex `S` if it preserves all the
left homology data of `S`. -/
/-
**CategoryTheory.Functor.PreservesLeftHomologyOf** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D)
 → [F.PreservesZeroMorphisms] → CategoryTheory.ShortComplex C → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves the left homology of a short complex `S` if it preserves all
 the
left homology data of `S`.
-/
class PreservesLeftHomologyOf : Prop where
  /-- the functor preserves all the left homology data of the short complex -/
  isPreservedBy : ∀ (h : S.LeftHomologyData), h.IsPreservedBy F

/-- A functor preserves the right homology of a short complex `S` if it preserves all the
right homology data of `S`. -/
/-
**CategoryTheory.Functor.PreservesRightHomologyOf** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D)
 → [F.PreservesZeroMorphisms] → CategoryTheory.ShortComplex C → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves the right homology of a short complex `S` if it preserves al
l the
right homology data of `S`.
-/
class PreservesRightHomologyOf : Prop where
  /-- the functor preserves all the right homology data of the short complex -/
  isPreservedBy : ∀ (h : S.RightHomologyData), h.IsPreservedBy F
/-
**CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesHomology`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] (S : Cate
goryTheory.ShortComplex C) [F.PreservesHomology],   F.PreservesLeftHomologyOf S
参数：F : CategoryTheory.Functor C D；S : CategoryTheory.ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PreservesHomology.preservesLeftHomologyOf [F.PreservesHomology] :
    F.PreservesLeftHomologyOf S := ⟨inferInstance⟩
/-
**CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesHomology`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] (S : Cate
goryTheory.ShortComplex C) [F.PreservesHomology],   F.PreservesRightHomologyOf S
参数：F : CategoryTheory.Functor C D；S : CategoryTheory.ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PreservesHomology.preservesRightHomologyOf [F.PreservesHomology] :
    F.PreservesRightHomologyOf S := ⟨inferInstance⟩

variable {S}

/-- If a functor preserves a certain left homology data of a short complex `S`, then it
preserves the left homology of `S`. -/
/-
**CategoryTheory.Functor.PreservesLeftHomologyOf.mk'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.PreservesLeftHomologyOf`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] {S : Cate
goryTheory.ShortComplex C} (h : S.LeftHomologyData) [h.IsPreservedBy F],   F.Pre
servesLeftHomologyOf S
参数：F : CategoryTheory.Functor C D；h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.hg`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy.hf'`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.cyclesMapIso'_hom`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.f'_cyclesMap'`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
If a functor preserves a certain left homology data of a short complex `S`, then
 it
preserves the left homology of `S`.
-/
lemma PreservesLeftHomologyOf.mk' (h : S.LeftHomologyData) [h.IsPreservedBy F] :
    F.PreservesLeftHomologyOf S where
  isPreservedBy h' :=
    { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
      f' := by
        have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
        let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
          parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
            (by simp) (by simp)
        exact preservesColimit_of_iso_diagram F e }

/-- If a functor preserves a certain right homology data of a short complex `S`, then it
preserves the right homology of `S`. -/
/-
**CategoryTheory.Functor.PreservesRightHomologyOf.mk'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor.PreservesRightHomologyOf`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] {S : Cate
goryTheory.ShortComplex C} (h : S.RightHomologyData) [h.IsPreservedBy F],   F.Pr
eservesRightHomologyOf S
参数：F : CategoryTheory.Functor C D；h : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.hf`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy.hg'`：∀ {C : 
Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMapIso'_hom`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_g'`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
If a functor preserves a certain right homology data of a short complex `S`, the
n it
preserves the right homology of `S`.
-/
lemma PreservesRightHomologyOf.mk' (h : S.RightHomologyData) [h.IsPreservedBy F] :
    F.PreservesRightHomologyOf S where
  isPreservedBy h' :=
    { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
      g' := by
        have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
        let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
          parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
            (by simp) (by simp)
        exact preservesLimit_of_iso_diagram F e }

end Functor

namespace ShortComplex

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-
**CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h₁ : S.LeftHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf 
S], h₁.IsPreservedBy F
参数：h₁ : S.LeftHomologyData；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesLeftHomologyOf.isPreservedBy`：∀ {C : Typ
e u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : 
CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
instance LeftHomologyData.isPreservedBy_of_preserves [F.PreservesLeftHomologyOf S] :
    h₁.IsPreservedBy F :=
  Functor.PreservesLeftHomologyOf.isPreservedBy _
/-
**CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h₂ : S.RightHomologyData)   (F : CategoryTh
eory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [F.PreservesRightHomologyO
f S],   h₂.IsPreservedBy F
参数：h₂ : S.RightHomologyData；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesRightHomologyOf.isPreservedBy`：∀ {C : Ty
pe u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 :
 CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
instance RightHomologyData.isPreservedBy_of_preserves [F.PreservesRightHomologyOf S] :
    h₂.IsPreservedBy F :=
  Functor.PreservesRightHomologyOf.isPreservedBy _

variable (S)
/-
**CategoryTheory.ShortComplex.hasLeftHomology_of_preserves** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasLeftHomology_of_preserves [S.HasLeftHomology] [F.PreservesLeftHomologyO
f S] : (S.map F).HasLeftHomology
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance hasLeftHomology_of_preserves [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).HasLeftHomology :=
  HasLeftHomology.mk' (S.leftHomologyData.map F)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.hasLeftHomology_of_preserves'** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasLeftHomology_of_preserves' [S.HasLeftHomology] [F.PreservesLeftHomology
Of S] : (F.mapShortComplex.obj S).HasLeftHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLeftHomology_of_preserves' [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (F.mapShortComplex.obj S).HasLeftHomology := by
  dsimp; infer_instance
/-
**CategoryTheory.ShortComplex.hasRightHomology_of_preserves** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasRightHomology_of_preserves [S.HasRightHomology] [F.PreservesRightHomolo
gyOf S] : (S.map F).HasRightHomology
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasRightHomology.mk'`：mk' (h : S.RightHomolo
gyData) : HasRightHomology S
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance hasRightHomology_of_preserves [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).HasRightHomology :=
  HasRightHomology.mk' (S.rightHomologyData.map F)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.hasRightHomology_of_preserves'** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasRightHomology_of_preserves' [S.HasRightHomology] [F.PreservesRightHomol
ogyOf S] : (F.mapShortComplex.obj S).HasRightHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasRightHomology_of_preserves' [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasRightHomology := by
  dsimp; infer_instance
/-
**CategoryTheory.ShortComplex.hasHomology_of_preserves** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_preserves [S.HasHomology] [F.PreservesLeftHomologyOf S] [F.
PreservesRightHomologyOf S] : (S.map F).HasHomology
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance hasHomology_of_preserves [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    (S.map F).HasHomology :=
  HasHomology.mk' (S.homologyData.map F)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.hasHomology_of_preserves'** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_preserves' [S.HasHomology] [F.PreservesLeftHomologyOf S] [F
.PreservesRightHomologyOf S] : (F.mapShortComplex.obj S).HasHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasHomology_of_preserves' [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasHomology := by
  dsimp; infer_instance

section

variable
  (hl : S.LeftHomologyData) (hr : S.RightHomologyData)
  {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  (hl₁ : S₁.LeftHomologyData) (hr₁ : S₁.RightHomologyData)
  (hl₂ : S₂.LeftHomologyData) (hr₂ : S₂.RightHomologyData)
  (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

namespace LeftHomologyData

variable [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F]

/-
**CategoryTheory.ShortComplex.LeftHomologyData.map_cyclesMap'** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：map_cyclesMap' : F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) = ShortComplex.
cyclesMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.map_φK`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma map_cyclesMap' : F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) =
    ShortComplex.cyclesMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F) := by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.cyclesMap'_eq, (γ.map F).cyclesMap'_eq, ShortComplex.LeftHomologyMapData.map_φK]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：map_leftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = S
hortComplex.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.map_φH`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma map_leftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) =
    ShortComplex.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F) := by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.leftHomologyMap'_eq, (γ.map F).leftHomologyMap'_eq,
    ShortComplex.LeftHomologyMapData.map_φH]

end LeftHomologyData

namespace RightHomologyData

variable [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F]

/-
**CategoryTheory.ShortComplex.RightHomologyData.map_opcyclesMap'** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：map_opcyclesMap' : F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) = ShortComp
lex.opcyclesMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.map_φQ`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma map_opcyclesMap' : F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) =
    ShortComplex.opcyclesMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F) := by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.opcyclesMap'_eq, (γ.map F).opcyclesMap'_eq, ShortComplex.RightHomologyMapData.map_φQ]
/-
**CategoryTheory.ShortComplex.RightHomologyData.map_rightHomologyMap'** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：map_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) =
 ShortComplex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.map_φH`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma map_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) =
    ShortComplex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F) := by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.rightHomologyMap'_eq, (γ.map F).rightHomologyMap'_eq,
    ShortComplex.RightHomologyMapData.map_φH]

end RightHomologyData

/-
**CategoryTheory.ShortComplex.HomologyData.map_homologyMap'** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)   (h₁ : S₁.HomologyData) (
h₂ : S₂.HomologyData) (F : CategoryTheory.Functor C D) [inst_4 : F.PreservesZero
Morphisms]   [inst_5 : h₁.left.IsPreservedBy F] [inst_6 : h₁.right.IsPreservedBy
 F] [inst_7 : h₂.left.IsPreservedBy F]   [inst_8 : h₂.right.IsPreservedBy F],   
F.map (CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂) =     CategoryTheory.Sh
ortComplex.homologyMap' (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；F : CategoryTheory.Func
tor C D；CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂；F.mapShortComplex.map φ
；h₁.map F；h₂.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'`：map_l
eftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = ShortComplex
.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F)…
-/
lemma HomologyData.map_homologyMap'
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    F.map (ShortComplex.homologyMap' φ h₁ h₂) =
      ShortComplex.homologyMap' (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) :=
  LeftHomologyData.map_leftHomologyMap' _ _ _ _

/-- When a functor `F` preserves the left homology of a short complex `S`, this is the
canonical isomorphism `(S.map F).cycles ≅ F.obj S.cycles`. -/
/-
**CategoryTheory.ShortComplex.mapCyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：mapCyclesIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] : (S.map F)
.cycles ≅ F.obj S.cycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a functor `F` preserves the left homology of a short complex `S`, this is t
he
canonical isomorphism `(S.map F).cycles ≅ F.obj S.cycles`.
-/
noncomputable def mapCyclesIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).cycles ≅ F.obj S.cycles :=
  (S.leftHomologyData.map F).cyclesIso

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：mapCyclesIso_hom_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S]
 : (S.mapCyclesIso F).hom ≫ F.map S.iCycles = (S.map F).iCycles
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i`：cycle
sIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
-/
lemma mapCyclesIso_hom_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).hom ≫ F.map S.iCycles = (S.map F).iCycles := by
  apply LeftHomologyData.cyclesIso_hom_comp_i

/-- When a functor `F` preserves the left homology of a short complex `S`, this is the
canonical isomorphism `(S.map F).leftHomology ≅ F.obj S.leftHomology`. -/
/-
**CategoryTheory.ShortComplex.mapLeftHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：mapLeftHomologyIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] : (S.
map F).leftHomology ≅ F.obj S.leftHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a functor `F` preserves the left homology of a short complex `S`, this is t
he
canonical isomorphism `(S.map F).leftHomology ≅ F.obj S.leftHomology`.
-/
noncomputable def mapLeftHomologyIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).leftHomology ≅ F.obj S.leftHomology :=
  (S.leftHomologyData.map F).leftHomologyIso

/-- When a functor `F` preserves the right homology of a short complex `S`, this is the
canonical isomorphism `(S.map F).opcycles ≅ F.obj S.opcycles`. -/
/-
**CategoryTheory.ShortComplex.mapOpcyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：mapOpcyclesIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] : (S.ma
p F).opcycles ≅ F.obj S.opcycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a functor `F` preserves the right homology of a short complex `S`, this is 
the
canonical isomorphism `(S.map F).opcycles ≅ F.obj S.opcycles`.
-/
noncomputable def mapOpcyclesIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).opcycles ≅ F.obj S.opcycles :=
  (S.rightHomologyData.map F).opcyclesIso

/-- When a functor `F` preserves the right homology of a short complex `S`, this is the
canonical isomorphism `(S.map F).rightHomology ≅ F.obj S.rightHomology`. -/
/-
**CategoryTheory.ShortComplex.mapRightHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：mapRightHomologyIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] : 
(S.map F).rightHomology ≅ F.obj S.rightHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a functor `F` preserves the right homology of a short complex `S`, this is 
the
canonical isomorphism `(S.map F).rightHomology ≅ F.obj S.rightHomology`.
-/
noncomputable def mapRightHomologyIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).rightHomology ≅ F.obj S.rightHomology :=
  (S.rightHomologyData.map F).rightHomologyIso

/-- When a functor `F` preserves the left homology of a short complex `S`, this is the
canonical isomorphism `(S.map F).homology ≅ F.obj S.homology`. -/
/-
**CategoryTheory.ShortComplex.mapHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：mapHomologyIso [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHom
ologyOf S] : (S.map F).homology ≅ F.obj S.homology
参数：S.map F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a functor `F` preserves the left homology of a short complex `S`, this is t
he
canonical isomorphism `(S.map F).homology ≅ F.obj S.homology`.
-/
noncomputable def mapHomologyIso [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology :=
  (S.homologyData.left.map F).homologyIso

/-- When a functor `F` preserves the right homology of a short complex `S`, this is the
canonical isomorphism `(S.map F).homology ≅ F.obj S.homology`. -/
/-
**CategoryTheory.ShortComplex.mapHomologyIso'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：mapHomologyIso' [S.HasHomology] [(S.map F).HasHomology] [F.PreservesRightH
omologyOf S] : (S.map F).homology ≅ F.obj S.homology
参数：S.map F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a functor `F` preserves the right homology of a short complex `S`, this is 
the
canonical isomorphism `(S.map F).homology ≅ F.obj S.homology`.
-/
noncomputable def mapHomologyIso' [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesRightHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology :=
  (S.homologyData.right.map F).homologyIso ≪≫ F.mapIso S.homologyData.right.homologyIso.symm

variable {S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.LeftHomologyData.mapCyclesIso_eq** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (hl : S.LeftHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S.HasLeftHomology
]   [inst_6 : F.PreservesLeftHomologyOf S], S.mapCyclesIso F = (hl.map F).cycles
Iso ≪≫ F.mapIso hl.cyclesIso.symm
参数：hl : S.LeftHomologyData；F : CategoryTheory.Functor C D；hl.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_cyclesMap'`：map_cyclesM
ap' : F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) = ShortComplex.cyclesMap' (F.map
ShortComplex.map φ) (hl₁.map F) (hl₂.map F)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.mapCyclesIso_eq [S.HasLeftHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapCyclesIso F = (hl.map F).cyclesIso ≪≫ F.mapIso hl.cyclesIso.symm := by
  ext
  dsimp [mapCyclesIso, cyclesIso]
  simp only [map_cyclesMap', ← cyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.LeftHomologyData.mapLeftHomologyIso_eq** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (hl : S.LeftHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S.HasLeftHomology
]   [inst_6 : F.PreservesLeftHomologyOf S],   S.mapLeftHomologyIso F = (hl.map F
).leftHomologyIso ≪≫ F.mapIso hl.leftHomologyIso.symm
参数：hl : S.LeftHomologyData；F : CategoryTheory.Functor C D；hl.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.leftHomology_ext`：leftHomology_ext {A : C} (
f₁ f₂ : S.leftHomology ⟶ A) (h : S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂) : 
f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'`：map_l
eftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = ShortComplex
.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F)…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.mapLeftHomologyIso_eq [S.HasLeftHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapLeftHomologyIso F = (hl.map F).leftHomologyIso ≪≫ F.mapIso hl.leftHomologyIso.symm := by
  ext
  dsimp [mapLeftHomologyIso, leftHomologyIso]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.RightHomologyData.mapOpcyclesIso_eq** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (hr : S.RightHomologyData)   (F : CategoryTh
eory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S.HasRightHomolo
gy]   [inst_6 : F.PreservesRightHomologyOf S], S.mapOpcyclesIso F = (hr.map F).o
pcyclesIso ≪≫ F.mapIso hr.opcyclesIso.symm
参数：hr : S.RightHomologyData；F : CategoryTheory.Functor C D；hr.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.opcycles_ext`：opcycles_ext {A : C} (f₁ f₂ : 
S.opcycles ⟶ A) (h : S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.map_opcyclesMap'`：map_opcy
clesMap' : F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) = ShortComplex.opcyclesMa
p' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.mapOpcyclesIso_eq [S.HasRightHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapOpcyclesIso F = (hr.map F).opcyclesIso ≪≫ F.mapIso hr.opcyclesIso.symm := by
  ext
  dsimp [mapOpcyclesIso, opcyclesIso]
  simp only [map_opcyclesMap', ← opcyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.RightHomologyData.mapRightHomologyIso_eq** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (hr : S.RightHomologyData)   (F : CategoryTh
eory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S.HasRightHomolo
gy]   [inst_6 : F.PreservesRightHomologyOf S],   S.mapRightHomologyIso F = (hr.m
ap F).rightHomologyIso ≪≫ F.mapIso hr.rightHomologyIso.symm
参数：hr : S.RightHomologyData；F : CategoryTheory.Functor C D；hr.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.map_rightHomologyMap'`：map
_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) = ShortCom
plex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.mapRightHomologyIso_eq [S.HasRightHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapRightHomologyIso F = (hr.map F).rightHomologyIso ≪≫
      F.mapIso hr.rightHomologyIso.symm := by
  ext
  dsimp [mapRightHomologyIso, rightHomologyIso]
  simp only [map_rightHomologyMap', ← rightHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.LeftHomologyData.mapHomologyIso_eq** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (hl : S.LeftHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S.HasHomology]   
[inst_6 : (S.map F).HasHomology] [inst_7 : F.PreservesLeftHomologyOf S],   S.map
HomologyIso F = (hl.map F).homologyIso ≪≫ F.mapIso hl.homologyIso.symm
参数：hl : S.LeftHomologyData；F : CategoryTheory.Functor C D；S.map F；hl.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'`：map_l
eftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = ShortComplex
.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F)…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.mapHomologyIso_eq [S.HasHomology]
    [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    S.mapHomologyIso F = (hl.map F).homologyIso ≪≫ F.mapIso hl.homologyIso.symm := by
  ext
  dsimp only [mapHomologyIso, homologyIso, ShortComplex.leftHomologyIso,
    leftHomologyMapIso', leftHomologyIso, Functor.mapIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, Functor.map_id,
    Functor.mapShortComplex_obj]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.RightHomologyData.mapHomologyIso'_eq** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (hr : S.RightHomologyData)   (F : CategoryTh
eory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S.HasHomology]  
 [inst_6 : (S.map F).HasHomology] [inst_7 : F.PreservesRightHomologyOf S],   S.m
apHomologyIso' F = (hr.map F).homologyIso ≪≫ F.mapIso hr.homologyIso.symm
参数：hr : S.RightHomologyData；F : CategoryTheory.Functor C D；S.map F；hr.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.map_rightHomologyMap'`：map
_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) = ShortCom
plex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.mapHomologyIso'_eq [S.HasHomology]
    [(S.map F).HasHomology] [F.PreservesRightHomologyOf S] :
    S.mapHomologyIso' F = (hr.map F).homologyIso ≪≫ F.mapIso hr.homologyIso.symm := by
  ext
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, mapHomologyIso', homologyIso,
    rightHomologyIso, rightHomologyMapIso', ShortComplex.rightHomologyIso]
  simp only [assoc, F.map_comp, map_rightHomologyMap', ← rightHomologyMap'_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapCyclesIso_hom_naturality** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapCyclesIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology] [F.P
reservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] : cyclesMap (F.mapShor
tComplex.map φ) ≫ (S₂.mapCyclesIso F).hom = (S₁.mapCyclesIso F).hom ≫ F.map (cyc
lesMap φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_cyclesMap'`：map_cyclesM
ap' : F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) = ShortComplex.cyclesMap' (F.map
ShortComplex.map φ) (hl₁.map F) (hl₂.map F)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCyclesIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    cyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapCyclesIso F).hom =
      (S₁.mapCyclesIso F).hom ≫ F.map (cyclesMap φ) := by
  dsimp only [cyclesMap, mapCyclesIso, LeftHomologyData.cyclesIso, cyclesMapIso', Iso.refl]
  simp only [LeftHomologyData.map_cyclesMap', Functor.mapShortComplex_obj, ← cyclesMap'_comp,
    comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapCyclesIso_inv_naturality** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapCyclesIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology] [F.P
reservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] : F.map (cyclesMap φ) 
≫ (S₂.mapCyclesIso F).inv = (S₁.mapCyclesIso F).inv ≫ cyclesMap (F.mapShortCompl
ex.map φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.mapCyclesIso_hom_naturality_assoc`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapCyclesIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (cyclesMap φ) ≫ (S₂.mapCyclesIso F).inv =
      (S₁.mapCyclesIso F).inv ≫ cyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapCyclesIso F).hom, ← mapCyclesIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapLeftHomologyIso_hom_naturality** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapLeftHomologyIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology
] [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] : leftHomologyMa
p (F.mapShortComplex.map φ) ≫ (S₂.mapLeftHomologyIso F).hom = (S₁.mapLeftHomolog
yIso F).hom ≫ F.map (leftHomologyMap φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'`：map_l
eftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = ShortComplex
.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F)…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapLeftHomologyIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    leftHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapLeftHomologyIso F).hom =
      (S₁.mapLeftHomologyIso F).hom ≫ F.map (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap, mapLeftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', Functor.mapShortComplex_obj,
    ← leftHomologyMap'_comp, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapLeftHomologyIso_inv_naturality** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapLeftHomologyIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology
] [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] : F.map (leftHom
ologyMap φ) ≫ (S₂.mapLeftHomologyIso F).inv = (S₁.mapLeftHomologyIso F).inv ≫ le
ftHomologyMap (F.mapShortComplex.map φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.mapLeftHomologyIso_hom_naturality_assoc`：∀ {
C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapLeftHomologyIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (leftHomologyMap φ) ≫ (S₂.mapLeftHomologyIso F).inv =
      (S₁.mapLeftHomologyIso F).inv ≫ leftHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapLeftHomologyIso F).hom, ← mapLeftHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapOpcyclesIso_hom_naturality** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapOpcyclesIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology] 
[F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] : opcyclesMap (F
.mapShortComplex.map φ) ≫ (S₂.mapOpcyclesIso F).hom = (S₁.mapOpcyclesIso F).hom 
≫ F.map (opcyclesMap φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.map_opcyclesMap'`：map_opcy
clesMap' : F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) = ShortComplex.opcyclesMa
p' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapOpcyclesIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    opcyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapOpcyclesIso F).hom =
      (S₁.mapOpcyclesIso F).hom ≫ F.map (opcyclesMap φ) := by
  dsimp only [opcyclesMap, mapOpcyclesIso, RightHomologyData.opcyclesIso,
    opcyclesMapIso', Iso.refl]
  simp only [RightHomologyData.map_opcyclesMap', Functor.mapShortComplex_obj, ← opcyclesMap'_comp,
    comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapOpcyclesIso_inv_naturality** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapOpcyclesIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology] 
[F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] : F.map (opcycle
sMap φ) ≫ (S₂.mapOpcyclesIso F).inv = (S₁.mapOpcyclesIso F).inv ≫ opcyclesMap (F
.mapShortComplex.map φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.mapOpcyclesIso_hom_naturality_assoc`：∀ {C : 
Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapOpcyclesIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (opcyclesMap φ) ≫ (S₂.mapOpcyclesIso F).inv =
      (S₁.mapOpcyclesIso F).inv ≫ opcyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapOpcyclesIso F).hom, ← mapOpcyclesIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapRightHomologyIso_hom_naturality** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapRightHomologyIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomol
ogy] [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] : rightHomo
logyMap (F.mapShortComplex.map φ) ≫ (S₂.mapRightHomologyIso F).hom = (S₁.mapRigh
tHomologyIso F).hom ≫ F.map (rightHomologyMap φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.map_rightHomologyMap'`：map
_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) = ShortCom
plex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRightHomologyIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    rightHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapRightHomologyIso F).hom =
      (S₁.mapRightHomologyIso F).hom ≫ F.map (rightHomologyMap φ) := by
  dsimp only [rightHomologyMap, mapRightHomologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', Iso.refl]
  simp only [RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    ← rightHomologyMap'_comp, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapRightHomologyIso_inv_naturality** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapRightHomologyIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomol
ogy] [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] : F.map (ri
ghtHomologyMap φ) ≫ (S₂.mapRightHomologyIso F).inv = (S₁.mapRightHomologyIso F).
inv ≫ rightHomologyMap (F.mapShortComplex.map φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.mapRightHomologyIso_hom_naturality_assoc`：∀ 
{C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapRightHomologyIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (rightHomologyMap φ) ≫ (S₂.mapRightHomologyIso F).inv =
      (S₁.mapRightHomologyIso F).inv ≫ rightHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapRightHomologyIso F).hom, ← mapRightHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] [(S₁.map F
).HasHomology] [(S₂.map F).HasHomology] [F.PreservesLeftHomologyOf S₁] [F.Preser
vesLeftHomologyOf S₂] : @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComp
lex.map φ) _ _ ≫ (S₂.mapHomologyIso F).hom = (S₁.mapHomologyIso F).hom ≫ F.map (
homologyMap φ)
参数：S₁.map F；S₂.map F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'`：map_l
eftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = ShortComplex
.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F)…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ ≫
      (S₂.mapHomologyIso F).hom = (S₁.mapHomologyIso F).hom ≫ F.map (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap', mapHomologyIso, LeftHomologyData.homologyIso,
    LeftHomologyData.leftHomologyIso, leftHomologyMapIso', leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, id_comp]

@[reassoc]
/-
**CategoryTheory.ShortComplex.mapHomologyIso_inv_naturality** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mapHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] [(S₁.map F
).HasHomology] [(S₂.map F).HasHomology] [F.PreservesLeftHomologyOf S₁] [F.Preser
vesLeftHomologyOf S₂] : F.map (homologyMap φ) ≫ (S₂.mapHomologyIso F).inv = (S₁.
mapHomologyIso F).inv ≫ @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComp
lex.map φ) _ _
参数：S₁.map F；S₂.map F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality_assoc`：∀ {C : 
Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (homologyMap φ) ≫ (S₂.mapHomologyIso F).inv =
      (S₁.mapHomologyIso F).inv ≫
      @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ := by
  rw [← cancel_epi (S₁.mapHomologyIso F).hom, ← mapHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.mapHomologyIso'_hom_naturality** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)   (F : CategoryTheory.Func
tor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S₁.HasHomology]   [inst_6
 : S₂.HasHomology] [inst_7 : (S₁.map F).HasHomology] [inst_8 : (S₂.map F).HasHom
ology]   [inst_9 : F.PreservesRightHomologyOf S₁] [inst_10 : F.PreservesRightHom
ologyOf S₂],   CategoryTheory.CategoryStruct.comp (CategoryTheory.ShortComplex.h
omologyMap (F.mapShortComplex.map φ))       (S₂.mapHomologyIso' F).hom =     Cat
egoryTheory.CategoryStruct.comp (S₁.mapHomologyIso' F).hom (F.map (CategoryTheor
y.ShortComplex.homologyMap φ))
参数：φ : S₁ ⟶ S₂；F : CategoryTheory.Functor C D；S₁.map F；S₂.map F；CategoryTheory.S
hortComplex.homologyMap (F.mapShortComplex.map φ)；S₂.mapHomologyIso' F；S₁.mapHom
ologyIso' F；F.map (CategoryTheory.ShortComplex.homologyMap φ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_hom_natur
ality_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_inv_natur
ality`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapHomologyIso'_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ ≫
      (S₂.mapHomologyIso' F).hom = (S₁.mapHomologyIso' F).hom ≫ F.map (homologyMap φ) := by
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, mapHomologyIso']
  simp only [← RightHomologyData.rightHomologyIso_hom_naturality_assoc _
    ((homologyData S₁).right.map F) ((homologyData S₂).right.map F), assoc,
    ← RightHomologyData.map_rightHomologyMap', ← F.map_comp,
    RightHomologyData.rightHomologyIso_inv_naturality _
      (homologyData S₁).right (homologyData S₂).right]

@[reassoc]
/-
**CategoryTheory.ShortComplex.mapHomologyIso'_inv_naturality** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)   (F : CategoryTheory.Func
tor C D) [inst_4 : F.PreservesZeroMorphisms] [inst_5 : S₁.HasHomology]   [inst_6
 : S₂.HasHomology] [inst_7 : (S₁.map F).HasHomology] [inst_8 : (S₂.map F).HasHom
ology]   [inst_9 : F.PreservesRightHomologyOf S₁] [inst_10 : F.PreservesRightHom
ologyOf S₂],   CategoryTheory.CategoryStruct.comp (F.map (CategoryTheory.ShortCo
mplex.homologyMap φ)) (S₂.mapHomologyIso' F).inv =     CategoryTheory.CategorySt
ruct.comp (S₁.mapHomologyIso' F).inv       (CategoryTheory.ShortComplex.homology
Map (F.mapShortComplex.map φ))
参数：φ : S₁ ⟶ S₂；F : CategoryTheory.Functor C D；S₁.map F；S₂.map F；F.map (CategoryT
heory.ShortComplex.homologyMap φ)；S₂.mapHomologyIso' F；S₁.mapHomologyIso' F；Cate
goryTheory.ShortComplex.homologyMap (F.mapShortComplex.map φ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.mapHomologyIso'_hom_naturality_assoc`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapHomologyIso'_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (homologyMap φ) ≫ (S₂.mapHomologyIso' F).inv = (S₁.mapHomologyIso' F).inv ≫
      @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ := by
  rw [← cancel_epi (S₁.mapHomologyIso' F).hom, ← mapHomologyIso'_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

variable (S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.mapHomologyIso'_eq_mapHomologyIso** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(S : CategoryTheory.ShortComplex C)   (F : CategoryTheory.Functor C D) [inst_4 :
 F.PreservesZeroMorphisms] [inst_5 : S.HasHomology]   [inst_6 : F.PreservesLeftH
omologyOf S] [inst_7 : F.PreservesRightHomologyOf S],   S.mapHomologyIso' F = S.
mapHomologyIso F
参数：S : CategoryTheory.ShortComplex C；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.mapHomologyIso_eq`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.mapHomologyIso'_eq`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.map_rightHomologyMap'`：map
_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) = ShortCom
plex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.map_leftHomologyMap'`：map_l
eftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) = ShortComplex
.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F)…
· 使用引理 `CategoryTheory.ShortComplex.HomologyMapData.comm`：comm (h : HomologyMapD
ata φ h₁ h₂) : h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ h.right.φH
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapHomologyIso'_eq_mapHomologyIso [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    S.mapHomologyIso' F = S.mapHomologyIso F := by
  ext
  rw [S.homologyData.left.mapHomologyIso_eq F, S.homologyData.right.mapHomologyIso'_eq F]
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso, LeftHomologyData.homologyIso,
    leftHomologyIso, LeftHomologyData.leftHomologyIso]
  simp only [RightHomologyData.map_H, rightHomologyMapIso'_inv, rightHomologyMapIso'_hom, assoc,
    Functor.map_comp, RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    Functor.map_id, LeftHomologyData.map_H, leftHomologyMapIso'_inv, leftHomologyMapIso'_hom,
    LeftHomologyData.map_leftHomologyMap', ← rightHomologyMap'_comp_assoc, ← leftHomologyMap'_comp,
    id_comp]
  have γ : HomologyMapData (𝟙 (S.map F)) (map S F).homologyData (S.homologyData.map F) := default
  have eq := γ.comm
  rw [← γ.left.leftHomologyMap'_eq, ← γ.right.rightHomologyMap'_eq] at eq
  dsimp at eq
  simp only [← reassoc_of% eq, ← F.map_comp, Iso.hom_inv_id, F.map_id, comp_id]

end

section

variable {S}
  {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S]
  [F.PreservesRightHomologyOf S] [G.PreservesRightHomologyOf S]

set_option backward.defeqAttrib.useBackward true in
/-- Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preserve
the left homology of a short complex `S`, and a left homology data for `S`,
this is the left homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.natTransApp** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S : CategoryTheory.ShortComplex
 C} →               {F G : CategoryTheory.Functor C D} →                 [inst_4
 : F.PreservesZeroMorphisms] →                   [inst_5 : G.PreservesZeroMorphi
sms] →                     [inst_6 : F.PreservesLeftHomologyOf S] →             
          [inst_7 : G.PreservesLeftHomologyOf S] →                         (h : 
S.LeftHomologyData) →                           (τ : F ⟶ G) →                   
          CategoryTheory.ShortComplex.LeftHomologyMapData (S.mapNatTrans τ) (h.m
ap F) (h.map G)
参数：h : S.LeftHomologyData；τ : F ⟶ G；S.mapNatTrans τ；h.map F；h.map G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preser
ve
the left homology of a short complex `S`, and a left homology data for `S`,
this is the left homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`.
-/
noncomputable def LeftHomologyMapData.natTransApp (h : LeftHomologyData S) (τ : F ⟶ G) :
    LeftHomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  φK := τ.app h.K
  φH := τ.app h.H

set_option backward.defeqAttrib.useBackward true in
/-- Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preserve
the right homology of a short complex `S`, and a right homology data for `S`,
this is the right homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.natTransApp** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S : CategoryTheory.ShortComplex
 C} →               {F G : CategoryTheory.Functor C D} →                 [inst_4
 : F.PreservesZeroMorphisms] →                   [inst_5 : G.PreservesZeroMorphi
sms] →                     [inst_6 : F.PreservesRightHomologyOf S] →            
           [inst_7 : G.PreservesRightHomologyOf S] →                         (h 
: S.RightHomologyData) →                           (τ : F ⟶ G) →                
             CategoryTheory.ShortComplex.RightHomologyMapData (S.mapNatTrans τ) 
(h.map F) (h.map G)
参数：h : S.RightHomologyData；τ : F ⟶ G；S.mapNatTrans τ；h.map F；h.map G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preser
ve
the right homology of a short complex `S`, and a right homology data for `S`,
this is the right homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`.
-/
noncomputable def RightHomologyMapData.natTransApp (h : RightHomologyData S) (τ : F ⟶ G) :
    RightHomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  φQ := τ.app h.Q
  φH := τ.app h.H

/-- Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preserve
the homology of a short complex `S`, and a homology data for `S`,
this is the homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.natTransApp** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : Category
Theory.Limits.HasZeroMorphisms D] →             {S : CategoryTheory.ShortComplex
 C} →               {F G : CategoryTheory.Functor C D} →                 [inst_4
 : F.PreservesZeroMorphisms] →                   [inst_5 : G.PreservesZeroMorphi
sms] →                     [inst_6 : F.PreservesLeftHomologyOf S] →             
          [inst_7 : G.PreservesLeftHomologyOf S] →                         [inst
_8 : F.PreservesRightHomologyOf S] →                           [inst_9 : G.Prese
rvesRightHomologyOf S] →                             (h : S.HomologyData) →     
                          (τ : F ⟶ G) →                                 Category
Theory.ShortComplex.HomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G)
参数：h : S.HomologyData；τ : F ⟶ G；S.mapNatTrans τ；h.map F；h.map G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preser
ve
the homology of a short complex `S`, and a homology data for `S`,
this is the homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`.
-/
noncomputable def HomologyMapData.natTransApp (h : HomologyData S) (τ : F ⟶ G) :
    HomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  left := LeftHomologyMapData.natTransApp h.left τ
  right := RightHomologyMapData.natTransApp h.right τ

variable (S)
/-
**CategoryTheory.ShortComplex.homologyMap_mapNatTrans** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：homologyMap_mapNatTrans [S.HasHomology] (τ : F ⟶ G) : homologyMap (S.mapNa
tTrans τ) = (S.mapHomologyIso F).hom ≫ τ.app S.homology ≫ (S.mapHomologyIso G).i
nv
参数：τ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_eq`：homology
Map_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma homologyMap_mapNatTrans [S.HasHomology] (τ : F ⟶ G) :
    homologyMap (S.mapNatTrans τ) =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology ≫ (S.mapHomologyIso G).inv :=
  (LeftHomologyMapData.natTransApp S.homologyData.left τ).homologyMap_eq

end

section

variable [HasKernels C] [HasCokernels C] [HasKernels D] [HasCokernels D]

/-- The natural isomorphism
`F.mapShortComplex ⋙ cyclesFunctor D ≅ cyclesFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology. -/
/-
**CategoryTheory.ShortComplex.cyclesFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：cyclesFunctorIso [F.PreservesHomology] : F.mapShortComplex ⋙ ShortComplex.
cyclesFunctor D ≅ ShortComplex.cyclesFunctor C ⋙ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The natural isomorphism
`F.mapShortComplex ⋙ cyclesFunctor D ≅ cyclesFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology.
-/
noncomputable def cyclesFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.cyclesFunctor D ≅
      ShortComplex.cyclesFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapCyclesIso F)
    (fun f => ShortComplex.mapCyclesIso_hom_naturality f F)

/-- The natural isomorphism
`F.mapShortComplex ⋙ leftHomologyFunctor D ≅ leftHomologyFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology. -/
/-
**CategoryTheory.ShortComplex.leftHomologyFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：leftHomologyFunctorIso [F.PreservesHomology] : F.mapShortComplex ⋙ ShortCo
mplex.leftHomologyFunctor D ≅ ShortComplex.leftHomologyFunctor C ⋙ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The natural isomorphism
`F.mapShortComplex ⋙ leftHomologyFunctor D ≅ leftHomologyFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology.
-/
noncomputable def leftHomologyFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.leftHomologyFunctor D ≅
      ShortComplex.leftHomologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapLeftHomologyIso F)
    (fun f => ShortComplex.mapLeftHomologyIso_hom_naturality f F)

/-- The natural isomorphism
`F.mapShortComplex ⋙ opcyclesFunctor D ≅ opcyclesFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology. -/
/-
**CategoryTheory.ShortComplex.opcyclesFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：opcyclesFunctorIso [F.PreservesHomology] : F.mapShortComplex ⋙ ShortComple
x.opcyclesFunctor D ≅ ShortComplex.opcyclesFunctor C ⋙ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The natural isomorphism
`F.mapShortComplex ⋙ opcyclesFunctor D ≅ opcyclesFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology.
-/
noncomputable def opcyclesFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.opcyclesFunctor D ≅
      ShortComplex.opcyclesFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapOpcyclesIso F)
    (fun f => ShortComplex.mapOpcyclesIso_hom_naturality f F)

/-- The natural isomorphism
`F.mapShortComplex ⋙ rightHomologyFunctor D ≅ rightHomologyFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology. -/
/-
**CategoryTheory.ShortComplex.rightHomologyFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：rightHomologyFunctorIso [F.PreservesHomology] : F.mapShortComplex ⋙ ShortC
omplex.rightHomologyFunctor D ≅ ShortComplex.rightHomologyFunctor C ⋙ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The natural isomorphism
`F.mapShortComplex ⋙ rightHomologyFunctor D ≅ rightHomologyFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology.
-/
noncomputable def rightHomologyFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.rightHomologyFunctor D ≅
      ShortComplex.rightHomologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapRightHomologyIso F)
    (fun f => ShortComplex.mapRightHomologyIso_hom_naturality f F)

end

/-- The natural isomorphism
`F.mapShortComplex ⋙ homologyFunctor D ≅ homologyFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology. -/
/-
**CategoryTheory.ShortComplex.homologyFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：homologyFunctorIso [CategoryWithHomology C] [CategoryWithHomology D] [F.Pr
eservesHomology] : F.mapShortComplex ⋙ ShortComplex.homologyFunctor D ≅ ShortCom
plex.homologyFunctor C ⋙ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The natural isomorphism
`F.mapShortComplex ⋙ homologyFunctor D ≅ homologyFunctor C ⋙ F`
for a functor `F : C ⥤ D` which preserves homology.
-/
noncomputable def homologyFunctorIso
    [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.homologyFunctor D ≅
      ShortComplex.homologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality f F)

section

variable
  {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
  {hl₁ : S₁.LeftHomologyData} {hr₁ : S₁.RightHomologyData}
  {hl₂ : S₂.LeftHomologyData} {hr₂ : S₂.RightHomologyData}
  (ψl : LeftHomologyMapData φ hl₁ hl₂)
  (ψr : RightHomologyMapData φ hr₁ hr₂)

/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_map_iff** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] {S₁ S₂ : 
CategoryTheory.ShortComplex C} {φ : S₁ ⟶ S₂} {hl₁ : S₁.LeftHomologyData}   {hl₂ 
: S₂.LeftHomologyData} (ψl : CategoryTheory.ShortComplex.LeftHomologyMapData φ h
l₁ hl₂)   [inst_5 : (F.mapShortComplex.obj S₁).HasHomology] [inst_6 : (F.mapShor
tComplex.obj S₂).HasHomology]   [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F],   C
ategoryTheory.ShortComplex.QuasiIso (F.mapShortComplex.map φ) ↔ CategoryTheory.I
sIso (F.map ψl.φH)
参数：F : CategoryTheory.Functor C D；ψl : CategoryTheory.ShortComplex.LeftHomologyM
apData φ hl₁ hl₂；F.mapShortComplex.obj S₁；F.mapShortComplex.obj S₂；F.mapShortCom
plex.map φ；F.map ψl.φH。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma LeftHomologyMapData.quasiIso_map_iff
    [(F.mapShortComplex.obj S₁).HasHomology]
    [(F.mapShortComplex.obj S₂).HasHomology]
    [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ IsIso (F.map ψl.φH) :=
  (ψl.map F).quasiIso_iff
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_map_iff** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
(F : CategoryTheory.Functor C D)   [inst_4 : F.PreservesZeroMorphisms] {S₁ S₂ : 
CategoryTheory.ShortComplex C} {φ : S₁ ⟶ S₂} {hr₁ : S₁.RightHomologyData}   {hr₂
 : S₂.RightHomologyData} (ψr : CategoryTheory.ShortComplex.RightHomologyMapData 
φ hr₁ hr₂)   [inst_5 : (F.mapShortComplex.obj S₁).HasHomology] [inst_6 : (F.mapS
hortComplex.obj S₂).HasHomology]   [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F], 
  CategoryTheory.ShortComplex.QuasiIso (F.mapShortComplex.map φ) ↔ CategoryTheor
y.IsIso (F.map ψr.φH)
参数：F : CategoryTheory.Functor C D；ψr : CategoryTheory.ShortComplex.RightHomology
MapData φ hr₁ hr₂；F.mapShortComplex.obj S₁；F.mapShortComplex.obj S₂；F.mapShortCo
mplex.map φ；F.map ψr.φH。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma RightHomologyMapData.quasiIso_map_iff
    [(F.mapShortComplex.obj S₁).HasHomology]
    [(F.mapShortComplex.obj S₂).HasHomology]
    [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ IsIso (F.map ψr.φH) :=
  (ψr.map F).quasiIso_iff

variable (φ) [S₁.HasHomology] [S₂.HasHomology]
    [(F.mapShortComplex.obj S₁).HasHomology] [(F.mapShortComplex.obj S₂).HasHomology]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_map_of_preservesLeftHomology** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_map_of_preservesLeftHomology [F.PreservesLeftHomologyOf S₁] [F.Pr
eservesLeftHomologyOf S₂] [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.map_φH`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance quasiIso_map_of_preservesLeftHomology
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ) := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff, LeftHomologyMapData.map_φH]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_map_iff_of_preservesLeftHomology** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_map_iff_of_preservesLeftHomology [F.PreservesLeftHomologyOf S₁] [
F.PreservesLeftHomologyOf S₂] [F.ReflectsIsomorphisms] : QuasiIso (F.mapShortCom
plex.map φ) ↔ QuasiIso φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.map_φH`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
lemma quasiIso_map_iff_of_preservesLeftHomology
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    [F.ReflectsIsomorphisms] :
    QuasiIso (F.mapShortComplex.map φ) ↔ QuasiIso φ := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  rw [γ.quasiIso_iff, (γ.map F).quasiIso_iff, LeftHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_map_of_preservesRightHomology** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_map_of_preservesRightHomology [F.PreservesRightHomologyOf S₁] [F.
PreservesRightHomologyOf S₂] [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.map_φH`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance quasiIso_map_of_preservesRightHomology
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂]
    [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ) := by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff, RightHomologyMapData.map_φH]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_map_iff_of_preservesRightHomology** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_map_iff_of_preservesRightHomology [F.PreservesRightHomologyOf S₁]
 [F.PreservesRightHomologyOf S₂] [F.ReflectsIsomorphisms] : QuasiIso (F.mapShort
Complex.map φ) ↔ QuasiIso φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.map_φH`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
lemma quasiIso_map_iff_of_preservesRightHomology
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂]
    [F.ReflectsIsomorphisms] :
    QuasiIso (F.mapShortComplex.map φ) ↔ QuasiIso φ := by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  rw [γ.quasiIso_iff, (γ.map F).quasiIso_iff, RightHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

end

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

/-- If a short complex `S` is such that `S.f = 0` and that the kernel of `S.g` is preserved
by a functor `F`, then `F` preserves the left homology of `S`. -/
/-
**CategoryTheory.Functor.preservesLeftHomology_of_zero_f** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：preservesLeftHomology_of_zero_f (hf : S.f = 0) [PreservesLimit (parallelPa
ir S.g 0) F] : F.PreservesLeftHomologyOf S
参数：hf : S.f = 0；parallelPair S.g 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesCokernel_zero'`：preservesCokernel_zero' (
f : X ⟶ Y) (hf : f = 0) : PreservesColimit (parallelPair f 0) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)

--- 原说明 ---
If a short complex `S` is such that `S.f = 0` and that the kernel of `S.g` is pr
eserved
by a functor `F`, then `F` preserves the left homology of `S`.
-/
lemma preservesLeftHomology_of_zero_f (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by infer_instance
    f' := Limits.preservesCokernel_zero' _ _
      (by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]) }⟩

/-- If a short complex `S` is such that `S.g = 0` and that the cokernel of `S.f` is preserved
by a functor `F`, then `F` preserves the right homology of `S`. -/
/-
**CategoryTheory.Functor.preservesRightHomology_of_zero_g** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：preservesRightHomology_of_zero_g (hg : S.g = 0) [PreservesColimit (paralle
lPair S.f 0) F] : F.PreservesRightHomologyOf S
参数：hg : S.g = 0；parallelPair S.f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesKernel_zero'`：preservesKernel_zero' (f : 
X ⟶ Y) (hf : f = 0) : PreservesLimit (parallelPair f 0) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instEpiP`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)

--- 原说明 ---
If a short complex `S` is such that `S.g = 0` and that the cokernel of `S.f` is 
preserved
by a functor `F`, then `F` preserves the right homology of `S`.
-/
lemma preservesRightHomology_of_zero_g (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by infer_instance
    g' := Limits.preservesKernel_zero' _ _
      (by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]) }⟩

set_option backward.isDefEq.respectTransparency false in
/-- If a short complex `S` is such that `S.g = 0` and that the cokernel of `S.f` is preserved
by a functor `F`, then `F` preserves the left homology of `S`. -/
/-
**CategoryTheory.Functor.preservesLeftHomology_of_zero_g** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：preservesLeftHomology_of_zero_g (hg : S.g = 0) [PreservesColimit (parallel
Pair S.f 0) F] : F.PreservesLeftHomologyOf S
参数：hg : S.g = 0；parallelPair S.f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.isIso_i`：isIso_i (hg : S.g 
= 0) : IsIso h.i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
If a short complex `S` is such that `S.g = 0` and that the cokernel of `S.f` is 
preserved
by a functor `F`, then `F` preserves the left homology of `S`.
-/
lemma preservesLeftHomology_of_zero_g (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by
      rw [hg]
      infer_instance
    f' := by
      have := h.isIso_i hg
      let e : parallelPair h.f' 0 ≅ parallelPair S.f 0 :=
        parallelPair.ext (Iso.refl _) (asIso h.i) (by simp) (by simp)
      exact Limits.preservesColimit_of_iso_diagram F e.symm}⟩

set_option backward.isDefEq.respectTransparency false in
/-- If a short complex `S` is such that `S.f = 0` and that the kernel of `S.g` is preserved
by a functor `F`, then `F` preserves the right homology of `S`. -/
/-
**CategoryTheory.Functor.preservesRightHomology_of_zero_f** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：preservesRightHomology_of_zero_f (hf : S.f = 0) [PreservesLimit (parallelP
air S.g 0) F] : F.PreservesRightHomologyOf S
参数：hf : S.f = 0；parallelPair S.g 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.isIso_p`：isIso_p (hf : S.f
 = 0) : IsIso h.p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
If a short complex `S` is such that `S.f = 0` and that the kernel of `S.g` is pr
eserved
by a functor `F`, then `F` preserves the right homology of `S`.
-/
lemma preservesRightHomology_of_zero_f (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by
      rw [hf]
      infer_instance
    g' := by
      have := h.isIso_p hf
      let e : parallelPair S.g 0 ≅ parallelPair h.g' 0 :=
        parallelPair.ext (asIso h.p) (Iso.refl _) (by simp) (by simp)
      exact Limits.preservesLimit_of_iso_diagram F e }⟩

end Functor

/-
**CategoryTheory.NatTrans.app_homology** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{F G : CategoryTheory.Functor C D} (τ : F ⟶ G)   (S : CategoryTheory.ShortComple
x C) [inst_4 : S.HasHomology] [inst_5 : F.PreservesZeroMorphisms]   [inst_6 : G.
PreservesZeroMorphisms] [inst_7 : F.PreservesLeftHomologyOf S] [inst_8 : G.Prese
rvesLeftHomologyOf S]   [inst_9 : F.PreservesRightHomologyOf S] [inst_10 : G.Pre
servesRightHomologyOf S],   τ.app S.homology =     CategoryTheory.CategoryStruct
.comp (S.mapHomologyIso F).inv       (CategoryTheory.CategoryStruct.comp (Catego
ryTheory.ShortComplex.homologyMap (S.mapNatTrans τ))         (S.mapHomologyIso G
).hom)
参数：τ : F ⟶ G；S : CategoryTheory.ShortComplex C；S.mapHomologyIso F；CategoryTheory
.CategoryStruct.comp (CategoryTheory.ShortComplex.homologyMap (S.mapNatTrans τ))
         (S.mapHomologyIso G).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_mapNatTrans`：homologyMap_mapNatT
rans [S.HasHomology] (τ : F ⟶ G) : homologyMap (S.mapNatTrans τ) = (S.mapHomolog
yIso F).hom ≫ τ.app S.homology ≫ (S.mapHo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma NatTrans.app_homology {F G : C ⥤ D} (τ : F ⟶ G)
    (S : ShortComplex C) [S.HasHomology] [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [G.PreservesRightHomologyOf S] :
    τ.app S.homology = (S.mapHomologyIso F).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom := by
  rw [ShortComplex.homologyMap_mapNatTrans, assoc, assoc, Iso.inv_hom_id,
    comp_id, Iso.inv_hom_id_assoc]

end CategoryTheory

