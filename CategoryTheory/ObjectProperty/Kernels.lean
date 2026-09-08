/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Objects that are (co)kernels of morphisms

Given a morphism property `W` on a category, we introduce two object properties
`kernels W` and `cokernels W`, consisting of all (co)kernels of morphisms
satisfying `W`.

Given an object property `P`, we also introduce two predicates
`P.IsClosedUnderKernels` and `P.IsClosedUnderCokernels`, stating that all
(co)kernels of morphisms between objects in `P` remain in `P`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- The property of objects that are kernels of morphisms satisfying `W`. -/
/-
**CategoryTheory.MorphismProperty.kernels** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [Ca
tegoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.MorphismProperty C → Ca
tegoryTheory.ObjectProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are kernels of morphisms satisfying `W`.
-/
inductive kernels : ObjectProperty C
  | of_isLimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : KernelFork f) (hk : IsLimit k)
    (hf : W f) : kernels k.pt
/-
**CategoryTheory.MorphismProperty.nonempty_kernels** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：nonempty_kernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f] : W.ke
rnels.Nonempty
参数：f : X₁ ⟶ X₂；hf : W f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma nonempty_kernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f] :
    W.kernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (kernels.of_isLimit f _ (kernelIsKernel f) hf)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : W.kernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isLimit f (KernelFork.ofι (i.inv ≫ k.ι) (by simp))
      (IsLimit.ofIsoLimit hk (Fork.ext i)) hf

/-- The property of objects that are cokernels of morphisms satisfying `W`. -/
/-
**CategoryTheory.MorphismProperty.cokernels** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [Ca
tegoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.MorphismProperty C → Ca
tegoryTheory.ObjectProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are cokernels of morphisms satisfying `W`.
-/
inductive cokernels : ObjectProperty C
  | of_isColimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : CokernelCofork f) (hk : IsColimit k)
    (hf : W f) : cokernels k.pt
/-
**CategoryTheory.MorphismProperty.nonempty_cokernels** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：nonempty_cokernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f] : 
W.cokernels.Nonempty
参数：f : X₁ ⟶ X₂；hf : W f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma nonempty_cokernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f] :
    W.cokernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (cokernels.of_isColimit f _ (cokernelIsCokernel f) hf)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : W.cokernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isColimit f (CokernelCofork.ofπ (k.π ≫ i.hom) (by simp))
      (IsColimit.ofIsoColimit hk (Cofork.ext i)) hf

end MorphismProperty

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- A property of objects satisfies `P.IsClosedUnderKernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.IsClosedUnderKernels** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [Ca
tegoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects satisfies `P.IsClosedUnderKernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`.
-/
class IsClosedUnderKernels : Prop where
  kernels_le : (MorphismProperty.ofObjectProperty P P).kernels ≤ P
/-
**CategoryTheory.ObjectProperty.prop_of_isLimit_kernelFork** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_of_isLimit_kernelFork [P.IsClosedUnderKernels] {X Y : C} {f : X ⟶ Y} 
{k : KernelFork f} (hk : IsLimit k) (hX : P X) (hY : P Y) : P k.pt
参数：hk : IsLimit k；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderKernels.kernels_le`：∀ {C : Ty
pe u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C}   {P : CategoryTheory.Obj…
-/
lemma prop_of_isLimit_kernelFork [P.IsClosedUnderKernels] {X Y : C} {f : X ⟶ Y} {k : KernelFork f}
    (hk : IsLimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderKernels.kernels_le _ (.of_isLimit _ k hk ⟨hX, hY⟩)
/-
**CategoryTheory.ObjectProperty.prop_kernel** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：prop_kernel [P.IsClosedUnderKernels] {X Y : C} (f : X ⟶ Y) [HasKernel f] (
hX : P X) (hY : P Y) : P (kernel f)
参数：f : X ⟶ Y；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit_kernelFork`：prop_of_isLimi
t_kernelFork [P.IsClosedUnderKernels] {X Y : C} {f : X ⟶ Y} {k : KernelFork f} (
hk : IsLimit k) (hX : P X) (hY : P Y) : P k.pt
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma prop_kernel [P.IsClosedUnderKernels] {X Y : C} (f : X ⟶ Y) [HasKernel f] (hX : P X)
    (hY : P Y) : P (kernel f) :=
  (P.prop_of_isLimit_kernelFork (kernelIsKernel f) hX hY :)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderSubobjects] : P.IsClosedUnderKernels where
  kernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    let := Fork.IsLimit.mono hk
    exact P.prop_of_mono k.ι hf.1
/-
**CategoryTheory.ObjectProperty.hasLimit_parallelPair_comp_** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLimit_parallelPair_comp_ι {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasKernel f.hom] :
    HasLimit (parallelPair f 0 ⋙ P.ι) :=
  hasLimit_of_iso (F := parallelPair f.hom 0) (Iso.symm (diagramIsoParallelPair _))

set_option backward.defeqAttrib.useBackward true in
/-- If an object property `P` is closed under kernels, then `P.ι` creates kernels.
In particular, this implies `P.ι` preserves kernels. -/
@[reducible]
/-
**CategoryTheory.ObjectProperty.createsKernels** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：createsKernels [P.IsClosedUnderKernels] {X Y : P.FullSubcategory} (f : X ⟶
 Y) [HasKernel f.hom] : CreatesLimit (parallelPair f 0) P.ι
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If an object property `P` is closed under kernels, then `P.ι` creates kernels.
In particular, this implies `P.ι` preserves kernels.
-/
noncomputable def createsKernels [P.IsClosedUnderKernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasKernel f.hom] : CreatesLimit (parallelPair f 0) P.ι := by
  fapply createsLimitFullSubcategoryInclusion'
  · exact (Cone.postcompose (Iso.symm (diagramIsoParallelPair _)).hom).obj
      (Fork.ofι (kernel.ι f.hom) (by simp))
  · exact (IsLimit.postcomposeInvEquiv _ _).symm (kernelIsKernel f.hom)
  · exact P.prop_kernel f.hom X.property Y.property
/-
**CategoryTheory.ObjectProperty.preservesKernels_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preservesKernels_ι [HasKernels C] [P.IsClosedUnderKernels] ⦃X Y : P.FullSubcategory⦄
    (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) P.ι := by
  have := P.createsKernels f
  have := P.hasLimit_parallelPair_comp_ι f
  exact preservesLimit_of_createsLimit_and_hasLimit _ _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderKernels] [HasKernels C] : HasKernels P.FullSubcategory where
  has_limit f :=
    letI := P.createsKernels f
    letI := P.hasLimit_parallelPair_comp_ι f
    hasLimit_of_created _ P.ι

/-- A property of objects satisfies `P.IsClosedUnderCokernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.IsClosedUnderCokernels** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [Ca
tegoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects satisfies `P.IsClosedUnderCokernels` if whenever `X` and `
Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`.
-/
class IsClosedUnderCokernels : Prop where
  cokernels_le : (MorphismProperty.ofObjectProperty P P).cokernels ≤ P
/-
**CategoryTheory.ObjectProperty.prop_of_isColimit_cokernelCofork** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_of_isColimit_cokernelCofork [P.IsClosedUnderCokernels] {X Y : C} {f :
 X ⟶ Y} {k : CokernelCofork f} (hk : IsColimit k) (hX : P X) (hY : P Y) : P k.pt
参数：hk : IsColimit k；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderCokernels.cokernels_le`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroMorphisms C}   {P : CategoryTheory.Obj…
-/
lemma prop_of_isColimit_cokernelCofork [P.IsClosedUnderCokernels] {X Y : C} {f : X ⟶ Y}
    {k : CokernelCofork f} (hk : IsColimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderCokernels.cokernels_le _ (.of_isColimit _ k hk ⟨hX, hY⟩)
/-
**CategoryTheory.ObjectProperty.prop_cokernel** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：prop_cokernel [P.IsClosedUnderCokernels] {X Y : C} (f : X ⟶ Y) [HasCokerne
l f] (hX : P X) (hY : P Y) : P (cokernel f)
参数：f : X ⟶ Y；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit_cokernelCofork`：prop_of_
isColimit_cokernelCofork [P.IsClosedUnderCokernels] {X Y : C} {f : X ⟶ Y} {k : C
okernelCofork f} (hk : IsColimit k) (hX : P X) (hY :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma prop_cokernel [P.IsClosedUnderCokernels] {X Y : C} (f : X ⟶ Y) [HasCokernel f] (hX : P X)
    (hY : P Y) : P (cokernel f) :=
  (P.prop_of_isColimit_cokernelCofork (cokernelIsCokernel f) hX hY :)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderQuotients] : P.IsClosedUnderCokernels where
  cokernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    let := Cofork.IsColimit.epi hk
    exact P.prop_of_epi k.π hf.2
/-
**CategoryTheory.ObjectProperty.hasColimit_parallelPair_comp_** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasColimit_parallelPair_comp_ι {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom] :
    HasColimit (parallelPair f 0 ⋙ P.ι) :=
  hasColimit_of_iso (F := parallelPair f.hom 0) (diagramIsoParallelPair _)

set_option backward.defeqAttrib.useBackward true in
/-- If an object property `P` is closed under cokernels, then `P.ι` creates cokernels.
In particular, this implies `P.ι` preserves cokernels. -/
@[reducible]
/-
**CategoryTheory.ObjectProperty.createsCokernels** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：createsCokernels [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory} (f :
 X ⟶ Y) [HasCokernel f.hom] : CreatesColimit (parallelPair f 0) P.ι
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If an object property `P` is closed under cokernels, then `P.ι` creates cokernel
s.
In particular, this implies `P.ι` preserves cokernels.
-/
noncomputable def createsCokernels [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasCokernel f.hom] : CreatesColimit (parallelPair f 0) P.ι := by
  fapply createsColimitFullSubcategoryInclusion'
  · exact (Cocone.precompose (diagramIsoParallelPair _).hom).obj
      (Cofork.ofπ (cokernel.π f.hom) (by simp))
  · exact (IsColimit.precomposeHomEquiv _ _).symm (cokernelIsCokernel f.hom)
  · exact P.prop_cokernel f.hom X.property Y.property
/-
**CategoryTheory.ObjectProperty.preservesCokernels_** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preservesCokernels_ι [HasCokernels C] [P.IsClosedUnderCokernels] ⦃X Y : P.FullSubcategory⦄
    (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) P.ι := by
  have := P.createsCokernels f
  have := P.hasColimit_parallelPair_comp_ι f
  exact preservesColimit_of_createsColimit_and_hasColimit _ _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderCokernels] [HasCokernels C] : HasCokernels P.FullSubcategory where
  has_colimit f :=
    letI := P.createsCokernels f
    letI := P.hasColimit_parallelPair_comp_ι f
    hasColimit_of_created _ P.ι

end ObjectProperty

end CategoryTheory

