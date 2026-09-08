/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# The class of isomorphisms modulo a Serre class

Let `C` be an abelian category and `P : ObjectProperty C` a Serre class.
We define `P.isoModSerre : MorphismProperty C`, which is the class of
morphisms `f` such that `kernel f` and `cokernel f` satisfy `P`.
We show that `P.isoModSerre` is multiplicative, satisfies the two out
of three property and is stable under retracts. (Similarly, we define
`P.monoModSerre` and `P.epiModSerre`.)

## TODO

* show that a localized category with respect to `P.isoModSerre` is abelian.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Limits ZeroObject MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of monomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` satisfies `P`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.ObjectProperty.monoModSerre** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：monoModSerre [P.IsSerreClass] : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of monomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` satisfies `P`.
-/
def monoModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (kernel f)

/-- The class of epimorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `cokernel f` satisfies `P`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.ObjectProperty.epiModSerre** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：epiModSerre [P.IsSerreClass] : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of epimorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `cokernel f` satisfies `P`.
-/
def epiModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (cokernel f)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.ObjectProperty.isoModSerre** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：isoModSerre [P.IsSerreClass] : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`.
-/
def isoModSerre [P.IsSerreClass] : MorphismProperty C :=
  P.monoModSerre ⊓ P.epiModSerre

variable [P.IsSerreClass]
/-
**CategoryTheory.ObjectProperty.monoModSerre_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：monoModSerre_iff {X Y : C} (f : X ⟶ Y) : P.monoModSerre f ↔ P (kernel f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma monoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.monoModSerre f ↔ P (kernel f) := Iff.rfl
/-
**CategoryTheory.ObjectProperty.monomorphisms_le_monoModSerre** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：monomorphisms_le_monoModSerre : monomorphisms C <= P.monoModSerre
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isZero`：prop_of_isZero [P.Contains
Zero] [P.IsClosedUnderIsomorphisms] {Z : C} (hZ : IsZero Z) : P Z
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toContainsZero`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C} 
  {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用引理 `CategoryTheory.Limits.isZero_kernel_of_mono`：isZero_kernel_of_mono {X Y 
: C} (f : X ⟶ Y) [Mono f] [HasKernel f] : IsZero (kernel f)
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
-/
lemma monomorphisms_le_monoModSerre : monomorphisms C ≤ P.monoModSerre :=
  fun _ _ f (_ : Mono f) ↦ P.prop_of_isZero (isZero_kernel_of_mono f)
/-
**CategoryTheory.ObjectProperty.monoModSerre_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：monoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : P.monoModSerre f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.monomorphisms_le_monoModSerre`：monomorphis
ms_le_monoModSerre : monomorphisms C <= P.monoModSerre
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.infer_property`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Categ
oryTheory.Mono f],   CategoryTheory.MorphismProper…
-/
lemma monoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.monoModSerre f :=
  P.monomorphisms_le_monoModSerre f (monomorphisms.infer_property f)
/-
**CategoryTheory.ObjectProperty.epiModSerre_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：epiModSerre_iff {X Y : C} (f : X ⟶ Y) : P.epiModSerre f ↔ P (cokernel f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma epiModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.epiModSerre f ↔ P (cokernel f) := Iff.rfl
/-
**CategoryTheory.ObjectProperty.epimorphisms_le_epiModSerre** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：epimorphisms_le_epiModSerre : epimorphisms C <= P.epiModSerre
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isZero`：prop_of_isZero [P.Contains
Zero] [P.IsClosedUnderIsomorphisms] {Z : C} (hZ : IsZero Z) : P Z
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toContainsZero`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C} 
  {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用引理 `CategoryTheory.Limits.isZero_cokernel_of_epi`：isZero_cokernel_of_epi {X 
Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] : IsZero (cokernel f)
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
-/
lemma epimorphisms_le_epiModSerre : epimorphisms C ≤ P.epiModSerre :=
  fun _ _ f (_ : Epi f) ↦ P.prop_of_isZero (isZero_cokernel_of_epi f)
/-
**CategoryTheory.ObjectProperty.epiModSerre_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：epiModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.epiModSerre f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.epimorphisms_le_epiModSerre`：epimorphisms_
le_epiModSerre : epimorphisms C <= P.epiModSerre
· 使用定理 `CategoryTheory.MorphismProperty.epimorphisms.infer_property`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Catego
ryTheory.Epi f],   CategoryTheory.MorphismPropert…
-/
lemma epiModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.epiModSerre f :=
  P.epimorphisms_le_epiModSerre f (epimorphisms.infer_property f)

@[simp]
/-
**CategoryTheory.ObjectProperty.epiModSerre_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：epiModSerre_zero_iff (X Y : C) : P.epiModSerre (0 : X ⟶ Y) ↔ P Y
参数：X Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
-/
lemma epiModSerre_zero_iff (X Y : C) :
    P.epiModSerre (0 : X ⟶ Y) ↔ P Y :=
  P.prop_iff_of_iso cokernelZeroIsoTarget

@[simp]
/-
**CategoryTheory.ObjectProperty.monoModSerre_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：monoModSerre_zero_iff (X Y : C) : P.monoModSerre (0 : X ⟶ Y) ↔ P X
参数：X Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
-/
lemma monoModSerre_zero_iff (X Y : C) :
    P.monoModSerre (0 : X ⟶ Y) ↔ P X :=
  P.prop_iff_of_iso kernelZeroIsoSource
/-
**CategoryTheory.ObjectProperty.isoModSerre_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：isoModSerre_iff {X Y : C} (f : X ⟶ Y) : P.isoModSerre f ↔ P.monoModSerre f
 ∧ P.epiModSerre f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f := Iff.rfl
/-
**CategoryTheory.ObjectProperty.isoModSerre_iff_of_mono** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : P.isoModSerre f ↔
 P.epiModSerre f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.monoModSerre_of_mono`：monoModSerre_of_mono
 {X Y : C} (f : X ⟶ Y) [Mono f] : P.monoModSerre f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff`：isoModSerre_iff {X Y : C}
 (f : X ⟶ Y) : P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f
-/
lemma isoModSerre_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.isoModSerre f ↔ P.epiModSerre f := by
  have := P.monoModSerre_of_mono f
  rw [isoModSerre_iff]
  tauto
/-
**CategoryTheory.ObjectProperty.isoModSerre_iff_of_epi** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.isoModSerre f ↔ P
.monoModSerre f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.epiModSerre_of_epi`：epiModSerre_of_epi {X 
Y : C} (f : X ⟶ Y) [Epi f] : P.epiModSerre f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff`：isoModSerre_iff {X Y : C}
 (f : X ⟶ Y) : P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f
-/
lemma isoModSerre_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.isoModSerre f ↔ P.monoModSerre f := by
  have := P.epiModSerre_of_epi f
  rw [isoModSerre_iff]
  tauto
/-
**CategoryTheory.ObjectProperty.isoModSerre_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P.epiModSerre f) 
: P.isoModSerre f
参数：f : X ⟶ Y；hf : P.epiModSerre f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff_of_mono`：isoModSerre_iff_o
f_mono {X Y : C} (f : X ⟶ Y) [Mono f] : P.isoModSerre f ↔ P.epiModSerre f
-/
lemma isoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P.epiModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_mono]
/-
**CategoryTheory.ObjectProperty.isoModSerre_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P.monoModSerre f) :
 P.isoModSerre f
参数：f : X ⟶ Y；hf : P.monoModSerre f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff_of_epi`：isoModSerre_iff_of
_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.isoModSerre f ↔ P.monoModSerre f
-/
lemma isoModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P.monoModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_epi]

@[simp]
/-
**CategoryTheory.ObjectProperty.isoModSerre_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_zero_iff (X Y : C) : P.isoModSerre (0 : X ⟶ Y) ↔ P X ∧ P Y
参数：X Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isoModSerre_zero_iff (X Y : C) :
    P.isoModSerre (0 : X ⟶ Y) ↔ P X ∧ P Y := by
  simp [isoModSerre_iff]
/-
**CategoryTheory.ObjectProperty.isomorphisms_le_isoModSerre** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isomorphisms_le_isoModSerre : isomorphisms C <= P.isoModSerre
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.monoModSerre_of_mono`：monoModSerre_of_mono
 {X Y : C} (f : X ⟶ Y) [Mono f] : P.monoModSerre f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用引理 `CategoryTheory.ObjectProperty.epiModSerre_of_epi`：epiModSerre_of_epi {X 
Y : C} (f : X ⟶ Y) [Epi f] : P.epiModSerre f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma isomorphisms_le_isoModSerre : isomorphisms C ≤ P.isoModSerre :=
  fun _ _ f (_ : IsIso f) ↦ ⟨P.monoModSerre_of_mono f, P.epiModSerre_of_epi f⟩
/-
**CategoryTheory.ObjectProperty.isoModSerre_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isoModSerre f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.isomorphisms_le_isoModSerre`：isomorphisms_
le_isoModSerre : isomorphisms C <= P.isoModSerre
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.infer_property`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Catego
ryTheory.IsIso f],   CategoryTheory.MorphismPrope…
-/
lemma isoModSerre_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isoModSerre f :=
  P.isomorphisms_le_isoModSerre f (isomorphisms.infer_property f)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.monoModSerre.IsMultiplicative where
  id_mem _ := P.monoModSerre_of_mono _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf hg
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.epiModSerre.IsMultiplicative where
  id_mem _ := P.epiModSerre_of_epi _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf hg
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.IsMultiplicative := by
  dsimp only [isoModSerre]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.monoModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.epiModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.IsStableUnderRetracts := by
  dsimp only [isoModSerre]
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg :=
    ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) hfg.2⟩
/-
**CategoryTheory.ObjectProperty.le_kernel_of_isoModSerre_isInvertedBy** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：le_kernel_of_isoModSerre_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphism
s] (hF : P.isoModSerre.IsInvertedBy F) : P <= F.kernel
参数：F : C ⥤ D；hF : P.isoModSerre.IsInvertedBy F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff_of_mono`：isoModSerre_iff_o
f_mono {X Y : C} (f : X ⟶ Y) [Mono f] : P.isoModSerre f ↔ P.epiModSerre f
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instMono`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
{X : C}   (f : 0 ⟶ X), CategoryThe…
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma le_kernel_of_isoModSerre_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : P.isoModSerre.IsInvertedBy F) :
    P ≤ F.kernel := by
  intro X hX
  let f : 0 ⟶ X := 0
  have := hF _ ((P.isoModSerre_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  exact (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))
/-
**CategoryTheory.ObjectProperty.isoModSerre_isInvertedBy_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isoModSerre_isInvertedBy_iff (F : C ⥤ D) [PreservesFiniteLimits F] [Preser
vesFiniteColimits F] : P.isoModSerre.IsInvertedBy F ↔ P <= F.kernel
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.le_kernel_of_isoModSerre_isInvertedBy`：le_
kernel_of_isoModSerre_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphisms] (hF : 
P.isoModSerre.IsInvertedBy F) : P <= F.kernel
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : C
ategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
-/
lemma isoModSerre_isInvertedBy_iff (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    P.isoModSerre.IsInvertedBy F ↔ P ≤ F.kernel := by
  refine ⟨P.le_kernel_of_isoModSerre_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ ↦ ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel f)).map F).epi_f (((hF _ h₂).eq_of_tgt _ _))
  exact isIso_of_mono_of_epi (F.map f)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.monoModSerre.IsStableUnderBaseChange where
  of_isPullback sq h :=
    have := isIso_kernel_map_of_isPullback sq.flip
    P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.w.symm)).symm h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.epiModSerre.IsStableUnderBaseChange where
  of_isPullback sq h :=
    have := Abelian.mono_cokernel_map_of_isPullback sq.flip
    P.prop_of_mono (cokernel.map _ _ _ _ sq.w.symm) h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.IsStableUnderBaseChange := by
  dsimp [isoModSerre]
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.monoModSerre.IsStableUnderCobaseChange where
  of_isPushout sq h :=
    have := Abelian.epi_kernel_map_of_isPushout sq.flip
    P.prop_of_epi (kernel.map _ _ _ _ sq.w.symm) h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.epiModSerre.IsStableUnderCobaseChange where
  of_isPushout sq h :=
    have := isIso_cokernel_map_of_isPushout sq.flip
    P.prop_of_iso (asIso (cokernel.map _ _ _ _ sq.w.symm)) h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.IsStableUnderCobaseChange := by
  dsimp [isoModSerre]
  infer_instance

end ObjectProperty

end CategoryTheory

