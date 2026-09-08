/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limit preservation properties of `Functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
preserve certain (co)limits and vice versa.

-/

public section


universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

/-- If `F : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesLimit_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：preservesLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] 
: PreservesLimit K F.op where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒ
ᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.op where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesLimit_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：preservesLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] 
: PreservesLimit K F where preserves {_} hc
参数：K : J ⥤ C；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D`
 preserves
limits of `K : J ⥤ C`.
-/
lemma preservesLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] :
    PreservesLimit K F where
  preserves {_} hc := ⟨isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesLimit_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：preservesLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.left
Op F] : PreservesLimit K F.leftOp where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒ
ᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesLimit_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op 
F.leftOp] : PreservesLimit K F where preserves {_} hc
参数：K : J ⥤ C；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ 
Dᵒᵖ` preserves
limits of `K : J ⥤ C`.
-/
lemma preservesLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))⟩

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesLimit_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：preservesLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F]
 : PreservesLimit K F.rightOp where preserves {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤
 Dᵒᵖ` preserves
limits of `K : J ⥤ C`.
-/
lemma preservesLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesLimit_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.
leftOp F.rightOp] : PreservesLimit K F where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F :
 Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesLimit_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：preservesLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] 
: PreservesLimit K F.unop where preserves {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ 
D` preserves
limits of `K : J ⥤ C`.
-/
lemma preservesLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)⟩

/-- If `F.unop : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesLimit_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：preservesLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.l
eftOp F.unop] : PreservesLimit K F where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ 
Dᵒᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : C ⥤ D` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesColimit_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：preservesColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] 
: PreservesColimit K F.op where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ`
 preserves
colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesColimit_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：preservesColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] 
: PreservesColimit K F where preserves {_} hc
参数：K : J ⥤ C；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` p
reserves
colimits of `K : J ⥤ C`.
-/
lemma preservesColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] :
    PreservesColimit K F where
  preserves {_} hc := ⟨isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesColimit_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.left
Op F] : PreservesColimit K F.leftOp where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ 
⥤ D` preserves
colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesColimit_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op 
F.leftOp] : PreservesColimit K F where preserves {_} hc
参数：K : J ⥤ C；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒ
ᵖ` preserves
colimits of `K : J ⥤ C`.
-/
lemma preservesColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))⟩

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesColimit_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F]
 : PreservesColimit K F.rightOp where preserves {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ D
ᵒᵖ` preserves
colimits of `K : J ⥤ C`.
-/
lemma preservesColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
preserves colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesColimit_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.
leftOp F.rightOp] : PreservesColimit K F where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ
 ⥤ D`
preserves colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.preservesColimit_unop** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：preservesColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] 
: PreservesColimit K F.unop where preserves {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D`
 preserves
colimits of `K : J ⥤ C`.
-/
lemma preservesColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)⟩

/-- If `F.unop : C ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.preservesColimit_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.l
eftOp F.unop] : PreservesColimit K F where preserves {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` p
reserves
colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma preservesColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/-- If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of
shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : P
reservesLimitsOfShape J F.op where preservesLimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_op`：preservesLimit_op (K : J ⥤ Cᵒᵖ)
 (F : C ⥤ D) [PreservesColimit K.leftOp F] : PreservesLimit K F.op where preserv
es {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preser
ves limits of
shape `J`.
-/
lemma preservesLimitsOfShape_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.op where preservesLimit {K} := preservesLimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_leftOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ 
F] : PreservesLimitsOfShape J F.leftOp where preservesLimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_leftOp`：preservesLimit_leftOp (K : 
J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] : PreservesLimit K F.leftOp
 where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` pr
eserves limits
of shape `J`.
-/
lemma preservesLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.leftOp where preservesLimit {K} := preservesLimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_rightOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ
 F] : PreservesLimitsOfShape J F.rightOp where preservesLimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_rightOp`：preservesLimit_rightOp (K 
: J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] : PreservesLimit K F.rightOp wh
ere preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` p
reserves limits
of shape `J`.
-/
lemma preservesLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.rightOp where preservesLimit {K} := preservesLimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves limits of
shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_unop** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ 
F] : PreservesLimitsOfShape J F.unop where preservesLimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_unop`：preservesLimit_unop (K : J ⥤ 
C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] : PreservesLimit K F.unop where pre
serves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` pres
erves limits of
shape `J`.
-/
lemma preservesLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.unop where preservesLimit {K} := preservesLimit_unop K F

/-- If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of
shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_op** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : P
reservesColimitsOfShape J F.op where preservesColimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_op`：preservesColimit_op (K : J ⥤ 
Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] : PreservesColimit K F.op where pre
serves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserve
s colimits of
shape `J`.
-/
lemma preservesColimitsOfShape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.op where preservesColimit {K} := preservesColimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_leftOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ 
F] : PreservesColimitsOfShape J F.leftOp where preservesColimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_leftOp`：preservesColimit_leftOp (
K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] : PreservesColimit K F.le
ftOp where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` pres
erves colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.leftOp where preservesColimit {K} := preservesColimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_rightOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ
 F] : PreservesColimitsOfShape J F.rightOp where preservesColimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_rightOp`：preservesColimit_rightOp
 (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] : PreservesColimit K F.rightO
p where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` pre
serves colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.rightOp where preservesColimit {K} := preservesColimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_unop** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ 
F] : PreservesColimitsOfShape J F.unop where preservesColimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_unop`：preservesColimit_unop (K : 
J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] : PreservesColimit K F.unop where
 preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preser
ves colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.unop where preservesColimit {K} := preservesColimit_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_op** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.o
p] : PreservesLimitsOfShape J F where preservesLimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_op`：preservesLimit_of_op (K : J 
⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] : PreservesLimit K F where preserv
es {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` preser
ves limits
of shape `J`.
-/
lemma preservesLimitsOfShape_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_leftOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape J
ᵒᵖ F.leftOp] : PreservesLimitsOfShape J F where preservesLimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_leftOp`：preservesLimit_of_leftOp
 (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp] : PreservesLimit K F
 where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` pr
eserves limits
of shape `J`.
-/
lemma preservesLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_rightOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape 
Jᵒᵖ F.rightOp] : PreservesLimitsOfShape J F where preservesLimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_rightOp`：preservesLimit_of_right
Op (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp] : Preserves
Limit K F where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` p
reserves limits
of shape `J`.
-/
lemma preservesLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_unop** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape J
ᵒᵖ F.unop] : PreservesLimitsOfShape J F where preservesLimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_unop`：preservesLimit_of_unop (K 
: J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop] : PreservesLimit K
 F where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` pres
erves limits
of shape `J`.
-/
lemma preservesLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_op** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.o
p] : PreservesColimitsOfShape J F where preservesColimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_op`：preservesColimit_of_op (K 
: J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] : PreservesColimit K F where pre
serves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserve
s colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_leftOp** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape J
ᵒᵖ F.leftOp] : PreservesColimitsOfShape J F where preservesColimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_leftOp`：preservesColimit_of_le
ftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp] : PreservesColimit
 K F where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` pres
erves colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_rightOp** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape 
Jᵒᵖ F.rightOp] : PreservesColimitsOfShape J F where preservesColimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_rightOp`：preservesColimit_of_r
ightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp] : Preserv
esColimit K F where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` pre
serves colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_unop** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape J
ᵒᵖ F.unop] : PreservesColimitsOfShape J F where preservesColimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_unop`：preservesColimit_of_unop
 (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop] : PreservesColim
it K F where preserves {_} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preser
ves colimits
of shape `J`.
-/
lemma preservesColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_unop K F

end

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_op** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
 PreservesLimitsOfSize.{w, w'} F.op where preservesLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_op`：preservesLimitsOfShape_
op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape J F.op 
where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits.
-/
lemma preservesLimitsOfSize_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'
} F] : PreservesLimitsOfSize.{w, w'} F.leftOp where preservesLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_leftOp`：preservesLimitsOfSh
ape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfSha
pe J F.leftOp where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits.
-/
lemma preservesLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_rightOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w
'} F] : PreservesLimitsOfSize.{w, w'} F.rightOp where preservesLimitsOfShape {_}
 _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_rightOp`：preservesLimitsOfS
hape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfS
hape J F.rightOp where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits
.
-/
lemma preservesLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_unop** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'
} F] : PreservesLimitsOfSize.{w, w'} F.unop where preservesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_unop`：preservesLimitsOfShap
e_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape
 J F.unop where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits.
-/
lemma preservesLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
 PreservesColimitsOfSize.{w, w'} F.op where preservesColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_op`：preservesColimitsOfSh
ape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfShape J F
.op where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits.
-/
lemma preservesColimitsOfSize_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_leftOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'
} F] : PreservesColimitsOfSize.{w, w'} F.leftOp where preservesColimitsOfShape {
_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_leftOp`：preservesColimits
OfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsO
fShape J F.leftOp where preservesColimit {K…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits.
-/
lemma preservesColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_rightOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w
'} F] : PreservesColimitsOfSize.{w, w'} F.rightOp where preservesColimitsOfShape
 {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_rightOp`：preservesColimit
sOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimit
sOfShape J F.rightOp where preservesColimit …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits
.
-/
lemma preservesColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_unop** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'
} F] : PreservesColimitsOfSize.{w, w'} F.unop where preservesColimitsOfShape {_}
 _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_unop`：preservesColimitsOf
Shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfS
hape J F.unop where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits.
-/
lemma preservesColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_of_op** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_of_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F
.op] : PreservesLimitsOfSize.{w, w'} F where preservesLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_op`：preservesLimitsOfSha
pe_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] : PreservesLimitsOfShap
e J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits.
-/
lemma preservesLimitsOfSize_of_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F.op] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_of_leftOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w,
 w'} F.leftOp] : PreservesLimitsOfSize.{w, w'} F where preservesLimitsOfShape {_
} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_leftOp`：preservesLimitsO
fShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] : Preserv
esLimitsOfShape J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits.
-/
lemma preservesLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.leftOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_of_rightOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w
, w'} F.rightOp] : PreservesLimitsOfSize.{w, w'} F where preservesLimitsOfShape 
{_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_rightOp`：preservesLimits
OfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] : Pres
ervesLimitsOfShape J F where preservesLimit {…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits
.
-/
lemma preservesLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F.rightOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_of_unop** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w,
 w'} F.unop] : PreservesLimitsOfSize.{w, w'} F where preservesLimitsOfShape {_} 
_
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_unop`：preservesLimitsOfS
hape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] : PreservesLi
mitsOfShape J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits.
-/
lemma preservesLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.unop] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_of_op** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_of_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F
.op] : PreservesColimitsOfSize.{w, w'} F where preservesColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_op`：preservesColimitsO
fShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] : PreservesColimitsOf
Shape J F where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits.
-/
lemma preservesColimitsOfSize_of_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F.op] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_of_leftOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w,
 w'} F.leftOp] : PreservesColimitsOfSize.{w, w'} F where preservesColimitsOfShap
e {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_leftOp`：preservesColim
itsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] : Prese
rvesColimitsOfShape J F where preservesColimit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits.
-/
lemma preservesColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.leftOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_of_rightOp** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w
, w'} F.rightOp] : PreservesColimitsOfSize.{w, w'} F where preservesColimitsOfSh
ape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_rightOp`：preservesColi
mitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] : Pr
eservesColimitsOfShape J F where preservesColim…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits
.
-/
lemma preservesColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F.rightOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_of_unop** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w,
 w'} F.unop] : PreservesColimitsOfSize.{w, w'} F where preservesColimitsOfShape 
{_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_unop`：preservesColimit
sOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] : Preserves
ColimitsOfShape J F where preservesColimit {…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits.
-/
lemma preservesColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.unop] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：preservesLimits_op (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.o
p where preservesLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_op`：preservesLimitsOfShape_
op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape J F.op 
where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits.
-/
lemma preservesLimits_op (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：preservesLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimi
ts F.leftOp where preservesLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_leftOp`：preservesLimitsOfSh
ape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfSha
pe J F.leftOp where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits.
-/
lemma preservesLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLim
its F.rightOp where preservesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_rightOp`：preservesLimitsOfS
hape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfS
hape J F.rightOp where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits
.
-/
lemma preservesLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLimits F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：preservesLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimi
ts F.unop where preservesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_unop`：preservesLimitsOfShap
e_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape
 J F.unop where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits.
-/
lemma preservesLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_op** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：preservesColimits_op (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F
.op where preservesColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_op`：preservesColimitsOfSh
ape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfShape J F
.op where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits.
-/
lemma preservesColimits_op (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColi
mits F.leftOp where preservesColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_leftOp`：preservesColimits
OfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsO
fShape J F.leftOp where preservesColimit {K…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits.
-/
lemma preservesColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] : PreservesCol
imits F.rightOp where preservesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_rightOp`：preservesColimit
sOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimit
sOfShape J F.rightOp where preservesColimit …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits
.
-/
lemma preservesColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] :
    PreservesColimits F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：preservesColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColi
mits F.unop where preservesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_unop`：preservesColimitsOf
Shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfS
hape J F.unop where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits.
-/
lemma preservesColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：preservesLimits_of_op (F : C ⥤ D) [PreservesColimits F.op] : PreservesLimi
ts F where preservesLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_op`：preservesLimitsOfSha
pe_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] : PreservesLimitsOfShap
e J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits.
-/
lemma preservesLimits_of_op (F : C ⥤ D) [PreservesColimits F.op] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp] : Pre
servesLimits F where preservesLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_leftOp`：preservesLimitsO
fShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] : Preserv
esLimitsOfShape J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits.
-/
lemma preservesLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp] : P
reservesLimits F where preservesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_rightOp`：preservesLimits
OfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] : Pres
ervesLimitsOfShape J F where preservesLimit {…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits
.
-/
lemma preservesLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp] :
    PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop] : Prese
rvesLimits F where preservesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_unop`：preservesLimitsOfS
hape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] : PreservesLi
mitsOfShape J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits.
-/
lemma preservesLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesColimits_of_op (F : C ⥤ D) [PreservesLimits F.op] : PreservesColi
mits F where preservesColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_op`：preservesColimitsO
fShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] : PreservesColimitsOf
Shape J F where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits.
-/
lemma preservesColimits_of_op (F : C ⥤ D) [PreservesLimits F.op] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp] : Pre
servesColimits F where preservesColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_leftOp`：preservesColim
itsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] : Prese
rvesColimitsOfShape J F where preservesColimit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits.
-/
lemma preservesColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp] : P
reservesColimits F where preservesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_rightOp`：preservesColi
mitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] : Pr
eservesColimitsOfShape J F where preservesColim…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits
.
-/
lemma preservesColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop] : Prese
rvesColimits F where preservesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_unop`：preservesColimit
sOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] : Preserves
ColimitsOfShape J F where preservesColimit {…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits.
-/
lemma preservesColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_op** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesFiniteLimits_op (F : C ⥤ D) [PreservesFiniteColimits F] : Preserv
esFiniteLimits F.op where preservesFiniteLimits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_op`：preservesLimitsOfShape_
op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape J F.op 
where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves fini
te
limits.
-/
lemma preservesFiniteLimits_op (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.op where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] : P
reservesFiniteLimits F.leftOp where preservesFiniteLimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_leftOp`：preservesLimitsOfSh
ape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfSha
pe J F.leftOp where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves 
finite
limits.
-/
lemma preservesFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] : 
PreservesFiniteLimits F.rightOp where preservesFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_rightOp`：preservesLimitsOfS
hape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfS
hape J F.rightOp where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
 finite
limits.
-/
lemma preservesFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] : P
reservesFiniteLimits F.unop where preservesFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_unop`：preservesLimitsOfShap
e_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape
 J F.unop where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves fi
nite
limits.
-/
lemma preservesFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_unop J F

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_op (F : C ⥤ D) [PreservesFiniteLimits F] : Preserv
esFiniteColimits F.op where preservesFiniteColimits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_op`：preservesColimitsOfSh
ape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfShape J F
.op where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
colimits.
-/
lemma preservesFiniteColimits_op (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.op where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] : P
reservesFiniteColimits F.leftOp where preservesFiniteColimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_leftOp`：preservesColimits
OfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsO
fShape J F.leftOp where preservesColimit {K…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves fi
nite
colimits.
-/
lemma preservesFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_rightOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] : 
PreservesFiniteColimits F.rightOp where preservesFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_rightOp`：preservesColimit
sOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimit
sOfShape J F.rightOp where preservesColimit …
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves f
inite
colimits.
-/
lemma preservesFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] : P
reservesFiniteColimits F.unop where preservesFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_unop`：preservesColimitsOf
Shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfS
hape J F.unop where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves fini
te
colimits.
-/
lemma preservesFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F : C ⥤ D` preserves finite limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_op (F : C ⥤ D) [PreservesFiniteColimits F.op] : P
reservesFiniteLimits F where preservesFiniteLimits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_op`：preservesLimitsOfSha
pe_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] : PreservesLimitsOfShap
e J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F : C ⥤ D` preserves fini
te limits.
-/
lemma preservesFiniteLimits_of_op (F : C ⥤ D) [PreservesFiniteColimits F.op] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite colimits, then `F : C ⥤ Dᵒᵖ` preserves finite
limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.l
eftOp] : PreservesFiniteLimits F where preservesFiniteLimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_leftOp`：preservesLimitsO
fShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] : Preserv
esLimitsOfShape J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite colimits, then `F : C ⥤ Dᵒᵖ` preserves 
finite
limits.
-/
lemma preservesFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.leftOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite colimits, then `F : Cᵒᵖ ⥤ D` preserves finite
limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_rightOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.
rightOp] : PreservesFiniteLimits F where preservesFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_rightOp`：preservesLimits
OfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] : Pres
ervesLimitsOfShape J F where preservesLimit {…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite colimits, then `F : Cᵒᵖ ⥤ D` preserves
 finite
limits.
-/
lemma preservesFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.rightOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` preserves finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.u
nop] : PreservesFiniteLimits F where preservesFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_unop`：preservesLimitsOfS
hape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] : PreservesLi
mitsOfShape J F where preservesLimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves fi
nite limits.
-/
lemma preservesFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.unop] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F : C ⥤ D` preserves finite colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_op (F : C ⥤ D) [PreservesFiniteLimits F.op] : P
reservesFiniteColimits F where preservesFiniteColimits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_op`：preservesColimitsO
fShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] : PreservesColimitsOf
Shape J F where preservesColimit {K}
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F : C ⥤ D` preserves finite
 colimits.
-/
lemma preservesFiniteColimits_of_op (F : C ⥤ D) [PreservesFiniteLimits F.op] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite limits, then `F : C ⥤ Dᵒᵖ` preserves finite
colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_leftOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.l
eftOp] : PreservesFiniteColimits F where preservesFiniteColimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_leftOp`：preservesColim
itsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] : Prese
rvesColimitsOfShape J F where preservesColimit…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite limits, then `F : C ⥤ Dᵒᵖ` preserves fi
nite
colimits.
-/
lemma preservesFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.leftOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite limits, then `F : Cᵒᵖ ⥤ D` preserves finite
colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_rightOp** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.
rightOp] : PreservesFiniteColimits F where preservesFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_rightOp`：preservesColi
mitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] : Pr
eservesColimitsOfShape J F where preservesColim…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite limits, then `F : Cᵒᵖ ⥤ D` preserves f
inite
colimits.
-/
lemma preservesFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.rightOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` preserves finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_unop** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.u
nop] : PreservesFiniteColimits F where preservesFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_unop`：preservesColimit
sOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] : Preserves
ColimitsOfShape J F where preservesColimit {…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` preserves finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves fini
te colimits.
-/
lemma preservesFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.unop] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_unop J F

/-- If `F : C ⥤ D` preserves finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
products. -/
/-
**CategoryTheory.Limits.preservesFiniteProducts_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesFiniteProducts_op (F : C ⥤ D) [PreservesFiniteCoproducts F] : Pre
servesFiniteProducts F.op where preserves n
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_op`：preservesLimitsOfShape_
op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape J F.op 
where preservesLimit {K}
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ D` preserves finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves fi
nite
products.
-/
lemma preservesFiniteProducts_op (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.op where
  preserves n := by
    apply +allowSynthFailures preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
products. -/
/-
**CategoryTheory.Limits.preservesFiniteProducts_leftOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F]
 : PreservesFiniteProducts F.leftOp where preserves _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_leftOp`：preservesLimitsOfSh
ape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfSha
pe J F.leftOp where preservesLimit {K}
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` preserve
s finite
products.
-/
lemma preservesFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
products. -/
/-
**CategoryTheory.Limits.preservesFiniteProducts_rightOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F
] : PreservesFiniteProducts F.rightOp where preserves _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_rightOp`：preservesLimitsOfS
hape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfS
hape J F.rightOp where preservesLimit {K}
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` preserv
es finite
products.
-/
lemma preservesFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite coproducts, then `F.unop : C ⥤ D` preserves finite
products. -/
/-
**CategoryTheory.Limits.preservesFiniteProducts_unop** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F]
 : PreservesFiniteProducts F.unop where preserves _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_unop`：preservesLimitsOfShap
e_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] : PreservesLimitsOfShape
 J F.unop where preservesLimit {K}
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite coproducts, then `F.unop : C ⥤ D` preserves 
finite
products.
-/
lemma preservesFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` preserves finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
coproducts. -/
/-
**CategoryTheory.Limits.preservesFiniteCoproducts_op** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesFiniteCoproducts_op (F : C ⥤ D) [PreservesFiniteProducts F] : Pre
servesFiniteCoproducts F.op where preserves _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_op`：preservesColimitsOfSh
ape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfShape J F
.op where preservesColimit {K}
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ D` preserves finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves fini
te
coproducts.
-/
lemma preservesFiniteCoproducts_op (F : C ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.op where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite products, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
coproducts. -/
/-
**CategoryTheory.Limits.preservesFiniteCoproducts_leftOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F]
 : PreservesFiniteCoproducts F.leftOp where preserves _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_leftOp`：preservesColimits
OfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsO
fShape J F.leftOp where preservesColimit {K…
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` preserves finite products, then `F.leftOp : Cᵒᵖ ⥤ D` preserves 
finite
coproducts.
-/
lemma preservesFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite products, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
coproducts. -/
/-
**CategoryTheory.Limits.preservesFiniteCoproducts_rightOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F
] : PreservesFiniteCoproducts F.rightOp where preserves _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_rightOp`：preservesColimit
sOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimit
sOfShape J F.rightOp where preservesColimit …
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` preserves finite products, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
 finite
coproducts.
-/
lemma preservesFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite products, then `F.unop : C ⥤ D` preserves finite
coproducts. -/
/-
**CategoryTheory.Limits.preservesFiniteCoproducts_unop** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F]
 : PreservesFiniteCoproducts F.unop where preserves _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_unop`：preservesColimitsOf
Shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] : PreservesColimitsOfS
hape J F.unop where preservesColimit {K}
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite products, then `F.unop : C ⥤ D` preserves fi
nite
coproducts.
-/
lemma preservesFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsLimit_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：reflectsLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsColimit K.leftOp F] : 
ReflectsLimit K F.op where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ
` reflects
limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.op where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ <| isColimitOfReflects F (isColimitCoconeLeftOpOfCone _ hc)⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` reflects
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsLimit_of_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：reflectsLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsColimit K.op F.op] : 
ReflectsLimit K F where reflects {_} hc
参数：K : J ⥤ C；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` 
reflects
limits of `K : J ⥤ C`.
-/
lemma reflectsLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsColimit K.op F.op] :
    ReflectsLimit K F where
  reflects {_} hc := ⟨isLimitOfOp (isColimitOfReflects F.op (IsLimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
reflects limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsLimit_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：reflectsLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp
 F] : ReflectsLimit K F.leftOp where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ
 ⥤ D`
reflects limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.leftOp where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ <| isColimitOfReflects F hc.op⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsLimit_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.op F.
leftOp] : ReflectsLimit K F where reflects {_} hc
参数：K : J ⥤ C；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D
ᵒᵖ` reflects
limits of `K : J ⥤ C`.
-/
lemma reflectsLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.op F.leftOp] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfOp <|
      isColimitOfReflects F.leftOp (isColimitOfConeRightOpOfCocone _ hc)⟩

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsLimit_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：reflectsLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.op F] :
 ReflectsLimit K F.rightOp where reflects {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ 
Dᵒᵖ` reflects
limits of `K : J ⥤ C`.
-/
lemma reflectsLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.op F] :
    ReflectsLimit K F.rightOp where
  reflects {_} hc :=
    ⟨isLimitOfOp <| isColimitOfReflects F <| isColimitOfConeRightOpOfCocone _ hc⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
reflects limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsLimit_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：reflectsLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.le
ftOp F.rightOp] : ReflectsLimit K F where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : 
Cᵒᵖ ⥤ D`
reflects limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.leftOp F.rightOp] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ <| isColimitOfReflects F.rightOp <|
      isColimitOfConeUnopOfCocone _ hc⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` reflects
limits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsLimit_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：reflectsLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.op F] : 
ReflectsLimit K F.unop where reflects {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D
` reflects
limits of `K : J ⥤ C`.
-/
lemma reflectsLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.op F] :
    ReflectsLimit K F.unop where
  reflects {_} hc := ⟨isLimitOfOp (isColimitOfReflects F hc.op)⟩

/-- If `F.unop : C ⥤ D` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsLimit_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：reflectsLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.lef
tOp F.unop] : ReflectsLimit K F where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D
ᵒᵖ` reflects
limits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F.unop] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfReflects F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : C ⥤ D` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsColimit_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：reflectsColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsLimit K.leftOp F] : 
ReflectsColimit K F.op where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` 
reflects
colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsLimit K.leftOp F] :
    ReflectsColimit K F.op where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` reflects
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsColimit_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：reflectsColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsLimit K.op F.op] : 
ReflectsColimit K F where reflects {_} hc
参数：K : J ⥤ C；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` re
flects
colimits of `K : J ⥤ C`.
-/
lemma reflectsColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsLimit K.op F.op] :
    ReflectsColimit K F where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F.op (IsColimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` reflects
colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsColimit_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：reflectsColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp
 F] : ReflectsColimit K F.leftOp where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤
 D` reflects
colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F] :
    ReflectsColimit K F.leftOp where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitOfCoconeUnopOfCone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsColimit_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.op F.
leftOp] : ReflectsColimit K F where reflects {_} hc
参数：K : J ⥤ C；F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ
` reflects
colimits of `K : J ⥤ C`.
-/
lemma reflectsColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.op F.leftOp] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfOp (isLimitOfReflects F.leftOp <| isLimitOfCoconeRightOpOfCone _ hc)⟩

/-- If `F : Cᵒᵖ ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsColimit_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.op F] :
 ReflectsColimit K F.rightOp where reflects {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒ
ᵖ` reflects
colimits of `K : J ⥤ C`.
-/
lemma reflectsColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.op F] :
    ReflectsColimit K F.rightOp where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F <| isLimitOfCoconeRightOpOfCone _ hc)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
reflects colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsColimit_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.le
ftOp F.rightOp] : ReflectsColimit K F where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ 
⥤ D`
reflects colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.leftOp F.rightOp] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.rightOp hc.op)⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` reflects
colimits of `K : J ⥤ C`. -/
/-
**CategoryTheory.Limits.reflectsColimit_unop** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：reflectsColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F] : 
ReflectsColimit K F.unop where reflects {_} hc
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` 
reflects
colimits of `K : J ⥤ C`.
-/
lemma reflectsColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F] :
    ReflectsColimit K F.unop where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F hc.op)⟩

/-- If `F.unop : C ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.reflectsColimit_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.lef
tOp F.unop] : ReflectsColimit K F where reflects {_} hc
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` re
flects
colimits of `K : J ⥤ Cᵒᵖ`.
-/
lemma reflectsColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F.unop] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/-- If `F : C ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of
shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_op** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : Ref
lectsLimitsOfShape J F.op where reflectsLimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_op`：reflectsLimit_op (K : J ⥤ Cᵒᵖ) (
F : C ⥤ D) [ReflectsColimit K.leftOp F] : ReflectsLimit K F.op where reflects {_
} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : C ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflect
s limits of
shape `J`.
-/
lemma reflectsLimitsOfShape_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.op where reflectsLimit {K} := reflectsLimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F]
 : ReflectsLimitsOfShape J F.leftOp where reflectsLimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_leftOp`：reflectsLimit_leftOp (K : J 
⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F] : ReflectsLimit K F.leftOp whe
re reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` ref
lects limits
of shape `J`.
-/
lemma reflectsLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.leftOp where reflectsLimit {K} := reflectsLimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_rightOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F
] : ReflectsLimitsOfShape J F.rightOp where reflectsLimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_rightOp`：reflectsLimit_rightOp (K : 
J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.op F] : ReflectsLimit K F.rightOp where 
reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` re
flects limits
of shape `J`.
-/
lemma reflectsLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.rightOp where reflectsLimit {K} := reflectsLimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` reflects limits of
shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_unop** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F]
 : ReflectsLimitsOfShape J F.unop where reflectsLimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_unop`：reflectsLimit_unop (K : J ⥤ C)
 (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.op F] : ReflectsLimit K F.unop where reflect
s {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` refle
cts limits of
shape `J`.
-/
lemma reflectsLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.unop where reflectsLimit {K} := reflectsLimit_unop K F

/-- If `F : C ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of
shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : Ref
lectsColimitsOfShape J F.op where reflectsColimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_op`：reflectsColimit_op (K : J ⥤ Cᵒ
ᵖ) (F : C ⥤ D) [ReflectsLimit K.leftOp F] : ReflectsColimit K F.op where reflect
s {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : C ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects 
colimits of
shape `J`.
-/
lemma reflectsColimitsOfShape_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.op where reflectsColimit {K} := reflectsColimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_leftOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F]
 : ReflectsColimitsOfShape J F.leftOp where reflectsColimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_leftOp`：reflectsColimit_leftOp (K 
: J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F] : ReflectsColimit K F.leftOp
 where reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` refle
cts colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.leftOp where reflectsColimit {K} := reflectsColimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_rightOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F
] : ReflectsColimitsOfShape J F.rightOp where reflectsColimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_rightOp`：reflectsColimit_rightOp (
K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.op F] : ReflectsColimit K F.rightOp wh
ere reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` refl
ects colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.rightOp where reflectsColimit {K} := reflectsColimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_unop** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F]
 : ReflectsColimitsOfShape J F.unop where reflectsColimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_unop`：reflectsColimit_unop (K : J 
⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F] : ReflectsColimit K F.unop where ref
lects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` reflect
s colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.unop where reflectsColimit {K} := reflectsColimit_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` reflects limits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_op** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op]
 : ReflectsLimitsOfShape J F where reflectsLimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_op`：reflectsLimit_of_op (K : J ⥤ 
C) (F : C ⥤ D) [ReflectsColimit K.op F.op] : ReflectsLimit K F where reflects {_
} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` reflect
s limits
of shape `J`.
-/
lemma reflectsLimitsOfShape_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects limits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_leftOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ
 F.leftOp] : ReflectsLimitsOfShape J F where reflectsLimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_leftOp`：reflectsLimit_of_leftOp (
K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.op F.leftOp] : ReflectsLimit K F whe
re reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` ref
lects limits
of shape `J`.
-/
lemma reflectsLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` reflects limits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_rightOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒ
ᵖ F.rightOp] : ReflectsLimitsOfShape J F where reflectsLimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_rightOp`：reflectsLimit_of_rightOp
 (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.leftOp F.rightOp] : ReflectsLimi
t K F where reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` re
flects limits
of shape `J`.
-/
lemma reflectsLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_unop** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ
 F.unop] : ReflectsLimitsOfShape J F where reflectsLimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_unop`：reflectsLimit_of_unop (K : 
J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F.unop] : ReflectsLimit K F w
here reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` refle
cts limits
of shape `J`.
-/
lemma reflectsLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F : C ⥤ D` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_op** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op]
 : ReflectsColimitsOfShape J F where reflectsColimit {K}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_op`：reflectsColimit_of_op (K : 
J ⥤ C) (F : C ⥤ D) [ReflectsLimit K.op F.op] : ReflectsColimit K F where reflect
s {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F : C ⥤ D` reflects 
colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_leftOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ
 F.leftOp] : ReflectsColimitsOfShape J F where reflectsColimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_leftOp`：reflectsColimit_of_left
Op (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.op F.leftOp] : ReflectsColimit K F
 where reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` refle
cts colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_rightOp** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒ
ᵖ F.rightOp] : ReflectsColimitsOfShape J F where reflectsColimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_rightOp`：reflectsColimit_of_rig
htOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.leftOp F.rightOp] : ReflectsCo
limit K F where reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` refl
ects colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits
of shape `J`. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_unop** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ
 F.unop] : ReflectsColimitsOfShape J F where reflectsColimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_unop`：reflectsColimit_of_unop (
K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F.unop] : ReflectsColimit K
 F where reflects {_} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflect
s colimits
of shape `J`.
-/
lemma reflectsColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_unop K F

end

/-- If `F : C ⥤ D` reflects colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_op** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] : R
eflectsLimitsOfSize.{w, w'} F.op where reflectsLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_op`：reflectsLimitsOfShape_op
 (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F.op wher
e reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ D` reflects colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimitsOfSize_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.op where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} 
F] : ReflectsLimitsOfSize.{w, w'} F.leftOp where reflectsLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_leftOp`：reflectsLimitsOfShap
e_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J
 F.leftOp where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits.
-/
lemma reflectsLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.leftOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'}
 F] : ReflectsLimitsOfSize.{w, w'} F.rightOp where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_rightOp`：reflectsLimitsOfSha
pe_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape
 J F.rightOp where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.rightOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F.unop : C ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_unop** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} 
F] : ReflectsLimitsOfSize.{w, w'} F.unop where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_unop`：reflectsLimitsOfShape_
unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F
.unop where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F.unop : C ⥤ D` reflects limits.
-/
lemma reflectsLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.unop where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` reflects limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] : R
eflectsColimitsOfSize.{w, w'} F.op where reflectsColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_op`：reflectsColimitsOfShap
e_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape J F.op 
where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ D` reflects limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimitsOfSize_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.op where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_leftOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} 
F] : ReflectsColimitsOfSize.{w, w'} F.leftOp where reflectsColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_leftOp`：reflectsColimitsOf
Shape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfSha
pe J F.leftOp where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits.
-/
lemma reflectsColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.leftOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_rightOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'}
 F] : ReflectsColimitsOfSize.{w, w'} F.rightOp where reflectsColimitsOfShape {_}
 _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_rightOp`：reflectsColimitsO
fShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfS
hape J F.rightOp where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.rightOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F.unop : C ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_unop** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} 
F] : ReflectsColimitsOfSize.{w, w'} F.unop where reflectsColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_unop`：reflectsColimitsOfSh
ape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape
 J F.unop where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F.unop : C ⥤ D` reflects colimits.
-/
lemma reflectsColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.unop where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F : C ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_of_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.o
p] : ReflectsLimitsOfSize.{w, w'} F where reflectsLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_op`：reflectsLimitsOfShape
_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op] : ReflectsLimitsOfShape J 
F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F : C ⥤ D` reflects limits.
-/
lemma reflectsLimitsOfSize_of_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.op] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits, then `F : C ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w
'} F.leftOp] : ReflectsLimitsOfSize.{w, w'} F where reflectsLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_leftOp`：reflectsLimitsOfS
hape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp] : ReflectsLi
mitsOfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits, then `F : C ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.leftOp] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits, then `F : Cᵒᵖ ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_of_rightOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, 
w'} F.rightOp] : ReflectsLimitsOfSize.{w, w'} F where reflectsLimitsOfShape {_} 
_
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_rightOp`：reflectsLimitsOf
Shape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp] : Reflect
sLimitsOfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits, then `F : Cᵒᵖ ⥤ D` reflects limits.
-/
lemma reflectsLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.rightOp] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w
'} F.unop] : ReflectsLimitsOfSize.{w, w'} F where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_unop`：reflectsLimitsOfSha
pe_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop] : ReflectsLimits
OfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.unop] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F : C ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_of_op** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_of_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.o
p] : ReflectsColimitsOfSize.{w, w'} F where reflectsColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_op`：reflectsColimitsOfS
hape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op] : ReflectsColimitsOfShap
e J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F : C ⥤ D` reflects colimits.
-/
lemma reflectsColimitsOfSize_of_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.op] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits, then `F : C ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_of_leftOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w
'} F.leftOp] : ReflectsColimitsOfSize.{w, w'} F where reflectsColimitsOfShape {_
} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_leftOp`：reflectsColimit
sOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp] : Reflects
ColimitsOfShape J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits, then `F : C ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.leftOp] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits, then `F : Cᵒᵖ ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_of_rightOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, 
w'} F.rightOp] : ReflectsColimitsOfSize.{w, w'} F where reflectsColimitsOfShape 
{_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_rightOp`：reflectsColimi
tsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp] : Refle
ctsColimitsOfShape J F where reflectsColimit {…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits, then `F : Cᵒᵖ ⥤ D` reflects colimits.
-/
lemma reflectsColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.rightOp] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_of_unop** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w
'} F.unop] : ReflectsColimitsOfSize.{w, w'} F where reflectsColimitsOfShape {_} 
_
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_unop`：reflectsColimitsO
fShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop] : ReflectsColi
mitsOfShape J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.unop] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` reflects colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：reflectsLimits_op (F : C ⥤ D) [ReflectsColimits F] : ReflectsLimits F.op w
here reflectsLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_op`：reflectsLimitsOfShape_op
 (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F.op wher
e reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ D` reflects colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimits_op (F : C ⥤ D) [ReflectsColimits F] : ReflectsLimits F.op where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：reflectsLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits 
F.leftOp where reflectsLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_leftOp`：reflectsLimitsOfShap
e_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J
 F.leftOp where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits.
-/
lemma reflectsLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits F.leftOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：reflectsLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F] : ReflectsLimits
 F.rightOp where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_rightOp`：reflectsLimitsOfSha
pe_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape
 J F.rightOp where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F] : ReflectsLimits F.rightOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F.unop : C ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：reflectsLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits 
F.unop where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_unop`：reflectsLimitsOfShape_
unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F
.unop where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F.unop : C ⥤ D` reflects limits.
-/
lemma reflectsLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits F.unop where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` reflects limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：reflectsColimits_op (F : C ⥤ D) [ReflectsLimits F] : ReflectsColimits F.op
 where reflectsColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_op`：reflectsColimitsOfShap
e_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape J F.op 
where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ D` reflects limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimits_op (F : C ⥤ D) [ReflectsLimits F] : ReflectsColimits F.op where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimit
s F.leftOp where reflectsColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_leftOp`：reflectsColimitsOf
Shape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfSha
pe J F.leftOp where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits.
-/
lemma reflectsColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimits F.leftOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：reflectsColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F] : ReflectsColimi
ts F.rightOp where reflectsColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_rightOp`：reflectsColimitsO
fShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfS
hape J F.rightOp where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F] :
    ReflectsColimits F.rightOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F.unop : C ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：reflectsColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimit
s F.unop where reflectsColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_unop`：reflectsColimitsOfSh
ape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape
 J F.unop where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F.unop : C ⥤ D` reflects colimits.
-/
lemma reflectsColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimits F.unop where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F : C ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：reflectsLimits_of_op (F : C ⥤ D) [ReflectsColimits F.op] : ReflectsLimits 
F where reflectsLimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_op`：reflectsLimitsOfShape
_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op] : ReflectsLimitsOfShape J 
F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F : C ⥤ D` reflects limits.
-/
lemma reflectsLimits_of_op (F : C ⥤ D) [ReflectsColimits F.op] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits, then `F : C ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：reflectsLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F.leftOp] : Refle
ctsLimits F where reflectsLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_leftOp`：reflectsLimitsOfS
hape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp] : ReflectsLi
mitsOfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits, then `F : C ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F.leftOp] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits, then `F : Cᵒᵖ ⥤ D` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F.rightOp] : Ref
lectsLimits F where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_rightOp`：reflectsLimitsOf
Shape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp] : Reflect
sLimitsOfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits, then `F : Cᵒᵖ ⥤ D` reflects limits.
-/
lemma reflectsLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F.rightOp] :
    ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
/-
**CategoryTheory.Limits.reflectsLimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：reflectsLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F.unop] : Reflect
sLimits F where reflectsLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_unop`：reflectsLimitsOfSha
pe_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop] : ReflectsLimits
OfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits.
-/
lemma reflectsLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F.unop] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F : C ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：reflectsColimits_of_op (F : C ⥤ D) [ReflectsLimits F.op] : ReflectsColimit
s F where reflectsColimitsOfShape {_} _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_op`：reflectsColimitsOfS
hape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op] : ReflectsColimitsOfShap
e J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F : C ⥤ D` reflects colimits.
-/
lemma reflectsColimits_of_op (F : C ⥤ D) [ReflectsLimits F.op] : ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits, then `F : C ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F.leftOp] : Refle
ctsColimits F where reflectsColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_leftOp`：reflectsColimit
sOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp] : Reflects
ColimitsOfShape J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits, then `F : C ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F.leftOp] :
    ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits, then `F : Cᵒᵖ ⥤ D` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_of_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F.rightOp] : Ref
lectsColimits F where reflectsColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_rightOp`：reflectsColimi
tsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp] : Refle
ctsColimitsOfShape J F where reflectsColimit {…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits, then `F : Cᵒᵖ ⥤ D` reflects colimits.
-/
lemma reflectsColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F.rightOp] :
    ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
/-
**CategoryTheory.Limits.reflectsColimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：reflectsColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F.unop] : Reflect
sColimits F where reflectsColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_unop`：reflectsColimitsO
fShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop] : ReflectsColi
mitsOfShape J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits.
-/
lemma reflectsColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F.unop] : ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` reflects finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_op** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_op (F : C ⥤ D) [ReflectsFiniteColimits F] : ReflectsF
initeLimits F.op where reflects J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_op`：reflectsLimitsOfShape_op
 (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F.op wher
e reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` reflects finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
limits.
-/
lemma reflectsFiniteLimits_op (F : C ⥤ D) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.op where
  reflects J _ _ := reflectsLimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` reflects finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] : Ref
lectsFiniteLimits F.leftOp where reflects J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_leftOp`：reflectsLimitsOfShap
e_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J
 F.leftOp where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects fi
nite
limits.
-/
lemma reflectsFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.leftOp where
  reflects J _ _ := reflectsLimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` reflects finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F] : Re
flectsFiniteLimits F.rightOp where reflects J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_rightOp`：reflectsLimitsOfSha
pe_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape
 J F.rightOp where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects f
inite
limits.
-/
lemma reflectsFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.rightOp where
  reflects J _ _ := reflectsLimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits, then `F.unop : C ⥤ D` reflects finite
limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] : Ref
lectsFiniteLimits F.unop where reflects J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_unop`：reflectsLimitsOfShape_
unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F
.unop where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits, then `F.unop : C ⥤ D` reflects fini
te
limits.
-/
lemma reflectsFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.unop where
  reflects J _ _ := reflectsLimitsOfShape_unop J F

/-- If `F : C ⥤ D` reflects finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_op (F : C ⥤ D) [ReflectsFiniteLimits F] : ReflectsF
initeColimits F.op where reflects J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_op`：reflectsColimitsOfShap
e_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape J F.op 
where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` reflects finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
colimits.
-/
lemma reflectsFiniteColimits_op (F : C ⥤ D) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.op where
  reflects J _ _ := reflectsColimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` reflects finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_leftOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] : Ref
lectsFiniteColimits F.leftOp where reflects J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_leftOp`：reflectsColimitsOf
Shape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfSha
pe J F.leftOp where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects fini
te
colimits.
-/
lemma reflectsFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.leftOp where
  reflects J _ _ := reflectsColimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` reflects finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_rightOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F] : Re
flectsFiniteColimits F.rightOp where reflects J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_rightOp`：reflectsColimitsO
fShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfS
hape J F.rightOp where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects fin
ite
colimits.
-/
lemma reflectsFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.rightOp where
  reflects J _ _ := reflectsColimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits, then `F.unop : C ⥤ D` reflects finite
colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_unop** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] : Ref
lectsFiniteColimits F.unop where reflects J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_unop`：reflectsColimitsOfSh
ape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape
 J F.unop where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits, then `F.unop : C ⥤ D` reflects finite
colimits.
-/
lemma reflectsFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.unop where
  reflects J _ _ := reflectsColimitsOfShape_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits, then `F : C ⥤ D` reflects finite limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_of_op (F : C ⥤ D) [ReflectsFiniteColimits F.op] : Ref
lectsFiniteLimits F where reflects J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_op`：reflectsLimitsOfShape
_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op] : ReflectsLimitsOfShape J 
F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits, then `F : C ⥤ D` reflects finite
 limits.
-/
lemma reflectsFiniteLimits_of_op (F : C ⥤ D) [ReflectsFiniteColimits F.op] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects finite colimits, then `F : C ⥤ Dᵒᵖ` reflects finite
limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.lef
tOp] : ReflectsFiniteLimits F where reflects J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_leftOp`：reflectsLimitsOfS
hape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp] : ReflectsLi
mitsOfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects finite colimits, then `F : C ⥤ Dᵒᵖ` reflects fi
nite
limits.
-/
lemma reflectsFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.leftOp] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects finite colimits, then `F : Cᵒᵖ ⥤ D` reflects finite
limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_of_rightOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F.ri
ghtOp] : ReflectsFiniteLimits F where reflects J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_rightOp`：reflectsLimitsOf
Shape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp] : Reflect
sLimitsOfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects finite colimits, then `F : Cᵒᵖ ⥤ D` reflects f
inite
limits.
-/
lemma reflectsFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F.rightOp] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` reflects finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits. -/
/-
**CategoryTheory.Limits.reflectsFiniteLimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.uno
p] : ReflectsFiniteLimits F where reflects J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_unop`：reflectsLimitsOfSha
pe_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop] : ReflectsLimits
OfShape J F where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects fini
te limits.
-/
lemma reflectsFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.unop] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits, then `F : C ⥤ D` reflects finite colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_of_op** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_of_op (F : C ⥤ D) [ReflectsFiniteLimits F.op] : Ref
lectsFiniteColimits F where reflects J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_op`：reflectsColimitsOfS
hape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op] : ReflectsColimitsOfShap
e J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits, then `F : C ⥤ D` reflects finite c
olimits.
-/
lemma reflectsFiniteColimits_of_op (F : C ⥤ D) [ReflectsFiniteLimits F.op] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects finite limits, then `F : C ⥤ Dᵒᵖ` reflects finite
colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_of_leftOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.lef
tOp] : ReflectsFiniteColimits F where reflects J _ _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_leftOp`：reflectsColimit
sOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp] : Reflects
ColimitsOfShape J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` reflects finite limits, then `F : C ⥤ Dᵒᵖ` reflects fini
te
colimits.
-/
lemma reflectsFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.leftOp] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects finite limits, then `F : Cᵒᵖ ⥤ D` reflects finite
colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_of_rightOp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F.ri
ghtOp] : ReflectsFiniteColimits F where reflects J _ _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_rightOp`：reflectsColimi
tsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp] : Refle
ctsColimitsOfShape J F where reflectsColimit {…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` reflects finite limits, then `F : Cᵒᵖ ⥤ D` reflects fin
ite
colimits.
-/
lemma reflectsFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F.rightOp] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` reflects finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits. -/
/-
**CategoryTheory.Limits.reflectsFiniteColimits_of_unop** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.uno
p] : ReflectsFiniteColimits F where reflects J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_unop`：reflectsColimitsO
fShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop] : ReflectsColi
mitsOfShape J F where reflectsColimit {K}
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F.unop : C ⥤ D` reflects finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
 colimits.
-/
lemma reflectsFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.unop] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_unop J F

/-- If `F : C ⥤ D` reflects finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
products. -/
/-
**CategoryTheory.Limits.reflectsFiniteProducts_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsFiniteProducts_op (F : C ⥤ D) [ReflectsFiniteCoproducts F] : Refle
ctsFiniteProducts F.op where reflects n
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_op`：reflectsLimitsOfShape_op
 (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F.op wher
e reflectsLimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `CategoryTheory.Limits.instReflectsColimitsOfShapeDiscreteOfReflectsFinit
eCoproductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C]
 {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheo
r…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ D` reflects finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects fini
te
products.
-/
lemma reflectsFiniteProducts_op (F : C ⥤ D) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.op where
  reflects n := by
    apply +allowSynthFailures reflectsLimitsOfShape_op
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` reflects finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
products. -/
/-
**CategoryTheory.Limits.reflectsFiniteProducts_leftOp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
 ReflectsFiniteProducts F.leftOp where reflects _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_leftOp`：reflectsLimitsOfShap
e_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J
 F.leftOp where reflectsLimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `CategoryTheory.Limits.instReflectsColimitsOfShapeDiscreteOfReflectsFinit
eCoproductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C]
 {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheo
r…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` reflects 
finite
products.
-/
lemma reflectsFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.leftOp where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_leftOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` reflects finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
products. -/
/-
**CategoryTheory.Limits.reflectsFiniteProducts_rightOp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteCoproducts F] 
: ReflectsFiniteProducts F.rightOp where reflects _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_rightOp`：reflectsLimitsOfSha
pe_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape
 J F.rightOp where reflectsLimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `CategoryTheory.Limits.instReflectsColimitsOfShapeDiscreteOfReflectsFinit
eCoproductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C]
 {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheo
r…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` reflects
 finite
products.
-/
lemma reflectsFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_rightOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite coproducts, then `F.unop : C ⥤ D` reflects finite
products. -/
/-
**CategoryTheory.Limits.reflectsFiniteProducts_unop** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
 ReflectsFiniteProducts F.unop where reflects _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_unop`：reflectsLimitsOfShape_
unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] : ReflectsLimitsOfShape J F
.unop where reflectsLimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `CategoryTheory.Limits.instReflectsColimitsOfShapeDiscreteOfReflectsFinit
eCoproductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C]
 {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheo
r…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite coproducts, then `F.unop : C ⥤ D` reflects fi
nite
products.
-/
lemma reflectsFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.unop where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_unop
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` reflects finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
coproducts. -/
/-
**CategoryTheory.Limits.reflectsFiniteCoproducts_op** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsFiniteCoproducts_op (F : C ⥤ D) [ReflectsFiniteProducts F] : Refle
ctsFiniteCoproducts F.op where reflects _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_op`：reflectsColimitsOfShap
e_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape J F.op 
where reflectsColimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ D` reflects finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
coproducts.
-/
lemma reflectsFiniteCoproducts_op (F : C ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.op where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_op
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` reflects finite products, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
coproducts. -/
/-
**CategoryTheory.Limits.reflectsFiniteCoproducts_leftOp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
 ReflectsFiniteCoproducts F.leftOp where reflects _
参数：F : C ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_leftOp`：reflectsColimitsOf
Shape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfSha
pe J F.leftOp where reflectsColimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` reflects finite products, then `F.leftOp : Cᵒᵖ ⥤ D` reflects fi
nite
coproducts.
-/
lemma reflectsFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.leftOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_leftOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` reflects finite products, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
coproducts. -/
/-
**CategoryTheory.Limits.reflectsFiniteCoproducts_rightOp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F] 
: ReflectsFiniteCoproducts F.rightOp where reflects _
参数：F : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_rightOp`：reflectsColimitsO
fShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfS
hape J F.rightOp where reflectsColimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` reflects finite products, then `F.rightOp : C ⥤ Dᵒᵖ` reflects f
inite
coproducts.
-/
lemma reflectsFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_rightOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite products, then `F.unop : C ⥤ D` reflects finite
coproducts. -/
/-
**CategoryTheory.Limits.reflectsFiniteCoproducts_unop** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
 ReflectsFiniteCoproducts F.unop where reflects _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_unop`：reflectsColimitsOfSh
ape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] : ReflectsColimitsOfShape
 J F.unop where reflectsColimit {K}
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite products, then `F.unop : C ⥤ D` reflects fini
te
coproducts.
-/
lemma reflectsFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.unop where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_unop
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

end CategoryTheory.Limits

