/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Closure of a property of objects under colimits of certain shapes

In this file, given a property `P` of objects in a category `C` and
family of categories `J : α → Type _`, we introduce the closure
`P.colimitsClosure J` of `P` under colimits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that it is essentially small.

(We deduce these results about the closure under colimits by dualising the
results in the file `Mathlib/CategoryTheory/ObjectProperty/LimitsClosure.lean`.)

-/

public section

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

/-- The closure of a property of objects of a category under colimits of
shape `J a` for a family of categories `J`. -/
/-
**CategoryTheory.ObjectProperty.colimitsClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.ObjectProperty C →       {α : Type t} →         (J : α → Type u') → [(a : 
α) → CategoryTheory.Category.{v', u'} (J a)] → CategoryTheory.ObjectProperty C
参数：J : α → Type u'；a : α；J a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of a property of objects of a category under colimits of
shape `J a` for a family of categories `J`.
-/
inductive colimitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : colimitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : colimitsClosure X) : colimitsClosure Y
  | of_colimitPresentation {X : C} {a : α} (pres : ColimitPresentation (J a) X)
      (h : ∀ j, colimitsClosure (pres.diag.obj j)) : colimitsClosure X

@[simp]
/-
**CategoryTheory.ObjectProperty.le_colimitsClosure** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：le_colimitsClosure : P <= P.colimitsClosure J
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_colimitsClosure : P ≤ P.colimitsClosure J :=
  fun X hX ↦ .of_mem X hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : (P.colimitsClosure J).Nonempty :=
  .mono (P.le_colimitsClosure J)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.colimitsClosure J).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : α) : (P.colimitsClosure J).IsClosedUnderColimitsOfShape (J a) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_colimitPresentation hX.toColimitPresentation hX.prop_diag_obj

variable {P J} in
/-
**CategoryTheory.ObjectProperty.colimitsClosure_le** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [f
orall (a : α), Q.IsClosedUnderColimitsOfShape (J a)] (h : P <= Q) : P.colimitsCl
osure J <= Q
参数：a : α；J a；h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit`：prop_of_isColimit {F : 
J ⥤ C} {c : Cocone F} (hc : IsColimit c) (hF : forall (j : J), P (F.obj j)) : P 
c.pt
-/
lemma colimitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (a : α), Q.IsClosedUnderColimitsOfShape (J a)] (h : P ≤ Q) :
    P.colimitsClosure J ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'

variable {P} in
/-
**CategoryTheory.ObjectProperty.colimitsClosure_monotone** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_monotone {Q : ObjectProperty C} (h : P <= Q) : P.colimitsC
losure J <= Q.colimitsClosure J
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_le`：colimitsClosure_le {Q 
: ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnd
erColimitsOfShape (J a)] (h : P <= Q) …
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsColimitsClosu
re`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory
.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeColimitsCl
osure`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryThe
ory.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_colimitsClosure`：le_colimitsClosure : P
 <= P.colimitsClosure J
-/
lemma colimitsClosure_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.colimitsClosure J ≤ Q.colimitsClosure J :=
  colimitsClosure_le (h.trans (Q.le_colimitsClosure J))
/-
**CategoryTheory.ObjectProperty.colimitsClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_eq_self [P.IsClosedUnderIsomorphisms] [forall (a : α), P.I
sClosedUnderColimitsOfShape (J a)] : P.colimitsClosure J = P
参数：a : α；J a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_le`：colimitsClosure_le {Q 
: ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnd
erColimitsOfShape (J a)] (h : P <= Q) …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `CategoryTheory.ObjectProperty.le_colimitsClosure`：le_colimitsClosure : P
 <= P.colimitsClosure J
-/
lemma colimitsClosure_eq_self [P.IsClosedUnderIsomorphisms]
    [∀ (a : α), P.IsClosedUnderColimitsOfShape (J a)] : P.colimitsClosure J = P :=
  le_antisymm (colimitsClosure_le (le_refl P)) (P.le_colimitsClosure J)

@[simp]
/-
**CategoryTheory.ObjectProperty.colimitsClosure_bot** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_bot [forall (a : α), Nonempty (J a)] : colimitsClosure (⊥ 
: ObjectProperty C) J = ⊥
参数：a : α；J a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_eq_self`：colimitsClosure_e
q_self [P.IsClosedUnderIsomorphisms] [forall (a : α), P.IsClosedUnderColimitsOfS
hape (J a)] : P.colimitsClosure J = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsBot`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊥.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeBotOfNonem
pty`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Type u'
)   [inst_1 : CategoryTheory.Category.{v', u'} J] [Nonempty J], ⊥…
-/
lemma colimitsClosure_bot [∀ (a : α), Nonempty (J a)] :
    colimitsClosure (⊥ : ObjectProperty C) J = ⊥ :=
  colimitsClosure_eq_self _ _

@[simp]
/-
**CategoryTheory.ObjectProperty.colimitsClosure_top** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_top : colimitsClosure (⊤ : ObjectProperty C) J = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_eq_self`：colimitsClosure_e
q_self [P.IsClosedUnderIsomorphisms] [forall (a : α), P.IsClosedUnderColimitsOfS
hape (J a)] : P.colimitsClosure J = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeTop`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Type u')   [inst_
1 : CategoryTheory.Category.{v', u'} J], ⊤.IsClosedUnde…
-/
lemma colimitsClosure_top : colimitsClosure (⊤ : ObjectProperty C) J = ⊤ :=
  colimitsClosure_eq_self _ _
/-
**CategoryTheory.ObjectProperty.colimitsClosure_isoClosure** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_isoClosure : P.isoClosure.colimitsClosure J = P.colimitsCl
osure J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_le`：colimitsClosure_le {Q 
: ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnd
erColimitsOfShape (J a)] (h : P <= Q) …
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsColimitsClosu
re`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory
.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeColimitsCl
osure`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryThe
ory.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用引理 `CategoryTheory.ObjectProperty.le_colimitsClosure`：le_colimitsClosure : P
 <= P.colimitsClosure J
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_monotone`：colimitsClosure_
monotone {Q : ObjectProperty C} (h : P <= Q) : P.colimitsClosure J <= Q.colimits
Closure J
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma colimitsClosure_isoClosure :
    P.isoClosure.colimitsClosure J = P.colimitsClosure J := by
  refine le_antisymm (colimitsClosure_le ?_)
    (colimitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_colimitsClosure P J

/-- The closure of a property of objects of a category under colimits of
shape `J` for a category `J`. -/
/-
**CategoryTheory.ObjectProperty.colimitClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：colimitClosure (J : Type*) [Category* J] : ObjectProperty C
参数：J : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of a property of objects of a category under colimits of
shape `J` for a category `J`.
-/
abbrev colimitClosure (J : Type*) [Category* J] : ObjectProperty C :=
  P.colimitsClosure (fun (_ : Unit) ↦ J)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [Category* J] : (P.colimitClosure J).IsClosedUnderColimitsOfShape J :=
  P.instIsClosedUnderColimitsOfShapeColimitsClosure _ ()
/-
**CategoryTheory.ObjectProperty.colimitsClosure_eq_unop_limitsClosure** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsClosure_eq_unop_limitsClosure : P.colimitsClosure J = (P.op.limits
Closure (fun a => (J a)ᵒᵖ)).unop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_le`：colimitsClosure_le {Q 
: ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnd
erColimitsOfShape (J a)] (h : P <= Q) …
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsUnopOfOpposit
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.
ObjectProperty Cᵒᵖ)   [P.IsClosedUnderIsomorphisms], P.unop.IsC…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsLimitsClosure
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.O
bjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeUnopOfIsCl
osedUnderLimitsOfShapeOpposite`：∀ {C : Type u_1} [inst : CategoryTheory.Category
.{v_1, u_1} C] (J : Type u')   [inst_1 : CategoryTheory.Category.{v', u'} J] (Q 
: CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeLimitsClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.
ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone_iff`：op_monotone_iff {P Q : Ob
jectProperty C} : P.op <= Q.op ↔ P <= Q
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用引理 `CategoryTheory.ObjectProperty.le_limitsClosure`：le_limitsClosure : P <= 
P.limitsClosure J
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_le`：limitsClosure_le {Q : Ob
jectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnderLi
mitsOfShape (J a)] (h : P <= Q) : P.…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsOppositeOp`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C)   [P.IsClosedUnderIsomorphisms], P.op.IsClose…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsColimitsClosu
re`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory
.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeOppositeOpOf
IsClosedUnderColimitsOfShape`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{
v_1, u_1} C] (P : CategoryTheory.ObjectProperty C) (J : Type u')   [inst_1 : Cat
egoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeColimitsCl
osure`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryThe
ory.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用引理 `CategoryTheory.ObjectProperty.le_colimitsClosure`：le_colimitsClosure : P
 <= P.colimitsClosure J
-/
lemma colimitsClosure_eq_unop_limitsClosure :
    P.colimitsClosure J = (P.op.limitsClosure (fun a ↦ (J a)ᵒᵖ)).unop := by
  refine le_antisymm ?_ ?_
  · apply colimitsClosure_le
    rw [← op_monotone_iff, op_unop]
    apply le_limitsClosure
  · rw [← op_monotone_iff, op_unop]
    apply limitsClosure_le
    rw [op_monotone_iff]
    apply le_colimitsClosure
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.colimitsClosure J) := by
  rw [colimitsClosure_eq_unop_limitsClosure]
  have (a : α) : Small.{w} (J a)ᵒᵖ := Opposite.small
  infer_instance

end CategoryTheory.ObjectProperty

