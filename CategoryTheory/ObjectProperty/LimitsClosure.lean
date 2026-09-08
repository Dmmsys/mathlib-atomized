/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Closure of a property of objects under limits of certain shapes

In this file, given a property `P` of objects in a category `C` and
a family of categories `J : α → Type _`, we introduce the closure
`P.limitsClosure J` of `P` under limits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that it is essentially small.

-/

@[expose] public section

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

/-- The closure of a property of objects of a category under limits of
shape `J a` for a family of categories `J`. -/
/-
**CategoryTheory.ObjectProperty.limitsClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.ObjectProperty C →       {α : Type t} →         (J : α → Type u') → [(a : 
α) → CategoryTheory.Category.{v', u'} (J a)] → CategoryTheory.ObjectProperty C
参数：J : α → Type u'；a : α；J a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of a property of objects of a category under limits of
shape `J a` for a family of categories `J`.
-/
inductive limitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : limitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : limitsClosure X) : limitsClosure Y
  | of_limitPresentation {X : C} {a : α} (pres : LimitPresentation (J a) X)
      (h : ∀ j, limitsClosure (pres.diag.obj j)) : limitsClosure X

@[simp]
/-
**CategoryTheory.ObjectProperty.le_limitsClosure** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：le_limitsClosure : P <= P.limitsClosure J
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_limitsClosure : P ≤ P.limitsClosure J :=
  fun X hX ↦ .of_mem X hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : (P.limitsClosure J).Nonempty := .mono (P.le_limitsClosure J)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.limitsClosure J).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : α) : (P.limitsClosure J).IsClosedUnderLimitsOfShape (J a) where
  limitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_limitPresentation hX.toLimitPresentation hX.prop_diag_obj

variable {P J} in
/-
**CategoryTheory.ObjectProperty.limitsClosure_le** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：limitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [for
all (a : α), Q.IsClosedUnderLimitsOfShape (J a)] (h : P <= Q) : P.limitsClosure 
J <= Q
参数：a : α；J a；h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit`：prop_of_isLimit {F : J ⥤ 
C} {c : Cone F} (hc : IsLimit c) (hF : forall (j : J), P (F.obj j)) : P c.pt
-/
lemma limitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (a : α), Q.IsClosedUnderLimitsOfShape (J a)] (h : P ≤ Q) :
    P.limitsClosure J ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_limitPresentation pres h h' => exact Q.prop_of_isLimit pres.isLimit h'

variable {P} in
/-
**CategoryTheory.ObjectProperty.limitsClosure_monotone** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsClosure_monotone {Q : ObjectProperty C} (h : P <= Q) : P.limitsClosu
re J <= Q.limitsClosure J
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_le`：limitsClosure_le {Q : Ob
jectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnderLi
mitsOfShape (J a)] (h : P <= Q) : P.…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsLimitsClosure
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.O
bjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeLimitsClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.
ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_limitsClosure`：le_limitsClosure : P <= 
P.limitsClosure J
-/
lemma limitsClosure_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.limitsClosure J ≤ Q.limitsClosure J :=
  limitsClosure_le (h.trans (Q.le_limitsClosure J))
/-
**CategoryTheory.ObjectProperty.limitsClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：limitsClosure_eq_self [P.IsClosedUnderIsomorphisms] [forall (a : α), P.IsC
losedUnderLimitsOfShape (J a)] : P.limitsClosure J = P
参数：a : α；J a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_le`：limitsClosure_le {Q : Ob
jectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnderLi
mitsOfShape (J a)] (h : P <= Q) : P.…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `CategoryTheory.ObjectProperty.le_limitsClosure`：le_limitsClosure : P <= 
P.limitsClosure J
-/
lemma limitsClosure_eq_self [P.IsClosedUnderIsomorphisms]
    [∀ (a : α), P.IsClosedUnderLimitsOfShape (J a)] : P.limitsClosure J = P :=
  le_antisymm (limitsClosure_le (le_refl P)) (P.le_limitsClosure J)

@[simp]
/-
**CategoryTheory.ObjectProperty.limitsClosure_bot** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：limitsClosure_bot [forall (a : α), Nonempty (J a)] : limitsClosure (⊥ : Ob
jectProperty C) J = ⊥
参数：a : α；J a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_eq_self`：limitsClosure_eq_se
lf [P.IsClosedUnderIsomorphisms] [forall (a : α), P.IsClosedUnderLimitsOfShape (
J a)] : P.limitsClosure J = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsBot`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊥.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeBotOfNonempt
y`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Type u') 
  [inst_1 : CategoryTheory.Category.{v', u'} J] [Nonempty J], ⊥…
-/
lemma limitsClosure_bot [∀ (a : α), Nonempty (J a)] :
    limitsClosure (⊥ : ObjectProperty C) J = ⊥ :=
  limitsClosure_eq_self _ _

@[simp]
/-
**CategoryTheory.ObjectProperty.limitsClosure_top** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：limitsClosure_top : limitsClosure (⊤ : ObjectProperty C) J = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_eq_self`：limitsClosure_eq_se
lf [P.IsClosedUnderIsomorphisms] [forall (a : α), P.IsClosedUnderLimitsOfShape (
J a)] : P.limitsClosure J = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeTop`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Type u')   [inst_1 
: CategoryTheory.Category.{v', u'} J], ⊤.IsClosedUnde…
-/
lemma limitsClosure_top : limitsClosure (⊤ : ObjectProperty C) J = ⊤ :=
  limitsClosure_eq_self _ _
/-
**CategoryTheory.ObjectProperty.limitsClosure_isoClosure** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsClosure_isoClosure : P.isoClosure.limitsClosure J = P.limitsClosure 
J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_le`：limitsClosure_le {Q : Ob
jectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnderLi
mitsOfShape (J a)] (h : P <= Q) : P.…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsLimitsClosure
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.O
bjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeLimitsClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.
ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用引理 `CategoryTheory.ObjectProperty.le_limitsClosure`：le_limitsClosure : P <= 
P.limitsClosure J
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_monotone`：limitsClosure_mono
tone {Q : ObjectProperty C} (h : P <= Q) : P.limitsClosure J <= Q.limitsClosure 
J
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma limitsClosure_isoClosure :
    P.isoClosure.limitsClosure J = P.limitsClosure J := by
  refine le_antisymm (limitsClosure_le ?_)
    (limitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_limitsClosure P J

/-- The closure of a property of objects of a category under limits of
shape `J` for a category `J`. -/
/-
**CategoryTheory.ObjectProperty.limitClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：limitClosure (J : Type*) [Category* J] : ObjectProperty C
参数：J : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of a property of objects of a category under limits of
shape `J` for a category `J`.
-/
abbrev limitClosure (J : Type*) [Category* J] : ObjectProperty C :=
  P.limitsClosure (fun (_ : Unit) ↦ J)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [Category* J] : (P.limitClosure J).IsClosedUnderLimitsOfShape J :=
  P.instIsClosedUnderLimitsOfShapeLimitsClosure _ ()

/-- Given `P : ObjectProperty C` and a family of categories `J : α → Type _`,
this property of objects contains `P` and all objects that are equal to `lim F`
for some functor `F : J a ⥤ C` such that `F.obj j` satisfies `P` for any `j`. -/
/-
**CategoryTheory.ObjectProperty.strictLimitsClosureStep** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsClosureStep : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C` and a family of categories `J : α → Type _`,
this property of objects contains `P` and all objects that are equal to `lim F`
for some functor `F : J a ⥤ C` such that `F.obj j` satisfies `P` for any `j`.
-/
def strictLimitsClosureStep : ObjectProperty C :=
  P ⊔ (⨆ (a : α), P.strictLimitsOfShape (J a))

@[simp]
/-
**CategoryTheory.ObjectProperty.le_strictLimitsClosureStep** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：le_strictLimitsClosureStep : P <= P.strictLimitsClosureStep J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma le_strictLimitsClosureStep : P ≤ P.strictLimitsClosureStep J := le_sup_left
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : (P.strictLimitsClosureStep J).Nonempty :=
  .mono (P.le_strictLimitsClosureStep J)

variable {P} in
/-
**CategoryTheory.ObjectProperty.strictLimitsClosureStep_monotone** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsClosureStep_monotone {Q : ObjectProperty C} (h : P <= Q) : P.s
trictLimitsClosureStep J <= Q.strictLimitsClosureStep J
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用引理 `CategoryTheory.ObjectProperty.strictLimitsOfShape_monotone`：strictLimits
OfShape_monotone {Q : ObjectProperty C} (h : P <= Q) : P.strictLimitsOfShape J <
= Q.strictLimitsOfShape J
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma strictLimitsClosureStep_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictLimitsClosureStep J ≤ Q.strictLimitsClosureStep J := by
  dsimp [strictLimitsClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨h.trans le_sup_left, fun a ↦
    (strictLimitsOfShape_monotone (J a) h).trans <|
      le_iSup (fun a ↦ Q.strictLimitsOfShape (J a)) a |>.trans le_sup_right⟩

section

variable {β : Type w'} [LinearOrder β] [OrderBot β] [SuccOrder β] [WellFoundedLT β]

/-- Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.strictLimitsClosureStep J`. -/
/-
**CategoryTheory.ObjectProperty.strictLimitsClosureIter** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsClosureIter (b : β) : ObjectProperty C
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.strictLimitsClosureStep J`.
-/
abbrev strictLimitsClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q ↦ Q.strictLimitsClosureStep J) b P
/-
**CategoryTheory.ObjectProperty.le_strictLimitsClosureIter** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：le_strictLimitsClosureIter (b : β) : P <= P.strictLimitsClosureIter J b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `transfiniteIterate_bot`：transfiniteIterate_bot [OrderBot J] (i₀ : I) : t
ransfiniteIterate φ (⊥ : J) i₀ = i₀
· 使用引理 `monotone_transfiniteIterate`：monotone_transfiniteIterate (hφ : forall (i
 : I), i <= φ i) : Monotone (fun (j : J) => transfiniteIterate φ j i₀)
· 使用引理 `CategoryTheory.ObjectProperty.le_strictLimitsClosureStep`：le_strictLimit
sClosureStep : P <= P.strictLimitsClosureStep J
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma le_strictLimitsClosureIter (b : β) :
    P ≤ P.strictLimitsClosureIter J b :=
  le_of_eq_of_le (transfiniteIterate_bot _ _).symm
    (monotone_transfiniteIterate _ _ (fun _ ↦ le_strictLimitsClosureStep _ _) bot_le)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (b : β) [P.Nonempty] : (P.strictLimitsClosureIter J b).Nonempty :=
  .mono (P.le_strictLimitsClosureIter J b)
/-
**CategoryTheory.ObjectProperty.strictLimitsClosureIter_le_limitsClosure** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsClosureIter_le_limitsClosure (b : β) : P.strictLimitsClosureIt
er J b <= P.limitsClosure J
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `transfiniteIterate_bot`：transfiniteIterate_bot [OrderBot J] (i₀ : I) : t
ransfiniteIterate φ (⊥ : J) i₀ = i₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `CategoryTheory.ObjectProperty.strictLimitsClosureIter.eq_1`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty 
C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用引理 `transfiniteIterate_succ`：transfiniteIterate_succ (i₀ : I) (j : J) (hj : 
¬ IsMax j) : transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j 
i₀)
· 使用定理 `CategoryTheory.ObjectProperty.strictLimitsClosureStep.eq_1`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty 
C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.strictLimitsOfShape_le_limitsOfShape`：stri
ctLimitsOfShape_le_limitsOfShape : P.strictLimitsOfShape J <= P.limitsOfShape J
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_monotone`：limitsOfShape_mono
tone {Q : ObjectProperty C} (hPQ : P <= Q) : P.limitsOfShape J <= Q.limitsOfShap
e J
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.limitsOfShape_l
e`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} (P : CategoryT
heory.ObjectProperty C) (J : Type u')   {inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeLimitsClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.
ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用引理 `transfiniteIterate_limit`：transfiniteIterate_limit (i₀ : I) (j : J) (hj 
: Order.IsSuccLimit j) : transfiniteIterate φ j i₀ = ⨆ (x : Set.Iio j), transfin
iteIterate φ x…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
lemma strictLimitsClosureIter_le_limitsClosure (b : β) :
    P.strictLimitsClosureIter J b ≤ P.limitsClosure J := by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    rw [strictLimitsClosureIter, transfiniteIterate_succ _ _ _ hb,
      strictLimitsClosureStep, sup_le_iff, iSup_le_iff]
    exact ⟨hb', fun a ↦ ((strictLimitsOfShape_le_limitsOfShape _ _).trans
      (limitsOfShape_monotone _ hb')).trans (limitsOfShape_le _ _)⟩
  | isSuccLimit b hb hb' =>
    simp only [transfiniteIterate_limit _ _ _ hb,
      iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro c hc
    exact hb' _ hc

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] (b : β)
    [hb₀ : Small.{w} (Set.Iio b)] :
    ObjectProperty.Small.{w} (P.strictLimitsClosureIter J b) := by
  have H {b c : β} (hbc : b ≤ c) [Small.{w} (Set.Iio c)] : Small.{w} (Set.Iio b) :=
    small_of_injective (f := fun x ↦ (⟨x.1, lt_of_lt_of_le x.2 hbc⟩ : Set.Iio c))
      (fun _ _ _ ↦ by aesop)
  induction b using SuccOrder.limitRecOn generalizing hb₀ with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp only [transfiniteIterate_bot]
    infer_instance
  | succ b hb hb' =>
    have := H (Order.le_succ b)
    rw [strictLimitsClosureIter, transfiniteIterate_succ _ _ _ hb,
      strictLimitsClosureStep]
    infer_instance
  | isSuccLimit b hb hb' =>
    simp only [transfiniteIterate_limit _ _ _ hb]
    have (c : Set.Iio b) : ObjectProperty.Small.{w}
      (transfiniteIterate (fun Q ↦ Q.strictLimitsClosureStep J) c.1 P) := by
      have := H c.2.le
      exact hb' c.1 c.2
    infer_instance

end

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : ∀ (a : α), HasCardinalLT (J a) κ)

include h

/-
**CategoryTheory.ObjectProperty.strictLimitsClosureStep_strictLimitsClosureIter_
eq_self** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsClosureStep_strictLimitsClosureIter_eq_self : (P.strictLimitsC
losureIter J κ.ord).strictLimitsClosureStep J = (P.strictLimitsClosureIter J κ.o
rd)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `HasCardinalLT.small`：small : Small.{v} X
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Ordinal.iSup_lt_of_lt_cof`：iSup_lt_of_lt_cof {f : α -> Ordinal.{u}} {a :
 Ordinal.{u}} (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, f i < a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `hasCardinalLT_iff_cardinal_mk_lt`：hasCardinalLT_iff_cardinal_mk_lt (X : 
Type u) (κ : Cardinal.{u}) : HasCardinalLT X κ ↔ Cardinal.mk X < κ
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `monotone_transfiniteIterate`：monotone_transfiniteIterate (hφ : forall (i
 : I), i <= φ i) : Monotone (fun (j : J) => transfiniteIterate φ j i₀)
· 使用引理 `CategoryTheory.ObjectProperty.le_strictLimitsClosureStep`：le_strictLimit
sClosureStep : P <= P.strictLimitsClosureStep J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用引理 `transfiniteIterate_succ`：transfiniteIterate_succ (i₀ : I) (j : J) (hj : 
¬ IsMax j) : transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j 
i₀)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `transfiniteIterate_limit`：transfiniteIterate_limit (i₀ : I) (j : J) (hj 
: Order.IsSuccLimit j) : transfiniteIterate φ j i₀ = ⨆ (x : Set.Iio j), transfin
iteIterate φ x…
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
（共 34 条，此处仅展示前 30 条）
-/
lemma strictLimitsClosureStep_strictLimitsClosureIter_eq_self :
    (P.strictLimitsClosureIter J κ.ord).strictLimitsClosureStep J =
      (P.strictLimitsClosureIter J κ.ord) := by
  have hκ : κ.IsRegular := Fact.out
  have (a : α) := (h a).small
  refine le_antisymm (fun X hX ↦ ?_) (le_strictLimitsClosureStep _ _)
  simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff] at hX
  obtain (hX | ⟨a, F, hF⟩) := hX
  · exact hX
  · simp only [strictLimitsClosureIter, transfiniteIterate_limit _ _ _
      (Cardinal.isSuccLimit_ord hκ.aleph0_le), prop_iSup_iff,
      Subtype.exists, Set.mem_Iio, exists_prop] at hF
    choose o ho ho' using hF
    obtain ⟨m, hm, hm'⟩ : ∃ (m : Ordinal.{w}) (hm : m < κ.ord), ∀ (j : J a), o j ≤ m := by
      refine ⟨⨆ j, o ((equivShrink.{w} (J a)).symm j),
        Ordinal.iSup_lt_of_lt_cof ?_ (fun _ ↦ ho _), fun j ↦ ?_⟩
      · rw [hκ.cof_ord, ← hasCardinalLT_iff_cardinal_mk_lt _ κ,
          ← hasCardinalLT_iff_of_equiv (equivShrink.{w} (J a))]
        exact h a
      · obtain ⟨j, rfl⟩ := (equivShrink.{w} (J a)).symm.surjective j
        exact le_ciSup Ordinal.bddAbove_of_small _
    refine monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) ↦ Q.le_strictLimitsClosureStep J) (Order.succ_le_iff.2 hm) _ ?_
    dsimp
    rw [transfiniteIterate_succ _ _ _ (by simp)]
    simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff]
    exact Or.inr ⟨a, ⟨_, fun j ↦ monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) ↦ Q.le_strictLimitsClosureStep J)  (hm' j) _ (ho' j)⟩⟩
/-
**CategoryTheory.ObjectProperty.isoClosure_strictLimitsClosureIter_eq_limitsClos
ure** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isoClosure_strictLimitsClosureIter_eq_limitsClosure : (P.strictLimitsClosu
reIter J κ.ord).isoClosure = P.limitsClosure J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsLimitsClosure
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.O
bjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用引理 `CategoryTheory.ObjectProperty.strictLimitsClosureIter_le_limitsClosure`：
strictLimitsClosureIter_le_limitsClosure (b : β) : P.strictLimitsClosureIter J b
 <= P.limitsClosure J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.strictLimitsClosureStep_strictLimitsClosur
eIter_eq_self`：strictLimitsClosureStep_strictLimitsClosureIter_eq_self : (P.stri
ctLimitsClosureIter J κ.ord).strictLimitsClosureStep J = (P.strictLimitsClo…
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_isoClosure`：limitsOfShape_is
oClosure : P.isoClosure.limitsOfShape J = P.limitsOfShape J
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_strictLimitsOfShape`：isoClosure
_strictLimitsOfShape : (P.strictLimitsOfShape J).isoClosure = P.limitsOfShape J
· 使用定理 `CategoryTheory.ObjectProperty.strictLimitsClosureStep.eq_1`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty 
C) {α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用引理 `CategoryTheory.ObjectProperty.monotone_isoClosure`：monotone_isoClosure (
h : P <= Q) : isoClosure P <= isoClosure Q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_le`：limitsClosure_le {Q : Ob
jectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnderLi
mitsOfShape (J a)] (h : P <= Q) : P.…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsIsoClosure`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C),   P.isoClosure.IsClosedUnderIsomorphisms
· 使用引理 `CategoryTheory.ObjectProperty.le_strictLimitsClosureIter`：le_strictLimit
sClosureIter (b : β) : P <= P.strictLimitsClosureIter J b
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma isoClosure_strictLimitsClosureIter_eq_limitsClosure :
    (P.strictLimitsClosureIter J κ.ord).isoClosure = P.limitsClosure J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictLimitsClosureIter_le_limitsClosure J κ.ord
  · have (a : α) :
        (P.strictLimitsClosureIter J κ.ord).isoClosure.IsClosedUnderLimitsOfShape (J a) := ⟨by
      conv_rhs => rw [← P.strictLimitsClosureStep_strictLimitsClosureIter_eq_self J κ h]
      rw [limitsOfShape_isoClosure, ← isoClosure_strictLimitsOfShape,
        strictLimitsClosureStep]
      exact monotone_isoClosure ((le_trans (by rfl) (le_iSup _ a)).trans le_sup_right)⟩
    refine limitsClosure_le
      ((P.le_strictLimitsClosureIter J κ.ord).trans (le_isoClosure _))
/-
**CategoryTheory.ObjectProperty.isEssentiallySmall_limitsClosure** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isEssentiallySmall_limitsClosure [ObjectProperty.EssentiallySmall.{w} P] [
LocallySmall.{w} C] [Small.{w} α] [forall a, Small.{w} (J a)] [forall a, Locally
Small.{w} (J a)] : ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J)
参数：J a；J a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_isoClosure`：limitsClosure_is
oClosure : P.isoClosure.limitsClosure J = P.limitsClosure J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_strictLimitsClosureIter_eq_limi
tsClosure`：isoClosure_strictLimitsClosureIter_eq_limitsClosure : (P.strictLimits
ClosureIter J κ.ord).isoClosure = P.limitsClosure J
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallIsoClosure`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPropert
y C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallOfSmall`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C
)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallStrictLimitsClosureIterOfLocallyS
mallOfSmallElemIio`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P 
: CategoryTheory.ObjectProperty C) {α : Type t}   (J : α → Type u') [inst_1 : (a
…
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.of_le`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.ObjectProperty C}  
 [CategoryTheory.ObjectProperty.Essentiall…
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_monotone`：limitsClosure_mono
tone {Q : ObjectProperty C} (h : P <= Q) : P.limitsClosure J <= Q.limitsClosure 
J
-/
lemma isEssentiallySmall_limitsClosure
    [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J) := by
  obtain ⟨Q, hQ, hQ₁, hQ₂⟩ := EssentiallySmall.exists_small_le.{w} P
  have : ObjectProperty.EssentiallySmall.{w} (Q.isoClosure.limitsClosure J) := by
    rw [limitsClosure_isoClosure,
      ← Q.isoClosure_strictLimitsClosureIter_eq_limitsClosure J κ h]
    infer_instance
  exact .of_le (limitsClosure_monotone J hQ₂)

end

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J) := by
  obtain ⟨κ, h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall J
  have : Fact κ.IsRegular := ⟨h₁⟩
  exact isEssentiallySmall_limitsClosure P J κ h₂

end CategoryTheory.ObjectProperty

