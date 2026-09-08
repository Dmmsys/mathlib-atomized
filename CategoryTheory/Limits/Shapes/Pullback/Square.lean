/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Square

/-!
# Commutative squares that are pushout or pullback squares

In this file, we translate the `IsPushout` and `IsPullback`
API for the objects of the category `Square C` of commutative
squares in a category `C`. We also obtain lemmas which state
in this language that a pullback of a monomorphism is
a monomorphism (and similarly for pushouts of epimorphisms).

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Square

variable (sq : Square C)

/-- The pullback cone attached to a commutative square. -/
/-
**CategoryTheory.Square.pullbackCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Square`。
形式化陈述：pullbackCone : PullbackCone sq.f₂₄ sq.f₃₄
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…

--- 原说明 ---
The pullback cone attached to a commutative square.
-/
abbrev pullbackCone : PullbackCone sq.f₂₄ sq.f₃₄ :=
  PullbackCone.mk sq.f₁₂ sq.f₁₃ sq.fac

/-- The pushout cocone attached to a commutative square. -/
/-
**CategoryTheory.Square.pushoutCocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Square`。
形式化陈述：pushoutCocone : PushoutCocone sq.f₁₂ sq.f₁₃
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…

--- 原说明 ---
The pushout cocone attached to a commutative square.
-/
abbrev pushoutCocone : PushoutCocone sq.f₁₂ sq.f₁₃ :=
  PushoutCocone.mk sq.f₂₄ sq.f₃₄ sq.fac

/-- The condition that a commutative square is a pullback square. -/
/-
**CategoryTheory.Square.IsPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Squ
are`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Square C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a commutative square is a pullback square.
-/
protected def IsPullback : Prop :=
  IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

/-- The condition that a commutative square is a pushout square. -/
/-
**CategoryTheory.Square.IsPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Squa
re`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Square C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a commutative square is a pushout square.
-/
protected def IsPushout : Prop :=
  IsPushout sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄
/-
**CategoryTheory.Square.isPullback_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Square`。
形式化陈述：isPullback_iff : sq.IsPullback ↔ Nonempty (IsLimit sq.pullbackCone)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
-/
lemma isPullback_iff :
    sq.IsPullback ↔ Nonempty (IsLimit sq.pullbackCone) :=
  ⟨fun h ↦ ⟨h.isLimit⟩, fun h ↦ { w := sq.fac, isLimit' := h }⟩
/-
**CategoryTheory.Square.isPushout_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Square`。
形式化陈述：isPushout_iff : sq.IsPushout ↔ Nonempty (IsColimit sq.pushoutCocone)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
-/
lemma isPushout_iff :
    sq.IsPushout ↔ Nonempty (IsColimit sq.pushoutCocone) :=
  ⟨fun h ↦ ⟨h.isColimit⟩, fun h ↦ { w := sq.fac, isColimit' := h }⟩
/-
**CategoryTheory.Square.IsPullback.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (sq : CategoryThe
ory.Square C)   (h : CategoryTheory.Limits.IsLimit sq.pullbackCone), sq.IsPullba
ck
参数：sq : CategoryTheory.Square C；h : CategoryTheory.Limits.IsLimit sq.pullbackCon
e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Square.isPullback_iff`：isPullback_iff : sq.IsPullback ↔ N
onempty (IsLimit sq.pullbackCone)
-/
lemma IsPullback.mk (h : IsLimit sq.pullbackCone) : sq.IsPullback :=
  sq.isPullback_iff.2 ⟨h⟩
/-
**CategoryTheory.Square.IsPushout.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
quare.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (sq : CategoryThe
ory.Square C)   (h : CategoryTheory.Limits.IsColimit sq.pushoutCocone), sq.IsPus
hout
参数：sq : CategoryTheory.Square C；h : CategoryTheory.Limits.IsColimit sq.pushoutCo
cone。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Square.isPushout_iff`：isPushout_iff : sq.IsPushout ↔ None
mpty (IsColimit sq.pushoutCocone)
-/
lemma IsPushout.mk (h : IsColimit sq.pushoutCocone) : sq.IsPushout :=
  sq.isPushout_iff.2 ⟨h⟩

variable {sq}

/-- If a commutative square `sq` is a pullback square,
then `sq.pullbackCone` is a limit. -/
/-
**CategoryTheory.Square.IsPullback.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Square.IsPullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {sq : Cat
egoryTheory.Square C} → sq.IsPullback → CategoryTheory.Limits.IsLimit sq.pullbac
kCone
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a commutative square `sq` is a pullback square,
then `sq.pullbackCone` is a limit.
-/
noncomputable def IsPullback.isLimit (h : sq.IsPullback) :
    IsLimit sq.pullbackCone :=
  CategoryTheory.IsPullback.isLimit h

/-- If a commutative square `sq` is a pushout square,
then `sq.pushoutCocone` is a colimit. -/
/-
**CategoryTheory.Square.IsPushout.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Square.IsPushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {sq : Cat
egoryTheory.Square C} → sq.IsPushout → CategoryTheory.Limits.IsColimit sq.pushou
tCocone
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a commutative square `sq` is a pushout square,
then `sq.pushoutCocone` is a colimit.
-/
noncomputable def IsPushout.isColimit (h : sq.IsPushout) :
    IsColimit sq.pushoutCocone :=
  CategoryTheory.IsPushout.isColimit h
/-
**CategoryTheory.Square.IsPullback.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq₁ sq₂ : Catego
ryTheory.Square C},   sq₁.IsPullback → ∀ (e : sq₁ ≅ sq₂), sq₂.IsPullback
参数：e : sq₁ ≅ sq₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Square.evaluation₂_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₂.ma…
· 使用定理 `CategoryTheory.Square.Hom.comm₁₂`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Square.evaluation₁_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₁.ma…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Square.evaluation₃_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₃.ma…
· 使用定理 `CategoryTheory.Square.Hom.comm₁₃`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
· 使用定理 `CategoryTheory.Square.evaluation₄_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₄.ma…
· 使用定理 `CategoryTheory.Square.Hom.comm₂₄`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
· 使用定理 `CategoryTheory.Square.Hom.comm₃₄`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
-/
lemma IsPullback.of_iso {sq₁ sq₂ : Square C} (h : sq₁.IsPullback)
    (e : sq₁ ≅ sq₂) : sq₂.IsPullback := by
  refine CategoryTheory.IsPullback.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp
/-
**CategoryTheory.Square.IsPullback.iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq₁ sq₂ : Catego
ryTheory.Square C} (e : sq₁ ≅ sq₂),   sq₁.IsPullback ↔ sq₂.IsPullback
参数：e : sq₁ ≅ sq₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.of_iso`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C},   sq₁.IsPullback 
→ ∀ (e : sq₁ ≅ sq₂), sq₂.IsPu…
-/
lemma IsPullback.iff_of_iso {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂) :
    sq₁.IsPullback ↔ sq₂.IsPullback :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩
/-
**CategoryTheory.Square.IsPushout.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Square.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq₁ sq₂ : Catego
ryTheory.Square C},   sq₁.IsPushout → ∀ (e : sq₁ ≅ sq₂), sq₂.IsPushout
参数：e : sq₁ ≅ sq₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Square.evaluation₂_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₂.ma…
· 使用定理 `CategoryTheory.Square.Hom.comm₁₂`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Square.evaluation₁_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₁.ma…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Square.evaluation₃_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₃.ma…
· 使用定理 `CategoryTheory.Square.Hom.comm₁₃`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
· 使用定理 `CategoryTheory.Square.evaluation₄_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : CategoryTheory.Square C} (φ : X ⟶ Y),   CategoryT
heory.Square.evaluation₄.ma…
· 使用定理 `CategoryTheory.Square.Hom.comm₂₄`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
· 使用定理 `CategoryTheory.Square.Hom.comm₃₄`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (self : sq₁.Hom sq₂),   C
ategoryTheory.Category…
-/
lemma IsPushout.of_iso {sq₁ sq₂ : Square C} (h : sq₁.IsPushout)
    (e : sq₁ ≅ sq₂) : sq₂.IsPushout := by
  refine CategoryTheory.IsPushout.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp
/-
**CategoryTheory.Square.IsPushout.iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Square.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq₁ sq₂ : Catego
ryTheory.Square C} (e : sq₁ ≅ sq₂),   sq₁.IsPushout ↔ sq₂.IsPushout
参数：e : sq₁ ≅ sq₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPushout.of_iso`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C},   sq₁.IsPushout → 
∀ (e : sq₁ ≅ sq₂), sq₂.IsPus…
-/
lemma IsPushout.iff_of_iso {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂) :
    sq₁.IsPushout ↔ sq₂.IsPushout :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩
/-
**CategoryTheory.Square.IsPushout.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
quare.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq : CategoryThe
ory.Square C}, sq.IsPushout → sq.op.IsPullback
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
lemma IsPushout.op {sq : Square C} (h : sq.IsPushout) : sq.op.IsPullback :=
  CategoryTheory.IsPushout.op h.flip
/-
**CategoryTheory.Square.IsPushout.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Square.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq : CategoryThe
ory.Square Cᵒᵖ},   sq.IsPushout → sq.unop.IsPullback
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.unop`：unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶
 Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) : IsPullback inr.uno
p inl.unop g.unop f…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
lemma IsPushout.unop {sq : Square Cᵒᵖ} (h : sq.IsPushout) : sq.unop.IsPullback :=
  CategoryTheory.IsPushout.unop h.flip
/-
**CategoryTheory.Square.IsPullback.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq : CategoryThe
ory.Square C}, sq.IsPullback → sq.op.IsPushout
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.op`：op (h : IsPullback fst snd f g) : IsPushou
t g.op f.op snd.op fst.op
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma IsPullback.op {sq : Square C} (h : sq.IsPullback) : sq.op.IsPushout :=
  CategoryTheory.IsPullback.op h.flip
/-
**CategoryTheory.Square.IsPullback.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {sq : CategoryThe
ory.Square Cᵒᵖ},   sq.IsPullback → sq.unop.IsPushout
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma IsPullback.unop {sq : Square Cᵒᵖ} (h : sq.IsPullback) : sq.unop.IsPushout :=
  CategoryTheory.IsPullback.unop h.flip

namespace IsPullback

variable (h : sq.IsPullback)

include h

/-
**CategoryTheory.Square.IsPullback.flip** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Square.IsPullback`。
形式化陈述：flip : sq.flip.IsPullback
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma flip : sq.flip.IsPullback := CategoryTheory.IsPullback.flip h
/-
**CategoryTheory.Square.IsPullback.mono_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Square.IsPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_f₁₃ [Mono sq.f₂₄] : Mono sq.f₁₃ :=
  (MorphismProperty.monomorphisms C).of_isPullback h (by assumption)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Square.IsPullback.mono_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Square.IsPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_f₁₂ [Mono sq.f₃₄] : Mono sq.f₁₂ := by
  have : Mono sq.flip.f₂₄ := by dsimp; infer_instance
  exact h.flip.mono_f₁₃

end IsPullback

namespace IsPushout

variable (h : sq.IsPushout)

include h

/-
**CategoryTheory.Square.IsPushout.flip** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Square.IsPushout`。
形式化陈述：flip : sq.flip.IsPushout
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
lemma flip : sq.flip.IsPushout := CategoryTheory.IsPushout.flip h
/-
**CategoryTheory.Square.IsPushout.epi_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Square.IsPushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epi_f₂₄ [Epi sq.f₁₃] : Epi sq.f₂₄ :=
  (MorphismProperty.epimorphisms C).of_isPushout h (by assumption)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Square.IsPushout.epi_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Square.IsPushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epi_f₃₄ [Epi sq.f₁₂] : Epi sq.f₃₄ := by
  have : Epi sq.flip.f₁₃ := by dsimp; infer_instance
  exact h.flip.epi_f₂₄

end IsPushout

end Square

end CategoryTheory

