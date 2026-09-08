/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Relation of morphism properties with limits

The following predicates are introduces for morphism properties `P`:
* `IsStableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `IsStableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

We define `P.universally` for the class of morphisms which satisfy `P` after any base change.

We also introduce properties `IsStableUnderProductsOfShape`, `IsStableUnderLimitsOfShape`,
`IsStableUnderFiniteProducts`, and similar properties for colimits and coproducts.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : MorphismProperty C)

/-- Given a class of morphisms `P`, this is the class of pullbacks
of morphisms in `P`. -/
/-
**CategoryTheory.MorphismProperty.pullbacks** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：pullbacks : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a class of morphisms `P`, this is the class of pullbacks
of morphisms in `P`.
-/
def pullbacks : MorphismProperty C := fun A B q ↦
  ∃ (X Y : C) (p : X ⟶ Y) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPullback f q p g
/-
**CategoryTheory.MorphismProperty.pullbacks_mk** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：pullbacks_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
 (sq : IsPullback f q p g) (hp : P p) : P.pullbacks q
参数：sq : IsPullback f q p g；hp : P p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbacks_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPullback f q p g) (hp : P p) :
    P.pullbacks q :=
  ⟨_, _, _, _, _, hp, sq⟩
/-
**CategoryTheory.MorphismProperty.le_pullbacks** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：le_pullbacks : P <= P.pullbacks
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.pullbacks_mk`：pullbacks_mk {A B X Y : C}
 {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (sq : IsPullback f q p g) (hp :
 P p) : P.pullbacks q
· 使用引理 `CategoryTheory.IsPullback.of_id_fst`：of_id_fst : IsPullback (𝟙 _) f f (𝟙
 _)
-/
lemma le_pullbacks : P ≤ P.pullbacks := by
  intro A B q hq
  exact P.pullbacks_mk IsPullback.of_id_fst hq
/-
**CategoryTheory.MorphismProperty.pullbacks_monotone** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：pullbacks_monotone : Monotone (pullbacks (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbacks_monotone : Monotone (pullbacks (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

/-- Given a class of morphisms `P`, this is the class of pushouts
of morphisms in `P`. -/
/-
**CategoryTheory.MorphismProperty.pushouts** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：pushouts : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a class of morphisms `P`, this is the class of pushouts
of morphisms in `P`.
-/
def pushouts : MorphismProperty C := fun X Y q ↦
  ∃ (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g
/-
**CategoryTheory.MorphismProperty.pushouts_mk** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：pushouts_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} 
(sq : IsPushout f q p g) (hq : P q) : P.pushouts p
参数：sq : IsPushout f q p g；hq : P q。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushouts_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout f q p g) (hq : P q) :
    P.pushouts p :=
  ⟨_, _, _, _, _, hq, sq⟩
/-
**CategoryTheory.MorphismProperty.le_pushouts** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：le_pushouts : P <= P.pushouts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_mk`：pushouts_mk {A B X Y : C} {
f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (sq : IsPushout f q p g) (hq : P 
q) : P.pushouts p
· 使用引理 `CategoryTheory.IsPushout.of_id_fst`：of_id_fst : IsPushout (𝟙 _) f f (𝟙 _
)
-/
lemma le_pushouts : P ≤ P.pushouts := by
  intro X Y p hp
  exact P.pushouts_mk IsPushout.of_id_fst hp
/-
**CategoryTheory.MorphismProperty.pushouts_monotone** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：pushouts_monotone : Monotone (pushouts (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushouts_monotone : Monotone (pushouts (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.pushouts.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.pullbacks.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨X, Y, p, f, g, hp, h⟩
    exact ⟨X, Y, p, e.inv.left ≫ f, e.inv.right ≫ g, hp,
      IsPullback.paste_horiz (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) h⟩)

/-- If `P : MorphismProperty C` is such that any object in `C` maps to the
target of some morphism in `P`, then `P.pushouts` contains the isomorphisms. -/
/-
**CategoryTheory.MorphismProperty.isomorphisms_le_pushouts** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isomorphisms_le_pushouts (h : forall (X : C), exists (A B : C) (p : A ⟶ B)
 (_ : P p) (_ : B ⟶ X), IsIso p) : isomorphisms C <= P.pushouts
参数：h : forall (X : C), exists (A B : C) (p : A ⟶ B) (_ : P p) (_ : B ⟶ X), IsIso
 p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用引理 `CategoryTheory.IsPushout.of_id_snd`：of_id_snd : IsPushout f (𝟙 _) (𝟙 _) 
f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
If `P : MorphismProperty C` is such that any object in `C` maps to the
target of some morphism in `P`, then `P.pushouts` contains the isomorphisms.
-/
lemma isomorphisms_le_pushouts
    (h : ∀ (X : C), ∃ (A B : C) (p : A ⟶ B) (_ : P p) (_ : B ⟶ X), IsIso p) :
    isomorphisms C ≤ P.pushouts := by
  intro X Y f (_ : IsIso f)
  obtain ⟨A, B, p, hp, g, _⟩ := h X
  exact ⟨A, B, p, p ≫ g, g ≫ f, hp, (IsPushout.of_id_snd (f := p ≫ g)).of_iso
    (Iso.refl _) (Iso.refl _) (asIso p) (asIso f) (by simp) (by simp) (by simp) (by simp)⟩

/-- A morphism property is `IsStableUnderBaseChange` if the base change of such a morphism
still falls in the class. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange** 是 Mathlib 中的一个归纳类型，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property is `IsStableUnderBaseChange` if the base change of such a mo
rphism
still falls in the class.
-/
class IsStableUnderBaseChange : Prop where
  of_isPullback {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g'
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.pullbacks.IsStableUnderBaseChange where
  of_isPullback := by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pullbacks_mk (h.paste_horiz hq) hp

/-- A morphism property is `IsStableUnderCobaseChange` if the cobase change of such a morphism
still falls in the class. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange** 是 Mathlib 中的一个归纳类型
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property is `IsStableUnderCobaseChange` if the cobase change of such 
a morphism
still falls in the class.
-/
class IsStableUnderCobaseChange : Prop where
  of_isPushout {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f'
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.pushouts.IsStableUnderCobaseChange where
  of_isPushout := by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pushouts_mk (hq.paste_horiz h) hp

/-- `P.HasPullbacksAlong f` states that for any morphism satisfying `P` with the same codomain
as `f`, the pullback of that morphism along `f` exists. -/
/-
**CategoryTheory.MorphismProperty.HasPullbacksAlong** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → {X Y : C} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.HasPullbacksAlong f` states that for any morphism satisfying `P` with the sam
e codomain
as `f`, the pullback of that morphism along `f` exists.
-/
protected class HasPullbacksAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPullback {W} (g : W ⟶ Y) : P g → HasPullback g f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : P.HasPullbacksAlong f where
  hasPullback _ _ := inferInstance

/-- `P.HasPushoutsAlong f` states that for any morphism satisfying `P` with the same domain
as `f`, the pushout of that morphism along `f` exists. -/
/-
**CategoryTheory.MorphismProperty.HasPushoutsAlong** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → {X Y : C} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.HasPushoutsAlong f` states that for any morphism satisfying `P` with the same
 domain
as `f`, the pushout of that morphism along `f` exists.
-/
protected class HasPushoutsAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPushout {W} (g : X ⟶ W) : P g → HasPushout g f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] : P.HasPushoutsAlong f where
  hasPushout _ _ := inferInstance

/-- `P.IsStableUnderBaseChangeAlong f` states that for any morphism satisfying `P` with the same
codomain as `f`, any pullback of that morphism along `f` also satisfies `P`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong** 是 Mathlib 中的一个归
纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → {X Y : C} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.IsStableUnderBaseChangeAlong f` states that for any morphism satisfying `P` w
ith the same
codomain as `f`, any pullback of that morphism along `f` also satisfies `P`.
-/
class IsStableUnderBaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPullback {Z W : C} {f' : W ⟶ Z} {g' : W ⟶ X} {g : Z ⟶ Y}
    (pb : IsPullback f' g' g f) : P g → P g'
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) : P.IsStableUnderBaseChangeAlong f where
  of_isPullback := IsStableUnderBaseChange.of_isPullback

/-- `P.IsStableUnderCobaseChangeAlong f` states that for any morphism satisfying `P` with the same
codomain as `f`, any pullback of that morphism along `f` also satisfies `P`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAlong** 是 Mathlib 中的一
个归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → {X Y : C} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.IsStableUnderCobaseChangeAlong f` states that for any morphism satisfying `P`
 with the same
codomain as `f`, any pullback of that morphism along `f` also satisfies `P`.
-/
class IsStableUnderCobaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPushout {Z W : C} {f' : Z ⟶ W} {g' : Y ⟶ W} {g : X ⟶ Z}
    (pb : IsPushout f g g' f') : P g → P g'
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderCobaseChange] {X Y : C} (f : X ⟶ Y) :
    P.IsStableUnderCobaseChangeAlong f where
  of_isPushout := IsStableUnderCobaseChange.of_isPushout

alias of_isPullback := IsStableUnderBaseChange.of_isPullback
/-
**CategoryTheory.MorphismProperty.isStableUnderBaseChange_iff_pullbacks_le** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderBaseChange_iff_pullbacks_le : P.IsStableUnderBaseChange ↔ P.p
ullbacks <= P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
-/
lemma isStableUnderBaseChange_iff_pullbacks_le :
    P.IsStableUnderBaseChange ↔ P.pullbacks ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩
/-
**CategoryTheory.MorphismProperty.pullbacks_le** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：pullbacks_le [P.IsStableUnderBaseChange] : P.pullbacks <= P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderBaseChange_iff_pullbacks_le
`：isStableUnderBaseChange_iff_pullbacks_le : P.IsStableUnderBaseChange ↔ P.pullb
acks <= P
-/
lemma pullbacks_le [P.IsStableUnderBaseChange] : P.pullbacks ≤ P := by
  rwa [← isStableUnderBaseChange_iff_pullbacks_le]

variable {P} in
/-- Alternative constructor for `IsStableUnderBaseChange`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.mk'** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C} [P.RespectsIso],   (∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S)
 [inst_2 : CategoryTheory.Limits.HasPullback f g],       P g → P (CategoryTheory
.Limits.pullback.fst f g)) →     P.IsStableUnderBaseChange
参数：∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) [inst_2 : CategoryTheory.Limits.HasPull
back f g],       P g → P (CategoryTheory.Limits.pullback.fst f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst`：isoPullback_inv_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.f
st _ _

--- 原说明 ---
Alternative constructor for `IsStableUnderBaseChange`.
-/
theorem IsStableUnderBaseChange.mk' [RespectsIso P]
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (_ : P g),
      P (pullback.fst f g)) :
    IsStableUnderBaseChange P where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    have : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv, sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPul
lback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBa
seChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C} [P.RespectsIso],   (∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
 [CategoryTheory.Limits.HasPullback f g],       P g → ∃ T fst snd, CategoryTheor
y.IsPullback fst snd f g ∧ P fst) →     P.IsStableUnderBaseChange
参数：∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [CategoryTheory.Limits.HasPullback f g]
,       P g → ∃ T fst snd, CategoryTheory.IsPullback fst snd f g ∧ P fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.mk'`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProper
ty C} [P.RespectsIso],   (∀ (X Y S : C) (f : X ⟶ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst`：isoPullback_inv_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.f
st _ _
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma IsStableUnderBaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (_ : P g),
      ∃ (T : C) (fst : T ⟶ X) (snd : T ⟶ Y), IsPullback fst snd f g ∧ P fst) :
    P.IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ hg ↦ ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

variable (C)
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.isomorphisms C).IsStableUnderBaseChange
参数：C : Type u；CategoryTheory.MorphismProperty.isomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.isIso_snd_of_isIso`：isIso_snd_of_isIso (h : Is
Pullback fst snd f g) (inst : IsIso f
-/
instance IsStableUnderBaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderBaseChange where
  of_isPullback h _ := h.isIso_snd_of_isIso
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.monomorphisms C).IsStableUnderBaseChange
参数：C : Type u；CategoryTheory.MorphismProperty.monomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.mono_snd_of_mono`：mono_snd_of_mono (h : IsPull
back fst snd f g) (inst : Mono f
-/
instance IsStableUnderBaseChange.monomorphisms :
    (monomorphisms C).IsStableUnderBaseChange where
  of_isPullback h _ := h.mono_snd_of_mono

variable {C P}
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) IsStableUnderBaseChange.respectsIso
    [IsStableUnderBaseChange P] : RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
/-
**CategoryTheory.MorphismProperty.pullback_fst** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：pullback_fst {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsSt
ableUnderBaseChangeAlong f] (H : P g) : P (pullback.fst f g)
参数：f : X ⟶ S；g : Y ⟶ S；H : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullba
ck`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory
.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
theorem pullback_fst {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong f] (H : P g) : P (pullback.fst f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g).flip H
/-
**CategoryTheory.MorphismProperty.pullback_snd** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：pullback_snd {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsSt
ableUnderBaseChangeAlong g] (H : P f) : P (pullback.snd f g)
参数：f : X ⟶ S；g : Y ⟶ S；H : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullba
ck`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory
.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
theorem pullback_snd {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong g] (H : P f) : P (pullback.snd f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g) H
/-
**CategoryTheory.MorphismProperty.baseChange_obj** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：baseChange_obj {S S' : C} (f : S' ⟶ S) [HasPullbacksAlong f] [P.IsStableUn
derBaseChangeAlong f] (X : Over S) (H : P X.hom) : P ((Over.pullback f).obj X).h
om
参数：f : S' ⟶ S；X : Over S；H : P X.hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
-/
theorem baseChange_obj {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (X : Over S) (H : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  pullback_snd X.hom f H

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.pullbackLift_fst_snd** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：pullbackLift_fst_snd [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ 
S) {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) [HasPullback v
₁₂ f] [HasPullback v₂₂ f] (H : P g) : P (pullback.lift (f
参数：f : S' ⟶ S；hv₁₂ : v₁₂ = g ≫ v₂₂；H : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackLift_fst_snd [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) [HasPullback v₁₂ f]
    [HasPullback v₂₂ f] (H : P g) : P (pullback.lift (f := v₂₂) (g := f) (pullback.fst v₁₂ f ≫ g)
    (pullback.snd v₁₂ f) (by simp [pullback.condition, ← hv₁₂])) := by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

@[deprecated (since := "2026-03-20")]
alias baseChange_map' := pullbackLift_fst_snd
/-
**CategoryTheory.MorphismProperty.overPullbackMap** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：overPullbackMap [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S) [HasPu
llbacksAlong f] {X Y : Over S} (g : X ⟶ Y) (H : P g.left) : P ((Over.pullback f)
.map g).left
参数：f : S' ⟶ S；g : X ⟶ Y；H : P g.left。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullbackLift_fst_snd`：pullbackLift_fst_s
nd [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S) {v₁₂ : X ⟶ S} {v₂₂ : 
Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheo
ry.CategoryStru…
-/
theorem overPullbackMap [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] {X Y : Over S} (g : X ⟶ Y) (H : P g.left) :
    P ((Over.pullback f).map g).left :=
  pullbackLift_fst_snd f (g.w.symm) H

@[deprecated (since := "2026-03-20")]
alias baseChange_map := overPullbackMap

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] hasPullback_symmetry_of_hasPullbacksAlong in
/-
**CategoryTheory.MorphismProperty.pullbackMap** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：pullbackMap [IsStableUnderBaseChange P] [P.IsStableUnderComposition] {S X 
X' Y Y' : C} {f : X ⟶ S} [HasPullbacksAlong f] {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y
' ⟶ S} {i₁ : X ⟶ X'} [HasPullbacksAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂
) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') : P (pullback.map f g f' g' i₁ i₂ (𝟙 _) 
((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂))
参数：h₁ : P i₁；h₂ : P i₂；e₁ : f = i₁ ≫ f'；e₂ : g = i₂ ≫ g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry_of_hasPullbacksAlong`：hasPull
back_symmetry_of_hasPullbacksAlong {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f]
 {g : Y ⟶ S} : HasPullback f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Over.pullback_map_left`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasPullbacksAlong f] (g : C…
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MorphismProperty.overPullbackMap`：overPullbackMap [IsStab
leUnderBaseChange P] {S S' : C} (f : S' ⟶ S) [HasPullbacksAlong f] {X Y : Over S
} (g : X ⟶ Y) (H : P g.left) : P ((Ov…
-/
theorem pullbackMap
    [IsStableUnderBaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : X ⟶ S}
    [HasPullbacksAlong f] {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'}
    [HasPullbacksAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have : HasPullbacksAlong (Over.mk f).hom := by cat_disch
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((Over.pullback g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [overPullbackMap _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂,
    overPullbackMap _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁]

@[deprecated (since := "2026-03-20")]
alias pullback_map := pullbackMap
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_
monomorphisms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStabl
eUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [P.IsStableUnderBaseChange], P.HasOfPostcompProperty (C
ategoryTheory.MorphismProperty.monomorphisms C)
参数：CategoryTheory.MorphismProperty.monomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
-/
instance IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
    [P.IsStableUnderBaseChange] : P.HasOfPostcompProperty (MorphismProperty.monomorphisms C) where
  of_postcomp {X Y Z} f g (hg : Mono g) hcomp := by
    have : f = (asIso (pullback.fst (f ≫ g) g)).inv ≫ pullback.snd (f ≫ g) g := by
      simp [← cancel_mono g, pullback.condition]
    rw [this, cancel_left_of_respectsIso (P := P)]
    exact P.pullback_snd _ _ hcomp

alias of_isPushout := IsStableUnderCobaseChange.of_isPushout
/-
**CategoryTheory.MorphismProperty.isStableUnderCobaseChange_iff_pushouts_le** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderCobaseChange_iff_pushouts_le : P.IsStableUnderCobaseChange ↔ 
P.pushouts <= P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPushout`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self :
 P.IsStableUnderCobaseChange] {A A…
-/
lemma isStableUnderCobaseChange_iff_pushouts_le :
    P.IsStableUnderCobaseChange ↔ P.pushouts ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPushout h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩
/-
**CategoryTheory.MorphismProperty.pushouts_le** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：pushouts_le [P.IsStableUnderCobaseChange] : P.pushouts <= P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderCobaseChange_iff_pushouts_l
e`：isStableUnderCobaseChange_iff_pushouts_le : P.IsStableUnderCobaseChange ↔ P.p
ushouts <= P
-/
lemma pushouts_le [P.IsStableUnderCobaseChange] : P.pushouts ≤ P := by
  rwa [← isStableUnderCobaseChange_iff_pushouts_le]

@[simp]
/-
**CategoryTheory.MorphismProperty.pushouts_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：pushouts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderCobaseChange] :
 P.pushouts <= Q ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.MorphismProperty.le_pushouts`：le_pushouts : P <= P.pushou
ts
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_monotone`：pushouts_monotone : M
onotone (pushouts (C
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_le`：pushouts_le [P.IsStableUnde
rCobaseChange] : P.pushouts <= P
-/
lemma pushouts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderCobaseChange] :
    P.pushouts ≤ Q ↔ P ≤ Q := by
  constructor
  · exact le_trans P.le_pushouts
  · intro h
    exact le_trans (pushouts_monotone h) pushouts_le

/-- An alternative constructor for `IsStableUnderCobaseChange`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.mk'** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C} [P.RespectsIso],   (∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ 
B) [inst_2 : CategoryTheory.Limits.HasPushout f g],       P f → P (CategoryTheor
y.Limits.pushout.inr f g)) →     P.IsStableUnderCobaseChange
参数：∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) [inst_2 : CategoryTheory.Limits.HasPu
shout f g],       P f → P (CategoryTheory.Limits.pushout.inr f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.hasPushout`：hasPushout (h : IsPushout f g inl i
nr) : HasPushout f g where exists_colimit
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_hom`：inr_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.hom = pushout.inr _ _

--- 原说明 ---
An alternative constructor for `IsStableUnderCobaseChange`.
-/
theorem IsStableUnderCobaseChange.mk' [RespectsIso P]
    (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (_ : P f),
      P (pushout.inr f g)) :
    IsStableUnderCobaseChange P where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    have : HasPushout f g := sq.flip.hasPushout
    let e := sq.flip.isoPushout
    rw [← P.cancel_right_of_respectsIso _ e.hom, sq.flip.inr_isoPushout_hom]
    exact hP₂ _ _ _ f g hf
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.of_forall_exists_isP
ullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnder
CobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C} [P.RespectsIso],   (∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
 [CategoryTheory.Limits.HasPushout f g],       P f → ∃ T inl inr, CategoryTheory
.IsPushout f g inl inr ∧ P inr) →     P.IsStableUnderCobaseChange
参数：∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) [CategoryTheory.Limits.HasPushout f g],
       P f → ∃ T inl inr, CategoryTheory.IsPushout f g inl inr ∧ P inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.mk'`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProp
erty C} [P.RespectsIso],   (∀ (A B A' : C) (f : A ⟶…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_hom`：inr_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.hom = pushout.inr _ _
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma IsStableUnderCobaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] (_ : P f),
      ∃ (T : C) (inl : X ⟶ T) (inr : Y ⟶ T), IsPushout f g inl inr ∧ P inr) :
    P.IsStableUnderCobaseChange := by
  refine .mk' fun X Y S f g _ hg ↦ ?_
  obtain ⟨T, inl, inr, h, hinl⟩ := H f g hg
  rwa [← h.inr_isoPushout_hom, P.cancel_right_of_respectsIso]
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.isomorphisms** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.isomorphisms C).IsStableUnderCobaseChange
参数：CategoryTheory.MorphismProperty.isomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.isIso_inl_of_isIso`：isIso_inl_of_isIso (h : IsP
ushout f g inl inr) (inst : IsIso g
-/
instance IsStableUnderCobaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderCobaseChange where
  of_isPushout h _ := h.isIso_inl_of_isIso

variable (C) in
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.epimorphisms** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.epimorphisms C).IsStableUnderCobaseChange
参数：C : Type u；CategoryTheory.MorphismProperty.epimorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.epi_inl_of_epi`：epi_inl_of_epi (h : IsPushout f
 g inl inr) (inst : Epi g
-/
instance IsStableUnderCobaseChange.epimorphisms :
    (epimorphisms C).IsStableUnderCobaseChange where
  of_isPushout h _ := h.epi_inl_of_epi
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.respectsIso** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [P.IsStableUnderCobaseChange], P.RespectsIso
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.of_respects_arrow_iso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C),   (∀ (f g : CategoryTheory.Arrow C) (x : f…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.of_isPushout`：
∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Mor
phismProperty C}   [self : P.IsStableUnderCobaseChange] {A A…
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso`：of_horiz_isIso [IsIso f] [IsIso
 inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
instance IsStableUnderCobaseChange.respectsIso
    [IsStableUnderCobaseChange P] : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e ↦
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))
/-
**CategoryTheory.MorphismProperty.pushout_inl** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：pushout_inl {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] [P.IsSt
ableUnderCobaseChangeAlong f] (H : P g) : P (pushout.inl f g)
参数：f : A ⟶ A'；g : A ⟶ B；H : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPush
out`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheor
y.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
theorem pushout_inl {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
    [P.IsStableUnderCobaseChangeAlong f] (H : P g) :
    P (pushout.inl f g) :=
  IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g) H
/-
**CategoryTheory.MorphismProperty.pushout_inr** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：pushout_inr {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] [P.IsSt
ableUnderCobaseChangeAlong g] (H : P f) : P (pushout.inr f g)
参数：f : A ⟶ A'；g : A ⟶ B；H : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPush
out`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheor
y.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
theorem pushout_inr {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
    [P.IsStableUnderCobaseChangeAlong g] (H : P f) : P (pushout.inr f g) :=
  IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g).flip H

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.pushoutDesc_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：pushoutDesc_inl_inr [IsStableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ 
S') {v₁₂ : S ⟶ X} {v₂₂ : S ⟶ Y} {g : Y ⟶ X} (hv₁₂ : v₁₂ = v₂₂ ≫ g) [HasPushout v
₁₂ f] [HasPushout v₂₂ f] (H : P g) : P (pushout.desc (f
参数：f : S ⟶ S'；hv₁₂ : v₁₂ = v₂₂ ≫ g；H : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPush
out`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheor
y.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAlongOfIsSt
ableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] {X Y : C
} (…
· 使用定理 `CategoryTheory.IsPushout.of_top`：of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h
₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂
 ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutDesc_inl_inr [IsStableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ S')
    {v₁₂ : S ⟶ X} {v₂₂ : S ⟶ Y} {g : Y ⟶ X} (hv₁₂ : v₁₂ = v₂₂ ≫ g) [HasPushout v₁₂ f]
    [HasPushout v₂₂ f] (H : P g) :
    P (pushout.desc (f := v₂₂) (g := f) (g ≫ pushout.inl v₁₂ f)
      (pushout.inr v₁₂ f) (by simp [pushout.condition, ← reassoc_of% hv₁₂])) := by
  subst hv₁₂
  refine IsStableUnderCobaseChangeAlong.of_isPushout (f' := pushout.inl (v₂₂ ≫ g) f)
    (f := pushout.inl v₂₂ f) ?_ H
  refine IsPushout.of_top ?_ (by simp) (IsPushout.of_hasPushout v₂₂ f).flip
  simpa using (IsPushout.of_hasPushout (v₂₂ ≫ g) f).flip
/-
**CategoryTheory.MorphismProperty.underPushoutMap** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：underPushoutMap [IsStableUnderCobaseChange P] {S S' : C} (f : S' ⟶ S) [Has
PushoutsAlong f] {X Y : Under S'} (g : X ⟶ Y) (H : P g.right) : P ((Under.pushou
t f).map g).right
参数：f : S' ⟶ S；g : X ⟶ Y；H : P g.right。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pushoutDesc_inl_inr`：pushoutDesc_inl_inr
 [IsStableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ S') {v₁₂ : S ⟶ X} {v₂₂ : 
S ⟶ Y} {g : Y ⟶ X} (hv₁₂ : v₁₂ = v₂₂ ≫ g)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Under.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Under X} (φ : f ⟶ g),   CategoryTh
eory.CategoryStr…
-/
theorem underPushoutMap [IsStableUnderCobaseChange P] {S S' : C} (f : S' ⟶ S)
    [HasPushoutsAlong f] {X Y : Under S'} (g : X ⟶ Y) (H : P g.right) :
    P ((Under.pushout f).map g).right :=
  pushoutDesc_inl_inr f g.w.symm H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] hasPushouts_symmetry_of_hasPushoutsAlong in
/-
**CategoryTheory.MorphismProperty.pushoutMap** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：pushoutMap [IsStableUnderCobaseChange P] [P.IsStableUnderComposition] {S X
 X' Y Y' : C} {f : S ⟶ X} {g : S ⟶ Y} {f' : S ⟶ X'} {g' : S ⟶ Y'} {i₁ : X ⟶ X'} 
[HasPushoutsAlong f] [HasPushoutsAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
 (e₁ : f' = f ≫ i₁) (e₂ : g' = g ≫ i₂) : P (pushout.map f g f' g' i₁ i₂ (𝟙 _) (b
y simp [e₁]) (by simp [e₂]))
参数：h₁ : P i₁；h₂ : P i₂；e₁ : f' = f ≫ i₁；e₂ : g' = g ≫ i₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.hasPushouts_symmetry_of_hasPushoutsAlong`：hasPusho
uts_symmetry_of_hasPushoutsAlong {S X Y : C} {f : S ⟶ X} [HasPushoutsAlong f] {g
 : S ⟶ Y} : HasPushout f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.respectsIso`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morp
hismProperty C}   [P.IsStableUnderCobaseChange], P.Respects…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MorphismProperty.underPushoutMap`：underPushoutMap [IsStab
leUnderCobaseChange P] {S S' : C} (f : S' ⟶ S) [HasPushoutsAlong f] {X Y : Under
 S'} (g : X ⟶ Y) (H : P g.right) : P …
-/
theorem pushoutMap
    [IsStableUnderCobaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : S ⟶ X}
    {g : S ⟶ Y} {f' : S ⟶ X'} {g' : S ⟶ Y'} {i₁ : X ⟶ X'} [HasPushoutsAlong f]
    [HasPushoutsAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f' = f ≫ i₁) (e₂ : g' = g ≫ i₂) :
    P (pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂])) := by
  have : HasPushoutsAlong (Under.mk g').hom := by cat_disch
  have : pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂]) =
      ((pushoutSymmetry _ _).hom ≫
        ((Under.pushout f).map (Under.homMk _ e₂.symm : Under.mk g ⟶ Under.mk g')).right) ≫
        (pushoutSymmetry _ _).hom ≫
        ((Under.pushout g').map (Under.homMk _ e₁.symm : Under.mk f ⟶ Under.mk f')).right := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [underPushoutMap _ _ h₂, underPushoutMap _ _ h₁]
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.hasOfPrecompProperty
_epimorphisms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStabl
eUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [P.IsStableUnderCobaseChange], P.HasOfPrecompProperty (
CategoryTheory.MorphismProperty.epimorphisms C)
参数：CategoryTheory.MorphismProperty.epimorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.asIso_inv`：asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).in
v = inv f
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.respectsIso`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morp
hismProperty C}   [P.IsStableUnderCobaseChange], P.Respects…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.pushout_inr`：pushout_inr {A B A' : C} (f
 : A ⟶ A') (g : A ⟶ B) [HasPushout f g] [P.IsStableUnderCobaseChangeAlong g] (H 
: P f) : P (pushout.inr f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAlongOfIsSt
ableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] {X Y : C
} (…
-/
instance IsStableUnderCobaseChange.hasOfPrecompProperty_epimorphisms
    [P.IsStableUnderCobaseChange] : P.HasOfPrecompProperty (MorphismProperty.epimorphisms C) where
  of_precomp {X Y Z} f g (hf : Epi f) hcomp := by
    have : g = pushout.inr (f ≫ g) f ≫ (asIso (pushout.inl (f ≫ g) f)).inv := by
      rw [asIso_inv, IsIso.eq_comp_inv, ← cancel_epi f, ← pushout.condition, assoc]
    rw [this, cancel_right_of_respectsIso (P := P)]
    exact P.pushout_inr _ _ hcomp
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.op** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [P.IsStableUnderCobaseChange], P.op.IsStableUnderBaseCh
ange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPushout`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self :
 P.IsStableUnderCobaseChange] {A A…
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
-/
instance IsStableUnderCobaseChange.op [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.op where
  of_isPullback sq hg := P.of_isPushout sq.unop hg
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.unop** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty Cᵒᵖ}   [P.IsStableUnderCobaseChange], P.unop.IsStableUnderBa
seChange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPushout`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self :
 P.IsStableUnderCobaseChange] {A A…
· 使用定理 `CategoryTheory.IsPullback.op`：op (h : IsPullback fst snd f g) : IsPushou
t g.op f.op snd.op fst.op
-/
instance IsStableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.unop where
  of_isPullback sq hg := P.of_isPushout sq.op hg
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.op** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [P.IsStableUnderBaseChange], P.op.IsStableUnderCobaseCh
ange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPushout.unop`：unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶
 Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) : IsPullback inr.uno
p inl.unop g.unop f…
-/
instance IsStableUnderBaseChange.op [IsStableUnderBaseChange P] :
    IsStableUnderCobaseChange P.op where
  of_isPushout sq hf := P.of_isPullback sq.unop hf
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.unop** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty Cᵒᵖ}   [P.IsStableUnderBaseChange], P.unop.IsStableUnderCoba
seChange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
-/
instance IsStableUnderBaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderBaseChange P] :
    IsStableUnderCobaseChange P.unop where
  of_isPushout sq hf := P.of_isPullback sq.op hf
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTh
eory.MorphismProperty C}   [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChang
e], (P ⊓ Q).IsStableUnderBaseChange
参数：P ⊓ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morp
hismProperty C}   [self : P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance IsStableUnderBaseChange.inf {P Q : MorphismProperty C} [IsStableUnderBaseChange P]
    [IsStableUnderBaseChange Q] :
    IsStableUnderBaseChange (P ⊓ Q) where
  of_isPullback hp hg := ⟨of_isPullback hp hg.left, of_isPullback hp hg.right⟩
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.inf** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTh
eory.MorphismProperty C}   [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseC
hange], (P ⊓ Q).IsStableUnderCobaseChange
参数：P ⊓ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.of_isPushout`：
∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Mor
phismProperty C}   [self : P.IsStableUnderCobaseChange] {A A…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance IsStableUnderCobaseChange.inf {P Q : MorphismProperty C} [IsStableUnderCobaseChange P]
    [IsStableUnderCobaseChange Q] :
    IsStableUnderCobaseChange (P ⊓ Q) where
  of_isPushout hp hg := ⟨of_isPushout hp hg.left, of_isPushout hp hg.right⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : MorphismProperty C).IsStableUnderCobaseChange where
  of_isPushout _ _ := trivial

end

section LimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category* J]

/-- The class of morphisms in `C` that are limits of shape `J` of
natural transformations involving morphisms in `W`. -/
/-
**CategoryTheory.MorphismProperty.limitsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C →       (J : Type u_1) → [CategoryTheory.Category.{v_1,
 u_1} J] → CategoryTheory.MorphismProperty C
参数：J : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms in `C` that are limits of shape `J` of
natural transformations involving morphisms in `W`.
-/
inductive limitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      limitsOfShape (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

variable {W J} in
/-
**CategoryTheory.MorphismProperty.limitsOfShape.mk'** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.limitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type u_1}   [inst_1 : CategoryTheory.Category.{v_1, 
u_1} J] (X₁ X₂ : CategoryTheory.Functor J C)   (c₁ : CategoryTheory.Limits.Cone 
X₁) (c₂ : CategoryTheory.Limits.Cone X₂) (h₁ : CategoryTheory.Limits.IsLimit c₁)
   (h₂ : CategoryTheory.Limits.IsLimit c₂) (f : X₁ ⟶ X₂),   W.functorCategory J 
f →     ∀ (φ : c₁.pt ⟶ c₂.pt),       (∀ (j : J),           CategoryTheory.Catego
ryStruct.comp φ (c₂.π.app j) =             CategoryTheory.CategoryStruct.comp (c
₁.π.app j) (f.app j)) →         W.limitsOfShape J φ
参数：X₁ X₂ : CategoryTheory.Functor J C；c₁ : CategoryTheory.Limits.Cone X₁；c₂ : Ca
tegoryTheory.Limits.Cone X₂；h₁ : CategoryTheory.Limits.IsLimit c₁；h₂ : CategoryT
heory.Limits.IsLimit c₂；f : X₁ ⟶ X₂；φ : c₁.pt ⟶ c₂.pt；∀ (j : J),           Categ
oryTheory.CategoryStruct.comp φ (c₂.π.app j) =             CategoryTheory.Catego
ryStruct.comp (c₁.π.app j) (f.app j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma limitsOfShape.mk' (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (hf : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) :
    W.limitsOfShape J φ := by
  obtain rfl : φ = h₂.lift (Cone.mk _ (c₁.π ≫ f)) := h₂.hom_ext (fun j ↦ by simp [hφ])
  exact ⟨_, _, _, _, h₁, _, _, hf⟩
/-
**CategoryTheory.MorphismProperty.limitsOfShape_monotone** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：limitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂) (J : Ty
pe*) [Category* J] : W₁.limitsOfShape J <= W₂.limitsOfShape J
参数：h : W₁ <= W₂；J : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma limitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂)
    (J : Type*) [Category* J] :
    W₁.limitsOfShape J ≤ W₂.limitsOfShape J := by
  rintro _ _ _ ⟨_, _, _, _, h₁, _, f, hf⟩
  exact ⟨_, _, _, _, h₁, _, f, fun j ↦ h _ (hf j)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (W.limitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : g ≫ e₂.inv = e₁.inv ≫ h₂.lift (Cone.mk _ (c₁.π ≫ f)) :=
      e.inv.w.symm
    let c₁' : Cone X₁ := { pt := Y₁, π := (Functor.const _).map e₁.inv ≫ c₁.π }
    let c₂' : Cone X₂ := { pt := Y₂, π := (Functor.const _).map e₂.inv ≫ c₂.π }
    have h₁' : IsLimit c₁' := IsLimit.ofIsoLimit h₁ (Cone.ext e₁)
    have h₂' : IsLimit c₂' := IsLimit.ofIsoLimit h₂ (Cone.ext e₂)
    obtain hg : h₂'.lift (Cone.mk _ (c₁'.π ≫ f)) = g :=
      h₂'.hom_ext (fun j ↦ by
        rw [h₂'.fac]
        simp [reassoc_of% fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, h₁', _, _, hf⟩)

variable {W J} in
/-
**CategoryTheory.MorphismProperty.limitsOfShape_limMap** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：limitsOfShape_limMap {X Y : J ⥤ C} (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (
hf : W.functorCategory _ f) : W.limitsOfShape J (limMap f)
参数：f : X ⟶ Y；hf : W.functorCategory _ f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitsOfShape_limMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W.limitsOfShape J (limMap f) :=
  ⟨_, _, _, _, limit.isLimit X, _, _, hf⟩

/-- The property that a morphism property `W` is stable under limits
indexed by a category `J`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderLimitsOfShape** 是 Mathlib 中的一个归纳类
型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → (J : Type u_1) → [CategoryTheory.Category.{v_1, u_1} 
J] → Prop
参数：J : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism property `W` is stable under limits
indexed by a category `J`.
-/
class IsStableUnderLimitsOfShape : Prop where
  condition (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) : W φ
/-
**CategoryTheory.MorphismProperty.isStableUnderLimitsOfShape_iff_limitsOfShape_l
e** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderLimitsOfShape_iff_limitsOfShape_le : W.IsStableUnderLimitsOfS
hape J ↔ W.limitsOfShape J <= W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderLimitsOfShape.condition`：∀ 
{C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morph
ismProperty C} {J : Type u_1}   {inst_1 : CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.MorphismProperty.limitsOfShape.mk'`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {J :
 Type u_1}   [inst_1 : CategoryTheory.C…
-/
lemma isStableUnderLimitsOfShape_iff_limitsOfShape_le :
    W.IsStableUnderLimitsOfShape J ↔ W.limitsOfShape J ≤ W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (limitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

variable {W J}
/-
**CategoryTheory.MorphismProperty.limitsOfShape_le** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：limitsOfShape_le [W.IsStableUnderLimitsOfShape J] : W.limitsOfShape J <= W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderLimitsOfShape_iff_limitsOfS
hape_le`：isStableUnderLimitsOfShape_iff_limitsOfShape_le : W.IsStableUnderLimits
OfShape J ↔ W.limitsOfShape J <= W
-/
lemma limitsOfShape_le [W.IsStableUnderLimitsOfShape J] :
    W.limitsOfShape J ≤ W := by
  rwa [← isStableUnderLimitsOfShape_iff_limitsOfShape_le]
/-
**CategoryTheory.MorphismProperty.limMap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.MorphismProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type u_1}   [inst_1 : CategoryTheory.Category.{v_1, 
u_1} J] [W.IsStableUnderLimitsOfShape J] {X Y : CategoryTheory.Functor J C}   (f
 : X ⟶ Y) [inst_3 : CategoryTheory.Limits.HasLimit X] [inst_4 : CategoryTheory.L
imits.HasLimit Y],   W.functorCategory J f → W (CategoryTheory.Limits.limMap f)
参数：f : X ⟶ Y；CategoryTheory.Limits.limMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.limitsOfShape_le`：limitsOfShape_le [W.Is
StableUnderLimitsOfShape J] : W.limitsOfShape J <= W
· 使用引理 `CategoryTheory.MorphismProperty.limitsOfShape_limMap`：limitsOfShape_limM
ap {X Y : J ⥤ C} (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _
 f) : W.limitsOfShape J (limMap f)
-/
protected lemma limMap [W.IsStableUnderLimitsOfShape J] {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W (limMap f) :=
  limitsOfShape_le _ (limitsOfShape_limMap _ hf)

end LimitsOfShape

section ColimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category* J]

/-- The class of morphisms in `C` that are colimits of shape `J` of
natural transformations involving morphisms in `W`. -/
/-
**CategoryTheory.MorphismProperty.colimitsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C →       (J : Type u_1) → [CategoryTheory.Category.{v_1,
 u_1} J] → CategoryTheory.MorphismProperty C
参数：J : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms in `C` that are colimits of shape `J` of
natural transformations involving morphisms in `W`.
-/
inductive colimitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      colimitsOfShape (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

set_option backward.isDefEq.respectTransparency false in
variable {W J} in
/-
**CategoryTheory.MorphismProperty.colimitsOfShape.mk'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.colimitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type u_1}   [inst_1 : CategoryTheory.Category.{v_1, 
u_1} J] (X₁ X₂ : CategoryTheory.Functor J C)   (c₁ : CategoryTheory.Limits.Cocon
e X₁) (c₂ : CategoryTheory.Limits.Cocone X₂)   (h₁ : CategoryTheory.Limits.IsCol
imit c₁) (h₂ : CategoryTheory.Limits.IsColimit c₂) (f : X₁ ⟶ X₂),   W.functorCat
egory J f →     ∀ (φ : c₁.pt ⟶ c₂.pt),       (∀ (j : J),           CategoryTheor
y.CategoryStruct.comp (c₁.ι.app j) φ =             CategoryTheory.CategoryStruct
.comp (f.app j) (c₂.ι.app j)) →         W.colimitsOfShape J φ
参数：X₁ X₂ : CategoryTheory.Functor J C；c₁ : CategoryTheory.Limits.Cocone X₁；c₂ : 
CategoryTheory.Limits.Cocone X₂；h₁ : CategoryTheory.Limits.IsColimit c₁；h₂ : Cat
egoryTheory.Limits.IsColimit c₂；f : X₁ ⟶ X₂；φ : c₁.pt ⟶ c₂.pt；∀ (j : J),        
   CategoryTheory.CategoryStruct.comp (c₁.ι.app j) φ =             CategoryTheor
y.CategoryStruct.comp (f.app j) (c₂.ι.app j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma colimitsOfShape.mk' (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (hf : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    W.colimitsOfShape J φ := by
  obtain rfl : φ = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) := h₁.hom_ext (fun j ↦ by simp [hφ])
  exact ⟨_, _, _, _, _, h₂, _, hf⟩
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_monotone** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂) (J : 
Type*) [Category* J] : W₁.colimitsOfShape J <= W₂.colimitsOfShape J
参数：h : W₁ <= W₂；J : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma colimitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂)
    (J : Type*) [Category* J] :
    W₁.colimitsOfShape J ≤ W₂.colimitsOfShape J := by
  rintro _ _ _ ⟨_, _, _, _, _, h₂, f, hf⟩
  exact ⟨_, _, _, _, _, h₂, f, fun j ↦ h _ (hf j)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {J} in
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_le_of_final** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_le_of_final {J' : Type*} [Category* J'] (F : J ⥤ J') [F.Fi
nal] : W.colimitsOfShape J' <= W.colimitsOfShape J
参数：F : J ⥤ J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma colimitsOfShape_le_of_final {J' : Type*} [Category* J'] (F : J ⥤ J') [F.Final] :
    W.colimitsOfShape J' ≤ W.colimitsOfShape J := by
  intro _ _ _ ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
  have h₁' : IsColimit (c₁.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₁).symm h₁
  have h₂' : IsColimit (c₂.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₂).symm h₂
  have : h₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι)) =
      h₁'.desc (Cocone.mk c₂.pt (Functor.whiskerLeft _ f ≫ (c₂.whisker F).ι)) :=
    h₁'.hom_ext (fun j ↦ by
      have := h₁'.fac (Cocone.mk c₂.pt (Functor.whiskerLeft F f ≫ Functor.whiskerLeft F c₂.ι)) j
      dsimp at this ⊢
      simp [this])
  rw [this]
  exact ⟨_, _, _, _, h₁', h₂', _, fun _ ↦ hf _⟩

variable {J} in
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_eq_of_equivalence** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_eq_of_equivalence {J' : Type*} [Category* J'] (e : J ≌ J')
 : W.colimitsOfShape J = W.colimitsOfShape J'
参数：e : J ≌ J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le_of_final`：colimitsOfS
hape_le_of_final {J' : Type*} [Category* J'] (F : J ⥤ J') [F.Final] : W.colimits
OfShape J' <= W.colimitsOfShape J
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma colimitsOfShape_eq_of_equivalence {J' : Type*} [Category* J'] (e : J ≌ J') :
    W.colimitsOfShape J = W.colimitsOfShape J' :=
  le_antisymm (W.colimitsOfShape_le_of_final e.inverse)
    (W.colimitsOfShape_le_of_final e.functor)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (W.colimitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : e₁.hom ≫ g = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) ≫ e₂.hom := e.hom.w
    let c₁' : Cocone X₁ := { pt := Y₁, ι := c₁.ι ≫ (Functor.const _).map e₁.hom }
    let c₂' : Cocone X₂ := { pt := Y₂, ι := c₂.ι ≫ (Functor.const _).map e₂.hom }
    have h₁' : IsColimit c₁' := IsColimit.ofIsoColimit h₁ (Cocone.ext e₁)
    have h₂' : IsColimit c₂' := IsColimit.ofIsoColimit h₂ (Cocone.ext e₂)
    obtain hg : h₁'.desc (Cocone.mk _ (f ≫ c₂'.ι)) = g :=
      h₁'.hom_ext (fun j ↦ by
        rw [h₁'.fac]
        simp [fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, _, h₂', _, hf⟩)

variable {W J} in
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_colimMap** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_colimMap {X Y : J ⥤ C} (f : X ⟶ Y) [HasColimit X] [HasColi
mit Y] (hf : W.functorCategory _ f) : W.colimitsOfShape J (colimMap f)
参数：f : X ⟶ Y；hf : W.functorCategory _ f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma colimitsOfShape_colimMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W.colimitsOfShape J (colimMap f) :=
  ⟨_, _, _, _, _, colimit.isColimit Y, _, hf⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local instance] IsCofiltered.isConnected in
variable {W} in
/-
**CategoryTheory.MorphismProperty.colimitsOfShape.of_isColimit** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty.colimitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type u_2}   [inst_1 : Preorder J] [inst_2 : OrderBot
 J] {F : CategoryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone F}   (hc 
: CategoryTheory.Limits.IsColimit c),   (∀ (j : J), W (F.map (CategoryTheory.hom
OfLE ⋯))) → W.colimitsOfShape J (c.ι.app ⊥)
参数：hc : CategoryTheory.Limits.IsColimit c；∀ (j : J), W (F.map (CategoryTheory.ho
mOfLE ⋯))；c.ι.app ⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `CategoryTheory.MorphismProperty.colimitsOfShape.mk'`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {J
 : Type u_1}   [inst_1 : CategoryTheory.C…
· 使用定理 `CategoryTheory.IsCofiltered.isConnected`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsCofiltered C], CategoryTheory.IsConn
ected C
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `OrderBot.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : LE α] [OrderBot
 α], IsCodirectedOrder α
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma colimitsOfShape.of_isColimit
    {J : Type*} [Preorder J] [OrderBot J] {F : J ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (h : ∀ (j : J), W (F.map (homOfLE bot_le : ⊥ ⟶ j))) :
    W.colimitsOfShape J (c.ι.app ⊥) :=
  .mk' _ _ _ _ (isColimitConstCocone J (F.obj ⊥)) hc
    { app k := F.map (homOfLE bot_le)
      naturality _ _ _ := by
        dsimp
        rw [Category.id_comp, ← Functor.map_comp]
        rfl } h _ (by simp)

/-- The property that a morphism property `W` is stable under colimits
indexed by a category `J`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderColimitsOfShape** 是 Mathlib 中的一个归
纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → (J : Type u_1) → [CategoryTheory.Category.{v_1, u_1} 
J] → Prop
参数：J : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism property `W` is stable under colimits
indexed by a category `J`.
-/
class IsStableUnderColimitsOfShape : Prop where
  condition (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₁ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : W φ

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfSha
pe_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderColimitsOfShape_iff_colimitsOfShape_le : W.IsStableUnderColim
itsOfShape J ↔ W.colimitsOfShape J <= W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderColimitsOfShape.condition`：
∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Mor
phismProperty C} {J : Type u_1}   {inst_1 : CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.MorphismProperty.colimitsOfShape.mk'`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {J
 : Type u_1}   [inst_1 : CategoryTheory.C…
-/
lemma isStableUnderColimitsOfShape_iff_colimitsOfShape_le :
    W.IsStableUnderColimitsOfShape J ↔ W.colimitsOfShape J ≤ W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (colimitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

variable {W J}
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_le** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_le [W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape 
J <= W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderColimitsOfShape_iff_colimit
sOfShape_le`：isStableUnderColimitsOfShape_iff_colimitsOfShape_le : W.IsStableUnd
erColimitsOfShape J ↔ W.colimitsOfShape J <= W
-/
lemma colimitsOfShape_le [W.IsStableUnderColimitsOfShape J] :
    W.colimitsOfShape J ≤ W := by
  rwa [← isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
/-
**CategoryTheory.MorphismProperty.colimMap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type u_1}   [inst_1 : CategoryTheory.Category.{v_1, 
u_1} J] [W.IsStableUnderColimitsOfShape J] {X Y : CategoryTheory.Functor J C}   
(f : X ⟶ Y) [inst_3 : CategoryTheory.Limits.HasColimit X] [inst_4 : CategoryTheo
ry.Limits.HasColimit Y],   W.functorCategory J f → W (CategoryTheory.Limits.coli
mMap f)
参数：f : X ⟶ Y；CategoryTheory.Limits.colimMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le`：colimitsOfShape_le [
W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape J <= W
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_colimMap`：colimitsOfShap
e_colimMap {X Y : J ⥤ C} (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.funct
orCategory _ f) : W.colimitsOfShape J (colimMa…
-/
protected lemma colimMap [W.IsStableUnderColimitsOfShape J] {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W (colimMap f) :=
  colimitsOfShape_le _ (colimitsOfShape_colimMap _ hf)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C J) in
/-
**CategoryTheory.MorphismProperty.IsStableUnderColimitsOfShape.isomorphisms** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderColimitsOfSh
ape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (J : Type u_1) [i
nst_1 : CategoryTheory.Category.{v_1, u_1} J],   (CategoryTheory.MorphismPropert
y.isomorphisms C).IsStableUnderColimitsOfShape J
参数：C : Type u；J : Type u_1；CategoryTheory.MorphismProperty.isomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsColimit.fac_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance IsStableUnderColimitsOfShape.isomorphisms :
    (isomorphisms C).IsStableUnderColimitsOfShape J where
  condition F₁ F₂ c₁ c₂ h₁ h₂ f (_ : ∀ j, IsIso (f.app j)) φ hφ := by
    have := NatIso.isIso_of_isIso_app f
    exact ⟨h₂.desc (Cocone.mk _ (inv f ≫ c₁.ι)),
      h₁.hom_ext (fun j ↦ by simp [reassoc_of% (hφ j)]),
      h₂.hom_ext (by simp [hφ])⟩

end ColimitsOfShape

/-- The condition that a property of morphisms is stable by filtered colimits. -/
@[pp_with_univ]
/-
**CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits** 是 Mathlib 中的一个
类，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsStableUnderFilteredColimits (W : MorphismProperty C) : Prop where isStab
leUnderColimitsOfShape (J : Type w') [Category.{w} J] [IsFiltered J] : W.IsStabl
eUnderColimitsOfShape J
参数：W : MorphismProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a property of morphisms is stable by filtered colimits.
-/
class IsStableUnderFilteredColimits (W : MorphismProperty C) : Prop where
  isStableUnderColimitsOfShape (J : Type w') [Category.{w} J] [IsFiltered J] :
    W.IsStableUnderColimitsOfShape J := by infer_instance

attribute [instance] IsStableUnderFilteredColimits.isStableUnderColimitsOfShape
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderFilteredColimits.{w, w'} (isomorphisms C) where

section Coproducts

variable (W : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is class of morphisms that are
isomorphic to a coproduct of a family (indexed by some `J : Type w`) of maps in `W`. -/
@[pp_with_univ]
/-
**CategoryTheory.MorphismProperty.coproducts** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：coproducts : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : MorphismProperty C`, this is class of morphisms that are
isomorphic to a coproduct of a family (indexed by some `J : Type w`) of maps in 
`W`.
-/
def coproducts : MorphismProperty C := ⨆ (J : Type w), W.colimitsOfShape (Discrete J)
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_le_coproducts** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_le_coproducts (J : Type w) : W.colimitsOfShape (Discrete J
) <= coproducts.{w} W
参数：J : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma colimitsOfShape_le_coproducts (J : Type w) :
    W.colimitsOfShape (Discrete J) ≤ coproducts.{w} W :=
  le_iSup (f := fun (J : Type w) ↦ W.colimitsOfShape (Discrete J)) J
/-
**CategoryTheory.MorphismProperty.coproducts_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：coproducts_iff {X Y : C} (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Ty
pe w), W.colimitsOfShape (Discrete J) f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coproducts_iff {X Y : C} (f : X ⟶ Y) :
    coproducts.{w} W f ↔ ∃ (J : Type w), W.colimitsOfShape (Discrete J) f := by
  simp only [coproducts, iSup_iff]
/-
**CategoryTheory.MorphismProperty.coproducts_of_small** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：coproducts_of_small {X Y : C} (f : X ⟶ Y) {J : Type w'} (hf : W.colimitsOf
Shape (Discrete J) f) [Small.{w} J] : coproducts.{w} W f
参数：f : X ⟶ Y；hf : W.colimitsOfShape (Discrete J) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_iff`：coproducts_iff {X Y : C}
 (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Disc
rete J) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_eq_of_equivalence`：colim
itsOfShape_eq_of_equivalence {J' : Type*} [Category* J'] (e : J ≌ J') : W.colimi
tsOfShape J = W.colimitsOfShape J'
-/
lemma coproducts_of_small {X Y : C} (f : X ⟶ Y) {J : Type w'}
    (hf : W.colimitsOfShape (Discrete J) f) [Small.{w} J] :
    coproducts.{w} W f := by
  rw [coproducts_iff]
  refine ⟨Shrink J, ?_⟩
  rwa [← W.colimitsOfShape_eq_of_equivalence (Discrete.equivalence (equivShrink.{w} J))]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.le_colimitsOfShape_punit** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：le_colimitsOfShape_punit : W <= W.colimitsOfShape (Discrete PUnit.{w + 1})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.IsInitial.to_self`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X),   
t.to X = CategoryTheory.Categ…
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `PUnit.ext`：∀ (a b : PUnit.{u_1}), a = b
-/
lemma le_colimitsOfShape_punit : W ≤ W.colimitsOfShape (Discrete PUnit.{w + 1}) := by
  intro X₁ X₂ f hf
  have h := initialIsInitial (C := Discrete (PUnit.{w + 1}))
  let c₁ := coconeOfDiagramInitial (F := Discrete.functor (fun _ ↦ X₁)) h
  let c₂ := coconeOfDiagramInitial (F := Discrete.functor (fun _ ↦ X₂)) h
  have hc₁ : IsColimit c₁ := colimitOfDiagramInitial h _
  have hc₂ : IsColimit c₂ := colimitOfDiagramInitial h _
  have : hc₁.desc (Cocone.mk _ (Discrete.natTrans (fun _ ↦ by exact f) ≫ c₂.ι)) = f :=
    hc₁.hom_ext (fun x ↦ by
      obtain rfl : x = ⊥_ _ := by ext
      rw [IsColimit.fac]
      simp [c₁, c₂])
  rw [← this]
  exact ⟨_, _, _, _, _, hc₂, _, fun _ ↦ hf⟩
/-
**CategoryTheory.MorphismProperty.le_coproducts** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：le_coproducts : W <= coproducts.{w} W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.MorphismProperty.le_colimitsOfShape_punit`：le_colimitsOfS
hape_punit : W <= W.colimitsOfShape (Discrete PUnit.{w + 1})
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le_coproducts`：colimitsO
fShape_le_coproducts (J : Type w) : W.colimitsOfShape (Discrete J) <= coproducts
.{w} W
-/
lemma le_coproducts : W ≤ coproducts.{w} W :=
  (le_colimitsOfShape_punit.{w} W).trans
    (colimitsOfShape_le_coproducts W PUnit.{w + 1})
/-
**CategoryTheory.MorphismProperty.coproducts_monotone** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：coproducts_monotone : Monotone (coproducts.{w} (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_iff`：coproducts_iff {X Y : C}
 (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Disc
rete J) f
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le_coproducts`：colimitsO
fShape_le_coproducts (J : Type w) : W.colimitsOfShape (Discrete J) <= coproducts
.{w} W
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_monotone`：colimitsOfShap
e_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂) (J : Type*) [Category* J]
 : W₁.colimitsOfShape J <= W₂.colimitsOfShape …
-/
lemma coproducts_monotone : Monotone (coproducts.{w} (C := C)) := by
  rintro W₁ W₂ h X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact W₂.colimitsOfShape_le_coproducts J _
    (colimitsOfShape_monotone h _ _ hf)

end Coproducts

section Products

variable (W : MorphismProperty C)

/-- The property that a morphism property `W` is stable under products indexed by a type `J`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderProductsOfShape** 是 Mathlib 中的一个缩
写定义，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsStableUnderProductsOfShape (J : Type*)
参数：J : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism property `W` is stable under products indexed by a 
type `J`.
-/
abbrev IsStableUnderProductsOfShape (J : Type*) := W.IsStableUnderLimitsOfShape (Discrete J)

/-- The property that a morphism property `W` is stable under coproducts indexed by a type `J`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderCoproductsOfShape** 是 Mathlib 中的一
个缩写定义，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsStableUnderCoproductsOfShape (J : Type*)
参数：J : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism property `W` is stable under coproducts indexed by 
a type `J`.
-/
abbrev IsStableUnderCoproductsOfShape (J : Type*) := W.IsStableUnderColimitsOfShape (Discrete J)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsStableUnderProductsOfShape.mk** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderProductsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheo
ry.MorphismProperty C) (J : Type u_1)   [W.RespectsIso],   (∀ (X₁ X₂ : J → C) [i
nst_2 : CategoryTheory.Limits.HasProduct X₁] [inst_3 : CategoryTheory.Limits.Has
Product X₂]       (f : (j : J) → X₁ j ⟶ X₂ j), (∀ (j : J), W (f j)) → W (Categor
yTheory.Limits.Pi.map f)) →     W.IsStableUnderProductsOfShape J
参数：W : CategoryTheory.MorphismProperty C；J : Type u_1；∀ (X₁ X₂ : J → C) [inst_2 
: CategoryTheory.Limits.HasProduct X₁] [inst_3 : CategoryTheory.Limits.HasProduc
t X₂]       (f : (j : J) → X₁ j ⟶ X₂ j), (∀ (j : J), W (f j)) → W (CategoryTheor
y.Limits.Pi.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.Pi.isoLimit_inv_π_assoc`：∀ {α : Type w₂} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   (X : CategoryTheory.Functor (Cat
egoryTheory.Discrete α) C)   [inst_…
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp_assoc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Ca
tegoryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Pi.isoLimit_inv_π`：∀ {α : Type w₂} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   (X : CategoryTheory.Functor (CategoryT
heory.Discrete α) C)   [inst_…
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsStableUnderProductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : ∀ (X₁ X₂ : J → C) [HasProduct X₁] [HasProduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Pi.map f)) : W.IsStableUnderProductsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf α hα := by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasLimit X₁ := ⟨c₁, hc₁⟩
    have : HasLimit X₂ := ⟨c₂, hc₂⟩
    have : HasProduct fun j ↦ X₁.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₁.obj j)))
    have : HasProduct fun j ↦ X₂.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₂.obj j)))
    have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
    refine (W.arrow_mk_iso_iff ?_).2 hf'
    refine Arrow.isoMk
      (IsLimit.conePointUniqueUpToIso hc₁ (limit.isLimit X₁) ≪≫ (Pi.isoLimit X₁).symm)
      (IsLimit.conePointUniqueUpToIso hc₂ (limit.isLimit X₂) ≪≫ (Pi.isoLimit _).symm) ?_
    apply limit.hom_ext
    rintro ⟨j⟩
    simp [φ, hα]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsStableUnderCoproductsOfShape.mk** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderCoproductsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheo
ry.MorphismProperty C) (J : Type u_1)   [W.RespectsIso],   (∀ (X₁ X₂ : J → C) [i
nst_2 : CategoryTheory.Limits.HasCoproduct X₁] [inst_3 : CategoryTheory.Limits.H
asCoproduct X₂]       (f : (j : J) → X₁ j ⟶ X₂ j), (∀ (j : J), W (f j)) → W (Cat
egoryTheory.Limits.Sigma.map f)) →     W.IsStableUnderCoproductsOfShape J
参数：W : CategoryTheory.MorphismProperty C；J : Type u_1；∀ (X₁ X₂ : J → C) [inst_2 
: CategoryTheory.Limits.HasCoproduct X₁] [inst_3 : CategoryTheory.Limits.HasCopr
oduct X₂]       (f : (j : J) → X₁ j ⟶ X₂ j), (∀ (j : J), W (f j)) → W (CategoryT
heory.Limits.Sigma.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_isoColimit_hom_assoc`：∀ {α : Type w₂} {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C]   (X : CategoryTheory.Functor
 (CategoryTheory.Discrete α) C)   [inst_…
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom_assoc`：∀
 {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 
: CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsStableUnderCoproductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : ∀ (X₁ X₂ : J → C) [HasCoproduct X₁] [HasCoproduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Sigma.map f)) : W.IsStableUnderCoproductsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf α hα := by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasColimit X₁ := ⟨c₁, hc₁⟩
    have : HasColimit X₂ := ⟨c₂, hc₂⟩
    have : HasCoproduct fun j ↦ X₁.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₁.obj j)))
    have : HasCoproduct fun j ↦ X₂.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₂.obj j)))
    have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
    refine (W.arrow_mk_iso_iff ?_).1 hf'
    refine Arrow.isoMk
      ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₁) hc₁)
      ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₂) hc₂) ?_
    apply colimit.hom_ext
    rintro ⟨j⟩
    simp [φ, hα]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [(monomorphisms C).IsStableUnderCoproductsOfShape J]
    {X₁ X₂ : J → C} (f : ∀ j, X₁ j ⟶ X₂ j) [HasCoproduct X₁] [HasCoproduct X₂]
    [∀ j, Mono (f j)] :
    Mono (Limits.Sigma.map f) :=
  MorphismProperty.colimMap _ (fun ⟨j⟩ ↦ inferInstanceAs (Mono (f j)))

/-- The condition that a property of morphisms is stable by finite products. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts** 是 Mathlib 中的一个归纳
类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a property of morphisms is stable by finite products.
-/
class IsStableUnderFiniteProducts : Prop where
  isStableUnderProductsOfShape (J : Type) [Finite J] : W.IsStableUnderProductsOfShape J

attribute [instance] IsStableUnderFiniteProducts.isStableUnderProductsOfShape

/-- The condition that a property of morphisms is stable by finite coproducts. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderFiniteCoproducts** 是 Mathlib 中的一个
归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a property of morphisms is stable by finite coproducts.
-/
class IsStableUnderFiniteCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type) [Finite J] : W.IsStableUnderCoproductsOfShape J

attribute [instance] IsStableUnderFiniteCoproducts.isStableUnderCoproductsOfShape

/-- The condition that a property of morphisms is stable by coproducts. -/
@[pp_with_univ]
/-
**CategoryTheory.MorphismProperty.IsStableUnderCoproducts** 是 Mathlib 中的一个类，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsStableUnderCoproducts : Prop where isStableUnderCoproductsOfShape (J : T
ype w) : W.IsStableUnderCoproductsOfShape J
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a property of morphisms is stable by coproducts.
-/
class IsStableUnderCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type w) : W.IsStableUnderCoproductsOfShape J := by
    infer_instance

attribute [instance] IsStableUnderCoproducts.isStableUnderCoproductsOfShape
/-
**CategoryTheory.MorphismProperty.coproducts_le** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：coproducts_le [IsStableUnderCoproducts.{w} W] : coproducts.{w} W <= W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_iff`：coproducts_iff {X Y : C}
 (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Disc
rete J) f
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le`：colimitsOfShape_le [
W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCoproducts.isStableUnderCop
roductsOfShape`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Ca
tegoryTheory.MorphismProperty C}   [self : CategoryTheory.MorphismProperty.I…
-/
lemma coproducts_le [IsStableUnderCoproducts.{w} W] :
    coproducts.{w} W ≤ W := by
  intro X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact colimitsOfShape_le _ hf

@[simp]
/-
**CategoryTheory.MorphismProperty.coproducts_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：coproducts_eq_self [IsStableUnderCoproducts.{w} W] : coproducts.{w} W = W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_le`：coproducts_le [IsStableUn
derCoproducts.{w} W] : coproducts.{w} W <= W
· 使用引理 `CategoryTheory.MorphismProperty.le_coproducts`：le_coproducts : W <= copr
oducts.{w} W
-/
lemma coproducts_eq_self [IsStableUnderCoproducts.{w} W] :
    coproducts.{w} W = W :=
  le_antisymm W.coproducts_le W.le_coproducts

@[simp]
/-
**CategoryTheory.MorphismProperty.coproducts_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：coproducts_le_iff {P Q : MorphismProperty C} [IsStableUnderCoproducts.{w} 
Q] : coproducts.{w} P <= Q ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.MorphismProperty.le_coproducts`：le_coproducts : W <= copr
oducts.{w} W
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_monotone`：coproducts_monotone
 : Monotone (coproducts.{w} (C
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_le`：coproducts_le [IsStableUn
derCoproducts.{w} W] : coproducts.{w} W <= W
-/
lemma coproducts_le_iff {P Q : MorphismProperty C} [IsStableUnderCoproducts.{w} Q] :
    coproducts.{w} P ≤ Q ↔ P ≤ Q := by
  constructor
  · exact le_trans P.le_coproducts
  · intro h
    exact le_trans (coproducts_monotone h) Q.coproducts_le

end Products

section Diagonal

variable [HasPullbacks C] {P : MorphismProperty C}

/-- For `P : MorphismProperty C`, `P.diagonal` is a morphism property that holds for `f : X ⟶ Y`
whenever `P` holds for `X ⟶ Y xₓ Y`. -/
/-
**CategoryTheory.MorphismProperty.diagonal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：diagonal (P : MorphismProperty C) : MorphismProperty C
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `P : MorphismProperty C`, `P.diagonal` is a morphism property that holds for
 `f : X ⟶ Y`
whenever `P` holds for `X ⟶ Y xₓ Y`.
-/
def diagonal (P : MorphismProperty C) : MorphismProperty C := fun _ _ f => P (pullback.diagonal f)
/-
**CategoryTheory.MorphismProperty.diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f) :=
  Iff.rfl
/-
**CategoryTheory.MorphismProperty.RespectsIso.diagonal** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C]   {P : CategoryTheory.MorphismProperty C} [P.Resp
ectsIso], P.diagonal.RespectsIso
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.diagonal_iff`：diagonal_iff {X Y : C} {f 
: X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f)
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_comp`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}   [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C] (f : X ⟶ Y) (g …
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 :
 CategoryTheory.Limits.HasPullback f f] [Cat…
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
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.instHasPullbackCompOfIsIso`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) {X' : 
C} (i : X' ⟶ X)   [CategoryTheory.IsIs…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
instance RespectsIso.diagonal [P.RespectsIso] : P.diagonal.RespectsIso := by
  apply RespectsIso.mk
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, P.cancel_left_of_respectsIso,
      P.cancel_left_of_respectsIso, ← P.cancel_right_of_respectsIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.condition, P.cancel_left_of_respectsIso]
  · introv H
    delta diagonal
    rwa [pullback.diagonal_comp, P.cancel_right_of_respectsIso]
/-
**CategoryTheory.MorphismProperty.diagonal_isStableUnderComposition** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：diagonal_isStableUnderComposition [P.IsStableUnderComposition] [RespectsIs
o P] [IsStableUnderBaseChange P] : P.diagonal.IsStableUnderComposition where com
p_mem _ _ h₁ h₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.diagonal_iff`：diagonal_iff {X Y : C} {f 
: X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f)
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_comp`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}   [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C] (f : X ⟶ Y) (g …
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
-/
instance diagonal_isStableUnderComposition [P.IsStableUnderComposition] [RespectsIso P]
    [IsStableUnderBaseChange P] : P.diagonal.IsStableUnderComposition where
  comp_mem _ _ h₁ h₂ := by
    rw [diagonal_iff, pullback.diagonal_comp]
    exact P.comp_mem _ _ h₁
      (by simpa only [cancel_left_of_respectsIso] using P.pullback_snd _ _ h₂)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] [P.RespectsIso] : P.diagonal.ContainsIdentities where
  id_mem _ := P.of_isIso _
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsMultiplicative] [P.IsStableUnderBaseChange] : P.diagonal.IsMultiplicative where

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C]   {P : CategoryTheory.MorphismProperty C} [P.IsSt
ableUnderBaseChange] [P.RespectsIso],   P.diagonal.IsStableUnderBaseChange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.mk'`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProper
ty C} [P.RespectsIso],   (∀ (X Y S : C) (f : X ⟶ …
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.diagonal`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasPullba
cks C]   {P : CategoryTheory.MorphismPrope…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.diagonal_iff`：diagonal_iff {X Y : C} {f 
: X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f)
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.diagonal_pullback_fst`：diagonal_pullback_fst {X Y 
Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : diagonal (pullback.fst f g) = (pullbackSymmetry
 _ _).hom ≫ ((Over.pullback f).ma…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.overPullbackMap`：overPullbackMap [IsStab
leUnderBaseChange P] {S S' : C} (f : S' ⟶ S) [HasPullbacksAlong f] {X Y : Over S
} (g : X ⟶ Y) (H : P g.left) : P ((Ov…
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
-/
instance IsStableUnderBaseChange.diagonal [IsStableUnderBaseChange P] [P.RespectsIso] :
    P.diagonal.IsStableUnderBaseChange :=
  IsStableUnderBaseChange.mk'
    (by
      introv h
      rw [diagonal_iff, diagonal_pullback_fst, P.cancel_left_of_respectsIso,
        P.cancel_right_of_respectsIso]
      exact P.overPullbackMap f _ (by simpa))
/-
**CategoryTheory.MorphismProperty.diagonal_isomorphisms** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：diagonal_isomorphisms : (isomorphisms C).diagonal = monomorphisms C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用引理 `CategoryTheory.Limits.pullback.isIso_diagonal_iff`：isIso_diagonal_iff : 
IsIso (diagonal f) ↔ Mono f
-/
lemma diagonal_isomorphisms : (isomorphisms C).diagonal = monomorphisms C :=
  ext _ _ fun _ _ _ ↦ pullback.isIso_diagonal_iff _

set_option backward.isDefEq.respectTransparency false in
/-- If `P` is multiplicative and stable under base change, having the of-postcomp property
w.r.t. `Q` is equivalent to `Q` implying `P` on the diagonal. -/
/-
**CategoryTheory.MorphismProperty.hasOfPostcompProperty_iff_le_diagonal** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：hasOfPostcompProperty_iff_le_diagonal [P.IsStableUnderBaseChange] [P.IsMul
tiplicative] {Q : MorphismProperty C} [Q.IsStableUnderBaseChange] : P.HasOfPostc
ompProperty Q ↔ Q <= P.diagonal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasOfPostcompProperty.of_postcomp`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {W W' : CategoryTheory.Morph
ismProperty C}   [self : W.HasOfPostcompProperty W'] {X…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_fst`：pullback_fst {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong f] (H :
 P g) : P (pullback.fst f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用引理 `CategoryTheory.Limits.pullback_lift_diagonal_isPullback`：pullback_lift_d
iagonal_isPullback (g : Y ⟶ X) (f : X ⟶ S) : IsPullback g (pullback.lift (𝟙 Y) g
 (by simp)) (diagonal f) (pullback.map (g ≫ f…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)

--- 原说明 ---
If `P` is multiplicative and stable under base change, having the of-postcomp pr
operty
w.r.t. `Q` is equivalent to `Q` implying `P` on the diagonal.
-/
lemma hasOfPostcompProperty_iff_le_diagonal [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] {Q : MorphismProperty C} [Q.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty Q ↔ Q ≤ P.diagonal := by
  refine ⟨fun hP X Y f hf ↦ ?_, fun hP ↦ ⟨fun {Y X S} g f hf hcomp ↦ ?_⟩⟩
  · exact hP.of_postcomp _ _ (Q.pullback_fst _ _ hf) (by simpa using P.id_mem X)
  · set gr : Y ⟶ pullback (g ≫ f) f := pullback.lift (𝟙 Y) g (by simp)
    have : g = gr ≫ pullback.snd _ _ := by simp [gr]
    rw [this]
    apply P.comp_mem
    · exact P.of_isPullback (pullback_lift_diagonal_isPullback g f) (hP _ hf)
    · exact P.pullback_snd _ _ hcomp

end Diagonal

section Universally

/-- `P.universally` holds for a morphism `f : X ⟶ Y` iff `P` holds for all `X ×[Y] Y' ⟶ Y'`. -/
/-
**CategoryTheory.MorphismProperty.universally** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：universally (P : MorphismProperty C) : MorphismProperty C
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.universally` holds for a morphism `f : X ⟶ Y` iff `P` holds for all `X ×[Y] Y
' ⟶ Y'`.
-/
def universally (P : MorphismProperty C) : MorphismProperty C := fun X Y f =>
  ∀ ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'
/-
**CategoryTheory.MorphismProperty.universally_respectsIso** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：universally_respectsIso (P : MorphismProperty C) : P.universally.RespectsI
so
参数：P : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
instance universally_respectsIso (P : MorphismProperty C) : P.universally.RespectsIso := by
  apply RespectsIso.mk
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    exact hf _ _ _
      (by simpa only [Iso.inv_hom_id_assoc, Category.id_comp] using this.paste_horiz H)
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) i₂ (i₂ ≫ e.inv) e.inv :=
      IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩
    exact hf _ _ _ (by simpa only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.comp_id] using H.paste_horiz this)
/-
**CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：universally_isStableUnderBaseChange (P : MorphismProperty C) : P.universal
ly.IsStableUnderBaseChange where of_isPullback H h₁ _ _ _ _ _ H'
参数：P : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
instance universally_isStableUnderBaseChange (P : MorphismProperty C) :
    P.universally.IsStableUnderBaseChange where
  of_isPullback H h₁ _ _ _ _ _ H' := h₁ _ _ _ (H'.paste_vert H.flip)
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.universally** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasPullbacks C]   (P : CategoryTheory.MorphismProperty C) [hP : P.IsStable
UnderComposition], P.universally.IsStableUnderComposition
参数：P : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
instance IsStableUnderComposition.universally [HasPullbacks C] (P : MorphismProperty C)
    [hP : P.IsStableUnderComposition] : P.universally.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg X' Z' i₁ i₂ f' H := by
    have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
    rw [← this] at H ⊢
    apply P.comp_mem _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
    exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))
/-
**CategoryTheory.MorphismProperty.universally_le** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：universally_le (P : MorphismProperty C) : P.universally <= P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem universally_le (P : MorphismProperty C) : P.universally ≤ P := by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)
/-
**CategoryTheory.MorphismProperty.universally_inf** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：universally_inf (P Q : MorphismProperty C) : (P ⊓ Q).universally = P.unive
rsally ⊓ Q.universally
参数：P Q : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem universally_inf (P Q : MorphismProperty C) :
    (P ⊓ Q).universally = P.universally ⊓ Q.universally := by
  ext X Y f
  change _ ↔ _ ∧ _
  simp_rw [universally, ← forall_and]
  rfl
/-
**CategoryTheory.MorphismProperty.universally_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：universally_eq_iff {P : MorphismProperty C} : P.universally = P ↔ P.IsStab
leUnderBaseChange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `CategoryTheory.MorphismProperty.universally_le`：universally_le (P : Morp
hismProperty C) : P.universally <= P
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morp
hismProperty C}   [self : P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
theorem universally_eq_iff {P : MorphismProperty C} :
    P.universally = P ↔ P.IsStableUnderBaseChange :=
  ⟨(· ▸ P.universally_isStableUnderBaseChange),
    fun hP ↦ P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP.of_isPullback H.flip hf⟩
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChange.universally_eq** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [hP : P.IsStableUnderBaseChange], P.universally = P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.universally_eq_iff`：universally_eq_iff {
P : MorphismProperty C} : P.universally = P ↔ P.IsStableUnderBaseChange
-/
theorem IsStableUnderBaseChange.universally_eq {P : MorphismProperty C}
    [hP : P.IsStableUnderBaseChange] : P.universally = P := universally_eq_iff.mpr hP
/-
**CategoryTheory.MorphismProperty.universally_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：universally_mono : Monotone (universally : MorphismProperty C -> MorphismP
roperty C)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem universally_mono : Monotone (universally : MorphismProperty C → MorphismProperty C) :=
  fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ (h₁ _ _ _ H)
/-
**CategoryTheory.MorphismProperty.universally_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：universally_mk' (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X 
⟶ Y) (H : forall {T : C} (f : T ⟶ Y) [HasPullback f g], P (pullback.fst f g)) : 
universally P g
参数：P : MorphismProperty C；g : X ⟶ Y；H : forall {T : C} (f : T ⟶ Y) [HasPullback 
f g], P (pullback.fst f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma universally_mk' (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y)
    (H : ∀ {T : C} (f : T ⟶ Y) [HasPullback f g], P (pullback.fst f g)) :
    universally P g := by
  introv X' h
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst, P.cancel_left_of_respectsIso]
  exact H ..

end Universally

variable (P : MorphismProperty C)

/-- `P` has pullbacks if for every `f` satisfying `P`, pullbacks of arbitrary morphisms along `f`
exist. -/
/-
**CategoryTheory.MorphismProperty.HasPullbacks** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` has pullbacks if for every `f` satisfying `P`, pullbacks of arbitrary morphi
sms along `f`
exist.
-/
protected class HasPullbacks : Prop where
  hasPullback {X Y S : C} {f : X ⟶ S} (g : Y ⟶ S) : P f → HasPullback f g := by infer_instance
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPullbacks C] : P.HasPullbacks where

alias hasPullback := HasPullbacks.hasPullback
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.HasPullbacks] {X Y : C} {f : X ⟶ Y} : P.HasPullbacksAlong f where
  hasPullback _ := hasPullback _

/-- `P` has pushouts if for every `f` satisfying `P`, pushouts of arbitrary morphisms along `f`
exist. -/
/-
**CategoryTheory.MorphismProperty.HasPushouts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` has pushouts if for every `f` satisfying `P`, pushouts of arbitrary morphism
s along `f`
exist.
-/
protected class HasPushouts : Prop where
  hasPushout {X Y S : C} {f : S ⟶ X} (g : S ⟶ Y) : P f → HasPushout f g := by infer_instance
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPushouts C] : P.HasPushouts where

alias hasPushout := HasPushouts.hasPushout
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.HasPushouts] {X Y : C} {f : X ⟶ Y} : P.HasPushoutsAlong f where
  hasPushout _ := hasPushout _
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] : P.HasPullbacksAlong (f ≫ g) where
  hasPullback h p :=
    have : HasPullback h g := HasPullbacksAlong.hasPullback h p
    have : HasPullback (pullback.snd h g) f := HasPullbacksAlong.hasPullback (pullback.snd h g)
      (P.pullback_snd h g p)
    IsPullback.hasPullback (IsPullback.paste_horiz (IsPullback.of_hasPullback
      (pullback.snd h g) f) (IsPullback.of_hasPullback h g))
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong g] :
    P.IsStableUnderBaseChangeAlong (f ≫ g) where
  of_isPullback {_ _ _ _ p} pb hp :=
    have : HasPullback p g := HasPullbacksAlong.hasPullback p hp
    have right := IsPullback.of_hasPullback p g
    IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_right' pb right)
      (IsStableUnderBaseChangeAlong.of_isPullback right hp)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderCobaseChangeAlong f]
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] : P.HasPushoutsAlong (f ≫ g) where
  hasPushout h p :=
    have : HasPushout h f := HasPushoutsAlong.hasPushout h p
    have : HasPushout (pushout.inr h f) g := HasPushoutsAlong.hasPushout _
      (P.pushout_inr _ _ p)
    IsPushout.hasPushout (IsPushout.paste_vert (.of_hasPushout _ _) (.of_hasPushout _ _))
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderCobaseChangeAlong f]
    [P.IsStableUnderCobaseChangeAlong g] [P.HasPushoutsAlong f] :
    P.IsStableUnderCobaseChangeAlong (f ≫ g) where
  of_isPushout {_ _ _ _ p} pb hp :=
    have : HasPushout p f := HasPushoutsAlong.hasPushout p hp
    have right := IsPushout.of_hasPushout p f
    IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_left' pb right.flip)
      (IsStableUnderCobaseChangeAlong.of_isPushout right.flip hp)

/-- `P.IsStableUnderBaseChangeAgainst P'` states that for any morphism `f` satisfying `P` and
any morphism `g` with the same codomain as `f` satisfying `P'`, any pullback of `f` along `g`
also satisfies `P`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst** 是 Mathlib 中的一
个归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.IsStableUnderBaseChangeAgainst P'` states that for any morphism `f` satisfyin
g `P` and
any morphism `g` with the same codomain as `f` satisfying `P'`, any pullback of 
`f` along `g`
also satisfies `P`.
-/
class IsStableUnderBaseChangeAgainst
    (P P' : MorphismProperty C) : Prop where
  isStableUnderBaseChangeAlong ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P' f) :
    P.IsStableUnderBaseChangeAlong f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    (P' : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst P' where
  isStableUnderBaseChangeAlong := inferInstance
/-
**CategoryTheory.MorphismProperty.isStableUnderBaseChangeAgainst_top_iff** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderBaseChangeAgainst_top_iff (P : MorphismProperty C) : P.IsStab
leUnderBaseChangeAgainst ⊤ ↔ P.IsStableUnderBaseChange where mp h
参数：P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullba
ck`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory
.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst.isStableU
nderBaseChangeAlong`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P
 P' : CategoryTheory.MorphismProperty C}   [self : P.IsStableUnderBaseChangeAgai
n…
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAgainstOfIsSt
ableUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P
 : CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] (P' : Catego
r…
-/
lemma isStableUnderBaseChangeAgainst_top_iff
    (P : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst ⊤ ↔ P.IsStableUnderBaseChange where
  mp h :=
    ⟨fun {_ _ _ _} _ _ _ _ h' h'' ↦
      (h.isStableUnderBaseChangeAlong _ (by tauto)).of_isPullback h' h''⟩
  mpr _ := inferInstance

/-- `P.HasPullbacksAgainst P'` states that for any morphism `f` satisfying `P'`,
`P` has pullbacks along `f`. -/
/-
**CategoryTheory.MorphismProperty.HasPullbacksAgainst** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.HasPullbacksAgainst P'` states that for any morphism `f` satisfying `P'`,
`P` has pullbacks along `f`.
-/
class HasPullbacksAgainst
    (P P' : MorphismProperty C) : Prop where
  hasPullbacksAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.HasPullbacksAlong f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty C) [P.HasPullbacks] (P' : MorphismProperty C) :
    P.HasPullbacksAgainst P' where
  hasPullbacksAlong := inferInstance
/-
**CategoryTheory.MorphismProperty.hasPullbacksAgainst_top_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：hasPullbacksAgainst_top_iff (P : MorphismProperty C) : P.HasPullbacksAgain
st ⊤ ↔ P.HasPullbacks where mp h
参数：P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasPullbacksAlong.hasPullback`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProp
erty C} {X Y : C} {f : X ⟶ Y}   [self : P.HasPullba…
· 使用定理 `CategoryTheory.MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P P' : CategoryTheory.M
orphismProperty C}   [self : P.HasPullbacksAgainst P'] ⦃X Y…
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAgainstOfHasPullbacks`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morp
hismProperty C) [P.HasPullbacks]   (P' : CategoryTheory.Mor…
-/
lemma hasPullbacksAgainst_top_iff
    (P : MorphismProperty C) :
    P.HasPullbacksAgainst ⊤ ↔ P.HasPullbacks where
  mp h :=
    ⟨fun _ h' ↦
      (h.hasPullbacksAlong _ (by tauto)).hasPullback _ h'⟩
  mpr _ := inferInstance
/-
**CategoryTheory.MorphismProperty._root_.CategoryTheory.Limits.hasPullback_ofHas
PullbacksAgainst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Limits.hasPullback_ofHasPullbacksAgainst
    {P : MorphismProperty C} {P' : MorphismProperty C} {c c' c'' : C}
    {f : c ⟶ c'} {g : c'' ⟶ c'} [P.HasPullbacksAgainst P'] (hf : P f) (hg : P' g) :
    Limits.HasPullback f g :=
  letI : P.HasPullbacksAlong g :=
    MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong g hg
  MorphismProperty.HasPullbacksAlong.hasPullback f hf

/-- `P.IsStableUnderCobaseChangeAgainst P'` states that for any morphism `f` satisfying `P` and
any morphism `g` with the same domain as `f` satisfying `P'`, any pushout of `f` along `g`
also satisfies `P`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAgainst** 是 Mathlib 中
的一个归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.IsStableUnderCobaseChangeAgainst P'` states that for any morphism `f` satisfy
ing `P` and
any morphism `g` with the same domain as `f` satisfying `P'`, any pushout of `f`
 along `g`
also satisfies `P`.
-/
class IsStableUnderCobaseChangeAgainst
    (P P' : MorphismProperty C) : Prop where
  isStableUnderCobaseChangeAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.IsStableUnderCobaseChangeAlong f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (P' : MorphismProperty C) :
    P.IsStableUnderCobaseChangeAgainst P' where
  isStableUnderCobaseChangeAlong := inferInstance
/-
**CategoryTheory.MorphismProperty.isStableUnderCobaseChangeAgainst_top_iff** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderCobaseChangeAgainst_top_iff (P : MorphismProperty C) : P.IsSt
ableUnderCobaseChangeAgainst ⊤ ↔ P.IsStableUnderCobaseChange where mp h
参数：P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPush
out`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheor
y.MorphismProperty C} {X Y : C} {f : X ⟶ Y}   [self : P.IsStableU…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAgainst.isStabl
eUnderCobaseChangeAlong`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C
} {P P' : CategoryTheory.MorphismProperty C}   [self : P.IsStableUnderCobaseChan
geAga…
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAgainstOfIs
StableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] (P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] (P' : 
Categ…
-/
lemma isStableUnderCobaseChangeAgainst_top_iff
    (P : MorphismProperty C) :
    P.IsStableUnderCobaseChangeAgainst ⊤ ↔ P.IsStableUnderCobaseChange where
  mp h :=
    ⟨fun {_ _ _ _} _ _ _ _ h' h'' ↦
      (h.isStableUnderCobaseChangeAlong _ (by tauto)).of_isPushout h' h''⟩
  mpr _ := inferInstance

/-- `P.HasPushoutsAgainst P'` states that for any morphism `f` satisfying `P'`,
`P` has pushouts along `f`. -/
/-
**CategoryTheory.MorphismProperty.HasPushoutsAgainst** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.HasPushoutsAgainst P'` states that for any morphism `f` satisfying `P'`,
`P` has pushouts along `f`.
-/
class HasPushoutsAgainst
    (P P' : MorphismProperty C) : Prop where
  hasPushoutsAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.HasPushoutsAlong f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty C) [P.HasPushouts] (P' : MorphismProperty C) :
    P.HasPushoutsAgainst P' where
  hasPushoutsAlong := inferInstance
/-
**CategoryTheory.MorphismProperty.hasPushoutsAgainst_top_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：hasPushoutsAgainst_top_iff (P : MorphismProperty C) : P.HasPushoutsAgainst
 ⊤ ↔ P.HasPushouts where mp h
参数：P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasPushoutsAlong.hasPushout`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProper
ty C} {X Y : C} {f : X ⟶ Y}   [self : P.HasPushou…
· 使用定理 `CategoryTheory.MorphismProperty.HasPushoutsAgainst.hasPushoutsAlong`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P P' : CategoryTheory.Mor
phismProperty C}   [self : P.HasPushoutsAgainst P'] ⦃X Y …
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAgainstOfHasPushouts`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPushouts]   (P' : CategoryTheory.Morp…
-/
lemma hasPushoutsAgainst_top_iff
    (P : MorphismProperty C) :
    P.HasPushoutsAgainst ⊤ ↔ P.HasPushouts where
  mp h :=
    ⟨fun _ h' ↦
      (h.hasPushoutsAlong _ (by tauto)).hasPushout _ h'⟩
  mpr _ := inferInstance
/-
**CategoryTheory.MorphismProperty._root_.CategoryTheory.Limits.hasPushout_ofHasP
ushoutsAgainst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Limits.hasPushout_ofHasPushoutsAgainst
    {P : MorphismProperty C} {P' : MorphismProperty C} {c c' c'' : C}
    {f : c ⟶ c'} {g : c ⟶ c''} [P.HasPushoutsAgainst P'] (hf : P f) (hg : P' g) :
    Limits.HasPushout f g :=
  letI : P.HasPushoutsAlong g :=
    MorphismProperty.HasPushoutsAgainst.hasPushoutsAlong g hg
  MorphismProperty.HasPushoutsAlong.hasPushout f hf

end MorphismProperty

end CategoryTheory

