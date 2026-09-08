/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Exact sequences

A sequence of `n` composable arrows `S : ComposableArrows C` (i.e. a functor
`S : Fin (n + 1) ⥤ C`) is said to be exact (`S.Exact`) if the composition
of two consecutive arrows are zero (`S.IsComplex`) and the diagram is
exact at each `i` for `1 ≤ i < n`.

Together with the inductive construction of composable arrows
`ComposableArrows.precomp`, this is useful in order to state that certain
finite sequences of morphisms are exact (e.g the snake lemma), even though
in the applications it would usually be more convenient to use individual
lemmas expressing the exactness at a particular object.

This implementation is a refactor of `exact_seq` with appeared in the
Liquid Tensor Experiment as a property of lists in `Arrow C`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- The composable arrows associated to a short complex. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.toComposableArrows** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       CategoryTheory.ShortCom
plex C → CategoryTheory.ComposableArrows C 2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composable arrows associated to a short complex.
-/
def ShortComplex.toComposableArrows (S : ShortComplex C) : ComposableArrows C 2 :=
  ComposableArrows.mk₂ S.f S.g

/-- A map of short complexes induces a map of composable arrows with the same data. -/
/-
**CategoryTheory.ShortComplex.mapToComposableArrows** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {S₁ S₂ : CategoryTheory
.ShortComplex C} → (S₁ ⟶ S₂) → (S₁.toComposableArrows ⟶ S₂.toComposableArrows)
参数：S₁ ⟶ S₂；S₁.toComposableArrows ⟶ S₂.toComposableArrows。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map of short complexes induces a map of composable arrows with the same data.
-/
def ShortComplex.mapToComposableArrows {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    S₁.toComposableArrows ⟶ S₂.toComposableArrows :=
  ComposableArrows.homMk₂ φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

@[simp]
/-
**CategoryTheory.ShortComplex.mapToComposableArrows_app_0** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂),   (CategoryTheory.ShortComplex.mapToComposableArrows φ).app 0 
= φ.τ₁
参数：φ : S₁ ⟶ S₂；CategoryTheory.ShortComplex.mapToComposableArrows φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ShortComplex.mapToComposableArrows_app_0 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 0 = φ.τ₁ := rfl

@[simp]
/-
**CategoryTheory.ShortComplex.mapToComposableArrows_app_1** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂),   (CategoryTheory.ShortComplex.mapToComposableArrows φ).app 1 
= φ.τ₂
参数：φ : S₁ ⟶ S₂；CategoryTheory.ShortComplex.mapToComposableArrows φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ShortComplex.mapToComposableArrows_app_1 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 1 = φ.τ₂ := rfl

@[simp]
/-
**CategoryTheory.ShortComplex.mapToComposableArrows_app_2** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂),   (CategoryTheory.ShortComplex.mapToComposableArrows φ).app 2 
= φ.τ₃
参数：φ : S₁ ⟶ S₂；CategoryTheory.ShortComplex.mapToComposableArrows φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ShortComplex.mapToComposableArrows_app_2 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 2 = φ.τ₃ := rfl

@[simp]
/-
**CategoryTheory.ShortComplex.mapToComposableArrows_id** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ : CategoryTheory.ShortComplex C},
   CategoryTheory.ShortComplex.mapToComposableArrows (CategoryTheory.CategoryStr
uct.id S₁) =     CategoryTheory.CategoryStruct.id S₁.toComposableArrows
参数：CategoryTheory.CategoryStruct.id S₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₂`：hom_ext₂ {f g : ComposableArro
ws C 2} {φ φ' : f ⟶ g} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (
h₂ : app' φ 2 = app' φ' 2) : φ…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ShortComplex.mapToComposableArrows_id {S₁ : ShortComplex C} :
    (ShortComplex.mapToComposableArrows (𝟙 S₁)) = 𝟙 S₁.toComposableArrows := by
  cat_disch

@[simp]
/-
**CategoryTheory.ShortComplex.mapToComposableArrows_comp** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ S₃ : CategoryTheory.ShortCompl
ex C} (φ : S₁ ⟶ S₂) (ψ : S₂ ⟶ S₃),   CategoryTheory.ShortComplex.mapToComposable
Arrows (CategoryTheory.CategoryStruct.comp φ ψ) =     CategoryTheory.CategoryStr
uct.comp (CategoryTheory.ShortComplex.mapToComposableArrows φ)       (CategoryTh
eory.ShortComplex.mapToComposableArrows ψ)
参数：φ : S₁ ⟶ S₂；ψ : S₂ ⟶ S₃；CategoryTheory.CategoryStruct.comp φ ψ；CategoryTheory
.ShortComplex.mapToComposableArrows φ；CategoryTheory.ShortComplex.mapToComposabl
eArrows ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₂`：hom_ext₂ {f g : ComposableArro
ws C 2} {φ φ' : f ⟶ g} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (
h₂ : app' φ 2 = app' φ' 2) : φ…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ShortComplex.mapToComposableArrows_comp {S₁ S₂ S₃ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (ψ : S₂ ⟶ S₃) : ShortComplex.mapToComposableArrows (φ ≫ ψ) =
      ShortComplex.mapToComposableArrows φ ≫ ShortComplex.mapToComposableArrows ψ := by
  cat_disch

namespace ComposableArrows

variable {n : ℕ} (S : ComposableArrows C n)

-- We do not yet replace `omega` with `lia` here, as it is measurably slower.
/-- `F : ComposableArrows C n` is a complex if all compositions of
two consecutive arrows are zero. -/
/-
**CategoryTheory.ComposableArrows.IsComplex** 是 Mathlib 中的一个结构，位于命名空间 `CategoryT
heory.ComposableArrows`。
形式化陈述：IsComplex : Prop where /-- the composition of two consecutive arrows is ze
ro -/ zero (i : Nat) (hi : i + 2 <= n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F : ComposableArrows C n` is a complex if all compositions of
two consecutive arrows are zero.
-/
structure IsComplex : Prop where
  /-- the composition of two consecutive arrows is zero -/
  zero (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

attribute [reassoc] IsComplex.zero

variable {S}

@[reassoc]
/-
**CategoryTheory.ComposableArrows.IsComplex.zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ComposableArrows.IsComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTheory.Composabl
eArrows C n},   S.IsComplex →     ∀ (i j k : ℕ) (hij : autoParam (i + 1 = j) Cat
egoryTheory.ComposableArrows.IsComplex.zero'._auto_1)       (hjk : autoParam (j 
+ 1 = k) CategoryTheory.ComposableArrows.IsComplex.zero'._auto_3)       (hk : au
toParam (k ≤ n) CategoryTheory.ComposableArrows.IsComplex.zero'._auto_5),       
CategoryTheory.CategoryStruct.comp (S.map' i j ⋯ ⋯) (S.map' j k ⋯ hk) = 0
参数：i j k : ℕ；hij : autoParam (i + 1 = j) CategoryTheory.ComposableArrows.IsCompl
ex.zero'._auto_1；hjk : autoParam (j + 1 = k) CategoryTheory.ComposableArrows.IsC
omplex.zero'._auto_3；hk : autoParam (k ≤ n) CategoryTheory.ComposableArrows.IsCo
mplex.zero'._auto_5；S.map' i j ⋯ ⋯；S.map' j k ⋯ hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
-/
lemma IsComplex.zero' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S.map' i j ≫ S.map' j k = 0 := by
  subst hij hjk
  exact hS.zero i hk
/-
**CategoryTheory.ComposableArrows.isComplex_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ComposableArrows`。
形式化陈述：isComplex_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsC
omplex) : S₂.IsComplex where zero i hi
参数：e : S₁ ≅ S₂；h₁ : S₁.IsComplex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma isComplex_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) :
    S₂.IsComplex where
  zero i hi := by
    rw [← cancel_epi (ComposableArrows.app' e.hom i), comp_zero,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality,
      reassoc_of% (h₁.zero i hi), zero_comp]
/-
**CategoryTheory.ComposableArrows.isComplex_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ComposableArrows`。
形式化陈述：isComplex_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) : S₁.IsC
omplex ↔ S₂.IsComplex
参数：e : S₁ ≅ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.isComplex_of_iso`：isComplex_of_iso {S₁ S
₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) : S₂.IsComplex where
 zero i hi
-/
lemma isComplex_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.IsComplex ↔ S₂.IsComplex :=
  ⟨isComplex_of_iso e, isComplex_of_iso e.symm⟩
/-
**CategoryTheory.ComposableArrows.isComplex** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isComplex₀ (S : ComposableArrows C 0) : S.IsComplex where
  zero i hi := by simp at hi
/-
**CategoryTheory.ComposableArrows.isComplex** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isComplex₁ (S : ComposableArrows C 1) : S.IsComplex where
  zero i hi := by lia

variable (S)

/-- The short complex consisting of maps `S.map' i j` and `S.map' j k` when we know
that `S : ComposableArrows C n` satisfies `S.IsComplex`. -/
/-
**CategoryTheory.ComposableArrows.sc'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：sc' (hS : S.IsComplex) (i j k : Nat) (hij : i + 1 = j
参数：hS : S.IsComplex；i j k : Nat。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero'`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {n : ℕ} {S : CategoryTh…

--- 原说明 ---
The short complex consisting of maps `S.map' i j` and `S.map' j k` when we know
that `S : ComposableArrows C n` satisfies `S.IsComplex`.
-/
abbrev sc' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    ShortComplex C :=
  ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

/-- The short complex consisting of maps `S.map' i (i + 1)` and `S.map' (i + 1) (i + 2)`
when we know that `S : ComposableArrows C n` satisfies `S.IsComplex`. -/
/-
**CategoryTheory.ComposableArrows.sc** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ComposableArrows`。
形式化陈述：sc (hS : S.IsComplex) (i : Nat) (hi : i + 2 <= n
参数：hS : S.IsComplex；i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex consisting of maps `S.map' i (i + 1)` and `S.map' (i + 1) (i +
 2)`
when we know that `S : ComposableArrows C n` satisfies `S.IsComplex`.
-/
abbrev sc (hS : S.IsComplex) (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    ShortComplex C :=
  S.sc' hS i (i + 1) (i + 2)

/-- `F : ComposableArrows C n` is exact if it is a complex and that all short
complexes consisting of two consecutive arrows are exact. -/
/-
**CategoryTheory.ComposableArrows.Exact** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：Exact : Prop extends S.IsComplex where exact (i : Nat) (hi : i + 2 <= n
继承自：S.IsComplex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F : ComposableArrows C n` is exact if it is a complex and that all short
complexes consisting of two consecutive arrows are exact.
-/
structure Exact : Prop extends S.IsComplex where
  exact (i : ℕ) (hi : i + 2 ≤ n := by omega) : (S.sc toIsComplex i).Exact

variable {S}
/-
**CategoryTheory.ComposableArrows.Exact.exact'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ComposableArrows.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTheory.Composabl
eArrows C n} (hS : S.Exact) (i j k : ℕ)   (hij : autoParam (i + 1 = j) CategoryT
heory.ComposableArrows.Exact.exact'._auto_1)   (hjk : autoParam (j + 1 = k) Cate
goryTheory.ComposableArrows.Exact.exact'._auto_3)   (hk : autoParam (k ≤ n) Cate
goryTheory.ComposableArrows.Exact.exact'._auto_5), (S.sc' ⋯ i j k hij hjk hk).Ex
act
参数：hS : S.Exact；i j k : ℕ；hij : autoParam (i + 1 = j) CategoryTheory.ComposableA
rrows.Exact.exact'._auto_1；hjk : autoParam (j + 1 = k) CategoryTheory.Composable
Arrows.Exact.exact'._auto_3；hk : autoParam (k ≤ n) CategoryTheory.ComposableArro
ws.Exact.exact'._auto_5；S.sc' ⋯ i j k hij hjk hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
-/
lemma Exact.exact' (hS : S.Exact) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    (S.sc' hS.toIsComplex i j k).Exact := by
  subst hij hjk
  exact hS.exact i hk

/-- The (exact) short complex consisting of maps `S.map' i j` and `S.map' j k` when we know
that `S : ComposableArrows C n` is exact. -/
/-
**CategoryTheory.ComposableArrows.Exact.sc'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ComposableArrows.Exact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {n : ℕ} →         {S : 
CategoryTheory.ComposableArrows C n} →           S.Exact →             (i j k : 
ℕ) →               autoParam (i + 1 = j) CategoryTheory.ComposableArrows.Exact.s
c'._auto_1 →                 autoParam (j + 1 = k) CategoryTheory.ComposableArro
ws.Exact.sc'._auto_3 →                   autoParam (k ≤ n) CategoryTheory.Compos
ableArrows.Exact.sc'._auto_5 → CategoryTheory.ShortComplex C
参数：i j k : ℕ；i + 1 = j；j + 1 = k；k ≤ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…

--- 原说明 ---
The (exact) short complex consisting of maps `S.map' i j` and `S.map' j k` when 
we know
that `S : ComposableArrows C n` is exact.
-/
abbrev Exact.sc' (hS : S.Exact) (i j k : ℕ) (hij : i + 1 = j := by lia)
    (hjk : j + 1 = k := by lia) (hk : k ≤ n := by lia) :
    ShortComplex C :=
  S.sc' hS.toIsComplex i j k

/-- The short complex consisting of maps `S.map' i (i + 1)` and `S.map' (i + 1) (i + 2)`
when we know that `S : ComposableArrows C n` is exact. -/
/-
**CategoryTheory.ComposableArrows.Exact.sc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ComposableArrows.Exact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {n : ℕ} →         {S : 
CategoryTheory.ComposableArrows C n} →           S.Exact →             (i : ℕ) →
               autoParam (i + 2 ≤ n) CategoryTheory.ComposableArrows.Exact.sc._a
uto_1 → CategoryTheory.ShortComplex C
参数：i : ℕ；i + 2 ≤ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…

--- 原说明 ---
The short complex consisting of maps `S.map' i (i + 1)` and `S.map' (i + 1) (i +
 2)`
when we know that `S : ComposableArrows C n` is exact.
-/
abbrev Exact.sc (hS : S.Exact) (i : ℕ) (hi : i + 2 ≤ n := by lia) :
    ShortComplex C :=
  S.sc' hS.toIsComplex i (i + 1) (i + 2)

/-- Functoriality maps for `ComposableArrows.sc'`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.sc'Map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {n : ℕ} →         {S₁ S
₂ : CategoryTheory.ComposableArrows C n} →           (S₁ ⟶ S₂) →             (h₁
 : S₁.IsComplex) →               (h₂ : S₂.IsComplex) →                 (i j k : 
ℕ) →                   (hij : autoParam (i + 1 = j) CategoryTheory.ComposableArr
ows.sc'Map._auto_1) →                     (hjk : autoParam (j + 1 = k) CategoryT
heory.ComposableArrows.sc'Map._auto_3) →                       (hk : autoParam (
k ≤ n) CategoryTheory.ComposableArrows.sc'Map._auto_5) →                        
 S₁.sc' h₁ i j k hij hjk hk ⟶ S₂.sc' h₂ i j k hij hjk hk
参数：S₁ ⟶ S₂；h₁ : S₁.IsComplex；h₂ : S₂.IsComplex；i j k : ℕ；hij : autoParam (i + 1 
= j) CategoryTheory.ComposableArrows.sc'Map._auto_1；hjk : autoParam (j + 1 = k) 
CategoryTheory.ComposableArrows.sc'Map._auto_3；hk : autoParam (k ≤ n) CategoryTh
eory.ComposableArrows.sc'Map._auto_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality maps for `ComposableArrows.sc'`.
-/
def sc'Map {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S₁.sc' h₁ i j k ⟶ S₂.sc' h₂ i j k where
  τ₁ := φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

/-- Functoriality maps for `ComposableArrows.sc`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.scMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：scMap {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂
 : S₂.IsComplex) (i : Nat) (hi : i + 2 <= n
参数：φ : S₁ ⟶ S₂；h₁ : S₁.IsComplex；h₂ : S₂.IsComplex；i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality maps for `ComposableArrows.sc`.
-/
def scMap {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    S₁.sc h₁ i ⟶ S₂.sc h₂ i :=
  sc'Map φ h₁ h₂ i (i + 1) (i + 2)

/-- The isomorphism `S₁.sc' _ i j k ≅ S₂.sc' _ i j k` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.sc'MapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ComposableArrows`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {n : ℕ} →         {S₁ S
₂ : CategoryTheory.ComposableArrows C n} →           (S₁ ≅ S₂) →             (h₁
 : S₁.IsComplex) →               (h₂ : S₂.IsComplex) →                 (i j k : 
ℕ) →                   (hij : autoParam (i + 1 = j) CategoryTheory.ComposableArr
ows.sc'MapIso._auto_1) →                     (hjk : autoParam (j + 1 = k) Catego
ryTheory.ComposableArrows.sc'MapIso._auto_3) →                       (hk : autoP
aram (k ≤ n) CategoryTheory.ComposableArrows.sc'MapIso._auto_5) →               
          S₁.sc' h₁ i j k hij hjk hk ≅ S₂.sc' h₂ i j k hij hjk hk
参数：S₁ ≅ S₂；h₁ : S₁.IsComplex；h₂ : S₂.IsComplex；i j k : ℕ；hij : autoParam (i + 1 
= j) CategoryTheory.ComposableArrows.sc'MapIso._auto_1；hjk : autoParam (j + 1 = 
k) CategoryTheory.ComposableArrows.sc'MapIso._auto_3；hk : autoParam (k ≤ n) Cate
goryTheory.ComposableArrows.sc'MapIso._auto_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S₁.sc' _ i j k ≅ S₂.sc' _ i j k` induced by an isomorphism `S₁ 
≅ S₂`
in `ComposableArrows C n`.
-/
def sc'MapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S₁.sc' h₁ i j k ≅ S₂.sc' h₂ i j k where
  hom := sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.scMapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ComposableArrows`。
形式化陈述：scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) 
(h₂ : S₂.IsComplex) (i : Nat) (hi : i + 2 <= n
参数：e : S₁ ≅ S₂；h₁ : S₁.IsComplex；h₂ : S₂.IsComplex；i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`.
-/
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    S₁.sc h₁ i ≅ S₂.sc h₂ i where
  hom := scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp
/-
**CategoryTheory.ComposableArrows.exact_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ComposableArrows`。
形式化陈述：exact_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) 
: S₂.Exact where toIsComplex
参数：e : S₁ ≅ S₂；h₁ : S₁.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.isComplex_of_iso`：isComplex_of_iso {S₁ S
₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) : S₂.IsComplex where
 zero i hi
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
-/
lemma exact_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) :
    S₂.Exact where
  toIsComplex := isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)
/-
**CategoryTheory.ComposableArrows.exact_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ComposableArrows`。
形式化陈述：exact_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) : S₁.Exact ↔
 S₂.Exact
参数：e : S₁ ≅ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.exact_of_iso`：exact_of_iso {S₁ S₂ : Comp
osableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) : S₂.Exact where toIsComplex
-/
lemma exact_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩
/-
**CategoryTheory.ComposableArrows.exact** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₀ (S : ComposableArrows C 0) : S.Exact where
  toIsComplex := S.isComplex₀
  exact i hi := by simp at hi
/-
**CategoryTheory.ComposableArrows.exact** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₁ (S : ComposableArrows C 1) : S.Exact where
  toIsComplex := S.isComplex₁
  exact i hi := by exfalso; lia
/-
**CategoryTheory.ComposableArrows.isComplex** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isComplex₂_iff (S : ComposableArrows C 2) :
    S.IsComplex ↔ S.map' 0 1 ≫ S.map' 1 2 = 0 := by
  constructor
  · intro h
    exact h.zero 0 (by lia)
  · intro h
    refine IsComplex.mk (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h
/-
**CategoryTheory.ComposableArrows.isComplex** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isComplex₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) :
    S.IsComplex :=
  S.isComplex₂_iff.2 w

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows._root_.CategoryTheory.ShortComplex.isComplex_t
oComposableArrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows (S : ShortComplex C) :
    S.toComposableArrows.IsComplex :=
  -- Disable `Fin.reduceFinMk` because otherwise `Precompose.map_one_succ` does not apply. (https://github.com/leanprover-community/mathlib4/issues/27382)
  isComplex₂_mk _ (by simp [-Fin.reduceFinMk])
/-
**CategoryTheory.ComposableArrows.exact** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₂_iff (S : ComposableArrows C 2) (hS : S.IsComplex) :
    S.Exact ↔ (S.sc' hS 0 1 2).Exact := by
  constructor
  · intro h
    exact h.exact 0 (by lia)
  · intro h
    refine Exact.mk hS (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h
/-
**CategoryTheory.ComposableArrows.exact** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
    (h : (ShortComplex.mk _ _ w).Exact) : S.Exact :=
  (S.exact₂_iff (S.isComplex₂_mk w)).2 h
/-
**CategoryTheory.ComposableArrows._root_.CategoryTheory.ShortComplex.Exact.exact
_toComposableArrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows
    {S : ShortComplex C} (hS : S.Exact) :
    S.toComposableArrows.Exact :=
  exact₂_mk _ _ hS
/-
**CategoryTheory.ComposableArrows._root_.CategoryTheory.ShortComplex.exact_iff_e
xact_toComposableArrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ComposableArro
ws`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows
    (S : ShortComplex C) :
    S.Exact ↔ S.toComposableArrows.Exact :=
  (S.toComposableArrows.exact₂_iff S.isComplex_toComposableArrows).symm
/-
**CategoryTheory.ComposableArrows.exact_iff_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_iff_δ₀ (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact ∧ S.δ₀.Exact := by
  constructor
  · intro h
    constructor
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by lia)
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero (i + 1)))
        (fun i hi => h.exact (i + 1))
  · rintro ⟨h, h₀⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i
/-
**CategoryTheory.ComposableArrows.Exact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Exact.δ₀ {S : ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δ₀.Exact := by
  rw [exact_iff_δ₀] at hS
  exact hS.2

/-- If `S : ComposableArrows C (n + 2)` is such that the first two arrows form
an exact sequence and that the tail `S.δ₀` is exact, then `S` is also exact.
See `ShortComplex.SnakeInput.snake_lemma` in `Algebra.Homology.ShortComplex.SnakeLemma`
for a use of this lemma. -/
/-
**CategoryTheory.ComposableArrows.exact_of_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S : ComposableArrows C (n + 2)` is such that the first two arrows form
an exact sequence and that the tail `S.δ₀` is exact, then `S` is also exact.
See `ShortComplex.SnakeInput.snake_lemma` in `Algebra.Homology.ShortComplex.Snak
eLemma`
for a use of this lemma.
-/
lemma exact_of_δ₀ {S : ComposableArrows C (n + 2)}
    (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) : S.Exact := by
  rw [exact_iff_δ₀]
  constructor <;> assumption
/-
**CategoryTheory.ComposableArrows.exact_iff_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_iff_δlast {n : ℕ} (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ S.δlast.Exact ∧ (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact := by
  constructor
  · intro h
    constructor
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero i))
        (fun i hi => h.exact i)
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero n
      exact h.exact n (by lia)
  · rintro ⟨h, h'⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.toIsComplex.zero i
      · exact h'.toIsComplex.zero 0
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.exact i
      · exact h'.exact 0
/-
**CategoryTheory.ComposableArrows.Exact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Exact.δlast {S : ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δlast.Exact := by
  rw [exact_iff_δlast] at hS
  exact hS.1
/-
**CategoryTheory.ComposableArrows.exact_of_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_of_δlast {n : ℕ} (S : ComposableArrows C (n + 2))
    (h₁ : S.δlast.Exact) (h₂ : (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact) :
    S.Exact := by
  rw [exact_iff_δlast]
  constructor <;> assumption
/-
**CategoryTheory.ComposableArrows.natAddLEFunctor_obj_exact** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ComposableArrows`。
形式化陈述：natAddLEFunctor_obj_exact {n k l : Nat} (h : k + l <= n) {R : ComposableAr
rows C n} (hR : R.Exact) : ((natAddLEFunctor h).obj R).Exact
参数：h : k + l <= n；hR : R.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
-/
theorem natAddLEFunctor_obj_exact {n k l : ℕ} (h : k + l ≤ n) {R : ComposableArrows C n}
    (hR : R.Exact) :
    ((natAddLEFunctor h).obj R).Exact :=
  ⟨⟨fun i _ => hR.1.1 (k + i)⟩, fun i _ => hR.exact (k + i)⟩
/-
**CategoryTheory.ComposableArrows.Exact.isIso_map'** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ComposableArrows.Exact`。
形式化陈述：∀ {C : Type u_2} [inst : CategoryTheory.Category.{v_2, u_2} C] [inst_1 : C
ategoryTheory.Preadditive C]   [CategoryTheory.Balanced C] {n : ℕ} {S : Category
Theory.ComposableArrows C n},   S.Exact →     ∀ (k : ℕ) (hk : k + 3 ≤ n),       
S.map' k (k + 1) ⋯ ⋯ = 0 → S.map' (k + 2) (k + 3) ⋯ hk = 0 → CategoryTheory.IsIs
o (S.map' (k + 1) (k + 2) ⋯ ⋯)
参数：k : ℕ；hk : k + 3 ≤ n；k + 1；k + 2；k + 3；S.map' (k + 1) (k + 2) ⋯ ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : C
ategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
lemma Exact.isIso_map' {C : Type*} [Category* C] [Preadditive C]
    [Balanced C] {n : ℕ} {S : ComposableArrows C n} (hS : S.Exact) (k : ℕ) (hk : k + 3 ≤ n)
    (h₀ : S.map' k (k + 1) = 0) (h₁ : S.map' (k + 2) (k + 3) = 0) :
    IsIso (S.map' (k + 1) (k + 2)) := by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

end ComposableArrows

end CategoryTheory

