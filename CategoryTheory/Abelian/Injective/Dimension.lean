/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.ENat.Lattice

/-!
# Injective dimension

In an abelian category `C`, we shall say that `X : C` has Injective dimension `< n`
if all `Ext Y X i` vanish when `n ≤ i`. This defines a type class
`HasInjectiveDimensionLT X n`. We also define a type class
`HasInjectiveDimensionLE X n` as an abbreviation for
`HasInjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasInjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasInjectiveDimensionLE`.)

We also define the Injective dimension in `WithBot ℕ∞` as `injectiveDimension`,
`injectiveDimension X = ⊥` iff `X` is zero and behaves as expected on non-negative values.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object `X` in an abelian category has Injective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasInjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasInjectiveDimensionLT.mk`, and the lemmas `hasInjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasInjectiveDimensionLT`.) -/
/-
**CategoryTheory.HasInjectiveDimensionLT** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheor
y`。
形式化陈述：HasInjectiveDimensionLT (X : C) (n : Nat) : Prop where mk' :: subsingleton
' (i : Nat) (hi : n <= i) ⦃Y : C⦄ : letI
参数：X : C；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in an abelian category has Injective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasInjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasInjectiveDimensionLT.mk`, and the lemmas `hasInjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasInjectiveDimensionLT`.)
-/
class HasInjectiveDimensionLT (X : C) (n : ℕ) : Prop where mk' ::
  subsingleton' (i : ℕ) (hi : n ≤ i) ⦃Y : C⦄ :
    letI := HasExt.standard C
    Subsingleton (Ext.{max u v} Y X i)

/-- An object `X` in an abelian category has Injective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i` -/
/-
**CategoryTheory.HasInjectiveDimensionLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：HasInjectiveDimensionLE (X : C) (n : Nat) : Prop
参数：X : C；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in an abelian category has Injective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i`
-/
abbrev HasInjectiveDimensionLE (X : C) (n : ℕ) : Prop :=
  HasInjectiveDimensionLT X (n + 1)

namespace HasInjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : ℕ)

/-
**CategoryTheory.HasInjectiveDimensionLT.subsingleton** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.HasInjectiveDimensionLT`。
形式化陈述：subsingleton [hX : HasInjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y
 : C) : Subsingleton (Ext.{w} Y X i)
参数：i : Nat；hi : n <= i；Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `CategoryTheory.HasInjectiveDimensionLT.subsingleton'`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C} {X : 
C} {n : ℕ}   [self : CategoryTheory.HasInj…
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma subsingleton [hX : HasInjectiveDimensionLT X n] (i : ℕ) (hi : n ≤ i) (Y : C) :
    Subsingleton (Ext.{w} Y X i) := by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
/-
**CategoryTheory.HasInjectiveDimensionLT.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.HasInjectiveDimensionLT`。
形式化陈述：mk (hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e 
= 0) : HasInjectiveDimensionLT X n where subsingleton' i hi Y
参数：hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mk (hX : ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext Y X i), e = 0) :
    HasInjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext Y X i) := ⟨fun e₁ e₂ ↦ by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasInjectiveDimensionLT

/-
**CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} {i : ℕ} (e : C
ategoryTheory.Abelian.Ext Y X i) (n : ℕ)   [CategoryTheory.HasInjectiveDimension
LT X n], n ≤ i → e = 0
参数：e : CategoryTheory.Abelian.Ext Y X i；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `CategoryTheory.HasInjectiveDimensionLT.subsingleton`：subsingleton [hX : 
HasInjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (Ext
.{w} Y X i)
-/
lemma Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : ℕ} (e : Ext Y X i) (n : ℕ) [HasInjectiveDimensionLT X n]
    (hi : n ≤ i) : e = 0 :=
  (HasInjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : ℕ)

/-
**CategoryTheory.hasInjectiveDimensionLT_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：hasInjectiveDimensionLT_iff [HasExt.{w} C] : HasInjectiveDimensionLT X n ↔
 forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
· 使用引理 `CategoryTheory.HasInjectiveDimensionLT.mk`：mk (hX : forall (i : Nat) (_ 
: n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0) : HasInjectiveDimensionLT X n 
where subsingleton' i hi Y
-/
lemma hasInjectiveDimensionLT_iff [HasExt.{w} C] :
    HasInjectiveDimensionLT X n ↔
      ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext Y X i), e = 0 :=
  ⟨fun _ _ hi _ e ↦ e.eq_zero_of_hasInjectiveDimensionLT n hi,
    HasInjectiveDimensionLT.mk⟩

variable {X} in
/-
**CategoryTheory.Limits.IsZero.hasInjectiveDimensionLT_zero** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X : C},   CategoryTheory.Limits.IsZero X → CategoryTheory.Ha
sInjectiveDimensionLT X 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasInjectiveDimensionLT_iff`：hasInjectiveDimensionLT_iff 
[HasExt.{w} C] : HasInjectiveDimensionLT X n ↔ forall (i : Nat) (_ : n <= i) ⦃Y 
: C⦄, forall (e : Ext Y X i), e …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Ext.comp_mk₀_id`：comp_mk₀_id (α : Ext X Y n) : α.
comp (mk₀ (𝟙 Y)) (add_zero n) = α
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_tgt`：eq_zero_of_tgt {X Y : C} (o
 : IsZero Y) (f : X ⟶ Y) : f = 0
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_zero`：mk₀_zero : mk₀ (0 : X ⟶ Y) = 0
· 使用引理 `CategoryTheory.Abelian.Ext.comp_zero`：comp_zero (α : Ext X Y n) (Z : C) 
(m : Nat) (p : Nat) (h : n + m = p) : α.comp (0 : Ext Y Z m) h = 0
-/
lemma Limits.IsZero.hasInjectiveDimensionLT_zero (hX : IsZero X) :
    HasInjectiveDimensionLT X 0 := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.comp_mk₀_id, hX.eq_zero_of_tgt (𝟙 X), Ext.mk₀_zero, Ext.comp_zero]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasInjectiveDimensionLT (0 : C) 0 :=
  (isZero_zero C).hasInjectiveDimensionLT_zero
/-
**CategoryTheory.isZero_of_hasInjectiveDimensionLT_zero** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：isZero_of_hasInjectiveDimensionLT_zero [HasInjectiveDimensionLT X 0] : IsZ
ero X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Abelian.Ext.homEquiv₀_symm_apply`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 
: CategoryTheory.HasExt C] {X Y : C} …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_zero`：mk₀_zero : mk₀ (0 : X ⟶ Y) = 0
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isZero_of_hasInjectiveDimensionLT_zero [HasInjectiveDimensionLT X 0] : IsZero X := by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT _ 0 (by rfl)
/-
**CategoryTheory.hasInjectiveDimensionLT_zero_iff_isZero** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory`。
形式化陈述：hasInjectiveDimensionLT_zero_iff_isZero : HasInjectiveDimensionLT X 0 ↔ Is
Zero X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isZero_of_hasInjectiveDimensionLT_zero`：isZero_of_hasInje
ctiveDimensionLT_zero [HasInjectiveDimensionLT X 0] : IsZero X
· 使用定理 `CategoryTheory.Limits.IsZero.hasInjectiveDimensionLT_zero`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] 
{X : C},   CategoryTheory.Limits.IsZero X → Cat…
-/
lemma hasInjectiveDimensionLT_zero_iff_isZero : HasInjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ ↦ isZero_of_hasInjectiveDimensionLT_zero X, fun h ↦ h.hasInjectiveDimensionLT_zero⟩
/-
**CategoryTheory.hasInjectiveDimensionLT_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：hasInjectiveDimensionLT_of_ge (m : Nat) (h : n <= m) [HasInjectiveDimensio
nLT X n] : HasInjectiveDimensionLT X m
参数：m : Nat；h : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasInjectiveDimensionLT_iff`：hasInjectiveDimensionLT_iff 
[HasExt.{w} C] : HasInjectiveDimensionLT X n ↔ forall (i : Nat) (_ : n <= i) ⦃Y 
: C⦄, forall (e : Ext Y X i), e …
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
-/
lemma hasInjectiveDimensionLT_of_ge (m : ℕ) (h : n ≤ m)
    [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X m := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasInjectiveDimensionLT n (by lia)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasInjectiveDimensionLT X n] (k : ℕ) :
    HasInjectiveDimensionLT X (n + k) :=
  hasInjectiveDimensionLT_of_ge X n (n + k) (by lia)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasInjectiveDimensionLT X n] (k : ℕ) :
    HasInjectiveDimensionLT X (k + n) :=
  hasInjectiveDimensionLT_of_ge X n (k + n) (by lia)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasInjectiveDimensionLT X (n + 1))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Injective X] : HasInjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_injective

variable {X} in
/-
**CategoryTheory.injective_iff_subsingleton_ext_one** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：injective_iff_subsingleton_ext_one [HasExt.{w} C] : Injective X ↔ forall ⦃
Y : C⦄, Subsingleton (Ext Y X 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.HasInjectiveDimensionLT.subsingleton`：subsingleton [hX : 
HasInjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (Ext
.{w} Y X i)
· 使用定理 `CategoryTheory.instHasInjectiveDimensionLTOfNatNatOfInjective`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C] (X : C)   [CategoryTheory.Injective X], Categor…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`：contravariant_
sequence_exact₁ {n₀ : Nat} (x₁ : Ext S.X₁ Y n₀) {n₁ : Nat} (hn₁ : 1 + n₀ = n₁) (
hx₁ : hS.extClass.comp x₁ hn₁ = 0) : exists (x…
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Ext.homEquiv₀_symm_apply`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 
: CategoryTheory.HasExt C] {X Y : C} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Abelian.Ext.comp.congr_simp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.HasExt C] {X Y Z : C…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_comp_mk₀`：mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y
 ⟶ Z) : (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g)
-/
lemma injective_iff_subsingleton_ext_one [HasExt.{w} C] :
    Injective X ↔ ∀ ⦃Y : C⦄, Subsingleton (Ext Y X 1) := by
  refine ⟨fun h ↦ HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h ↦ ⟨fun f g _ ↦ ?_⟩⟩
  obtain ⟨φ, hφ⟩ := Ext.contravariant_sequence_exact₁ { exact := ShortComplex.exact_cokernel g } _
    (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective (by simpa using hφ)⟩

variable {X} in
/-
**CategoryTheory.injective_iff_hasInjectiveDimensionLT_one** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory`。
形式化陈述：injective_iff_hasInjectiveDimensionLT_one : Injective X ↔ HasInjectiveDime
nsionLT X 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `CategoryTheory.instHasInjectiveDimensionLTOfNatNatOfInjective`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C] (X : C)   [CategoryTheory.Injective X], Categor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.injective_iff_subsingleton_ext_one`：injective_iff_subsing
leton_ext_one [HasExt.{w} C] : Injective X ↔ forall ⦃Y : C⦄, Subsingleton (Ext Y
 X 1)
· 使用引理 `CategoryTheory.HasInjectiveDimensionLT.subsingleton`：subsingleton [hX : 
HasInjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (Ext
.{w} Y X i)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma injective_iff_hasInjectiveDimensionLT_one :
    Injective X ↔ HasInjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ injective_iff_subsingleton_ext_one.2
    (HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [HasInjectiveDimensionLT X 1] : Injective X :=
  injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›

end

/-
**CategoryTheory.Retract.hasInjectiveDimensionLT** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Retract`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X Y : C}   (h : CategoryTheory.Retract X Y) (n : ℕ) [Categor
yTheory.HasInjectiveDimensionLT Y n],   CategoryTheory.HasInjectiveDimensionLT X
 n
参数：h : CategoryTheory.Retract X Y；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasInjectiveDimensionLT_iff`：hasInjectiveDimensionLT_iff 
[HasExt.{w} C] : HasInjectiveDimensionLT X n ↔ forall (i : Nat) (_ : n <= i) ⦃Y 
: C⦄, forall (e : Ext Y X i), e …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Ext.comp_mk₀_id`：comp_mk₀_id (α : Ext X Y n) : α.
comp (mk₀ (𝟙 Y)) (add_zero n) = α
· 使用定理 `CategoryTheory.Retract.retract`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X Y : C} (self : CategoryTheory.Retract X Y),   CategoryTheory
.CategoryStruct.comp…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_comp_mk₀`：mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y
 ⟶ Z) : (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g)
· 使用引理 `CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero`：comp_assoc_of_
second_deg_zero {a₁ a₃ a₁₃ : Nat} (α : Ext X Y a₁) (β : Ext Y Z 0) (γ : Ext Z T 
a₃) (h₁₃ : a₁ + a₃ = a₁₃) : (α.comp β (add_zer…
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0
-/
lemma Retract.hasInjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : ℕ)
    [HasInjectiveDimensionLT Y n] :
    HasInjectiveDimensionLT X n := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.comp_mk₀_id, ← h.retract, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    (x.comp (Ext.mk₀ h.i) (add_zero i)).eq_zero_of_hasInjectiveDimensionLT n hi, Ext.zero_comp]
/-
**CategoryTheory.hasInjectiveDimensionLT_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：hasInjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : Nat) [HasInjec
tiveDimensionLT X n] : HasInjectiveDimensionLT X' n
参数：e : X ≅ X'；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Retract.hasInjectiveDimensionLT`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C}  
 (h : CategoryTheory.Retract X Y) (n…
-/
lemma hasInjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : ℕ)
    [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X' n :=
  e.symm.retract.hasInjectiveDimensionLT n

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
include hS

-- In the following lemmas, the parameters `HasInjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

/-
**CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasInjectiveDimensionLT_X₂ (h₁ : HasInjectiveDimensionLT S.X₁ n)
    (h₃ : HasInjectiveDimensionLT S.X₃ n) :
    HasInjectiveDimensionLT S.X₂ n := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x₂
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasInjectiveDimensionLT n hi, Ext.zero_comp]
/-
**CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasInjectiveDimensionLT_X₁ (h₁ : HasInjectiveDimensionLT S.X₃ n)
    (h₂ : HasInjectiveDimensionLT S.X₂ (n + 1)) :
    HasInjectiveDimensionLT S.X₁ (n + 1) := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x₃
      (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) hi) rfl
    rw [x₁.eq_zero_of_hasInjectiveDimensionLT n (by lia), Ext.zero_comp]
/-
**CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasInjectiveDimensionLT_X₃ (h₂ : HasInjectiveDimensionLT S.X₂ n)
    (h₃ : HasInjectiveDimensionLT S.X₁ (n + 1)) :
    HasInjectiveDimensionLT S.X₃ n := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasInjectiveDimensionLT n (by lia), Ext.zero_comp]
/-
**CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasInjectiveDimensionLT_X₃_iff (n : ℕ) (h₂ : Injective S.X₂) :
    HasInjectiveDimensionLT S.X₃ (n + 1) ↔ HasInjectiveDimensionLT S.X₁ (n + 2) :=
  ⟨fun _ ↦ hS.hasInjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ ↦ hS.hasInjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact

end ShortComplex

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) (n : ℕ) [HasInjectiveDimensionLT X n]
    [HasInjectiveDimensionLT Y n] :
    HasInjectiveDimensionLT (X ⊞ Y) n :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact.hasInjectiveDimensionLT_X₂ n ‹_› ‹_›
/-
**CategoryTheory.hasInjectiveDimensionLT_of_enoughProjectives** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory`。
形式化陈述：hasInjectiveDimensionLT_of_enoughProjectives [HasExt.{w} C] [EnoughProject
ives C] (X : C) (n : Nat) (hX : forall Y : C, Subsingleton (Ext Y X n)) : HasInj
ectiveDimensionLT X n
参数：X : C；n : Nat；hX : forall Y : C, Subsingleton (Ext Y X n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.EnoughProjectives.presentation`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.EnoughProjectives C] (X :
 C),   Nonempty (CategoryTheory.Pro…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.ShortComplex.exact_kernel`：exact_kernel {X Y : C} (f : X 
⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.ProjectivePresentation.epi`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X : C} (self : CategoryTheory.ProjectivePresentatio
n X),   CategoryTheory.Epi self…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃`：contravariant_
sequence_exact₃ {n₁ : Nat} (x₃ : Ext S.X₃ Y n₁) (hx₃ : (mk₀ S.g).comp x₃ (zero_a
dd n₁) = 0) {n₀ : Nat} (hn₀ : 1 + n₀ = n₁) : e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_projective`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.HasExt C] {P Y : C} …
· 使用定理 `CategoryTheory.ProjectivePresentation.projective`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X : C} (self : CategoryTheory.ProjectivePres
entation X),   CategoryTheory.Projecti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Abelian.Ext.comp.congr_simp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.HasExt C] {X Y Z : C…
· 使用引理 `CategoryTheory.Abelian.Ext.comp_zero`：comp_zero (α : Ext X Y n) (Z : C) 
(m : Nat) (p : Nat) (h : n + m = p) : α.comp (0 : Ext Y Z m) h = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.HasInjectiveDimensionLT.mk`：mk (hX : forall (i : Nat) (_ 
: n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0) : HasInjectiveDimensionLT X n 
where subsingleton' i hi Y
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hasInjectiveDimensionLT_of_enoughProjectives [HasExt.{w} C] [EnoughProjectives C] (X : C)
    (n : ℕ) (hX : ∀ Y : C, Subsingleton (Ext Y X n)) : HasInjectiveDimensionLT X n := by
  suffices ∀ ⦃d : ℕ⦄ ⦃Y : C⦄ (e : Ext Y X d) (k : ℕ), d = n + k → e = 0 from
    HasInjectiveDimensionLT.mk (fun i hi Y e ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl : d = n := by simpa using hd
    subsingleton
  | succ k hk =>
    let ⟨p⟩ := EnoughProjectives.presentation Y
    have h : (ShortComplex.mk _ _ (kernel.condition p.f)).ShortExact :=
      { exact := ShortComplex.exact_kernel p.f }
    have hd : (n + k) + 1 = d := by lia
    obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ h X e
      (by subst hd; apply Ext.eq_zero_of_projective) ((add_comm _ _).trans hd)
    simp [hk x rfl]

end CategoryTheory

section InjectiveDimension

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The injective dimension of an object in an abelian category. -/
/-
**CategoryTheory.injectiveDimension** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：injectiveDimension (X : C) : WithBot Nat∞
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injective dimension of an object in an abelian category.
-/
noncomputable def injectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasInjectiveDimensionLT X i}
/-
**CategoryTheory.injectiveDimension_eq_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：injectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) : injectiveDimension X 
= injectiveDimension Y
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用引理 `CategoryTheory.hasInjectiveDimensionLT_of_iso`：hasInjectiveDimensionLT_o
f_iso {X X' : C} (e : X ≅ X') (n : Nat) [HasInjectiveDimensionLT X n] : HasInjec
tiveDimensionLT X' n
-/
lemma injectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    injectiveDimension X = injectiveDimension Y := by
  simp only [injectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasInjectiveDimensionLT_of_iso e _,
    fun h ↦ hasInjectiveDimensionLT_of_iso e.symm _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Retract.injectiveDimension_le** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Retract`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X Y : C}   (h : CategoryTheory.Retract X Y), CategoryTheory.
injectiveDimension X ≤ CategoryTheory.injectiveDimension Y
参数：h : CategoryTheory.Retract X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le_sInf_of_subset_insert_top`：∀ {α : Type u_1} [inst : CompleteLatt
ice α] {s t : Set α}, s ⊆ insert ⊤ t → sInf t ≤ sInf s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Retract.hasInjectiveDimensionLT`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C}  
 (h : CategoryTheory.Retract X Y) (n…
-/
lemma Retract.injectiveDimension_le {X Y : C} (h : Retract X Y) :
    injectiveDimension X ≤ injectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn ↦ by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasInjectiveDimensionLT i)
/-
**CategoryTheory.injectiveDimension_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：injectiveDimension_lt_iff {X : C} {n : Nat} : injectiveDimension X < n ↔ H
asInjectiveDimensionLT X n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sInf_lt_iff`：∀ {α : Type u_1} [inst : CompleteLinearOrder α] {s : Set α}
 {b : α}, sInf s < b ↔ ∃ a ∈ s, a < b
· 使用引理 `CategoryTheory.hasInjectiveDimensionLT_of_ge`：hasInjectiveDimensionLT_of
_ge (m : Nat) (h : n <= m) [HasInjectiveDimensionLT X n] : HasInjectiveDimension
LT X m
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma injectiveDimension_lt_iff {X : C} {n : ℕ} :
    injectiveDimension X < n ↔ HasInjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ sInf_lt_iff.2 ?_⟩
  · have : injectiveDimension X ∈ _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ ↦ hasInjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi ↦ hasInjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [ENat.WithBot.lt_add_one_iff]⟩
/-
**CategoryTheory.injectiveDimension_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：injectiveDimension_le_iff (X : C) (n : Nat) : injectiveDimension X <= n ↔ 
HasInjectiveDimensionLE X n
参数：X : C；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma injectiveDimension_le_iff (X : C) (n : ℕ) :
    injectiveDimension X ≤ n ↔ HasInjectiveDimensionLE X n := by
  simp [← injectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]
/-
**CategoryTheory.injectiveDimension_ge_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：injectiveDimension_ge_iff (X : C) (n : Nat) : n <= injectiveDimension X ↔ 
¬ HasInjectiveDimensionLT X n
参数：X : C；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.injectiveDimension_lt_iff`：injectiveDimension_lt_iff {X :
 C} {n : Nat} : injectiveDimension X < n ↔ HasInjectiveDimensionLT X n
-/
lemma injectiveDimension_ge_iff (X : C) (n : ℕ) :
    n ≤ injectiveDimension X ↔ ¬ HasInjectiveDimensionLT X n := by
  contrapose!; exact injectiveDimension_lt_iff
/-
**CategoryTheory.injectiveDimension_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：injectiveDimension_eq_bot_iff (X : C) : injectiveDimension X = ⊥ ↔ Limits.
IsZero X
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.hasInjectiveDimensionLT_zero_iff_isZero`：hasInjectiveDime
nsionLT_zero_iff_isZero : HasInjectiveDimensionLT X 0 ↔ IsZero X
· 使用引理 `CategoryTheory.injectiveDimension_lt_iff`：injectiveDimension_lt_iff {X :
 C} {n : Nat} : injectiveDimension X < n ↔ HasInjectiveDimensionLT X n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `WithBot.lt_coe_bot`：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma injectiveDimension_eq_bot_iff (X : C) :
    injectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasInjectiveDimensionLT_zero_iff_isZero, ← injectiveDimension_lt_iff,
    Nat.cast_zero, ← WithBot.lt_coe_bot, bot_eq_zero', WithBot.coe_zero]
/-
**CategoryTheory.injectiveDimension_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：injectiveDimension_ne_top_iff (X : C) : injectiveDimension X != ⊤ ↔ exists
 n, HasInjectiveDimensionLE X n
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `WithBot.coe_top`：coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.injectiveDimension_le_iff`：injectiveDimension_le_iff (X :
 C) (n : Nat) : injectiveDimension X <= n ↔ HasInjectiveDimensionLE X n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma injectiveDimension_ne_top_iff (X : C) :
    injectiveDimension X ≠ ⊤ ↔ ∃ n, HasInjectiveDimensionLE X n := by
  generalize hd : injectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← injectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← injectiveDimension_le_iff, hd, WithBot.coe_top, top_le_iff] at hn
      exact ENat.natCast_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.natCast_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← injectiveDimension_le_iff] using! hd.le⟩

end CategoryTheory

end InjectiveDimension

