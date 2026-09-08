/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.ENat.Lattice

/-!
# Projective dimension

In an abelian category `C`, we shall say that `X : C` has projective dimension `< n`
if all `Ext X Y i` vanish when `n ≤ i`. This defines a type class
`HasProjectiveDimensionLT X n`. We also define a type class
`HasProjectiveDimensionLE X n` as an abbreviation for
`HasProjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasProjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasProjectiveDimensionLE`.)

We also define the projective dimension in `WithBot ℕ∞` as `projectiveDimension`,
`projectiveDimension X = ⊥` iff `X` is zero and behaves as expected on non-negative values.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object `X` in an abelian category has projective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasProjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasProjectiveDimensionLT.mk`, and the lemmas `hasProjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasProjectiveDimensionLT`.) -/
/-
**CategoryTheory.HasProjectiveDimensionLT** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheo
ry`。
形式化陈述：HasProjectiveDimensionLT (X : C) (n : Nat) : Prop where mk' :: subsingleto
n' (i : Nat) (hi : n <= i) ⦃Y : C⦄ : letI
参数：X : C；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in an abelian category has projective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasProjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasProjectiveDimensionLT.mk`, and the lemmas `hasProjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasProjectiveDimensionLT`.)
-/
class HasProjectiveDimensionLT (X : C) (n : ℕ) : Prop where mk' ::
  subsingleton' (i : ℕ) (hi : n ≤ i) ⦃Y : C⦄ :
    letI := HasExt.standard C
    Subsingleton (Ext.{max u v} X Y i)

/-- An object `X` in an abelian category has projective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i` -/
/-
**CategoryTheory.HasProjectiveDimensionLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory`。
形式化陈述：HasProjectiveDimensionLE (X : C) (n : Nat) : Prop
参数：X : C；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in an abelian category has projective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i`
-/
abbrev HasProjectiveDimensionLE (X : C) (n : ℕ) : Prop :=
  HasProjectiveDimensionLT X (n + 1)

namespace HasProjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : ℕ)

/-
**CategoryTheory.HasProjectiveDimensionLT.subsingleton** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.HasProjectiveDimensionLT`。
形式化陈述：subsingleton [hX : HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (
Y : C) : Subsingleton (Ext.{w} X Y i)
参数：i : Nat；hi : n <= i；Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `CategoryTheory.HasProjectiveDimensionLT.subsingleton'`：∀ {C : Type u} {i
nst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C} {X :
 C} {n : ℕ}   [self : CategoryTheory.HasPro…
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma subsingleton [hX : HasProjectiveDimensionLT X n] (i : ℕ) (hi : n ≤ i) (Y : C) :
    Subsingleton (Ext.{w} X Y i) := by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
/-
**CategoryTheory.HasProjectiveDimensionLT.mk** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.HasProjectiveDimensionLT`。
形式化陈述：mk (hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e 
= 0) : HasProjectiveDimensionLT X n where subsingleton' i hi Y
参数：hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0。
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
lemma mk (hX : ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext X Y i), e = 0) :
    HasProjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext X Y i) := ⟨fun e₁ e₂ ↦ by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasProjectiveDimensionLT

/-
**CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} {i : ℕ} (e : C
ategoryTheory.Abelian.Ext X Y i) (n : ℕ)   [CategoryTheory.HasProjectiveDimensio
nLT X n], n ≤ i → e = 0
参数：e : CategoryTheory.Abelian.Ext X Y i；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `CategoryTheory.HasProjectiveDimensionLT.subsingleton`：subsingleton [hX :
 HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (E
xt.{w} X Y i)
-/
lemma Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : ℕ} (e : Ext X Y i) (n : ℕ) [HasProjectiveDimensionLT X n]
    (hi : n ≤ i) : e = 0 :=
  (HasProjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : ℕ)

/-
**CategoryTheory.hasProjectiveDimensionLT_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：hasProjectiveDimensionLT_iff [HasExt.{w} C] : HasProjectiveDimensionLT X n
 ↔ forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
· 使用引理 `CategoryTheory.HasProjectiveDimensionLT.mk`：mk (hX : forall (i : Nat) (_
 : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0) : HasProjectiveDimensionLT X 
n where subsingleton' i hi Y
-/
lemma hasProjectiveDimensionLT_iff [HasExt.{w} C] :
    HasProjectiveDimensionLT X n ↔
      ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext X Y i), e = 0 :=
  ⟨fun _ _ hi _ e ↦ e.eq_zero_of_hasProjectiveDimensionLT n hi,
    HasProjectiveDimensionLT.mk⟩

variable {X} in
/-
**CategoryTheory.Limits.IsZero.hasProjectiveDimensionLT_zero** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X : C},   CategoryTheory.Limits.IsZero X → CategoryTheory.Ha
sProjectiveDimensionLT X 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasProjectiveDimensionLT_iff`：hasProjectiveDimensionLT_if
f [HasExt.{w} C] : HasProjectiveDimensionLT X n ↔ forall (i : Nat) (_ : n <= i) 
⦃Y : C⦄, forall (e : Ext X Y i), …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_id_comp`：mk₀_id_comp (α : Ext X Y n) : (m
k₀ (𝟙 X)).comp α (zero_add n) = α
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_zero`：mk₀_zero : mk₀ (0 : X ⟶ Y) = 0
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0
-/
lemma Limits.IsZero.hasProjectiveDimensionLT_zero (hX : IsZero X) :
    HasProjectiveDimensionLT X 0 := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.mk₀_id_comp, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasProjectiveDimensionLT (0 : C) 0 :=
  (isZero_zero C).hasProjectiveDimensionLT_zero
/-
**CategoryTheory.isZero_of_hasProjectiveDimensionLT_zero** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory`。
形式化陈述：isZero_of_hasProjectiveDimensionLT_zero [HasProjectiveDimensionLT X 0] : I
sZero X
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
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isZero_of_hasProjectiveDimensionLT_zero [HasProjectiveDimensionLT X 0] : IsZero X := by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 0 (by rfl)
/-
**CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：hasProjectiveDimensionLT_zero_iff_isZero : HasProjectiveDimensionLT X 0 ↔ 
IsZero X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isZero_of_hasProjectiveDimensionLT_zero`：isZero_of_hasPro
jectiveDimensionLT_zero [HasProjectiveDimensionLT X 0] : IsZero X
· 使用定理 `CategoryTheory.Limits.IsZero.hasProjectiveDimensionLT_zero`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]
 {X : C},   CategoryTheory.Limits.IsZero X → Cat…
-/
lemma hasProjectiveDimensionLT_zero_iff_isZero : HasProjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ ↦ isZero_of_hasProjectiveDimensionLT_zero X, fun h ↦ h.hasProjectiveDimensionLT_zero⟩
/-
**CategoryTheory.hasProjectiveDimensionLT_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：hasProjectiveDimensionLT_of_ge (m : Nat) (h : n <= m) [HasProjectiveDimens
ionLT X n] : HasProjectiveDimensionLT X m
参数：m : Nat；h : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasProjectiveDimensionLT_iff`：hasProjectiveDimensionLT_if
f [HasExt.{w} C] : HasProjectiveDimensionLT X n ↔ forall (i : Nat) (_ : n <= i) 
⦃Y : C⦄, forall (e : Ext X Y i), …
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
-/
lemma hasProjectiveDimensionLT_of_ge (m : ℕ) (h : n ≤ m)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X m := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasProjectiveDimensionLT n (by lia)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (n + k) :=
  hasProjectiveDimensionLT_of_ge X n (n + k) (by lia)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (k + n) :=
  hasProjectiveDimensionLT_of_ge X n (k + n) (by lia)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasProjectiveDimensionLT X (n + 1))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Projective X] : HasProjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_projective

variable {X} in
/-
**CategoryTheory.projective_iff_subsingleton_ext_one** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：projective_iff_subsingleton_ext_one [HasExt.{w} C] : Projective X ↔ forall
 ⦃Y : C⦄, Subsingleton (Ext X Y 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.HasProjectiveDimensionLT.subsingleton`：subsingleton [hX :
 HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (E
xt.{w} X Y i)
· 使用定理 `CategoryTheory.instHasProjectiveDimensionLTOfNatNatOfProjective`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abeli
an C] (X : C)   [CategoryTheory.Projective X], Catego…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`：covariant_sequence
_exact₃ {n₀ : Nat} (x₃ : Ext X S.X₃ n₀) {n₁ : Nat} (hn₁ : n₀ + 1 = n₁) (hx₃ : x₃
.comp hS.extClass hn₁ = 0) : exists (x₂ : …
· 使用定理 `CategoryTheory.ShortComplex.exact_kernel`：exact_kernel {X Y : C} (f : X 
⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
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
lemma projective_iff_subsingleton_ext_one [HasExt.{w} C] :
    Projective X ↔ ∀ ⦃Y : C⦄, Subsingleton (Ext X Y 1) := by
  refine ⟨fun h ↦ HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h ↦ ⟨fun f g _ ↦ ?_⟩⟩
  obtain ⟨φ, hφ⟩ :=
    Ext.covariant_sequence_exact₃ _ { exact := ShortComplex.exact_kernel g }
      (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective (by simpa using hφ)⟩

variable {X} in
/-
**CategoryTheory.projective_iff_hasProjectiveDimensionLT_one** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory`。
形式化陈述：projective_iff_hasProjectiveDimensionLT_one : Projective X ↔ HasProjective
DimensionLT X 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `CategoryTheory.instHasProjectiveDimensionLTOfNatNatOfProjective`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abeli
an C] (X : C)   [CategoryTheory.Projective X], Catego…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.projective_iff_subsingleton_ext_one`：projective_iff_subsi
ngleton_ext_one [HasExt.{w} C] : Projective X ↔ forall ⦃Y : C⦄, Subsingleton (Ex
t X Y 1)
· 使用引理 `CategoryTheory.HasProjectiveDimensionLT.subsingleton`：subsingleton [hX :
 HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (E
xt.{w} X Y i)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma projective_iff_hasProjectiveDimensionLT_one :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ projective_iff_subsingleton_ext_one.2
    (HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩
/-
**CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory`。
形式化陈述：projective_iff_hasProjectiveDimensionLE_zero : Projective X ↔ HasProjectiv
eDimensionLE X 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.projective_iff_hasProjectiveDimensionLT_one`：projective_i
ff_hasProjectiveDimensionLT_one : Projective X ↔ HasProjectiveDimensionLT X 1
-/
lemma projective_iff_hasProjectiveDimensionLE_zero : Projective X ↔ HasProjectiveDimensionLE X 0 :=
  projective_iff_hasProjectiveDimensionLT_one
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [HasProjectiveDimensionLT X 1] : Projective X :=
  projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›

end

/-
**CategoryTheory.Retract.hasProjectiveDimensionLT** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Retract`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X Y : C}   (h : CategoryTheory.Retract X Y) (n : ℕ) [Categor
yTheory.HasProjectiveDimensionLT Y n],   CategoryTheory.HasProjectiveDimensionLT
 X n
参数：h : CategoryTheory.Retract X Y；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasExt.standard`：∀ (C : Type u) [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Abelian C], CategoryTheory.HasExt C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasProjectiveDimensionLT_iff`：hasProjectiveDimensionLT_if
f [HasExt.{w} C] : HasProjectiveDimensionLT X n ↔ forall (i : Nat) (_ : n <= i) 
⦃Y : C⦄, forall (e : Ext X Y i), …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_id_comp`：mk₀_id_comp (α : Ext X Y n) : (m
k₀ (𝟙 X)).comp α (zero_add n) = α
· 使用定理 `CategoryTheory.Retract.retract`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X Y : C} (self : CategoryTheory.Retract X Y),   CategoryTheory
.CategoryStruct.comp…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_comp_mk₀`：mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y
 ⟶ Z) : (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero`：comp_assoc_of_
second_deg_zero {a₁ a₃ a₁₃ : Nat} (α : Ext X Y a₁) (β : Ext Y Z 0) (γ : Ext Z T 
a₃) (h₁₃ : a₁ + a₃ = a₁₃) : (α.comp β (add_zer…
· 使用定理 `CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : CategoryTheory.HasExt C] {X Y : C} …
· 使用引理 `CategoryTheory.Abelian.Ext.comp_zero`：comp_zero (α : Ext X Y n) (Z : C) 
(m : Nat) (p : Nat) (h : n + m = p) : α.comp (0 : Ext Y Z m) h = 0
-/
lemma Retract.hasProjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : ℕ)
    [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.mk₀_id_comp, ← h.retract, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero,
    ((Ext.mk₀ h.r).comp x (zero_add i)).eq_zero_of_hasProjectiveDimensionLT n hi,
    Ext.comp_zero]
/-
**CategoryTheory.hasProjectiveDimensionLT_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：hasProjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : Nat) [HasProj
ectiveDimensionLT X n] : HasProjectiveDimensionLT X' n
参数：e : X ≅ X'；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Retract.hasProjectiveDimensionLT`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C} 
  (h : CategoryTheory.Retract X Y) (n…
-/
lemma hasProjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : ℕ)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X' n :=
  e.symm.retract.hasProjectiveDimensionLT n

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
include hS

-- In the following lemmas, the parameters `HasProjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

/-
**CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasProjectiveDimensionLT_X₂ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ n) :
    HasProjectiveDimensionLT S.X₂ n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasProjectiveDimensionLT n hi, Ext.comp_zero]
/-
**CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasProjectiveDimensionLT_X₃ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₂ : HasProjectiveDimensionLT S.X₂ (n + 1)) :
    HasProjectiveDimensionLT S.X₃ (n + 1) := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS _ x₃
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) hi) (add_comm _ _)
    rw [x₁.eq_zero_of_hasProjectiveDimensionLT n (by lia), Ext.comp_zero]
/-
**CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasProjectiveDimensionLT_X₁ (h₂ : HasProjectiveDimensionLT S.X₂ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ (n + 1)) :
    HasProjectiveDimensionLT S.X₁ n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasProjectiveDimensionLT n (by lia), Ext.comp_zero]
/-
**CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasProjectiveDimensionLT_X₃_iff (n : ℕ) (h₂ : Projective S.X₂) :
    HasProjectiveDimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n + 1) :=
  ⟨fun _ ↦ hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ ↦ hS.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact

end ShortComplex

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) (n : ℕ) [HasProjectiveDimensionLT X n] [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT (X ⊞ Y) n :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact.hasProjectiveDimensionLT_X₂ n ‹_› ‹_›
/-
**CategoryTheory.hasProjectiveDimensionLT_of_enoughInjectives** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory`。
形式化陈述：hasProjectiveDimensionLT_of_enoughInjectives [HasExt.{w} C] [EnoughInjecti
ves C] (X : C) (n : Nat) (hX : forall Y : C, Subsingleton (Ext X Y n)) : HasProj
ectiveDimensionLT X n
参数：X : C；n : Nat；hX : forall Y : C, Subsingleton (Ext X Y n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.EnoughInjectives.presentation`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.EnoughInjectives C] (X 
: C),   Nonempty (CategoryTheory.I…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.InjectivePresentation.mono`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.InjectivePresentat
ion X),   CategoryTheory.Mono s…
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁`：covariant_sequence
_exact₁ {n₁ : Nat} (x₁ : Ext X S.X₁ n₁) (hx₁ : x₁.comp (mk₀ S.f) (add_zero n₁) =
 0) {n₀ : Nat} (hn₀ : n₀ + 1 = n₁) : exist…
· 使用引理 `CategoryTheory.Abelian.Ext.eq_zero_of_injective`：eq_zero_of_injective [H
asExt.{w} C] {X I : C} {n : Nat} [Injective I] (e : Ext X I (n + 1)) : e = 0
· 使用定理 `CategoryTheory.InjectivePresentation.injective`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.InjectivePres
entation X),   CategoryTheory.Inject…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Abelian.Ext.comp.congr_simp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.HasExt C] {X Y Z : C…
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.HasProjectiveDimensionLT.mk`：mk (hX : forall (i : Nat) (_
 : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0) : HasProjectiveDimensionLT X 
n where subsingleton' i hi Y
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hasProjectiveDimensionLT_of_enoughInjectives [HasExt.{w} C] [EnoughInjectives C] (X : C)
    (n : ℕ) (hX : ∀ Y : C, Subsingleton (Ext X Y n)) : HasProjectiveDimensionLT X n := by
  suffices ∀ ⦃d : ℕ⦄ ⦃Y : C⦄ (e : Ext X Y d) (k : ℕ), d = n + k → e = 0 from
    HasProjectiveDimensionLT.mk (fun i hi Y e ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl : d = n := by simpa using hd
    subsingleton
  | succ k hk =>
    let ⟨p⟩ := EnoughInjectives.presentation Y
    have h : (ShortComplex.mk _ _ (cokernel.condition p.f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel p.f }
    have hd : n + k + 1 = d := by lia
    obtain ⟨x, rfl⟩ := Ext.covariant_sequence_exact₁ X h e
      (by subst hd; apply Ext.eq_zero_of_injective) hd
    simp [hk x rfl]

end CategoryTheory

section ProjectiveDimension

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The projective dimension of an object in an abelian category. -/
/-
**CategoryTheory.projectiveDimension** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：projectiveDimension (X : C) : WithBot Nat∞
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projective dimension of an object in an abelian category.
-/
noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}
/-
**CategoryTheory.projectiveDimension_eq_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) : projectiveDimension 
X = projectiveDimension Y
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用引理 `CategoryTheory.hasProjectiveDimensionLT_of_iso`：hasProjectiveDimensionLT
_of_iso {X X' : C} (e : X ≅ X') (n : Nat) [HasProjectiveDimensionLT X n] : HasPr
ojectiveDimensionLT X' n
-/
lemma projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasProjectiveDimensionLT_of_iso e _,
    fun h ↦ hasProjectiveDimensionLT_of_iso e.symm _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Retract.projectiveDimension_le** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Retract`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X Y : C}   (h : CategoryTheory.Retract X Y), CategoryTheory.
projectiveDimension X ≤ CategoryTheory.projectiveDimension Y
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
· 使用定理 `CategoryTheory.Retract.hasProjectiveDimensionLT`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C} 
  (h : CategoryTheory.Retract X Y) (n…
-/
lemma Retract.projectiveDimension_le {X Y : C} (h : Retract X Y) :
    projectiveDimension X ≤ projectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn ↦ by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasProjectiveDimensionLT i)
/-
**CategoryTheory.projectiveDimension_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：projectiveDimension_lt_iff {X : C} {n : Nat} : projectiveDimension X < n ↔
 HasProjectiveDimensionLT X n
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
· 使用引理 `CategoryTheory.hasProjectiveDimensionLT_of_ge`：hasProjectiveDimensionLT_
of_ge (m : Nat) (h : n <= m) [HasProjectiveDimensionLT X n] : HasProjectiveDimen
sionLT X m
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
lemma projectiveDimension_lt_iff {X : C} {n : ℕ} :
    projectiveDimension X < n ↔ HasProjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ sInf_lt_iff.2 ?_⟩
  · have : projectiveDimension X ∈ _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ ↦ hasProjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi ↦ hasProjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [ENat.WithBot.lt_add_one_iff]⟩
/-
**CategoryTheory.projectiveDimension_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：projectiveDimension_le_iff (X : C) (n : Nat) : projectiveDimension X <= n 
↔ HasProjectiveDimensionLE X n
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
lemma projectiveDimension_le_iff (X : C) (n : ℕ) :
    projectiveDimension X ≤ n ↔ HasProjectiveDimensionLE X n := by
  simp [← projectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]
/-
**CategoryTheory.projectiveDimension_ge_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：projectiveDimension_ge_iff (X : C) (n : Nat) : n <= projectiveDimension X 
↔ ¬ HasProjectiveDimensionLT X n
参数：X : C；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.projectiveDimension_lt_iff`：projectiveDimension_lt_iff {X
 : C} {n : Nat} : projectiveDimension X < n ↔ HasProjectiveDimensionLT X n
-/
lemma projectiveDimension_ge_iff (X : C) (n : ℕ) :
    n ≤ projectiveDimension X ↔ ¬ HasProjectiveDimensionLT X n := by
  contrapose!; exact projectiveDimension_lt_iff
/-
**CategoryTheory.projectiveDimension_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：projectiveDimension_eq_bot_iff (X : C) : projectiveDimension X = ⊥ ↔ Limit
s.IsZero X
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero`：hasProjectiveDi
mensionLT_zero_iff_isZero : HasProjectiveDimensionLT X 0 ↔ IsZero X
· 使用引理 `CategoryTheory.projectiveDimension_lt_iff`：projectiveDimension_lt_iff {X
 : C} {n : Nat} : projectiveDimension X < n ↔ HasProjectiveDimensionLT X n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `WithBot.lt_coe_bot`：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma projectiveDimension_eq_bot_iff (X : C) :
    projectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero, ← projectiveDimension_lt_iff,
    Nat.cast_zero, ← WithBot.lt_coe_bot, bot_eq_zero', WithBot.coe_zero]
/-
**CategoryTheory.projectiveDimension_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：projectiveDimension_ne_top_iff (X : C) : projectiveDimension X != ⊤ ↔ exis
ts n, HasProjectiveDimensionLE X n
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
· 使用引理 `CategoryTheory.projectiveDimension_le_iff`：projectiveDimension_le_iff (X
 : C) (n : Nat) : projectiveDimension X <= n ↔ HasProjectiveDimensionLE X n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma projectiveDimension_ne_top_iff (X : C) :
    projectiveDimension X ≠ ⊤ ↔ ∃ n, HasProjectiveDimensionLE X n := by
  generalize hd : projectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← projectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← projectiveDimension_le_iff, hd, WithBot.coe_top, top_le_iff] at hn
      exact ENat.natCast_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.natCast_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← projectiveDimension_le_iff] using! hd.le⟩
/-
**CategoryTheory.projectiveDimension_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：projectiveDimension_eq_zero_iff (X : C) : projectiveDimension X = 0 ↔ Proj
ective X ∧ ¬ Limits.IsZero X
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.projectiveDimension_eq_bot_iff`：projectiveDimension_eq_bo
t_iff (X : C) : projectiveDimension X = ⊥ ↔ Limits.IsZero X
· 使用引理 `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`：projective_
iff_hasProjectiveDimensionLE_zero : Projective X ↔ HasProjectiveDimensionLE X 0
· 使用引理 `CategoryTheory.projectiveDimension_le_iff`：projectiveDimension_le_iff (X
 : C) (n : Nat) : projectiveDimension X <= n ↔ HasProjectiveDimensionLE X n
· 使用引理 `WithBot.lt_zero_iff_eq_bot`：lt_zero_iff_eq_bot {α : Type*} [AddMonoid α]
 [Preorder α] [CanonicallyOrderedAdd α] (a : WithBot α) : a < 0 ↔ a = ⊥
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma projectiveDimension_eq_zero_iff (X : C) :
    projectiveDimension X = 0 ↔ Projective X ∧ ¬ Limits.IsZero X := by
  rw [← projectiveDimension_eq_bot_iff, projective_iff_hasProjectiveDimensionLE_zero,
    ← projectiveDimension_le_iff, ← WithBot.lt_zero_iff_eq_bot, not_lt, Nat.cast_zero,
    le_antisymm_iff]

end CategoryTheory

end ProjectiveDimension

