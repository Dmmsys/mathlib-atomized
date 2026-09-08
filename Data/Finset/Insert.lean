/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Util.Delaborators

/-!
# Constructing finite sets by adding one element

This file contains the definitions of `{a} : Finset α`, `insert a s : Finset α` and `Finset.cons`,
all ways to construct a `Finset` by adding one element.

## Main declarations

* `Finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `Finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `Finset α`,
  then it holds for the finset obtained by inserting a new element.
* `Finset.instSingletonFinset`: Denoted by `{a}`; the finset consisting of one element.
* `insert` and `Finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*}

namespace Finset

/-! ### Subset and strict subset relations -/

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### singleton -/


section Singleton

variable {s : Finset α} {a b : α}

/-- `{a} : Finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `DecidableEq` instance for `α`.
-/
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{a} : Finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `DecidableEq` insta
nce for `α`.
-/
instance : Singleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]
/-
**Finset.singleton_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_val (a : α) : ({a} : Finset α).1 = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl

@[simp, grind =]
/-
**Finset.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
-/
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  Multiset.mem_singleton
/-
**Finset.eq_of_mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_singleton {x y : α} (h : x in ({y} : Finset α)) : x = y
参数：h : x in ({y} : Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Finset α)) : x = y :=
  mem_singleton.1 h
/-
**Finset.notMem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem notMem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a ≠ b :=
  not_congr mem_singleton
/-
**Finset.mem_singleton_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_singleton_self (a : α) : a in ({a} : Finset α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_singleton_self (a : α) : a ∈ ({a} : Finset α) :=
  mem_singleton.mpr rfl

@[simp]
/-
**Finset.val_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_eq_singleton_iff {a : α} {s : Finset α} : s.val = {a} ↔ s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_eq_singleton_iff {a : α} {s : Finset α} : s.val = {a} ↔ s = {a} := by
  rw [← val_inj]
  rfl
/-
**Finset.singleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_injective : Injective (singleton : α -> Finset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem singleton_injective : Injective (singleton : α → Finset α) := fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)

@[simp]
/-
**Finset.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_inj : ({a} : Finset α) = {b} ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
-/
theorem singleton_inj : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.singleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_nonempty (a : α) : ({a} : Finset α).Nonempty
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩

@[simp]
/-
**Finset.singleton_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_ne_empty (a : α) : ({a} : Finset α) != ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
-/
theorem singleton_ne_empty (a : α) : ({a} : Finset α) ≠ ∅ :=
  (singleton_nonempty a).ne_empty

@[simp]
/-
**Finset.empty_ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_ne_singleton (a : α) : ∅ != ({a} : Finset α)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Finset α)
 != ∅
-/
theorem empty_ne_singleton (a : α) : ∅ ≠ ({a} : Finset α) :=
  (singleton_ne_empty a).symm
/-
**Finset.empty_ssubset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_ssubset_singleton : (∅ : Finset α) ⊂ {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.empty_ssubset`：∀ {α : Type u_1} {s : Finset α}, s.Nonemp
ty → ∅ ⊂ s
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
-/
theorem empty_ssubset_singleton : (∅ : Finset α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp, norm_cast]
/-
**Finset.coe_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} := by grind

@[simp, norm_cast]
/-
**Finset.coe_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by grind

@[norm_cast]
/-
**Finset.coe_subset_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_subset_singleton : (s : Set α) subseteq {a} ↔ s subseteq {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_subset_singleton : (s : Set α) ⊆ {a} ↔ s ⊆ {a} := by grind

@[norm_cast]
/-
**Finset.singleton_subset_coe** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_subset_coe : {a} subseteq (s : Set α) ↔ {a} subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleton_subset_coe : {a} ⊆ (s : Set α) ↔ {a} ⊆ s := by grind
/-
**Finset.eq_singleton_iff_unique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a in s ∧ fo
rall x in s, x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by
  grind
/-
**Finset.eq_singleton_iff_nonempty_unique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} : s = {a} ↔ s.
Nonempty ∧ forall x in s, x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a := by
  grind [singleton_nonempty]
/-
**Finset.nonempty_iff_eq_singleton_default** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} : s.Nonempty ↔
 s = {default}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} :
    s.Nonempty ↔ s = {default} := by
  simp [eq_singleton_iff_nonempty_unique_mem, eq_iff_true_of_subsingleton]

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default
/-
**Finset.singleton_iff_unique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_iff_unique_mem (s : Finset α) : (exists a, s = {a}) ↔ exists! a,
 a in s
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]
/-
**Finset.singleton_subset_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) subseteq 
s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) ⊆ s ↔ a ∈ s := by
  grind

@[simp, grind =]
/-
**Finset.singleton_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_subset_iff {s : Finset α} {a : α} : {a} subseteq s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_subset_set_iff`：singleton_subset_set_iff {s : Set α} {a
 : α} : ↑({a} : Finset α) subseteq s ↔ a in s
-/
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff

@[simp]
/-
**Finset.subset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_singleton_iff {s : Finset α} {a : α} : s subseteq {a} ↔ s = ∅ ∨ s =
 {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} := by
  grind
/-
**Finset.singleton_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_subset_singleton : ({a} : Finset α) subseteq {b} ↔ a = b
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
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_subset_singleton : ({a} : Finset α) ⊆ {b} ↔ a = b := by simp
/-
**Finset.Nonempty.subset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempt
y`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α}, s.Nonempty → (s ⊆ {a} ↔ s = {a})
参数：s ⊆ {a} ↔ s = {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.subset_singleton_iff`：subset_singleton_iff {s : Finset α} {a : α}
 : s subseteq {a} ↔ s = ∅ ∨ s = {a}
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
-/
protected theorem Nonempty.subset_singleton_iff {s : Finset α} {a : α} (h : s.Nonempty) :
    s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff.trans <| or_iff_right h.ne_empty
/-
**Finset.subset_singleton_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_singleton_iff' {s : Finset α} {a : α} : s subseteq {a} ↔ forall b i
n s, b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem subset_singleton_iff' {s : Finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
  forall₂_congr fun _ _ => mem_singleton

@[simp]
/-
**Finset.ssubset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ := by grind
/-
**Finset.eq_empty_of_ssubset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = 
∅
参数：hs : s ⊂ {x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.ssubset_singleton_iff`：ssubset_singleton_iff {s : Finset α} {a : 
α} : s ⊂ {a} ↔ s = ∅
-/
theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/-- A finset is nontrivial if it has at least two elements. -/
/-
**Finset.Nontrivial** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finset is nontrivial if it has at least two elements.
-/
protected abbrev Nontrivial (s : Finset α) : Prop := (s : Set α).Nontrivial

@[grind =]
/-
**Finset.nontrivial_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nontrivial_def {s : Finset α} : s.Nontrivial ↔ exists a, a in s ∧ exists b
, b in s ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nontrivial_def {s : Finset α} : s.Nontrivial ↔ ∃ a, a ∈ s ∧ ∃ b, b ∈ s ∧ a ≠ b := Iff.rfl

nonrec lemma Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty := hs.nonempty

@[simp]
/-
**Finset.not_nontrivial_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_nontrivial_empty : ¬(∅ : Finset α).Nontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_nontrivial_empty : ¬(∅ : Finset α).Nontrivial := by simp [Finset.Nontrivial]

@[simp]
/-
**Finset.not_nontrivial_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_nontrivial_singleton : ¬({a} : Finset α).Nontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_nontrivial_singleton : ¬({a} : Finset α).Nontrivial := by simp [Finset.Nontrivial]
/-
**Finset.Nontrivial.ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α}, s.Nontrivial → s ≠ {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.not_nontrivial_singleton`：not_nontrivial_singleton : ¬({a} : Fins
et α).Nontrivial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Nontrivial.ne_singleton (hs : s.Nontrivial) : s ≠ {a} := by
  rintro rfl; exact not_nontrivial_singleton hs

nonrec lemma Nontrivial.exists_ne (hs : s.Nontrivial) (a : α) : ∃ b ∈ s, b ≠ a := hs.exists_ne _
/-
**Finset.eq_singleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_singleton_or_nontrivial (ha : a in s) : s = {a} ∨ s.Nontrivial
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
· 使用引理 `Set.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in s)
 : s = {a} ∨ s.Nontrivial
-/
theorem eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial := by
  rw [← coe_eq_singleton]; exact Set.eq_singleton_or_nontrivial ha
/-
**Finset.nontrivial_iff_ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nontrivial_iff_ne_singleton (ha : a in s) : s.Nontrivial ↔ s != {a}
参数：ha : a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nontrivial.ne_singleton`：∀ {α : Type u_1} {s : Finset α} {a : α},
 s.Nontrivial → s ≠ {a}
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Finset.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in
 s) : s = {a} ∨ s.Nontrivial
-/
theorem nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩
/-
**Finset.Nonempty.exists_eq_singleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `F
inset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivia
l
参数：∃ a, s = {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `Finset.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in
 s) : s = {a} ∨ s.Nontrivial
-/
theorem Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
/-
**Finset.nontrivial_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, (↑s).Nontrivial ↔ s.Nontrivial
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma nontrivial_coe : (s : Set α).Nontrivial ↔ s.Nontrivial := .rfl

alias ⟨Nontrivial.of_coe, Nontrivial.coe⟩ := nontrivial_coe
/-
**Finset.Nontrivial.not_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontr
ivial`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α}, s.Nontrivial → ¬s ⊆ {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nontrivial.not_subset_singleton`：∀ {α : Type u} {s : Set α} {x : α},
 s.Nontrivial → ¬s ⊆ {x}
· 使用定理 `Finset.Nontrivial.coe`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivial → (
↑s).Nontrivial
-/
lemma Nontrivial.not_subset_singleton (hs : s.Nontrivial) : ¬s ⊆ {a} :=
  mod_cast hs.coe.not_subset_singleton
/-
**Finset.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instNontrivial [Nonempty α] : Nontrivial (Finset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Finset.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Finset α)
 != ∅
-/
instance instNontrivial [Nonempty α] : Nontrivial (Finset α) :=
  ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (Finset α) where
  default := ∅
  uniq _ := eq_empty_of_forall_notMem isEmptyElim
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : α) : Unique ({i} : Finset α) where
  default := ⟨i, mem_singleton_self i⟩
  uniq j := Subtype.ext <| mem_singleton.mp j.2

@[simp]
/-
**Finset.default_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：default_singleton (i : α) : ((default : ({i} : Finset α)) : α) = i
参数：i : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma default_singleton (i : α) : ((default : ({i} : Finset α)) : α) = i := rfl
/-
**Finset.Nontrivial.instDecidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Nontrivi
al`。
形式化陈述：{α : Type u_1} → DecidablePred Finset.Nontrivial
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
instance Nontrivial.instDecidablePred : DecidablePred (Finset.Nontrivial (α := α)) := fun s =>
  /-
  We don't use `Finset.one_lt_card_iff_nontrivial`
  because `Finset.card` is defined in a different file.
  -/
  Quotient.recOnSubsingleton (motive := fun (s : Multiset α) =>
      (h : s.Nodup) → Decidable (Finset.Nontrivial ⟨s, h⟩))
    s.val (fun l h => match l with
      | [] => isFalse (by simp)
      | [_] => isFalse (by simp [SetLike.coe])
      | a :: b :: _ => isTrue ⟨a, by simp, b, by simp,
        List.ne_of_not_mem_cons (List.nodup_cons.mp h).left⟩) s.nodup

end Singleton

/-! ### cons -/


section Cons

variable {s t : Finset α} {a b : α}

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `DecidableEq α`,
and the union is guaranteed to be disjoint. -/
/-
**Finset.cons** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α
参数：a : α；s : Finset α；h : a ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is 
the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `De
cidableEq α`,
and the union is guaranteed to be disjoint.
-/
def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp, grind =]
/-
**Finset.mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
-/
theorem mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s :=
  Multiset.mem_cons
/-
**Finset.mem_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b ∉ s} (ha : a in s) : a in
 cons b s hb
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem mem_cons_of_mem {a b : α} {s : Finset α} {hb : b ∉ s} (ha : a ∈ s) : a ∈ cons b s hb :=
  Multiset.mem_cons_of_mem ha
/-
**Finset.mem_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_cons_self (a : α) (s : Finset α) {h} : a in cons a s h
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
-/
theorem mem_cons_self (a : α) (s : Finset α) {h} : a ∈ cons a s h :=
  Multiset.mem_cons_self _ _

@[simp]
/-
**Finset.cons_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl
/-
**Finset.eq_of_mem_cons_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_cons_of_notMem (has : a ∉ s) (h : b in cons a s has) (hb : b ∉ s
) : b = a
参数：has : a ∉ s；h : b in cons a s has；hb : b ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
-/
theorem eq_of_mem_cons_of_notMem (has : a ∉ s) (h : b ∈ cons a s has) (hb : b ∉ s) : b = a :=
  (mem_cons.1 h).resolve_right hb
/-
**Finset.mem_of_mem_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_mem_cons_of_ne {s : Finset α} {a : α} {has} {i : α} (hi : i in cons
 a s has) (hia : i != a) : i in s
参数：hi : i in cons a s has；hia : i != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
-/
theorem mem_of_mem_cons_of_ne {s : Finset α} {a : α} {has} {i : α}
    (hi : i ∈ cons a s has) (hia : i ≠ a) : i ∈ s :=
  (mem_cons.1 hi).resolve_left hia
/-
**Finset.forall_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (forall x, x in cons a s h -
> p x) ↔ p a ∧ forall x, x in s -> p x
参数：h : a ∉ s；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_mem_cons (h : a ∉ s) (p : α → Prop) :
    (∀ x, x ∈ cons a s h → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  grind

/-- Useful in proofs by induction. -/
/-
**Finset.forall_of_forall_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_of_forall_cons {p : α -> Prop} {h : a ∉ s} (H : forall x, x in cons
 a s h -> p x) (x) (h : x in s) : p x
参数：H : forall x, x in cons a s h -> p x；x；h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s

--- 原说明 ---
Useful in proofs by induction.
-/
theorem forall_of_forall_cons {p : α → Prop} {h : a ∉ s} (H : ∀ x, x ∈ cons a s h → p x) (x)
    (h : x ∈ s) : p x :=
  H _ <| mem_cons.2 <| Or.inr h

@[simp]
/-
**Finset.mk_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) : (⟨a ::ₘ s, h⟩ : Finset α)
 = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1
参数：h : (a ::ₘ s).Nodup。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl

@[simp]
/-
**Finset.cons_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_empty (a : α) : cons a ∅ (notMem_empty _) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem cons_empty (a : α) : cons a ∅ (notMem_empty _) = {a} := rfl

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.cons_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
-/
theorem cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 <| Or.inl rfl⟩
/-
**Finset.cons_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α} (h : a ∉ s), Finset.cons a s h ≠ ∅
参数：h : a ∉ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
-/
@[simp] theorem cons_ne_empty (h : a ∉ s) : cons a s h ≠ ∅ := (cons_nonempty _).ne_empty

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finset.nonempty_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m ≠ 0 := by
  induction m using Multiset.induction_on <;> simp

@[simp]
/-
**Finset.coe_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (s : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a (s : Set α) := by
  ext
  simp
/-
**Finset.subset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_cons (h : a ∉ s) : s subseteq s.cons a h
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_cons`：subset_cons (s : Multiset α) (a : α) : s subseteq 
a ::ₘ s
-/
theorem subset_cons (h : a ∉ s) : s ⊆ s.cons a h :=
  Multiset.subset_cons _ _
/-
**Finset.ssubset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ssubset_cons`：ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s
) : s ⊂ a ::ₘ s
-/
theorem ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h :=
  Multiset.ssubset_cons h
/-
**Finset.cons_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_subset {h : a ∉ s} : s.cons a h subseteq t ↔ a in t ∧ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.cons_subset`：cons_subset {a : α} {s t : Multiset α} : a ::ₘ s s
ubseteq t ↔ a in t ∧ s subseteq t
-/
theorem cons_subset {h : a ∉ s} : s.cons a h ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  Multiset.cons_subset

@[simp]
/-
**Finset.cons_subset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_subset_cons {hs ht} : s.cons a hs subseteq t.cons a ht ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Set.insert_subset_insert_iff`：∀ {α : Type u_1} {s t : Set α} {a : α}, a 
∉ s → (insert a s ⊆ insert a t ↔ s ⊆ t)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t := by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]
/-
**Finset.ssubset_iff_exists_cons_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_iff_exists_cons_subset : s ⊂ t ↔ exists (a : _) (h : a ∉ s), s.con
s a h subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ (a : _) (h : a ∉ s), s.cons a h ⊆ t := by
  grind
/-
**Finset.cons_swap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_swap (hb : b ∉ s) (ha : a ∉ s.cons b hb) : (s.cons b hb).cons a ha = 
(s.cons a fun h => ha (mem_cons.mpr (.inr h))).cons b fun h => ha (mem_cons.mpr 
(.inl ((mem_cons.mp h).elim symm (fun h => False.elim (hb h)))))
参数：hb : b ∉ s；ha : a ∉ s.cons b hb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
-/
theorem cons_swap (hb : b ∉ s) (ha : a ∉ s.cons b hb) :
    (s.cons b hb).cons a ha = (s.cons a fun h ↦ ha (mem_cons.mpr (.inr h))).cons b fun h ↦
      ha (mem_cons.mpr (.inl ((mem_cons.mp h).elim symm (fun h ↦ False.elim (hb h))))) :=
  eq_of_veq <| Multiset.cons_swap a b s.val

/-- Split the added element of cons off a Pi type. -/
@[simps!]
/-
**Finset.consPiProd** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：consPiProd (f : α -> Type*) (has : a ∉ s) (x : Π i in cons a s has, f i) :
 f a × Π i in s, f i
参数：f : α -> Type*；has : a ∉ s；x : Π i in cons a s has, f i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb

--- 原说明 ---
Split the added element of cons off a Pi type.
-/
def consPiProd (f : α → Type*) (has : a ∉ s) (x : Π i ∈ cons a s has, f i) : f a × Π i ∈ s, f i :=
  (x a (mem_cons_self a s), fun i hi => x i (mem_cons_of_mem hi))

/-- Combine a product with a pi type to pi of cons. -/
/-
**Finset.prodPiCons** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：prodPiCons [DecidableEq α] (f : α -> Type*) {a : α} (has : a ∉ s) (x : f a
 × Π i in s, f i) : (Π i in cons a s has, f i)
参数：f : α -> Type*；has : a ∉ s；x : f a × Π i in s, f i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_mem_cons_of_ne`：mem_of_mem_cons_of_ne {s : Finset α} {a : 
α} {has} {i : α} (hi : i in cons a s has) (hia : i != a) : i in s

--- 原说明 ---
Combine a product with a pi type to pi of cons.
-/
def prodPiCons [DecidableEq α] (f : α → Type*) {a : α} (has : a ∉ s) (x : f a × Π i ∈ s, f i) :
    (Π i ∈ cons a s has, f i) :=
  fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_cons_of_ne hi h)

/-- The equivalence between pi types on cons and the product. -/
/-
**Finset.consPiProdEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：consPiProdEquiv [DecidableEq α] {s : Finset α} (f : α -> Type*) {a : α} (h
as : a ∉ s) : (Π i in cons a s has, f i) ≃ f a × Π i in s, f i where toFun
参数：f : α -> Type*；has : a ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between pi types on cons and the product.
-/
def consPiProdEquiv [DecidableEq α] {s : Finset α} (f : α → Type*) {a : α} (has : a ∉ s) :
    (Π i ∈ cons a s has, f i) ≃ f a × Π i ∈ s, f i where
  toFun := consPiProd f has
  invFun := prodPiCons f has
  left_inv _ := by grind [prodPiCons, consPiProd]
  right_inv _ := by
    -- I'm surprised `grind` needs this `ext` step: it is just `Prod.ext` and `funext`.
    ext _ hi <;> grind [prodPiCons, consPiProd]

end Cons

/-! ### insert -/

section Insert

variable [DecidableEq α] {s t : Finset α} {a b : α} {f : α → β}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`.
-/
instance : Insert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩
/-
**Finset.insert_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl

@[simp]
/-
**Finset.insert_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl
/-
**Finset.insert_val'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1)
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.dedup_cons`：dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ 
s) = ndinsert a (dedup s)
· 使用定理 `Finset.dedup_eq_self`：dedup_eq_self [DecidableEq α] (s : Finset α) : ded
up s.1 = s.1
-/
theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons, dedup_eq_self]; rfl
/-
**Finset.insert_val_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_val_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 =
 a ::ₘ s.1
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_val`：insert_val (a : α) (s : Finset α) : (insert a s).1 = 
ndinsert a s.1
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
-/
theorem insert_val_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_notMem h]

@[simp, grind =]
/-
**Finset.mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_insert : a in insert b s ↔ a = b ∨ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_ndinsert`：mem_ndinsert {a b : α} {s : Multiset α} : a in nd
insert b s ↔ a = b ∨ a in s
-/
theorem mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert
/-
**Finset.mem_insert_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_insert_self (a : α) (s : Finset α) : a in insert a s
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_ndinsert_self`：mem_ndinsert_self (a : α) (s : Multiset α) :
 a in ndinsert a s
-/
theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1
/-
**Finset.mem_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_insert_of_mem (h : a in s) : a in insert b s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_ndinsert_of_mem`：mem_ndinsert_of_mem {a b : α} {s : Multise
t α} (h : a in s) : a in ndinsert b s
-/
theorem mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s :=
  mem_ndinsert_of_mem h
/-
**Finset.mem_of_mem_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_mem_insert_of_ne (h : b in insert a s) : b != a -> b in s
参数：h : b in insert a s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
-/
theorem mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  (mem_insert.1 h).resolve_left
/-
**Finset.eq_of_mem_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_insert_of_notMem (ha : b in insert a s) (hb : b ∉ s) : b = a
参数：ha : b in insert a s；hb : b ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
-/
theorem eq_of_mem_insert_of_notMem (ha : b ∈ insert a s) (hb : b ∉ s) : b = a :=
  (mem_insert.1 ha).resolve_right hb

/-- A version of `LawfulSingleton.insert_empty_eq` that works with `dsimp`. -/
/-
**Finset.insert_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {a : α}, insert a ∅ = {a}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LawfulSingleton.insert_empty_eq` that works with `dsimp`.
-/
@[simp] lemma insert_empty : insert a (∅ : Finset α) = {a} := rfl

@[simp, grind =]
/-
**Finset.cons_eq_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_eq_insert (a s h) : @cons α a s h = insert a s
参数：a s h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A version of `LawfulSingleton.insert_empty_eq` that works with `dsimp`.
-/
theorem cons_eq_insert (a s h) : @cons α a s h = insert a s :=
  ext fun a => by simp

@[simp, norm_cast]
/-
**Finset.coe_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α)
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) := by grind
/-
**Finset.mem_insert_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_insert_coe {s : Finset α} {x y : α} : x in insert y s ↔ x in insert y 
(s : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) := by
  simp
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulSingleton α (Finset α) :=
  ⟨fun a => by simp⟩

@[simp, grind =]
/-
**Finset.insert_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_eq_of_mem (h : a in s) : insert a s = s
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.ndinsert_of_mem`：ndinsert_of_mem {a : α} {s : Multiset α} : a i
n s -> ndinsert a s = s
-/
theorem insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
  eq_of_veq <| ndinsert_of_mem h

@[simp]
/-
**Finset.insert_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_eq_self : insert a s = s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq_self : insert a s = s ↔ a ∈ s := by grind
/-
**Finset.insert_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_ne_self : insert a s != s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.insert_eq_self`：insert_eq_self : insert a s = s ↔ a in s
-/
theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.not
/-
**Finset.pair_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem <| mem_singleton_self _
/-
**Finset.insert_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (i
nsert a s)
参数：a b : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) := by
  grind

@[norm_cast]
/-
**Finset.coe_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b} := by grind

@[simp, norm_cast]
/-
**Finset.coe_eq_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_pair`：coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a
, b}
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b} := by
  rw [← coe_pair, coe_inj]
/-
**Finset.pair_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pair_comm (a b : α) : ({a, b} : Finset α) = {b, a}
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.insert_comm`：insert_comm (a b : α) (s : Finset α) : insert a (ins
ert b s) = insert b (insert a s)
-/
theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  insert_comm a b ∅
/-
**Finset.insert_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s := by grind

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.insert_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩

@[simp]
/-
**Finset.insert_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_ne_empty (a : α) (s : Finset α) : insert a s != ∅
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
-/
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s ≠ ∅ :=
  (insert_nonempty a s).ne_empty
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : α) (s : Finset α) : Nonempty ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype
/-
**Finset.ne_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ne_insert_of_notMem (s t : Finset α) {a : α} (h : a ∉ s) : s != insert a t
参数：s t : Finset α；h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem ne_insert_of_notMem (s t : Finset α) {a : α} (h : a ∉ s) : s ≠ insert a t := by
  contrapose h
  simp [h]
/-
**Finset.insert_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_subset_iff : insert a s subseteq t ↔ a in t ∧ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by grind
/-
**Finset.insert_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_subset (ha : a in t) (hs : s subseteq t) : insert a s subseteq t
参数：ha : a in t；hs : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a 
in t ∧ s subseteq t
-/
theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha,hs⟩
/-
**Finset.subset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s : Finset α), s ⊆ insert
 a s
参数：a : α；s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
@[simp] theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s := fun _b => mem_insert_of_mem

@[gcongr, simp]
/-
**Finset.insert_subset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_subset_insert (a : α) {s t : Finset α} (h : s subseteq t) : insert 
a s subseteq insert a t
参数：a : α；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t := by
  grind
/-
**Finset.insert_subset_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} {a : α}, a ∉ s → 
(insert a s ⊆ insert a t ↔ s ⊆ t)
参数：insert a s ⊆ insert a t ↔ s ⊆ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  simp_rw [← coe_subset]; simp [ha]
/-
**Finset.insert_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_mem_insert_of_notMem`：eq_of_mem_insert_of_notMem (ha : b in
 insert a s) (hb : b ∉ s) : b = a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert_self _ _) ha, congr_arg (insert · s)⟩
/-
**Finset.insert_inj_on** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) sᶜ
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.insert_inj`：insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a
 = b
-/
theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) sᶜ := fun _ h _ _ =>
  (insert_inj h).1
/-
**Finset.ssubset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_iff : s ⊂ t ↔ exists a ∉ s, insert a s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ssubset_iff_insert`：ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ exist
s a ∉ s, insert a s subseteq t
-/
theorem ssubset_iff : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := mod_cast @Set.ssubset_iff_insert α s t
/-
**Finset.ssubset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_insert (h : a ∉ s) : s ⊂ insert a s
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.ssubset_iff`：ssubset_iff : s ⊂ t ↔ exists a ∉ s, insert a s subse
teq t
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩

@[elab_as_elim]
/-
**Finset.cons_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_3} {motive : Finset α → Prop},   motive ∅ → (∀ (a : α) (s : 
Finset α) (h : a ∉ s), motive s → motive (Finset.cons a s h)) → ∀ (s : Finset α)
, motive s
参数：∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a s h)；s
 : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mk_cons`：mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) : (⟨a ::ₘ
 s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1
-/
theorem cons_induction {α : Type*} {motive : Finset α → Prop} (empty : motive ∅)
    (cons : ∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (cons a s h)) : ∀ s, motive s
  | ⟨s, nd⟩ => by
    induction s using Multiset.induction with
    | empty => exact empty
    | cons a s IH =>
      rw [mk_cons nd]
      exact cons a _ _ (IH _)

@[elab_as_elim]
/-
**Finset.cons_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：cons_induction_on {α : Type*} {motive : Finset α -> Prop} (s : Finset α) (
empty : motive ∅) (cons : forall (a : α) (s : Finset α) (h : a ∉ s), motive s ->
 motive (cons a s h)) : motive s
参数：s : Finset α；empty : motive ∅；cons : forall (a : α) (s : Finset α) (h : a ∉ s
), motive s -> motive (cons a s h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
-/
theorem cons_induction_on {α : Type*} {motive : Finset α → Prop} (s : Finset α) (empty : motive ∅)
    (cons : ∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (cons a s h)) : motive s :=
  cons_induction empty cons s

@[elab_as_elim]
/-
**Finset.induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : DecidableEq α],   moti
ve ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)) → ∀ (s
 : Finset α), motive s
参数：∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)；s : Finset α
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
-/
protected theorem induction {α : Type*} {motive : Finset α → Prop} [DecidableEq α]
    (empty : motive ∅)
    (insert : ∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)) : ∀ s, motive s :=
  cons_induction empty fun a s ha => (s.cons_eq_insert a ha).symm ▸ insert a s ha

/-- To prove a proposition about an arbitrary `Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α`,
then it holds for the `Finset` obtained by inserting a new element.
-/
@[elab_as_elim]
/-
**Finset.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : DecidableEq α] (s : Fi
nset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (inse
rt a s)) → motive s
参数：s : Finset α；∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…

--- 原说明 ---
To prove a proposition about an arbitrary `Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α`,
then it holds for the `Finset` obtained by inserting a new element.
-/
protected theorem induction_on {α : Type*} {motive : Finset α → Prop} [DecidableEq α] (s : Finset α)
    (empty : motive ∅)
    (insert : ∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)) : motive s :=
  Finset.induction empty insert s

/-- To prove a proposition about `S : Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α ⊆ S`,
then it holds for the `Finset` obtained by inserting a new element of `S`.
-/
@[elab_as_elim]
/-
**Finset.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on' {α : Type*} {motive : Finset α -> Prop} [DecidableEq α] (S :
 Finset α) (empty : motive ∅) (insert : forall (a s), a in S -> s subseteq S -> 
a ∉ s -> motive s -> motive (insert a s)) : motive S
参数：S : Finset α；empty : motive ∅；insert : forall (a s), a in S -> s subseteq S -
> a ∉ s -> motive s -> motive (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a 
in t ∧ s subseteq t
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s

--- 原说明 ---
To prove a proposition about `S : Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α ⊆ S`,
then it holds for the `Finset` obtained by inserting a new element of `S`.
-/
theorem induction_on' {α : Type*} {motive : Finset α → Prop} [DecidableEq α] (S : Finset α)
    (empty : motive ∅)
    (insert : ∀ (a s), a ∈ S → s ⊆ S → a ∉ s → motive s → motive (insert a s)) : motive S :=
  @Finset.induction_on α (fun T => T ⊆ S → motive T) _ S (fun _ => empty)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset_iff.1 hs
      insert a s hS sS has (hqs sS))
    (Finset.Subset.refl S)

/-- To prove a proposition about a nonempty `s : Finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : Finset α`, then it also holds for the `Finset`
obtained by inserting an element in `t`. -/
@[elab_as_elim]
/-
**Finset.Nonempty.cons_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_3} {motive : (s : Finset α) → s.Nonempty → Prop},   (∀ (a : 
α), motive {a} ⋯) →     (∀ (a : α) (s : Finset α) (h : a ∉ s) (hs : s.Nonempty),
 motive s hs → motive (Finset.cons a s h) ⋯) →       ∀ {s : Finset α} (hs : s.No
nempty), motive s hs
参数：s : Finset α；∀ (a : α), motive {a} ⋯；∀ (a : α) (s : Finset α) (h : a ∉ s) (hs
 : s.Nonempty), motive s hs → motive (Finset.cons a s h) ⋯；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `Finset.not_nonempty_empty`：not_nonempty_empty : ¬(∅ : Finset α).Nonempty
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
To prove a proposition about a nonempty `s : Finset α`, it suffices to show it h
olds for all
singletons and that if it holds for nonempty `t : Finset α`, then it also holds 
for the `Finset`
obtained by inserting an element in `t`.
-/
theorem Nonempty.cons_induction {α : Type*} {motive : ∀ s : Finset α, s.Nonempty → Prop}
    (singleton : ∀ a, motive {a} (singleton_nonempty _))
    (cons : ∀ a s (h : a ∉ s) (hs), motive s hs → motive (Finset.cons a s h) (cons_nonempty h))
    {s : Finset α} (hs : s.Nonempty) : motive s hs := by
  induction s using Finset.cons_induction with
  | empty => exact (not_nonempty_empty hs).elim
  | cons a t ha h =>
    obtain rfl | ht := t.eq_empty_or_nonempty
    · exact singleton a
    · exact cons a t ha ht (h ht)

-- We use a fresh `α` here to exclude the unneeded `DecidableEq α` instance from the section.
/-
**Finset.Nonempty.exists_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_3} {s : Finset α}, s.Nonempty → ∃ t a, ∃ (ha : a ∉ t), Finse
t.cons a t ha = s
参数：ha : a ∉ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Finset.cons_empty`：cons_empty (a : α) : cons a ∅ (notMem_empty _) = {a}
-/
lemma Nonempty.exists_cons_eq {α} {s : Finset α} (hs : s.Nonempty) : ∃ t a ha, cons a t ha = s :=
  hs.cons_induction (fun a ↦ ⟨∅, a, _, cons_empty _⟩) fun _ _ _ _ _ ↦ ⟨_, _, _, rfl⟩

/-- Inserting an element to a finite set is equivalent to the option type. -/
/-
**Finset.subtypeInsertEquivOption** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) : { i // i in 
insert x t } ≃ Option { i // i in t } where toFun y
参数：h : x ∉ t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s

--- 原说明 ---
Inserting an element to a finite set is equivalent to the option type.
-/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
  toFun y := if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
  invFun y := (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

/-- Split the added element of insert off a Pi type. -/
@[simps!]
/-
**Finset.insertPiProd** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：insertPiProd (f : α -> Type*) (x : Π i in insert a s, f i) : f a × Π i in 
s, f i
参数：f : α -> Type*；x : Π i in insert a s, f i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
Split the added element of insert off a Pi type.
-/
def insertPiProd (f : α → Type*) (x : Π i ∈ insert a s, f i) : f a × Π i ∈ s, f i :=
  (x a (mem_insert_self a s), fun i hi => x i (mem_insert_of_mem hi))

/-- Combine a product with a pi type to pi of insert. -/
/-
**Finset.prodPiInsert** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：prodPiInsert (f : α -> Type*) {a : α} (x : f a × Π i in s, f i) : (Π i in 
insert a s, f i)
参数：f : α -> Type*；x : f a × Π i in s, f i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_mem_insert_of_ne`：mem_of_mem_insert_of_ne (h : b in insert
 a s) : b != a -> b in s

--- 原说明 ---
Combine a product with a pi type to pi of insert.
-/
def prodPiInsert (f : α → Type*) {a : α} (x : f a × Π i ∈ s, f i) : (Π i ∈ insert a s, f i) :=
  fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_insert_of_ne hi h)

/-- The equivalence between pi types on insert and the product. -/
/-
**Finset.insertPiProdEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：insertPiProdEquiv {s : Finset α} (f : α -> Type*) {a : α} (has : a ∉ s) : 
(Π i in insert a s, f i) ≃ f a × Π i in s, f i where toFun
参数：f : α -> Type*；has : a ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between pi types on insert and the product.
-/
def insertPiProdEquiv {s : Finset α} (f : α → Type*) {a : α} (has : a ∉ s) :
    (Π i ∈ insert a s, f i) ≃ f a × Π i ∈ s, f i where
  toFun := insertPiProd f
  invFun := prodPiInsert f
  left_inv _ := by grind [prodPiInsert, insertPiProd]
  right_inv _ := by ext _ hi <;> grind [prodPiInsert, insertPiProd]

-- useful rules for calculations with quantifiers
/-
**Finset.exists_mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_mem_insert (a : α) (s : Finset α) (p : α -> Prop) : (exists x, x in
 insert a s ∧ p x) ↔ p a ∨ exists x, x in s ∧ p x
参数：a : α；s : Finset α；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_mem_insert (a : α) (s : Finset α) (p : α → Prop) :
    (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x := by grind
/-
**Finset.forall_mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_mem_insert (a : α) (s : Finset α) (p : α -> Prop) : (forall x, x in
 insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
参数：a : α；s : Finset α；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_mem_insert (a : α) (s : Finset α) (p : α → Prop) :
    (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by grind

/-- Useful in proofs by induction. -/
/-
**Finset.forall_of_forall_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_of_forall_insert {p : α -> Prop} {a : α} {s : Finset α} (H : forall
 x, x in insert a s -> p x) (x) (h : x in s) : p x
参数：H : forall x, x in insert a s -> p x；x；h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
Useful in proofs by induction.
-/
theorem forall_of_forall_insert {p : α → Prop} {a : α} {s : Finset α}
    (H : ∀ x, x ∈ insert a s → p x) (x) (h : x ∈ s) : p x :=
  H _ <| mem_insert_of_mem h

end Insert

end Finset

namespace Multiset

variable [DecidableEq α]

@[simp]
/-
**Multiset.toFinset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_zero : toFinset (0 : Multiset α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_zero : toFinset (0 : Multiset α) = ∅ :=
  rfl

@[simp]
/-
**Multiset.toFinset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (to
Finset s)
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.dedup_cons`：dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ 
s) = ndinsert a (dedup s)
-/
theorem toFinset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (toFinset s) :=
  Finset.eq_of_veq dedup_cons

@[simp]
/-
**Multiset.toFinset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_singleton (a : α) : toFinset ({a} : Multiset α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_zero`：cons_zero (a : α) : a ::ₘ 0 = {a}
· 使用定理 `Multiset.toFinset_cons`：toFinset_cons (a : α) (s : Multiset α) : toFinse
t (a ::ₘ s) = insert a (toFinset s)
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
-/
theorem toFinset_singleton (a : α) : toFinset ({a} : Multiset α) = {a} := by
  rw [← cons_zero, toFinset_cons, toFinset_zero, LawfulSingleton.insert_empty_eq]

end Multiset

namespace List

variable [DecidableEq α] {l : List α} {a : α}

@[simp]
/-
**List.toFinset_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_nil : toFinset (@nil α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_nil : toFinset (@nil α) = ∅ :=
  rfl

@[simp]
/-
**List.toFinset_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_cons : toFinset (a :: l) = insert a (toFinset l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
-/
theorem toFinset_cons : toFinset (a :: l) = insert a (toFinset l) :=
  Finset.eq_of_veq <| by by_cases h : a ∈ l <;> simp [h]
/-
**List.toFinset_replicate_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_replicate_of_ne_zero {n : Nat} (hn : n != 0) : (List.replicate n 
a).toFinset = {a}
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_replicate_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (List.replicate n a).toFinset = {a} := by
  ext x
  simp [hn, List.mem_replicate]

@[simp]
/-
**List.toFinset_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil
参数：l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by
  cases l <;> simp

@[simp]
/-
**List.toFinset_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_nonempty_iff (l : List α) : l.toFinset.Nonempty ↔ l != []
参数：l : List α。
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
theorem toFinset_nonempty_iff (l : List α) : l.toFinset.Nonempty ↔ l ≠ [] := by
  simp [Finset.nonempty_iff_ne_empty]

end List

namespace Finset

section ToList

@[simp]
/-
**Finset.toList_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.toList.eq_1`：∀ {α : Type u_1} (s : Finset α), s.toList = s.val.to
List
· 使用定理 `Multiset.toList_eq_singleton_iff`：toList_eq_singleton_iff {a : α} {m : M
ultiset α} : m.toList = [a] ↔ m = {a}
· 使用定理 `Finset.val_eq_singleton_iff`：val_eq_singleton_iff {a : α} {s : Finset α}
 : s.val = {a} ↔ s = {a}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a} := by
  rw [toList, Multiset.toList_eq_singleton_iff, val_eq_singleton_iff]

@[simp]
/-
**Finset.toList_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_singleton : forall a, ({a} : Finset α).toList = [a]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.toList_singleton`：toList_singleton (a : α) : ({a} : Multiset α)
.toList = [a]
-/
theorem toList_singleton : ∀ a, ({a} : Finset α).toList = [a] :=
  Multiset.toList_singleton

open scoped List in
/-
**Finset.toList_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :
: s.toList
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]

open scoped List in
/-
**Finset.toList_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) : (insert
 a s).toList ~ a :: s.toList
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.toList_cons`：toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (co
ns a s h).toList ~ a :: s.toList
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
-/
theorem toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ toList_cons _

end ToList

section Pairwise

variable {s : Finset α}

/-
**Finset.pairwise_cons'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwise_cons' {a : α} (ha : a ∉ s) (r : β -> β -> Prop) (f : α -> β) : Pa
irwise (r on fun a : s.cons a ha => f a) ↔ Pairwise (r on fun a : s => f a) ∧ fo
rall b in s, r (f a) (f b) ∧ r (f b) (f a)
参数：ha : a ∉ s；r : β -> β -> Prop；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
-/
theorem pairwise_cons' {a : α} (ha : a ∉ s) (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun a : s.cons a ha => f a) ↔
    Pairwise (r on fun a : s => f a) ∧ ∀ b ∈ s, r (f a) (f b) ∧ r (f b) (f a) := by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert]
  grind
/-
**Finset.pairwise_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwise_cons {a : α} (ha : a ∉ s) (r : α -> α -> Prop) : Pairwise (r on f
un a : s.cons a ha => a) ↔ Pairwise (r on fun a : s => a) ∧ forall b in s, r a b
 ∧ r b a
参数：ha : a ∉ s；r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pairwise_cons'`：pairwise_cons' {a : α} (ha : a ∉ s) (r : β -> β -
> Prop) (f : α -> β) : Pairwise (r on fun a : s.cons a ha => f a) ↔ Pairwise (r 
on fun a : …
-/
theorem pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
    Pairwise (r on fun a : s.cons a ha => a) ↔
      Pairwise (r on fun a : s => a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_cons' ha r id

end Pairwise

end Finset

