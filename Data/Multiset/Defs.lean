/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Quot
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Multisets

Multisets are finite sets with duplicates allowed. They are implemented here as the quotient of
lists by permutation. This gives them computational content.

This file contains the definition of `Multiset` and the basic predicates. Most operations
have been split off into their own files. The goal is that we can define `Finset` with only
importing `Multiset.Defs`.

## Main definitions

* `Multiset`: the type of finite sets with duplicates allowed.

* `Coe (List α) (Multiset α)`: turn a list into a multiset by forgetting the order.
* `Multiset.pmap`: map a partial function defined on a superset of the multiset's elements.
* `Multiset.attach`: add a proof of membership to the elements of the multiset.
* `Multiset.card`: number of elements of a multiset (counted with repetition).

* `Membership α (Multiset α)` instance: `x ∈ s` if `x` has multiplicity at least one in `s`.
* `Subset (Multiset α)` instance: `s ⊆ t` if every `x ∈ s` also enjoys `x ∈ t`.
* `PartialOrder (Multiset α)` instance: `s ≤ t` if all `x` have multiplicity in
  `s` less than their multiplicity in `t`.
* `Multiset.Pairwise`: `Pairwise r s` holds iff there exists a list of elements
  of `s` such that `r` holds pairwise.
* `Multiset.Nodup`: `Nodup s` holds if the multiplicity of any element is at most 1.

## Notation (defined later)

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.
* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.
* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

/-- `Multiset α` is the quotient of `List α` by list permutation. The result
  is a type of finite sets with duplicates allowed. -/
/-
**Multiset.** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiset α` is the quotient of `List α` by list permutation. The result
  is a type of finite sets with duplicates allowed.
-/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

/-- The quotient map from `List α` to `Multiset α`. -/
@[coe]
/-
**Multiset.ofList** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：ofList : List α -> Multiset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map from `List α` to `Multiset α`.
-/
def ofList : List α → Multiset α :=
  Quot.mk _
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (List α) (Multiset α) :=
  ⟨ofList⟩

@[simp]
/-
**Multiset.quot_mk_to_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：quot_mk_to_coe (l : List α) : @Eq (Multiset α) ⟦l⟧ l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_to_coe (l : List α) : @Eq (Multiset α) ⟦l⟧ l :=
  rfl

@[simp]
/-
**Multiset.quot_mk_to_coe'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l :=
  rfl

@[simp]
/-
**Multiset.quot_mk_to_coe''** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoid.r l) l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoid.r l) l :=
  rfl

@[simp]
/-
**Multiset.lift_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lift_coe {α β : Type*} (x : List α) (f : List α -> β) (h : forall a b : Li
st α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset α) = f x
参数：x : List α；f : List α -> β；h : forall a b : List α, a ≈ b -> f a = f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.lift_mk`：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : fora
ll a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = 
f x
-/
theorem lift_coe {α β : Type*} (x : List α) (f : List α → β)
    (h : ∀ a b : List α, a ≈ b → f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk _ _ _

@[simp]
/-
**Multiset.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂ :=
  Quotient.eq

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: move to better place
-- (upstream to Batteries?)
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ ≈ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (isSetoid α l₁ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))
/-
**Multiset.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → DecidableEq (Multiset α)
参数：Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEq [DecidableEq α] : DecidableEq (Multiset α)
  | s₁, s₂ => Quotient.recOnSubsingleton₂ s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq_iff_equiv

section Mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
/-
**Multiset.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Mem (s : Multiset α) (a : α) : Prop
参数：s : Multiset α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a ∈ s` means that `a` has nonzero multiplicity in `s`.
-/
def Mem (s : Multiset α) (a : α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ (e : l₁ ~ l₂) => propext <| e.mem_iff
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Multiset α) :=
  ⟨Mem⟩

@[simp]
/-
**Multiset.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔ a in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {a : α} {l : List α} : a ∈ (l : Multiset α) ↔ a ∈ l :=
  Iff.rfl
/-
**Multiset.decidableMem** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a in s)
参数：a : α；s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) :=
  Quot.recOnSubsingleton s fun l ↦ inferInstanceAs (Decidable (a ∈ l))

end Mem

/-! ### `Multiset.Subset` -/


section Subset
variable {s : Multiset α} {a : α}

/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
/-
**Multiset.Subset** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → Multiset α → Multiset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal tha
n in `t`;
  see `s ≤ t` for this relation.
-/
protected def Subset (s t : Multiset α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → a ∈ t
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSubset (Multiset α) :=
  ⟨Multiset.Subset⟩
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSSubset (Multiset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩
/-
**Multiset.instIsNonstrictStrictOrder** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instIsNonstrictStrictOrder : IsNonstrictStrictOrder (Multiset α) (· subset
eq ·) (· ⊂ ·) where right_iff_left_not_left _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance instIsNonstrictStrictOrder : IsNonstrictStrictOrder (Multiset α) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := Iff.rfl

@[simp]
/-
**Multiset.coe_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_subset {l₁ l₂ : List α} : (l₁ : Multiset α) subseteq l₂ ↔ l₁ subseteq 
l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_subset {l₁ l₂ : List α} : (l₁ : Multiset α) ⊆ l₂ ↔ l₁ ⊆ l₂ :=
  Iff.rfl

@[simp]
/-
**Multiset.Subset.refl** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Subset`。
形式化陈述：∀ {α : Type u_1} (s : Multiset α), s ⊆ s
参数：s : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subset.refl (s : Multiset α) : s ⊆ s := fun _ h => h
/-
**Multiset.Subset.trans** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Subset`。
形式化陈述：∀ {α : Type u_1} {s t u : Multiset α}, s ⊆ t → t ⊆ u → s ⊆ u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subset.trans {s t u : Multiset α} : s ⊆ t → t ⊆ u → s ⊆ u := fun h₁ h₂ _ m => h₂ (h₁ m)
/-
**Multiset.subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_iff {s t : Multiset α} : s subseteq t ↔ forall ⦃x⦄, x in s -> x in 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_iff {s t : Multiset α} : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t :=
  Iff.rfl

@[gcongr]
/-
**Multiset.mem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_of_subset {s t : Multiset α} {a : α} (h : s subseteq t) : a in s -> a 
in t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_subset {s t : Multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t :=
  @h _

end Subset

/-! ### Partial order on `Multiset`s -/


/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
/-
**Multiset.Le** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → Multiset α → Multiset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`.
-/
protected def Le (s t : Multiset α) : Prop :=
  (Quotient.liftOn₂ s t (· <+~ ·)) fun _ _ _ _ p₁ p₂ =>
    propext (p₂.subperm_left.trans p₁.subperm_right)
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Multiset α) where
  le := Multiset.Le
  le_refl := by rintro ⟨l⟩; exact Subperm.refl _
  le_trans := by rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @Subperm.trans _ _ _ _
  le_antisymm := by rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact Quot.sound (Subperm.antisymm h₁ h₂)
/-
**Multiset.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：decidableLE [DecidableEq α] : DecidableLE (Multiset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
instance decidableLE [DecidableEq α] : DecidableLE (Multiset α) :=
  fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm

section

variable {s t : Multiset α} {a : α}

/-
**Multiset.subset_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_of_le : s <= t -> s subseteq t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.Subperm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Subperm l₂ → 
l₁ ⊆ l₂
-/
theorem subset_of_le : s ≤ t → s ⊆ t :=
  Quotient.inductionOn₂ s t fun _ _ => Subperm.subset

alias Le.subset := subset_of_le
/-
**Multiset.mem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_of_le (h : s <= t) : a in s -> a in t
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_subset`：mem_of_subset {s t : Multiset α} {a : α} (h : s 
subseteq t) : a in s -> a in t
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
-/
theorem mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t :=
  mem_of_subset (subset_of_le h)
/-
**Multiset.notMem_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：notMem_mono (h : s subseteq t) : a ∉ t -> a ∉ s
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem notMem_mono (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| @h _

@[simp]
/-
**Multiset.coe_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) <= l₂ ↔ l₁ <+~ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) ≤ l₂ ↔ l₁ <+~ l₂ :=
  Iff.rfl

@[elab_as_elim]
/-
**Multiset.leInductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：leInductionOn {C : Multiset α -> Multiset α -> Prop} {s t : Multiset α} (h
 : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C l₁ l₂) : C s t
参数：h : s <= t；H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C l₁ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
-/
theorem leInductionOn {C : Multiset α → Multiset α → Prop} {s t : Multiset α} (h : s ≤ t)
    (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
  Quotient.inductionOn₂ s t (fun l₁ _ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

end

/-! ### Cardinality -/


/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
/-
**Multiset.card** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：card : Multiset α -> Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length

--- 原说明 ---
The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list.
-/
def card : Multiset α → ℕ := Quot.lift length fun _l₁ _l₂ => Perm.length_eq

@[simp]
/-
**Multiset.coe_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_card (l : List α) : card (l : Multiset α) = length l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_card (l : List α) : card (l : Multiset α) = length l :=
  rfl
/-
**Multiset.card_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_le_card {s t : Multiset α} (h : s <= t) : card s <= card t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂
 → l₁.length ≤ l₂.length
-/
theorem card_le_card {s t : Multiset α} (h : s ≤ t) : card s ≤ card t :=
  leInductionOn h Sublist.length_le
/-
**Multiset.eq_of_le_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_of_le_of_card_le {s t : Multiset α} (h : s <= t) : card t <= card s -> 
s = t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Sublist.eq_of_length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Subl
ist l₂ → l₂.length ≤ l₁.length → l₁ = l₂
-/
theorem eq_of_le_of_card_le {s t : Multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
  leInductionOn h fun s h₂ => congr_arg _ <| s.eq_of_length_le h₂
/-
**Multiset.card_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_lt_card {s t : Multiset α} (h : s < t) : card s < card t
参数：h : s < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem card_lt_card {s t : Multiset α} (h : s < t) : card s < card t :=
  lt_of_not_ge fun h₂ => _root_.ne_of_lt h <| eq_of_le_of_card_le (le_of_lt h) h₂

@[gcongr, mono]
/-
**Multiset.card_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_mono : Monotone (@card α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
-/
theorem card_mono : Monotone (@card α) := fun _a _b => card_le_card

@[gcongr]
/-
**Multiset.card_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：card_strictMono : StrictMono (@card α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_lt_card`：card_lt_card {s t : Multiset α} (h : s < t) : car
d s < card t
-/
lemma card_strictMono : StrictMono (@card α) := fun _ _ ↦ card_lt_card

/-- Another way of expressing `strongInductionOn`: the `(<)` relation is well-founded. -/
/-
**Multiset.instWellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instWellFoundedLT : WellFoundedLT (Multiset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Multiset.card_lt_card`：card_lt_card {s t : Multiset α} (h : s < t) : car
d s < card t
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel

--- 原说明 ---
Another way of expressing `strongInductionOn`: the `(<)` relation is well-founde
d.
-/
instance instWellFoundedLT : WellFoundedLT (Multiset α) :=
  ⟨Subrelation.wf Multiset.card_lt_card (measure Multiset.card).2⟩

@[simp]
/-
**Multiset.coe_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_reverse (l : List α) : (reverse l : Multiset α) = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
-/
theorem coe_reverse (l : List α) : (reverse l : Multiset α) = l :=
  Quot.sound <| reverse_perm _

/-! ### Map for partial functions -/

/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
nonrec def pmap {p : α → Prop} (f : ∀ a, p a → β) (s : Multiset α) : (∀ a ∈ s, p a) → Multiset β :=
  Quot.recOn s (fun l H => ↑(pmap f l H)) fun l₁ l₂ (pp : l₁ ~ l₂) =>
    funext fun H₂ : ∀ a ∈ l₂, p a =>
      have H₁ : ∀ a ∈ l₁, p a := fun a h => H₂ a (pp.subset h)
      have : ∀ {s₂ e H}, @Eq.ndrec (Multiset α) l₁ (fun s => (∀ a ∈ s, p a) → Multiset β)
          (fun _ => ↑(pmap f l₁ H₁)) s₂ e H = ↑(pmap f l₁ H₁) := by
        intro s₂ e _; subst e; rfl
      this.trans <| Quot.sound <| pp.pmap f

@[simp]
/-
**Multiset.coe_pmap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_pmap {p : α -> Prop} (f : forall a, p a -> β) (l : List α) (H : forall
 a in l, p a) : pmap f l H = l.pmap f H
参数：f : forall a, p a -> β；l : List α；H : forall a in l, p a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pmap {p : α → Prop} (f : ∀ a, p a → β) (l : List α) (H : ∀ a ∈ l, p a) :
    pmap f l H = l.pmap f H :=
  rfl
/-
**Multiset.pmap_congr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pmap_congr {p q : α -> Prop} {f : forall a, p a -> β} {g : forall a, q a -
> β} (s : Multiset α) : forall {H₁ H₂}, (forall a in s, forall (h₁ h₂), f a h₁ =
 g a h₂) -> pmap f s H₁ = pmap g s H₂
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.pmap_congr_left`：∀ {α : Type u_1} {β : Type u_2} {p q : α → Prop} {
f : (a : α) → p a → β} {g : (a : α) → q a → β} (l : List α)   {H₁ : ∀ a ∈ l, p a
} {H₂ : ∀ …
-/
theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (s : Multiset α) :
    ∀ {H₁ H₂}, (∀ a ∈ s, ∀ (h₁ h₂), f a h₁ = g a h₂) → pmap f s H₁ = pmap g s H₂ :=
  @(Quot.inductionOn s (fun l _H₁ _H₂ h => congr_arg _ <| List.pmap_congr_left l h))

@[simp]
/-
**Multiset.mem_pmap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_pmap {p : α -> Prop} {f : forall a, p a -> β} {s H b} : b in pmap f s 
H ↔ exists (a : _) (h : a in s), f a (H a h) = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : 
α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a} {b : β},   b ∈ List.pmap f l H ↔ ∃
 a,…
-/
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {s H b} :
    b ∈ pmap f s H ↔ ∃ (a : _) (h : a ∈ s), f a (H a h) = b :=
  Quot.inductionOn s (fun _l _H => List.mem_pmap) H

@[simp]
/-
**Multiset.card_pmap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_pmap {p : α -> Prop} (f : forall a, p a -> β) (s H) : card (pmap f s 
H) = card s
参数：f : forall a, p a -> β；s H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a
 : α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (List.pmap f l H).length = l
.lengt…
-/
theorem card_pmap {p : α → Prop} (f : ∀ a, p a → β) (s H) : card (pmap f s H) = card s :=
  Quot.inductionOn s (fun _l _H => length_pmap) H

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
/-
**Multiset.attach** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：attach (s : Multiset α) : Multiset { x // x in s }
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`.
-/
def attach (s : Multiset α) : Multiset { x // x ∈ s } :=
  pmap Subtype.mk s fun _a => id

@[simp]
/-
**Multiset.coe_attach** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_attach (l : List α) : @Eq (Multiset { x // x in l }) (@attach α l) l.a
ttach
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_attach (l : List α) : @Eq (Multiset { x // x ∈ l }) (@attach α l) l.attach :=
  rfl

@[simp]
/-
**Multiset.mem_attach** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_attach (s : Multiset α) : forall x, x in s.attach
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_attach`：∀ {α : Type u_1} (l : List α) (x : { x // x ∈ l }), x ∈
 l.attach
-/
theorem mem_attach (s : Multiset α) : ∀ x, x ∈ s.attach :=
  Quot.inductionOn s fun _l => List.mem_attach _

@[simp]
/-
**Multiset.card_attach** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_attach {m : Multiset α} : card (attach m) = card m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_pmap`：card_pmap {p : α -> Prop} (f : forall a, p a -> β) (
s H) : card (pmap f s H) = card s
-/
theorem card_attach {m : Multiset α} : card (attach m) = card m :=
  card_pmap _ _ _

section Decidable

variable {m : Multiset α}

/-- If `p` is a decidable predicate,
so is the predicate that all elements of a multiset satisfy `p`. -/
/-
**Multiset.decidableForallMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → {m : Multiset α} → {p : α → Prop} → [(a : α) → Decidable 
(p a)] → Decidable (∀ a ∈ m, p a)
参数：a : α；p a；∀ a ∈ m, p a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` is a decidable predicate,
so is the predicate that all elements of a multiset satisfy `p`.
-/
protected def decidableForallMultiset {p : α → Prop} [∀ a, Decidable (p a)] :
    Decidable (∀ a ∈ m, p a) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∀ a ∈ l, p a) <| by simp
/-
**Multiset.decidableDforallMultiset** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：decidableDforallMultiset {p : forall a in m, Prop} [_hp : forall (a) (h : 
a in m), Decidable (p a h)] : Decidable (forall (a) (h : a in m), p a h)
参数：a；h : a in m；p a h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableDforallMultiset {p : ∀ a ∈ m, Prop} [_hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ m), p a h) :=
  @decidable_of_iff _ _
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨_a, _ha⟩ _ => h _ _)
    (@Multiset.decidableForallMultiset _ m.attach (fun a => p a.1 a.2) _)

/-- decidable equality for functions whose domain is bounded by multisets -/
/-
**Multiset.decidableEqPiMultiset** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：decidableEqPiMultiset {β : α -> Type*} [forall a, DecidableEq (β a)] : Dec
idableEq (forall a in m, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
decidable equality for functions whose domain is bounded by multisets
-/
instance decidableEqPiMultiset {β : α → Type*} [∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ m, β a) := fun f g =>
  decidable_of_iff (∀ (a) (h : a ∈ m), f a h = g a h) (by simp [funext_iff])

/-- If `p` is a decidable predicate,
so is the existence of an element in a multiset satisfying `p`. -/
/-
**Multiset.decidableExistsMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → {m : Multiset α} → {p : α → Prop} → [DecidablePred p] → D
ecidable (∃ x ∈ m, p x)
参数：∃ x ∈ m, p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` is a decidable predicate,
so is the existence of an element in a multiset satisfying `p`.
-/
protected def decidableExistsMultiset {p : α → Prop} [DecidablePred p] : Decidable (∃ x ∈ m, p x) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∃ a ∈ l, p a) <| by simp
/-
**Multiset.decidableDexistsMultiset** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：decidableDexistsMultiset {p : forall a in m, Prop} [_hp : forall (a) (h : 
a in m), Decidable (p a h)] : Decidable (exists (a : _) (h : a in m), p a h)
参数：a；h : a in m；p a h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableDexistsMultiset {p : ∀ a ∈ m, Prop} [_hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∃ (a : _) (h : a ∈ m), p a h) :=
  @decidable_of_iff _ _
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ =>
      ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)
    (@Multiset.decidableExistsMultiset { a // a ∈ m } m.attach (fun a => p a.1 a.2) _)

end Decidable

/-- `Pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
/-
**Multiset.Pairwise** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Pairwise (r : α -> α -> Prop) (m : Multiset α) : Prop
参数：r : α -> α -> Prop；m : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pairwise r m` states that there exists a list of the elements s.t. `r` holds pa
irwise on this
list.
-/
def Pairwise (r : α → α → Prop) (m : Multiset α) : Prop :=
  ∃ l : List α, m = l ∧ l.Pairwise r
/-
**Multiset.pairwise_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pairwise_coe_iff {r : α -> α -> Prop} {l : List α} : Multiset.Pairwise r l
 ↔ exists l' : List α, l ~ l' ∧ l'.Pairwise r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pairwise_coe_iff {r : α → α → Prop} {l : List α} :
    Multiset.Pairwise r l ↔ ∃ l' : List α, l ~ l' ∧ l'.Pairwise r :=
  exists_congr <| by simp
/-
**Multiset.pairwise_coe_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pairwise_coe_iff_pairwise {r : α -> α -> Prop} [Std.Symm r] {l : List α} :
 Multiset.Pairwise r l ↔ l.Pairwise r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.pairwise_iff`：∀ {α : Type u_1} {R : α → α → Prop},   (∀ {x y :
 α}, R x y → R y x) → ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → (List.Pairwise R l₁ ↔ Lis
t.Pairwise R…
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
theorem pairwise_coe_iff_pairwise {r : α → α → Prop} [Std.Symm r] {l : List α} :
    Multiset.Pairwise r l ↔ l.Pairwise r :=
  ⟨fun ⟨_l', Eq, h⟩ ↦ Quotient.exact Eq |>.pairwise_iff symm |>.mpr h, fun h ↦ ⟨l, rfl, h⟩⟩

section Nodup

/-- `Nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
/-
**Multiset.Nodup** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Nodup (s : Multiset α) : Prop
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1.
-/
def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

@[simp]
/-
**Multiset.coe_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup :=
  Iff.rfl
/-
**Multiset.Nodup.ext** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s t : Multiset α}, s.Nodup → t.Nodup → (s = t ↔ ∀ (a : α
), a ∈ s ↔ a ∈ t)
参数：s = t ↔ ∀ (a : α), a ∈ s ↔ a ∈ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
-/
theorem Nodup.ext {s t : Multiset α} : Nodup s → Nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
  Quotient.inductionOn₂ s t fun _ _ d₁ d₂ => Quotient.eq.trans <| perm_ext_iff_of_nodup d₁ d₂
/-
**Multiset.le_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_iff_subset {s t : Multiset α} : Nodup s -> (s <= t ↔ s subseteq t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `List.Nodup.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l
₂ → l₁.Subperm l₂
-/
theorem le_iff_subset {s t : Multiset α} : Nodup s → (s ≤ t ↔ s ⊆ t) :=
  Quotient.inductionOn₂ s t fun _ _ d => ⟨subset_of_le, d.subperm⟩
/-
**Multiset.nodup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodup t -> Nodup s
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
-/
theorem nodup_of_le {s t : Multiset α} (h : s ≤ t) : Nodup t → Nodup s :=
  Multiset.leInductionOn h fun {_ _} => Nodup.sublist
/-
**Multiset.nodupDecidable** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodup s)
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodup s) :=
  Quotient.recOnSubsingleton s fun l => l.nodupDecidable

end Nodup

section SizeOf

/-- Defines a size for a multiset by referring to the size of the underlying list.

This has to be defined before the definition of `Finset`, otherwise its automatically generated
`SizeOf` instance will be wrong.
-/
protected
/-
**Multiset.sizeOf** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：sizeOf [SizeOf α] (s : Multiset α) : Nat
参数：s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.sizeOf_eq_sizeOf`：∀ {α : Type u_1} [inst : SizeOf α] {l₁ l₂ : 
List α}, l₁.Perm l₂ → sizeOf l₁ = sizeOf l₂
-/
def sizeOf [SizeOf α] (s : Multiset α) : ℕ :=
  (Quot.liftOn s SizeOf.sizeOf) fun _ _ => Perm.sizeOf_eq_sizeOf
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SizeOf α] : SizeOf (Multiset α) :=
  ⟨Multiset.sizeOf⟩

end SizeOf

end Multiset

