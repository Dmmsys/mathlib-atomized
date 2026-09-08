/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Sups
public import Mathlib.Logic.Function.Iterate

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `Finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

* `Finset.shadow`: The shadow of a set family. Everything we can get by removing a new element from
  some set.
* `Finset.upShadow`: The upper shadow of a set family. Everything we can get by adding an element
  to some set.

## Notation

We define notation in scope `FinsetFamily`:
* `∂ 𝒜`: Shadow of `𝒜`.
* `∂⁺ 𝒜`: Upper shadow of `𝒜`.

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : Finset α`
are finsets, and `𝒜, ℬ : Finset (Finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/

@[expose] public section


open Finset Nat

variable {α : Type*}

namespace Finset

section Shadow

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element from any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `𝒜`. -/
/-
**Finset.shadow** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：shadow (𝒜 : Finset (Finset α)) : Finset (Finset α)
参数：𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shadow of a set family `𝒜` is all sets we can get by removing one element fr
om any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get b
y removing `k`
elements from any set in `𝒜`.
-/
def shadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => s.image (erase s)

@[inherit_doc] scoped[FinsetFamily] notation:max "∂" => Finset.shadow

open FinsetFamily

/-- The shadow of the empty set is empty. -/
@[simp]
/-
**Finset.shadow_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：shadow_empty : ∂ (∅ : Finset (Finset α)) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shadow of the empty set is empty.
-/
theorem shadow_empty : ∂ (∅ : Finset (Finset α)) = ∅ :=
  rfl
/-
**Finset.shadow_iterate_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (k : ℕ), Finset.shadow^[k] ∅ = ∅
参数：k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] lemma shadow_iterate_empty (k : ℕ) : ∂^[k] (∅ : Finset (Finset α)) = ∅ := by
  induction k <;> simp [*, shadow_empty]

@[simp]
/-
**Finset.shadow_singleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：shadow_singleton_empty : ∂ ({∅} : Finset (Finset α)) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shadow_singleton_empty : ∂ ({∅} : Finset (Finset α)) = ∅ :=
  rfl

@[simp]
/-
**Finset.shadow_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：shadow_singleton (a : α) : ∂ {{a}} = {∅}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `Finset.erase_singleton`：erase_singleton (a : α) : ({a} : Finset α).erase
 a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem shadow_singleton (a : α) : ∂ {{a}} = {∅} := by
  simp [shadow]

/-- The shadow is monotone. -/
@[gcongr, mono]
/-
**Finset.shadow_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：shadow_monotone : Monotone (shadow : Finset (Finset α) -> Finset (Finset α
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f

--- 原说明 ---
The shadow is monotone.
-/
theorem shadow_monotone : Monotone (shadow : Finset (Finset α) → Finset (Finset α)) := fun _ _ =>
  sup_mono
/-
**Finset.shadow_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 ℬ : Finset (Finset α)}, 𝒜 ⊆ ℬ →
 𝒜.shadow ⊆ ℬ.shadow
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.shadow_monotone`：shadow_monotone : Monotone (shadow : Finset (Fin
set α) -> Finset (Finset α))
-/
@[gcongr] lemma shadow_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) : ∂ 𝒜 ⊆ ∂ ℬ := shadow_monotone h𝒜ℬ

/-- `t` is in the shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one element to
get `t`. -/
/-
**Finset.mem_shadow_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_shadow_iff : t in ∂ 𝒜 ↔ exists s in 𝒜, exists a in s, erase s a = t
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

--- 原说明 ---
`t` is in the shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one 
element to
get `t`.
-/
lemma mem_shadow_iff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∈ s, erase s a = t := by
  simp only [shadow, mem_sup, mem_image]
/-
**Finset.erase_mem_shadow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_mem_shadow (hs : s in 𝒜) (ha : a in s) : erase s a in ∂ 𝒜
参数：hs : s in 𝒜；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_shadow_iff`：mem_shadow_iff : t in ∂ 𝒜 ↔ exists s in 𝒜, exists
 a in s, erase s a = t
-/
theorem erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ ∂ 𝒜 :=
  mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/-- `t ∈ ∂𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add_one`. -/
/-
**Finset.mem_shadow_iff_exists_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_shadow_iff_exists_sdiff : t in ∂ 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s
 \ t) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`t ∈ ∂𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add_one`.
-/
lemma mem_shadow_iff_exists_sdiff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #(s \ t) = 1 := by
  simp_rw [mem_shadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]

/-- `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
/-
**Finset.mem_shadow_iff_insert_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_shadow_iff_insert_mem : t in ∂ 𝒜 ↔ exists a ∉ t, insert a t in 𝒜
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
`t` is in the shadow of `𝒜` iff we can add an element to it so that the resultin
g finset is in
`𝒜`.
-/
lemma mem_shadow_iff_insert_mem : t ∈ ∂ 𝒜 ↔ ∃ a ∉ t, insert a t ∈ 𝒜 := by
  simp_rw [mem_shadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]
  aesop

/-- `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_sdiff`. -/
/-
**Finset.mem_shadow_iff_exists_mem_card_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t`。
形式化陈述：mem_shadow_iff_exists_mem_card_add_one : t in ∂ 𝒜 ↔ exists s in 𝒜, t subse
teq s ∧ #s = #t + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Finset.mem_shadow_iff_exists_sdiff`：mem_shadow_iff_exists_sdiff : t in ∂
 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s \ t) = 1
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_sdiff`.
-/
lemma mem_shadow_iff_exists_mem_card_add_one : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #s = #t + 1 := by
  refine mem_shadow_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst
/-
**Finset.mem_shadow_iterate_iff_exists_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_shadow_iterate_iff_exists_card : t in ∂^[k] 𝒜 ↔ exists u : Finset α, #
u = k ∧ Disjoint t u ∧ t union u in 𝒜
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.union_empty`：union_empty (s : Finset α) : s union ∅ = s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma mem_shadow_iterate_iff_exists_card :
    t ∈ ∂^[k] 𝒜 ↔ ∃ u : Finset α, #u = k ∧ Disjoint t u ∧ t ∪ u ∈ 𝒜 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_shadow_iff_insert_mem, ih, Function.iterate_succ_apply', card_eq_succ]
    aesop

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add`. -/
/-
**Finset.mem_shadow_iterate_iff_exists_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_shadow_iterate_iff_exists_sdiff : t in ∂^[k] 𝒜 ↔ exists s in 𝒜, t subs
eteq s ∧ #(s \ t) = k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mem_shadow_iterate_iff_exists_card`：mem_shadow_iterate_iff_exists
_card : t in ∂^[k] 𝒜 ↔ exists u : Finset α, #u = k ∧ Disjoint t u ∧ t union u in
 𝒜
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.union_sdiff_cancel_left`：union_sdiff_cancel_left (h : Disjoint s 
t) : (s union t) \ s = t
· 使用定理 `Finset.disjoint_sdiff`：disjoint_sdiff : Disjoint s (t \ s)
· 使用定理 `Finset.union_sdiff_self_eq_union`：union_sdiff_self_eq_union : s union t 
\ s = s union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.union_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, s ∪ t = t ↔ s ⊆ t

--- 原说明 ---
`t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add`.
-/
lemma mem_shadow_iterate_iff_exists_sdiff : t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #(s \ t) = k := by
  rw [mem_shadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, htu, hsuA⟩
    exact ⟨_, hsuA, subset_union_left, by rw [union_sdiff_cancel_left htu]⟩
  · rintro ⟨s, hs, hts, rfl⟩
    refine ⟨s \ t, rfl, disjoint_sdiff, ?_⟩
    rwa [union_sdiff_self_eq_union, union_eq_right.2 hts]

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_shadow_iterate_iff_exists_sdiff`. -/
/-
**Finset.mem_shadow_iterate_iff_exists_mem_card_add** 是 Mathlib 中的一个引理，位于命名空间 `F
inset`。
形式化陈述：mem_shadow_iterate_iff_exists_mem_card_add : t in ∂^[k] 𝒜 ↔ exists s in 𝒜,
 t subseteq s ∧ #s = #t + k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Finset.mem_shadow_iterate_iff_exists_sdiff`：mem_shadow_iterate_iff_exist
s_sdiff : t in ∂^[k] 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s \ t) = k
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_shadow_iterate_iff_exists_sdiff`.
-/
lemma mem_shadow_iterate_iff_exists_mem_card_add :
    t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #s = #t + k := by
  refine mem_shadow_iterate_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

/-- The shadow of a family of `r`-sets is a family of `r - 1`-sets. -/
/-
**Finset._root_.Set.Sized.shadow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shadow of a family of `r`-sets is a family of `r - 1`-sets.
-/
protected theorem _root_.Set.Sized.shadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂ 𝒜 : Set (Finset α)).Sized (r - 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi, h𝒜 hA]

/-- The `k`-th shadow of a family of `r`-sets is a family of `r - k`-sets. -/
/-
**Finset._root_.Set.Sized.shadow_iterate** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`-th shadow of a family of `r`-sets is a family of `r - k`-sets.
-/
lemma _root_.Set.Sized.shadow_iterate (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂^[k] 𝒜 : Set (Finset α)).Sized (r - k) := by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff_of_subset hts, ← h𝒜 hs, Nat.sub_sub_self (card_le_card hts)]
/-
**Finset.sized_shadow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sized_shadow_iff (h : ∅ ∉ 𝒜) : (∂ 𝒜 : Set (Finset α)).Sized r ↔ (𝒜 : Set (
Finset α)).Sized (r + 1)
参数：h : ∅ ∉ 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_mem_shadow`：erase_mem_shadow (hs : s in 𝒜) (ha : a in s) : 
erase s a in ∂ 𝒜
· 使用定理 `Finset.card_erase_add_one`：card_erase_add_one : a in s -> #(s.erase a) +
 1 = #s
· 使用定理 `Set.Sized.shadow`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (F
inset α)} {r : ℕ}, Set.Sized r ↑𝒜 → Set.Sized (r - 1) ↑𝒜.shadow
-/
theorem sized_shadow_iff (h : ∅ ∉ 𝒜) :
    (∂ 𝒜 : Set (Finset α)).Sized r ↔ (𝒜 : Set (Finset α)).Sized (r + 1) := by
  refine ⟨fun h𝒜 s hs => ?_, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha), card_erase_add_one ha]

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
/-
**Finset.exists_subset_of_mem_shadow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_subset_of_mem_shadow (hs : t in ∂ 𝒜) : exists s in 𝒜, t subseteq s
参数：hs : t in ∂ 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.mem_shadow_iff_exists_mem_card_add_one`：mem_shadow_iff_exists_mem
_card_add_one : t in ∂ 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #s = #t + 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Being in the shadow of `𝒜` means we have a superset in `𝒜`.
-/
lemma exists_subset_of_mem_shadow (hs : t ∈ ∂ 𝒜) : ∃ s ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩

end Shadow

open FinsetFamily

section UpShadow

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

/-- The upper shadow of a set family `𝒜` is all sets we can get by adding one element to any set in
`𝒜`, and the (`k` times) iterated upper shadow (`upShadow^[k]`) is all sets we can get by adding
`k` elements from any set in `𝒜`. -/
/-
**Finset.upShadow** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：upShadow (𝒜 : Finset (Finset α)) : Finset (Finset α)
参数：𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper shadow of a set family `𝒜` is all sets we can get by adding one elemen
t to any set in
`𝒜`, and the (`k` times) iterated upper shadow (`upShadow^[k]`) is all sets we c
an get by adding
`k` elements from any set in `𝒜`.
-/
def upShadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => sᶜ.image fun a => insert a s

@[inherit_doc] scoped[FinsetFamily] notation:max "∂⁺ " => Finset.upShadow

/-- The upper shadow of the empty set is empty. -/
@[simp]
/-
**Finset.upShadow_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：upShadow_empty : ∂⁺ (∅ : Finset (Finset α)) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper shadow of the empty set is empty.
-/
theorem upShadow_empty : ∂⁺ (∅ : Finset (Finset α)) = ∅ :=
  rfl

/-- The upper shadow is monotone. -/
@[gcongr, mono]
/-
**Finset.upShadow_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：upShadow_monotone : Monotone (upShadow : Finset (Finset α) -> Finset (Fins
et α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f

--- 原说明 ---
The upper shadow is monotone.
-/
theorem upShadow_monotone : Monotone (upShadow : Finset (Finset α) → Finset (Finset α)) :=
  fun _ _ => sup_mono

/-- `t` is in the upper shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one element
to get `t`. -/
/-
**Finset.mem_upShadow_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_upShadow_iff : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, exists a ∉ s, insert a s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`t` is in the upper shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remov
e one element
to get `t`.
-/
lemma mem_upShadow_iff : t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∉ s, insert a s = t := by
  simp_rw [upShadow, mem_sup, mem_image, mem_compl]
/-
**Finset.insert_mem_upShadow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_mem_upShadow (hs : s in 𝒜) (ha : a ∉ s) : insert a s in ∂⁺ 𝒜
参数：hs : s in 𝒜；ha : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_upShadow_iff`：mem_upShadow_iff : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, e
xists a ∉ s, insert a s = t
-/
theorem insert_mem_upShadow (hs : s ∈ 𝒜) (ha : a ∉ s) : insert a s ∈ ∂⁺ 𝒜 :=
  mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly one element more than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add_one`. -/
/-
**Finset.mem_upShadow_iff_exists_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_upShadow_iff_exists_sdiff : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ 
#(t \ s) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`t` is in the upper shadow of `𝒜` iff `t` is exactly one element more than somet
hing from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add_one`.
-/
lemma mem_upShadow_iff_exists_sdiff : t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #(t \ s) = 1 := by
  simp_rw [mem_upShadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]

/-- `t` is in the upper shadow of `𝒜` iff we can remove an element from it so that the resulting
finset is in `𝒜`. -/
/-
**Finset.mem_upShadow_iff_erase_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_upShadow_iff_erase_mem : t in ∂⁺ 𝒜 ↔ exists a, a in t ∧ erase t a in 𝒜
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
`t` is in the upper shadow of `𝒜` iff we can remove an element from it so that t
he resulting
finset is in `𝒜`.
-/
lemma mem_upShadow_iff_erase_mem : t ∈ ∂⁺ 𝒜 ↔ ∃ a, a ∈ t ∧ erase t a ∈ 𝒜 := by
  simp_rw [mem_upShadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]
  aesop

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_sdiff`. -/
/-
**Finset.mem_upShadow_iff_exists_mem_card_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set`。
形式化陈述：mem_upShadow_iff_exists_mem_card_add_one : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s su
bseteq t ∧ #t = #s + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Finset.mem_upShadow_iff_exists_sdiff`：mem_upShadow_iff_exists_sdiff : t 
in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #(t \ s) = 1
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`t` is in the upper shadow of `𝒜` iff `t` is exactly one element less than somet
hing from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_sdiff`.
-/
lemma mem_upShadow_iff_exists_mem_card_add_one :
    t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #t = #s + 1 := by
  refine mem_upShadow_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst
/-
**Finset.mem_upShadow_iterate_iff_exists_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：mem_upShadow_iterate_iff_exists_card : t in ∂⁺^[k] 𝒜 ↔ exists u : Finset α
, #u = k ∧ u subseteq t ∧ t \ u in 𝒜
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sdiff_empty`：sdiff_empty : s \ ∅ = s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Finset.erase_sdiff_comm`：erase_sdiff_comm (s t : Finset α) (a : α) : s.e
rase a \ t = (s \ t).erase a
· 使用定理 `Finset.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : 
insert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a 
in t ∧ s subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mem_upShadow_iterate_iff_exists_card :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ u : Finset α, #u = k ∧ u ⊆ t ∧ t \ u ∈ 𝒜 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_upShadow_iff_erase_mem, ih, Function.iterate_succ_apply', card_eq_succ,
      subset_erase, erase_sdiff_comm, ← sdiff_insert]
    constructor
    · rintro ⟨a, hat, u, rfl, ⟨hut, hau⟩, htu⟩
      exact ⟨_, ⟨_, _, hau, rfl, rfl⟩, insert_subset hat hut, htu⟩
    · rintro ⟨_, ⟨a, u, hau, rfl, rfl⟩, hut, htu⟩
      rw [insert_subset_iff] at hut
      exact ⟨a, hut.1, _, rfl, ⟨hut.2, hau⟩, htu⟩

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly `k` elements less than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add`. -/
/-
**Finset.mem_upShadow_iterate_iff_exists_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：mem_upShadow_iterate_iff_exists_sdiff : t in ∂⁺^[k] 𝒜 ↔ exists s in 𝒜, s s
ubseteq t ∧ #(t \ s) = k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mem_upShadow_iterate_iff_exists_card`：mem_upShadow_iterate_iff_ex
ists_card : t in ∂⁺^[k] 𝒜 ↔ exists u : Finset α, #u = k ∧ u subseteq t ∧ t \ u i
n 𝒜
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `Finset.sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : t subseteq s) : s \
 (s \ t) = t

--- 原说明 ---
`t` is in the upper shadow of `𝒜` iff `t` is exactly `k` elements less than some
thing from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add`.
-/
lemma mem_upShadow_iterate_iff_exists_sdiff : t ∈ ∂⁺^[k] 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #(t \ s) = k := by
  rw [mem_upShadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, hut, htu⟩
    exact ⟨_, htu, sdiff_subset, by rw [sdiff_sdiff_eq_self hut]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    exact ⟨_, rfl, sdiff_subset, by rwa [sdiff_sdiff_eq_self hst]⟩

/-- `t ∈ ∂⁺^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_upShadow_iterate_iff_exists_sdiff`. -/
/-
**Finset.mem_upShadow_iterate_iff_exists_mem_card_add** 是 Mathlib 中的一个引理，位于命名空间 
`Finset`。
形式化陈述：mem_upShadow_iterate_iff_exists_mem_card_add : t in ∂⁺^[k] 𝒜 ↔ exists s in
 𝒜, s subseteq t ∧ #t = #s + k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Finset.mem_upShadow_iterate_iff_exists_sdiff`：mem_upShadow_iterate_iff_e
xists_sdiff : t in ∂⁺^[k] 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #(t \ s) = k
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`t ∈ ∂⁺^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_upShadow_iterate_iff_exists_sdiff`.
-/
lemma mem_upShadow_iterate_iff_exists_mem_card_add :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #t = #s + k := by
  refine mem_upShadow_iterate_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

/-- The upper shadow of a family of `r`-sets is a family of `r + 1`-sets. -/
/-
**Finset._root_.Set.Sized.upShadow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper shadow of a family of `r`-sets is a family of `r + 1`-sets.
-/
protected lemma _root_.Set.Sized.upShadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂⁺ 𝒜 : Set (Finset α)).Sized (r + 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_notMem hi, h𝒜 hA]

/-- Being in the upper shadow of `𝒜` means we have a superset in `𝒜`. -/
/-
**Finset.exists_subset_of_mem_upShadow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_subset_of_mem_upShadow (hs : s in ∂⁺ 𝒜) : exists t in 𝒜, t subseteq
 s
参数：hs : s in ∂⁺ 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.mem_upShadow_iff_exists_mem_card_add_one`：mem_upShadow_iff_exists
_mem_card_add_one : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #t = #s + 1

--- 原说明 ---
Being in the upper shadow of `𝒜` means we have a superset in `𝒜`.
-/
theorem exists_subset_of_mem_upShadow (hs : s ∈ ∂⁺ 𝒜) : ∃ t ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements more than something in `𝒜`. -/
/-
**Finset.mem_upShadow_iff_exists_mem_card_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：mem_upShadow_iff_exists_mem_card_add : s in ∂⁺ ^[k] 𝒜 ↔ exists t in 𝒜, t s
ubseteq s ∧ #t + k = #s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.mem_upShadow_iff_exists_mem_card_add_one`：mem_upShadow_iff_exists
_mem_card_add_one : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #t = #s + 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用引理 `Finset.exists_subsuperset_card_eq`：exists_subsuperset_card_eq (hst : s s
ubseteq t) (hsn : #s <= n) (hnt : n <= #t) : exists u, s subseteq u ∧ u subseteq
 t ∧ #u = n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
`t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements more than something in `𝒜`.
-/
theorem mem_upShadow_iff_exists_mem_card_add :
    s ∈ ∂⁺ ^[k] 𝒜 ↔ ∃ t ∈ 𝒜, t ⊆ s ∧ #t + k = #s := by
  induction k generalizing 𝒜 s with
  | zero =>
    refine ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, ?_⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  | succ k ih =>
    simp only [Function.comp_apply, Function.iterate_succ]
    refine ih.trans ?_
    clear ih
    constructor
    · rintro ⟨t, ht, hts, hcardst⟩
      obtain ⟨u, hu, hut, hcardtu⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 ht
      refine ⟨u, hu, hut.trans hts, ?_⟩
      rw [← hcardst, hcardtu, add_right_comm]
      rfl
    · rintro ⟨t, ht, hts, hcard⟩
      obtain ⟨u, htu, hus, hu⟩ := Finset.exists_subsuperset_card_eq hts (Nat.le_add_right _ 1)
        (by lia)
      refine ⟨u, mem_upShadow_iff_exists_mem_card_add_one.2 ⟨t, ht, htu, hu⟩, hus, ?_⟩
      rw [hu, ← hcard, add_right_comm]
      rfl
/-
**Finset.shadow_compls** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {𝒜 : Finset (
Finset α)},   𝒜.compls.shadow = 𝒜.upShadow.compls
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Finset.compl_insert`：compl_insert : (insert a s)ᶜ = sᶜ.erase a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma shadow_compls : ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]
/-
**Finset.upShadow_compls** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {𝒜 : Finset (
Finset α)},   𝒜.compls.upShadow = 𝒜.shadow.compls
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Finset.compl_erase`：compl_erase : (s.erase a)ᶜ = insert a sᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma upShadow_compls : ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

end UpShadow

end Finset

