/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Cardinality of a finite set

This defines the cardinality of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.card`: `#s : ℕ` returns the cardinality of `s : Finset α`.

### Induction principles

* `Finset.strongInduction`: Strong induction
* `Finset.strongInductionOn`
* `Finset.strongDownwardInduction`
* `Finset.strongDownwardInductionOn`
* `Finset.case_strong_induction_on`
* `Finset.Nonempty.strong_induction`
* `Finset.eraseInduction`
-/

@[expose] public section

assert_not_exists Monoid

open Function Multiset Nat

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b c : α}

/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
/-
**Finset.card** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：card (s : Finset α) : Nat
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale.
-/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card
/-
**Finset.card_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_def (s : Finset α) : #s = Multiset.card s.1
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_def (s : Finset α) : #s = Multiset.card s.1 :=
  rfl
/-
**Finset.card_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), s.val.card = s.card
参数：s : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma card_val (s : Finset α) : Multiset.card s.1 = #s := rfl

@[simp]
/-
**Finset.card_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mk {m nodup} : #(⟨m, nodup⟩ : Finset α) = Multiset.card m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_mk {m nodup} : #(⟨m, nodup⟩ : Finset α) = Multiset.card m :=
  rfl

@[simp, grind =]
/-
**Finset.card_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_empty : #(∅ : Finset α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_empty : #(∅ : Finset α) = 0 :=
  rfl

@[gcongr]
/-
**Finset.card_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card : s subseteq t -> #s <= #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
-/
theorem card_le_card : s ⊆ t → #s ≤ #t :=
  Multiset.card_le_card ∘ val_le_iff.mpr

-- This pattern is unreasonable to use generally, but it's convenient in this file.
-- (Note that we turn it on again later in this file.)
local grind_pattern card_le_card => #s, #t

@[mono]
/-
**Finset.card_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mono : Monotone (@card α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
-/
theorem card_mono : Monotone (@card α) := by apply card_le_card
/-
**Finset.card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
-/
@[simp] lemma card_eq_zero : #s = 0 ↔ s = ∅ := Multiset.card_eq_zero.trans val_eq_zero
/-
**Finset.card_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_ne_zero : #s != 0 ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
-/
lemma card_ne_zero : #s ≠ 0 ↔ s.Nonempty := card_eq_zero.ne.trans nonempty_iff_ne_empty.symm
/-
**Finset.card_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `Finset.card_ne_zero`：card_ne_zero : #s != 0 ↔ s.Nonempty
-/
@[simp] lemma card_pos : 0 < #s ↔ s.Nonempty := Nat.pos_iff_ne_zero.trans card_ne_zero
/-
**Finset.one_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, 1 ≤ s.card ↔ s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
-/
@[simp] lemma one_le_card : 1 ≤ #s ↔ s.Nonempty := card_pos

alias ⟨_, Nonempty.card_pos⟩ := card_pos
alias ⟨_, Nonempty.card_ne_zero⟩ := card_ne_zero
/-
**Finset.card_ne_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_ne_zero_of_mem (h : a in s) : #s != 0
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.ne_empty_of_mem`：ne_empty_of_mem {a : α} {s : Finset α} (h : a in
 s) : s != ∅
-/
theorem card_ne_zero_of_mem (h : a ∈ s) : #s ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h

grind_pattern card_ne_zero_of_mem => a ∈ s, #s

@[simp, grind =]
/-
**Finset.card_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_singleton (a : α) : #{a} = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
-/
theorem card_singleton (a : α) : #{a} = 1 :=
  Multiset.card_singleton _
/-
**Finset.card_singleton_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_singleton_inter [DecidableEq α] : #({a} inter s) <= 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_singleton_inter [DecidableEq α] : #({a} ∩ s) ≤ 1 := by grind

@[simp, grind =]
/-
**Finset.card_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
-/
theorem card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1 :=
  Multiset.card_cons _ _

section InsertErase

variable [DecidableEq α]

@[simp, grind =]
/-
**Finset.card_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_insert_of_notMem (h : a ∉ s) : #(insert a s) = #s + 1
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_insert_of_notMem (h : a ∉ s) : #(insert a s) = #s + 1 := by
  grind [=_ cons_eq_insert]
/-
**Finset.card_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_insert_of_mem (h : a in s) : #(insert a s) = #s
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
-/
theorem card_insert_of_mem (h : a ∈ s) : #(insert a s) = #s := by rw [insert_eq_of_mem h]
/-
**Finset.card_insert_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_insert_le (a : α) (s : Finset α) : #(insert a s) <= #s + 1
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_insert_le (a : α) (s : Finset α) : #(insert a s) ≤ #s + 1 := by grind

section

variable {a b c d e f : α}

/-
**Finset.card_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_two : #{a, b} <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
-/
theorem card_le_two : #{a, b} ≤ 2 := card_insert_le _ _
/-
**Finset.card_le_three** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_three : #{a, b, c} <= 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Finset.card_le_two`：card_le_two : #{a, b} <= 2
-/
theorem card_le_three : #{a, b, c} ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)
/-
**Finset.card_le_four** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_four : #{a, b, c, d} <= 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Finset.card_le_three`：card_le_three : #{a, b, c} <= 3
-/
theorem card_le_four : #{a, b, c, d} ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_three)
/-
**Finset.card_le_five** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_five : #{a, b, c, d, e} <= 5
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Finset.card_le_four`：card_le_four : #{a, b, c, d} <= 4
-/
theorem card_le_five : #{a, b, c, d, e} ≤ 5 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_four)
/-
**Finset.card_le_six** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_six : #{a, b, c, d, e, f} <= 6
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Finset.card_le_five`：card_le_five : #{a, b, c, d, e} <= 5
-/
theorem card_le_six : #{a, b, c, d, e, f} ≤ 6 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_five)

end

/-- If `a ∈ s` is known, see also `Finset.card_insert_of_mem` and `Finset.card_insert_of_notMem`.
-/
/-
**Finset.card_insert_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_insert_eq_ite : #(insert a s) = if a in s then #s else #s + 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a ∈ s` is known, see also `Finset.card_insert_of_mem` and `Finset.card_inser
t_of_notMem`.
-/
theorem card_insert_eq_ite : #(insert a s) = if a ∈ s then #s else #s + 1 := by grind

@[simp]
/-
**Finset.card_pair_eq_one_or_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_pair_eq_one_or_two : #{a, b} = 1 ∨ #{a, b} = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_pair_eq_one_or_two : #{a, b} = 1 ∨ #{a, b} = 2 := by grind

/-- A two-element finset `{a, b}` has cardinality `2` iff `a ≠ b`. The reverse direction is
`Finset.card_pair`. -/
/-
**Finset.card_pair_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_pair_eq_two_iff : #{a, b} = 2 ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_insert_eq_ite`：card_insert_eq_ite : #(insert a s) = if a in 
s then #s else #s + 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A two-element finset `{a, b}` has cardinality `2` iff `a ≠ b`. The reverse direc
tion is
`Finset.card_pair`.
-/
theorem card_pair_eq_two_iff : #{a, b} = 2 ↔ a ≠ b := by
  aesop (add simp card_insert_eq_ite)

alias ⟨_, card_pair⟩ := card_pair_eq_two_iff

/-- A three-element finset `{a, b, c}` has cardinality `3` iff `a`, `b`, `c` are pairwise
distinct. -/
/-
**Finset.card_triple_eq_three_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_triple_eq_three_iff : #{a, b, c} = 3 ↔ a != b ∧ a != c ∧ b != c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_insert_eq_ite`：card_insert_eq_ite : #(insert a s) = if a in 
s then #s else #s + 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
A three-element finset `{a, b, c}` has cardinality `3` iff `a`, `b`, `c` are pai
rwise
distinct.
-/
theorem card_triple_eq_three_iff : #{a, b, c} = 3 ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  aesop (add simp card_insert_eq_ite)

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$. -/
@[simp, grind =]
/-
**Finset.card_erase_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_erase_of_mem : a in s -> #(s.erase a) = #s - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_erase_of_mem`：card_erase_of_mem {a : α} {s : Multiset α} :
 a in s -> card (s.erase a) = pred (card s)

--- 原说明 ---
$\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$.
-/
theorem card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1 :=
  Multiset.card_erase_of_mem

-- @[simp] -- removed because LHS is not in simp normal form
/-
**Finset.card_erase_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_erase_add_one : a in s -> #(s.erase a) + 1 = #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_erase_add_one`：card_erase_add_one {a : α} {s : Multiset α}
 : a in s -> card (s.erase a) + 1 = card s
-/
theorem card_erase_add_one : a ∈ s → #(s.erase a) + 1 = #s :=
  Multiset.card_erase_add_one
/-
**Finset.card_erase_lt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_erase_lt_of_mem : a in s -> #(s.erase a) < #s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_erase_lt_of_mem`：card_erase_lt_of_mem {a : α} {s : Multise
t α} : a in s -> card (s.erase a) < card s
-/
theorem card_erase_lt_of_mem : a ∈ s → #(s.erase a) < #s :=
  Multiset.card_erase_lt_of_mem
/-
**Finset.card_erase_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_erase_le : #(s.erase a) <= #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_erase_le`：card_erase_le {a : α} {s : Multiset α} : card (s
.erase a) <= card s
-/
theorem card_erase_le : #(s.erase a) ≤ #s :=
  Multiset.card_erase_le
/-
**Finset.pred_card_le_card_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pred_card_le_card_erase : #s - 1 <= #(s.erase a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pred_card_le_card_erase : #s - 1 ≤ #(s.erase a) := by grind

/-- If `a ∈ s` is known, see also `Finset.card_erase_of_mem` and `Finset.erase_eq_of_notMem`. -/
/-
**Finset.card_erase_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_erase_eq_ite : #(s.erase a) = if a in s then #s - 1 else #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_erase_eq_ite`：card_erase_eq_ite {a : α} {s : Multiset α} :
 card (s.erase a) = if a in s then pred (card s) else card s

--- 原说明 ---
If `a ∈ s` is known, see also `Finset.card_erase_of_mem` and `Finset.erase_eq_of
_notMem`.
-/
theorem card_erase_eq_ite : #(s.erase a) = if a ∈ s then #s - 1 else #s :=
  Multiset.card_erase_eq_ite

end InsertErase

@[simp, grind =]
/-
**Finset.card_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_range (n : Nat) : #(range n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_range`：card_range (n : Nat) : card (range n) = n
-/
theorem card_range (n : ℕ) : #(range n) = n :=
  Multiset.card_range n

@[simp, grind =]
/-
**Finset.card_attach** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_attach : #s.attach = #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_attach`：card_attach {m : Multiset α} : card (attach m) = c
ard m
-/
theorem card_attach : #s.attach = #s :=
  Multiset.card_attach

end Finset

open scoped Finset

section ToMultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

/-
**Multiset.card_toFinset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.card_toFinset : #m.toFinset = Multiset.card m.dedup
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Multiset.card_toFinset : #m.toFinset = Multiset.card m.dedup :=
  rfl
/-
**Multiset.toFinset_card_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.toFinset_card_le : #m.toFinset <= Multiset.card m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
-/
theorem Multiset.toFinset_card_le : #m.toFinset ≤ Multiset.card m :=
  card_le_card <| dedup_le _
/-
**Multiset.toFinset_card_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.toFinset_card_of_nodup {m : Multiset α} (h : m.Nodup) : #m.toFins
et = Multiset.card m
参数：h : m.Nodup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
-/
theorem Multiset.toFinset_card_of_nodup {m : Multiset α} (h : m.Nodup) :
    #m.toFinset = Multiset.card m :=
  congr_arg card <| Multiset.dedup_eq_self.mpr h
/-
**Multiset.dedup_card_eq_card_iff_nodup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.dedup_card_eq_card_iff_nodup {m : Multiset α} : card m.dedup = ca
rd m ↔ m.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
-/
theorem Multiset.dedup_card_eq_card_iff_nodup {m : Multiset α} :
    card m.dedup = card m ↔ m.Nodup :=
  .trans ⟨fun h ↦ eq_of_le_of_card_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self
/-
**Multiset.toFinset_card_eq_card_iff_nodup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.toFinset_card_eq_card_iff_nodup {m : Multiset α} : #m.toFinset = 
card m ↔ m.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.dedup_card_eq_card_iff_nodup`：Multiset.dedup_card_eq_card_iff_n
odup {m : Multiset α} : card m.dedup = card m ↔ m.Nodup
-/
theorem Multiset.toFinset_card_eq_card_iff_nodup {m : Multiset α} :
    #m.toFinset = card m ↔ m.Nodup := dedup_card_eq_card_iff_nodup
/-
**List.card_toFinset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.card_toFinset : #l.toFinset = l.dedup.length
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.card_toFinset : #l.toFinset = l.dedup.length :=
  rfl
/-
**List.toFinset_card_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.toFinset_card_le : #l.toFinset <= l.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
-/
theorem List.toFinset_card_le : #l.toFinset ≤ l.length :=
  Multiset.toFinset_card_le ⟦l⟧
/-
**List.toFinset_card_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.toFinset_card_of_nodup {l : List α} (h : l.Nodup) : #l.toFinset = l.l
ength
参数：h : l.Nodup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.toFinset_card_of_nodup`：Multiset.toFinset_card_of_nodup {m : Mu
ltiset α} (h : m.Nodup) : #m.toFinset = Multiset.card m
-/
theorem List.toFinset_card_of_nodup {l : List α} (h : l.Nodup) : #l.toFinset = l.length :=
  Multiset.toFinset_card_of_nodup h
/-
**List.Nodup.card_eq_countP** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：List.Nodup.card_eq_countP {l : List α} {P : α -> Prop} [DecidablePred P] (
h : l.Nodup) : (l.toFinset.filter P).card = countP P l
参数：h : l.Nodup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.countP_eq_length_filter`：∀ {α : Type u_1} {p : α → Bool} {l : List 
α}, List.countP p l = (List.filter p l).length
· 使用定理 `List.filter_toFinset`：filter_toFinset (s : List α) (p : α -> Prop) [Deci
dablePred p] : s.toFinset.filter p = (s.filter p).toFinset
· 使用定理 `List.toFinset_card_of_nodup`：List.toFinset_card_of_nodup {l : List α} (h
 : l.Nodup) : #l.toFinset = l.length
· 使用定理 `List.Nodup.filter`：∀ {α : Type u} (p : α → Bool) {l : List α}, l.Nodup →
 (List.filter p l).Nodup
-/
lemma List.Nodup.card_eq_countP {l : List α} {P : α → Prop} [DecidablePred P] (h : l.Nodup) :
    (l.toFinset.filter P).card = countP P l := by
  rw [l.countP_eq_length_filter, l.filter_toFinset P]
  exact toFinset_card_of_nodup (h.filter P)

end ToMultiset

namespace Finset

variable {s t u : Finset α} {f : α → β} {n : ℕ}

@[simp, grind =]
/-
**Finset.length_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：length_toList (s : Finset α) : s.toList.length = #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.toList.eq_1`：∀ {α : Type u_1} (s : Finset α), s.toList = s.val.to
List
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_card`：coe_card (l : List α) : card (l : Multiset α) = lengt
h l
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
-/
theorem length_toList (s : Finset α) : s.toList.length = #s := by
  rw [toList, ← Multiset.coe_card, Multiset.coe_toList, card_def]
/-
**Finset.card_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_image_le [DecidableEq β] : #(s.image f) <= #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
-/
theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s := by
  simpa only [card_map] using! (s.1.map f).toFinset_card_le

grind_pattern card_image_le => #(s.image f)
grind_pattern card_image_le => s.image f, #s
/-
**Finset.card_image_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #
s
参数：H : Set.InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_val_of_injOn`：image_val_of_injOn (H : Set.InjOn f s) : (ima
ge f s).1 = s.1.map f
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #s := by
  simp only [card, image_val_of_injOn H, card_map]
/-
**Finset.injOn_of_card_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：injOn_of_card_image_eq [DecidableEq β] (H : #(s.image f) = #s) : Set.InjOn
 f s
参数：H : #(s.image f) = #s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.nodup_dedup`：nodup_dedup (s : Multiset α) : Nodup (dedup s)
· 使用定理 `Multiset.toFinset.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mul
tiset α), s.toFinset = { val := s.dedup, nodup := ⋯ }
· 使用定理 `Finset.image.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β
] (f : α → β) (s : Finset α),   Finset.image f s = (Multiset.map f s.val).toFins
et
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `Multiset.inj_on_of_nodup_map`：inj_on_of_nodup_map {f : α -> β} {s : Mult
iset α} : Nodup (map f s) -> forall x in s, forall y in s, f x = f y -> x = y
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
-/
theorem injOn_of_card_image_eq [DecidableEq β] (H : #(s.image f) = #s) : Set.InjOn f s := by
  rw [card_def, card_def, image, toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) ?_
    simp only [H, Multiset.card_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this
/-
**Finset.card_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_image_iff [DecidableEq β] : #(s.image f) = #s ↔ Set.InjOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.injOn_of_card_image_eq`：injOn_of_card_image_eq [DecidableEq β] (H
 : #(s.image f) = #s) : Set.InjOn f s
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
-/
theorem card_image_iff [DecidableEq β] : #(s.image f) = #s ↔ Set.InjOn f s :=
  ⟨injOn_of_card_image_eq, card_image_of_injOn⟩

grind_pattern card_image_iff => #(s.image f)
grind_pattern card_image_iff => s.image f, #s
/-
**Finset.card_image_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
 #(s.image f) = #s
参数：s : Finset α；H : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
-/
theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    #(s.image f) = #s :=
  card_image_of_injOn fun _ _ _ _ h => H h
/-
**Finset.fiber_card_ne_zero_iff_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α -> β) [DecidableEq 
β] (y : β) : #(s.filter fun x => f x = y) != 0 ↔ y in s.image f
参数：s : Finset α；f : α -> β；y : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Finset.fiber_nonempty_iff_mem_image`：fiber_nonempty_iff_mem_image {y : β
} : (s.filter (f · = y)).Nonempty ↔ y in s.image f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    #(s.filter fun x ↦ f x = y) ≠ 0 ↔ y ∈ s.image f := by
  rw [← Nat.pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]
/-
**Finset.card_filter_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_filter_le_iff (s : Finset α) (P : α -> Prop) [DecidablePred P] (n : N
at) : #(s.filter P) <= n ↔ forall s' subseteq s, n < #s' -> exists a in s', ¬ P 
a
参数：s : Finset α；P : α -> Prop；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Multiset.card_filter_le_iff`：card_filter_le_iff (s : Multiset α) (P : α 
-> Prop) [DecidablePred P] (n : Nat) : card (s.filter P) <= n ↔ forall s' <= s, 
n < card s' -> ex…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
-/
lemma card_filter_le_iff (s : Finset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    #(s.filter P) ≤ n ↔ ∀ s' ⊆ s, n < #s' → ∃ a ∈ s', ¬ P a :=
  (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h ↦ H s'.1 (by simp_all) h,
    fun H s' hs' h ↦ H ⟨s', nodup_of_le hs' s.2⟩ (fun _ hx ↦ Multiset.subset_of_le hs' hx) h⟩

@[simp, grind =]
/-
**Finset.card_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_map (f : α ↪ β) : #(s.map f) = #s
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
theorem card_map (f : α ↪ β) : #(s.map f) = #s :=
  Multiset.card_map _ _

@[simp, grind =]
/-
**Finset.card_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_subtype (p : α -> Prop) [DecidablePred p] (s : Finset α) : #(s.subtyp
e p) = #(s.filter p)
参数：p : α -> Prop；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) :
    #(s.subtype p) = #(s.filter p) := by simp [Finset.subtype]
/-
**Finset.card_filter_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_filter_le (s : Finset α) (p : α -> Prop) [DecidablePred p] : #(s.filt
er p) <= #s
参数：s : Finset α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] :
    #(s.filter p) ≤ #s :=
  card_le_card <| filter_subset _ _

grind_pattern card_filter_le => #(s.filter p)
grind_pattern card_filter_le => s.filter p, #s
/-
**Finset.eq_of_subset_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_subset_of_card_le (h : s subseteq t) (h₂ : #t <= #s) : s = t
参数：h : s subseteq t；h₂ : #t <= #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
-/
theorem eq_of_subset_of_card_le (h : s ⊆ t) (h₂ : #t ≤ #s) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂
/-
**Finset.eq_iff_card_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_iff_card_le_of_subset (hst : s subseteq t) : #t <= #s ↔ s = t
参数：hst : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem eq_iff_card_le_of_subset (hst : s ⊆ t) : #t ≤ #s ↔ s = t :=
  ⟨eq_of_subset_of_card_le hst, (ge_of_eq <| congr_arg _ ·)⟩
/-
**Finset.eq_of_superset_of_card_ge** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_superset_of_card_ge (hst : s subseteq t) (hts : #t <= #s) : t = s
参数：hst : s subseteq t；hts : #t <= #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
-/
theorem eq_of_superset_of_card_ge (hst : s ⊆ t) (hts : #t ≤ #s) : t = s :=
  (eq_of_subset_of_card_le hst hts).symm
/-
**Finset.eq_iff_card_ge_of_superset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_iff_card_ge_of_superset (hst : s subseteq t) : #t <= #s ↔ t = s
参数：hst : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.eq_iff_card_le_of_subset`：eq_iff_card_le_of_subset (hst : s subse
teq t) : #t <= #s ↔ s = t
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem eq_iff_card_ge_of_superset (hst : s ⊆ t) : #t ≤ #s ↔ t = s :=
  (eq_iff_card_le_of_subset hst).trans eq_comm
/-
**Finset.subset_iff_eq_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_iff_eq_of_card_le (h : #t <= #s) : s subseteq t ↔ s = t
参数：h : #t <= #s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem subset_iff_eq_of_card_le (h : #t ≤ #s) : s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset⟩
/-
**Finset.map_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_eq_of_subset {f : α ↪ α} (hs : s.map f subseteq s) : s.map f = s
参数：hs : s.map f subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).ge
/-
**Finset.card_filter_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_filter_eq_iff {p : α -> Prop} [DecidablePred p] : #(s.filter p) = #s 
↔ forall x in s, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `Finset.eq_iff_card_le_of_subset`：eq_iff_card_le_of_subset (hst : s subse
teq t) : #t <= #s ↔ s = t
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Finset.filter_eq_self`：∀ {α : Type u_1} {p : α → Prop} [inst : Decidable
Pred p] {s : Finset α}, Finset.filter p s = s ↔ ∀ x ∈ s, p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_filter_eq_iff {p : α → Prop} [DecidablePred p] :
    #(s.filter p) = #s ↔ ∀ x ∈ s, p x := by
  rw [← (card_filter_le s p).ge_iff_eq, eq_iff_card_le_of_subset (filter_subset p s),
    filter_eq_self]

alias ⟨filter_card_eq, _⟩ := card_filter_eq_iff
/-
**Finset.card_filter_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_filter_eq_zero_iff {p : α -> Prop} [DecidablePred p] : #(s.filter p) 
= 0 ↔ forall x in s, ¬ p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.filter_eq_empty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, Finset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_filter_eq_zero_iff {p : α → Prop} [DecidablePred p] :
    #(s.filter p) = 0 ↔ ∀ x ∈ s, ¬ p x := by
  rw [card_eq_zero, filter_eq_empty_iff]

@[gcongr]
nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t := card_lt_card <| val_lt_iff.2 h
/-
**Finset.card_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_strictMono : StrictMono (card : Finset α -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
-/
lemma card_strictMono : StrictMono (card : Finset α → ℕ) := fun _ _ ↦ card_lt_card

section bij

/--
See also `card_bij`.
TODO: consider deprecating, since this has been unused in mathlib for a long time and is just a
special case of `card_bij`.
-/
/-
**Finset.card_eq_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_of_bijective (f : forall i, i < n -> α) (hf : forall a in s, exist
s i, exists h : i < n, f i h = a) (hf' : forall i (h : i < n), f i h in s) (f_in
j : forall i j (hi : i < n) (hj : j < n), f i hi = f j hj -> i = j) : #s = n
参数：f : forall i, i < n -> α；hf : forall a in s, exists i, exists h : i < n, f i 
h = a；hf' : forall i (h : i < n), f i h in s；f_inj : forall i j (hi : i < n) (hj
 : j < n), f i hi = f j hj -> i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n

--- 原说明 ---
See also `card_bij`.
TODO: consider deprecating, since this has been unused in mathlib for a long tim
e and is just a
special case of `card_bij`.
-/
theorem card_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ i (h : i < n), f i h ∈ s)
    (f_inj : ∀ i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : #s = n := by
  classical
  have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
    ext a
    suffices _ : a ∈ s ↔ ∃ (i : _) (hi : i ∈ range n), f i (mem_range.1 hi) = a by
      simpa only [mem_image, mem_attach, true_and, Subtype.exists]
    constructor
    · intro ha; obtain ⟨i, hi, rfl⟩ := hf a ha; use i, mem_range.2 hi
    · rintro ⟨i, hi, rfl⟩; apply hf'
  calc
    #s = #((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
    _ = #(range n).attach := ?_
    _ = #(range n) := card_attach
    _ = n := card_range n
  apply card_image_of_injective
  intro ⟨i, hi⟩ ⟨j, hj⟩ eq
  exact Subtype.ext <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq

variable {t : Finset β}

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.card_nbij` is that the bijection is allowed to use membership of the
domain, rather than being a non-dependent function. -/
/-
**Finset.card_bij** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_bij (i : forall a in s, β) (hi : forall a ha, i a ha in t) (i_inj : f
orall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj : forall b in t, ex
ists a ha, i a ha = b) : #s = #t
参数：i : forall a in s, β；hi : forall a ha, i a ha in t；i_inj : forall a₁ ha₁ a₂ h
a₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂；i_surj : forall b in t, exists a ha, i a ha =
 b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Given a bijection from a finite set `s` to a finite set `t`, the cardinalities o
f `s` and `t`
are equal.

The difference with `Finset.card_bij'` is that the bijection is specified as a s
urjective injection,
rather than by an inverse function.

The difference with `Finset.card_nbij` is that the bijection is allowed to use m
embership of the
domain, rather than being a non-dependent function.
-/
lemma card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : #s = #t := by
  classical
  calc
    #s = #s.attach := card_attach.symm
    _ = #(s.attach.image fun a ↦ i a.1 a.2) := Eq.symm ?_
    _ = #t := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains, rather than being non-dependent functions. -/
/-
**Finset.card_bij'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_bij' (i : forall a in s, β) (j : forall a in t, α) (hi : forall a ha,
 i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : forall a ha, j (i a ha
) (hi a ha) = a) (right_inv : forall a ha, i (j a ha) (hj a ha) = a) : #s = #t
参数：i : forall a in s, β；j : forall a in t, α；hi : forall a ha, i a ha in t；hj : 
forall a ha, j a ha in s；left_inv : forall a ha, j (i a ha) (hi a ha) = a；right_
inv : forall a ha, i (j a ha) (hj a ha) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a bijection from a finite set `s` to a finite set `t`, the cardinalities o
f `s` and `t`
are equal.

The difference with `Finset.card_bij` is that the bijection is specified with an
 inverse, rather
than as a surjective injection.

The difference with `Finset.card_nbij'` is that the bijection and its inverse ar
e allowed to use
membership of the domains, rather than being non-dependent functions.
-/
lemma card_bij' (i : ∀ a ∈ s, β) (j : ∀ a ∈ t, α) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : #s = #t := by
  refine card_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1, ← left_inv a2 h2]
  simp only [eq]

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain. -/
/-
**Finset.card_nbij** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_nbij (i : α -> β) (hi : Set.MapsTo i s t) (i_inj : (s : Set α).InjOn 
i) (i_surj : (s : Set α).SurjOn i t) : #s = #t
参数：i : α -> β；hi : Set.MapsTo i s t；i_inj : (s : Set α).InjOn i；i_surj : (s : Se
t α).SurjOn i t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given a bijection from a finite set `s` to a finite set `t`, the cardinalities o
f `s` and `t`
are equal.

The difference with `Finset.card_nbij'` is that the bijection is specified as a 
surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent f
unction, rather than
being allowed to use membership of the domain.
-/
lemma card_nbij (i : α → β) (hi : Set.MapsTo i s t) (i_inj : (s : Set α).InjOn i)
    (i_surj : (s : Set α).SurjOn i t) : #s = #t :=
  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using! i_surj)

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to hold on the domains,
rather than on the entire types. -/
/-
**Finset.card_nbij'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo i s t) (hj : Set.Map
sTo j t s) (left_inv : Set.LeftInvOn j i s) (right_inv : Set.RightInvOn j i t) :
 #s = #t
参数：i : α -> β；j : β -> α；hi : Set.MapsTo i s t；hj : Set.MapsTo j t s；left_inv : 
Set.LeftInvOn j i s；right_inv : Set.RightInvOn j i t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_bij'`：card_bij' (i : forall a in s, β) (j : forall a in t, α
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…

--- 原说明 ---
Given a bijection from a finite set `s` to a finite set `t`, the cardinalities o
f `s` and `t`
are equal.

The difference with `Finset.card_nbij` is that the bijection is specified with a
n inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are
 non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to 
hold on the domains,
rather than on the entire types.
-/
lemma card_nbij' (i : α → β) (j : β → α) (hi : Set.MapsTo i s t) (hj : Set.MapsTo j t s)
    (left_inv : Set.LeftInvOn j i s) (right_inv : Set.RightInvOn j i t) : #s = #t :=
  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv

/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `s` and `t` are `univ`. -/
/-
**Finset.card_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i in t) : #s = #t
参数：e : α ≃ β；hst : forall i, i in s ↔ e i in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_nbij'`：card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo
 i s t) (hj : Set.MapsTo j t s) (left_inv : Set.LeftInvOn j i s) (right_inv : Se
t.Right…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Specialization of `Finset.card_nbij'` that automatically fills in most arguments
.

See `Fintype.card_equiv` for the version where `s` and `t` are `univ`.
-/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst, Set.MapsTo, Set.LeftInvOn, Set.RightInvOn]

/-- Specialization of `Finset.card_nbij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `s` and `t` are `univ`. -/
/-
**Finset.card_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_bijective (e : α -> β) (he : e.Bijective) (hst : forall i, i in s ↔ e
 i in t) : #s = #t
参数：e : α -> β；he : e.Bijective；hst : forall i, i in s ↔ e i in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t

--- 原说明 ---
Specialization of `Finset.card_nbij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `s` and `t` are `univ`.
-/
lemma card_bijective (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t) :
    #s = #t := card_equiv (.ofBijective e he) hst
/-
**Finset._root_.Set.BijOn.finsetCard_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.BijOn.finsetCard_eq (e : α → β) (he : Set.BijOn e s t) : #s = #t :=
  card_nbij e he.mapsTo he.injOn he.surjOn
/-
**Finset.card_le_card_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_of_injOn (f : α -> β) (hf : Set.MapsTo f s t) (f_inj : (s : S
et α).InjOn f) : #s <= #t
参数：f : α -> β；hf : Set.MapsTo f s t；f_inj : (s : Set α).InjOn f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
-/
lemma card_le_card_of_injOn (f : α → β) (hf : Set.MapsTo f s t) (f_inj : (s : Set α).InjOn f) :
    #s ≤ #t := by
  classical
  calc
    #s = #(s.image f) := (card_image_of_injOn f_inj).symm
    _ ≤ #t := card_le_card <| image_subset_iff.2 hf
/-
**Finset.card_le_card_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_of_injective {f : s -> t} (hf : f.Injective) : #s <= #t
参数：hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
-/
lemma card_le_card_of_injective {f : s → t} (hf : f.Injective) : #s ≤ #t := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  · classical
    let f' : α → β := fun a => f (if ha : a ∈ s then ⟨a, ha⟩ else ⟨a₀, ha₀⟩)
    apply card_le_card_of_injOn f'
    · aesop (add safe unfold Set.MapsTo)
    · intro a₁ ha₁ a₂ ha₂ haa
      rw [mem_coe] at ha₁ ha₂
      simp only [f', ha₁, ha₂, ← Subtype.ext_iff] at haa
      exact Subtype.ext_iff.mp (hf haa)

grind_pattern card_le_card_of_injective => f.Injective, #s
grind_pattern card_le_card_of_injective => f.Injective, #t
/-
**Finset.card_le_card_of_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_of_surjOn (f : α -> β) (hf : Set.SurjOn f s t) : #t <= #s
参数：f : α -> β；hf : Set.SurjOn f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
lemma card_le_card_of_surjOn (f : α → β) (hf : Set.SurjOn f s t) : #t ≤ #s := by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.

See also `Set.exists_ne_map_eq_of_encard_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_ncard_lt_of_maps_to`. -/
/-
**Finset.exists_ne_map_eq_of_card_lt_of_maps_to** 是 Mathlib 中的一个定理，位于命名空间 `Finse
t`。
形式化陈述：exists_ne_map_eq_of_card_lt_of_maps_to (hc : #t < #s) {f : α -> β} (hf : S
et.MapsTo f s t) : exists x in s, exists y in s, x != y ∧ f x = f y
参数：hc : #t < #s；hf : Set.MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If there are more pigeons than pigeonholes, then there are two pigeons in the sa
me pigeonhole.

See also `Set.exists_ne_map_eq_of_encard_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_ncard_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to (hc : #t < #s) {f : α → β}
    (hf : Set.MapsTo f s t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra! hz
  refine hc.not_ge (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

/-- a special case of `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` where `t` is `s.image f` -/
/-
**Finset.exists_ne_map_eq_of_card_image_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_ne_map_eq_of_card_image_lt [DecidableEq β] {f : α -> β} (hc : #(s.i
mage f) < #s) : exists x in s, exists y in s, x != y ∧ f x = f y
参数：hc : #(s.image f) < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`：exists_ne_map_eq_of_card_
lt_of_maps_to (hc : #t < #s) {f : α -> β} (hf : Set.MapsTo f s t) : exists x in 
s, exists y in s, x != y ∧ f x = f …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s

--- 原说明 ---
a special case of `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` where `t` is `
s.image f`
-/
theorem exists_ne_map_eq_of_card_image_lt [DecidableEq β] {f : α → β} (hc : #(s.image f) < #s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
  exists_ne_map_eq_of_card_lt_of_maps_to hc (coe_image (β := β) ▸ Set.mapsTo_image f s)

/-- a variant of `Finset.exists_ne_map_eq_of_card_image_lt` using `Set.InjOn` -/
/-
**Finset.not_injOn_of_card_image_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_injOn_of_card_image_lt [DecidableEq β] {f : α -> β} (hc : #(s.image f)
 < #s) : ¬ Set.InjOn f s
参数：hc : #(s.image f) < #s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
a variant of `Finset.exists_ne_map_eq_of_card_image_lt` using `Set.InjOn`
-/
theorem not_injOn_of_card_image_lt [DecidableEq β] {f : α → β} (hc : #(s.image f) < #s) :
    ¬ Set.InjOn f s :=
  mt card_image_of_injOn hc.ne

/--
See also `Finset.card_le_card_of_injOn`, which is a more general version of this lemma.
TODO: consider deprecating, since this is just a special case of `Finset.card_le_card_of_injOn`.
-/
/-
**Finset.le_card_of_inj_on_range** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_card_of_inj_on_range (f : Nat -> α) (hf : forall i < n, f i in s) (f_in
j : forall i < n, forall j < n, f i = f j -> i = j) : n <= #s
参数：f : Nat -> α；hf : forall i < n, f i in s；f_inj : forall i < n, forall j < n, 
f i = f j -> i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n

--- 原说明 ---
See also `Finset.card_le_card_of_injOn`, which is a more general version of this
 lemma.
TODO: consider deprecating, since this is just a special case of `Finset.card_le
_card_of_injOn`.
-/
lemma le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ #s :=
  calc
    n = #(range n) := (card_range n).symm
    _ ≤ #s := card_le_card_of_injOn f (by simpa [Set.MapsTo, mem_range] using hf) (by simpa)

/--
Given an injective map `f` from a finite set `s` to another finite set `t`, if `t` is no larger
than `s`, then `f` is surjective to `t` when restricted to `s`.
See `Finset.surj_on_of_inj_on_of_card_le` for the version where `f` is a dependent function.
-/
/-
**Finset.surjOn_of_injOn_of_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：surjOn_of_injOn_of_card_le (f : α -> β) (hf : Set.MapsTo f s t) (hinj : Se
t.InjOn f s) (hst : #t <= #s) : Set.SurjOn f s t
参数：f : α -> β；hf : Set.MapsTo f s t；hinj : Set.InjOn f s；hst : #t <= #s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.finsetImage_subset`：∀ {α : Type u_1} {β : Type u_2} [inst : D
ecidableEq β] {f : α → β} {s : Finset α} {t : Finset β},   Set.MapsTo f ↑s ↑t → 
Finset.image f s ⊆ …
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.surjOn_iff_subset_image`：surjOn_iff_subset_image : Set.SurjOn f s
 t ↔ t subseteq s.image f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Given an injective map `f` from a finite set `s` to another finite set `t`, if `
t` is no larger
than `s`, then `f` is surjective to `t` when restricted to `s`.
See `Finset.surj_on_of_inj_on_of_card_le` for the version where `f` is a depende
nt function.
-/
lemma surjOn_of_injOn_of_card_le (f : α → β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s)
    (hst : #t ≤ #s) : Set.SurjOn f s t := by
  classical
  suffices s.image f = t by rw [Finset.surjOn_iff_subset_image, this]
  have : s.image f ⊆ t := hf.finsetImage_subset
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

/--
Given an injective map `f` defined on a finite set `s` to another finite set `t`, if `t` is no
larger than `s`, then `f` is surjective to `t` when restricted to `s`.
See `Finset.surjOn_of_injOn_of_card_le` for the version where `f` is a non-dependent function.
-/
/-
**Finset.surj_on_of_inj_on_of_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：surj_on_of_inj_on_of_card_le (f : forall a in s, β) (hf : forall a ha, f a
 ha in t) (hinj : forall a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ -> a₁ = a₂) (hst : #
t <= #s) : forall b in t, exists a ha, b = f a ha
参数：f : forall a in s, β；hf : forall a ha, f a ha in t；hinj : forall a₁ a₂ ha₁ ha
₂, f a₁ ha₁ = f a₂ ha₂ -> a₁ = a₂；hst : #t <= #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `Finset.surjOn_of_injOn_of_card_le`：surjOn_of_injOn_of_card_le (f : α -> 
β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s) (hst : #t <= #s) : Set.SurjOn 
f s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s

--- 原说明 ---
Given an injective map `f` defined on a finite set `s` to another finite set `t`
, if `t` is no
larger than `s`, then `f` is surjective to `t` when restricted to `s`.
See `Finset.surjOn_of_injOn_of_card_le` for the version where `f` is a non-depen
dent function.
-/
lemma surj_on_of_inj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : #t ≤ #s) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  let f' : s → β := fun a ↦ f a a.2
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy ↦ Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx ↦ hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le _ hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

/--
Given a surjective map `f` from a finite set `s` to another finite set `t`, if `s` is no larger
than `t`, then `f` is injective when restricted to `s`.
See `Finset.inj_on_of_surj_on_of_card_le` for the version where `f` is a dependent function.
-/
/-
**Finset.injOn_of_surjOn_of_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：injOn_of_surjOn_of_card_le (f : α -> β) (hf : Set.MapsTo f s t) (hsurj : S
et.SurjOn f s t) (hst : #s <= #t) : Set.InjOn f s
参数：f : α -> β；hf : Set.MapsTo f s t；hsurj : Set.SurjOn f s t；hst : #s <= #t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.SurjOn.image_eq_of_mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β}, Set.SurjOn f s t → Set.MapsTo f s t → f '' s = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_iff`：card_image_iff [DecidableEq β] : #(s.image f) = #
s ↔ Set.InjOn f s

--- 原说明 ---
Given a surjective map `f` from a finite set `s` to another finite set `t`, if `
s` is no larger
than `t`, then `f` is injective when restricted to `s`.
See `Finset.inj_on_of_surj_on_of_card_le` for the version where `f` is a depende
nt function.
-/
lemma injOn_of_surjOn_of_card_le (f : α → β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
    (hst : #s ≤ #t) : Set.InjOn f s := by
  classical
  have : s.image f = t := Finset.coe_injective <| by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) ≤ #s := card_image_le
  rw [← card_image_iff]
  lia

/--
Given a surjective map `f` defined on a finite set `s` to another finite set `t`, if `s` is no
larger than `t`, then `f` is injective when restricted to `s`.
See `Finset.injOn_of_surjOn_of_card_le` for the version where `f` is a non-dependent function.
-/
/-
**Finset.inj_on_of_surj_on_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inj_on_of_surj_on_of_card_le (f : forall a in s, β) (hf : forall a ha, f a
 ha in t) (hsurj : forall b in t, exists a ha, f a ha = b) (hst : #s <= #t) ⦃a₁⦄
 (ha₁ : a₁ in s) ⦃a₂⦄ (ha₂ : a₂ in s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂
参数：f : forall a in s, β；hf : forall a ha, f a ha in t；hsurj : forall b in t, exi
sts a ha, f a ha = b；hst : #s <= #t；ha₁ : a₁ in s；ha₂ : a₂ in s；ha₁a₂ : f a₁ ha₁
 = f a₂ ha₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `Finset.injOn_of_surjOn_of_card_le`：injOn_of_surjOn_of_card_le (f : α -> 
β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t) (hst : #s <= #t) : Set.Inj
On f s
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Given a surjective map `f` defined on a finite set `s` to another finite set `t`
, if `s` is no
larger than `t`, then `f` is injective when restricted to `s`.
See `Finset.injOn_of_surjOn_of_card_le` for the version where `f` is a non-depen
dent function.
-/
theorem inj_on_of_surj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, f a ha = b) (hst : #s ≤ #t) ⦃a₁⦄ (ha₁ : a₁ ∈ s) ⦃a₂⦄
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ := by
  let f' : s → β := fun a ↦ f a a.2
  have hsurj' : Set.SurjOn f' s.attach t := fun x hx ↦ by simpa [f'] using hsurj x hx
  have hinj' := injOn_of_surjOn_of_card_le f' (fun x hx ↦ hf _ _) hsurj' (by simpa)
  exact congrArg Subtype.val (@hinj' ⟨a₁, ha₁⟩ (by simp) ⟨a₂, ha₂⟩ (by simp) ha₁a₂)
/-
**Finset.image_eq_iff_bijOn_of_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_eq_iff_bijOn_of_card [DecidableEq β] (h : #s <= #t) : s.image f = t 
↔ Set.BijOn f s t
参数：h : #s <= #t。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_eq_iff_bijOn_of_card [DecidableEq β] (h : #s ≤ #t) :
    s.image f = t ↔ Set.BijOn f s t := by
  grind [injOn_of_surjOn_of_card_le, Set.BijOn, image_eq_iff_surjOn_mapsTo]

end bij

@[simp, grind =]
/-
**Finset.card_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_disjUnion (s t : Finset α) (h) : #(s.disjUnion t h) = #s + #t
参数：s t : Finset α；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t
-/
theorem card_disjUnion (s t : Finset α) (h) : #(s.disjUnion t h) = #s + #t :=
  Multiset.card_add _ _

/-! ### Lattice structure -/

-- This pattern is unreasonable to use generally, but it's convenient in this file.
-- (Note that we've already turned it on earlier in this file, but need to redo it now.)
local grind_pattern card_le_card => #s, #t

section Lattice

variable [DecidableEq α]

/-
**Finset.card_union_add_card_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_union_add_card_inter (s t : Finset α) : #(s union t) + #(s inter t) =
 #s + #t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.union_empty`：union_empty (s : Finset α) : s union ∅ = s
· 使用定理 `Finset.inter_empty`：inter_empty (s : Finset α) : s inter ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_union_add_card_inter (s t : Finset α) :
    #(s ∪ t) + #(s ∩ t) = #s + #t :=
  Finset.induction_on t (by simp) (by grind)

grind_pattern card_union_add_card_inter => #(s ∪ t), s ∩ t
grind_pattern card_union_add_card_inter => s ∪ t, #(s ∩ t)
grind_pattern card_union_add_card_inter => #(s ∪ t), #s
grind_pattern card_union_add_card_inter => #(s ∪ t), #t
grind_pattern card_union_add_card_inter => #(s ∩ t), #s
grind_pattern card_union_add_card_inter => #(s ∩ t), #t
/-
**Finset.card_inter_add_card_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_inter_add_card_union (s t : Finset α) : #(s inter t) + #(s union t) =
 #s + #t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_inter_add_card_union (s t : Finset α) :
    #(s ∩ t) + #(s ∪ t) = #s + #t := by grind
/-
**Finset.card_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_union (s t : Finset α) : #(s union t) = #s + #t - #(s inter t)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_union (s t : Finset α) : #(s ∪ t) = #s + #t - #(s ∩ t) := by grind
/-
**Finset.card_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_inter (s t : Finset α) : #(s inter t) = #s + #t - #(s union t)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_inter (s t : Finset α) : #(s ∩ t) = #s + #t - #(s ∪ t) := by grind
/-
**Finset.card_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_union_le (s t : Finset α) : #(s union t) <= #s + #t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_union_le (s t : Finset α) : #(s ∪ t) ≤ #s + #t := by grind
/-
**Finset.card_union_eq_card_add_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_union_eq_card_add_card : #(s union t) = #s + #t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma card_union_eq_card_add_card : #(s ∪ t) = #s + #t ↔ Disjoint s t := by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card

@[grind =]
/-
**Finset.card_sdiff_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_of_subset (h : s subseteq t) : #(t \ s) = #t - #s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
-/
theorem card_sdiff_of_subset (h : s ⊆ t) : #(t \ s) = #t - #s := by
  suffices #(t \ s) = #(t \ s ∪ s) - #s by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint, Nat.add_sub_cancel_right]

@[grind =]
/-
**Finset.card_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sdiff : #(t \ s) = #t - #(s inter t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
-/
theorem card_sdiff : #(t \ s) = #t - #(s ∩ t) := by
  rw [← card_sdiff_of_subset] <;> grind
/-
**Finset.card_sdiff_add_card_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_add_card_eq_card (h : s subseteq t) : #(t \ s) + #s = #t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_sdiff_add_card_eq_card (h : s ⊆ t) : #(t \ s) + #s = #t := by grind
/-
**Finset.card_sub_card_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_sub_card_eq (s t : Finset α) : #t - #s = #(t \ s) - #(s \ t)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_sub_card_eq (s t : Finset α) : #t - #s = #(t \ s) - #(s \ t) :=
  calc
    #t - #s = #t - #(s ∩ t) - #(s \ t) := by grind
    _ = #(t \ (s ∩ t)) - #(s \ t) := by grind
    _ = #(t \ s) - #(s \ t) := by grind
/-
**Finset.le_card_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_card_sdiff (s t : Finset α) : #t - #s <= #(t \ s)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_card_sdiff (s t : Finset α) : #t - #s ≤ #(t \ s) := by grind

grind_pattern le_card_sdiff => #(t \ s), #t
grind_pattern le_card_sdiff => #(t \ s), #s
/-
**Finset.card_le_card_sdiff_add_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_sdiff_add_card : #s <= #(s \ t) + #t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_le_card_sdiff_add_card : #s ≤ #(s \ t) + #t := by grind
/-
**Finset.card_sdiff_add_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_add_card (s t : Finset α) : #(s \ t) + #t = #(s union t)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `Finset.sdiff_union_self_eq_union`：sdiff_union_self_eq_union : s \ t unio
n t = s union t
-/
theorem card_sdiff_add_card (s t : Finset α) : #(s \ t) + #t = #(s ∪ t) := by
  rw [← card_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]
/-
**Finset.sdiff_nonempty_of_card_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_nonempty_of_card_lt_card (h : #s < #t) : (t \ s).Nonempty
参数：h : #s < #t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_nonempty_of_card_lt_card (h : #s < #t) : (t \ s).Nonempty := by
  grind

omit [DecidableEq α] in
/-
**Finset.exists_mem_notMem_of_card_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_mem_notMem_of_card_lt_card (h : #s < #t) : exists e, e in t ∧ e ∉ s
参数：h : #s < #t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sdiff_nonempty_of_card_lt_card`：sdiff_nonempty_of_card_lt_card (h
 : #s < #t) : (t \ s).Nonempty
-/
theorem exists_mem_notMem_of_card_lt_card (h : #s < #t) : ∃ e, e ∈ t ∧ e ∉ s := by
  classical simpa [Finset.Nonempty] using sdiff_nonempty_of_card_lt_card h

@[simp]
/-
**Finset.card_sdiff_add_card_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_add_card_inter (s t : Finset α) : #(s \ t) + #(s inter t) = #s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.disjoint_sdiff_inter`：disjoint_sdiff_inter (s t : Finset α) : Dis
joint (s \ t) (s inter t)
· 使用定理 `Finset.sdiff_union_inter`：sdiff_union_inter (s t : Finset α) : s \ t uni
on s inter t = s
-/
lemma card_sdiff_add_card_inter (s t : Finset α) :
    #(s \ t) + #(s ∩ t) = #s := by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

grind_pattern card_sdiff_add_card_inter => #(s \ t), #(s ∩ t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s

@[simp]
/-
**Finset.card_inter_add_card_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_inter_add_card_sdiff (s t : Finset α) : #(s inter t) + #(s \ t) = #s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_inter_add_card_sdiff (s t : Finset α) :
    #(s ∩ t) + #(s \ t) = #s := by grind
/-
**Finset.card_sdiff_le_card_sdiff_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_le_card_sdiff_iff : #(s \ t) <= #(t \ s) ↔ #s <= #t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_sdiff_le_card_sdiff_iff : #(s \ t) ≤ #(t \ s) ↔ #s ≤ #t := by grind
/-
**Finset.card_sdiff_lt_card_sdiff_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_lt_card_sdiff_iff : #(s \ t) < #(t \ s) ↔ #s < #t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_sdiff_lt_card_sdiff_iff : #(s \ t) < #(t \ s) ↔ #s < #t := by grind
/-
**Finset.card_sdiff_eq_card_sdiff_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_sdiff_eq_card_sdiff_iff : #(s \ t) = #(t \ s) ↔ #s = #t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_sdiff_eq_card_sdiff_iff : #(s \ t) = #(t \ s) ↔ #s = #t := by grind

alias ⟨_, card_sdiff_comm⟩ := card_sdiff_eq_card_sdiff_iff

/-- **Pigeonhole principle** for two finsets inside an ambient finset. -/
/-
**Finset.inter_nonempty_of_card_lt_card_add_card** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：inter_nonempty_of_card_lt_card_add_card (hts : t subseteq s) (hus : u subs
eteq s) (hstu : #s < #t + #u) : (t inter u).Nonempty
参数：hts : t subseteq s；hus : u subseteq s；hstu : #s < #t + #u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u

--- 原说明 ---
**Pigeonhole principle** for two finsets inside an ambient finset.
-/
theorem inter_nonempty_of_card_lt_card_add_card (hts : t ⊆ s) (hus : u ⊆ s)
    (hstu : #s < #t + #u) : (t ∩ u).Nonempty := by
  contrapose! hstu
  calc
    _ = #(t ∪ u) := by simp [← card_union_add_card_inter, hstu]
    _ ≤ #s := by gcongr; exact union_subset hts hus

end Lattice

/-
**Finset.card_filter_add_card_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_filter_add_card_filter_not (p : α -> Prop) [DecidablePred p] [forall 
x, Decidable (¬p x)] : #(s.filter p) + #(s.filter fun a => ¬ p a) = #s
参数：p : α -> Prop；¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.disjoint_filter_filter_not`：disjoint_filter_filter_not (s t : Fin
set α) (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : Disjoint
 (s.filter p) (t.filter…
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
-/
theorem card_filter_add_card_filter_not
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    #(s.filter p) + #(s.filter fun a ↦ ¬ p a) = #s := by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_not _ _ _), filter_union_filter_not_eq]

/-- Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively, there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`. -/
/-
**Finset.exists_subsuperset_card_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_subsuperset_card_eq (hst : s subseteq t) (hsn : #s <= n) (hnt : n <
= #t) : exists u, s subseteq u ∧ u subseteq t ∧ #u = n
参数：hst : s subseteq t；hsn : #s <= n；hnt : n <= #t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively,
 there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`.
-/
lemma exists_subsuperset_card_eq (hst : s ⊆ t) (hsn : #s ≤ n) (hnt : n ≤ #t) :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ #u = n := by
  classical
  refine Nat.decreasingInduction' ?_ hnt ⟨t, by simp [hst]⟩
  intro k _ hnk ⟨u, hu₁, hu₂, hu₃⟩
  obtain ⟨a, ha⟩ : (u \ s).Nonempty := by grind
  exact ⟨u.erase a, by grind⟩

/-- We can shrink a set to any smaller size. -/
/-
**Finset.exists_subset_card_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_subset_card_eq (hns : n <= #s) : exists t subseteq s, #t = n
参数：hns : n <= #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Finset.exists_subsuperset_card_eq`：exists_subsuperset_card_eq (hst : s s
ubseteq t) (hsn : #s <= n) (hnt : n <= #t) : exists u, s subseteq u ∧ u subseteq
 t ∧ #u = n
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
We can shrink a set to any smaller size.
-/
lemma exists_subset_card_eq (hns : n ≤ #s) : ∃ t ⊆ s, #t = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns
/-
**Finset.le_card_iff_exists_subset_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_card_iff_exists_subset_card : n <= #s ↔ exists t subseteq s, #t = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
-/
theorem le_card_iff_exists_subset_card : n ≤ #s ↔ ∃ t ⊆ s, #t = n := by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_subset_card_eq h
/-
**Finset.exists_subset_or_subset_of_two_mul_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `F
inset`。
形式化陈述：exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α
} {n : Nat} (hXY : 2 * n < #(X union Y)) : exists C : Finset α, n < #C ∧ (C subs
eteq X ∨ C subseteq Y)
参数：hXY : 2 * n < #(X union Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) : ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    finish

/-! ### Explicit description of a finset from its card -/


/-
**Finset.card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_one : #s = 1 ↔ exists a, s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### Explicit description of a finset from its card
-/
theorem card_eq_one : #s = 1 ↔ ∃ a, s = {a} := by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]
/-
**Finset.card_eq_one_iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_one_iff_existsUnique : #s = 1 ↔ exists! a, a in s
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
theorem card_eq_one_iff_existsUnique : #s = 1 ↔ ∃! a, a ∈ s := by
  simp [card_eq_one, Finset.singleton_iff_unique_mem]
/-
**Finset.exists_eq_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_eq_insert_iff [DecidableEq α] : (exists a ∉ s, insert a s = t) ↔ s 
subseteq t ∧ #s + 1 = #t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
-/
theorem exists_eq_insert_iff [DecidableEq α] :
    (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ #s + 1 = #t := by
  constructor
  · grind
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} := card_eq_one.mp (by grind)
    grind =>
      have : a ∈ t \ s
      have h : insert a s ⊆ t
      have := eq_of_subset_of_card_le h
      instantiate
/-
**Finset.card_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_one : #s <= 1 ↔ forall a in s, forall b in s, a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
-/
theorem card_le_one : #s ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).ge_iff_eq'.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · grind
  · exact fun h => ⟨x, by grind⟩
/-
**Finset.card_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s -> b in s -> a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_le_one_iff : #s ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  grind [card_le_one]
/-
**Finset.card_le_one_iff_subsingleton_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_one_iff_subsingleton_coe : #s <= 1 ↔ Subsingleton (s : Type _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
-/
theorem card_le_one_iff_subsingleton_coe : #s ≤ 1 ↔ Subsingleton (s : Type _) :=
  card_le_one.trans (s : Set α).subsingleton_coe.symm

/-- A finset has cardinality at most 1 iff its underlying set is subsingleton. -/
/-
**Finset.card_le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_one_iff_subsingleton : #s <= 1 ↔ (s : Set α).Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_le_one_iff_subsingleton_coe`：card_le_one_iff_subsingleton_co
e : #s <= 1 ↔ Subsingleton (s : Type _)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `SetLike.coe_sort_coe`：coe_sort_coe : ((p : Set B) : Type _) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finset has cardinality at most 1 iff its underlying set is subsingleton.
-/
theorem card_le_one_iff_subsingleton : #s ≤ 1 ↔ (s : Set α).Subsingleton := by
  rw [card_le_one_iff_subsingleton_coe, ← Set.subsingleton_coe, SetLike.coe_sort_coe]
/-
**Finset.card_le_one_iff_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_one_iff_subset_singleton [Nonempty α] : #s <= 1 ↔ exists x : α, s 
subseteq {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
-/
theorem card_le_one_iff_subset_singleton [Nonempty α] : #s ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  refine ⟨fun H => ?_, ?_⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_card hx
/-
**Finset.exists_mem_ne** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in s, b != a
参数：hs : 1 < #s；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_le_one_iff_subset_singleton`：card_le_one_iff_subset_singleto
n [Nonempty α] : #s <= 1 ↔ exists x : α, s subseteq {x}
· 使用定理 `Finset.subset_singleton_iff'`：subset_singleton_iff' {s : Finset α} {a : 
α} : s subseteq {a} ↔ forall b in s, b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma exists_mem_ne (hs : 1 < #s) (a : α) : ∃ b ∈ s, b ≠ a := by
  have : Nonempty α := ⟨a⟩
  by_contra!
  exact hs.not_ge (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)

/-- A `Finset` of a subsingleton type has cardinality at most one. -/
/-
**Finset.card_le_one_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : #s <= 1
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_le_one_iff`：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s
 -> b in s -> a = b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
A `Finset` of a subsingleton type has cardinality at most one.
-/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : #s ≤ 1 :=
  Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _
/-
**Finset.one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_lt_card : 1 < #s ↔ exists a in s, exists b in s, a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
-/
theorem one_lt_card : 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  contrapose!; exact card_le_one
/-
**Finset.one_lt_card_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_lt_card_iff : 1 < #s ↔ exists a b, a in s ∧ b in s ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.one_lt_card`：one_lt_card : 1 < #s ↔ exists a in s, exists b in s,
 a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_card_iff : 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_card]
  simp only [exists_and_left]
/-
**Finset.one_lt_card_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_lt_card_iff_nontrivial : 1 < #s ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Finset.Nontrivial.eq_1`：∀ {α : Type u_1} (s : Finset α), s.Nontrivial = 
(↑s).Nontrivial
· 使用定理 `Set.nontrivial_coe_sort`：nontrivial_coe_sort {s : Set α} : Nontrivial s 
↔ s.Nontrivial
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Finset.card_le_one_iff_subsingleton_coe`：card_le_one_iff_subsingleton_co
e : #s <= 1 ↔ Subsingleton (s : Type _)
· 使用定理 `Finset.coe_sort_coe`：coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _
) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_lt_card_iff_nontrivial : 1 < #s ↔ s.Nontrivial := by
  rw [← not_iff_not, not_lt, Finset.Nontrivial, ← Set.nontrivial_coe_sort,
    not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton_coe, coe_sort_coe]

/-- Given an injective map `f : α → β` for finite sets `s ⊂ α` and `t ⊂ β` such that `t` has
    cardinality one more than `s`, there exists a unique element of `t` not in `f(s)`. -/
/-
**Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one** 是 Mathlib 中的一个定
理，位于命名空间 `Finset`。
形式化陈述：existsUnique_notMem_image_of_injOn_of_card_eq_add_one {t : Finset β} [Deci
dableEq β] (hf : Set.InjOn f s) (hf' : Set.MapsTo f s t) (h : #t = #s + 1) : exi
sts! x, x in t ∧ x ∉ s.image f
参数：hf : Set.InjOn f s；hf' : Set.MapsTo f s t；h : #t = #s + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Given an injective map `f : α → β` for finite sets `s ⊂ α` and `t ⊂ β` such that
 `t` has
    cardinality one more than `s`, there exists a unique element of `t` not in `
f(s)`.
-/
theorem existsUnique_notMem_image_of_injOn_of_card_eq_add_one
    {t : Finset β} [DecidableEq β]
    (hf : Set.InjOn f s) (hf' : Set.MapsTo f s t) (h : #t = #s + 1) :
    ∃! x, x ∈ t ∧ x ∉ s.image f := by
  have : #(t \ s.image f) = 1 := by
    grind [card_sdiff_of_subset hf'.finsetImage_subset, card_image_of_injOn hf]
  simpa [card_eq_one_iff_existsUnique] using this

/-- If a Finset in a Pi type is nontrivial (has at least two elements), then
  its projection to some factor is nontrivial, and the fibers of the projection
  are proper subsets. -/
/-
**Finset.exists_of_one_lt_card_pi** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_of_one_lt_card_pi {ι : Type*} {α : ι -> Type*} [forall i, Decidable
Eq (α i)] {s : Finset (forall i, α i)} (h : 1 < #s) : exists i, 1 < #(s.image (·
 i)) ∧ forall ai, s.filter (· i = ai) ⊂ s
参数：α i；forall i, α i；h : 1 < #s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.filter_ssubset`：∀ {α : Type u_1} {p : α → Prop} [inst : Decidable
Pred p] {s : Finset α}, Finset.filter p s ⊂ s ↔ ∃ x ∈ s, ¬p x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y

--- 原说明 ---
If a Finset in a Pi type is nontrivial (has at least two elements), then
  its projection to some factor is nontrivial, and the fibers of the projection
  are proper subsets.
-/
lemma exists_of_one_lt_card_pi {ι : Type*} {α : ι → Type*} [∀ i, DecidableEq (α i)]
    {s : Finset (∀ i, α i)} (h : 1 < #s) :
    ∃ i, 1 < #(s.image (· i)) ∧ ∀ ai, s.filter (· i = ai) ⊂ s := by
  simp_rw [one_lt_card_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]
/-
**Finset.card_eq_succ_iff_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_succ_iff_cons : #s = n + 1 ↔ exists a t, exists (h : a ∉ t), cons 
a t h = s ∧ #t = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_eq_succ_iff_cons :
    #s = n + 1 ↔ ∃ a t, ∃ (h : a ∉ t), cons a t h = s ∧ #t = n :=
  ⟨cons_induction_on s (by simp) fun a s _ _ _ => ⟨a, s, by simp_all⟩,
   fun ⟨a, t, _, hs, _⟩ => by simpa [← hs]⟩

section DecidableEq
variable [DecidableEq α]

/-
**Finset.card_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ insert a t = s ∧ #t = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
-/
theorem card_eq_succ : #s = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ #t = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < #s)
    ⟨a, s.erase a, s.notMem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨_, _, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_notMem hat⟩
/-
**Finset.card_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_two : #s = 2 ↔ exists x y, x != y ∧ s = {x, y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_succ`：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ ins
ert a t = s ∧ #t = n
-/
theorem card_eq_two : #s = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_one]
  · grind
/-
**Finset.card_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_three : #s = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, 
y, z}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_succ`：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ ins
ert a t = s ∧ #t = n
-/
theorem card_eq_three : #s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_two]
  · grind
/-
**Finset.card_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_four : #s = 4 ↔ exists x y z w, x != y ∧ x != z ∧ x != w ∧ y != z 
∧ y != w ∧ z != w ∧ s = {x, y, z, w}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_succ`：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ ins
ert a t = s ∧ #t = n
-/
theorem card_eq_four : #s = 4 ↔
    ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ s = {x, y, z, w} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_three]
  · grind

end DecidableEq

/-
**Finset.two_lt_card_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：two_lt_card_iff : 2 < #s ↔ exists a b c, a in s ∧ b in s ∧ c in s ∧ a != b
 ∧ a != c ∧ b != c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem two_lt_card_iff : 2 < #s ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_three,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, t, hsub, hab, hac, hbc, rfl⟩
      exact ⟨a, b, c, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, {a, b, c}, by simp_all [insert_subset_iff]⟩
/-
**Finset.two_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：two_lt_card : 2 < #s ↔ exists a in s, exists b in s, exists c in s, a != b
 ∧ a != c ∧ b != c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem two_lt_card : 2 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [two_lt_card_iff, exists_and_left]
/-
**Finset.three_lt_card_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：three_lt_card_iff : 3 < #s ↔ exists a b c d, a in s ∧ b in s ∧ c in s ∧ d 
in s ∧ a != b ∧ a != c ∧ a != d ∧ b != c ∧ b != d ∧ c != d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem three_lt_card_iff : 3 < #s ↔
    ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_four,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, d, t, hsub, hab, hac, had, hbc, hbd, hcd, rfl⟩
      exact ⟨a, b, c, d, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
      exact ⟨a, b, c, d, {a, b, c, d}, by simp_all [insert_subset_iff]⟩
/-
**Finset.three_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：three_lt_card : 3 < #s ↔ exists a in s, exists b in s, exists c in s, exis
ts d in s, a != b ∧ a != c ∧ a != d ∧ b != c ∧ b != d ∧ c != d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem three_lt_card : 3 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp_rw [three_lt_card_iff, exists_and_left]

/-! ### Inductions -/


/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
/-
**Finset.strongInduction** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：strongInduction {p : Finset α -> Sort*} (H : forall s, (forall t ⊂ s, p t)
 -> p s) : forall s : Finset α, p s | s => H s fun t h => have : #t < #s
参数：H : forall s, (forall t ⊂ s, p t) -> p s。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card

--- 原说明 ---
Suppose that, given objects defined on all strict subsets of any finset `s`, one
 knows how to
define an object on `s`. Then one can inductively define an object on all finset
s, starting from
the empty set and iterating. This can be used either to define data, or to prove
 properties.
-/
def strongInduction {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
    ∀ s : Finset α, p s
  | s =>
    H s fun t h =>
      have : #t < #s := card_lt_card h
      strongInduction H t
  termination_by s => #s
/-
**Finset.strongInduction_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：strongInduction_eq {p : Finset α -> Sort*} (H : forall s, (forall t ⊂ s, p
 t) -> p s) (s : Finset α) : strongInduction H s = H s fun t _ => strongInductio
n H t
参数：H : forall s, (forall t ⊂ s, p t) -> p s；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.strongInduction.eq_1`：∀ {α : Type u_1} {p : Finset α → Sort u_4} 
(H : (s : Finset α) → ((t : Finset α) → t ⊂ s → p t) → p s) (x : Finset α),   Fi
nset.strongInduct…
-/
theorem strongInduction_eq {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s)
    (s : Finset α) : strongInduction H s = H s fun t _ => strongInduction H t := by
  rw [strongInduction]

/-- Analogue of `strongInduction` with order of arguments swapped. -/
@[elab_as_elim]
/-
**Finset.strongInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：strongInductionOn {p : Finset α -> Sort*} (s : Finset α) : (forall s, (for
all t ⊂ s, p t) -> p s) -> p s
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogue of `strongInduction` with order of arguments swapped.
-/
def strongInductionOn {p : Finset α → Sort*} (s : Finset α) :
    (∀ s, (∀ t ⊂ s, p t) → p s) → p s := fun H => strongInduction H s
/-
**Finset.strongInductionOn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：strongInductionOn_eq {p : Finset α -> Sort*} (s : Finset α) (H : forall s,
 (forall t ⊂ s, p t) -> p s) : s.strongInductionOn H = H s fun t _ => t.strongIn
ductionOn H
参数：s : Finset α；H : forall s, (forall t ⊂ s, p t) -> p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.strongInduction.eq_1`：∀ {α : Type u_1} {p : Finset α → Sort u_4} 
(H : (s : Finset α) → ((t : Finset α) → t ⊂ s → p t) → p s) (x : Finset α),   Fi
nset.strongInduct…
-/
theorem strongInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
    s.strongInductionOn H = H s fun t _ => t.strongInductionOn H := by
  dsimp only [strongInductionOn]
  rw [strongInduction]

@[elab_as_elim]
/-
**Finset.case_strong_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：case_strong_induction_on [DecidableEq α] {p : Finset α -> Prop} (s : Finse
t α) (h₀ : p ∅) (h₁ : forall a s, a ∉ s -> (forall t subseteq s, p t) -> p (inse
rt a s)) : p s
参数：s : Finset α；h₀ : p ∅；h₁ : forall a s, a ∉ s -> (forall t subseteq s, p t) ->
 p (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Finset.ssubset_insert`：ssubset_insert (h : a ∉ s) : s ⊂ insert a s
-/
theorem case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ t ⊆ s, p t) → p (insert a s)) : p s :=
  Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

/-- Suppose that, given objects defined on all nonempty strict subsets of any nontrivial finset `s`,
one knows how to define an object on `s`. Then one can inductively define an object on all finsets,
starting from singletons and iterating.

TODO: Currently this can only be used to prove properties.
Replace `Finset.Nonempty.exists_eq_singleton_or_nontrivial` with computational content
in order to let `p` be `Sort`-valued. -/
@[elab_as_elim]
/-
**Finset.Nonempty.strong_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {p : (s : Finset α) → s.Nonempty → Prop},   (∀ (a : α), p
 {a} ⋯) →     (∀ ⦃s : Finset α⦄ (hs : s.Nontrivial), (∀ (t : Finset α) (ht : t.N
onempty), t ⊂ s → p t ht) → p s ⋯) →       ∀ ⦃s : Finset α⦄ (hs : s.Nonempty), p
 s hs
参数：s : Finset α；∀ (a : α), p {a} ⋯；∀ ⦃s : Finset α⦄ (hs : s.Nontrivial), (∀ (t :
 Finset α) (ht : t.Nonempty), t ⊂ s → p t ht) → p s ⋯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Finset.Nontrivial.nonempty`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivia
l → s.Nonempty
· 使用定理 `Finset.Nonempty.strong_induction._unary`：∀ {α : Type u_1} {p : (s : Fins
et α) → s.Nonempty → Prop},   (∀ (a : α), p {a} ⋯) →     (∀ ⦃s : Finset α⦄ (hs :
 s.Nontrivial), (∀ (t : Finse…

--- 原说明 ---
Suppose that, given objects defined on all nonempty strict subsets of any nontri
vial finset `s`,
one knows how to define an object on `s`. Then one can inductively define an obj
ect on all finsets,
starting from singletons and iterating.

TODO: Currently this can only be used to prove properties.
Replace `Finset.Nonempty.exists_eq_singleton_or_nontrivial` with computational c
ontent
in order to let `p` be `Sort`-valued.
-/
protected lemma Nonempty.strong_induction {p : ∀ s, s.Nonempty → Prop}
    (h₀ : ∀ a, p {a} (singleton_nonempty _))
    (h₁ : ∀ ⦃s⦄ (hs : s.Nontrivial), (∀ t ht, t ⊂ s → p t ht) → p s hs.nonempty) :
    ∀ ⦃s : Finset α⦄ (hs), p s hs
  | s, hs => by
    obtain ⟨a, rfl⟩ | hs := hs.exists_eq_singleton_or_nontrivial
    · exact h₀ _
    · refine h₁ hs fun t ht hts ↦ ?_
      have := card_lt_card hts
      exact ht.strong_induction h₀ h₁
termination_by s => #s

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
/-
**Finset.strongDownwardInduction** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：strongDownwardInduction {p : Finset α -> Sort*} {n : Nat} (H : forall t₁, 
(forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁) : for
all s : Finset α, #s <= n -> p s | s => H s fun {t} ht h => have
参数：H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <
= n -> p t₁。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card

--- 原说明 ---
Suppose that, given that `p t` can be defined on all supersets of `s` of cardina
lity less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for al
l finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties.
-/
def strongDownwardInduction {p : Finset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    ∀ s : Finset α, #s ≤ n → p s
  | s =>
    H s fun {t} ht h =>
      have := Finset.card_lt_card h
      have : n - #t < n - #s := by lia
      strongDownwardInduction H t ht
  termination_by s => n - #s
/-
**Finset.strongDownwardInduction_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：strongDownwardInduction_eq {p : Finset α -> Sort*} (H : forall t₁, (forall
 {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁) (s : Finset 
α) : strongDownwardInduction H s = H s fun {t} ht _ => strongDownwardInduction H
 t ht
参数：H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <
= n -> p t₁；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.strongDownwardInduction.eq_1`：∀ {α : Type u_1} {p : Finset α → So
rt u_4} {n : ℕ}   (H : (t₁ : Finset α) → ({t₂ : Finset α} → t₂.card ≤ n → t₁ ⊂ t
₂ → p t₂) → t₁.card ≤ n →…
-/
theorem strongDownwardInduction_eq {p : Finset α → Sort*}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁)
    (s : Finset α) :
    strongDownwardInduction H s = H s fun {t} ht _ => strongDownwardInduction H t ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
/-
**Finset.strongDownwardInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：strongDownwardInductionOn {p : Finset α -> Sort*} (s : Finset α) (H : fora
ll t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁
) : #s <= n -> p s
参数：s : Finset α；H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p
 t₂) -> #t₁ <= n -> p t₁。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogue of `strongDownwardInduction` with order of arguments swapped.
-/
def strongDownwardInductionOn {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    #s ≤ n → p s :=
  strongDownwardInduction H s
/-
**Finset.strongDownwardInductionOn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：strongDownwardInductionOn_eq {p : Finset α -> Sort*} (s : Finset α) (H : f
orall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p
 t₁) : s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInduc
tionOn H ht
参数：s : Finset α；H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p
 t₂) -> #t₁ <= n -> p t₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.strongDownwardInduction.eq_1`：∀ {α : Type u_1} {p : Finset α → So
rt u_4} {n : ℕ}   (H : (t₁ : Finset α) → ({t₂ : Finset α} → t₂.card ≤ n → t₁ ⊂ t
₂ → p t₂) → t₁.card ≤ n →…
-/
theorem strongDownwardInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]
/-
**Finset.lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lt_wf {α} : WellFounded (@LT.lt (Finset α) _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
-/
theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
  Subrelation.wf H <| InvImage.wf _ <| (Nat.lt_wfRel).2

/--
To prove a proposition for an arbitrary `Finset α`,
it suffices to prove that for any `S : Finset α`, the following is true:
the property is true for S with any element `s` removed, then the property holds for `S`.

This is a weaker version of `Finset.strongInduction`.
But it can be more precise when the induction argument
only requires removing single elements at a time.
-/
/-
**Finset.eraseInduction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseInduction [DecidableEq α] {p : Finset α -> Prop} (H : (S : Finset α) 
-> (forall s in S, p (S.erase s)) -> p S) (S : Finset α) : p S
参数：H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S；S : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.erase_ssubset`：erase_ssubset {a : α} {s : Finset α} (h : a in s) 
: s.erase a ⊂ s

--- 原说明 ---
To prove a proposition for an arbitrary `Finset α`,
it suffices to prove that for any `S : Finset α`, the following is true:
the property is true for S with any element `s` removed, then the property holds
 for `S`.

This is a weaker version of `Finset.strongInduction`.
But it can be more precise when the induction argument
only requires removing single elements at a time.
-/
theorem eraseInduction [DecidableEq α] {p : Finset α → Prop}
    (H : (S : Finset α) → (∀ s ∈ S, p (S.erase s)) → p S) (S : Finset α) : p S :=
  S.strongInduction fun S ih => H S fun _ hs => ih _ (erase_ssubset hs)

/--
Given a function `f` which sends the finite set `s` to itself, the sequence of images of `s` under
iterates of `f` is eventually constant. Furthermore, the sequence of images stabilises in fewer
than `#s` steps.
-/
/-
**Finset.image_iterate_stabilises_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_iterate_stabilises_lt_card [DecidableEq α] {f : α -> α} {s : Finset 
α} (hs : Set.MapsTo f s s) (hs₀ : s.Nonempty) : exists n < #s, forall m, n <= m 
-> s.image f^[m] = s.image f^[n]
参数：hs : Set.MapsTo f s s；hs₀ : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.image_subset_image`：image_subset_image {s₁ s₂ : Finset α} (h : s₁
 subseteq s₂) : s₁.image f subseteq s₂.image f
· 使用定理 `Set.MapsTo.finsetImage_subset`：∀ {α : Type u_1} {β : Type u_2} [inst : D
ecidableEq β] {f : α → β} {s : Finset α} {t : Finset β},   Set.MapsTo f ↑s ↑t → 
Finset.image f s ⊆ …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Nat.sub_le_sub_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n - k ≤ m - k
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `Nat.stabilises_of_antitone`：Nat.stabilises_of_antitone {f : Nat -> Nat} 
(hfmono : Antitone f) (hfstab : forall m, f m = f (m + 1) -> f (m + 1) = f (m + 
2)) : exists n <…

--- 原说明 ---
Given a function `f` which sends the finite set `s` to itself, the sequence of i
mages of `s` under
iterates of `f` is eventually constant. Furthermore, the sequence of images stab
ilises in fewer
than `#s` steps.
-/
theorem image_iterate_stabilises_lt_card [DecidableEq α] {f : α → α} {s : Finset α}
    (hs : Set.MapsTo f s s) (hs₀ : s.Nonempty) :
    ∃ n < #s, ∀ m, n ≤ m → s.image f^[m] = s.image f^[n] := by
  let g (i : ℕ) : Finset α := s.image f^[i]
  have (i : ℕ) : 0 < #(g i) := (hs₀.image _).card_pos
  have hg : Antitone g := antitone_nat_of_succ_le <| fun i ↦ by
    simp_rw [g, Function.iterate_succ, ← image_image]
    grw [hs.finsetImage_subset]
  have eq_iff (i j : ℕ) : #(g i) - 1 = #(g j) - 1 ↔ g i = g j := by
    wlog hij : j ≤ i generalizing i j
    · grind
    exact ⟨fun h ↦ eq_of_subset_of_card_le (hg hij) (by grind), by grind⟩
  have hG : Antitone (fun i ↦ #(g i) - 1) := fun i j h ↦ by dsimp; gcongr #?_ - 1; exact hg h
  rcases Nat.stabilises_of_antitone hG (by grind [=_ image_image, iterate_succ']) with ⟨n, hn, hn'⟩
  exact ⟨n, by grind⟩

/--
Given a function `f` which sends the finite set `s` to itself, the sequence of images of `s` under
iterates of `f` is eventually constant. Furthermore, the sequence of images stabilises in at most
`#s` steps.
-/
/-
**Finset.image_iterate_stabilises_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_iterate_stabilises_le_card [DecidableEq α] {f : α -> α} {s : Finset 
α} (hs : Set.MapsTo f s s) : exists n <= #s, forall m, n <= m -> s.image f^[m] =
 s.image f^[n]
参数：hs : Set.MapsTo f s s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_iterate_stabilises_lt_card`：image_iterate_stabilises_lt_car
d [DecidableEq α] {f : α -> α} {s : Finset α} (hs : Set.MapsTo f s s) (hs₀ : s.N
onempty) : exists n < #s, for…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Given a function `f` which sends the finite set `s` to itself, the sequence of i
mages of `s` under
iterates of `f` is eventually constant. Furthermore, the sequence of images stab
ilises in at most
`#s` steps.
-/
theorem image_iterate_stabilises_le_card [DecidableEq α] {f : α → α} {s : Finset α}
    (hs : Set.MapsTo f s s) :
    ∃ n ≤ #s, ∀ m, n ≤ m → s.image f^[m] = s.image f^[n] := by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain ⟨n, hn', hn⟩ := image_iterate_stabilises_lt_card hs hs₀
  exact ⟨n, hn'.le, hn⟩

end Finset

