/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.AddSub

/-!
# Repeating elements in multisets

## Main definitions

* `replicate n a` is the multiset containing only `a` with multiplicity `n`

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.replicate` -/

/-- `replicate n a` is the multiset containing only `a` with multiplicity `n`. -/
/-
**Multiset.replicate** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：replicate (n : Nat) (a : α) : Multiset α
参数：n : Nat；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`replicate n a` is the multiset containing only `a` with multiplicity `n`.
-/
def replicate (n : ℕ) (a : α) : Multiset α :=
  List.replicate n a
/-
**Multiset.coe_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_replicate (n : Nat) (a : α) : (List.replicate n a : Multiset α) = repl
icate n a
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_replicate (n : ℕ) (a : α) : (List.replicate n a : Multiset α) = replicate n a := rfl
/-
**Multiset.replicate_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (a : α), Multiset.replicate 0 a = 0
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem replicate_zero (a : α) : replicate 0 a = 0 := rfl
/-
**Multiset.replicate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (a : α) (n : ℕ), Multiset.replicate (n + 1) a = a ::ₘ Mul
tiset.replicate n a
参数：a : α；n : ℕ；n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem replicate_succ (a : α) (n) : replicate (n + 1) a = a ::ₘ replicate n a := rfl
/-
**Multiset.replicate_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_add (m n : Nat) (a : α) : replicate (m + n) a = replicate m a + 
replicate n a
参数：m n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.replicate_add`：replicate_add (m n) (a : α) : replicate (m + n) a = 
replicate m a ++ replicate n a
-/
theorem replicate_add (m n : ℕ) (a : α) : replicate (m + n) a = replicate m a + replicate n a :=
  congr_arg _ <| List.replicate_add ..
/-
**Multiset.replicate_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_one (a : α) : replicate 1 a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicate_one (a : α) : replicate 1 a = {a} := rfl
/-
**Multiset.card_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.replicate n a).card = n
参数：n : ℕ；a : α；Multiset.replicate n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
-/
@[simp] theorem card_replicate (n) (a : α) : card (replicate n a) = n :=
  length_replicate
/-
**Multiset.mem_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_replicate {a b : α} {n : Nat} : b in replicate n a ↔ n != 0 ∧ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.replica
te n a ↔ n ≠ 0 ∧ b = a
-/
theorem mem_replicate {a b : α} {n : ℕ} : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a :=
  List.mem_replicate
/-
**Multiset.eq_of_mem_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_of_mem_replicate {a b : α} {n} : b in replicate n a -> b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
-/
theorem eq_of_mem_replicate {a b : α} {n} : b ∈ replicate n a → b = a :=
  List.eq_of_mem_replicate
/-
**Multiset.eq_replicate_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_replicate_card {a : α} {s : Multiset α} : s = replicate (card s) a ↔ fo
rall b in s, b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `List.perm_replicate`：∀ {α : Type u_1} {n : ℕ} {a : α} {l : List α}, l.Pe
rm (List.replicate n a) ↔ l = List.replicate n a
· 使用定理 `List.eq_replicate_length`：∀ {α : Type u} {a : α} {l : List α}, l = List.
replicate l.length a ↔ ∀ b ∈ l, b = a
-/
theorem eq_replicate_card {a : α} {s : Multiset α} : s = replicate (card s) a ↔ ∀ b ∈ s, b = a :=
  Quot.inductionOn s fun _l => coe_eq_coe.trans <| perm_replicate.trans eq_replicate_length

alias ⟨_, eq_replicate_of_mem⟩ := eq_replicate_card
/-
**Multiset.eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_replicate {a : α} {n} {s : Multiset α} : s = replicate n a ↔ card s = n
 ∧ forall b in s, b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {s : Multiset α},
 (∀ b ∈ s, b = a) → s = Multiset.replicate s.card a
-/
theorem eq_replicate {a : α} {n} {s : Multiset α} :
    s = replicate n a ↔ card s = n ∧ ∀ b ∈ s, b = a :=
  ⟨fun h => h.symm ▸ ⟨card_replicate _ _, fun _b => eq_of_mem_replicate⟩,
    fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩
/-
**Multiset.replicate_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_right_injective {n : Nat} (hn : n != 0) : Injective (@replicate 
α n)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_replicate`：mem_replicate {a b : α} {n : Nat} : b in replica
te n a ↔ n != 0 ∧ b = a
-/
theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩
/-
**Multiset.replicate_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {a b : α} {n : ℕ}, n ≠ 0 → (Multiset.replicate n a = Mult
iset.replicate n b ↔ a = b)
参数：Multiset.replicate n a = Multiset.replicate n b ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Multiset.replicate_right_injective`：replicate_right_injective {n : Nat} 
(hn : n != 0) : Injective (@replicate α n)
-/
@[simp] theorem replicate_right_inj {a b : α} {n : ℕ} (h : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective h).eq_iff
/-
**Multiset.replicate_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_left_injective (a : α) : Injective (replicate · a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
-/
theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (card_replicate · a)
/-
**Multiset.replicate_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_subset_singleton (n : Nat) (a : α) : replicate n a subseteq {a}
参数：n : Nat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.replicate_subset_singleton`：replicate_subset_singleton (n) (a : α) 
: replicate n a subseteq [a]
-/
theorem replicate_subset_singleton (n : ℕ) (a : α) : replicate n a ⊆ {a} :=
  List.replicate_subset_singleton n a
/-
**Multiset.replicate_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_le_coe {a : α} {n} {l : List α} : replicate n a <= l ↔ List.repl
icate n a <+ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.perm_replicate`：∀ {α : Type u_1} {n : ℕ} {a : α} {l : List α}, l.Pe
rm (List.replicate n a) ↔ l = List.replicate n a
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
-/
theorem replicate_le_coe {a : α} {n} {l : List α} : replicate n a ≤ l ↔ List.replicate n a <+ l :=
  ⟨fun ⟨_l', p, s⟩ => perm_replicate.1 p ▸ s, Sublist.subperm⟩
/-
**Multiset.replicate_le_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_le_replicate (a : α) {k n : Nat} : replicate k a <= replicate n 
a ↔ k <= n
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.replicate_le_coe`：replicate_le_coe {a : α} {n} {l : List α} : r
eplicate n a <= l ↔ List.replicate n a <+ l
· 使用定理 `Multiset.coe_replicate`：coe_replicate (n : Nat) (a : α) : (List.replicat
e n a : Multiset α) = replicate n a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `List.replicate_sublist_replicate`：∀ {α : Type u_1} {m n : ℕ} (a : α), (L
ist.replicate m a).Sublist (List.replicate n a) ↔ m ≤ n
-/
theorem replicate_le_replicate (a : α) {k n : ℕ} : replicate k a ≤ replicate n a ↔ k ≤ n :=
  _root_.trans (by rw [← replicate_le_coe, coe_replicate]) (List.replicate_sublist_replicate a)

@[gcongr]
/-
**Multiset.replicate_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_mono (a : α) {k n : Nat} (h : k <= n) : replicate k a <= replica
te n a
参数：a : α；h : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.replicate_le_replicate`：replicate_le_replicate (a : α) {k n : N
at} : replicate k a <= replicate n a ↔ k <= n
-/
theorem replicate_mono (a : α) {k n : ℕ} (h : k ≤ n) : replicate k a ≤ replicate n a :=
  (replicate_le_replicate a).2 h
/-
**Multiset.le_replicate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_replicate_iff {m : Multiset α} {a : α} {n : Nat} : m <= replicate n a ↔
 exists k <= n, m = replicate k a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Multiset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_replicate_card`：eq_replicate_card {a : α} {s : Multiset α} :
 s = replicate (card s) a ↔ forall b in s, b = a
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.replicate_le_replicate`：replicate_le_replicate (a : α) {k n : N
at} : replicate k a <= replicate n a ↔ k <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_replicate_iff {m : Multiset α} {a : α} {n : ℕ} :
    m ≤ replicate n a ↔ ∃ k ≤ n, m = replicate k a :=
  ⟨fun h => ⟨card m, (card_mono h).trans_eq (card_replicate _ _),
      eq_replicate_card.2 fun _ hb => eq_of_mem_replicate <| subset_of_le h hb⟩,
    fun ⟨_, hkn, hm⟩ => hm.symm ▸ (replicate_le_replicate _).2 hkn⟩
/-
**Multiset.lt_replicate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lt_replicate_succ {m : Multiset α} {x : α} {n : Nat} : m < replicate (n + 
1) x ↔ m <= replicate n x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.lt_iff_cons_le`：lt_iff_cons_le {s t : Multiset α} : s < t ↔ exi
sts a, a ::ₘ s <= t
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
· 使用定理 `Multiset.replicate_succ`：∀ {α : Type u_1} (a : α) (n : ℕ), Multiset.repl
icate (n + 1) a = a ::ₘ Multiset.replicate n a
· 使用定理 `Multiset.cons_le_cons`：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ
 t
-/
theorem lt_replicate_succ {m : Multiset α} {x : α} {n : ℕ} :
    m < replicate (n + 1) x ↔ m ≤ replicate n x := by
  rw [lt_iff_cons_le]
  constructor
  · rintro ⟨x', hx'⟩
    have := eq_of_mem_replicate (mem_of_le hx' (mem_cons_self _ _))
    rwa [this, replicate_succ, cons_le_cons_iff] at hx'
  · intro h
    rw [replicate_succ]
    exact ⟨x, cons_le_cons _ h⟩

/-! ### Multiplicity of an element -/

section

variable [DecidableEq α] {s t u : Multiset α}

@[simp]
/-
**Multiset.count_replicate_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_replicate_self (a : α) (n : Nat) : count a (replicate n a) = n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `Multiset.coe_replicate`：coe_replicate (n : Nat) (a : α) : (List.replicat
e n a : Multiset α) = replicate n a
· 使用定理 `List.count_replicate_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α]
 {a : α} {n : ℕ}, List.count a (List.replicate n a) = n
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem count_replicate_self (a : α) (n : ℕ) : count a (replicate n a) = n := by
  convert! List.count_replicate_self (a := a)
  rw [← coe_count, coe_replicate]
/-
**Multiset.count_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_replicate (a b : α) (n : Nat) : count a (replicate n b) = if b = a t
hen n else 0
参数：a b : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `Multiset.coe_replicate`：coe_replicate (n : Nat) (a : α) : (List.replicat
e n a : Multiset α) = replicate n a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.count_replicate`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a b
 : α} {n : ℕ},   List.count a (List.replicate n b) = if (b == a) = true then n e
lse 0
-/
theorem count_replicate (a b : α) (n : ℕ) : count a (replicate n b) = if b = a then n else 0 := by
  convert! List.count_replicate (a := a)
  · rw [← coe_count, coe_replicate]
  · simp
/-
**Multiset.le_count_iff_replicate_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_count_iff_replicate_le {a : α} {s : Multiset α} {n : Nat} : n <= count 
a s ↔ replicate n a <= s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.replicate_sublist_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α
] {n : ℕ} {a : α} {l : List α},   (List.replicate n a).Sublist l ↔ n ≤ List.coun
t a l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Multiset.replicate_le_coe`：replicate_le_coe {a : α} {n} {l : List α} : r
eplicate n a <= l ↔ List.replicate n a <+ l
-/
theorem le_count_iff_replicate_le {a : α} {s : Multiset α} {n : ℕ} :
    n ≤ count a s ↔ replicate n a ≤ s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', coe_count]
    exact replicate_sublist_iff.symm.trans replicate_le_coe.symm

end

/-! ### Lift a relation to `Multiset`s -/

section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

/-
**Multiset.rel_replicate_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_replicate_left {m : Multiset α} {a : α} {r : α -> α -> Prop} {n : Nat}
 : (replicate n a).Rel r m ↔ card m = n ∧ forall x, x in m -> r a x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_eq_card_of_rel`：card_eq_card_of_rel {r : α -> β -> Prop} {
s : Multiset α} {t : Multiset β} (h : Rel r s t) : card s = card t
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `Multiset.exists_mem_of_rel_of_mem`：exists_mem_of_rel_of_mem {r : α -> β 
-> Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) : forall {a : α}, a i
n s -> exists b in t, r…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.rel_flip`：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `Multiset.rel_of_forall`：rel_of_forall {m1 m2 : Multiset α} {r : α -> α -
> Prop} (h : forall a b, a in m1 -> b in m2 -> r a b) (hc : card m1 = card m2) :
 m1.Rel r m2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem rel_replicate_left {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    (replicate n a).Rel r m ↔ card m = n ∧ ∀ x, x ∈ m → r a x :=
  ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_replicate _ _), fun x hx => by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_replicate hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun _ _ hx hy => (eq_of_mem_replicate hx).symm ▸ h.2 _ hy)
      (Eq.trans (card_replicate _ _) h.1.symm)⟩
/-
**Multiset.rel_replicate_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_replicate_right {m : Multiset α} {a : α} {r : α -> α -> Prop} {n : Nat
} : m.Rel r (replicate n a) ↔ card m = n ∧ forall x, x in m -> r x a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.rel_flip`：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
· 使用定理 `Multiset.rel_replicate_left`：rel_replicate_left {m : Multiset α} {a : α}
 {r : α -> α -> Prop} {n : Nat} : (replicate n a).Rel r m ↔ card m = n ∧ forall 
x, x in m -> r a …
-/
theorem rel_replicate_right {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    m.Rel r (replicate n a) ↔ card m = n ∧ ∀ x, x ∈ m → r x a :=
  rel_flip.trans rel_replicate_left

end Rel

section Replicate

variable {r : α → α → Prop} {s : Multiset α}

/-
**Multiset.nodup_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_iff_le {s : Multiset α} : Nodup s ↔ forall a : α, ¬a ::ₘ a ::ₘ 0 <= 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.nodup_iff_sublist`：nodup_iff_sublist {l : List α} : Nodup l ↔ foral
l a, ¬[a, a] <+ l
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Multiset.replicate_le_coe`：replicate_le_coe {a : α} {n} {l : List α} : r
eplicate n a <= l ↔ List.replicate n a <+ l
-/
theorem nodup_iff_le {s : Multiset α} : Nodup s ↔ ∀ a : α, ¬a ::ₘ a ::ₘ 0 ≤ s :=
  Quot.induction_on s fun _ =>
    nodup_iff_sublist.trans <| forall_congr' fun a => not_congr (@replicate_le_coe _ a 2 _).symm
/-
**Multiset.nodup_iff_ne_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_iff_ne_cons_cons {s : Multiset α} : s.Nodup ↔ forall a t, s != a ::ₘ
 a ::ₘ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.nodup_iff_le`：nodup_iff_le {s : Multiset α} : Nodup s ↔ forall 
a : α, ¬a ::ₘ a ::ₘ 0 <= s
· 使用定理 `Multiset.cons_le_cons`：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ
 t
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_iff_exists_add`：le_iff_exists_add {s t : Multiset α} : s <= 
t ↔ exists u, t = s + u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
-/
theorem nodup_iff_ne_cons_cons {s : Multiset α} : s.Nodup ↔ ∀ a t, s ≠ a ::ₘ a ::ₘ t :=
  nodup_iff_le.trans
    ⟨fun h a _ s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, Multiset.zero_add] at s_eq)⟩
/-
**Multiset.nodup_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_iff_pairwise {α} {s : Multiset α} : Nodup s ↔ Pairwise (· != ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Multiset.pairwise_coe_iff_pairwise`：pairwise_coe_iff_pairwise {r : α -> 
α -> Prop} [Std.Symm r] {l : List α} : Multiset.Pairwise r l ↔ l.Pairwise r
· 使用定理 `Function.instSymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Symm
 r], Std.Symm (Function.swap r)
· 使用定理 `instSymmNe_mathlib`：∀ (α : Sort u_1), Std.Symm Ne
-/
theorem nodup_iff_pairwise {α} {s : Multiset α} : Nodup s ↔ Pairwise (· ≠ ·) s :=
  Quotient.inductionOn s fun _ ↦ pairwise_coe_iff_pairwise.symm
/-
**Multiset.Nodup.pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Multiset α},   (∀ a ∈ s, ∀ b ∈ s,
 a ≠ b → r a b) → s.Nodup → Multiset.Pairwise r s
参数：∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.Pairwise.imp_of_mem`：∀ {α : Type u_1} {l : List α} {R S : α → α → P
rop},   (∀ {a b : α}, a ∈ l → b ∈ l → R a b → S a b) → List.Pairwise R l → List.
Pairwise S l
-/
protected theorem Nodup.pairwise : (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) → Nodup s → Pairwise r s :=
  Quotient.inductionOn s fun l h hl => ⟨l, rfl, hl.imp_of_mem fun {a b} ha hb => h a ha b hb⟩

end Replicate

end Multiset

