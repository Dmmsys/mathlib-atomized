/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.PartialSups

/-!
# Accumulate

The function `accumulate` takes `s : α → Set β` with `LE α` and returns `⋃ y ≤ x, s y`.
It is related to `dissipate s := ⋂ y ≤ x, s y`.

`accumulate` is closely related to the function `partialSups`, although these two functions have
slightly different typeclass assumptions and API. `partialSups_eq_accumulate` shows
that they coincide on `ℕ`.
-/

@[expose] public section

variable {α β : Type*} {s : α → Set β}

namespace Set

/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
/-
**Set.accumulate** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：accumulate [LE α] (s : α -> Set β) (x : α) : Set β
参数：s : α -> Set β；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`accumulate s` is the union of `s y` for `y ≤ x`.
-/
def accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y
/-
**Set.accumulate_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：accumulate_def [LE α] {x : α} : accumulate s x = ⋃ y <= x, s y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem accumulate_def [LE α] {x : α} : accumulate s x = ⋃ y ≤ x, s y :=
  rfl
/-
**Set.accumulate_eq_biInter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：accumulate_eq_biInter_lt {s : Nat -> Set β} {n : Nat} : accumulate s n = ⋃
 k < n + 1, s k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem accumulate_eq_biInter_lt {s : ℕ → Set β} {n : ℕ} : accumulate s n = ⋃ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, accumulate]

@[simp]
/-
**Set.mem_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_accumulate [LE α] {x : α} {z : β} : z in accumulate s x ↔ exists y <= 
x, z in s y
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
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ y ≤ x, z ∈ s y := by
  simp_rw [accumulate_def, mem_iUnion₂, exists_prop]
/-
**Set.subset_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_accumulate [Preorder α] {x : α} : s x subseteq accumulate s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ accumulate s x := fun _ => mem_biUnion le_rfl
/-
**Set.accumulate_subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：accumulate_subset_iUnion [LE α] (x : α) : accumulate s x subseteq ⋃ i, s i
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.biUnion_univ`：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = 
⋃ x, s x
-/
theorem accumulate_subset_iUnion [LE α] (x : α) : accumulate s x ⊆ ⋃ i, s i :=
  (biUnion_subset_biUnion_left (subset_univ _)).trans_eq (biUnion_univ _)
/-
**Set.monotone_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_accumulate [Preorder α] : Monotone (accumulate s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem monotone_accumulate [Preorder α] : Monotone (accumulate s) := fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy

@[gcongr]
/-
**Set.accumulate_subset_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：accumulate_subset_accumulate [Preorder α] {x y} (h : x <= y) : accumulate 
s x subseteq accumulate s y
参数：h : x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
-/
theorem accumulate_subset_accumulate [Preorder α] {x y} (h : x ≤ y) :
    accumulate s x ⊆ accumulate s y :=
  monotone_accumulate h

@[simp]
/-
**Set.biUnion_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_accumulate [Preorder α] (x : α) : ⋃ y <= x, accumulate s y = ⋃ y <
= x, s y
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `Set.subset_accumulate`：subset_accumulate [Preorder α] {x : α} : s x subs
eteq accumulate s x
-/
theorem biUnion_accumulate [Preorder α] (x : α) : ⋃ y ≤ x, accumulate s y = ⋃ y ≤ x, s y := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

@[simp]
/-
**Set.iUnion_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_accumulate [Preorder α] : ⋃ x, accumulate s x = ⋃ x, s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.subset_accumulate`：subset_accumulate [Preorder α] {x : α} : s x subs
eteq accumulate s x
-/
theorem iUnion_accumulate [Preorder α] : ⋃ x, accumulate s x = ⋃ x, s x := by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate

@[simp]
/-
**Set.accumulate_bot** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：accumulate_bot [PartialOrder α] [OrderBot α] (s : α -> Set β) : accumulate
 s ⊥ = s ⊥
参数：s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma accumulate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : accumulate s ⊥ = s ⊥ := by
  simp [Set.accumulate_def]

@[simp]
/-
**Set.accumulate_zero_nat** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：accumulate_zero_nat (s : Nat -> Set β) : accumulate s 0 = s 0
参数：s : Nat -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma accumulate_zero_nat (s : ℕ → Set β) : accumulate s 0 = s 0 := by
  simp [accumulate_def]

open Function in
/-
**Set.disjoint_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_accumulate [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α}
 (hij : i < j) : Disjoint (accumulate s i) (s j)
参数：hs : Pairwise (Disjoint on s)；hij : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem disjoint_accumulate [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α} (hij : i < j) :
    Disjoint (accumulate s i) (s j) := by
  apply disjoint_left.2 (fun x hx ↦ ?_)
  simp only [accumulate, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hx⟩
  exact disjoint_left.1 (hs (hk.trans_lt hij).ne) hx

@[simp]
/-
**Set.accumulate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：accumulate_succ (u : Nat -> Set α) (n : Nat) : accumulate u (n + 1) = accu
mulate u n union u (n + 1)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biUnion_le_succ`：biUnion_le_succ (u : Nat -> Set α) (n : Nat) : ⋃ k 
<= n + 1, u k = (⋃ k <= n, u k) union u (n + 1)
-/
theorem accumulate_succ (u : ℕ → Set α) (n : ℕ) :
    accumulate u (n + 1) = accumulate u n ∪ u (n + 1) := biUnion_le_succ u n
/-
**Set.partialSups_eq_accumulate** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：partialSups_eq_accumulate (f : Nat -> Set α) : partialSups f = accumulate 
f
参数：f : Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `partialSups_eq_sup_range`：partialSups_eq_sup_range [OrderBot α] (f : Nat
 -> α) (n : Nat) : partialSups f n = (Finset.range (n + 1)).sup f
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma partialSups_eq_accumulate (f : ℕ → Set α) :
    partialSups f = accumulate f := by
  ext n
  simp [partialSups_eq_sup_range, accumulate, Nat.lt_succ_iff]

/-- For a directed set of sets `s : ℕ → Set α` and `n : ℕ`, there exists `m : ℕ` (maybe
larger than `n`) such that `accumulate s n ⊆ s m`. -/
/-
**Set.exists_subset_accumulate_of_directed** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_subset_accumulate_of_directed {s : Nat -> Set α} (hd : Directed (· 
subseteq ·) s) (n : Nat) : exists m, accumulate s n subseteq s m
参数：hd : Directed (· subseteq ·) s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Set.accumulate_succ`：accumulate_succ (u : Nat -> Set α) (n : Nat) : accu
mulate u (n + 1) = accumulate u n union u (n + 1)

--- 原说明 ---
For a directed set of sets `s : ℕ → Set α` and `n : ℕ`, there exists `m : ℕ` (ma
ybe
larger than `n`) such that `accumulate s n ⊆ s m`.
-/
lemma exists_subset_accumulate_of_directed {s : ℕ → Set α}
  (hd : Directed (· ⊆ ·) s) (n : ℕ) : ∃ m, accumulate s n ⊆ s m := by
  induction n with
  | zero => use 0; simp [accumulate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    simp at hk
    exact ⟨k, by simp; grind⟩
/-
**Set.directed_accumulate** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：directed_accumulate {s : Nat -> Set α} : Directed (· subseteq ·) (accumula
te s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
-/
lemma directed_accumulate {s : ℕ → Set α} : Directed (· ⊆ ·) (accumulate s) :=
  monotone_accumulate.directed_le
/-
**Set.exists_accumulate_eq_univ_iff_of_directed** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_accumulate_eq_univ_iff_of_directed {s : Nat -> Set α} (hd : Directe
d (· subseteq ·) s) : (exists n, accumulate s n = univ) ↔ exists n, s n = univ
参数：hd : Directed (· subseteq ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.exists_subset_accumulate_of_directed`：exists_subset_accumulate_of_di
rected {s : Nat -> Set α} (hd : Directed (· subseteq ·) s) (n : Nat) : exists m,
 accumulate s n subseteq s m
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_accumulate`：subset_accumulate [Preorder α] {x : α} : s x subs
eteq accumulate s x
-/
lemma exists_accumulate_eq_univ_iff_of_directed {s : ℕ → Set α} (hd : Directed (· ⊆ ·) s) :
    (∃ n, accumulate s n = univ) ↔ ∃ n, s n = univ := by
  refine ⟨?_, fun ⟨n, hn⟩ ↦ ⟨n,
    subset_antisymm (subset_univ _) (hn.symm.le.trans subset_accumulate)⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_accumulate_of_directed hd n
  grind

end Set

