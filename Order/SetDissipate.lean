/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

module

public import Mathlib.Order.SetAccumulate

/-!
# Dissipate

The function `dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.
It is related to `accumulate s := ⋃ y ≤ x, s y`.

-/

@[expose] public section

variable {α β : Type*} {s : α → Set β}

namespace Set

/-- `dissipate s` is the intersection of `s y` for `y ≤ x`. -/
/-
**Set.dissipate** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：dissipate [LE α] (s : α -> Set β) (x : α) : Set β
参数：s : α -> Set β；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dissipate s` is the intersection of `s y` for `y ≤ x`.
-/
def dissipate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋂ y ≤ x, s y
/-
**Set.dissipate_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dissipate_def [LE α] {x : α} : dissipate s x = ⋂ y <= x, s y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dissipate_def [LE α] {x : α} : dissipate s x = ⋂ y ≤ x, s y := rfl
/-
**Set.dissipate_eq_biInter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dissipate_eq_biInter_lt {s : Nat -> Set β} {n : Nat} : dissipate s n = ⋂ k
 < n + 1, s k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dissipate_eq_biInter_lt {s : ℕ → Set β} {n : ℕ} : dissipate s n = ⋂ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, dissipate]

@[simp]
/-
**Set.mem_dissipate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_dissipate [LE α] {x : α} {z : β} : z in dissipate s x ↔ forall y <= x,
 z in s y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_dissipate [LE α] {x : α} {z : β} : z ∈ dissipate s x ↔ ∀ y ≤ x, z ∈ s y := by
  simp [dissipate_def]
/-
**Set.dissipate_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dissipate_subset [LE α] {x y : α} (hy : y <= x) : dissipate s x subseteq s
 y
参数：hy : y <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
-/
theorem dissipate_subset [LE α] {x y : α} (hy : y ≤ x) : dissipate s x ⊆ s y :=
  biInter_subset_of_mem hy
/-
**Set.iInter_subset_dissipate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_subset_dissipate [LE α] (x : α) : ⋂ i, s i subseteq dissipate s x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.iInter_subset_of_subset`：iInter_subset_of_subset {s : ι -> Set α} {t
 : Set α} (i : ι) (h : s i subseteq t) : ⋂ i, s i subseteq t
-/
theorem iInter_subset_dissipate [LE α] (x : α) : ⋂ i, s i ⊆ dissipate s x := by
  simp only [dissipate, subset_iInter_iff]
  exact fun x h ↦ iInter_subset_of_subset x fun ⦃a⦄ a ↦ a
/-
**Set.antitone_dissipate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：antitone_dissipate [Preorder α] : Antitone (dissipate s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem antitone_dissipate [Preorder α] : Antitone (dissipate s) :=
  fun _ _ hab ↦ biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]
/-
**Set.dissipate_subset_dissipate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dissipate_subset_dissipate [Preorder α] {x y} (h : y <= x) : dissipate s x
 subseteq dissipate s y
参数：h : y <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.antitone_dissipate`：antitone_dissipate [Preorder α] : Antitone (diss
ipate s)
-/
theorem dissipate_subset_dissipate [Preorder α] {x y} (h : y ≤ x) :
    dissipate s x ⊆ dissipate s y :=
  antitone_dissipate h

@[simp]
/-
**Set.biInter_dissipate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_dissipate [Preorder α] {s : α -> Set β} {x : α} : ⋂ y, ⋂ (_ : y <=
 x), dissipate s y = dissipate s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.dissipate_subset_dissipate`：dissipate_subset_dissipate [Preorder α] 
{x y} (h : y <= x) : dissipate s x subseteq dissipate s y
-/
theorem biInter_dissipate [Preorder α] {s : α → Set β} {x : α} :
    ⋂ y, ⋂ (_ : y ≤ x), dissipate s y = dissipate s x := by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy ↦ ?_
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h ↦ hy h z le_rfl
  · simp only [subset_iInter_iff]
    exact fun i j ↦ dissipate_subset_dissipate j

@[simp]
/-
**Set.iInter_dissipate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_dissipate [Preorder α] : ⋂ x, dissipate s x = ⋂ x, s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iInter_dissipate [Preorder α] : ⋂ x, dissipate s x = ⋂ x, s x := by
  apply Subset.antisymm <;> simp_rw [subset_def, dissipate_def, mem_iInter]
  · exact fun z h x' ↦ h x' x' le_rfl
  · exact fun z h x' y hy ↦ h y

@[simp]
/-
**Set.dissipate_bot** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：dissipate_bot [PartialOrder α] [OrderBot α] (s : α -> Set β) : dissipate s
 ⊥ = s ⊥
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
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dissipate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : dissipate s ⊥ = s ⊥ := by
  simp [dissipate_def]

@[simp]
/-
**Set.dissipate_zero_nat** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：dissipate_zero_nat (s : Nat -> Set β) : dissipate s 0 = s 0
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
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dissipate_zero_nat (s : ℕ → Set β) : dissipate s 0 = s 0 := by
  simp [dissipate_def]

@[simp]
/-
**Set.dissipate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dissipate_succ (s : Nat -> Set α) (n : Nat) : dissipate s (n + 1) = (dissi
pate s n) inter s (n + 1)
参数：s : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem dissipate_succ (s : ℕ → Set α) (n : ℕ) :
  dissipate s (n + 1) = (dissipate s n) ∩ s (n + 1) := by
  ext x
  simp_all only [dissipate_def, mem_iInter, mem_inter_iff]
  grind

/-- For a directed set of sets `s : ℕ → Set α` and `n : ℕ`, there exists `m : ℕ` (maybe
larger than `n`) such that `s m ⊆ dissipate s n`. -/
/-
**Set.exists_subset_dissipate_of_directed** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_subset_dissipate_of_directed {s : Nat -> Set α} (hd : Directed (· ⊇
 ·) s) (n : Nat) : exists m, s m subseteq dissipate s n
参数：hd : Directed (· ⊇ ·) s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Set.dissipate_succ`：dissipate_succ (s : Nat -> Set α) (n : Nat) : dissip
ate s (n + 1) = (dissipate s n) inter s (n + 1)

--- 原说明 ---
For a directed set of sets `s : ℕ → Set α` and `n : ℕ`, there exists `m : ℕ` (ma
ybe
larger than `n`) such that `s m ⊆ dissipate s n`.
-/
lemma exists_subset_dissipate_of_directed {s : ℕ → Set α}
  (hd : Directed (· ⊇ ·) s) (n : ℕ) : ∃ m, s m ⊆ dissipate s n := by
  induction n with
  | zero => use 0; simp [dissipate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    exact ⟨k, by simp; grind⟩
/-
**Set.directed_dissipate** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：directed_dissipate {s : Nat -> Set α} : Directed (· ⊇ ·) (dissipate s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.directed_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [IsDirectedOrder α] [inst_2 : Preorder β] {f : α → β},   Antitone f → Directed
 (fun x1 x…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.antitone_dissipate`：antitone_dissipate [Preorder α] : Antitone (diss
ipate s)
-/
lemma directed_dissipate {s : ℕ → Set α} : Directed (· ⊇ ·) (dissipate s) :=
  antitone_dissipate.directed_ge
/-
**Set.exists_dissipate_eq_empty_iff_of_directed** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_dissipate_eq_empty_iff_of_directed {s : Nat -> Set α} (hd : Directe
d (· ⊇ ·) s) : (exists n, dissipate s n = ∅) ↔ exists n, s n = ∅
参数：hd : Directed (· ⊇ ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Set.exists_subset_dissipate_of_directed`：exists_subset_dissipate_of_dire
cted {s : Nat -> Set α} (hd : Directed (· ⊇ ·) s) (n : Nat) : exists m, s m subs
eteq dissipate s n
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.subset_eq_empty`：subset_eq_empty {s t : Set α} (h : t subseteq s) (e
 : s = ∅) : t = ∅
· 使用定理 `Set.dissipate_subset`：dissipate_subset [LE α] {x y : α} (hy : y <= x) : 
dissipate s x subseteq s y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma exists_dissipate_eq_empty_iff_of_directed {s : ℕ → Set α} (hd : Directed (· ⊇ ·) s) :
    (∃ n, dissipate s n = ∅) ↔ ∃ n, s n = ∅ := by
  refine ⟨?_, fun ⟨n, hn⟩ ↦ ⟨n, subset_eq_empty (dissipate_subset le_rfl) hn⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
  exact (h m).mono hm

end Set

