/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Order.LiminfLimsup
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality and limit of sum of indicators

This file contains results relating the cardinality of subsets of ℕ and limits,
limsups of sums of indicators.

## Tags
finite, indicator, limsup, tendsto
-/

public section

namespace Set

open Filter Finset

/-
**Set.sum_indicator_eventually_eq_card** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sum_indicator_eventually_eq_card {α : Type*} [AddCommMonoid α] (a : α) {s 
: Set Nat} (hs : s.Finite) : forallᶠ n in atTop, ∑ k in Finset.range n, s.indica
tor (fun _ => a) k = (Nat.card s) • a
参数：a : α；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用引理 `Nat.card_eq_card_finite_toFinset`：card_eq_card_finite_toFinset {s : Set 
α} (hs : s.Finite) : Nat.card s = hs.toFinset.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_eq_card_nsmul`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι}
 [inst : AddCommMonoid M] {f : ι → M} {b : M},   (∀ a ∈ s, f a = b) → ∑ a ∈ s, f
 a = s.card • …
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
lemma sum_indicator_eventually_eq_card {α : Type*} [AddCommMonoid α] (a : α) {s : Set ℕ}
    (hs : s.Finite) :
    ∀ᶠ n in atTop, ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ a) k = (Nat.card s) • a := by
  have key : ∀ x ∈ hs.toFinset, s.indicator (fun _ ↦ a) x = a := by
    intro x hx
    rw [indicator_of_mem (hs.mem_toFinset.1 hx) (fun _ ↦ a)]
  rw [Nat.card_eq_card_finite_toFinset hs, ← sum_eq_card_nsmul key, eventually_atTop]
  obtain ⟨m, hm⟩ := hs.bddAbove
  refine ⟨m + 1, fun n n_m ↦ (sum_subset ?_ ?_).symm⟩ <;> intro x <;> rw [hs.mem_toFinset]
  · rw [Finset.mem_range]
    exact fun x_s ↦ ((mem_upperBounds.1 hm) x x_s).trans_lt (Nat.lt_of_succ_le n_m)
  · exact fun _ x_s ↦ indicator_of_notMem x_s (fun _ ↦ a)
/-
**Set.infinite_iff_tendsto_sum_indicator_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：infinite_iff_tendsto_sum_indicator_atTop {R : Type*} [AddCommMonoid R] [Pa
rtialOrder R] [IsOrderedAddMonoid R] [AddLeftStrictMono R] [Archimedean R] {r : 
R} (h : 0 < r) {s : Set Nat} : s.Infinite ↔ atTop.Tendsto (fun n => ∑ k in Finse
t.range n, s.indicator (fun _ => r) k) atTop
参数：h : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Finset.sum_mono_set_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : A
ddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} [AddLeftMono N],   (∀ (x : ι),
 0 ≤ f x) → Monoton…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.indicator_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder M
] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ a ∈ s, 0 ≤ f a) → ∀ (a : α), 0
 ≤ s.indic…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finset.range_mono`：range_mono : Monotone range
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.tendsto_atTop_atTop_iff`：∀ {α : Type u_3} {β : Type u_4} [Nonem
pty α] [inst : Preorder α] [IsDirectedOrder α] {f : α → β} [inst_2 : Preorder β]
,   Monotone f → (Filt…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `exists_lt_nsmul`：∀ {R : Type u_1} [inst : AddCommMonoid R] [inst_1 : Par
tialOrder R] [AddLeftStrictMono R] [Archimedean R] {a : R},   0 < a → ∀ (b : R),
 ∃ n,…
· 使用定理 `Set.Infinite.exists_subset_card_eq`：∀ {α : Type u} {s : Set α}, s.Infini
te → ∀ (n : ℕ), ∃ t, ↑t ⊆ s ∧ t.card = n
· 使用定理 `Finset.bddAbove`：∀ {α : Type u} [inst : SemilatticeSup α] [Nonempty α] (
s : Finset α), BddAbove ↑s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.sum_eq_card_nsmul`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι}
 [inst : AddCommMonoid M] {f : ι → M} {b : M},   (∀ a ∈ s, f a = b) → ∑ a ∈ s, f
 a = s.card • …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
（共 39 条，此处仅展示前 30 条）
-/
lemma infinite_iff_tendsto_sum_indicator_atTop {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) {s : Set ℕ} :
    s.Infinite ↔ atTop.Tendsto (fun n ↦ ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ r) k) atTop := by
  constructor
  · have h_mono : Monotone fun n ↦ ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ r) k := by
      refine (sum_mono_set_of_nonneg ?_).comp range_mono
      exact (fun _ ↦ indicator_nonneg (fun _ _ ↦ h.le) _)
    rw [h_mono.tendsto_atTop_atTop_iff]
    intro hs n
    obtain ⟨n', hn'⟩ := exists_lt_nsmul h n
    obtain ⟨t, t_s, t_card⟩ := hs.exists_subset_card_eq n'
    obtain ⟨m, hm⟩ := t.bddAbove
    use m + 1
    grw [hn', ← t_s]
    have h : t ⊆ Finset.range (m + 1) := by
      intro i i_t
      rw [Finset.mem_range]
      exact (hm i_t).trans_lt (lt_add_one m)
    rw [sum_indicator_subset (fun _ ↦ r) h, sum_eq_card_nsmul (fun _ _ ↦ rfl), t_card]
  · contrapose!
    intro hs
    rw [tendsto_congr' (sum_indicator_eventually_eq_card r hs), tendsto_atTop_atTop]
    push Not
    obtain ⟨m, hm⟩ := exists_lt_nsmul h (Nat.card s • r)
    exact ⟨m • r, fun n ↦ ⟨n, le_refl n, not_le_of_gt hm⟩⟩
/-
**Set.limsup_eq_tendsto_sum_indicator_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：limsup_eq_tendsto_sum_indicator_atTop {α R : Type*} [AddCommMonoid R] [Par
tialOrder R] [IsOrderedAddMonoid R] [AddLeftStrictMono R] [Archimedean R] {r : R
} (h : 0 < r) (s : Nat -> Set α) : atTop.limsup s = { ω | atTop.Tendsto (fun n =
> ∑ k in Finset.range n, (s k).indicator (fun _ => r) ω) atTop }
参数：h : 0 < r；s : Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Filter.cofinite.limsup_set_eq`：∀ {α : Type u_1} {ι : Type u_4} {s : ι → 
Set α}, Filter.limsup s Filter.cofinite = {x | {n | x ∈ s n}.Infinite}
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用引理 `Set.infinite_iff_tendsto_sum_indicator_atTop`：infinite_iff_tendsto_sum_i
ndicator_atTop {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoi
d R] [AddLeftStrictMono R] [Archim…
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
-/
lemma limsup_eq_tendsto_sum_indicator_atTop {α R : Type*}
    [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) (s : ℕ → Set α) :
    atTop.limsup s = { ω | atTop.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, (s k).indicator (fun _ ↦ r) ω) atTop } := by
  nth_rw 1 [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq]
  ext ω
  rw [mem_ofPred_eq, mem_ofPred_eq, infinite_iff_tendsto_sum_indicator_atTop h, iff_eq_eq]
  congr

end Set

