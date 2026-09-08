/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `isCompactSystem_insert_univ_iff`: A set system is a compact system iff inserting `univ`
  gives a compact system.
* `isCompactSystem_isCompact_isClosed`: The set of closed and compact sets is a compact system.
* `isCompactSystem_isCompact`: In a `T2Space`, the set of compact sets is a compact system.
-/

@[expose] public section

open Set Finset Nat

variable {α : Type*} {S : Set (Set α)} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
/-
**IsCompactSystem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCompactSystem (S : Set (Set α)) : Prop
参数：S : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of sets is a compact system if, whenever a countable subfamily has empty i
ntersection,
then finitely many of them already have empty intersection.
-/
def IsCompactSystem (S : Set (Set α)) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

/-
**IsCompactSystem.of_nonempty_iInter** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactSystem`
。
形式化陈述：of_nonempty_iInter (h : forall C : Nat -> Set α, (forall i, C i in S) -> (
forall n, (dissipate C n).Nonempty) -> (⋂ i, C i).Nonempty) : IsCompactSystem S
参数：h : forall C : Nat -> Set α, (forall i, C i in S) -> (forall n, (dissipate C 
n).Nonempty) -> (⋂ i, C i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma of_nonempty_iInter
    (h : ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :
    IsCompactSystem S := by
  intro C hC
  contrapose!
  exact h C hC
/-
**IsCompactSystem.nonempty_iInter** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactSystem`。
形式化陈述：nonempty_iInter (hp : IsCompactSystem S) {C : Nat -> Set α} (hC : forall i
, C i in S) (h_nonempty : forall n, (dissipate C n).Nonempty) : (⋂ i, C i).Nonem
pty
参数：hp : IsCompactSystem S；hC : forall i, C i in S；h_nonempty : forall n, (dissip
ate C n).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma nonempty_iInter (hp : IsCompactSystem S) {C : ℕ → Set α} (hC : ∀ i, C i ∈ S)
    (h_nonempty : ∀ n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC
/-
**IsCompactSystem.iff_nonempty_iInter** 是 Mathlib 中的一个定理，位于命名空间 `IsCompactSystem
`。
形式化陈述：iff_nonempty_iInter (S : Set (Set α)) : IsCompactSystem S ↔ forall C : Nat
 -> Set α, (forall i, C i in S) -> (forall n, (dissipate C n).Nonempty) -> (⋂ i,
 C i).Nonempty
参数：S : Set (Set α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactSystem.nonempty_iInter`：nonempty_iInter (hp : IsCompactSystem S
) {C : Nat -> Set α} (hC : forall i, C i in S) (h_nonempty : forall n, (dissipat
e C n).Nonempty) : (⋂…
· 使用引理 `IsCompactSystem.of_nonempty_iInter`：of_nonempty_iInter (h : forall C : N
at -> Set α, (forall i, C i in S) -> (forall n, (dissipate C n).Nonempty) -> (⋂ 
i, C i).Nonempty) : IsCo…
-/
theorem iff_nonempty_iInter (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]
/-
**IsCompactSystem.of_IsEmpty** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactSystem`。
形式化陈述：of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S
参数：S : Set (Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
-/
lemma of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- Any subset of a compact system is a compact system. -/
/-
**IsCompactSystem.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsCompactSystem`。
形式化陈述：mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S subseteq T) : IsC
ompactSystem S
参数：Set α；hT : IsCompactSystem T；hST : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any subset of a compact system is a compact system.
-/
theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S ⊆ T) :
    IsCompactSystem S := fun C hC1 hC2 ↦ hT C (fun i ↦ hST (hC1 i)) hC2

/-- Inserting `∅` into a compact system gives a compact system. -/
/-
**IsCompactSystem.insert_empty** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactSystem`。
形式化陈述：insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S)
参数：h : IsCompactSystem S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.dissipate_subset`：dissipate_subset [LE α] {x y : α} (hy : y <= x) : 
dissipate s x subseteq s y
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.mem_of_mem_insert_of_ne`：mem_of_mem_insert_of_ne : b in insert a s -
> b != a -> b in s
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Inserting `∅` into a compact system gives a compact system.
-/
lemma insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S) := by
  intro s h' hd
  by_cases! g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · exact h s (fun i ↦ (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

/-- Inserting `univ` into a compact system gives a compact system. -/
/-
**IsCompactSystem.insert_univ** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactSystem`。
形式化陈述：insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S)
参数：h : IsCompactSystem S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompactSystem.iff_nonempty_iInter`：iff_nonempty_iInter (S : Set (Set α
)) : IsCompactSystem S ↔ forall C : Nat -> Set α, (forall i, C i in S) -> (foral
l n, (dissipate C n).None…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.antitone_dissipate`：antitone_dissipate [Preorder α] : Antitone (diss
ipate s)
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `Nat.le_max_right`：∀ (a b : ℕ), b ≤ max a b

--- 原说明 ---
Inserting `univ` into a compact system gives a compact system.
-/
lemma insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S) := by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases! h₀ : ∀ n, s n ∉ S
  · simp_all
  classical
  let n := Nat.find h₀
  let s' := fun i ↦ if s i ∈ S then s i else s n
  have h₁ : ∀ i, s' i ∈ S := by grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! ⟨j, hj⟩
  have h₃ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v := by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

end IsCompactSystem

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
/-
**isCompactSystem_iff_nonempty_iInter_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) : IsCompactSys
tem S ↔ forall C : Nat -> Set α, (forall i, C i in S) -> (forall n, (⋂ k < n, C 
k).Nonempty) -> (⋂ i, C i).Nonempty
参数：S : Set (Set α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.dissipate_eq_biInter_lt`：dissipate_eq_biInter_lt {s : Nat -> Set β} 
{n : Nat} : dissipate s n = ⋂ k < n + 1, s k
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`.
-/
lemma isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ h C hi (fun n ↦ dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' ↦ h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g ↦ h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le_trans (fun x ↦ by simp; grind) g

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
/-
**isCompactSystem_insert_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCompactSystem_insert_empty_iff : IsCompactSystem (insert ∅ S) ↔ IsCompac
tSystem S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactSystem.mono`：mono {T : Set (Set α)} (hT : IsCompactSystem T) (h
ST : S subseteq T) : IsCompactSystem S
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用引理 `IsCompactSystem.insert_empty`：insert_empty (h : IsCompactSystem S) : IsC
ompactSystem (insert ∅ S)

--- 原说明 ---
A set system is a compact system iff adding `∅` gives a compact system.
-/
lemma isCompactSystem_insert_empty_iff :
    IsCompactSystem (insert ∅ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_empty⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
/-
**isCompactSystem_insert_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsComp
actSystem S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactSystem.mono`：mono {T : Set (Set α)} (hT : IsCompactSystem T) (h
ST : S subseteq T) : IsCompactSystem S
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用引理 `IsCompactSystem.insert_univ`：insert_univ (h : IsCompactSystem S) : IsCom
pactSystem (insert univ S)

--- 原说明 ---
A set system is a compact system iff adding `univ` gives a compact system.
-/
lemma isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_univ⟩

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
/-
**isCompactSystem_iff_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactSystem_iff_of_directed (hpi : IsPiSystem S) : IsCompactSystem S ↔
 forall (C : Nat -> Set α), Directed (· ⊇ ·) C -> (forall i, C i in S) -> ⋂ i, C
 i = ∅ -> exists n, C n = ∅
参数：hpi : IsPiSystem S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isCompactSystem_insert_empty_iff`：isCompactSystem_insert_empty_iff : IsC
ompactSystem (insert ∅ S) ↔ IsCompactSystem S
· 使用引理 `Set.exists_dissipate_eq_empty_iff_of_directed`：exists_dissipate_eq_empty
_iff_of_directed {s : Nat -> Set α} (hd : Directed (· ⊇ ·) s) : (exists n, dissi
pate s n = ∅) ↔ exists n, s n = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `IsPiSystem.dissipate_mem`：IsPiSystem.dissipate_mem {s : Nat -> Set α} {C
 : Set (Set α)} (hC : IsPiSystem C) (h : forall n, s n in C) (n : Nat) (h' : (di
ssipate s n).N…
· 使用定理 `IsPiSystem.insert_empty`：IsPiSystem.insert_empty {S : Set (Set α)} (h_pi
 : IsPiSystem S) : IsPiSystem (insert ∅ S)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用引理 `Set.biInter_le_eq_iInter`：biInter_le_eq_iInter [Preorder α] {s : α -> Se
t β} : ⋂ (n) (m <= n), s m = ⋂ (n), s n
· 使用引理 `Set.directed_dissipate`：directed_dissipate {s : Nat -> Set α} : Directed
 (· ⊇ ·) (dissipate s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
To prove that a set of sets is a compact system, it suffices to consider directe
d families of
sets.
-/
theorem isCompactSystem_iff_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
      ∀ (C : ℕ → Set α), Directed (· ⊇ ·) C → (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ n, C n = ∅ := by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (∀ n, dissipate C n ∈ S ∨ dissipate C n = ∅) ∧ (⋂ n, dissipate C n = ∅) by
    by_cases! f : ∀ n, dissipate C n ∈ S
    · exact h (dissipate C) directed_dissipate f this.2
    · obtain ⟨n, hn⟩ := f
      exact ⟨n, by simpa [hn] using this.1 n⟩
  refine ⟨fun n ↦ ?_, h2⟩
  by_cases g : (dissipate C n).Nonempty
  · simpa [or_comm] using hpi.insert_empty.dissipate_mem h1 n g
  · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
/-
**isCompactSystem_iff_nonempty_iInter_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactSystem_iff_nonempty_iInter_of_directed (hpi : IsPiSystem S) : IsC
ompactSystem S ↔ forall (C : Nat -> Set α), (Directed (· ⊇ ·) C) -> (forall i, C
 i in S) -> (forall n, (C n).Nonempty) -> (⋂ i, C i).Nonempty
参数：hpi : IsPiSystem S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompactSystem_iff_of_directed`：isCompactSystem_iff_of_directed (hpi : 
IsPiSystem S) : IsCompactSystem S ↔ forall (C : Nat -> Set α), Directed (· ⊇ ·) 
C -> (forall i, C i i…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
To prove that a set of sets is a compact system, it suffices to consider directe
d families of
sets.
-/
theorem isCompactSystem_iff_nonempty_iInter_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    ∀ (C : ℕ → Set α), (Directed (· ⊇ ·) C) → (∀ i, C i ∈ S) → (∀ n, (C n).Nonempty) →
      (⋂ i, C i).Nonempty := by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> contrapose!
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

/-- The set of compact and closed sets is a compact system. -/
/-
**isCompactSystem_isCompact_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] : IsCo
mpactSystem {s : Set α | IsCompact s ∧ IsClosed s}
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactSystem.of_nonempty_iInter`：of_nonempty_iInter (h : forall C : N
at -> Set α, (forall i, C i in S) -> (forall n, (dissipate C n).Nonempty) -> (⋂ 
i, C i).Nonempty) : IsCo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iInter_dissipate`：iInter_dissipate [Preorder α] : ⋂ x, dissipate s x
 = ⋂ x, s x
· 使用定理 `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : Nat -> Set X) 
(htd : forall i, t (i + 1) subseteq t i) (htn : forall …
· 使用定理 `Set.antitone_dissipate`：antitone_dissipate [Preorder α] : Antitone (diss
ipate s)
· 使用引理 `Set.dissipate_zero_nat`：dissipate_zero_nat (s : Nat -> Set β) : dissipat
e s 0 = s 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The set of compact and closed sets is a compact system.
-/
theorem isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem {s : Set α | IsCompact s ∧ IsClosed s} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty ↦ ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) h_nonempty ?_ (fun n ↦ isClosed_biInter (fun i _ ↦ (hC_cc i).2))
  · exact Set.antitone_dissipate (by lia)
  · simpa using (hC_cc 0).1

/-- In a `T2Space` the set of compact sets is a compact system. -/
/-
**isCompactSystem_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] : I
sCompactSystem {s : Set α | IsCompact s}
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `isCompactSystem_isCompact_isClosed`：isCompactSystem_isCompact_isClosed (
α : Type*) [TopologicalSpace α] : IsCompactSystem {s : Set α | IsCompact s ∧ IsC
losed s}

--- 原说明 ---
In a `T2Space` the set of compact sets is a compact system.
-/
theorem isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] :
    IsCompactSystem {s : Set α | IsCompact s} := by
  convert! isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
/-
**isCompactSystem_insert_univ_isCompact_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpa
ce α] : IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s})
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactSystem.insert_univ`：insert_univ (h : IsCompactSystem S) : IsCom
pactSystem (insert univ S)
· 使用定理 `isCompactSystem_isCompact_isClosed`：isCompactSystem_isCompact_isClosed (
α : Type*) [TopologicalSpace α] : IsCompactSystem {s : Set α | IsCompact s ∧ IsC
losed s}

--- 原说明 ---
The set of sets which are either compact and closed, or `univ`, is a compact sys
tem.
-/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed

