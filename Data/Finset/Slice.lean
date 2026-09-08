/-
Copyright (c) 2021 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# `r`-sets and slice

This file defines the `r`-th slice of a set family and provides a way to say that a set family is
made of `r`-sets.

An `r`-set is a finset of cardinality `r` (aka of *size* `r`). The `r`-th slice of a set family is
the set family made of its `r`-sets.

## Main declarations

* `Set.Sized`: `A.Sized r` means that `A` only contains `r`-sets.
* `Finset.slice`: `A.slice r` is the set of `r`-sets in `A`.

## Notation

`A # r` is notation for `A.slice r` in scope `finset_family`.
-/

@[expose] public section


open Finset Nat

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace Set

variable {A B : Set (Finset α)} {s : Finset α} {r : ℕ}

/-! ### Families of `r`-sets -/


/-- `Sized r A` means that every Finset in `A` has size `r`. -/
/-
**Set.Sized** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Sized (r : Nat) (A : Set (Finset α)) : Prop
参数：r : Nat；A : Set (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sized r A` means that every Finset in `A` has size `r`.
-/
def Sized (r : ℕ) (A : Set (Finset α)) : Prop := ∀ ⦃x⦄, x ∈ A → #x = r
/-
**Set.Sized.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sized`。
形式化陈述：∀ {α : Type u_1} {A B : Set (Finset α)} {r : ℕ}, A ⊆ B → Set.Sized r B → S
et.Sized r A
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sized.mono (h : A ⊆ B) (hB : B.Sized r) : A.Sized r := fun _x hx => hB <| h hx
/-
**Set.sized_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {r : ℕ}, Set.Sized r ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma sized_empty : (∅ : Set (Finset α)).Sized r := by simp [Sized]
/-
**Set.sized_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {r : ℕ}, Set.Sized r {s} ↔ s.card = r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sized_singleton : ({s} : Set (Finset α)).Sized r ↔ #s = r := by simp [Sized]
/-
**Set.sized_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sized_union : (A union B).Sized r ↔ A.Sized r ∧ B.Sized r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Sized.mono`：∀ {α : Type u_1} {A B : Set (Finset α)} {r : ℕ}, A ⊆ B →
 Set.Sized r B → Set.Sized r A
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sized_union : (A ∪ B).Sized r ↔ A.Sized r ∧ B.Sized r :=
  ⟨fun hA => ⟨hA.mono subset_union_left, hA.mono subset_union_right⟩, fun hA _x hx =>
    hx.elim (fun h => hA.1 h) fun h => hA.2 h⟩

alias ⟨_, sized.union⟩ := sized_union

--TODO: A `forall_iUnion` lemma would be handy here.
@[simp]
/-
**Set.sized_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sized_iUnion {f : ι -> Set (Finset α)} : (⋃ i, f i).Sized r ↔ forall i, (f
 i).Sized r
参数：Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem sized_iUnion {f : ι → Set (Finset α)} : (⋃ i, f i).Sized r ↔ ∀ i, (f i).Sized r := by
  simp_rw [Set.Sized, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

-- `simp` normal form is `sized_iUnion`.
/-
**Set.sized_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sized_iUnion {f : ι -> Set (Finset α)} : (⋃ i, f i).Sized r ↔ forall i, (f
 i).Sized r
参数：Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem sized_iUnion₂ {f : ∀ i, κ i → Set (Finset α)} :
    (⋃ (i) (j), f i j).Sized r ↔ ∀ i j, (f i j).Sized r := by
  simp only [Set.sized_iUnion]
/-
**Set.Sized.isAntichain** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sized`。
形式化陈述：∀ {α : Type u_1} {A : Set (Finset α)} {r : ℕ}, Set.Sized r A → IsAntichain
 (fun x1 x2 => x1 ⊆ x2) A
参数：Finset α；fun x1 x2 => x1 ⊆ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Sized.isAntichain (hA : A.Sized r) : IsAntichain (· ⊆ ·) A :=
  fun _s hs _t ht h hst => h <| Finset.eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le
/-
**Set.Sized.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sized`。
形式化陈述：∀ {α : Type u_1} {A : Set (Finset α)}, Set.Sized 0 A → A.Subsingleton
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_forall_eq`：subsingleton_of_forall_eq (a : α) (h : fo
rall b in s, b = a) : s.Subsingleton
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
-/
protected theorem Sized.subsingleton (hA : A.Sized 0) : A.Subsingleton :=
  subsingleton_of_forall_eq ∅ fun _s hs => card_eq_zero.1 <| hA hs
/-
**Set.Sized.subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sized`。
形式化陈述：∀ {α : Type u_1} {A : Set (Finset α)} [inst : Fintype α], Set.Sized (Finty
pe.card α) A → A.Subsingleton
参数：Finset α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_forall_eq`：subsingleton_of_forall_eq (a : α) (h : fo
rall b in s, b = a) : s.Subsingleton
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_iff_eq_univ`：Finset.card_eq_iff_eq_univ [Fintype α] (s : 
Finset α) : #s = Fintype.card α ↔ s = univ
-/
theorem Sized.subsingleton' [Fintype α] (hA : A.Sized (Fintype.card α)) : A.Subsingleton :=
  subsingleton_of_forall_eq Finset.univ fun s hs => s.card_eq_iff_eq_univ.1 <| hA hs
/-
**Set.Sized.empty_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sized`。
形式化陈述：∀ {α : Type u_1} {A : Set (Finset α)} {r : ℕ}, Set.Sized r A → (∅ ∈ A ↔ A 
= {∅})
参数：Finset α；∅ ∈ A ↔ A = {∅}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.bot_mem_iff`：IsAntichain.bot_mem_iff [OrderBot α] (hs : IsAn
tichain (· <= ·) s) : ⊥ in s ↔ s = {⊥}
· 使用定理 `Set.Sized.isAntichain`：∀ {α : Type u_1} {A : Set (Finset α)} {r : ℕ}, Se
t.Sized r A → IsAntichain (fun x1 x2 => x1 ⊆ x2) A
-/
theorem Sized.empty_mem_iff (hA : A.Sized r) : ∅ ∈ A ↔ A = {∅} :=
  hA.isAntichain.bot_mem_iff
/-
**Set.Sized.univ_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sized`。
形式化陈述：∀ {α : Type u_1} {A : Set (Finset α)} {r : ℕ} [inst : Fintype α], Set.Size
d r A → (Finset.univ ∈ A ↔ A = {Finset.univ})
参数：Finset α；Finset.univ ∈ A ↔ A = {Finset.univ}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.top_mem_iff`：IsAntichain.top_mem_iff [OrderTop α] (hs : IsAn
tichain (· <= ·) s) : ⊤ in s ↔ s = {⊤}
· 使用定理 `Set.Sized.isAntichain`：∀ {α : Type u_1} {A : Set (Finset α)} {r : ℕ}, Se
t.Sized r A → IsAntichain (fun x1 x2 => x1 ⊆ x2) A
-/
theorem Sized.univ_mem_iff [Fintype α] (hA : A.Sized r) : Finset.univ ∈ A ↔ A = {Finset.univ} :=
  hA.isAntichain.top_mem_iff
/-
**Set.sized_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sized_powersetCard (s : Finset α) (r : Nat) : (powersetCard r s : Set (Fin
set α)).Sized r
参数：s : Finset α；r : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
-/
theorem sized_powersetCard (s : Finset α) (r : ℕ) : (powersetCard r s : Set (Finset α)).Sized r :=
  fun _t ht => (mem_powersetCard.1 ht).2

end Set

namespace Finset

section Sized

variable [Fintype α] {𝒜 : Finset (Finset α)} {s : Finset α} {r : ℕ}

/-
**Finset.subset_powersetCard_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_powersetCard_univ_iff : 𝒜 subseteq powersetCard r univ ↔ (𝒜 : Set (
Finset α)).Sized r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mem_powersetCard_univ`：mem_powersetCard_univ : s in powersetCard 
k (univ : Finset α) ↔ #s = k
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_powersetCard_univ_iff : 𝒜 ⊆ powersetCard r univ ↔ (𝒜 : Set (Finset α)).Sized r :=
  forall_congr' fun A => by rw [mem_powersetCard_univ, mem_coe]

alias ⟨_, _root_.Set.Sized.subset_powersetCard_univ⟩ := subset_powersetCard_univ_iff
/-
**Finset._root_.Set.Sized.card_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Sized.card_le (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 ≤ (Fintype.card α).choose r := by
  rw [Fintype.card, ← card_powersetCard]
  exact card_le_card (subset_powersetCard_univ_iff.mpr h𝒜)

end Sized

/-! ### Slices -/


section Slice

variable {𝒜 : Finset (Finset α)} {A A₁ A₂ : Finset α} {r r₁ r₂ : ℕ}

/-- The `r`-th slice of a set family is the subset of its elements which have cardinality `r`. -/
/-
**Finset.slice** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：slice (𝒜 : Finset (Finset α)) (r : Nat) : Finset (Finset α)
参数：𝒜 : Finset (Finset α)；r : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `r`-th slice of a set family is the subset of its elements which have cardin
ality `r`.
-/
def slice (𝒜 : Finset (Finset α)) (r : ℕ) : Finset (Finset α) := {A ∈ 𝒜 | #A = r}

@[inherit_doc]
scoped[Finset] infixl:90 " # " => Finset.slice

/-- `A` is in the `r`-th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`. -/
/-
**Finset.mem_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_slice : A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a

--- 原说明 ---
`A` is in the `r`-th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`.
-/
theorem mem_slice : A ∈ 𝒜 # r ↔ A ∈ 𝒜 ∧ #A = r :=
  mem_filter

/-- The `r`-th slice of `𝒜` is a subset of `𝒜`. -/
/-
**Finset.slice_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：slice_subset : 𝒜 # r subseteq 𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s

--- 原说明 ---
The `r`-th slice of `𝒜` is a subset of `𝒜`.
-/
theorem slice_subset : 𝒜 # r ⊆ 𝒜 :=
  filter_subset _ _

/-- Everything in the `r`-th slice of `𝒜` has size `r`. -/
/-
**Finset.sized_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sized_slice : (𝒜 # r : Set (Finset α)).Sized r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_slice`：mem_slice : A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r

--- 原说明 ---
Everything in the `r`-th slice of `𝒜` has size `r`.
-/
theorem sized_slice : (𝒜 # r : Set (Finset α)).Sized r := fun _ => And.right ∘ mem_slice.mp
/-
**Finset.eq_of_mem_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_slice (h₁ : A in 𝒜 # r₁) (h₂ : A in 𝒜 # r₂) : r₁ = r₂
参数：h₁ : A in 𝒜 # r₁；h₂ : A in 𝒜 # r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sized_slice`：sized_slice : (𝒜 # r : Set (Finset α)).Sized r
-/
theorem eq_of_mem_slice (h₁ : A ∈ 𝒜 # r₁) (h₂ : A ∈ 𝒜 # r₂) : r₁ = r₂ :=
  (sized_slice h₁).symm.trans <| sized_slice h₂

/-- Elements in distinct slices must be distinct. -/
/-
**Finset.ne_of_mem_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ne_of_mem_slice (h₁ : A₁ in 𝒜 # r₁) (h₂ : A₂ in 𝒜 # r₂) : r₁ != r₂ -> A₁ !
= A₂
参数：h₁ : A₁ in 𝒜 # r₁；h₂ : A₂ in 𝒜 # r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sized_slice`：sized_slice : (𝒜 # r : Set (Finset α)).Sized r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Elements in distinct slices must be distinct.
-/
theorem ne_of_mem_slice (h₁ : A₁ ∈ 𝒜 # r₁) (h₂ : A₂ ∈ 𝒜 # r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  mt fun h => (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))
/-
**Finset.pairwiseDisjoint_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_slice : (Set.univ : Set Nat).PairwiseDisjoint (slice 𝒜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pairwiseDisjoint_slice : (Set.univ : Set ℕ).PairwiseDisjoint (slice 𝒜) := fun _ _ _ _ hmn =>
  disjoint_filter.2 fun _s _hs hm hn => hmn <| hm.symm.trans hn

variable [Fintype α] (𝒜)

@[simp]
/-
**Finset.biUnion_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：biUnion_slice [DecidableEq α] : (Iic <| Fintype.card α).biUnion 𝒜.slice = 
𝒜
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.biUnion_subset`：biUnion_subset {s' : Finset β} : s.biUnion t subs
eteq s' ↔ forall x in s, t x subseteq s'
· 使用定理 `Finset.slice_subset`：slice_subset : 𝒜 # r subseteq 𝒜
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Finset.mem_slice`：mem_slice : A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r
-/
theorem biUnion_slice [DecidableEq α] : (Iic <| Fintype.card α).biUnion 𝒜.slice = 𝒜 :=
  Subset.antisymm (biUnion_subset.2 fun _r _ => slice_subset) fun s hs =>
    mem_biUnion.2 ⟨#s, mem_Iic.2 <| s.card_le_univ, mem_slice.2 <| ⟨hs, rfl⟩⟩

@[simp]
/-
**Finset.sum_card_slice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_card_slice : ∑ r in Iic (Fintype.card α), #(𝒜 # r) = #𝒜
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Set.PairwiseDisjoint.subset`：∀ {α : Type u_1} {ι : Type u_4} [inst : Par
tialOrder α] [inst_1 : OrderBot α] {s t : Set ι} {f : ι → α},   t.PairwiseDisjoi
nt f → s ⊆ t → s.…
· 使用定理 `Finset.pairwiseDisjoint_slice`：pairwiseDisjoint_slice : (Set.univ : Set 
Nat).PairwiseDisjoint (slice 𝒜)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Finset.biUnion_slice`：biUnion_slice [DecidableEq α] : (Iic <| Fintype.ca
rd α).biUnion 𝒜.slice = 𝒜
-/
theorem sum_card_slice : ∑ r ∈ Iic (Fintype.card α), #(𝒜 # r) = #𝒜 := by
  let := Classical.decEq α
  rw [← card_biUnion, biUnion_slice]
  exact Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)

end Slice

end Finset

