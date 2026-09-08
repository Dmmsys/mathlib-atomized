/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert

/-!
# Disjoint finite sets

## Main declarations

* `Disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `Finset.disjUnion`: the union of the finite sets `s` and `t`, given a proof `Disjoint s t`

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

variable {ι α β γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### disjoint -/


section Disjoint

variable {f : α → β} {s t u : Finset α} {a b : α}

/-
**Finset.disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> a ∉ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht => notMem_empty a <|
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩

alias ⟨_root_.Disjoint.notMem_of_mem_left_finset, _⟩ := disjoint_left
/-
**Finset.disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -> a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by
  rw [_root_.disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right_finset, _⟩ := disjoint_right
/-
**Finset.disjoint_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_iff_ne : Disjoint s t ↔ forall a in s, forall b in t, a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_iff_ne : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']

@[simp]
/-
**Finset.disjoint_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_val : Disjoint s.1 t.1 ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
-/
theorem disjoint_val : Disjoint s.1 t.1 ↔ Disjoint s t :=
  Multiset.disjoint_left.trans disjoint_left.symm
/-
**Finset._root_.Disjoint.forall_ne_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.forall_ne_finset (h : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  disjoint_iff_ne.1 h _ ha _ hb
/-
**Finset.not_disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_disjoint_iff : ¬Disjoint s t ↔ exists a, a in s ∧ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  disjoint_left.not.trans <| not_forall.trans <| exists_congr fun _ => by
    rw [Classical.not_imp, not_not]
/-
**Finset.disjoint_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_of_subset_left (h : s subseteq u) (d : Disjoint u t) : Disjoint s
 t
参数：h : s subseteq u；d : Disjoint u t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun _x m₁ => (disjoint_left.1 d) (h m₁)
/-
**Finset.disjoint_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_of_subset_right (h : t subseteq u) (d : Disjoint s u) : Disjoint 
s t
参数：h : t subseteq u；d : Disjoint s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun _x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]
/-
**Finset.disjoint_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_empty_left (s : Finset α) : Disjoint ∅ s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
-/
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left

@[simp]
/-
**Finset.disjoint_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_empty_right (s : Finset α) : Disjoint s ∅
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_right`：disjoint_bot_right : Disjoint a ⊥
-/
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right

-- Higher priority than `disjoint_singleton_right` to make sure `Disjoint {a} {b}`
-- simplifies to `a ≠ b`.
@[simp default + 1]
/-
**Finset.disjoint_singleton_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s := by
  simp only [disjoint_left, mem_singleton, forall_eq]

@[simp]
/-
**Finset.disjoint_singleton_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
-/
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left

-- Not `simp` since `disjoint_singleton_{left,right}` prove it.
/-
**Finset.disjoint_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton]
/-
**Finset.disjoint_self_iff_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
-/
theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self

@[simp, norm_cast]
/-
**Finset.disjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]

@[simp, norm_cast]
/-
**Finset.pairwiseDisjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_coe {ι : Type*} {s : Set ι} {f : ι -> Finset α} : s.Pairw
iseDisjoint (fun i => f i : ι -> Set α) ↔ s.PairwiseDisjoint f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₅_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {ε : (a : α) → (b : β a
) →…
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
-/
theorem pairwiseDisjoint_coe {ι : Type*} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint (fun i => f i : ι → Set α) ↔ s.PairwiseDisjoint f :=
  forall₅_congr fun _ _ _ _ _ => disjoint_coe
/-
**Finset.pairwiseDisjoint_singleton_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {s : Set ι} {f : ι → α}, (s.PairwiseDisjoi
nt fun i => {f i}) ↔ Set.InjOn f s
参数：s.PairwiseDisjoint fun i => {f i}。
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
@[simp] lemma pairwiseDisjoint_singleton_iff_injOn {s : Set ι} {f : ι → α} :
    s.PairwiseDisjoint (fun i ↦ ({f i} : Finset α)) ↔ s.InjOn f := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_not, Set.InjOn]

variable [DecidableEq α]
/-
**Finset.decidableDisjoint** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V)
参数：U V : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidable_of_iff _ disjoint_left.symm

end Disjoint

/-! ### disjoint union -/


/-- `disjUnion s t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
@[simps]
/-
**Finset.disjUnion** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：disjUnion (s t : Finset α) (h : Disjoint s t) : Finset α
参数：s t : Finset α；h : Disjoint s t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`disjUnion s t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈
 t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the typ
e. The hypothesis
ensures that the sets are disjoint.
-/
def disjUnion (s t : Finset α) (h : Disjoint s t) : Finset α :=
  ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩

@[simp, grind =]
/-
**Finset.mem_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_disjUnion {α s t h a} : a in @disjUnion α s t h ↔ a in s ∨ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
-/
theorem mem_disjUnion {α s t h a} : a ∈ @disjUnion α s t h ↔ a ∈ s ∨ a ∈ t := by
  rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply List.mem_append

@[simp, norm_cast]
/-
**Finset.coe_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_disjUnion {s t : Finset α} (h : Disjoint s t) : (disjUnion s t h : Set
 α) = (s : Set α) union t
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_disjUnion {s t : Finset α} (h : Disjoint s t) :
    (disjUnion s t h : Set α) = (s : Set α) ∪ t :=
  Set.ext <| by simp
/-
**Finset.disjUnion_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_comm (s t : Finset α) (h : Disjoint s t) : disjUnion s t h = dis
jUnion t s h.symm
参数：s t : Finset α；h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
-/
theorem disjUnion_comm (s t : Finset α) (h : Disjoint s t) :
    disjUnion s t h = disjUnion t s h.symm :=
  eq_of_veq <| Multiset.add_comm _ _

@[simp]
/-
**Finset.disjUnion_inj_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_inj_left {s₁ s₂ t : Finset α} (h₁ : Disjoint s₁ t) (h₂ : Disjoin
t s₂ t) : s₁.disjUnion t h₁ = s₂.disjUnion t h₂ ↔ s₁ = s₂
参数：h₁ : Disjoint s₁ t；h₂ : Disjoint s₂ t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjUnion_val`：∀ {α : Type u_2} (s t : Finset α) (h : Disjoint s 
t), (s.disjUnion t h).val = s.val + t.val
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjUnion_inj_left {s₁ s₂ t : Finset α} (h₁ : Disjoint s₁ t) (h₂ : Disjoint s₂ t) :
    s₁.disjUnion t h₁ = s₂.disjUnion t h₂ ↔ s₁ = s₂ := by
  simp [← val_inj, Multiset.add_left_inj]

@[simp]
/-
**Finset.disjUnion_inj_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_inj_right {s t₁ t₂ : Finset α} (h₁ : Disjoint s t₁) (h₂ : Disjoi
nt s t₂) : s.disjUnion t₁ h₁ = s.disjUnion t₂ h₂ ↔ t₁ = t₂
参数：h₁ : Disjoint s t₁；h₂ : Disjoint s t₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjUnion_val`：∀ {α : Type u_2} (s t : Finset α) (h : Disjoint s 
t), (s.disjUnion t h).val = s.val + t.val
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjUnion_inj_right {s t₁ t₂ : Finset α} (h₁ : Disjoint s t₁) (h₂ : Disjoint s t₂) :
    s.disjUnion t₁ h₁ = s.disjUnion t₂ h₂ ↔ t₁ = t₂ := by
  simp [← val_inj, Multiset.add_right_inj]

@[simp]
/-
**Finset.empty_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_disjUnion (t : Finset α) (h : Disjoint ∅ t
参数：t : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
-/
theorem empty_disjUnion (t : Finset α) (h : Disjoint ∅ t := disjoint_bot_left) :
    disjUnion ∅ t h = t :=
  eq_of_veq <| Multiset.zero_add _

@[simp]
/-
**Finset.disjUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_empty (s : Finset α) (h : Disjoint s ∅
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
-/
theorem disjUnion_empty (s : Finset α) (h : Disjoint s ∅ := disjoint_bot_right) :
    disjUnion s ∅ h = s :=
  eq_of_veq <| Multiset.add_zero _
/-
**Finset.singleton_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_disjUnion (a : α) (t : Finset α) (h : Disjoint {a} t) : disjUnio
n {a} t h = cons a t (disjoint_singleton_left.mp h)
参数：a : α；t : Finset α；h : Disjoint {a} t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
-/
theorem singleton_disjUnion (a : α) (t : Finset α) (h : Disjoint {a} t) :
    disjUnion {a} t h = cons a t (disjoint_singleton_left.mp h) :=
  eq_of_veq <| Multiset.singleton_add _ _
/-
**Finset.disjUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_singleton (s : Finset α) (a : α) (h : Disjoint s {a}) : disjUnio
n s {a} h = cons a s (disjoint_singleton_right.mp h)
参数：s : Finset α；a : α；h : Disjoint s {a}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjUnion_comm`：disjUnion_comm (s t : Finset α) (h : Disjoint s t
) : disjUnion s t h = disjUnion t s h.symm
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `Finset.singleton_disjUnion`：singleton_disjUnion (a : α) (t : Finset α) (
h : Disjoint {a} t) : disjUnion {a} t h = cons a t (disjoint_singleton_left.mp h
)
-/
theorem disjUnion_singleton (s : Finset α) (a : α) (h : Disjoint s {a}) :
    disjUnion s {a} h = cons a s (disjoint_singleton_right.mp h) := by
  rw [disjUnion_comm, singleton_disjUnion]

/-! ### insert -/

section Insert

variable [DecidableEq α] {s t u v : Finset α} {a b : α} {f : α → β}

@[simp, grind =]
/-
**Finset.disjoint_insert_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]

@[simp, grind =]
/-
**Finset.disjoint_insert_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_insert_left`：disjoint_insert_left : Disjoint (insert a s
) t ↔ a ∉ t ∧ Disjoint s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  disjoint_comm.trans <| by rw [disjoint_insert_left, _root_.disjoint_comm]

end Insert

end Finset

namespace Multiset

variable [DecidableEq α]

@[simp]
/-
**Multiset.disjoint_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_toFinset {m1 m2 : Multiset α} : _root_.Disjoint m1.toFinset m2.to
Finset ↔ Disjoint m1 m2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_toFinset {m1 m2 : Multiset α} :
    _root_.Disjoint m1.toFinset m2.toFinset ↔ Disjoint m1 m2 := by
  simp [disjoint_left, Finset.disjoint_left]

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

@[simp]
/-
**List.disjoint_toFinset_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：disjoint_toFinset_iff_disjoint : _root_.Disjoint l.toFinset l'.toFinset ↔ 
l.Disjoint l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.disjoint_toFinset`：disjoint_toFinset {m1 m2 : Multiset α} : _ro
ot_.Disjoint m1.toFinset m2.toFinset ↔ Disjoint m1 m2
· 使用定理 `Multiset.coe_disjoint`：coe_disjoint (l₁ l₂ : List α) : Disjoint (l₁ : Mu
ltiset α) l₂ ↔ l₁.Disjoint l₂
-/
theorem disjoint_toFinset_iff_disjoint : _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_toFinset.trans (Multiset.coe_disjoint _ _)

end List

