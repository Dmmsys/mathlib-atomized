/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.

* `Set.powersetCard α n` is the set of all `Finset α` with cardinality `n`.
  The name is chosen in relation with `Finset.powersetCard` which corresponds to
  the analogous structure for subsets of given cardinality of a given `Finset`, as a `Finset`.

* `Set.powersetCard.card` proves that the `Nat.card`-cardinality
  of this set is equal to `(Nat.card α).choose n`.

-/

@[expose] public section

variable (α : Type*)

/-- The type of combinations of `n` elements of a type `α`.

See also `Finset.powersetCard`. -/
/-
**Set.powersetCard** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.powersetCard (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of combinations of `n` elements of a type `α`.

See also `Finset.powersetCard`.
-/
def Set.powersetCard (n : ℕ) := {s : Finset α | s.card = n}

variable {α} {n : ℕ}

namespace Set.powersetCard

open Finset Set Function

@[simp]
/-
**Set.powersetCard.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：mem_iff {s : Finset α} : s in powersetCard α n ↔ s.card = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.powersetCard.eq_1`：∀ (α : Type u_1) (n : ℕ), Set.powersetCard α n = 
{s | s.card = n}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {s : Finset α} :
    s ∈ powersetCard α n ↔ s.card = n := by
  rw [powersetCard, Set.mem_ofPred_eq]
/-
**Set.powersetCard.** 是 Mathlib 中的一个实例，位于命名空间 `Set.powersetCard`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (powersetCard α n) α := SetLike.instSubtype
/-
**Set.powersetCard.** 是 Mathlib 中的一个实例，位于命名空间 `Set.powersetCard`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Set.powersetCard α n) := .ofSetLike (Set.powersetCard α n) α

@[simp]
/-
**Set.powersetCard.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_coe {s : powersetCard α n} : ((s : Finset α) : Set α) = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe {s : powersetCard α n} :
    ((s : Finset α) : Set α) = s := rfl
/-
**Set.powersetCard.mem_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：mem_coe_iff {s : Set.powersetCard α n} {a : α} : a in (s : Finset α) ↔ a i
n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe_iff {s : Set.powersetCard α n} {a : α} : a ∈ (s : Finset α) ↔ a ∈ s := .rfl

@[simp]
/-
**Set.powersetCard.card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：card_eq (s : Set.powersetCard α n) : (s : Finset α).card = n
参数：s : Set.powersetCard α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem card_eq (s : Set.powersetCard α n) : (s : Finset α).card = n := s.prop

@[simp]
/-
**Set.powersetCard.ncard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：ncard_eq (s : Set.powersetCard α n) : (s : Set α).ncard = n
参数：s : Set.powersetCard α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.powersetCard.coe_coe`：coe_coe {s : powersetCard α n} : ((s : Finset 
α) : Set α) = s
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem ncard_eq (s : Set.powersetCard α n) : (s : Set α).ncard = n := by
  rw [← coe_coe, Set.ncard_coe_finset, s.prop]
/-
**Set.powersetCard.coe_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`
。
形式化陈述：coe_nonempty_iff {s : Set.powersetCard α n} : (s : Set α).Nonempty ↔ 1 <= 
n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.powersetCard.coe_coe`：coe_coe {s : powersetCard α n} : ((s : Finset 
α) : Set α) = s
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.one_le_card`：∀ {α : Type u_1} {s : Finset α}, 1 ≤ s.card ↔ s.None
mpty
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_nonempty_iff {s : Set.powersetCard α n} :
    (s : Set α).Nonempty ↔ 1 ≤ n := by
  rw [← Set.powersetCard.coe_coe, Finset.coe_nonempty, ← one_le_card, s.prop]
/-
**Set.powersetCard.coe_nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCar
d`。
形式化陈述：coe_nontrivial_iff {s : Set.powersetCard α n} : (s : Set α).Nontrivial ↔ 1
 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.powersetCard.coe_coe`：coe_coe {s : powersetCard α n} : ((s : Finset 
α) : Set α) = s
· 使用定理 `Finset.nontrivial_coe`：∀ {α : Type u_1} {s : Finset α}, (↑s).Nontrivial 
↔ s.Nontrivial
· 使用定理 `Finset.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < #s ↔
 s.Nontrivial
· 使用定理 `Set.powersetCard.card_eq`：card_eq (s : Set.powersetCard α n) : (s : Fins
et α).card = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_nontrivial_iff {s : Set.powersetCard α n} :
    (s : Set α).Nontrivial ↔ 1 < n := by
  rw [← coe_coe, Finset.nontrivial_coe, ← one_lt_card_iff_nontrivial, card_eq]
/-
**Set.powersetCard.eq_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：eq_iff_subset {s t : Set.powersetCard α n} : s = t ↔ (s : Finset α) subset
eq (t : Finset α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_iff_eq_of_card_le`：subset_iff_eq_of_card_le (h : #t <= #s)
 : s subseteq t ↔ s = t
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_iff_subset {s t : Set.powersetCard α n} : s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge), Subtype.ext_iff]
/-
**Set.powersetCard.exists_mem_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard
`。
形式化陈述：exists_mem_notMem (hn : 1 <= n) (hα : n < ENat.card α) {a b : α} (hab : a 
!= b) : exists s : powersetCard α n, a in s ∧ b ∉ s
参数：hn : 1 <= n；hα : n < ENat.card α；hab : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.lt_add_one_iff'`：lt_add_one_iff' (hm : m != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.encard_add_encard_compl`：encard_add_encard_compl (s : Set α) : s.enc
ard + sᶜ.encard = (univ : Set α).encard
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用定理 `Set.exists_superset_subset_encard_eq`：exists_superset_subset_encard_eq {
k : Nat∞} (hst : s subseteq t) (hsk : s.encard <= k) (hkt : k <= t.encard) : exi
sts r, s subseteq r ∧ r su…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
· 使用定理 `Set.powersetCard.mem_iff`：mem_iff {s : Finset α} : s in powersetCard α n
 ↔ s.card = n
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `Set.Finite.encard_eq_coe_toFinset_card`：∀ {α : Type u_1} {s : Set α} (h 
: s.Finite), s.encard = ↑h.toFinset.card
-/
theorem exists_mem_notMem (hn : 1 ≤ n) (hα : n < ENat.card α) {a b : α} (hab : a ≠ b) :
    ∃ s : powersetCard α n, a ∈ s ∧ b ∉ s := by
  have ha' : n ≤ Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.natCast_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne.symm hab]) (by simpa) ha'
  have : Set.Finite s := Set.finite_of_encard_eq_coe hs
  exact ⟨⟨Set.Finite.toFinset this, by
    rwa [mem_iff, ← ENat.natCast_inj, ← this.encard_eq_coe_toFinset_card]⟩,
      by simpa using has, by simpa using has'⟩
/-
**Set.powersetCard.exists_mem_notMem_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set.power
setCard`。
形式化陈述：exists_mem_notMem_iff_ne (s t : Set.powersetCard α n) : s != t ↔ exists a 
in s, a ∉ t
参数：s t : Set.powersetCard α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₂`：contrapose_iff₂ {p q : Prop} 
: (p ↔ ¬ q) -> (¬ p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.powersetCard.eq_iff_subset`：eq_iff_subset {s t : Set.powersetCard α 
n} : s = t ↔ (s : Finset α) subseteq (t : Finset α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exists_mem_notMem_iff_ne (s t : Set.powersetCard α n) : s ≠ t ↔ ∃ a ∈ s, a ∉ t := by
  contrapose!
  rw [eq_iff_subset]
  rfl

section map

variable (n) {β : Type*}

/-- The map `powersetCard α n → powersetCard β n` induced by embedding `f : α ↪ β`. -/
/-
**Set.powersetCard.map** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：map (f : α ↪ β) (s : powersetCard α n) : powersetCard β n
参数：f : α ↪ β；s : powersetCard α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `powersetCard α n → powersetCard β n` induced by embedding `f : α ↪ β`.
-/
def map (f : α ↪ β) (s : powersetCard α n) : powersetCard β n :=
    ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩
/-
**Set.powersetCard.mem_map_iff_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Set.powerset
Card`。
形式化陈述：mem_map_iff_mem_range (f : α ↪ β) (s : powersetCard α n) (b : β) : b in ma
p n f s ↔ b in f '' s
参数：f : α ↪ β；s : powersetCard α n；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_map_iff_mem_range (f : α ↪ β) (s : powersetCard α n) (b : β) :
    b ∈ map n f s ↔ b ∈ f '' s := by
  simp [map]
  rfl

@[simp]
/-
**Set.powersetCard.coe_map** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_map (f : α ↪ β) (s : powersetCard α n) : SetLike.coe (map n f s) = f '
' s
参数：f : α ↪ β；s : powersetCard α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_map (f : α ↪ β) (s : powersetCard α n) : SetLike.coe (map n f s) = f '' s := by
  ext
  simp [mem_map_iff_mem_range]

@[simp]
/-
**Set.powersetCard.val_map** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：val_map (f : α ↪ β) (s : powersetCard α n) : Subtype.val (map n f s) = s.v
al.map f
参数：f : α ↪ β；s : powersetCard α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_map (f : α ↪ β) (s : powersetCard α n) : Subtype.val (map n f s) = s.val.map f := rfl

end map

section of

/-- The coercion of a finite set to its corresponding element of `Set.powersetCard`. -/
/-
**Set.powersetCard.ofCard** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：ofCard {s : Finset α} (s_card : s.card = n) : powersetCard α n
参数：s_card : s.card = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion of a finite set to its corresponding element of `Set.powersetCard`.
-/
def ofCard {s : Finset α} (s_card : s.card = n) : powersetCard α n := ⟨s, mem_iff.mpr s_card⟩

@[simp]
/-
**Set.powersetCard.val_ofCard** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：val_ofCard {s : Finset α} (s_card : s.card = n) : Subtype.val (ofCard s_ca
rd) = s
参数：s_card : s.card = n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_ofCard {s : Finset α} (s_card : s.card = n) : Subtype.val (ofCard s_card) = s := rfl

@[simp]
/-
**Set.powersetCard.ofCard_coe** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：ofCard_coe {s : powersetCard α n} (h) : ofCard (s
参数：h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCard_coe {s : powersetCard α n} (h) : ofCard (s := s.val) h = s := rfl

/-- The equivalence sending `a : α` to the singleton `{a}`. -/
/-
**Set.powersetCard.ofSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：ofSingleton : α ≃ powersetCard α 1 where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1

--- 原说明 ---
The equivalence sending `a : α` to the singleton `{a}`.
-/
noncomputable def ofSingleton : α ≃ powersetCard α 1 where
  toFun a := ⟨{a}, Finset.card_singleton a⟩
  invFun s := (Finset.card_eq_one.mp s.prop).choose
  left_inv a := by simp
  right_inv s := by rw [← Subtype.val_inj, (Finset.card_eq_one.mp s.prop).choose_spec]

variable (n) (β : Type*)

/-- The image of an embedding `f : Fin n ↪ β` as an element of `powersetCard β n`. -/
/-
**Set.powersetCard.ofFinEmb** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：ofFinEmb (f : Fin n ↪ β) : powersetCard β n
参数：f : Fin n ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an embedding `f : Fin n ↪ β` as an element of `powersetCard β n`.
-/
def ofFinEmb (f : Fin n ↪ β) : powersetCard β n :=
  map n f ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, Fintype.card_fin]⟩

@[simp]
/-
**Set.powersetCard.mem_ofFinEmb_iff_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Set.pow
ersetCard`。
形式化陈述：mem_ofFinEmb_iff_mem_range (f : Fin n ↪ β) (b : β) : b in ofFinEmb n β f ↔
 b in Set.range f
参数：f : Fin n ↪ β；b : β。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_ofFinEmb_iff_mem_range (f : Fin n ↪ β) (b : β) :
    b ∈ ofFinEmb n β f ↔ b ∈ Set.range f := by
  simp [ofFinEmb, mem_map_iff_mem_range]

@[simp]
/-
**Set.powersetCard.coe_ofFinEmb** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_ofFinEmb (f : Fin n ↪ β) : SetLike.coe (ofFinEmb n β f) = Set.range f
参数：f : Fin n ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_ofFinEmb (f : Fin n ↪ β) : SetLike.coe (ofFinEmb n β f) = Set.range f := by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

@[simp]
/-
**Set.powersetCard.val_ofFinEmb** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：val_ofFinEmb (f : Fin n ↪ β) : Subtype.val (ofFinEmb n β f) = Finset.univ.
map f
参数：f : Fin n ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.powersetCard.coe_ofFinEmb`：coe_ofFinEmb (f : Fin n ↪ β) : SetLike.co
e (ofFinEmb n β f) = Set.range f
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma val_ofFinEmb (f : Fin n ↪ β) :
    Subtype.val (ofFinEmb n β f) = Finset.univ.map f := by
  simp [← coe_inj, coe_ofFinEmb]
/-
**Set.powersetCard.ofFinEmb_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCa
rd`。
形式化陈述：ofFinEmb_surjective : Function.Surjective (ofFinEmb n β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Embedding.exists_of_card_eq_finset`：exists_of_card_eq_finset [F
intype α] {s : Finset β} (hsn : Fintype.card α = s.card) : exists f : α ↪ β, Fin
set.univ.map f = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ofFinEmb_surjective :
    Function.Surjective (ofFinEmb n β) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ β, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

end of

section compl

variable [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)

/-- Complement of `Finset`s as an equivalence on `Set.powersetCard`. -/
/-
**Set.powersetCard.compl** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：compl : powersetCard α n ≃ powersetCard α m where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Complement of `Finset`s as an equivalence on `Set.powersetCard`.
-/
def compl : powersetCard α n ≃ powersetCard α m where
  toFun s := ⟨(sᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp s.2]; omega⟩
  invFun t := ⟨(tᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp t.2]; omega⟩
  left_inv s := by simp
  right_inv t := by simp

variable {hm}

@[simp]
/-
**Set.powersetCard.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_compl {s : powersetCard α n} : (compl hm s : Finset α) = (s : Finset α
)ᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compl {s : powersetCard α n} :
    (compl hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

@[simp]
/-
**Set.powersetCard.mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：mem_compl {s : powersetCard α n} {a : α} : a in compl hm s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
-/
theorem mem_compl {s : powersetCard α n} {a : α} :
    a ∈ compl hm s ↔ a ∉ s :=
  Finset.mem_compl
/-
**Set.powersetCard.compl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：compl_symm : (compl hm).symm = compl ((n.add_comm m).trans hm)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem compl_symm : (compl hm).symm = compl ((n.add_comm m).trans hm) := rfl

end compl

section disjUnion

variable {m : ℕ} {s : powersetCard α m} {t : powersetCard α n} (hst : Disjoint s.val t.val)

/-- The disjoint union of two `powersetCard`s. -/
/-
**Set.powersetCard.disjUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：disjUnion : powersetCard α (m + n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint union of two `powersetCard`s.
-/
def disjUnion : powersetCard α (m + n) :=
  ⟨s.val.disjUnion t hst, by rw [mem_iff, Finset.card_disjUnion, card_eq s, card_eq t]⟩

variable {hst}

@[simp]
/-
**Set.powersetCard.coe_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_disjUnion : (disjUnion hst : Finset α) = s.val.disjUnion t hst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_disjUnion : (disjUnion hst : Finset α) = s.val.disjUnion t hst := rfl

@[simp]
/-
**Set.powersetCard.mem_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：mem_disjUnion {a : α} : a in disjUnion hst ↔ a in s ∨ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_disjUnion`：mem_disjUnion {α s t h a} : a in @disjUnion α s t 
h ↔ a in s ∨ a in t
-/
theorem mem_disjUnion {a : α} : a ∈ disjUnion hst ↔ a ∈ s ∨ a ∈ t :=
  Finset.mem_disjUnion (h := hst)

end disjUnion

variable (α n)

/-
**Set.powersetCard.coe_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_finset [Fintype α] : powersetCard α n = Finset.powersetCard n (Finset.
univ : Finset α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_finset [Fintype α] :
    powersetCard α n = Finset.powersetCard n (Finset.univ : Finset α) := by
  ext; simp
/-
**Set.powersetCard.** 是 Mathlib 中的一个实例，位于命名空间 `Set.powersetCard`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype α] : Fintype (powersetCard α n) := by
  rw [coe_finset]
  infer_instance
/-
**Set.powersetCard.** 是 Mathlib 中的一个实例，位于命名空间 `Set.powersetCard`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] : Finite (powersetCard α n) := by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite
/-
**Set.powersetCard.exist_mem_powersetCard_of_inf** 是 Mathlib 中的一个引理，位于命名空间 `Set.
powersetCard`。
形式化陈述：exist_mem_powersetCard_of_inf (h : 0 < n) [Infinite α] (a : α) : exists s 
in powersetCard α n, a in s
参数：h : 0 < n；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.exists_superset_card_eq`：exists_superset_card_eq [Infinite α] (
s : Finset α) (n : Nat) (hn : #s <= n) : exists t : Finset α, s subseteq t ∧ #t 
= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.powersetCard.mem_iff`：mem_iff {s : Finset α} : s in powersetCard α n
 ↔ s.card = n
-/
lemma exist_mem_powersetCard_of_inf (h : 0 < n) [Infinite α] (a : α) :
    ∃ s ∈ powersetCard α n, a ∈ s := by
  obtain ⟨s, a_mem, s_card⟩ := Infinite.exists_superset_card_eq ({a} : Finset α) n
    (by rw [Finset.card_singleton]; exact h)
  use ↑s
  exact ⟨mem_iff.mp s_card, by simpa using a_mem⟩
/-
**Set.powersetCard.instInfinite** 是 Mathlib 中的一个实例，位于命名空间 `Set.powersetCard`。
形式化陈述：instInfinite [NeZero n] [Infinite α] : Infinite (powersetCard α n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
· 使用定理 `Set.sUnion_eq_univ_iff`：sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = un
iv ↔ forall a, exists b in c, a in b
· 使用引理 `Set.powersetCard.exist_mem_powersetCard_of_inf`：exist_mem_powersetCard_o
f_inf (h : 0 < n) [Infinite α] (a : α) : exists s in powersetCard α n, a in s
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finite.false`：∀ {α : Sort u_1} [Infinite α], Finite α → False
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `Set.Finite.sUnion`：∀ {α : Type u} {s : Set (Set α)}, s.Finite → (∀ t ∈ s
, t.Finite) → (⋃₀ s).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
instance instInfinite [NeZero n] [Infinite α] : Infinite (powersetCard α n) := by
  rw [← not_finite_iff_infinite]
  by_contra finite
  suffices ⋃₀ (SetLike.coe '' powersetCard α n) = Set.univ by
    apply Finite.false (α := α)
    rw [← Set.finite_univ_iff, ← this]
    apply Set.Finite.sUnion (Finite.image SetLike.coe finite)
    aesop
  rw [sUnion_eq_univ_iff]
  intro a
  obtain ⟨s, s_mem, mem_s⟩ := exist_mem_powersetCard_of_inf α n (Nat.pos_of_neZero n) a
  exact ⟨↑s, mem_image_of_mem SetLike.coe s_mem, mem_coe.mpr mem_s⟩
/-
**Set.powersetCard.card** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：∀ (α : Type u_1) (n : ℕ), Nat.card ↑(Set.powersetCard α n) = (Nat.card α).
choose n
参数：α : Type u_1；n : ℕ；Set.powersetCard α n；Nat.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.powersetCard.coe_finset`：coe_finset [Fintype α] : powersetCard α n =
 Finset.powersetCard n (Finset.univ : Finset α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_finset_len`：Fintype.card_finset_len [Fintype α] (k : Nat) :
 Fintype.card { s : Finset α // #s = k } = Nat.choose (Fintype.card α) k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.choose_zero_succ`：choose_zero_succ (k : Nat) : choose 0 (succ k) = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
protected theorem card :
    Nat.card (powersetCard α n) = (Nat.card α).choose n := by
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rw [Nat.card_eq_zero_of_infinite (α := α), Nat.choose_zero_succ]
      exact Nat.card_eq_zero_of_infinite

variable {α n}

/-- If `0 < n < ENat.card α`, then `powersetCard α n` is nontrivial. -/
/-
**Set.powersetCard.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：nontrivial (h1 : 0 < n) (h2 : n < ENat.card α) : Nontrivial (powersetCard 
α n)
参数：h1 : 0 < n；h2 : n < ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nontrivial_coe_sort`：nontrivial_coe_sort {s : Set α} : Nontrivial s 
↔ s.Nontrivial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.one_lt_ncard_iff_nontrivial`：one_lt_ncard_iff_nontrivial [Finite s] 
: 1 < s.ncard ↔ s.Nontrivial
· 使用定理 `Set.powersetCard.instFiniteElemFinset`：∀ (α : Type u_1) (n : ℕ) [Finite 
α], Finite ↑(Set.powersetCard α n)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Set.powersetCard.card`：∀ (α : Type u_1) (n : ℕ), Nat.card ↑(Set.powerset
Card α n) = (Nat.card α).choose n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `Nat.choose_eq_zero_iff`：choose_eq_zero_iff {n k : Nat} : n.choose k = 0 
↔ n < k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.choose_eq_one_iff`：choose_eq_one_iff {n k : Nat} : n.choose k = 1 ↔ 
k = 0 ∨ n = k
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α

--- 原说明 ---
If `0 < n < ENat.card α`, then `powersetCard α n` is nontrivial.
-/
theorem nontrivial (h1 : 0 < n) (h2 : n < ENat.card α) :
    Nontrivial (powersetCard α n) := by
  cases fintypeOrInfinite α
  · rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ← Nat.card_coe_set_eq,
      powersetCard.card]
    by_contra!
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
    rw [ENat.card_eq_coe_natCard] at h2
    norm_cast at h2
    rcases this with h | h
    · rw [Nat.choose_eq_zero_iff] at h
      exact (lt_self_iff_false n).mp (lt_trans h2 h)
    · rw [Nat.choose_eq_one_iff] at h
      aesop
  · have : NeZero n := NeZero.of_pos h1
    infer_instance

/-- A variant of `Set.powersetCard.nontrivial` that uses `Nat.card`. -/
/-
**Set.powersetCard.nontrivial'** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) : Nontrivial (powersetCard 
α n)
参数：h1 : 0 < n；h2 : n < Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.powersetCard.nontrivial`：nontrivial (h1 : 0 < n) (h2 : n < ENat.card
 α) : Nontrivial (powersetCard α n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
A variant of `Set.powersetCard.nontrivial` that uses `Nat.card`.
-/
theorem nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (powersetCard α n) := by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

@[simp]
/-
**Set.powersetCard.eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：eq_empty_iff [Finite α] : powersetCard α n = ∅ ↔ Nat.card α < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.powersetCard.instFiniteElemFinset`：∀ (α : Type u_1) (n : ℕ) [Finite 
α], Finite ↑(Set.powersetCard α n)
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Set.powersetCard.card`：∀ (α : Type u_1) (n : ℕ), Nat.card ↑(Set.powerset
Card α n) = (Nat.card α).choose n
· 使用定理 `Nat.choose_eq_zero_iff`：choose_eq_zero_iff {n k : Nat} : n.choose k = 0 
↔ n < k
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_empty_iff [Finite α] :
    powersetCard α n = ∅ ↔ Nat.card α < n := by
  rw [← Set.ncard_eq_zero, ← _root_.Nat.card_coe_set_eq, powersetCard.card, Nat.choose_eq_zero_iff]
/-
**Set.powersetCard.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：nontrivial_iff [Finite α] : Nontrivial (powersetCard α n) ↔ 0 < n ∧ n < Na
t.card α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `Set.powersetCard.instFiniteElemFinset`：∀ (α : Type u_1) (n : ℕ) [Finite 
α], Finite ↑(Set.powersetCard α n)
· 使用定理 `Set.powersetCard.card`：∀ (α : Type u_1) (n : ℕ), Nat.card ↑(Set.powerset
Card α n) = (Nat.card α).choose n
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.choose_eq_zero_iff`：choose_eq_zero_iff {n k : Nat} : n.choose k = 0 
↔ n < k
· 使用定理 `Nat.choose_eq_one_iff`：choose_eq_one_iff {n k : Nat} : n.choose k = 1 ↔ 
k = 0 ∨ n = k
-/
theorem nontrivial_iff [Finite α] :
    Nontrivial (powersetCard α n) ↔ 0 < n ∧ n < Nat.card α := by
  rw [← Finite.one_lt_card_iff_nontrivial, powersetCard.card, Nat.one_lt_iff_ne_zero_and_ne_one,
    ne_eq, Nat.choose_eq_zero_iff, ne_eq, Nat.choose_eq_one_iff]
  grind

/-- The bijection between the product of `(n : ℕ)` and the finsets of `α` of cardinality `n` and
`Finset α`. -/
/-
**Set.powersetCard.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：prodEquiv : (n : Nat) × (powersetCard α n) ≃ Finset α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the product of `(n : ℕ)` and the finsets of `α` of cardina
lity `n` and
`Finset α`.
-/
def prodEquiv : (n : ℕ) × (powersetCard α n) ≃ Finset α where
  toFun x := x.2
  invFun x := ⟨x.card, ⟨x, rfl⟩⟩
  left_inv x := by ext <;> simp

@[simp]
/-
**Set.powersetCard.prodEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCard`。
形式化陈述：prodEquiv_apply (x : (n : Nat) × (powersetCard α n)) : prodEquiv x = x.2
参数：x : (n : Nat) × (powersetCard α n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodEquiv_apply (x : (n : ℕ) × (powersetCard α n)) : prodEquiv x = x.2 := rfl

@[simp]
/-
**Set.powersetCard.prodEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetC
ard`。
形式化陈述：prodEquiv_symm_apply (s : Finset α) : prodEquiv.symm s = ⟨s.card, ofCard r
fl⟩
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma prodEquiv_symm_apply (s : Finset α) : prodEquiv.symm s = ⟨s.card, ofCard rfl⟩ := rfl

end Set.powersetCard

