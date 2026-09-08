/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Finite.Powerset

/-!
# Noncomputable Set Cardinality

We define the cardinality of set `s` as a term `Set.encard s : ℕ∞` and a term `Set.ncard s : ℕ`.
The latter takes the junk value of zero if `s` is infinite. Both functions are noncomputable, and
are defined in terms of `ENat.card` (which takes a type as its argument); this file can be seen
as an API for the same function in the special case where the type is a coercion of a `Set`,
allowing for smoother interactions with the `Set` API.

`Set.encard` never takes junk values, so is more mathematically natural than `Set.ncard`, even
though it takes values in a less convenient type. It is probably the right choice in settings where
one is concerned with the cardinalities of sets that may or may not be infinite.

`Set.ncard` has a nicer codomain, but when using it, `Set.Finite` hypotheses are normally needed to
make sure its values are meaningful.  More generally, `Set.ncard` is intended to be used over the
obvious alternative `Finset.card` when finiteness is 'propositional' rather than 'structural'.
When working with sets that are finite by virtue of their definition, then `Finset.card` probably
makes more sense. One setting where `Set.ncard` works nicely is in a type `α` with `[Finite α]`,
where every set is automatically finite. In this setting, we use default arguments and a simple
tactic so that finiteness goals are discharged automatically in `Set.ncard` theorems.

## Main Definitions

* `Set.encard s` is the cardinality of the set `s` as an extended natural number, with value `⊤` if
    `s` is infinite.
* `Set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is Finite.
  If `s` is Infinite, then `Set.ncard s = 0`.
* `toFinite_tac` is a tactic that tries to synthesize a `Set.Finite s` argument with
  `Set.toFinite`. This will work for `s : Set α` where there is a `Finite α` instance.

## Implementation Notes

The theorems in this file are very similar to those in `Mathlib/Data/Finset/Card.lean`, but with
`Set` operations instead of `Finset`. We first prove all the theorems for `Set.encard`, and then
derive most of the `Set.ncard` results as a consequence. Things are done this way to avoid reliance
on the `Finset` API for theorems about infinite sets, and to allow for a refactor that removes or
modifies `Set.ncard` in the future.

Nearly all the theorems for `Set.ncard` require finiteness of one or more of their arguments. We
provide this assumption with a default argument of the form `(hs : s.Finite := by toFinite_tac)`,
where `toFinite_tac` will find an `s.Finite` term in the cases where `s` is a set in a `Finite`
type.

Often, where there are two set arguments `s` and `t`, the finiteness of one follows from the other
in the context of the theorem, in which case we only include the ones that are needed, and derive
the other inside the proof. A few of the theorems, such as `ncard_union_le` do not require
finiteness arguments; they are true by coincidence due to junk values.
-/

@[expose] public section

namespace Set

variable {α β : Type*} {s t : Set α}

/-- The cardinality of a set as a term in `ℕ∞` -/
/-
**Set.encard** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：encard (s : Set α) : Nat∞
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of a set as a term in `ℕ∞`
-/
noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s
/-
**Set.encard_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (α : Type u_3), Set.univ.encard = ENat.card α
参数：α : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
-/
@[simp] theorem encard_univ (α : Type*) :
    encard (univ : Set α) = ENat.card α := by
  rw [encard, ENat.card_congr (Equiv.Set.univ α)]
/-
**Set._root_.ENat.card_coe_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.ENat.card_coe_set_eq (s : Set α) : ENat.card s = s.encard := rfl
/-
**Set.Finite.encard_eq_coe_toFinset_card** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α} (h : s.Finite), s.encard = ↑h.toFinset.card
参数：h : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem Finite.encard_eq_coe_toFinset_card (h : s.Finite) : s.encard = h.toFinset.card := by
  have := h.fintype
  rw [encard, ENat.card_eq_coe_fintype_card, toFinite_toFinset, toFinset_card]
/-
**Set.encard_eq_coe_toFinset_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_coe_toFinset_card (s : Set α) [Fintype s] : encard s = s.toFinse
t.card
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.encard_eq_coe_toFinset_card`：∀ {α : Type u_1} {s : Set α} (h 
: s.Finite), s.encard = ↑h.toFinset.card
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
-/
theorem encard_eq_coe_toFinset_card (s : Set α) [Fintype s] : encard s = s.toFinset.card := by
  have h := toFinite s
  rw [h.encard_eq_coe_toFinset_card, toFinite_toFinset]
/-
**Set.toENat_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s : Set α), Cardinal.toENat (Cardinal.mk ↑s) = s.encard
参数：s : Set α；Cardinal.mk ↑s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toENat_cardinalMk (s : Set α) : (Cardinal.mk s).toENat = s.encard := rfl
/-
**Set.toENat_cardinalMk_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toENat_cardinalMk_subtype (P : α -> Prop) : (Cardinal.mk {x // P x}).toENa
t = {x | P x}.encard
参数：P : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toENat_cardinalMk_subtype (P : α → Prop) :
    (Cardinal.mk {x // P x}).toENat = {x | P x}.encard :=
  rfl

variable (s) in
/-
**Set.coe_fintypeCard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_fintypeCard [Fintype s] : Fintype.card s = s.encard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_eq_coe_toFinset_card`：encard_eq_coe_toFinset_card (s : Set α)
 [Fintype s] : encard s = s.toFinset.card
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_fintypeCard [Fintype s] : Fintype.card s = s.encard := by
  simp [encard_eq_coe_toFinset_card]
/-
**Set.encard_coe_eq_coe_finsetCard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), (↑s).encard = ↑s.card
参数：s : Finset α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.encard_eq_coe_toFinset_card`：∀ {α : Type u_1} {s : Set α} (h 
: s.Finite), s.encard = ↑h.toFinset.card
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] theorem encard_coe_eq_coe_finsetCard (s : Finset α) :
    encard (s : Set α) = s.card := by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp
/-
**Set.Infinite.encard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.encard = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
-/
@[simp] theorem Infinite.encard_eq {s : Set α} (h : s.Infinite) : s.encard = ⊤ := by
  have := h.to_subtype
  rw [encard, ENat.card_eq_top_of_infinite]
/-
**Set.encard_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card_eq_zero_iff_empty`：card_eq_zero_iff_empty (α : Type*) : card α
 = 0 ↔ IsEmpty α
· 使用定理 `isEmpty_subtype`：isEmpty_subtype (p : α -> Prop) : IsEmpty (Subtype p) ↔
 forall x, ¬p x
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [encard, ENat.card_eq_zero_iff_empty, isEmpty_subtype, eq_empty_iff_forall_notMem]
/-
**Set.encard_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1}, ∅.encard = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
-/
@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by
  rw [encard_eq_zero]
/-
**Set.nonempty_of_encard_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_encard_ne_zero (h : s.encard != 0) : s.Nonempty
参数：h : s.encard != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
-/
theorem nonempty_of_encard_ne_zero (h : s.encard ≠ 0) : s.Nonempty := by
  rwa [nonempty_iff_ne_empty, Ne, ← encard_eq_zero]
/-
**Set.encard_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_ne_zero : s.encard != 0 ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem encard_ne_zero : s.encard ≠ 0 ↔ s.Nonempty := by
  rw [ne_eq, encard_eq_zero, nonempty_iff_ne_empty]
/-
**Set.encard_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, 0 < s.encard ↔ s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Set.encard_ne_zero`：encard_ne_zero : s.encard != 0 ↔ s.Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem encard_pos : 0 < s.encard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, encard_ne_zero]

protected alias ⟨_, Nonempty.encard_pos⟩ := encard_pos
/-
**Set.encard_ne_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_ne_zero_of_mem {a : α} (h : a in s) : s.encard != 0
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.encard_pos`：∀ {α : Type u_1} {s : Set α}, 0 < s.encard ↔ s.Nonempty
-/
theorem encard_ne_zero_of_mem {a : α} (h : a ∈ s) : s.encard ≠ 0 :=
  (encard_pos.mpr ⟨a, h⟩).ne.symm
/-
**Set.encard_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (e : α), {e}.encard = 1
参数：e : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Set.card_singleton`：card_singleton (a : α) : Fintype.card ({a} : Set α) 
= 1
· 使用定理 `Nat.cast_eq_one`：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
@[simp] theorem encard_singleton (e : α) : ({e} : Set α).encard = 1 := by
  rw [encard, ENat.card_eq_coe_fintype_card, card_singleton, Nat.cast_eq_one]
/-
**Set.encard_union_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_union_eq (h : Disjoint s t) : (s union t).encard = s.encard + t.enc
ard
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
· 使用定理 `ENat.card_sum`：card_sum (α β : Type*) : card (α oplus β) = card α + card
 β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem encard_union_eq (h : Disjoint s t) : (s ∪ t).encard = s.encard + t.encard := by
  classical
  unfold encard
  simp [ENat.card_congr (Equiv.Set.union h)]
/-
**Set.encard_ne_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_ne_add_one (a : α) : ({x | x != a}).encard + 1 = ENat.card α
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
theorem encard_ne_add_one (a : α) :
    ({x | x ≠ a}).encard + 1 = ENat.card α := by
  have : Disjoint {x | x ≠ a} {a} := disjoint_singleton_right.mpr <| by simp
  replace this := (Set.encard_union_eq this).symm
  have aux : {x | x ≠ a} ∪ {a} = univ := by ext x; simp [eq_or_ne x a]
  rwa [encard_singleton, aux, encard_univ] at this
/-
**Set.encard_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_insert_of_notMem {a : α} (has : a ∉ s) : (insert a s).encard = s.en
card + 1
参数：has : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
theorem encard_insert_of_notMem {a : α} (has : a ∉ s) : (insert a s).encard = s.encard + 1 := by
  rw [← union_singleton, encard_union_eq (by simpa), encard_singleton]
/-
**Set.Finite.encard_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Finite → s.encard < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
-/
theorem Finite.encard_lt_top (h : s.Finite) : s.encard < ⊤ := by
  induction s, h using Set.Finite.induction_on with
  | empty => simp
  | insert hat _ ht' =>
    rw [encard_insert_of_notMem hat]
    exact lt_tsub_iff_right.1 ht'
/-
**Set.Finite.encard_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Finite → s.encard = ↑s.encard.toNat
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
-/
theorem Finite.encard_eq_coe (h : s.Finite) : s.encard = ENat.toNat s.encard :=
  (ENat.natCast_toNat h.encard_lt_top.ne).symm
/-
**Set.Finite.exists_encard_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Finite → ∃ n, s.encard = ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.encard_eq_coe`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard = ↑s.encard.toNat
-/
theorem Finite.exists_encard_eq_coe (h : s.Finite) : ∃ (n : ℕ), s.encard = n :=
  ⟨_, h.encard_eq_coe⟩
/-
**Set.encard_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.encard < ⊤ ↔ s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Infinite.encard_eq`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.enc
ard = ⊤
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
-/
@[simp] theorem encard_lt_top_iff : s.encard < ⊤ ↔ s.Finite :=
  ⟨fun h ↦ by_contra fun h' ↦ h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩
/-
**Set.encard_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.encard = ⊤ ↔ s.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Set.encard_lt_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard < ⊤ ↔ s.Fi
nite
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem encard_eq_top_iff : s.encard = ⊤ ↔ s.Infinite := by
  contrapose!
  rw [← lt_top_iff_ne_top, encard_lt_top_iff]

alias ⟨_, encard_eq_top⟩ := encard_eq_top_iff
/-
**Set.encard_ne_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
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
theorem encard_ne_top_iff : s.encard ≠ ⊤ ↔ s.Finite := by
  simp
/-
**Set.finite_of_encard_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_of_encard_le_coe {k : Nat} (h : s.encard <= k) : s.Finite
参数：h : s.encard <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_lt_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard < ⊤ ↔ s.Fi
nite
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem finite_of_encard_le_coe {k : ℕ} (h : s.encard ≤ k) : s.Finite := by
  rw [← encard_lt_top_iff]; exact h.trans_lt (WithTop.coe_lt_top _)
/-
**Set.finite_of_encard_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_of_encard_eq_coe {k : Nat} (h : s.encard = k) : s.Finite
参数：h : s.encard = k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_encard_le_coe`：finite_of_encard_le_coe {k : Nat} (h : s.en
card <= k) : s.Finite
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem finite_of_encard_eq_coe {k : ℕ} (h : s.encard = k) : s.Finite :=
  finite_of_encard_le_coe h.le
/-
**Set.encard_le_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_coe_iff {k : Nat} : s.encard <= k ↔ s.Finite ∧ exists (n₀ : Nat)
, s.encard = n₀ ∧ n₀ <= k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_encard_le_coe`：finite_of_encard_le_coe {k : Nat} (h : s.en
card <= k) : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.le_natCast_iff`：le_natCast_iff {n : Nat∞} {k : Nat} : n <= ↑k ↔ exi
sts (n₀ : Nat), n = n₀ ∧ n₀ <= k
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem encard_le_coe_iff {k : ℕ} : s.encard ≤ k ↔ s.Finite ∧ ∃ (n₀ : ℕ), s.encard = n₀ ∧ n₀ ≤ k :=
  ⟨fun h ↦ ⟨finite_of_encard_le_coe h, by rwa [ENat.le_natCast_iff] at h⟩,
    fun ⟨_,⟨n₀,hs, hle⟩⟩ ↦ by rwa [hs, Nat.cast_le]⟩

@[simp]
/-
**Set.encard_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_prod {s : Set α} {t : Set β} : (s ×ˢ t).encard = s.encard * t.encar
d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
· 使用定理 `ENat.card_prod`：card_prod (α β : Type*) : card (α × β) = card α * card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem encard_prod {s : Set α} {t : Set β} : (s ×ˢ t).encard = s.encard * t.encard := by
  unfold encard
  simp [ENat.card_congr (Equiv.Set.prod ..)]

@[simp]
/-
**Set.encard_pi_eq_prod_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_pi_eq_prod_encard [h : Fintype α] {ι : α -> Type*} {s : forall i : 
α, Set (ι i)} : (Set.pi Set.univ s).encard = ∏ i, (s i).encard
参数：ι i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `Cardinal.prod_eq_of_fintype`：prod_eq_of_fintype {α : Type u} [h : Fintyp
e α] (f : α -> Cardinal.{v}) : prod f = Cardinal.lift.{u} (∏ i, f i)
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem encard_pi_eq_prod_encard [h : Fintype α] {ι : α → Type*} {s : ∀ i : α, Set (ι i)} :
    (Set.pi Set.univ s).encard = ∏ i, (s i).encard := by
  unfold encard ENat.card
  simp [Cardinal.mk_congr (Equiv.Set.univPi s), Cardinal.prod_eq_of_fintype]

section Lattice

@[gcongr]
/-
**Set.encard_le_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_encard (h : s subseteq t) : s.encard <= t.encard
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem encard_le_encard (h : s ⊆ t) : s.encard ≤ t.encard := by
  rw [← union_sdiff_cancel h, encard_union_eq disjoint_sdiff_right]; exact le_self_add
/-
**Set.encard_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_card : s.encard <= ENat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
-/
theorem encard_le_card : s.encard ≤ ENat.card α :=
  encard_univ _ ▸ encard_le_encard s.subset_univ
/-
**Set.encard_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_mono {α : Type*} : Monotone (encard : Set α -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
-/
theorem encard_mono {α : Type*} : Monotone (encard : Set α → ℕ∞) :=
  fun _ _ ↦ encard_le_encard
/-
**Set.encard_sdiff_add_encard_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_sdiff_add_encard_of_subset (h : s subseteq t) : (t \ s).encard + s.
encard = t.encard
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
-/
theorem encard_sdiff_add_encard_of_subset (h : s ⊆ t) : (t \ s).encard + s.encard = t.encard := by
  rw [← encard_union_eq disjoint_sdiff_left, sdiff_union_of_subset h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_of_subset := encard_sdiff_add_encard_of_subset
/-
**Set.encard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_sdiff (h : s subseteq t) (hs : s.Finite) : (t \ s).encard = t.encar
d - s.encard
参数：h : s subseteq t；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_of_subset`：encard_sdiff_add_encard_of_subset
 (h : s subseteq t) : (t \ s).encard + s.encard = t.encard
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable c → a…
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
-/
theorem encard_sdiff (h : s ⊆ t) (hs : s.Finite) :
    (t \ s).encard = t.encard - s.encard := by
  rw [← @Set.encard_sdiff_add_encard_of_subset _ s t h]
  exact (ENat.addLECancellable_of_ne_top <| encard_ne_top_iff.mpr hs).eq_tsub_of_add_eq rfl

@[deprecated (since := "2026-06-03")] alias encard_diff := encard_sdiff
/-
**Set.one_le_encard_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, 1 ≤ s.encard ↔ s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem one_le_encard_iff_nonempty : 1 ≤ s.encard ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, Ne, ← encard_eq_zero, Order.one_le_iff_ne_zero]
/-
**Set.encard_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_lt_one : s.encard < 1 ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma encard_lt_one : s.encard < 1 ↔ s = ∅ := by simp
/-
**Set.encard_sdiff_add_encard_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_sdiff_add_encard_inter (s t : Set α) : (s \ t).encard + (s inter t)
.encard = s.encard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_sdiff_inter`：disjoint_sdiff_inter : Disjoint (s \ t) (s int
er t)
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
-/
theorem encard_sdiff_add_encard_inter (s t : Set α) :
    (s \ t).encard + (s ∩ t).encard = s.encard := by
  rw [← encard_union_eq disjoint_sdiff_inter, sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_inter := encard_sdiff_add_encard_inter
/-
**Set.encard_union_add_encard_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_union_add_encard_inter (s t : Set α) : (s union t).encard + (s inte
r t).encard = s.encard + t.encard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Set.encard_sdiff_add_encard_inter`：encard_sdiff_add_encard_inter (s t : 
Set α) : (s \ t).encard + (s inter t).encard = s.encard
-/
theorem encard_union_add_encard_inter (s t : Set α) :
    (s ∪ t).encard + (s ∩ t).encard = s.encard + t.encard := by
  rw [← sdiff_union_self, encard_union_eq disjoint_sdiff_left, add_right_comm,
    encard_sdiff_add_encard_inter]
/-
**Set.encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff** 是 Mathlib 中的一个定理，位于命名空
间 `Set`。
形式化陈述：encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff (h : (s inter t).Finite)
 : s.encard = t.encard ↔ (s \ t).encard = (t \ s).encard
参数：h : (s inter t).Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_inter`：encard_sdiff_add_encard_inter (s t : 
Set α) : (s \ t).encard + (s inter t).encard = s.encard
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `AddLECancellable.inj_left`：∀ {α : Type u_1} [inst : Add α] [IsAddCommuta
tive α] [inst_2 : PartialOrder α] {a b c : α},   AddLECancellable c → (a + c = b
 + c ↔ a = b)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ENat.addLECancellable_of_lt_top`：addLECancellable_of_lt_top : a < ⊤ -> A
ddLECancellable a
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff (h : (s ∩ t).Finite) :
    s.encard = t.encard ↔ (s \ t).encard = (t \ s).encard := by
  rw [← encard_sdiff_add_encard_inter s t, ← encard_sdiff_add_encard_inter t s, inter_comm t s,
    (ENat.addLECancellable_of_lt_top h.encard_lt_top).inj_left]

@[deprecated (since := "2026-06-03")]
alias encard_eq_encard_iff_encard_diff_eq_encard_diff :=
  encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff
/-
**Set.encard_le_encard_iff_encard_sdiff_le_encard_sdiff** 是 Mathlib 中的一个定理，位于命名空
间 `Set`。
形式化陈述：encard_le_encard_iff_encard_sdiff_le_encard_sdiff (h : (s inter t).Finite)
 : s.encard <= t.encard ↔ (s \ t).encard <= (t \ s).encard
参数：h : (s inter t).Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_inter`：encard_sdiff_add_encard_inter (s t : 
Set α) : (s \ t).encard + (s inter t).encard = s.encard
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ENat.add_le_add_iff_right`：add_le_add_iff_right {m n k : ENat} (h : k !=
 ⊤) : n + k <= m + k ↔ n <= m
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem encard_le_encard_iff_encard_sdiff_le_encard_sdiff (h : (s ∩ t).Finite) :
    s.encard ≤ t.encard ↔ (s \ t).encard ≤ (t \ s).encard := by
  rw [← encard_sdiff_add_encard_inter s t, ← encard_sdiff_add_encard_inter t s, inter_comm t s,
    ENat.add_le_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_iff_encard_diff_le_encard_diff :=
  encard_le_encard_iff_encard_sdiff_le_encard_sdiff
/-
**Set.encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff** 是 Mathlib 中的一个定理，位于命名空
间 `Set`。
形式化陈述：encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff (h : (s inter t).Finite)
 : s.encard < t.encard ↔ (s \ t).encard < (t \ s).encard
参数：h : (s inter t).Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_inter`：encard_sdiff_add_encard_inter (s t : 
Set α) : (s \ t).encard + (s inter t).encard = s.encard
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `ENat.add_lt_add_iff_right`：add_lt_add_iff_right {k : Nat∞} (h : k != ⊤) 
: n + k < m + k ↔ n < m
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff (h : (s ∩ t).Finite) :
    s.encard < t.encard ↔ (s \ t).encard < (t \ s).encard := by
  rw [← encard_sdiff_add_encard_inter s t, ← encard_sdiff_add_encard_inter t s, inter_comm t s,
    ENat.add_lt_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_lt_encard_iff_encard_diff_lt_encard_diff :=
  encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff
/-
**Set.encard_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_union_le (s t : Set α) : (s union t).encard <= s.encard + t.encard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_union_add_encard_inter`：encard_union_add_encard_inter (s t : 
Set α) : (s union t).encard + (s inter t).encard = s.encard + t.encard
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem encard_union_le (s t : Set α) : (s ∪ t).encard ≤ s.encard + t.encard := by
  rw [← encard_union_add_encard_inter]; exact le_self_add
/-
**Set.finite_iff_finite_of_encard_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite
 ↔ t.Finite
参数：h : s.encard = t.encard。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_lt_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard < ⊤ ↔ s.Fi
nite
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite := by
  rw [← encard_lt_top_iff, ← encard_lt_top_iff, h]
/-
**Set.infinite_iff_infinite_of_encard_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) : s.In
finite ↔ t.Infinite
参数：h : s.encard = t.encard。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard = ⊤ ↔ s.In
finite
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) :
    s.Infinite ↔ t.Infinite := by rw [← encard_eq_top_iff, h, encard_eq_top_iff]
/-
**Set.Finite.finite_of_encard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, s.Finite → t.enca
rd ≤ s.encard → t.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.encard_lt_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard < ⊤ ↔ s.Fi
nite
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
-/
theorem Finite.finite_of_encard_le {s : Set α} {t : Set β} (hs : s.Finite)
    (h : t.encard ≤ s.encard) : t.Finite :=
  encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)
/-
**Set.Finite.eq_of_subset_of_encard_le'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s t : Set α}, t.Finite → s ⊆ t → t.encard ≤ s.encard → s
 = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddLECancellable.add_le_add_iff_right`：∀ {α : Type u_1} [inst : LE α] [i
nst_1 : Add α] [IsAddCommutative α] [AddLeftMono α] {a b c : α},   AddLECancella
ble a → (b + a ≤ c + a ↔ b …
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用引理 `ENat.addLECancellable_of_lt_top`：addLECancellable_of_lt_top : a < ⊤ -> A
ddLECancellable a
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_of_subset`：encard_sdiff_add_encard_of_subset
 (h : s subseteq t) : (t \ s).encard + s.encard = t.encard
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma Finite.eq_of_subset_of_encard_le' (ht : t.Finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
    s = t := by
  rw [← zero_add (a := encard s), ← encard_sdiff_add_encard_of_subset hst] at hts
  have hdiff :=
    (ENat.addLECancellable_of_lt_top (ht.subset hst).encard_lt_top).add_le_add_iff_right.mp hts
  rw [nonpos_iff_eq_zero, encard_eq_zero, sdiff_eq_empty] at hdiff
  exact hst.antisymm hdiff
/-
**Set.Finite.eq_of_subset_of_encard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s t : Set α}, s.Finite → s ⊆ t → t.encard ≤ s.encard → s
 = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le'`：∀ {α : Type u_1} {s t : Set α}, t
.Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Set.Finite.finite_of_encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β}, s.Finite → t.encard ≤ s.encard → t.Finite
-/
theorem Finite.eq_of_subset_of_encard_le (hs : s.Finite) (hst : s ⊆ t)
    (hts : t.encard ≤ s.encard) : s = t :=
  (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le' hst hts
/-
**Set.Finite.encard_lt_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s t : Set α}, s.Finite → s ⊂ t → s.encard < t.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Finite.encard_lt_encard (hs : s.Finite) (h : s ⊂ t) : s.encard < t.encard :=
  (encard_mono h.subset).lt_of_ne fun he ↦ h.ne (hs.eq_of_subset_of_encard_le h.subset he.symm.le)
/-
**Set.encard_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_strictMono [Finite α] : StrictMono (encard : Set α -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.encard_lt_encard`：∀ {α : Type u_1} {s t : Set α}, s.Finite → 
s ⊂ t → s.encard < t.encard
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem encard_strictMono [Finite α] : StrictMono (encard : Set α → ℕ∞) :=
  fun _ _ h ↦ (toFinite _).encard_lt_encard h
/-
**Set.Finite.encard_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1}, StrictMonoOn Set.encard (Set.ofPred Set.Finite)
参数：Set.ofPred Set.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.encard_lt_encard`：∀ {α : Type u_1} {s t : Set α}, s.Finite → 
s ⊂ t → s.encard < t.encard
-/
theorem Finite.encard_strictMonoOn : StrictMonoOn (α := Set α) encard (Set.ofPred Set.Finite) :=
  fun _ hs _ _ hlt ↦ hs.encard_lt_encard hlt
/-
**Set.Finite.encard_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Finite → s ≠ Set.univ → s.encard < ENat.ca
rd α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.encard_lt_encard`：∀ {α : Type u_1} {s t : Set α}, s.Finite → 
s ⊂ t → s.encard < t.encard
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_univ_iff`：ssubset_univ_iff : s ⊂ univ ↔ s != univ
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
-/
theorem Finite.encard_lt_card (hfin : s.Finite) (hne : s ≠ univ) : s.encard < ENat.card α :=
  encard_univ α ▸ hfin.encard_lt_encard (ssubset_univ_iff.mpr hne)
/-
**Set.encard_sdiff_add_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_sdiff_add_encard (s t : Set α) : (s \ t).encard + t.encard = (s uni
on t).encard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
-/
theorem encard_sdiff_add_encard (s t : Set α) : (s \ t).encard + t.encard = (s ∪ t).encard := by
  rw [← encard_union_eq disjoint_sdiff_left, sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias encard_diff_add_encard := encard_sdiff_add_encard
/-
**Set.encard_le_encard_sdiff_add_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_encard_sdiff_add_encard (s t : Set α) : s.encard <= (s \ t).enca
rd + t.encard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard`：encard_sdiff_add_encard (s t : Set α) : (s 
\ t).encard + t.encard = (s union t).encard
-/
theorem encard_le_encard_sdiff_add_encard (s t : Set α) : s.encard ≤ (s \ t).encard + t.encard :=
  (encard_mono subset_union_left).trans_eq (encard_sdiff_add_encard _ _).symm

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_diff_add_encard := encard_le_encard_sdiff_add_encard
/-
**Set.tsub_encard_le_encard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：tsub_encard_le_encard_sdiff (s t : Set α) : s.encard - t.encard <= (s \ t)
.encard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.encard_le_encard_sdiff_add_encard`：encard_le_encard_sdiff_add_encard
 (s t : Set α) : s.encard <= (s \ t).encard + t.encard
-/
theorem tsub_encard_le_encard_sdiff (s t : Set α) : s.encard - t.encard ≤ (s \ t).encard := by
  rw [tsub_le_iff_left, add_comm]; apply encard_le_encard_sdiff_add_encard

@[deprecated (since := "2026-06-03")]
alias tsub_encard_le_encard_diff := tsub_encard_le_encard_sdiff
/-
**Set.encard_add_encard_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_add_encard_compl (s : Set α) : s.encard + sᶜ.encard = (univ : Set α
).encard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
-/
theorem encard_add_encard_compl (s : Set α) : s.encard + sᶜ.encard = (univ : Set α).encard := by
  rw [← encard_union_eq disjoint_compl_right, union_compl_self]

end Lattice

section InsertErase

variable {a b : α}

/-
**Set.encard_insert_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_insert_le (s : Set α) (x : α) : (insert x s).encard <= s.encard + 1
参数：s : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Set.encard_union_le`：encard_union_le (s t : Set α) : (s union t).encard 
<= s.encard + t.encard
-/
theorem encard_insert_le (s : Set α) (x : α) : (insert x s).encard ≤ s.encard + 1 := by
  rw [← union_singleton, ← encard_singleton x]; apply encard_union_le
/-
**Set.one_le_encard_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_le_encard_insert (s : Set α) : 1 <= (insert a s).encard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Set.encard_ne_zero_of_mem`：encard_ne_zero_of_mem {a : α} (h : a in s) : 
s.encard != 0
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem one_le_encard_insert (s : Set α) : 1 ≤ (insert a s).encard :=
  Order.one_le_iff_ne_zero.mpr <| encard_ne_zero_of_mem (mem_insert a s)
/-
**Set.encard_singleton_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_singleton_inter (s : Set α) (x : α) : ({x} inter s).encard <= 1
参数：s : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem encard_singleton_inter (s : Set α) (x : α) : ({x} ∩ s).encard ≤ 1 := by
  grw [← encard_singleton x, inter_subset_left]
/-
**Set.encard_sdiff_singleton_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_sdiff_singleton_add_one (h : a in s) : (s \ {a}).encard + 1 = s.enc
ard
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
-/
theorem encard_sdiff_singleton_add_one (h : a ∈ s) :
    (s \ {a}).encard + 1 = s.encard := by
  rw [← encard_insert_of_notMem (fun h ↦ h.2 rfl), insert_sdiff_singleton, insert_eq_of_mem h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_add_one := encard_sdiff_singleton_add_one
/-
**Set.encard_sdiff_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_sdiff_singleton_of_mem (h : a in s) : (s \ {a}).encard = s.encard -
 1
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_singleton_add_one`：encard_sdiff_singleton_add_one (h : 
a in s) : (s \ {a}).encard + 1 = s.encard
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
-/
theorem encard_sdiff_singleton_of_mem (h : a ∈ s) :
    (s \ {a}).encard = s.encard - 1 := by
  rw [← encard_sdiff_singleton_add_one h,
    (ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_of_mem := encard_sdiff_singleton_of_mem
/-
**Set.encard_tsub_one_le_encard_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_tsub_one_le_encard_sdiff_singleton (s : Set α) (x : α) : s.encard -
 1 <= (s \ {x}).encard
参数：s : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Set.tsub_encard_le_encard_sdiff`：tsub_encard_le_encard_sdiff (s t : Set 
α) : s.encard - t.encard <= (s \ t).encard
-/
theorem encard_tsub_one_le_encard_sdiff_singleton (s : Set α) (x : α) :
    s.encard - 1 ≤ (s \ {x}).encard := by
  rw [← encard_singleton x]; apply tsub_encard_le_encard_sdiff

@[deprecated (since := "2026-06-03")]
alias encard_tsub_one_le_encard_diff_singleton := encard_tsub_one_le_encard_sdiff_singleton
/-
**Set.encard_exchange** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_exchange (ha : a ∉ s) (hb : b in s) : (insert a (s \ {b})).encard =
 s.encard
参数：ha : a ∉ s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.encard_sdiff_singleton_add_one`：encard_sdiff_singleton_add_one (h : 
a in s) : (s \ {a}).encard + 1 = s.encard
-/
theorem encard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).encard = s.encard := by
  rw [encard_insert_of_notMem, encard_sdiff_singleton_add_one hb]
  simp_all only [mem_sdiff, mem_singleton_iff, false_and, not_false_eq_true]
/-
**Set.encard_exchange'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_exchange' (ha : a ∉ s) (hb : b in s) : (insert a s \ {b}).encard = 
s.encard
参数：ha : a ∉ s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton_comm`：insert_sdiff_singleton_comm (hab : a !=
 b) (s : Set α) : insert a (s \ {b}) = insert a s \ {b}
· 使用定理 `Set.encard_exchange`：encard_exchange (ha : a ∉ s) (hb : b in s) : (inser
t a (s \ {b})).encard = s.encard
-/
theorem encard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).encard = s.encard := by
  rw [← insert_sdiff_singleton_comm (by rintro rfl; exact ha hb), encard_exchange ha hb]
/-
**Set.encard_eq_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_add_one_iff {k : Nat∞} : s.encard = k + 1 ↔ (exists a t, a ∉ t ∧
 insert a t = s ∧ t.encard = k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_encard_ne_zero`：nonempty_of_encard_ne_zero (h : s.encard
 != 0) : s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Set.encard_sdiff_singleton_of_mem`：encard_sdiff_singleton_of_mem (h : a 
in s) : (s \ {a}).encard = s.encard - 1
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
-/
theorem encard_eq_add_one_iff {k : ℕ∞} :
    s.encard = k + 1 ↔ (∃ a t, a ∉ t ∧ insert a t = s ∧ t.encard = k) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_of_encard_ne_zero (s := s) (by simp [h])
    refine ⟨a, s \ {a}, fun h ↦ h.2 rfl, by rwa [insert_sdiff_singleton, insert_eq_of_mem], ?_⟩
    rw [encard_sdiff_singleton_of_mem ha, h,
      (ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right]
  rintro ⟨a, t, h, rfl, rfl⟩
  rw [encard_insert_of_notMem h]

/-- Every set is either empty, infinite, or can have its `encard` reduced by a removal. Intended
  for well-founded induction on the value of `encard`. -/
/-
**Set.eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt** 是 Mathlib 中的一个定理，
位于命名空间 `Set`。
形式化陈述：eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt (s : Set α) : s = ∅
 ∨ s.encard = ⊤ ∨ exists a in s, (s \ {a}).encard < s.encard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_singleton_add_one`：encard_sdiff_singleton_add_one (h : 
a in s) : (s \ {a}).encard + 1 = s.encard
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ENat.add_lt_add_of_le_of_lt`：∀ {a b c d : ℕ∞}, a ≠ ⊤ → a ≤ b → c < d → a
 + c < b + d
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `Set.Infinite.encard_eq`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.enc
ard = ⊤

--- 原说明 ---
Every set is either empty, infinite, or can have its `encard` reduced by a remov
al. Intended
  for well-founded induction on the value of `encard`.
-/
theorem eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt (s : Set α) :
    s = ∅ ∨ s.encard = ⊤ ∨ ∃ a ∈ s, (s \ {a}).encard < s.encard := by
  refine s.eq_empty_or_nonempty.elim Or.inl (Or.inr ∘ fun ⟨a,ha⟩ ↦
    (s.finite_or_infinite.elim (fun hfin ↦ Or.inr ⟨a, ha, ?_⟩) (Or.inl ∘ Infinite.encard_eq)))
  rw [← encard_sdiff_singleton_add_one ha]; nth_rw 1 [← add_zero (encard _)]
  exact ENat.add_lt_add_of_le_of_lt hfin.sdiff.encard_lt_top.ne le_rfl zero_lt_one

@[deprecated (since := "2026-06-03")]
alias eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt :=
  eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt

end InsertErase

section SmallSets

/-
**Set.encard_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_pair {x y : α} (hne : x != y) : ({x, y} : Set α).encard = 2
参数：hne : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
theorem encard_pair {x y : α} (hne : x ≠ y) : ({x, y} : Set α).encard = 2 := by
  rw [encard_insert_of_notMem (by simpa), ← one_add_one_eq_two, encard_singleton]
/-
**Set.encard_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_encard_ne_zero`：nonempty_of_encard_ne_zero (h : s.encard
 != 0) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
theorem encard_eq_one : s.encard = 1 ↔ ∃ x, s = {x} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ by rw [hx, encard_singleton]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le (by simpa) (by simp [h])).symm⟩
/-
**Set.encard_le_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_one_iff_eq : s.encard <= 1 ↔ s = ∅ ∨ exists x, s = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Set.encard_eq_one`：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem encard_le_one_iff_eq : s.encard ≤ 1 ↔ s = ∅ ∨ ∃ x, s = {x} := by
  rw [le_iff_lt_or_eq, lt_iff_not_ge, Order.one_le_iff_ne_zero, not_not, encard_eq_zero,
    encard_eq_one]
/-
**Set.encard_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_one_iff : s.encard <= 1 ↔ forall a b, a in s -> b in s -> a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_le_one_iff_eq`：encard_le_one_iff_eq : s.encard <= 1 ↔ s = ∅ ∨
 exists x, s = {x}
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem encard_le_one_iff : s.encard ≤ 1 ↔ ∀ a b, a ∈ s → b ∈ s → a = b := by
  rw [encard_le_one_iff_eq, or_iff_not_imp_left, ← Ne, ← nonempty_iff_ne_empty]
  refine ⟨fun h a b has hbs ↦ ?_,
    fun h ⟨x, hx⟩ ↦ ⟨x, ((singleton_subset_iff.2 hx).antisymm' (fun y hy ↦ h _ _ hy hx))⟩⟩
  obtain ⟨x, rfl⟩ := h ⟨_, has⟩
  rw [(has : a = x), (hbs : b = x)]
/-
**Set.encard_le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_one_iff_subsingleton : s.encard <= 1 ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_le_one_iff`：encard_le_one_iff : s.encard <= 1 ↔ forall a b, a
 in s -> b in s -> a = b
· 使用定理 `Set.Subsingleton.eq_1`：∀ {α : Type u} (s : Set α), s.Subsingleton = ∀ ⦃x
 : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x = y
-/
theorem encard_le_one_iff_subsingleton : s.encard ≤ 1 ↔ s.Subsingleton := by
  rw [encard_le_one_iff, Set.Subsingleton]
  tauto
/-
**Set.one_lt_encard_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_lt_encard_iff_nontrivial : 1 < s.encard ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_le_one_iff_subsingleton`：encard_le_one_iff_subsingleton : s.e
ncard <= 1 ↔ s.Subsingleton
-/
theorem one_lt_encard_iff_nontrivial : 1 < s.encard ↔ s.Nontrivial := by
  contrapose!; exact encard_le_one_iff_subsingleton
/-
**Set.one_lt_encard_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_lt_encard_iff : 1 < s.encard ↔ exists a b, a in s ∧ b in s ∧ a != b
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
· 使用定理 `Set.encard_le_one_iff`：encard_le_one_iff : s.encard <= 1 ↔ forall a b, a
 in s -> b in s -> a = b
-/
theorem one_lt_encard_iff : 1 < s.encard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  contrapose!; exact encard_le_one_iff
/-
**Set.exists_ne_of_one_lt_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_ne_of_one_lt_encard (h : 1 < s.encard) (a : α) : exists b in s, b !
= a
参数：h : 1 < s.encard；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.one_lt_encard_iff`：one_lt_encard_iff : 1 < s.encard ↔ exists a b, a 
in s ∧ b in s ∧ a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem exists_ne_of_one_lt_encard (h : 1 < s.encard) (a : α) : ∃ b ∈ s, b ≠ a := by
  by_contra! h'
  obtain ⟨b, b', hb, hb', hne⟩ := one_lt_encard_iff.1 h
  apply hne
  rw [h' b hb, h' b' hb']
/-
**Set.encard_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_two : s.encard = 2 ↔ exists x y, x != y ∧ s = {x, y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.nonempty_of_encard_ne_zero`：nonempty_of_encard_ne_zero (h : s.encard
 != 0) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.encard_eq_one`：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
· 使用定理 `AddLECancellable.inj_left`：∀ {α : Type u_1} [inst : Add α] [IsAddCommuta
tive α] [inst_2 : PartialOrder α] {a b c : α},   AddLECancellable c → (a + c = b
 + c ↔ a = b)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Set.encard_pair`：encard_pair {x y : α} (hne : x != y) : ({x, y} : Set α)
.encard = 2
-/
theorem encard_eq_two : s.encard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, hne, hs⟩ ↦ by rw [hs, encard_pair hne]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  rw [← insert_eq_of_mem hx, ← insert_sdiff_singleton, encard_insert_of_notMem (fun h ↦ h.2 rfl),
    ← one_add_one_eq_two, (ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left,
    encard_eq_one] at h
  obtain ⟨y, h⟩ := h
  refine ⟨x, y, by rintro rfl; exact (h.symm.subset rfl).2 rfl, ?_⟩
  rw [← h, insert_sdiff_singleton, insert_eq_of_mem hx]
/-
**Set.encard_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_three {α : Type u_1} {s : Set α} : encard s = 3 ↔ exists x y z, 
x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.nonempty_of_encard_ne_zero`：nonempty_of_encard_ne_zero (h : s.encard
 != 0) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.encard_eq_two`：encard_eq_two : s.encard = 2 ↔ exists x y, x != y ∧ s
 = {x, y}
· 使用定理 `AddLECancellable.inj_left`：∀ {α : Type u_1} [inst : Add α] [IsAddCommuta
tive α] [inst_2 : PartialOrder α] {a b c : α},   AddLECancellable c → (a + c = b
 + c ↔ a = b)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem encard_eq_three {α : Type u_1} {s : Set α} :
    encard s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx, ← insert_sdiff_singleton,
      encard_insert_of_notMem (fun h ↦ h.2 rfl), (by exact rfl : (3 : ℕ∞) = 2 + 1),
      (ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left, encard_eq_two] at h
    obtain ⟨y, z, hne, hs⟩ := h
    refine ⟨x, y, z, ?_, ?_, hne, ?_⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr rfl)).2 rfl
    rw [← hs, insert_sdiff_singleton, insert_eq_of_mem hx]
  rw [hs, encard_insert_of_notMem, encard_insert_of_notMem, encard_singleton] <;> aesop
/-
**Set.encard_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_eq_four {α : Type u_1} {s : Set α} : encard s = 4 ↔ exists x y z w,
 x != y ∧ x != z ∧ x != w ∧ y != z ∧ y != w ∧ z != w ∧ s = {x, y, z, w}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.nonempty_of_encard_ne_zero`：nonempty_of_encard_ne_zero (h : s.encard
 != 0) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.encard_eq_three`：encard_eq_three {α : Type u_1} {s : Set α} : encard
 s = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
· 使用定理 `AddLECancellable.inj_left`：∀ {α : Type u_1} [inst : Add α] [IsAddCommuta
tive α] [inst_2 : PartialOrder α] {a b c : α},   AddLECancellable c → (a + c = b
 + c ↔ a = b)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
theorem encard_eq_four {α : Type u_1} {s : Set α} :
    encard s = 4 ↔ ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ s = {x, y, z, w} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hs⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx, ← insert_sdiff_singleton,
      encard_insert_of_notMem (fun h ↦ h.2 rfl), (by exact rfl : (4 : ℕ∞) = 3 + 1),
      (ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left, encard_eq_three] at h
    obtain ⟨y, z, w, hyz, hyw, hzw, hs⟩ := h
    refine ⟨x, y, z, w, ?_, ?_, ?_, hyz, hyw, hzw, ?_⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr (Or.inl rfl))).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr (Or.inr rfl))).2 rfl
    rw [← hs, insert_sdiff_singleton, insert_eq_of_mem hx]
  rw [hs, encard_insert_of_notMem, encard_insert_of_notMem, encard_insert_of_notMem,
    encard_singleton] <;> grind
/-
**Set.Nat.encard_range** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nat`。
形式化陈述：∀ (k : ℕ), {i | i < k}.encard = ↑k
参数：k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Set.Iio_def`：∀ {α : Type u_1} [inst : Preorder α] (a : α), {x | x < a} =
 Set.Iio a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Set.encard_coe_eq_coe_finsetCard`：∀ {α : Type u_1} (s : Finset α), (↑s).
encard = ↑s.card
-/
theorem Nat.encard_range (k : ℕ) : {i | i < k}.encard = k := by
  convert! encard_coe_eq_coe_finsetCard (Finset.range k) using 1
  · rw [Finset.coe_range, Iio_def]
  rw [Finset.card_range]

end SmallSets

/-
**Set.Finite.eq_insert_of_subset_of_encard_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Se
t.Finite`。
形式化陈述：∀ {α : Type u_1} {s t : Set α}, s.Finite → s ⊆ t → t.encard = s.encard + 1
 → ∃ a, t = insert a s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_eq_one`：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
· 使用定理 `AddLECancellable.inj_left`：∀ {α : Type u_1} [inst : Add α] [IsAddCommuta
tive α] [inst_2 : PartialOrder α] {a b c : α},   AddLECancellable c → (a + c = b
 + c ↔ a = b)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ENat.addLECancellable_of_lt_top`：addLECancellable_of_lt_top : a < ⊤ -> A
ddLECancellable a
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_of_subset`：encard_sdiff_add_encard_of_subset
 (h : s subseteq t) : (t \ s).encard + s.encard = t.encard
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
-/
theorem Finite.eq_insert_of_subset_of_encard_eq_succ (hs : s.Finite) (h : s ⊆ t)
    (hst : t.encard = s.encard + 1) : ∃ a, t = insert a s := by
  rw [← encard_sdiff_add_encard_of_subset h, add_comm _ 1,
    (ENat.addLECancellable_of_lt_top hs.encard_lt_top).inj_left, encard_eq_one] at hst
  obtain ⟨x, hx⟩ := hst; use x; rw [← sdiff_union_of_subset h, hx, singleton_union]
/-
**Set.exists_subset_encard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_subset_encard_eq {k : Nat∞} (hk : k <= s.encard) : exists t, t subs
eteq s ∧ t.encard = k
参数：hk : k <= s.encard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.nat_induction`：nat_induction {motive : Nat∞ -> Prop} (a : Nat∞) (ze
ro : motive 0) (succ : forall n : Nat, motive n -> motive n.succ) (top : (forall
 n : Nat…
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 34 条，此处仅展示前 30 条）
-/
theorem exists_subset_encard_eq {k : ℕ∞} (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k := by
  induction k using ENat.nat_induction with
  | zero => exact ⟨∅, empty_subset _, by simp⟩
  | succ n IH =>
    obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hk)
    simp only [Nat.cast_succ] at *
    have hne : t₀ ≠ s := by
      rintro rfl; rw [ht₀, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at hk; simp at hk
    obtain ⟨x, hx⟩ := exists_of_ssubset (ht₀s.ssubset_of_ne hne)
    exact ⟨insert x t₀, insert_subset hx.1 ht₀s, by rw [encard_insert_of_notMem hx.2, ht₀]⟩
  | top => rw [top_le_iff] at hk; exact ⟨s, Subset.rfl, hk⟩
/-
**Set.exists_superset_subset_encard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_superset_subset_encard_eq {k : Nat∞} (hst : s subseteq t) (hsk : s.
encard <= k) (hkt : k <= t.encard) : exists r, s subseteq r ∧ r subseteq t ∧ r.e
ncard = k
参数：hst : s subseteq t；hsk : s.encard <= k；hkt : k <= t.encard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `WithTop.le_of_add_le_add_right`：∀ {α : Type u} [inst : Add α] {x y z : W
ithTop α} [inst_1 : LE α] [AddRightReflectLE α], z ≠ ⊤ → x + z ≤ y + z → x ≤ y
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.encard_sdiff_add_encard_of_subset`：encard_sdiff_add_encard_of_subset
 (h : s subseteq t) : (t \ s).encard + s.encard = t.encard
· 使用定理 `Set.exists_subset_encard_eq`：exists_subset_encard_eq {k : Nat∞} (hk : k 
<= s.encard) : exists t, t subseteq s ∧ t.encard = k
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
-/
theorem exists_superset_subset_encard_eq {k : ℕ∞}
    (hst : s ⊆ t) (hsk : s.encard ≤ k) (hkt : k ≤ t.encard) :
    ∃ r, s ⊆ r ∧ r ⊆ t ∧ r.encard = k := by
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  have hk : k ≤ encard (t \ s) := by
    rw [← encard_sdiff_add_encard_of_subset hst, add_comm] at hkt
    exact WithTop.le_of_add_le_add_right hs hkt
  obtain ⟨r', hr', rfl⟩ := exists_subset_encard_eq hk
  refine ⟨s ∪ r', subset_union_left, union_subset hst (hr'.trans sdiff_subset), ?_⟩
  rw [encard_union_eq (disjoint_of_subset_right hr' disjoint_sdiff_right)]

section Function

variable {s : Set α} {t : Set β} {f : α → β}

/-
**Set.InjOn.encard_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.InjOn f s → (
f '' s).encard = s.encard
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card_image_of_injOn`：card_image_of_injOn {α β : Type*} {f : α -> β}
 {s : Set α} (h : Set.InjOn f s) : card (f '' s) = card s
-/
theorem InjOn.encard_image (h : InjOn f s) : (f '' s).encard = s.encard := by
  rw [encard, ENat.card_image_of_injOn h, encard]
/-
**Set.encard_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_congr (e : s ≃ t) : s.encard = t.encard
参数：e : s ≃ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.card_congr`：card_congr {α β : Type*} (f : α ≃ β) : card α = card β
-/
theorem encard_congr (e : s ≃ t) : s.encard = t.encard := ENat.card_congr e
/-
**Set._root_.Function.Injective.encard_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.encard_image (hf : f.Injective) (s : Set α) :
    (f '' s).encard = s.encard :=
  hf.injOn.encard_image
/-
**Set._root_.Function.Injective.encard_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.encard_range (hf : f.Injective) :
    ENat.card α ≤ (range f).encard := by
  rw [← image_univ, hf.encard_image, encard_univ]
/-
**Set._root_.Function.Embedding.encard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Embedding.encard_le (e : s ↪ t) : s.encard ≤ t.encard :=
  ENat.card_le_card_of_injective e.injective
/-
**Set.encard_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_image_le (f : α -> β) (s : Set α) : (f '' s).encard <= s.encard
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `Function.invFunOn_injOn_image`：∀ {α : Type u_1} {β : Type u_2} [inst : N
onempty α] (f : α → β) (s : Set α), Set.InjOn (Function.invFunOn f s) (f '' s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `Function.invFunOn_image_image_subset`：∀ {α : Type u_1} {β : Type u_2} [i
nst : Nonempty α] (f : α → β) (s : Set α), Function.invFunOn f s '' f '' s ⊆ s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem encard_image_le (f : α → β) (s : Set α) : (f '' s).encard ≤ s.encard := by
  obtain (h | h) := isEmpty_or_nonempty α
  · rw [s.eq_empty_of_isEmpty]; simp
  grw [← (f.invFunOn_injOn_image s).encard_image, f.invFunOn_image_image_subset s]
/-
**Set.Finite.injOn_of_encard_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, s.Finite → (f '' 
s).encard = s.encard → Set.InjOn f s
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.injOn_iff_invFunOn_image_image_eq_self`：injOn_iff_invFunOn_image_ima
ge_eq_self [Nonempty α] : InjOn f s ↔ (invFunOn f s) '' f '' s = s
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le'`：∀ {α : Type u_1} {s t : Set α}, t
.Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Function.invFunOn_image_image_subset`：∀ {α : Type u_1} {β : Type u_2} [i
nst : Nonempty α] (f : α → β) (s : Set α), Function.invFunOn f s '' f '' s ⊆ s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `Function.invFunOn_injOn_image`：∀ {α : Type u_1} {β : Type u_2} [inst : N
onempty α] (f : α → β) (s : Set α), Set.InjOn (Function.invFunOn f s) (f '' s)
-/
theorem Finite.injOn_of_encard_image_eq (hs : s.Finite) (h : (f '' s).encard = s.encard) :
    InjOn f s := by
  obtain (h' | hne) := isEmpty_or_nonempty α
  · simp
  rw [← (f.invFunOn_injOn_image s).encard_image] at h
  rw [injOn_iff_invFunOn_image_image_eq_self]
  exact hs.eq_of_subset_of_encard_le' (f.invFunOn_image_image_subset s) h.symm.le
/-
**Set.encard_preimage_of_injective_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_preimage_of_injective_subset_range (hf : f.Injective) (ht : t subse
teq range f) : (f ⁻¹' t).encard = t.encard
参数：hf : f.Injective；ht : t subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.encard_image`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β}, Function.Injective f → ∀ (s : Set α), (f '' s).encard = s.encard
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
theorem encard_preimage_of_injective_subset_range (hf : f.Injective) (ht : t ⊆ range f) :
    (f ⁻¹' t).encard = t.encard := by
  rw [← hf.encard_image, image_preimage_eq_inter_range, inter_eq_self_of_subset_left ht]
/-
**Set.encard_preimage_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_preimage_of_bijective (hf : f.Bijective) (t : Set β) : (f ⁻¹' t).en
card = t.encard
参数：hf : f.Bijective；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.encard_preimage_of_injective_subset_range`：encard_preimage_of_inject
ive_subset_range (hf : f.Injective) (ht : t subseteq range f) : (f ⁻¹' t).encard
 = t.encard
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
lemma encard_preimage_of_bijective (hf : f.Bijective) (t : Set β) : (f ⁻¹' t).encard = t.encard :=
  encard_preimage_of_injective_subset_range hf.injective (by simp [hf.surjective.range_eq])
/-
**Set.encard_le_encard_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_encard_of_injOn (hf : MapsTo f s t) (f_inj : InjOn f s) : s.enca
rd <= t.encard
参数：hf : MapsTo f s t；f_inj : InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem encard_le_encard_of_injOn (hf : MapsTo f s t) (f_inj : InjOn f s) :
    s.encard ≤ t.encard := by
  grw [← f_inj.encard_image, hf.image_subset]

open Notation in
/-
**Set.encard_preimage_val_le_encard_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_preimage_val_le_encard_left (P Q : Set α) : (P ↓inter Q).encard <= 
P.encard
参数：P Q : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {t : Set β} (e : ↑s ↪ ↑t), s.encard ≤ t.encard
-/
lemma encard_preimage_val_le_encard_left (P Q : Set α) : (P ↓∩ Q).encard ≤ P.encard :=
  (Function.Embedding.subtype _).encard_le

set_option backward.isDefEq.respectTransparency false in
open Notation in
/-
**Set.encard_preimage_val_le_encard_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_preimage_val_le_encard_right (P Q : Set α) : (P ↓inter Q).encard <=
 Q.encard
参数：P Q : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {t : Set β} (e : ↑s ↪ ↑t), s.encard ≤ t.encard
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
lemma encard_preimage_val_le_encard_right (P Q : Set α) : (P ↓∩ Q).encard ≤ Q.encard :=
  Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, hx⟩, fun _ _ h ↦ by
    simpa [Subtype.coe_inj] using h⟩
/-
**Set.Finite.exists_injOn_of_encard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Nonempty β] {s : Set α} {t : Set β},   s.
Finite → s.encard ≤ t.encard → ∃ f, s ⊆ f ⁻¹' t ∧ Set.InjOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_injOn_of_encard_le._unary`：∀ {α : Type u_1} {β : Type 
u_2} [Nonempty β] (_x : (s : Set α) ×' (t : Set β) ×' (_ : s.Finite) ×' s.encard
 ≤ t.encard),   ∃ f, _x.1 ⊆ f ⁻¹'…
-/
theorem Finite.exists_injOn_of_encard_le [Nonempty β] {s : Set α} {t : Set β} (hs : s.Finite)
    (hle : s.encard ≤ t.encard) : ∃ (f : α → β), s ⊆ f ⁻¹' t ∧ InjOn f s := by
  classical
  obtain (rfl | h | ⟨a, has, -⟩) := s.eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · simp
  · exact (encard_ne_top_iff.mpr hs h).elim
  obtain ⟨b, hbt⟩ := encard_pos.1 ((encard_pos.2 ⟨_, has⟩).trans_le hle)
  have hle' : (s \ {a}).encard ≤ (t \ {b}).encard := by
    rwa [← ENat.add_le_add_iff_right ENat.one_ne_top,
    encard_sdiff_singleton_add_one has, encard_sdiff_singleton_add_one hbt]
  obtain ⟨f₀, hf₀s, hinj⟩ := exists_injOn_of_encard_le hs.sdiff hle'
  simp only [preimage_sdiff, subset_def, mem_sdiff, mem_singleton_iff, mem_preimage, and_imp]
    at hf₀s
  use Function.update f₀ a b
  rw [← insert_eq_of_mem has, ← insert_sdiff_singleton, injOn_insert (fun h ↦ h.2 rfl)]
  simp only [mem_sdiff, mem_singleton_iff, insert_sdiff_singleton, subset_def,
    mem_insert_iff, mem_preimage, Function.update_apply, forall_eq_or_imp, ite_true, and_imp,
    mem_image, ite_eq_left_iff, not_exists, not_and, not_forall, exists_prop, and_iff_right hbt]
  refine ⟨?_, ?_, fun x hxs hxa ↦ ⟨hxa, (hf₀s x hxs hxa).2⟩⟩
  · rintro x hx; split_ifs with h
    · assumption
    · exact (hf₀s x hx h).1
  exact InjOn.congr hinj (fun x ⟨_, hxa⟩ ↦ by rwa [Function.update_of_ne])
termination_by encard s
/-
**Set.Finite.exists_bijOn_of_encard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} [Nonempty β],   s.
Finite → s.encard = t.encard → ∃ f, Set.BijOn f s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_injOn_of_encard_le`：∀ {α : Type u_1} {β : Type u_2} [N
onempty β] {s : Set α} {t : Set β},   s.Finite → s.encard ≤ t.encard → ∃ f, s ⊆ 
f ⁻¹' t ∧ Set.InjOn f s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
-/
theorem Finite.exists_bijOn_of_encard_eq [Nonempty β] (hs : s.Finite) (h : s.encard = t.encard) :
    ∃ (f : α → β), BijOn f s t := by
  obtain ⟨f, hf, hinj⟩ := hs.exists_injOn_of_encard_le h.le; use f
  convert! hinj.bijOn_image
  rw [(hs.image f).eq_of_subset_of_encard_le (image_subset_iff.mpr hf)
    (h.symm.trans hinj.encard_image.symm).le]

/-- A version of the pigeonhole principle for `Set`s rather than `Finset`s.

See also `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_ncard_lt_of_maps_to`. -/
/-
**Set.exists_ne_map_eq_of_encard_lt_of_maps_to** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_ne_map_eq_of_encard_lt_of_maps_to (hc : t.encard < s.encard) (hf : 
MapsTo f s t) : existsᵉ (a₁ in s) (a₂ in s), a₁ != a₂ ∧ f a₁ = f a₂
参数：hc : t.encard < s.encard；hf : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Set.MapsTo.restrict_inj`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Injective (Set.MapsTo.re
strict f s t …
· 使用定理 `Function.Embedding.encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {t : Set β} (e : ↑s ↪ ↑t), s.encard ≤ t.encard

--- 原说明 ---
A version of the pigeonhole principle for `Set`s rather than `Finset`s.

See also `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_ncard_lt_of_maps_to`.
-/
lemma exists_ne_map_eq_of_encard_lt_of_maps_to (hc : t.encard < s.encard) (hf : MapsTo f s t) :
    ∃ᵉ (a₁ ∈ s) (a₂ ∈ s), a₁ ≠ a₂ ∧ f a₁ = f a₂ := by
  contrapose! hc
  suffices Function.Injective (hf.restrict f) by
    let f' : s ↪ t := ⟨hf.restrict, this⟩
    exact f'.encard_le
  simpa only [hf.restrict_inj, not_imp_not] using! hc

end Function

section ncard

/-- A tactic (for use in default params) that applies `Set.toFinite` to synthesize a `Set.Finite`
  term. -/
syntax "toFinite_tac" : tactic

macro_rules
  | `(tactic| toFinite_tac) => `(tactic| apply Set.toFinite)

/-- A tactic useful for transferring proofs for `encard` to their corresponding `card` statements -/
syntax "to_encard_tac" : tactic

macro_rules
  | `(tactic| to_encard_tac) => `(tactic|
      simp only [← Nat.cast_le (α := ℕ∞), ← Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_one])


/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
/-
**Set.ncard** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：ncard (s : Set α) : Nat
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite
-/
noncomputable def ncard (s : Set α) : ℕ := ENat.toNat s.encard
/-
**Set.ncard_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard := rfl
/-
**Set.Finite.cast_ncard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.ncard = s.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard.eq_1`：∀ {α : Type u_1} (s : Set α), s.ncard = s.encard.toNat
· 使用定理 `ENat.natCast_toNat_eq_self`：natCast_toNat_eq_self : ENat.toNat n = n ↔ n
 != ⊤
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.encard_eq_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard = ⊤ ↔ s.In
finite
· 使用定理 `Set.Infinite.eq_1`：∀ {α : Type u} (s : Set α), s.Infinite = ¬s.Finite
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem Finite.cast_ncard_eq (hs : s.Finite) : s.ncard = s.encard := by
  rwa [ncard, ENat.natCast_toNat_eq_self, ne_eq, encard_eq_top_iff, Set.Infinite, not_not]

variable (s) in
@[simp]
/-
**Set.coe_ncard_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_ncard_eq_encard [Finite s] : s.ncard = s.encard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem coe_ncard_eq_encard [Finite s] : s.ncard = s.encard :=
  s.toFinite.cast_ncard_eq
/-
**Set.ncard_le_encard** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_le_encard (s : Set α) : s.ncard <= s.encard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.natCast_toNat_le_self`：natCast_toNat_le_self (n : Nat∞) : ↑(toNat n
) <= n
-/
lemma ncard_le_encard (s : Set α) : s.ncard ≤ s.encard := ENat.natCast_toNat_le_self _
/-
**Set._root_.Nat.card_coe_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := rfl
/-
**Set.ncard_eq_toFinset_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_toFinset_card (s : Set α) (hs : s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Set.Finite.card_toFinset`：∀ {α : Type u} {s : Set α} [inst : Fintype ↑s]
 (h : s.Finite), h.toFinset.card = Fintype.card ↑s
-/
theorem ncard_eq_toFinset_card (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [← _root_.Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ hs.fintype,
    @Finite.card_toFinset _ _ hs.fintype hs]
/-
**Set.ncard_eq_toFinset_card'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_toFinset_card' (s : Set α) [Fintype s] : s.ncard = s.toFinset.car
d
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ncard_eq_toFinset_card' (s : Set α) [Fintype s] :
    s.ncard = s.toFinset.card := by
  simp [← _root_.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

variable (s) in
@[simp]
/-
**Set.fintypeCard_eq_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fintypeCard_eq_ncard [Fintype s] : Fintype.card s = s.ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card'`：ncard_eq_toFinset_card' (s : Set α) [Fintyp
e s] : s.ncard = s.toFinset.card
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem fintypeCard_eq_ncard [Fintype s] : Fintype.card s = s.ncard := by
  rw [ncard_eq_toFinset_card', toFinset_card]
/-
**Set.cast_ncard** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：cast_ncard {s : Set α} (hs : s.Finite) : (s.ncard : Cardinal) = Cardinal.m
k s
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.cast_card`：cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal
.mk α
-/
lemma cast_ncard {s : Set α} (hs : s.Finite) :
    (s.ncard : Cardinal) = Cardinal.mk s := @Nat.cast_card _ hs
/-
**Set.encard_le_coe_iff_finite_ncard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：encard_le_coe_iff_finite_ncard_le {k : Nat} : s.encard <= k ↔ s.Finite ∧ s
.ncard <= k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_le_coe_iff`：encard_le_coe_iff {k : Nat} : s.encard <= k ↔ s.F
inite ∧ exists (n₀ : Nat), s.encard = n₀ ∧ n₀ <= k
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `ENat.toNat_natCast`：toNat_natCast (n : Nat) : toNat n = n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
-/
theorem encard_le_coe_iff_finite_ncard_le {k : ℕ} : s.encard ≤ k ↔ s.Finite ∧ s.ncard ≤ k := by
  rw [encard_le_coe_iff, and_congr_right_iff]
  exact fun hfin ↦ ⟨fun ⟨n₀, hn₀, hle⟩ ↦ by rwa [ncard_def, hn₀, ENat.toNat_natCast],
    fun h ↦ ⟨s.ncard, by rw [hfin.cast_ncard_eq], h⟩⟩
/-
**Set.Infinite.ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
-/
theorem Infinite.ncard (hs : s.Infinite) : s.ncard = 0 := by
  rw [← _root_.Nat.card_coe_set_eq, @Nat.card_eq_zero_of_infinite _ hs.to_subtype]

@[gcongr]
/-
**Set.ncard_le_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
参数：hst : s subseteq t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)
-/
theorem ncard_le_ncard (hst : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  rw [← Nat.cast_le (α := ℕ∞), ht.cast_ncard_eq, (ht.subset hst).cast_ncard_eq]
  exact encard_mono hst
/-
**Set.ncard_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := fun _ _ ↦ ncard_le_ncard
/-
**Set.ncard_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.ncard_eq_zero._auto_1
 → (s.ncard = 0 ↔ s = ∅)
参数：s.ncard = 0 ↔ s = ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem ncard_eq_zero (hs : s.Finite := by toFinite_tac) :
    s.ncard = 0 ↔ s = ∅ := by
  rw [← Nat.cast_inj (R := ℕ∞), hs.cast_ncard_eq, Nat.cast_zero, encard_eq_zero]
/-
**Set.ncard_coe_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.card
参数：s : Finset α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Finset.finite_toSet_toFinset`：finite_toSet_toFinset (s : Finset α) : s.f
inite_toSet.toFinset = s
-/
@[simp, norm_cast] theorem ncard_coe_finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_toFinset_card _, Finset.finite_toSet_toFinset]
/-
**Set.ncard_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
参数：α : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_univ`：card_univ : Nat.card (univ : Set α) = Nat.card α
-/
@[simp] theorem ncard_univ (α : Type*) : (univ : Set α).ncard = Nat.card α := Nat.card_univ
/-
**Set.ncard_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_card [Finite α] (s : Set α) : s.ncard <= Nat.card α
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
-/
theorem ncard_le_card [Finite α] (s : Set α) : s.ncard ≤ Nat.card α :=
  ncard_univ α ▸ ncard_le_ncard s.subset_univ
/-
**Set.ncard_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (α : Type u_3), ∅.ncard = 0
参数：α : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] theorem ncard_empty (α : Type*) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]
/-
**Set.ncard_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_pos (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ncard_pos (hs : s.Finite := by toFinite_tac) : 0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, Ne, ncard_eq_zero hs, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.ncard_pos⟩ := ncard_pos
/-
**Set.ncard_ne_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_ne_zero_of_mem {a : α} (h : a in s) (hs : s.Finite
参数：h : a in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
-/
theorem ncard_ne_zero_of_mem {a : α} (h : a ∈ s) (hs : s.Finite := by toFinite_tac) : s.ncard ≠ 0 :=
  ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm
/-
**Set.finite_of_ncard_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_of_ncard_ne_zero (hs : s.ncard != 0) : s.Finite
参数：hs : s.ncard != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
-/
theorem finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Finite :=
  s.finite_or_infinite.elim id fun h ↦ (hs h.ncard).elim
/-
**Set.finite_of_ncard_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite
参数：hs : 0 < s.ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_ncard_ne_zero`：finite_of_ncard_ne_zero (hs : s.ncard != 0)
 : s.Finite
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite :=
  finite_of_ncard_ne_zero hs.ne.symm
/-
**Set.nonempty_of_ncard_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_ncard_ne_zero (hs : s.ncard != 0) : s.Nonempty
参数：hs : s.ncard != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs
/-
**Set.ncard_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (a : α), {a}.ncard = 1
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by
  simp [ncard]
/-
**Set.ncard_singleton_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_singleton_inter (a : α) (s : Set α) : ({a} inter s).ncard <= 1
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.encard_singleton_inter`：encard_singleton_inter (s : Set α) (x : α) :
 ({x} inter s).encard <= 1
-/
theorem ncard_singleton_inter (a : α) (s : Set α) : ({a} ∩ s).ncard ≤ 1 := by
  rw [← Nat.cast_le (α := ℕ∞), (toFinite _).cast_ncard_eq, Nat.cast_one]
  apply encard_singleton_inter

@[simp]
/-
**Set.ncard_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_prod {s : Set α} {t : Set β} : (s ×ˢ t).ncard = s.ncard * t.ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_prod`：encard_prod {s : Set α} {t : Set β} : (s ×ˢ t).encard =
 s.encard * t.encard
· 使用定理 `ENat.toNat_mul`：∀ (a b : ℕ∞), (a * b).toNat = a.toNat * b.toNat
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ncard_prod {s : Set α} {t : Set β} : (s ×ˢ t).ncard = s.ncard * t.ncard := by
  simp [ncard, ENat.toNat_mul]

@[simp]
/-
**Set.ncard_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_powerset (s : Set α) (hs : s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.mk_powerset`：mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) =
 2 ^ #(↥s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.cast_ncard`：cast_ncard {s : Set α} (hs : s.Finite) : (s.ncard : Card
inal) = Cardinal.mk s
· 使用定理 `Set.Finite.powerset`：∀ {α : Type u} {s : Set α}, s.Finite → (𝒫 s).Finite
-/
theorem ncard_powerset (s : Set α) (hs : s.Finite := by toFinite_tac) :
    (𝒫 s).ncard = 2 ^ s.ncard := by
  have h := Cardinal.mk_powerset s
  rw [← cast_ncard hs.powerset, ← cast_ncard hs] at h
  norm_cast at h

section InsertErase

/-
**Set.ncard_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ s → autoParam s.Finite Set.nca
rd_insert_of_notMem._auto_1 → (insert a s).ncard = s.ncard + 1
参数：insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
-/
@[simp] theorem ncard_insert_of_notMem {a : α} (h : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  rw [← Nat.cast_inj (R := ℕ∞), (hs.insert a).cast_ncard_eq, Nat.cast_add, Nat.cast_one,
    hs.cast_ncard_eq, encard_insert_of_notMem h]
/-
**Set.ncard_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_insert_of_mem {a : α} (h : a in s) : ncard (insert a s) = s.ncard
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
-/
theorem ncard_insert_of_mem {a : α} (h : a ∈ s) : ncard (insert a s) = s.ncard := by
  rw [insert_eq_of_mem h]
/-
**Set.ncard_insert_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard <= s.ncard + 1
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
· 使用定理 `Set.encard_insert_le`：encard_insert_le (s : Set α) (x : α) : (insert x s
).encard <= s.encard + 1
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard ≤ s.ncard + 1 := by
  obtain hs | hs := s.finite_or_infinite
  · to_encard_tac; rw [hs.cast_ncard_eq, (hs.insert _).cast_ncard_eq]; apply encard_insert_le
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _
/-
**Set.one_le_ncard_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_le_ncard_insert (a : α) (s : Set α) (hs : s.Finite
参数：a : α；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Set.ncard_ne_zero_of_mem`：ncard_ne_zero_of_mem {a : α} (h : a in s) (hs 
: s.Finite
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem one_le_ncard_insert (a : α) (s : Set α) (hs : s.Finite := by toFinite_tac) :
    1 ≤ (insert a s).ncard :=
  Nat.one_le_iff_ne_zero.mpr <| ncard_ne_zero_of_mem (mem_insert a s) (by simp [hs])
/-
**Set.ncard_insert_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_insert_eq_ite {a : α} [Decidable (a in s)] (hs : s.Finite
参数：a in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_insert_of_mem`：ncard_insert_of_mem {a : α} (h : a in s) : ncar
d (insert a s) = s.ncard
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.ncard_insert_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ 
s → autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (insert a s).ncard =
 s.ncard + 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem ncard_insert_eq_ite {a : α} [Decidable (a ∈ s)] (hs : s.Finite := by toFinite_tac) :
    ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 := by
  by_cases h : a ∈ s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_notMem h hs, if_neg h]
/-
**Set.ncard_le_ncard_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard <= (insert a s).ncard
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_insert_eq_ite`：ncard_insert_eq_ite {a : α} [Decidable (a in s)
] (hs : s.Finite
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard ≤ (insert a s).ncard := by
  classical
  refine
    s.finite_or_infinite.elim (fun h ↦ ?_) (fun h ↦ by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp
/-
**Set.ncard_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_pair {a b : α} (h : a != b) : ({a, b} : Set α).ncard = 2
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_insert_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ 
s → autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (insert a s).ncard =
 s.ncard + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ncard_pair {a b : α} (h : a ≠ b) : ({a, b} : Set α).ncard = 2 := by
  simp [h]

-- removing `@[simp]` because the LHS is not in simp normal form
/-
**Set.ncard_sdiff_singleton_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff_singleton_add_one {a : α} (h : a in s) (hs : s.Finite
参数：h : a in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.encard_sdiff_singleton_add_one`：encard_sdiff_singleton_add_one (h : 
a in s) : (s \ {a}).encard + 1 = s.encard
-/
theorem ncard_sdiff_singleton_add_one {a : α} (h : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : (s \ {a}).ncard + 1 = s.ncard := by
  to_encard_tac
  rw [hs.cast_ncard_eq, hs.sdiff.cast_ncard_eq, encard_sdiff_singleton_add_one h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_add_one := ncard_sdiff_singleton_add_one
/-
**Set.ncard_sdiff_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s → (s \ {a}).ncard = s.ncard - 
1
参数：s \ {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_or_finite`：∀ {α : Type u} (s : Set α), s.Infinite ∨ s.Finit
e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Infinite.encard_eq`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.enc
ard = ⊤
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.ncard_sdiff_singleton_add_one`：ncard_sdiff_singleton_add_one {a : α}
 (h : a in s) (hs : s.Finite
-/
@[simp] theorem ncard_sdiff_singleton_of_mem {a : α} (h : a ∈ s) :
    (s \ {a}).ncard = s.ncard - 1 := by
  rcases s.infinite_or_finite with hs | hs
  · simp_all [ncard, Infinite.sdiff hs (finite_singleton a)]
  · exact eq_tsub_of_add_eq (ncard_sdiff_singleton_add_one h hs)

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_of_mem := ncard_sdiff_singleton_of_mem
/-
**Set.ncard_sdiff_singleton_lt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff_singleton_lt_of_mem {a : α} (h : a in s) (hs : s.Finite
参数：h : a in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_sdiff_singleton_add_one`：ncard_sdiff_singleton_add_one {a : α}
 (h : a in s) (hs : s.Finite
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem ncard_sdiff_singleton_lt_of_mem {a : α} (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard < s.ncard := by
  rw [← ncard_sdiff_singleton_add_one h hs]; apply lt_add_one

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_lt_of_mem := ncard_sdiff_singleton_lt_of_mem
/-
**Set.ncard_sdiff_singleton_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard <= s.ncard
参数：s : Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem ncard_sdiff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard ≤ s.ncard := by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_ncard sdiff_subset hs
  convert! Nat.zero_le _
  exact (hs.sdiff (by simp)).ncard

@[deprecated (since := "2026-06-03")] alias ncard_diff_singleton_le := ncard_sdiff_singleton_le
/-
**Set.pred_ncard_le_ncard_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pred_ncard_le_ncard_sdiff_singleton (s : Set α) (a : α) : s.ncard - 1 <= (
s \ {a}).ncard
参数：s : Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_sdiff_singleton_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, 
a ∈ s → (s \ {a}).ncard = s.ncard - 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
-/
theorem pred_ncard_le_ncard_sdiff_singleton (s : Set α) (a : α) :
    s.ncard - 1 ≤ (s \ {a}).ncard := by
  by_cases h : a ∈ s
  · rw [ncard_sdiff_singleton_of_mem h]
  rw [sdiff_singleton_eq_self h]
  apply Nat.pred_le

@[deprecated (since := "2026-06-03")]
alias pred_ncard_le_ncard_diff_singleton := pred_ncard_le_ncard_sdiff_singleton
/-
**Set.ncard_exchange** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_exchange {a b : α} (ha : a ∉ s) (hb : b in s) : (insert a (s \ {b}))
.ncard = s.ncard
参数：ha : a ∉ s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.encard_exchange`：encard_exchange (ha : a ∉ s) (hb : b in s) : (inser
t a (s \ {b})).encard = s.encard
-/
theorem ncard_exchange {a b : α} (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard :=
  congr_arg ENat.toNat <| encard_exchange ha hb
/-
**Set.ncard_exchange'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_exchange' {a b : α} (ha : a ∉ s) (hb : b in s) : (insert a s \ {b}).
ncard = s.ncard
参数：ha : a ∉ s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_exchange`：ncard_exchange {a b : α} (ha : a ∉ s) (hb : b in s) 
: (insert a (s \ {b})).ncard = s.ncard
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem ncard_exchange' {a b : α} (ha : a ∉ s) (hb : b ∈ s) :
    (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb, ← singleton_union, ← singleton_union, union_sdiff_distrib,
    sdiff_singleton_eq_self fun h ↦ ha (by rwa [← mem_singleton_iff.mp h])]
/-
**Set.odd_card_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：odd_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite
参数：ha : a ∉ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_insert_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ 
s → autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (insert a s).ncard =
 s.ncard + 1
· 使用定理 `Nat.odd_add`：∀ {m n : ℕ}, Odd (m + n) ↔ (Odd m ↔ Even n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma odd_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    Odd (insert a s).ncard ↔ Even s.ncard := by
  rw [ncard_insert_of_notMem ha hs, Nat.odd_add]
  simp only [← Nat.not_even_iff_odd, Nat.not_even_one, iff_false, Decidable.not_not]
/-
**Set.even_card_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：even_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite
参数：ha : a ∉ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_insert_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ 
s → autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (insert a s).ncard =
 s.ncard + 1
· 使用定理 `Nat.even_add_one`：∀ {n : ℕ}, Even (n + 1) ↔ ¬Even n
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma even_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    Even (insert a s).ncard ↔ Odd s.ncard := by
  rw [ncard_insert_of_notMem ha hs, Nat.even_add_one, Nat.not_even_iff_odd]

end InsertErase

variable {f : α → β}

/-
**Set.ncard_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_image_le (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.encard_image_le`：encard_image_le (f : α -> β) (s : Set α) : (f '' s)
.encard <= s.encard
-/
theorem ncard_image_le (hs : s.Finite := by toFinite_tac) : (f '' s).ncard ≤ s.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.image _).cast_ncard_eq]; apply encard_image_le
/-
**Set.InjOn.ncard_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.InjOn f s → (
f '' s).ncard = s.ncard
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
-/
theorem InjOn.ncard_image (H : Set.InjOn f s) : (f '' s).ncard = s.ncard :=
  congr_arg ENat.toNat <| H.encard_image

@[deprecated (since := "2026-01-30")] alias ncard_image_of_injOn := InjOn.ncard_image
/-
**Set.injOn_of_ncard_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite
参数：h : (f '' s).ncard = s.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.injOn_of_encard_image_eq`：∀ {α : Type u_1} {β : Type u_2} {s 
: Set α} {f : α → β}, s.Finite → (f '' s).encard = s.encard → Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac) :
    Set.InjOn f s := by
  rw [← Nat.cast_inj (R := ℕ∞), hs.cast_ncard_eq, (hs.image _).cast_ncard_eq] at h
  exact hs.injOn_of_encard_image_eq h
/-
**Set.ncard_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_image_iff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.injOn_of_ncard_image_eq`：injOn_of_ncard_image_eq (h : (f '' s).ncard
 = s.ncard) (hs : s.Finite
· 使用定理 `Set.InjOn.ncard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → (f '' s).ncard = s.ncard
-/
theorem ncard_image_iff (hs : s.Finite := by toFinite_tac) :
    (f '' s).ncard = s.ncard ↔ Set.InjOn f s :=
  ⟨fun h ↦ injOn_of_ncard_image_eq h hs, InjOn.ncard_image⟩
/-
**Set.ncard_image_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = 
s.ncard
参数：s : Set α；H : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.ncard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → (f '' s).ncard = s.ncard
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = s.ncard :=
  H.injOn.ncard_image
/-
**Set.ncard_preimage_of_injective_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective) (hs
 : s subseteq Set.range f) : (f ⁻¹' s).ncard = s.ncard
参数：H : f.Injective；hs : s subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
-/
theorem ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective)
    (hs : s ⊆ Set.range f) :
    (f ⁻¹' s).ncard = s.ncard := by
  rw [← ncard_image_of_injective _ H, image_preimage_eq_iff.mpr hs]
/-
**Set.fiber_ncard_ne_zero_iff_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_ncard_ne_zero`：nonempty_of_ncard_ne_zero (hs : s.ncard !
= 0) : s.Nonempty
· 使用定理 `Set.ncard_ne_zero_of_mem`：ncard_ne_zero_of_mem {a : α} (h : a in s) (hs 
: s.Finite
· 使用定理 `Set.mem_sep`：mem_sep (xs : x in s) (px : p x) : x in { x in s | p x }
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
-/
theorem fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite := by toFinite_tac) :
    { x ∈ s | f x = y }.ncard ≠ 0 ↔ y ∈ f '' s := by
  refine ⟨nonempty_of_ncard_ne_zero, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x ∈ s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))
/-
**Set.ncard_map** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} (f : α ↪ β), (⇑f '' s).ncard =
 s.ncard
参数：f : α ↪ β；⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
@[simp] theorem ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.inj'
/-
**Set.ncard_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (P : α → Prop) (s : Set α), {x | ↑x ∈ s}.ncard = (s ∩ Set
.ofPred P).ncard
参数：P : α → Prop；s : Set α；s ∩ Set.ofPred P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
@[simp] theorem ncard_subtype (P : α → Prop) (s : Set α) :
    { x : Subtype P | (x : α) ∈ s }.ncard = (s ∩ Set.ofPred P).ncard := by
  convert! (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [← and_assoc, exists_eq_right]
/-
**Set.ncard_inter_le_ncard_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ s.ncard :=
  ncard_le_ncard inter_subset_left hs
/-
**Set.ncard_inter_le_ncard_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ t.ncard :=
  ncard_le_ncard inter_subset_right ht
/-
**Set.eq_of_subset_of_ncard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_subset_of_ncard_le (h : s subseteq t) (h' : t.ncard <= s.ncard) (ht 
: t.Finite
参数：h : s subseteq t；h' : t.ncard <= s.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le'`：∀ {α : Type u_1} {s t : Set α}, t
.Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
    (ht : t.Finite := by toFinite_tac) : s = t :=
  ht.eq_of_subset_of_encard_le' h
    (by rwa [← Nat.cast_le (α := ℕ∞), ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq] at h')
/-
**Set.subset_iff_eq_of_ncard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iff_eq_of_ncard_le (h : t.ncard <= s.ncard) (ht : t.Finite
参数：h : t.ncard <= s.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_ncard_le`：eq_of_subset_of_ncard_le (h : s subseteq t
) (h' : t.ncard <= s.ncard) (ht : t.Finite
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem subset_iff_eq_of_ncard_le (h : t.ncard ≤ s.ncard) (ht : t.Finite := by toFinite_tac) :
    s ⊆ t ↔ s = t :=
  ⟨fun hst ↦ eq_of_subset_of_ncard_le hst h ht, Eq.subset⟩
/-
**Set.map_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：map_eq_of_subset {f : α ↪ α} (h : f '' s subseteq s) (hs : s.Finite
参数：h : f '' s subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_ncard_le`：eq_of_subset_of_ncard_le (h : s subseteq t
) (h' : t.ncard <= s.ncard) (ht : t.Finite
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.ncard_map`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} (f : α ↪ β), 
(⇑f '' s).ncard = s.ncard
-/
theorem map_eq_of_subset {f : α ↪ α} (h : f '' s ⊆ s) (hs : s.Finite := by toFinite_tac) :
    f '' s = s :=
  eq_of_subset_of_ncard_le h (ncard_map _).ge hs
/-
**Set.sep_of_ncard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_of_ncard_eq {a : α} {P : α -> Prop} (h : { x in s | P x }.ncard = s.nc
ard) (ha : a in s) (hs : s.Finite
参数：h : { x in s | P x }.ncard = s.ncard；ha : a in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sep_eq_self_iff_mem_true`：sep_eq_self_iff_mem_true : { x in s | p x 
} = s ↔ forall x in s, p x
· 使用定理 `Set.eq_of_subset_of_ncard_le`：eq_of_subset_of_ncard_le (h : s subseteq t
) (h' : t.ncard <= s.ncard) (ht : t.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sep_of_ncard_eq {a : α} {P : α → Prop} (h : { x ∈ s | P x }.ncard = s.ncard) (ha : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : P a :=
  sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha
/-
**Set.ncard_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite
参数：h : s ⊂ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Set.Finite.encard_lt_encard`：∀ {α : Type u_1} {s t : Set α}, s.Finite → 
s ⊂ t → s.encard < t.encard
-/
theorem ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard < t.ncard := by
  rw [← Nat.cast_lt (α := ℕ∞), ht.cast_ncard_eq, (ht.subset h.subset).cast_ncard_eq]
  exact (ht.subset h.subset).encard_lt_encard h
/-
**Set.ncard_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_lt_card [Finite α] (h : s != univ) : s.ncard < Nat.card α
参数：h : s != univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_lt_ncard`：ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_univ_iff`：ssubset_univ_iff : s ⊂ univ ↔ s != univ
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
-/
theorem ncard_lt_card [Finite α] (h : s ≠ univ) : s.ncard < Nat.card α :=
  ncard_univ α ▸ ncard_lt_ncard (ssubset_univ_iff.mpr h)
/-
**Set.ncard_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_lt_ncard`：ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard :=
  fun _ _ h ↦ ncard_lt_ncard h
/-
**Set.Finite.ncard_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1}, StrictMonoOn Set.ncard (Set.ofPred Set.Finite)
参数：Set.ofPred Set.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_lt_ncard`：ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite
-/
theorem Finite.ncard_strictMonoOn : StrictMonoOn (α := Set α) ncard (Set.ofPred Set.Finite) :=
  fun _ _ _ ht hlt ↦ ncard_lt_ncard hlt ht
/-
**Set.ncard_eq_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_of_bijective {n : Nat} (f : forall i, i < n -> α) (hf : forall a 
in s, exists i, exists h : i < n, f i h = a) (hf' : forall (i) (h : i < n), f i 
h in s) (f_inj : forall (i j) (hi : i < n) (hj : j < n), f i hi = f j hj -> i = 
j) : s.ncard = n
参数：f : forall i, i < n -> α；hf : forall a in s, exists i, exists h : i < n, f i 
h = a；hf' : forall (i) (h : i < n), f i h in s；f_inj : forall (i j) (hi : i < n)
 (hj : j < n), f i hi = f j hj -> i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.InjOn.ncard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → (f '' s).ncard = s.ncard
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
theorem ncard_eq_of_bijective {n : ℕ} (f : ∀ i, i < n → α)
    (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a) (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : s.ncard = n := by
  let f' : Fin n → α := fun i ↦ f i.val i.is_lt
  suffices himage : s = f' '' Set.univ by
    rw [← Fintype.card_fin n, ← Nat.card_eq_fintype_card, ← Set.ncard_univ, himage]
    exact InjOn.ncard_image <| fun i _hi j _hj h ↦ Fin.ext <| f_inj i.val j.val i.is_lt j.is_lt h
  ext x
  simp only [image_univ, mem_range]
  refine ⟨fun hx ↦ ?_, fun ⟨⟨i, hi⟩, hx⟩ ↦ hx ▸ hf' i hi⟩
  obtain ⟨i, hi, rfl⟩ := hf x hx
  use ⟨i, hi⟩
/-
**Set.ncard_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_congr {t : Set β} (f : forall a in s, β) (h₁ : forall a ha, f a ha i
n t) (h₂ : forall a b ha hb, f a ha = f b hb -> a = b) (h₃ : forall b in t, exis
ts a ha, f a ha = b) : s.ncard = t.ncard
参数：f : forall a in s, β；h₁ : forall a ha, f a ha in t；h₂ : forall a b ha hb, f a
 ha = f b hb -> a = b；h₃ : forall b in t, exists a ha, f a ha = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem ncard_congr {t : Set β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    s.ncard = t.ncard := by
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [f', Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  simp_rw [← _root_.Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective f' hbij)
/-
**Set.ncard_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_congr' {S : Set α} {T : Set β} (f : S ≃ T) : Set.ncard S = Set.ncard
 T
参数：f : S ≃ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_congr`：toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = 
toNat #β
-/
theorem ncard_congr' {S : Set α} {T : Set β} (f : S ≃ T) : Set.ncard S = Set.ncard T :=
  Cardinal.toNat_congr f
/-
**Set.ncard_le_ncard_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_ncard_of_injOn {t : Set β} (f : α -> β) (hf : forall a in s, f a 
in t) (f_inj : InjOn f s) (ht : t.Finite
参数：f : α -> β；hf : forall a in s, f a in t；f_inj : InjOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.encard_le_encard_of_injOn`：encard_le_encard_of_injOn (hf : MapsTo f 
s t) (f_inj : InjOn f s) : s.encard <= t.encard
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.finite_of_encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β}, s.Finite → t.encard ≤ s.encard → t.Finite
-/
theorem ncard_le_ncard_of_injOn {t : Set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : InjOn f s)
    (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  have hle := encard_le_encard_of_injOn hf f_inj
  to_encard_tac; rwa [ht.cast_ncard_eq, (ht.finite_of_encard_le hle).cast_ncard_eq]
/-
**Set.ncard_range_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_range_of_injective (hf : Function.Injective f) : (range f).ncard = N
at.card α
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
-/
theorem ncard_range_of_injective (hf : Function.Injective f) :
    (range f).ncard = Nat.card α := by
  rw [← image_univ, ncard_image_of_injective univ hf, ncard_univ]
/-
**Set.BijOn.ncard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {t : Set β}, Set.B
ijOn f s t → s.ncard = t.ncard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_congr'`：ncard_congr' {S : Set α} {T : Set β} (f : S ≃ T) : Set
.ncard S = Set.ncard T
-/
theorem BijOn.ncard_eq {t : Set β} (h : Set.BijOn f s t) : s.ncard = t.ncard := ncard_congr' h.equiv

/-- A version of the pigeonhole principle for `Set`s rather than `Finset`s.

See also `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_encard_lt_of_maps_to`. -/
/-
**Set.exists_ne_map_eq_of_ncard_lt_of_maps_to** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncar
d) {f : α -> β} (hf : forall a in s, f a in t) (ht : t.Finite
参数：hc : t.ncard < s.ncard；hf : forall a in s, f a in t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Set.ncard_le_ncard_of_injOn`：ncard_le_ncard_of_injOn {t : Set β} (f : α 
-> β) (hf : forall a in s, f a in t) (f_inj : InjOn f s) (ht : t.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
A version of the pigeonhole principle for `Set`s rather than `Finset`s.

See also `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_encard_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Finite := by toFinite_tac) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra h'
  simp only [Ne, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_gt hc
/-
**Set.le_ncard_of_inj_on_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_ncard_of_inj_on_range {n : Nat} (f : Nat -> α) (hf : forall i < n, f i 
in s) (f_inj : forall i < n, forall j < n, f i = f j -> i = j) (hs : s.Finite
参数：f : Nat -> α；hf : forall i < n, f i in s；f_inj : forall i < n, forall j < n, 
f i = f j -> i = j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用引理 `Finset.le_card_of_inj_on_range`：le_card_of_inj_on_range (f : Nat -> α) (
hf : forall i < n, f i in s) (f_inj : forall i < n, forall j < n, f i = f j -> i
 = j) : n <= #s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite := by toFinite_tac) :
    n ≤ s.ncard := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa
/-
**Set.surj_on_of_inj_on_of_ncard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surj_on_of_inj_on_of_ncard_le {t : Set β} (f : forall a in s, β) (hf : for
all a ha, f a ha in t) (hinj : forall a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ -> a₁ =
 a₂) (hst : t.ncard <= s.ncard) (ht : t.Finite
参数：f : forall a in s, β；hf : forall a ha, f a ha in t；hinj : forall a₁ a₂ ha₁ ha
₂, f a₁ ha₁ = f a₂ ha₂ -> a₁ = a₂；hst : t.ncard <= s.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.surj_on_of_inj_on_of_card_le`：surj_on_of_inj_on_of_card_le (f : f
orall a in s, β) (hf : forall a ha, f a ha in t) (hinj : forall a₁ a₂ ha₁ ha₂, f
 a₁ ha₁ = f a₂ ha₂ -> a₁ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Set.ncard_eq_toFinset_card'`：ncard_eq_toFinset_card' (s : Set α) [Fintyp
e s] : s.ncard = s.toFinset.card
-/
theorem surj_on_of_inj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.ncard ≤ s.ncard)
    (ht : t.Finite := by toFinite_tac) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  intro b hb
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [f', Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  convert! @Finset.surj_on_of_inj_on_of_card_le _ _ _ t.toFinset f'' _ _ _ _ (by simpa) using 1
  · simp [f'']
  · simp [f'', hf]
  · intro a₁ a₂ ha₁ ha₂ h
    rw [mem_toFinset] at ha₁ ha₂
    exact hinj _ _ ha₁ ha₂ h
  rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card']
/-
**Set.inj_on_of_surj_on_of_ncard_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inj_on_of_surj_on_of_ncard_le {t : Set β} (f : forall a in s, β) (hf : for
all a ha, f a ha in t) (hsurj : forall b in t, exists a ha, f a ha = b) (hst : s
.ncard <= t.ncard) ⦃a₁⦄ (ha₁ : a₁ in s) ⦃a₂⦄ (ha₂ : a₂ in s) (ha₁a₂ : f a₁ ha₁ =
 f a₂ ha₂) (hs : s.Finite
参数：f : forall a in s, β；hf : forall a ha, f a ha in t；hsurj : forall b in t, exi
sts a ha, f a ha = b；hst : s.ncard <= t.ncard；ha₁ : a₁ in s；ha₂ : a₂ in s；ha₁a₂ 
: f a₁ ha₁ = f a₂ ha₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.inj_on_of_surj_on_of_card_le`：inj_on_of_surj_on_of_card_le (f : f
orall a in s, β) (hf : forall a ha, f a ha in t) (hsurj : forall b in t, exists 
a ha, f a ha = b) (hst : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_eq_toFinset_card'`：ncard_eq_toFinset_card' (s : Set α) [Fintyp
e s] : s.ncard = s.toFinset.card
-/
theorem inj_on_of_surj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, f a ha = b) (hst : s.ncard ≤ t.ncard) ⦃a₁⦄ (ha₁ : a₁ ∈ s) ⦃a₂⦄
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) (hs : s.Finite := by toFinite_tac) :
    a₁ = a₂ := by
  classical
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  have := hs.fintype
  have := Fintype.ofSurjective _ hsurj
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  exact
    @Finset.inj_on_of_surj_on_of_card_le _ _ _ t.toFinset f''
      (fun a ha ↦ by { rw [mem_toFinset] at ha ⊢; exact hf a ha }) (by simpa)
      (by { rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card'] }) a₁
      (by simpa) a₂ (by simpa) (by simpa)
/-
**Set.ncard_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_coe {α : Type*} (s : Set α) : Set.ncard (Set.univ : Set (Set.Elem s)
) = s.ncard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ncard_coe {α : Type*} (s : Set α) :
    Set.ncard (Set.univ : Set (Set.Elem s)) = s.ncard := by simp
/-
**Set.ncard_graphOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (s : Set α) (f : α → β), (Set.graphOn f s)
.ncard = s.ncard
参数：s : Set α；f : α → β；Set.graphOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.ncard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → (f '' s).ncard = s.ncard
· 使用引理 `Set.fst_injOn_graph`：fst_injOn_graph : (s.graphOn f).InjOn Prod.fst
· 使用引理 `Set.image_fst_graphOn`：image_fst_graphOn (f : α -> β) (s : Set α) : Prod
.fst '' graphOn f s = s
-/
@[simp] lemma ncard_graphOn (s : Set α) (f : α → β) : (s.graphOn f).ncard = s.ncard := by
  rw [← fst_injOn_graph.ncard_image, image_fst_graphOn]

/-- Given a finite set `s`, the number of subsets of `s` with cardinality `n` is
`s.ncard.choose n`. See also `Finset.card_powersetCard`. -/
/-
**Set.ncard_powerset_ncard** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_powerset_ncard (hs : s.Finite) (n : Nat) : {t subseteq s | t.ncard =
 n}.ncard = s.ncard.choose n
参数：hs : s.Finite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mem_range_coe_iff`：mem_range_coe_iff {s : Set α} : s in Set.range
 ((↑) : Finset α -> Set α) ↔ s.Finite where mp
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a finite set `s`, the number of subsets of `s` with cardinality `n` is
`s.ncard.choose n`. See also `Finset.card_powersetCard`.
-/
lemma ncard_powerset_ncard (hs : s.Finite) (n : ℕ) :
    {t ⊆ s | t.ncard = n}.ncard = s.ncard.choose n := by
  lift s to Finset α using hs
  have h₁ : {t ⊆ (s : Set α) | t.ncard = n} ⊆ range ((↑) : Finset α → Set α) := by
    intro t ht
    rw [Finset.mem_range_coe_iff]
    exact s.finite_toSet.subset ht.1
  have h₂ : (↑) ⁻¹' {t ⊆ (s : Set α) | t.ncard = n} = (s.powersetCard n : Set (Finset α)) := by
    ext t
    simp
  grind [ncard_coe_finset, ncard_preimage_of_injective_subset_range, Finset.card_powersetCard]

section Lattice

/-
**Set.ncard_union_add_ncard_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_union_add_ncard_inter (s t : Set α) (hs : s.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.encard_union_add_encard_inter`：encard_union_add_encard_inter (s t : 
Set α) : (s union t).encard + (s inter t).encard = s.encard + t.encard
-/
theorem ncard_union_add_ncard_inter (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq,
    (hs.subset inter_subset_left).cast_ncard_eq, encard_union_add_encard_inter]
/-
**Set.ncard_inter_add_ncard_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.ncard_union_add_ncard_inter`：ncard_union_add_ncard_inter (s t : Set 
α) (hs : s.Finite
-/
theorem ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard := by
  rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]
/-
**Set.ncard_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_union_le (s t : Set α) : (s union t).ncard <= s.ncard + t.ncard
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.encard_union_le`：encard_union_le (s t : Set α) : (s union t).encard 
<= s.encard + t.encard
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem ncard_union_le (s t : Set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard := by
  obtain (h | h) := (s ∪ t).finite_or_infinite
  · to_encard_tac
    rw [h.cast_ncard_eq, (h.subset subset_union_left).cast_ncard_eq,
      (h.subset subset_union_right).cast_ncard_eq]
    apply encard_union_le
  rw [h.ncard]
  apply zero_le
/-
**Set.ncard_union_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
参数：h : Disjoint s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
-/
theorem ncard_union_eq (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard := by
  to_encard_tac
  rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq, encard_union_eq h]
/-
**Set.ncard_union_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_union_eq_iff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_union_add_ncard_inter`：ncard_union_add_ncard_inter (s t : Set 
α) (hs : s.Finite
· 使用定理 `left_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a = a + b ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ncard_union_eq_iff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard ↔ Disjoint s t := by
  rw [← ncard_union_add_ncard_inter s t hs ht, left_eq_add,
    ncard_eq_zero (hs.inter_of_left t), disjoint_iff_inter_eq_empty]
/-
**Set.ncard_union_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_union_lt (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Set.ncard_union_le`：ncard_union_le (s t : Set α) : (s union t).ncard <= 
s.ncard + t.ncard
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ncard_union_eq_iff`：ncard_union_eq_iff (hs : s.Finite
-/
theorem ncard_union_lt (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) (h : ¬ Disjoint s t) :
    (s ∪ t).ncard < s.ncard + t.ncard :=
  (ncard_union_le s t).lt_of_ne (mt (ncard_union_eq_iff hs ht).mp h)
/-
**Set.ncard_sdiff_add_ncard_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff_add_ncard_of_subset (h : s subseteq t) (ht : t.Finite
参数：h : s subseteq t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.encard_sdiff_add_encard_of_subset`：encard_sdiff_add_encard_of_subset
 (h : s subseteq t) : (t \ s).encard + s.encard = t.encard
-/
theorem ncard_sdiff_add_ncard_of_subset (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  to_encard_tac
  rw [ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq, ht.sdiff.cast_ncard_eq,
    encard_sdiff_add_encard_of_subset h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_add_ncard_of_subset := ncard_sdiff_add_ncard_of_subset

/-- This is the same as `ncard_sdiff` but we require `t` to be finite instead. -/
/-
**Set.ncard_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff' (hst : s subseteq t) (ht : t.Finite
参数：hst : s subseteq t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_sdiff_add_ncard_of_subset`：ncard_sdiff_add_ncard_of_subset (h 
: s subseteq t) (ht : t.Finite
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
This is the same as `ncard_sdiff` but we require `t` to be finite instead.
-/
theorem ncard_sdiff' (hst : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  rw [← ncard_sdiff_add_ncard_of_subset hst ht, add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")] alias ncard_diff' := ncard_sdiff'

/-- This is the same as `ncard_sdiff'` but we require `s` to be finite instead. -/
/-
**Set.ncard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff (hst : s subseteq t) (hs : s.Finite
参数：hst : s subseteq t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Set.ncard_sdiff'`：ncard_sdiff' (hst : s subseteq t) (ht : t.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Nat.zero_sub`：∀ (n : ℕ), 0 - n = 0
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite

--- 原说明 ---
This is the same as `ncard_sdiff'` but we require `s` to be finite instead.
-/
theorem ncard_sdiff (hst : s ⊆ t) (hs : s.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  obtain ht | ht := t.finite_or_infinite
  · exact ncard_sdiff' hst ht
  · rw [ht.ncard, Nat.zero_sub, (ht.sdiff hs).ncard]

@[deprecated (since := "2026-06-03")] alias ncard_diff := ncard_sdiff
/-
**Set.cast_ncard_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：cast_ncard_sdiff {R : Type*} [AddGroupWithOne R] (hst : s subseteq t) (ht 
: t.Finite) : ((t \ s).ncard : R) = t.ncard - s.ncard
参数：hst : s subseteq t；ht : t.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_sdiff`：ncard_sdiff (hst : s subseteq t) (hs : s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
-/
lemma cast_ncard_sdiff {R : Type*} [AddGroupWithOne R] (hst : s ⊆ t) (ht : t.Finite) :
    ((t \ s).ncard : R) = t.ncard - s.ncard := by
  rw [ncard_sdiff hst (ht.subset hst), Nat.cast_sub (ncard_le_ncard hst ht)]
/-
**Set.ncard_le_ncard_sdiff_add_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_ncard_sdiff_add_ncard (s t : Set α) (ht : t.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.encard_le_encard_sdiff_add_encard`：encard_le_encard_sdiff_add_encard
 (s t : Set α) : s.encard <= (s \ t).encard + t.encard
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem ncard_le_ncard_sdiff_add_ncard (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ (s \ t).ncard + t.ncard := by
  rcases s.finite_or_infinite with hs | hs
  · to_encard_tac
    rw [ht.cast_ncard_eq, hs.cast_ncard_eq, hs.sdiff.cast_ncard_eq]
    apply encard_le_encard_sdiff_add_encard
  convert! Nat.zero_le _
  rw [hs.ncard]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_diff_add_ncard := ncard_le_ncard_sdiff_add_ncard
/-
**Set.le_ncard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_ncard_sdiff (s t : Set α) (hs : s.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.ncard_le_ncard_sdiff_add_ncard`：ncard_le_ncard_sdiff_add_ncard (s t 
: Set α) (ht : t.Finite
-/
theorem le_ncard_sdiff (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    t.ncard - s.ncard ≤ (t \ s).ncard :=
  tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_sdiff_add_ncard _ _ hs)

@[deprecated (since := "2026-06-03")] alias le_ncard_diff := le_ncard_sdiff
/-
**Set.ncard_sdiff_add_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sdiff_add_ncard (s t : Set α) (hs : s.Finite
参数：s t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_union_eq`：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
-/
theorem ncard_sdiff_add_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) :
    (s \ t).ncard + t.ncard = (s ∪ t).ncard := by
  rw [← ncard_union_eq disjoint_sdiff_left hs.sdiff ht, sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias ncard_diff_add_ncard := ncard_sdiff_add_ncard
/-
**Set.sdiff_nonempty_of_ncard_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.Finite
参数：h : s.ncard < t.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
-/
theorem sdiff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by toFinite_tac) : (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne, sdiff_eq_empty]
  exact fun h' ↦ h.not_ge (ncard_le_ncard h' hs)

@[deprecated (since := "2026-06-03")]
alias diff_nonempty_of_ncard_lt_ncard := sdiff_nonempty_of_ncard_lt_ncard
/-
**Set.exists_mem_notMem_of_ncard_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_mem_notMem_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.Finite
参数：h : s.ncard < t.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_nonempty_of_ncard_lt_ncard`：sdiff_nonempty_of_ncard_lt_ncard (
h : s.ncard < t.ncard) (hs : s.Finite
-/
theorem exists_mem_notMem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by toFinite_tac) : ∃ e, e ∈ t ∧ e ∉ s :=
  sdiff_nonempty_of_ncard_lt_ncard h hs
/-
**Set.ncard_inter_add_ncard_sdiff_eq_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s t : Set α),   autoParam s.Finite Set.ncard_inter_add_n
card_sdiff_eq_ncard._auto_1 → (s ∩ t).ncard + (s \ t).ncard = s.ncard
参数：s t : Set α；s ∩ t；s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_union_eq`：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
-/
@[simp] theorem ncard_inter_add_ncard_sdiff_eq_ncard (s t : Set α)
    (hs : s.Finite := by toFinite_tac) : (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  rw [← ncard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right)
    (hs.inter_of_left _) hs.sdiff, union_comm, sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias ncard_inter_add_ncard_diff_eq_ncard := ncard_inter_add_ncard_sdiff_eq_ncard
/-
**Set.ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `S
et`。
形式化陈述：ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_inter_add_ncard_sdiff_eq_ncard`：∀ {α : Type u_1} (s t : Set α)
,   autoParam s.Finite Set.ncard_inter_add_ncard_sdiff_eq_ncard._auto_1 → (s ∩ t
).ncard + (s \ t).ncard = s.nc…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs, ← ncard_inter_add_ncard_sdiff_eq_ncard t s ht,
    inter_comm, add_right_inj]

@[deprecated (since := "2026-06-03")]
alias ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff := ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff
/-
**Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `S
et`。
形式化陈述：ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_inter_add_ncard_sdiff_eq_ncard`：∀ {α : Type u_1} (s t : Set α)
,   autoParam s.Finite Set.ncard_inter_add_ncard_sdiff_eq_ncard._auto_1 → (s ∩ t
).ncard + (s \ t).ncard = s.nc…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs, ← ncard_inter_add_ncard_sdiff_eq_ncard t s ht,
    inter_comm, add_le_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_iff_ncard_diff_le_ncard_diff := ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff
/-
**Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `S
et`。
形式化陈述：ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_inter_add_ncard_sdiff_eq_ncard`：∀ {α : Type u_1} (s t : Set α)
,   autoParam s.Finite Set.ncard_inter_add_ncard_sdiff_eq_ncard._auto_1 → (s ∩ t
).ncard + (s \ t).ncard = s.nc…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs, ← ncard_inter_add_ncard_sdiff_eq_ncard t s ht,
    inter_comm, add_lt_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff := ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff
/-
**Set.ncard_add_ncard_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_add_ncard_compl (s : Set α) (hs : s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.ncard_union_eq`：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
-/
theorem ncard_add_ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ, ← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]
/-
**Set.ncard_compl_add_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_compl_add_ncard (s : Set α) (hs : s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
-/
theorem ncard_compl_add_ncard (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : sᶜ.ncard + s.ncard = Nat.card α := by
  rw [add_comm, ncard_add_ncard_compl s hs hsc]
/-
**Set.ncard_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_compl (s : Set α) (hs : s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
-/
theorem ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : sᶜ.ncard = Nat.card α - s.ncard := by
  rw [← ncard_add_ncard_compl s hs hsc, Nat.add_sub_cancel_left]
/-
**Set.ncard_compl_of_ncard_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_compl_of_ncard_eq_add [Finite α] (s : Set α) {n : Nat} (h : Nat.card
 α = n + s.ncard) : sᶜ.ncard = n
参数：s : Set α；h : Nat.card α = n + s.ncard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_right_cancel_iff`：∀ {m k n : ℕ}, m + n = k + n ↔ m = k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_compl_add_ncard`：ncard_compl_add_ncard (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem ncard_compl_of_ncard_eq_add [Finite α] (s : Set α) {n : ℕ}
    (h : Nat.card α = n + s.ncard) :
    sᶜ.ncard = n := by
  rwa [← ncard_compl_add_ncard s, Nat.add_right_cancel_iff] at h
/-
**Set.eq_univ_iff_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_univ_iff_ncard [Finite α] (s : Set α) : s = univ ↔ ncard s = Nat.card α
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `left_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a = a + b ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_univ_iff_ncard [Finite α] (s : Set α) :
    s = univ ↔ ncard s = Nat.card α := by
  rw [← compl_empty_iff, ← ncard_eq_zero, ← ncard_add_ncard_compl s, left_eq_add]
/-
**Set.even_ncard_compl_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：even_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) : 
Even sᶜ.ncard ↔ Even s.ncard
参数：heven : Even (Nat.card α)；s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.even_add`：∀ {m n : ℕ}, Even (m + n) ↔ (Even m ↔ Even n)
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma even_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) :
    Even sᶜ.ncard ↔ Even s.ncard := by
  rwa [iff_comm, ← Nat.even_add, ncard_add_ncard_compl]
/-
**Set.odd_ncard_compl_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：odd_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) : O
dd sᶜ.ncard ↔ Odd s.ncard
参数：heven : Even (Nat.card α)；s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用引理 `Set.even_ncard_compl_iff`：even_ncard_compl_iff [Finite α] (heven : Even 
(Nat.card α)) (s : Set α) : Even sᶜ.ncard ↔ Even s.ncard
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma odd_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) :
    Odd sᶜ.ncard ↔ Odd s.ncard := by
  rw [← Nat.not_even_iff_odd, even_ncard_compl_iff heven, Nat.not_even_iff_odd]
/-
**Set.nonempty_inter_of_lt_ncard_add_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_inter_of_lt_ncard_add_ncard [Finite α] (h : Nat.card α < s.ncard 
+ t.ncard) : (s inter t).Nonempty
参数：h : Nat.card α < s.ncard + t.ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Set.ncard_le_card`：ncard_le_card [Finite α] (s : Set α) : s.ncard <= Nat
.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_union_add_ncard_inter`：ncard_union_add_ncard_inter (s t : Set 
α) (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem nonempty_inter_of_lt_ncard_add_ncard [Finite α]
    (h : Nat.card α < s.ncard + t.ncard) : (s ∩ t).Nonempty := by
  rw [← ncard_union_add_ncard_inter s t] at h
  replace h := (s ∪ t).ncard_le_card.trans_lt h
  rwa [lt_add_iff_pos_right, ncard_pos] at h
/-
**Set.nonempty_inter_of_le_ncard_add_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_inter_of_le_ncard_add_ncard [Finite α] (h' : Nat.card α <= s.ncar
d + t.ncard) (h : s union t != univ) : (s inter t).Nonempty
参数：h' : Nat.card α <= s.ncard + t.ncard；h : s union t != univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.ncard_lt_card`：ncard_lt_card [Finite α] (h : s != univ) : s.ncard < 
Nat.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_union_add_ncard_inter`：ncard_union_add_ncard_inter (s t : Set 
α) (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem nonempty_inter_of_le_ncard_add_ncard [Finite α]
    (h' : Nat.card α ≤ s.ncard + t.ncard) (h : s ∪ t ≠ univ) :
    (s ∩ t).Nonempty := by
  rw [← ncard_union_add_ncard_inter s t] at h'
  replace h := (ncard_lt_card h).trans_le h'
  rwa [lt_add_iff_pos_right, ncard_pos] at h
/-
**Set.union_ne_univ_of_ncard_add_ncard_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_ne_univ_of_ncard_add_ncard_lt (h : s.ncard + t.ncard < Nat.card α) :
 s union t != univ
参数：h : s.ncard + t.ncard < Nat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.ncard_union_le`：ncard_union_le (s t : Set α) : (s union t).ncard <= 
s.ncard + t.ncard
-/
theorem union_ne_univ_of_ncard_add_ncard_lt
    (h : s.ncard + t.ncard < Nat.card α) : s ∪ t ≠ univ := by
  contrapose! h
  rw [← ncard_univ, ← h]
  exact ncard_union_le s t
/-
**Set.nonempty_inter_compl_of_ncard_add_ncard_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`
。
形式化陈述：nonempty_inter_compl_of_ncard_add_ncard_lt (h : s.ncard + t.ncard < Nat.ca
rd α) : (sᶜ inter tᶜ).Nonempty
参数：h : s.ncard + t.ncard < Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用定理 `Set.union_ne_univ_of_ncard_add_ncard_lt`：union_ne_univ_of_ncard_add_ncar
d_lt (h : s.ncard + t.ncard < Nat.card α) : s union t != univ
-/
theorem nonempty_inter_compl_of_ncard_add_ncard_lt
    (h : s.ncard + t.ncard < Nat.card α) : (sᶜ ∩ tᶜ).Nonempty := by
  rw [← compl_union, nonempty_compl]
  exact union_ne_univ_of_ncard_add_ncard_lt h

end Lattice

/-- Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively, there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`. -/
/-
**Set.exists_subsuperset_card_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_subsuperset_card_eq {n : Nat} (hst : s subseteq t) (hsn : s.ncard <
= n) (hnt : n <= t.ncard) : exists u, s subseteq u ∧ u subseteq t ∧ u.ncard = n
参数：hst : s subseteq t；hsn : s.ncard <= n；hnt : n <= t.ncard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_or_finite`：∀ {α : Type u} (s : Set α), s.Infinite ∨ s.Finit
e
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Finset.exists_subsuperset_card_eq`：exists_subsuperset_card_eq (hst : s s
ubseteq t) (hsn : #s <= n) (hnt : n <= #t) : exists u, s subseteq u ∧ u subseteq
 t ∧ #u = n
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd

--- 原说明 ---
Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively,
 there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`.
-/
lemma exists_subsuperset_card_eq {n : ℕ} (hst : s ⊆ t) (hsn : s.ncard ≤ n) (hnt : n ≤ t.ncard) :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ u.ncard = n := by
  obtain ht | ht := t.infinite_or_finite
  · rw [ht.ncard, Nat.le_zero, ← ht.ncard] at hnt
    exact ⟨t, hst, Subset.rfl, hnt.symm⟩
  lift s to Finset α using ht.subset hst
  lift t to Finset α using ht
  obtain ⟨u, hsu, hut, hu⟩ := Finset.exists_subsuperset_card_eq (mod_cast hst) (by simpa using hsn)
    (mod_cast hnt)
  exact ⟨u, mod_cast hsu, mod_cast hut, mod_cast hu⟩

/-- We can shrink a set to any smaller size. -/
/-
**Set.exists_subset_card_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_subset_card_eq {n : Nat} (hns : n <= s.ncard) : exists t subseteq s
, t.ncard = n
参数：hns : n <= s.ncard。
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
· 使用引理 `Set.exists_subsuperset_card_eq`：exists_subsuperset_card_eq {n : Nat} (hs
t : s subseteq t) (hsn : s.ncard <= n) (hnt : n <= t.ncard) : exists u, s subset
eq u ∧ u subseteq t …
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
We can shrink a set to any smaller size.
-/
lemma exists_subset_card_eq {n : ℕ} (hns : n ≤ s.ncard) : ∃ t ⊆ s, t.ncard = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns
/-
**Set.Infinite.exists_subset_ncard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Infinite → ∀ (k : ℕ), ∃ t ⊆ s, t.Finite ∧ 
t.ncard = k
参数：k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.Infinite.exists_subset_card_eq`：∀ {α : Type u} {s : Set α}, s.Infini
te → ∀ (n : ℕ), ∃ t, ↑t ⊆ s ∧ t.card = n
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : ℕ) :
    ∃ t, t ⊆ s ∧ t.Finite ∧ t.ncard = k := by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), ?_⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp
/-
**Set.Infinite.exists_superset_ncard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`
。
形式化陈述：∀ {α : Type u_1} {s t : Set α},   t.Infinite → s ⊆ t → s.Finite → ∀ {k : ℕ
}, s.ncard ≤ k → ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.exists_subset_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Inf
inite → ∀ (k : ℕ), ∃ t ⊆ s, t.Finite ∧ t.ncard = k
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_union_eq`：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem Infinite.exists_superset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) : ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.sdiff hs).exists_subset_ncard_eq (k - s.ncard)
  refine ⟨s ∪ s₁, subset_union_left, union_subset hst (hs₁.trans sdiff_subset), ?_⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]
/-
**Set.exists_subset_or_subset_of_two_mul_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set
`。
形式化陈述：exists_subset_or_subset_of_two_mul_lt_ncard {n : Nat} (hst : 2 * n < (s un
ion t).ncard) : exists r : Set α, n < r.ncard ∧ (r subseteq s ∨ r subseteq t)
参数：hst : 2 * n < (s union t).ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_ncard_ne_zero`：finite_of_ncard_ne_zero (hs : s.ncard != 0)
 : s.Finite
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Finset.exists_subset_or_subset_of_two_mul_lt_card`：exists_subset_or_subs
et_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : Nat} (hXY : 2 * n < 
#(X union Y)) : exists C : Finset α, n …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.toFinset_union`：∀ {α : Type u} {s t : Set α} [inst : Decidabl
eEq α] (hs : s.Finite) (ht : t.Finite) (h : (s ∪ t).Finite),   h.toFinset = hs.t
oFinset ∪ ht.to…
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ} (hst : 2 * n < (s ∪ t).ncard) :
    ∃ r : Set α, n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) := by
  classical
  have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu,
    Finite.toFinset_union (hu.subset subset_union_left)
      (hu.subset subset_union_right)] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hst
  exact ⟨r', by simpa, by simpa using hr'⟩
/-
**Set._root_.Finset.exists_not_mem_of_card_lt_enatCard** 是 Mathlib 中的一个引理，位于命名空间
 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.exists_not_mem_of_card_lt_enatCard {s : Finset α} (hs : s.card < ENat.card α) :
    ∃ a, a ∉ s := by
  contrapose! hs
  simp [← Set.encard_coe_eq_coe_finsetCard, Set.eq_univ_of_forall (α := α) (s := s) hs]

/-! ### Explicit description of a set from its cardinality -/

/-
**Set.ncard_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.ncard = 1 ↔ ∃ a, s = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_ncard_ne_zero`：finite_of_ncard_ne_zero (hs : s.ncard != 0)
 : s.Finite
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_eq_toFinset_card'`：ncard_eq_toFinset_card' (s : Set α) [Fintyp
e s] : s.ncard = s.toFinset.card
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### Explicit description of a set from its cardinality
-/
@[simp] theorem ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} := by
  refine ⟨fun h ↦ ?_, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine h.imp fun a ha ↦ ?_
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only [Finset.ext_iff, mem_toFinset, Finset.mem_singleton] at ha
  exact ha
/-
**Set.exists_eq_insert_iff_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_eq_insert_iff_ncard (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.toFinset_subset_toFinset`：∀ {α : Type u} {s t : Set α} {hs : 
s.Finite} {ht : t.Finite}, hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t
· 使用定理 `Finset.exists_eq_insert_iff`：exists_eq_insert_iff [DecidableEq α] : (exi
sts a ∉ s, insert a s = t) ↔ s subseteq t ∧ #s + 1 = #t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
-/
theorem exists_eq_insert_iff_ncard (hs : s.Finite := by toFinite_tac) :
    (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard := by
  classical
  rcases t.finite_or_infinite with ht | ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ← @Finite.toFinset_subset_toFinset _ _ _ hs ht, ← Finset.exists_eq_insert_iff]
    convert! Iff.rfl using 2; simp only [Finite.mem_toFinset]
    ext x
    simp [Finset.ext_iff, Set.ext_iff]
  simp only [ht.ncard, add_eq_zero, and_false, iff_false, not_exists, not_and,
    reduceCtorEq]
  rintro x - rfl
  exact ht (hs.insert x)
/-
**Set.ncard_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_one (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ncard_le_one (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]
/-
**Set.ncard_le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} [Finite ↑s], s.ncard ≤ 1 ↔ s.Subsingleton
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_le_one`：ncard_le_one (hs : s.Finite
-/
@[simp] theorem ncard_le_one_iff_subsingleton [Finite s] :
    s.ncard ≤ 1 ↔ s.Subsingleton :=
  ncard_le_one <| inferInstanceAs (Finite s)
/-
**Set.ncard_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_one_iff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_le_one`：ncard_le_one (hs : s.Finite
-/
theorem ncard_le_one_iff (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [ncard_le_one hs]
  tauto
/-
**Set.ncard_le_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_one_iff_eq (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_le_one_iff`：ncard_le_one_iff (hs : s.Finite
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem ncard_le_one_iff_eq (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine ⟨fun h ↦ Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy ↦ h hy hx⟩, ?_⟩
  grind
/-
**Set.ncard_le_one_iff_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_one_iff_subset_singleton [Nonempty α] (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ncard_le_one_iff_subset_singleton [Nonempty α]
    (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]

/-- A `Set` of a subsingleton type has cardinality at most one. -/
/-
**Set.ncard_le_one_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard <= 1
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `Finset.card_le_one_of_subsingleton`：card_le_one_of_subsingleton [Subsing
leton α] (s : Finset α) : #s <= 1

--- 原说明 ---
A `Set` of a subsingleton type has cardinality at most one.
-/
theorem ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard ≤ 1 := by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _
/-
**Set.one_lt_ncard_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_lt_ncard_iff_nontrivial [Finite s] : 1 < s.ncard ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_subsingleton_iff`：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Non
trivial
· 使用定理 `Set.ncard_le_one_iff_subsingleton`：∀ {α : Type u_1} {s : Set α} [Finite 
↑s], s.ncard ≤ 1 ↔ s.Subsingleton
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_lt_ncard_iff_nontrivial [Finite s] :
    1 < s.ncard ↔ s.Nontrivial := by
  rw [← not_subsingleton_iff, ← ncard_le_one_iff_subsingleton, not_le]
/-
**Set.one_lt_ncard_iff_nontrivial_and_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_lt_ncard_iff_nontrivial_and_finite : 1 < s.ncard ↔ s.Nontrivial ∧ s.Fi
nite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_ncard_pos`：finite_of_ncard_pos (hs : 0 < s.ncard) : s.Fini
te
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.one_lt_ncard_iff_nontrivial`：one_lt_ncard_iff_nontrivial [Finite s] 
: 1 < s.ncard ↔ s.Nontrivial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
-/
theorem one_lt_ncard_iff_nontrivial_and_finite :
    1 < s.ncard ↔ s.Nontrivial ∧ s.Finite := by
  refine ⟨fun hs ↦ ?_, fun ⟨hs_nontrivial, hs_finite⟩ ↦ ?_⟩
  · have := finite_of_ncard_pos (Nat.zero_lt_of_lt hs)
    rw [← Set.finite_coe_iff] at this
    exact ⟨one_lt_ncard_iff_nontrivial.mp hs, this⟩
  · rw [← Set.finite_coe_iff] at hs_finite
    rwa [one_lt_ncard_iff_nontrivial]
/-
**Set.one_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_lt_ncard (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_ncard (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]
/-
**Set.one_lt_ncard_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_lt_ncard_iff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.one_lt_ncard`：one_lt_ncard (hs : s.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_ncard hs]
  simp only [exists_and_left]
/-
**Set.one_lt_ncard_of_nonempty_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：one_lt_ncard_of_nonempty_of_even (hs : Set.Finite s) (hn : Set.Nonempty s
参数：hs : Set.Finite s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
-/
lemma one_lt_ncard_of_nonempty_of_even (hs : Set.Finite s) (hn : Set.Nonempty s := by toFinite_tac)
    (he : Even (s.ncard)) : 1 < s.ncard := by
  rw [← Set.ncard_pos hs] at hn
  have : s.ncard ≠ 1 := fun h ↦ by simp [h] at he
  lia
/-
**Set.two_lt_ncard_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：two_lt_ncard_iff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem two_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]
/-
**Set.two_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：two_lt_ncard (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.two_lt_ncard_iff`：two_lt_ncard_iff (hs : s.Finite
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem two_lt_ncard (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [two_lt_ncard_iff hs, exists_and_left]
/-
**Set.three_lt_ncard_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：three_lt_ncard_iff (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem three_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    3 < s.ncard ↔
    ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.three_lt_card_iff, Finite.mem_toFinset]
/-
**Set.three_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：three_lt_ncard (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.three_lt_ncard_iff`：three_lt_ncard_iff (hs : s.Finite
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem three_lt_ncard (hs : s.Finite := by toFinite_tac) :
    3 < s.ncard ↔
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [three_lt_ncard_iff hs, exists_and_left]
/-
**Set.exists_ne_of_one_lt_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : exists b, b in s ∧ 
b != a
参数：hs : 1 < s.ncard；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_ncard_ne_zero`：finite_of_ncard_ne_zero (hs : s.ncard != 0)
 : s.Finite
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.exists_mem_ne`：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in 
s, b != a
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
-/
theorem exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  have hsf := finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_mem_ne hs a
/-
**Set.eq_insert_of_ncard_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_insert_of_ncard_eq_succ {n : Nat} (h : s.ncard = n + 1) : exists a t, a
 ∉ t ∧ insert a t = s ∧ t.ncard = n
参数：h : s.ncard = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_ncard_pos`：finite_of_ncard_pos (hs : 0 < s.ncard) : s.Fini
te
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_succ`：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ ins
ert a t = s ∧ #t = n
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
    ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
  have hsf := finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf, Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h
  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine ⟨a, t, hat, ?_, ?_⟩
  · simp [Set.ext_iff, hts]
  · simp
/-
**Set.ncard_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_succ {n : Nat} (hs : s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_insert_of_ncard_eq_succ`：eq_insert_of_ncard_eq_succ {n : Nat} (h 
: s.ncard = n + 1) : exists a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_insert_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ 
s → autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (insert a s).ncard =
 s.ncard + 1
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem ncard_eq_succ {n : ℕ} (hs : s.Finite := by toFinite_tac) :
    s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  refine ⟨eq_insert_of_ncard_eq_succ, ?_⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h, ncard_insert_of_notMem hat (hs.subset ((subset_insert a t).trans_eq h))]
/-
**Set.ncard_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_two : s.ncard = 2 ↔ exists x y, x != y ∧ s = {x, y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_two`：encard_eq_two : s.encard = 2 ↔ exists x y, x != y ∧ s
 = {x, y}
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  rw [← encard_eq_two, ncard_def]
  simp
/-
**Set.ncard_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_three : s.ncard = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s 
= {x, y, z}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_three`：encard_eq_three {α : Type u_1} {s : Set α} : encard
 s = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ncard_eq_three : s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  rw [← encard_eq_three, ncard_def]
  simp
/-
**Set.ncard_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_eq_four : s.ncard = 4 ↔ exists x y z w, x != y ∧ x != z ∧ x != w ∧ y
 != z ∧ y != w ∧ z != w ∧ s = {x, y, z, w}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_four`：encard_eq_four {α : Type u_1} {s : Set α} : encard s
 = 4 ↔ exists x y z w, x != y ∧ x != z ∧ x != w ∧ y != z ∧ y != w ∧ z != w ∧ s =
 {x, y, …
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ncard_eq_four : s.ncard = 4 ↔
    ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ s = {x, y, z, w} := by
  rw [← encard_eq_four, ncard_def]
  simp
/-
**Set.ncard_sumEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ncard_sumEquiv_symm_apply {α : Type*} (s : Set α) : (Set.sumEquiv.symm (s,
 s)).ncard = s.ncard + s.ncard
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ncard_union_eq_iff`：ncard_union_eq_iff (hs : s.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.disjoint_image_inl_image_inr`：disjoint_image_inl_image_inr {u : Set 
α} {v : Set β} : Disjoint (Sum.inl '' u) (Sum.inr '' v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `Set.infinite_union`：infinite_union {s t : Set α} : (s union t).Infinite 
↔ s.Infinite ∨ t.Infinite
· 使用定理 `Set.Infinite.image`：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β},
 Set.InjOn f s → s.Infinite → (f '' s).Infinite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem ncard_sumEquiv_symm_apply {α : Type*} (s : Set α) :
    (Set.sumEquiv.symm (s, s)).ncard = s.ncard + s.ncard := by
  by_cases hs : s.Finite
  · simp [(ncard_union_eq_iff (.image _ hs) (.image _ hs)).2 disjoint_image_inl_image_inr,
      ncard_image_of_injective _ Sum.inl_injective, ncard_image_of_injective _ Sum.inr_injective]
  · simp [(infinite_union.2 <| .inl <| .image Sum.inl_injective.injOn hs).ncard, Infinite.ncard hs]

end ncard
end Set

/-- A surjective function `f : α → β` decreases cardinality by at most one if and only if
there is at most a collision between a unique pair of elements. -/
/-
**Function.Surjective.card_le_card_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.card_le_card_add_one_iff {α β : Type*} [Finite α] {f :
 α -> β} (hf : Function.Surjective f) : Nat.card α <= Nat.card β + 1 ↔ forall a 
b c d, f a = f b -> f c = f d -> a != b -> c != d -> {a, b} = ({c, d} : Set α)
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_of_isEmpty`：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_range_of_injective`：ncard_range_of_injective (hf : Function.In
jective f) : (range f).ncard = Nat.card α
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `Set.ncard_le_one_iff_subset_singleton`：ncard_le_one_iff_subset_singleton
 [Nonempty α] (hs : s.Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A surjective function `f : α → β` decreases cardinality by at most one if and on
ly if
there is at most a collision between a unique pair of elements.
-/
theorem Function.Surjective.card_le_card_add_one_iff
    {α β : Type*} [Finite α] {f : α → β} (hf : Function.Surjective f) :
    Nat.card α ≤ Nat.card β + 1 ↔ ∀ a b c d,
      f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α) := by
  rcases isEmpty_or_nonempty α
  · simp
  -- pick an inverse `g` to `f`
  let g := Function.surjInv hf
  -- the "decreases cardinality by at most one condition" becomes "`g` misses at most one element"
  rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf),
    ← Set.ncard_add_ncard_compl (Set.range g), add_le_add_iff_left]
  replace hf : ∀ b, f (g b) = b := Function.surjInv_eq hf
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Set.ncard_le_one_iff_subset_singleton] at h
    -- if `g` misses at most one element, let `x` be this element
    obtain ⟨x, hx⟩ := h
    simp only [Set.subset_def, Set.mem_compl_iff] at hx
    -- we show that the only possible collision is between `x` and `g (f x)`
    suffices ∀ a b : α, f a = f b → a ≠ b → a = x ∨ a = g (f x) by grind
    intro a b
    by_cases ha : a ∈ Set.range g <;> by_cases hb : b ∈ Set.range g <;> grind
  · -- we must show that any two elements `a` and `b` missed by `g` are equal
    rw [Set.ncard_le_one]
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, ← ne_eq]
    intro a ha b hb
    -- there is a collision between `a` and `g (f a)`, and between `b` and `g (f b)`
    simpa [(ha (f b)).symm] using congrArg (a ∈ ·) (h a (g (f a)) b (g (f b))
      (hf (f a)).symm (hf (f b)).symm (ha (f a)).symm (hb (f b)).symm)

/-- A function `f : α → β` decreases cardinality by at most one if and only if
there is at most a collision between a unique pair of elements. -/
/-
**Set.ncard_le_ncard_image_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.ncard_le_ncard_image_add_one_iff {α β : Type*} (s : Set α) [Finite s] 
(f : α -> β) : s.ncard <= (f '' s).ncard + 1 ↔ forall a in s, forall b in s, for
all c in s, forall d in s, f a = f b -> f c = f d -> a != b -> c != d -> {a, b} 
= ({c, d} : Set α)
参数：s : Set α；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Function.Surjective.card_le_card_add_one_iff`：Function.Surjective.card_l
e_card_add_one_iff {α β : Type*} [Finite α] {f : α -> β} (hf : Function.Surjecti
ve f) : Nat.card α <= Nat.card β +…
· 使用定理 `Set.surjective_mapsTo_image_restrict`：surjective_mapsTo_image_restrict (
f : α -> β) (s : Set α) : Surjective ((mapsTo_image f s).restrict f s (f '' s))

--- 原说明 ---
A function `f : α → β` decreases cardinality by at most one if and only if
there is at most a collision between a unique pair of elements.
-/
theorem Set.ncard_le_ncard_image_add_one_iff {α β : Type*} (s : Set α) [Finite s] (f : α → β) :
    s.ncard ≤ (f '' s).ncard + 1 ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α) := by
  simpa [Subtype.ext_iff, ← (Set.image_injective.mpr Subtype.val_injective).eq_iff,
     Set.image_insert_eq, Set.image_singleton] using
      (Set.surjective_mapsTo_image_restrict f s).card_le_card_add_one_iff
