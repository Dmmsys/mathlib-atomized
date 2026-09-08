/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Order.Partition.Equipartition

/-!
# Equitabilising a partition

This file allows to blow partitions up into parts of controlled size. Given a partition `P` and
`a b m : ℕ`, we want to find a partition `Q` with `a` parts of size `m` and `b` parts of size
`m + 1` such that all parts of `P` are "as close as possible" to unions of parts of `Q`. By
"as close as possible", we mean that each part of `P` can be written as the union of some parts of
`Q` along with at most `m` other elements.

## Main declarations

* `Finpartition.equitabilise`: `P.equitabilise h` where `h : a * m + b * (m + 1)` is a partition
  with `a` parts of size `m` and `b` parts of size `m + 1` which almost refines `P`.
* `Finpartition.exists_equipartition_card_eq`: We can find equipartitions of arbitrary size.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset Nat

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} {m n a b : ℕ} {P : Finpartition s}

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`, we can
find a new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the
union of parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and
(provided `m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size
`m` and hence `a + b` parts in total. -/
/-
**Finpartition.equitabilise_aux** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：equitabilise_aux (hs : a * m + b * (m + 1) = #s) : exists Q : Finpartition
 s, (forall x : Finset α, x in Q.parts -> #x = m ∨ #x = m + 1) ∧ (forall x, x in
 P.parts -> #(x \ {y in Q.parts | y subseteq x}.biUnion id) <= m) ∧ #{i in Q.par
ts | #i = m + 1} = b
参数：hs : a * m + b * (m + 1) = #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.empty_parts`：∀ (α : Type u_1) [inst : Lattice α] [inst_1 : 
OrderBot α], (Finpartition.empty α).parts = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
（共 103 条，此处仅展示前 30 条）

--- 原说明 ---
Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`
, we can
find a new partition `Q` of `s` where each part has size `m` or `m + 1`, every p
art of `P` is the
union of parts of `Q` plus at most `m` extra elements, there are `b` parts of si
ze `m + 1` and
(provided `m > 0`, because a partition does not have parts of size `0`) there ar
e `a` parts of size
`m` and hence `a + b` parts in total.
-/
theorem equitabilise_aux (hs : a * m + b * (m + 1) = #s) :
    ∃ Q : Finpartition s,
      (∀ x : Finset α, x ∈ Q.parts → #x = m ∨ #x = m + 1) ∧
        (∀ x, x ∈ P.parts → #(x \ {y ∈ Q.parts | y ⊆ x}.biUnion id) ≤ m) ∧
          #{i ∈ Q.parts | #i = m + 1} = b := by
  -- Get rid of the easy case `m = 0`
  obtain rfl | m_pos := m.eq_zero_or_pos
  · refine ⟨⊥, by simp, ?_, by simpa [Finset.filter_true_of_mem] using hs.symm⟩
    simp only [le_zero_iff, card_eq_zero, mem_biUnion, mem_filter, id,
      and_assoc, sdiff_eq_empty_iff_subset, subset_iff]
    exact fun x hx a ha =>
      ⟨{a}, mem_map_of_mem _ (P.le hx ha), singleton_subset_iff.2 ha, mem_singleton_self _⟩
  -- Prove the case `m > 0` by strong induction on `s`
  induction s using Finset.strongInduction generalizing a b with | H s ih => _
  -- If `a = b = 0`, then `s = ∅` and we can partition into zero parts
  by_cases hab : a = 0 ∧ b = 0
  · -- Rewrite using `← bot_eq_empty` because we have theorems about `Finpartition ⊥`,
    -- and nothing about `Finpartition ∅`, even though they are defeq in this case.
    -- TODO: specialize the `Finpartition ⊥` lemmas to `Finpartition ∅`?
    simp only [hab.1, hab.2, add_zero, zero_mul, eq_comm, card_eq_zero, ← bot_eq_empty] at hs
    subst hs
    exact ⟨Finpartition.empty _, by simp, by simp [Unique.eq_default P, -bot_eq_empty],
      by simp [hab.2]⟩
  simp_rw [not_and_or, ← Ne.eq_def, ← pos_iff_ne_zero] at hab
  -- `n` will be the size of the smallest part
  set n := if 0 < a then m else m + 1 with hn
  -- Some easy facts about it
  obtain ⟨hn₀, hn₁, hn₂, hn₃⟩ : 0 < n ∧ n ≤ m + 1 ∧ n ≤ a * m + b * (m + 1) ∧
      ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #s - n := by
    rw [hn, ← hs]
    split_ifs with h <;> rw [tsub_mul, one_mul]
    · refine ⟨m_pos, le_succ _, le_add_right (Nat.le_mul_of_pos_left _ ‹0 < a›), ?_⟩
      rw [tsub_add_eq_add_tsub (Nat.le_mul_of_pos_left _ h)]
    · refine ⟨succ_pos', le_rfl,
        le_add_left (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›), ?_⟩
      rw [← add_tsub_assoc_of_le (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›)]
  /- We will call the inductive hypothesis on a partition of `s \ t` for a carefully chosen `t ⊆ s`.
    To decide which, however, we must distinguish the case where all parts of `P` have size `m` (in
    which case we take `t` to be an arbitrary subset of `s` of size `n`) from the case where at
    least one part `u` of `P` has size `m + 1` (in which case we take `t` to be an arbitrary subset
    of `u` of size `n`). The rest of each branch is just tedious calculations to satisfy the
    induction hypothesis. -/
  by_cases! h : ∀ u ∈ P.parts, #u < m + 1
  · obtain ⟨t, hts, htn⟩ := exists_subset_card_eq (hn₂.trans_eq hs)
    have ht : t.Nonempty := by rwa [← card_pos, htn]
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
      rw [card_sdiff_of_subset ‹t ⊆ s›, htn, hn₃]
    obtain ⟨R, hR₁, _, hR₃⟩ :=
      @ih (s \ t) (sdiff_ssubset hts ‹t.Nonempty›) (if 0 < a then a - 1 else a)
        (if 0 < a then b else b - 1) (P.avoid t) hcard
    refine ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel hts), ?_, ?_, ?_⟩
    · simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hR₁, htn, hn]
      exact ite_eq_or_eq _ _ _
    · exact fun x hx => (card_le_card sdiff_subset).trans (Nat.lt_succ_iff.1 <| h _ hx)
    simp_rw [extend_parts, filter_insert, htn, n, m.succ_ne_self.symm.ite_eq_right_iff]
    split_ifs with ha
    · rw [hR₃, if_pos ha]
    rw [card_insert_of_notMem, hR₃, if_neg ha, tsub_add_cancel_of_le]
    · exact hab.resolve_left ha
    · intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)
  obtain ⟨u, hu₁, hu₂⟩ := h
  obtain ⟨t, htu, htn⟩ := exists_subset_card_eq (hn₁.trans hu₂)
  have ht : t.Nonempty := by rwa [← card_pos, htn]
  have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
    rw [card_sdiff_of_subset (htu.trans <| P.le hu₁), htn, hn₃]
  obtain ⟨R, hR₁, hR₂, hR₃⟩ :=
    @ih (s \ t) (sdiff_ssubset (htu.trans <| P.le hu₁) ht) (if 0 < a then a - 1 else a)
      (if 0 < a then b else b - 1) (P.avoid t) hcard
  refine
    ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel <| htu.trans <| P.le hu₁), ?_, ?_, ?_⟩
  · simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hR₁, htn, hn]
    exact ite_eq_or_eq _ _ _
  · conv in _ ∈ _ => rw [← insert_erase hu₁]
    simp only [mem_insert, forall_eq_or_imp, extend_parts]
    refine ⟨?_, fun x hx => (card_le_card ?_).trans <| hR₂ x ?_⟩
    · simp only [filter_insert, if_pos htu, biUnion_insert, id]
      obtain rfl | hut := eq_or_ne u t
      · rw [sdiff_eq_empty_iff_subset.2 subset_union_left]
        exact bot_le
      refine
        (card_le_card fun i => ?_).trans
          (hR₂ (u \ t) <| P.mem_avoid.2 ⟨u, hu₁, fun i => hut <| i.antisymm htu, rfl⟩)
      simpa using fun hi₁ hi₂ hi₃ =>
        ⟨⟨hi₁, hi₂⟩, fun x hx hx' => hi₃ _ hx <| hx'.trans sdiff_subset⟩
    · apply sdiff_subset_sdiff Subset.rfl (biUnion_subset_biUnion_of_subset_left _ _)
      exact filter_subset_filter _ (subset_insert _ _)
    simp only [avoid, ofErase, mem_erase, mem_image, bot_eq_empty]
    exact
      ⟨(nonempty_of_mem_parts _ <| mem_of_mem_erase hx).ne_empty, _, mem_of_mem_erase hx,
        (disjoint_of_subset_right htu <|
            P.disjoint (mem_of_mem_erase hx) hu₁ <| ne_of_mem_erase hx).sdiff_eq_left⟩
  simp only [extend_parts, filter_insert, htn, hn, m.succ_ne_self.symm.ite_eq_right_iff]
  split_ifs with h
  · rw [hR₃, if_pos h]
  · rw [card_insert_of_notMem, hR₃, if_neg h, Nat.sub_add_cancel (hab.resolve_left h)]
    intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)

variable (h : a * m + b * (m + 1) = #s)

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`, build a
new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the union of
parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and (provided
`m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size `m` and
hence `a + b` parts in total. -/
/-
**Finpartition.equitabilise** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：equitabilise : Finpartition s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.equitabilise_aux`：equitabilise_aux (hs : a * m + b * (m + 1
) = #s) : exists Q : Finpartition s, (forall x : Finset α, x in Q.parts -> #x = 
m ∨ #x = m + 1) ∧ (…

--- 原说明 ---
Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`
, build a
new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of 
`P` is the union of
parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1
` and (provided
`m > 0`, because a partition does not have parts of size `0`) there are `a` part
s of size `m` and
hence `a + b` parts in total.
-/
noncomputable def equitabilise : Finpartition s :=
  (P.equitabilise_aux h).choose

variable {h}
/-
**Finpartition.card_eq_of_mem_parts_equitabilise** 是 Mathlib 中的一个定理，位于命名空间 `Finp
artition`。
形式化陈述：card_eq_of_mem_parts_equitabilise : t in (P.equitabilise h).parts -> #t = 
m ∨ #t = m + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finpartition.equitabilise_aux`：equitabilise_aux (hs : a * m + b * (m + 1
) = #s) : exists Q : Finpartition s, (forall x : Finset α, x in Q.parts -> #x = 
m ∨ #x = m + 1) ∧ (…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem card_eq_of_mem_parts_equitabilise :
    t ∈ (P.equitabilise h).parts → #t = m ∨ #t = m + 1 :=
  (P.equitabilise_aux h).choose_spec.1 _
/-
**Finpartition.equitabilise_isEquipartition** 是 Mathlib 中的一个定理，位于命名空间 `Finpartit
ion`。
形式化陈述：equitabilise_isEquipartition : (P.equitabilise h).IsEquipartition
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.equitableOn_iff_exists_eq_eq_add_one`：equitableOn_iff_exists_eq_eq_a
dd_one {s : Set α} {f : α -> Nat} : s.EquitableOn f ↔ exists b, forall a in s, f
 a = b ∨ f a = b + 1
· 使用定理 `Finpartition.card_eq_of_mem_parts_equitabilise`：card_eq_of_mem_parts_equ
itabilise : t in (P.equitabilise h).parts -> #t = m ∨ #t = m + 1
-/
theorem equitabilise_isEquipartition : (P.equitabilise h).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨m, fun _ => card_eq_of_mem_parts_equitabilise⟩

variable (P h)
/-
**Finpartition.card_filter_equitabilise_big** 是 Mathlib 中的一个定理，位于命名空间 `Finpartit
ion`。
形式化陈述：card_filter_equitabilise_big : #{u in (P.equitabilise h).parts | #u = m + 
1} = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finpartition.equitabilise_aux`：equitabilise_aux (hs : a * m + b * (m + 1
) = #s) : exists Q : Finpartition s, (forall x : Finset α, x in Q.parts -> #x = 
m ∨ #x = m + 1) ∧ (…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem card_filter_equitabilise_big : #{u ∈ (P.equitabilise h).parts | #u = m + 1} = b :=
  (P.equitabilise_aux h).choose_spec.2.2
/-
**Finpartition.card_filter_equitabilise_small** 是 Mathlib 中的一个定理，位于命名空间 `Finpart
ition`。
形式化陈述：card_filter_equitabilise_small (hm : m != 0) : #{u in (P.equitabilise h).p
arts | #u = m} = a
参数：hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_mul_right_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRigh
tCancelMulZero M₀] {a b c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sum_card_parts`：sum_card_parts : ∑ i in P.parts, #i = #s
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Finpartition.card_eq_of_mem_parts_equitabilise`：card_eq_of_mem_parts_equ
itabilise : t in (P.equitabilise h).parts -> #t = m ∨ #t = m + 1
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Finset.disjoint_filter_filter'`：disjoint_filter_filter' (s t : Finset α)
 {p q : α -> Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) : Disj
oint (s.filter p) (t…
· 使用定理 `Nat.succ_ne_self`：∀ (n : ℕ), n.succ ≠ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const_nat`：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : foral
l x in s, f x = m) : ∑ x in s, f x = #s * m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finpartition.card_filter_equitabilise_big`：card_filter_equitabilise_big 
: #{u in (P.equitabilise h).parts | #u = m + 1} = b
-/
theorem card_filter_equitabilise_small (hm : m ≠ 0) :
    #{u ∈ (P.equitabilise h).parts | #u = m} = a := by
  refine (mul_eq_mul_right_iff.1 <| (add_left_inj (b * (m + 1))).1 ?_).resolve_right hm
  rw [h, ← (P.equitabilise h).sum_card_parts]
  have hunion :
    (P.equitabilise h).parts =
      {u ∈ (P.equitabilise h).parts | #u = m} ∪ {u ∈ (P.equitabilise h).parts | #u = m + 1} := by
    rw [← filter_or, filter_true_of_mem]
    exact fun x => card_eq_of_mem_parts_equitabilise
  nth_rw 2 [hunion]
  rw [sum_union, sum_const_nat fun x hx => (mem_filter.1 hx).2,
    sum_const_nat fun x hx => (mem_filter.1 hx).2, P.card_filter_equitabilise_big]
  refine disjoint_filter_filter' _ _ ?_
  intro x ha hb i h
  apply succ_ne_self m _
  exact (hb i h).symm.trans (ha i h)
/-
**Finpartition.card_parts_equitabilise** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_parts_equitabilise (hm : m != 0) : #(P.equitabilise h).parts = a + b
参数：hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Finpartition.card_eq_of_mem_parts_equitabilise`：card_eq_of_mem_parts_equ
itabilise : t in (P.equitabilise h).parts -> #t = m ∨ #t = m + 1
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finpartition.card_filter_equitabilise_small`：card_filter_equitabilise_sm
all (hm : m != 0) : #{u in (P.equitabilise h).parts | #u = m} = a
· 使用定理 `Finpartition.card_filter_equitabilise_big`：card_filter_equitabilise_big 
: #{u in (P.equitabilise h).parts | #u = m + 1} = b
-/
theorem card_parts_equitabilise (hm : m ≠ 0) : #(P.equitabilise h).parts = a + b := by
  rw [← filter_true_of_mem fun x => card_eq_of_mem_parts_equitabilise, filter_or,
    card_union_of_disjoint, P.card_filter_equitabilise_small _ hm, P.card_filter_equitabilise_big]
  aesop (add norm disjoint_filter)
/-
**Finpartition.card_parts_equitabilise_subset_le** 是 Mathlib 中的一个定理，位于命名空间 `Finp
artition`。
形式化陈述：card_parts_equitabilise_subset_le : t in P.parts -> #(t \ {u in (P.equitab
ilise h).parts | u subseteq t}.biUnion id) <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finpartition.equitabilise_aux`：equitabilise_aux (hs : a * m + b * (m + 1
) = #s) : exists Q : Finpartition s, (forall x : Finset α, x in Q.parts -> #x = 
m ∨ #x = m + 1) ∧ (…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem card_parts_equitabilise_subset_le :
    t ∈ P.parts → #(t \ {u ∈ (P.equitabilise h).parts | u ⊆ t}.biUnion id) ≤ m :=
  (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

variable (s)

/-- We can find equipartitions of arbitrary size. -/
/-
**Finpartition.exists_equipartition_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finpartit
ion`。
形式化陈述：exists_equipartition_card_eq (hn : n != 0) (hs : n <= #s) : exists P : Fin
partition s, P.IsEquipartition ∧ #P.parts = n
参数：hn : n != 0；hs : n <= #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_mul`：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - 
b * c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finpartition.equitabilise_isEquipartition`：equitabilise_isEquipartition 
: (P.equitabilise h).IsEquipartition
· 使用定理 `Finpartition.card_parts_equitabilise`：card_parts_equitabilise (hm : m !=
 0) : #(P.equitabilise h).parts = a + b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b

--- 原说明 ---
We can find equipartitions of arbitrary size.
-/
theorem exists_equipartition_card_eq (hn : n ≠ 0) (hs : n ≤ #s) :
    ∃ P : Finpartition s, P.IsEquipartition ∧ #P.parts = n := by
  rw [← pos_iff_ne_zero] at hn
  have : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [tsub_mul, mul_add, ← add_assoc,
      tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (mod_lt _ hn).le), mul_one, add_comm,
      mod_add_div]
  refine
    ⟨(indiscrete (card_pos.1 <| hn.trans_le hs).ne_empty).equitabilise this,
      equitabilise_isEquipartition, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hs hn).ne', tsub_add_cancel_of_le (mod_lt _ hn).le]

end Finpartition

