/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SetFamily.HarrisKleitman
public import Mathlib.Combinatorics.SetFamily.Intersecting

/-!
# Kleitman's bound on the size of intersecting families

An intersecting family on `n` elements has size at most `2ⁿ⁻¹`, so we could naïvely think that two
intersecting families could cover all `2ⁿ` sets. But actually that's not case because for example
none of them can contain the empty set. Intersecting families are in some sense correlated.
Kleitman's bound stipulates that `k` intersecting families cover at most `2ⁿ - 2ⁿ⁻ᵏ` sets.

## Main declarations

* `Finset.card_biUnion_le_of_intersecting`: Kleitman's theorem.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

public section


open Finset

open Fintype (card)

variable {ι α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Kleitman's theorem**. An intersecting family on `n` elements contains at most `2ⁿ⁻¹` sets, and
each further intersecting family takes at most half of the sets that are in no previous family. -/
/-
**Finset.card_biUnion_le_of_intersecting** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_biUnion_le_of_intersecting (s : Finset ι) (f : ι -> Finset (Fi
nset α)) (hf : forall i in s, (f i : Set (Finset α)).Intersecting) : #(s.biUnion
 f) <= 2 ^ Fintype.card α - 2 ^ (Fintype.card α - #s)
参数：s : Finset ι；f : ι -> Finset (Finset α)；hf : forall i in s, (f i : Set (Finse
t α)).Intersecting。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.biUnion_subset`：biUnion_subset {s' : Finset β} : s.biUnion t subs
eteq s' ↔ forall x in s, t x subseteq s'
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `Set.Intersecting.ne_bot`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α}, s.Intersecting → a ∈ s → a ≠ ⊥
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Fintype.card_finset`：Fintype.card_finset [Fintype α] : Fintype.card (Fin
set α) = 2 ^ Fintype.card α
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Set.Intersecting.exists_card_eq`：∀ {α : Type u_1} [inst : BooleanAlgebra
 α] [Nontrivial α] [inst_2 : Fintype α] {s : Finset α},   (↑s).Intersecting → ∃ 
t, s ⊆ t ∧ 2 * t.card…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Set.Intersecting.isUpperSet'`：∀ {α : Type u_1} [inst : SemilatticeInf α]
 [inst_1 : OrderBot α] {s : Finset α},   (↑s).Intersecting → (∀ (t : Finset α), 
(↑t).Intersecting …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Intersecting.is_max_iff_card_eq`：∀ {α : Type u_1} [inst : BooleanAlg
ebra α] [Nontrivial α] [inst_2 : Fintype α] {s : Finset α},   (↑s).Intersecting 
→ ((∀ (t : Finset α), (↑t…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finset.biUnion_mono`：biUnion_mono (h : forall a in s, t₁ a subseteq t₂ a
) : s.biUnion t₁ subseteq s.biUnion t₂
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
**Kleitman's theorem**. An intersecting family on `n` elements contains at most 
`2ⁿ⁻¹` sets, and
each further intersecting family takes at most half of the sets that are in no p
revious family.
-/
theorem Finset.card_biUnion_le_of_intersecting (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    #(s.biUnion f) ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - #s) := by
  have : DecidableEq ι := by
    classical
    infer_instance
  obtain hs | hs := le_total (Fintype.card α) #s
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    refine (card_le_card <| biUnion_subset.2 fun i hi a ha ↦
      mem_compl.2 <| notMem_singleton.2 <| (hf _ hi).ne_bot ha).trans_eq ?_
    rw [card_compl, Fintype.card_finset, card_singleton]
  induction s using Finset.cons_induction generalizing f with
  | empty => simp
  | cons i s hi ih =>
  set f' : ι → Finset (Finset α) :=
    fun j ↦ if hj : j ∈ cons i s hi then (hf j hj).exists_card_eq.choose else ∅
  have hf₁ : ∀ j, j ∈ cons i s hi → f j ⊆ f' j ∧ 2 * #(f' j) =
      2 ^ Fintype.card α ∧ (f' j : Set (Finset α)).Intersecting := by
    rintro j hj
    simp_rw [f', dif_pos hj, ← Fintype.card_finset]
    exact Classical.choose_spec (hf j hj).exists_card_eq
  have hf₂ : ∀ j, j ∈ cons i s hi → IsUpperSet (f' j : Set (Finset α)) := by
    refine fun j hj ↦ (hf₁ _ hj).2.2.isUpperSet' ((hf₁ _ hj).2.2.is_max_iff_card_eq.2 ?_)
    rw [Fintype.card_finset]
    exact (hf₁ _ hj).2.1
  refine (card_le_card <| biUnion_mono fun j hj ↦ (hf₁ _ hj).1).trans ?_
  nth_rw 1 [cons_eq_insert i]
  rw [biUnion_insert]
  refine (card_mono <| @le_sup_sdiff _ _ (f' i) _).trans ((card_union_le _ _).trans ?_)
  rw [union_sdiff_left, sdiff_eq_inter_compl]
  refine le_of_mul_le_mul_left ?_ (pow_pos (zero_lt_two' ℕ) <| Fintype.card α + 1)
  rw [pow_succ, mul_add, mul_assoc, mul_comm _ 2, mul_assoc]
  refine (add_le_add
      ((mul_le_mul_iff_right₀ <| pow_pos (zero_lt_two' ℕ) _).2
      (hf₁ _ <| mem_cons_self _ _).2.2.card_le) <|
      (mul_le_mul_iff_right₀ <| zero_lt_two' ℕ).2 <| IsUpperSet.card_inter_le_finset ?_ ?_).trans ?_
  · rw [coe_biUnion]
    exact isUpperSet_iUnion₂ fun i hi ↦ hf₂ _ <| subset_cons _ hi
  · rw [coe_compl]
    exact (hf₂ _ <| mem_cons_self _ _).compl
  rw [mul_tsub, card_compl, Fintype.card_finset, mul_left_comm, mul_tsub,
    (hf₁ _ <| mem_cons_self _ _).2.1, two_mul, add_tsub_cancel_left, ← mul_tsub, ← mul_two,
    mul_assoc, ← add_mul, mul_comm]
  gcongr
  refine (add_le_add_right
    (ih _ (fun i hi ↦ (hf₁ _ <| subset_cons _ hi).2.2)
    ((card_le_card <| subset_cons _).trans hs)) _).trans ?_
  rw [mul_tsub, two_mul, ← pow_succ',
    ← add_tsub_assoc_of_le (pow_right_mono₀ (one_le_two : (1 : ℕ) ≤ 2) tsub_le_self),
    tsub_add_eq_add_tsub hs, card_cons, add_tsub_add_eq_tsub_right]
