/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Centralizer of an element in the alternating group

Given a finite type `α`, our goal is to compute the cardinality of conjugacy classes
in `alternatingGroup α`.

* `AlternatingGroup.card_of_cycleType_mul_eq m` and `AlternatingGroup.card_of_cycleType m`
  compute the number of even permutations of given cycle type.

* `Equiv.Perm.OnCycleFactors.odd_of_centralizer_le_alternatingGroup` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then all members of the `g.cycleType` are odd.

* `Equiv.Perm.card_le_of_centralizer_le_alternating` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then the cardinality of α
  is at most `g.cycleType.sum` plus one.

* `Equiv.Perm.count_le_one_of_centralizer_le_alternating` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then `g.cycleType` has no repetitions.

* `Equiv.Perm.centralizer_le_alternating_iff` :
  the previous three conditions are necessary and sufficient
  for having `Subgroup.centralizer {g} ≤ alternatingGroup α`.

TODO :
Deduce the formula for the cardinality of the centralizers
and conjugacy classes in `alternatingGroup α`.
-/

public section

open Equiv Finset Function MulAction

variable {α : Type*} [Fintype α] [DecidableEq α] {g : Perm α}

namespace Equiv.Perm.OnCycleFactors

/-
**Equiv.Perm.OnCycleFactors.odd_of_centralizer_le_alternatingGroup** 是 Mathlib 中
的一个定理，位于命名空间 `Equiv.Perm.OnCycleFactors`。
形式化陈述：odd_of_centralizer_le_alternatingGroup (h : Subgroup.centralizer {g} <= al
ternatingGroup α) (i : Nat) (hi : i in g.cycleType) : Odd i
参数：h : Subgroup.centralizer {g} <= alternatingGroup α；i : Nat；hi : i in g.cycleT
ype。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用引理 `Subgroup.mem_centralizer_singleton_iff`：mem_centralizer_singleton_iff {g
 k : G} : k in Subgroup.centralizer {g} ↔ k * g = g * k
· 使用定理 `Equiv.Perm.self_mem_cycle_factors_commute`：self_mem_cycle_factors_commut
e {g c : Perm α} (hc : c in g.cycleFactorsFinset) : Commute c g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `Int.units_ne_iff_eq_neg`：units_ne_iff_eq_neg {u v : Intˣ} : u != v ↔ u =
 -v
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Equiv.Perm.IsCycle.sign`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Fintype α] {f : Equiv.Perm α},   f.IsCycle → Equiv.Perm.sign f = -(-1) ^ f.su
pport.card
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
-/
theorem odd_of_centralizer_le_alternatingGroup (h : Subgroup.centralizer {g} ≤ alternatingGroup α)
    (i : ℕ) (hi : i ∈ g.cycleType) :
    Odd i := by
  rw [cycleType_def g, Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices sign c = 1 by
    rw [IsCycle.sign _, neg_eq_iff_eq_neg, ← Int.units_ne_iff_eq_neg] at this
    · rw [← Nat.not_even_iff_odd, comp_apply]
      exact fun h ↦ this h.neg_one_pow
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  apply h
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Equiv.Perm.self_mem_cycle_factors_commute hc

end Equiv.Perm.OnCycleFactors

namespace AlternatingGroup

open Nat Equiv.Perm.OnCycleFactors Equiv.Perm

/-
**AlternatingGroup.map_subtype_of_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Alternati
ngGroup`。
形式化陈述：map_subtype_of_cycleType (m : Multiset Nat) : ({g | (g : Perm α).cycleType
 = m} : Finset (alternatingGroup α)).map (Embedding.subtype _) = if Even (m.sum 
+ m.card) then ({g | g.cycleType = m} : Finset (Perm α)) else ∅
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Equiv.Perm.sign_of_cycleType`：sign_of_cycleType (f : Perm α) : sign f = 
(-1 : Intˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType)
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Finse
t α} : s = ∅ ↔ forall x, x ∉ s
· 使用引理 `neg_one_pow_eq_one_iff_even`：neg_one_pow_eq_one_iff_even (h : (-1 : R) !
= 1) : (-1 : R) ^ n = 1 ↔ Even n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem map_subtype_of_cycleType (m : Multiset ℕ) :
    ({g | (g : Perm α).cycleType = m} : Finset (alternatingGroup α)).map (Embedding.subtype _) =
      if Even (m.sum + m.card) then ({g | g.cycleType = m} : Finset (Perm α)) else ∅ := by
  split_ifs with hm
  · ext g
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right,
      and_iff_left_iff_imp]
    intro hg
    rw [sign_of_cycleType, hg, Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right] at hg
    rcases hg with ⟨hg, hs⟩
    rw [g.sign_of_cycleType, hg, neg_one_pow_eq_one_iff_even (by simp)] at hs
    contradiction

variable (α) in
/-- The cardinality of even permutations of given `cycleType` -/
/-
**AlternatingGroup.card_of_cycleType_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Alternati
ngGroup`。
形式化陈述：card_of_cycleType_mul_eq (m : Multiset Nat) : #{g : alternatingGroup α | g
.val.cycleType = m} * ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, 
(m.count n)!)) = if ((m.sum <= Fintype.card α ∧ forall a in m, 2 <= a) ∧ Even (m
.sum + Multiset.card m)) then (Fintype.card α)! else 0
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `AlternatingGroup.map_subtype_of_cycleType`：map_subtype_of_cycleType (m :
 Multiset Nat) : ({g | (g : Perm α).cycleType = m} : Finset (alternatingGroup α)
).map (Embedding.subtype _) = i…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `Equiv.Perm.card_of_cycleType_mul_eq`：card_of_cycleType_mul_eq (m : Multi
set Nat) : #({g | g.cycleType = m} : Finset (Perm α)) * ((Fintype.card α - m.sum
)! * m.prod * (∏ n in m.t…

--- 原说明 ---
The cardinality of even permutations of given `cycleType`
-/
theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    #{g : alternatingGroup α |  g.val.cycleType = m} *
        ((Fintype.card α - m.sum)! * m.prod * (∏ n ∈ m.toFinset, (m.count n)!)) =
          if ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m))
          then (Fintype.card α)!
          else 0 := by
  rw [← Finset.card_map, map_subtype_of_cycleType, apply_ite Finset.card,
    Finset.card_empty, ite_mul, zero_mul]
  simp only [and_comm (b := Even _)]
  rw [ite_and, Equiv.Perm.card_of_cycleType_mul_eq]

variable (α) in
/-- The cardinality of even permutations of given `cycleType` -/
/-
**AlternatingGroup.card_of_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingGroup
`。
形式化陈述：card_of_cycleType (m : Multiset Nat) : #{g : alternatingGroup α | (g : Equ
iv.Perm α).cycleType = m} = if (m.sum <= Fintype.card α ∧ forall a in m, 2 <= a)
 ∧ Even (m.sum + Multiset.card m) then (Fintype.card α)! / ((Fintype.card α - m.
sum)! * (m.prod * (∏ n in m.toFinset, (m.count n)!))) else 0
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `AlternatingGroup.map_subtype_of_cycleType`：map_subtype_of_cycleType (m :
 Multiset Nat) : ({g | (g : Perm α).cycleType = m} : Finset (alternatingGroup α)
).map (Embedding.subtype _) = i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.Perm.card_of_cycleType`：card_of_cycleType (m : Multiset Nat) : #({
g | g.cycleType = m} : Finset (Perm α)) = if m.sum <= Fintype.card α ∧ forall a 
in m, 2 <= a then …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b

--- 原说明 ---
The cardinality of even permutations of given `cycleType`
-/
theorem card_of_cycleType (m : Multiset ℕ) :
    #{g : alternatingGroup α | (g : Equiv.Perm α).cycleType = m} =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! *
            (m.prod * (∏ n ∈ m.toFinset, (m.count n)!)))
      else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map, map_subtype_of_cycleType, if_pos hm.2,
      Equiv.Perm.card_of_cycleType α m, if_pos hm.1, mul_assoc]
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map, map_subtype_of_cycleType]
    rw [apply_ite Finset.card, Finset.card_empty]
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg]
      obtain hm | hm := not_and_or.mp hm
      · exact hm
      · contradiction
    · rfl

open Fintype in
/-- The number of cycles of given length -/
/-
**AlternatingGroup.card_of_cycleType_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Altern
atingGroup`。
形式化陈述：card_of_cycleType_singleton {n : Nat} (hn : 2 <= n) (hα : n <= card α) : #
{g : alternatingGroup α | g.val.cycleType = {n}} = if Odd n then (n - 1)! * (cho
ose (card α) n) else 0
参数：hn : 2 <= n；hα : n <= card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `AlternatingGroup.map_subtype_of_cycleType`：map_subtype_of_cycleType (m :
 Multiset Nat) : ({g | (g : Perm α).cycleType = m} : Finset (alternatingGroup α)
).map (Embedding.subtype _) = i…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Equiv.Perm.card_of_cycleType_singleton`：card_of_cycleType_singleton {n :
 Nat} (hn' : 2 <= n) (hα : n <= card α) : #({g | g.cycleType = {n}} : Finset (Pe
rm α)) = (n - 1)! * (choose …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The number of cycles of given length
-/
lemma card_of_cycleType_singleton {n : ℕ} (hn : 2 ≤ n) (hα : n ≤ card α) :
    #{g : alternatingGroup α | g.val.cycleType = {n}} =
      if Odd n then (n - 1)! * (choose (card α) n) else 0 := by
  rw [← card_map, map_subtype_of_cycleType, apply_ite Finset.card]
  simp only [Multiset.sum_singleton, Multiset.card_singleton, Finset.card_empty]
  simp_rw [← Nat.not_odd_iff_even, Nat.odd_add_one, not_not,
    Perm.card_of_cycleType_singleton hn hα]

end AlternatingGroup

namespace Equiv.Perm

open Basis OnCycleFactors

/-
**Equiv.Perm.card_le_of_centralizer_le_alternating** 是 Mathlib 中的一个定理，位于命名空间 `Eq
uiv.Perm`。
形式化陈述：card_le_of_centralizer_le_alternating (h : Subgroup.centralizer {g} <= alt
ernatingGroup α) : Fintype.card α <= g.cycleType.sum + 1
参数：h : Subgroup.centralizer {g} <= alternatingGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.card_fixedPoints`：card_fixedPoints (σ : Equiv.Perm α) : Finty
pe.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `Nat.le_sub_iff_add_le`：∀ {k m n : ℕ}, k ≤ m → (n ≤ m - k ↔ n + k ≤ m)
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Fintype.exists_pair_of_one_lt_card`：exists_pair_of_one_lt_card (h : 1 < 
card α) : exists a b : α, a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply`：sign_kerParam_apply
_apply : sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign (v c).val
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_le_centralizer`：kerParam_range_
le_centralizer : (kerParam g).range <= Subgroup.centralizer {g}
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem card_le_of_centralizer_le_alternating (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    Fintype.card α ≤ g.cycleType.sum + 1 := by
  by_contra! hm
  replace hm : 2 + g.cycleType.sum ≤ Fintype.card α := by lia
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (kerParam g ⟨swap a b, 1⟩) ≠ 1 from
      this (h (kerParam_range_le_centralizer (Set.mem_range_self _)))
    simp [sign_kerParam_apply_apply, hab]
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _
/-
**Equiv.Perm.count_le_one_of_centralizer_le_alternating** 是 Mathlib 中的一个定理，位于命名空
间 `Equiv.Perm`。
形式化陈述：count_le_one_of_centralizer_le_alternating (h : Subgroup.centralizer {g} <
= alternatingGroup α) : forall i, g.cycleType.count i <= 1
参数：h : Subgroup.centralizer {g} <= alternatingGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用定理 `Multiset.nodup_map_iff_inj_on`：nodup_map_iff_inj_on {f : α -> β} {s : Mu
ltiset α} (d : Nodup s) : Nodup (map f s) ↔ forall x in s, forall y in s, f x = 
f y -> x = y
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.Basis.nonempty`：nonempty (g : Perm α) : Nonempty (Basis g)
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Multiset.eq_replicate_card`：eq_replicate_card {a : α} {s : Multiset α} :
 s = replicate (card s) a ↔ forall b in s, b = a
· 使用定理 `Equiv.Perm.pow_prime_eq_one_iff`：pow_prime_eq_one_iff {σ : Perm α} {p : 
Nat} [hp : Fact (Nat.Prime p)] : σ ^ p = 1 ↔ forall c in σ.cycleType, c = p
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用定理 `Subgroup.coe_one`：coe_one : ((1 : H) : G) = 1
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Equiv.swap_mul_self`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), 
Equiv.swap i j * Equiv.swap i j = 1
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `Equiv.Perm.sign_of_cycleType`：sign_of_cycleType (f : Perm α) : sign f = 
(-1 : Intˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
（共 57 条，此处仅展示前 30 条）
-/
theorem count_le_one_of_centralizer_le_alternating
    (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    ∀ i, g.cycleType.count i ≤ 1 := by
  rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra! ⟨c, hc, d, hd, hm, hm'⟩
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := Equiv.Perm.Basis.nonempty g
  have hτ : τ ∈ range_toPermHom' g := fun x ↦ by
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set k := toCentralizer a ⟨τ, hτ⟩ with hk
  suffices hsign_k : k.val.sign = -1 by
    apply units_ne_neg_self (1 : ℤˣ)
    rw [← hsign_k, h (toCentralizer a ⟨τ, hτ⟩).prop]
  /- to prove that `hsign_k : sign k = -1` below,
  we could prove that it is the product of the transpositions with disjoint supports
  [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
  which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
  but it will be sufficient to observe that `k ^ 2 = 1`
  (which implies that `k.cycleType` is of the form (2,2,…))
  and to control its support. -/
  have hk_cT : k.val.cycleType = Multiset.replicate k.val.cycleType.card 2 := by
    rw [Multiset.eq_replicate_card, ← pow_prime_eq_one_iff, ← Subgroup.coe_pow,
      ← Subgroup.coe_one, Subtype.coe_inj, hk, ← map_pow]
    convert! MonoidHom.map_one _
    rw [← Subtype.coe_inj]
    apply Equiv.swap_mul_self
  rw [sign_of_cycleType, hk_cT]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, pow_add,
    even_two, Even.mul_left, Even.neg_pow, one_pow, one_mul]
  apply Odd.neg_one_pow
  apply odd_of_centralizer_le_alternatingGroup h
  have : (k : Perm α).cycleType.card * 2 = (k : Perm α).support.card := by
    rw [← sum_cycleType, hk_cT]
    simp
  have that : Multiset.card (k : Perm α).cycleType = (c : Perm α).support.card := by
    rw [← Nat.mul_left_inj (a := 2) (by simp), this]
    simp only [hk, toCentralizer, MonoidHom.coe_mk, OneHom.coe_mk, card_ofPermHom_support]
    have H : (⟨c, hc⟩ : g.cycleFactorsFinset) ≠ ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
    simp only [τ, support_swap H]
    rw [Finset.sum_insert (by simp only [mem_singleton, H, not_false_eq_true]),
      Finset.sum_singleton, hm, mul_two]
  rw [that]
  simp only [cycleType_def, Multiset.mem_map]
  exact ⟨c, hc, by simp only [Function.comp_apply]⟩
/-
**Equiv.Perm.OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one** 是 Ma
thlib 中的一个定理，位于命名空间 `Equiv.Perm.OnCycleFactors`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Pe
rm α},   (∀ (i : ℕ), Multiset.count i g.cycleType ≤ 1) →     (Equiv.Perm.OnCycle
Factors.kerParam g).range = Subgroup.centralizer {g}
参数：∀ (i : ℕ), Multiset.count i g.cycleType ≤ 1；Equiv.Perm.OnCycleFactors.kerPara
m g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_le_centralizer`：kerParam_range_
le_centralizer : (kerParam g).range <= Subgroup.centralizer {g}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_eq`：kerParam_range_eq : (kerPar
am g).range = (toPermHom g).ker.map (Subgroup.subtype _)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Multiset.nodup_map_iff_inj_on`：nodup_map_iff_inj_on {f : α -> β} {s : Mu
ltiset α} (d : Nodup s) : Nodup (map f s) ↔ forall x in s, forall y in s, f x = 
f y -> x = y
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff`：mem_range_toPermHom_i
ff {τ} : τ in (toPermHom g).range ↔ forall c, #(τ c).val.support = #c.val.suppor
t
-/
theorem OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one
    (h_count : ∀ i, g.cycleType.count i ≤ 1) :
    (kerParam g).range = Subgroup.centralizer {g} := by
  ext x
  refine ⟨fun hx ↦ kerParam_range_le_centralizer hx, fun hx ↦ ?_⟩
  simp_rw [kerParam_range_eq, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  use hx
  ext c : 2
  rw [← Multiset.nodup_iff_count_le_one, cycleType_def,
    Multiset.nodup_map_iff_inj_on (cycleFactorsFinset g).nodup] at h_count
  exact h_count _ (by simp) _ c.prop (mem_range_toPermHom_iff.mp (by simp) c)

/-- The centralizer of a permutation is contained in the alternating group if and only if
its cycles have odd length, with at most one of each, and there is at most one fixed point. -/
/-
**Equiv.Perm.centralizer_le_alternating_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：centralizer_le_alternating_iff : Subgroup.centralizer {g} <= alternatingGr
oup α ↔ (forall c in g.cycleType, Odd c) ∧ Fintype.card α <= g.cycleType.sum + 1
 ∧ forall i, g.cycleType.count i <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Equiv.Perm.OnCycleFactors.odd_of_centralizer_le_alternatingGroup`：odd_of
_centralizer_le_alternatingGroup (h : Subgroup.centralizer {g} <= alternatingGro
up α) (i : Nat) (hi : i in g.cycleType) : Odd i
· 使用定理 `Equiv.Perm.card_le_of_centralizer_le_alternating`：card_le_of_centralizer
_le_alternating (h : Subgroup.centralizer {g} <= alternatingGroup α) : Fintype.c
ard α <= g.cycleType.sum + 1
· 使用定理 `Equiv.Perm.count_le_one_of_centralizer_le_alternating`：count_le_one_of_c
entralizer_le_alternating (h : Subgroup.centralizer {g} <= alternatingGroup α) :
 forall i, g.cycleType.count i <= 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.mem_range`：mem_range {f : G ->* N} {y : N} : y in f.range ↔ ex
ists x, f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one`
：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Perm α}
,   (∀ (i : ℕ), Multiset.count i g.cycleType ≤ 1) →     (Equi…
· 使用定理 `Equiv.Perm.mem_alternatingGroup`：mem_alternatingGroup {f : Perm α} : f i
n alternatingGroup α ↔ sign f = 1
· 使用定理 `Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply`：sign_kerParam_apply
_apply : sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign (v c).val
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `Equiv.Perm.IsCycle.sign`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Fintype α] {f : Equiv.Perm α},   f.IsCycle → Equiv.Perm.sign f = -(-1) ^ f.su
pport.card
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `Equiv.Perm.card_fixedPoints`：card_fixedPoints (σ : Equiv.Perm α) : Finty
pe.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum
· 使用定理 `Equiv.Perm.card_support_le_one`：card_support_le_one {f : Perm α} : #f.su
pport <= 1 ↔ f = 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The centralizer of a permutation is contained in the alternating group if and on
ly if
its cycles have odd length, with at most one of each, and there is at most one f
ixed point.
-/
theorem centralizer_le_alternating_iff :
    Subgroup.centralizer {g} ≤ alternatingGroup α ↔
      (∀ c ∈ g.cycleType, Odd c) ∧ Fintype.card α ≤ g.cycleType.sum + 1 ∧
        ∀ i, g.cycleType.count i ≤ 1 := by
  rw [SetLike.le_def]
  constructor
  · intro h
    exact ⟨odd_of_centralizer_le_alternatingGroup h,
      card_le_of_centralizer_le_alternating h,
      count_le_one_of_centralizer_le_alternating h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    rw [← kerParam_range_eq_centralizer_of_count_le_one h_count] at hx
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [mem_alternatingGroup, sign_kerParam_apply_apply (g := g) y uv]
    convert! mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk, map_zpow]
      convert! one_zpow k
      rw [IsCycle.sign, Odd.neg_one_pow, neg_neg]
      · apply h_odd
        rw [cycleType_def, Multiset.mem_map]
        exact ⟨c, hc, rfl⟩
      · rw [mem_cycleFactorsFinset_iff] at hc
        exact hc.left
    · suffices y = 1 by simp [this]
      have := card_fixedPoints g
      exact card_support_le_one.mp <| le_trans (Finset.card_le_univ _) (by lia)

namespace IsThreeCycle

variable (h5 : 5 ≤ Nat.card α) {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α))

include h5 hg

/-
**Equiv.Perm.IsThreeCycle.mem_commutatorSet_alternatingGroup** 是 Mathlib 中的一个定理，
位于命名空间 `Equiv.Perm.IsThreeCycle`。
形式化陈述：mem_commutatorSet_alternatingGroup : g in commutatorSet (alternatingGroup 
α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mem_commutatorSet_of_isConj_sq`：mem_commutatorSet_of_isConj_sq {g : G} (
hg : IsConj g (g ^ 2)) : g in commutatorSet G
· 使用定理 `alternatingGroup.isThreeCycle_isConj`：isThreeCycle_isConj (h5 : 5 <= Nat
.card α) {σ τ : alternatingGroup α} (hσ : IsThreeCycle (σ : Perm α)) (hτ : IsThr
eeCycle (τ : Perm α)) : Is…
· 使用定理 `Equiv.Perm.IsThreeCycle.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] 
{inst_1 : DecidableEq α} [inst_2 : DecidableEq α] (σ σ_1 : Equiv.Perm α),   σ = 
σ_1 → σ.IsThreeCycle = σ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Equiv.Perm.IsThreeCycle.isThreeCycle_sq`：isThreeCycle_sq {g : Perm α} (h
t : IsThreeCycle g) : IsThreeCycle (g * g)
-/
theorem mem_commutatorSet_alternatingGroup : g ∈ commutatorSet (alternatingGroup α) := by
  apply mem_commutatorSet_of_isConj_sq
  apply alternatingGroup.isThreeCycle_isConj h5 hg
  simpa [sq] using hg.isThreeCycle_sq
/-
**Equiv.Perm.IsThreeCycle.mem_commutator_alternatingGroup** 是 Mathlib 中的一个定理，位于命
名空间 `Equiv.Perm.IsThreeCycle`。
形式化陈述：mem_commutator_alternatingGroup : g in commutator (alternatingGroup α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `commutator_eq_closure`：commutator_eq_closure : commutator G = Subgroup.c
losure (commutatorSet G)
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Equiv.Perm.IsThreeCycle.mem_commutatorSet_alternatingGroup`：mem_commutat
orSet_alternatingGroup : g in commutatorSet (alternatingGroup α)
-/
theorem mem_commutator_alternatingGroup : g ∈ commutator (alternatingGroup α) := by
  rw [commutator_eq_closure]
  apply Subgroup.subset_closure
  exact hg.mem_commutatorSet_alternatingGroup h5

end IsThreeCycle

end Equiv.Perm

section Perfect

open Subgroup Equiv.Perm

/-
**alternatingGroup.commutator_perm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：alternatingGroup.commutator_perm_le : commutator (Perm α) <= alternatingGr
oup α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `commutator_eq_closure`：commutator_eq_closure : commutator G = Subgroup.c
losure (commutatorSet G)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_commutatorElement`：map_commutatorElement : (f ⁅g₁, g₂⁆ : G') = ⁅f g₁
, f g₂⁆
-/
theorem alternatingGroup.commutator_perm_le :
    commutator (Perm α) ≤ alternatingGroup α := by
  simp only [commutator_eq_closure, closure_le, Set.subset_def, mem_commutatorSet_iff,
    SetLike.mem_coe, mem_alternatingGroup, forall_exists_index]
  rintro _ p q rfl
  simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.all]

/-- If `n ≥ 5`, then the alternating group on `n` letters is perfect -/
/-
**commutator_alternatingGroup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commutator_alternatingGroup_eq_top (h5 : 5 <= Nat.card α) : commutator (al
ternatingGroup α) = ⊤
参数：h5 : 5 <= Nat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.closure_three_cycles_eq_alternating`：closure_three_cycles_eq_
alternating : closure { σ : Perm α | IsThreeCycle σ } = alternatingGroup α
· 使用定理 `Subgroup.closure_closure_coe_preimage`：closure_closure_coe_preimage {k :
 Set G} : closure (((↑) : closure k -> G) ⁻¹' k) = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Equiv.Perm.IsThreeCycle.mem_commutator_alternatingGroup`：mem_commutator_
alternatingGroup : g in commutator (alternatingGroup α)

--- 原说明 ---
If `n ≥ 5`, then the alternating group on `n` letters is perfect
-/
theorem commutator_alternatingGroup_eq_top (h5 : 5 ≤ Nat.card α) :
    commutator (alternatingGroup α) = ⊤ := by
  suffices closure {b : alternatingGroup α | (b : Perm α).IsThreeCycle} = ⊤ by
    rw [eq_top_iff, ← this, Subgroup.closure_le]
    intro b hb
    exact hb.mem_commutator_alternatingGroup h5
  rw [← closure_three_cycles_eq_alternating]
  exact Subgroup.closure_closure_coe_preimage

/-- If `n ≥ 5`, then the alternating group on `n` letters is perfect (subgroup version) -/
/-
**commutator_alternatingGroup_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commutator_alternatingGroup_eq_self (h5 : 5 <= Nat.card α) : ⁅alternatingG
roup α, alternatingGroup α⁆ = alternatingGroup α
参数：h5 : 5 <= Nat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.map_subtype_commutator`：Subgroup.map_subtype_commutator (H : Su
bgroup G) : (_root_.commutator H).map H.subtype = ⁅H, H⁆
· 使用定理 `commutator_alternatingGroup_eq_top`：commutator_alternatingGroup_eq_top (
h5 : 5 <= Nat.card α) : commutator (alternatingGroup α) = ⊤
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H

--- 原说明 ---
If `n ≥ 5`, then the alternating group on `n` letters is perfect (subgroup versi
on)
-/
theorem commutator_alternatingGroup_eq_self (h5 : 5 ≤ Nat.card α) :
    ⁅alternatingGroup α, alternatingGroup α⁆ = alternatingGroup α := by
  rw [← Subgroup.map_subtype_commutator, commutator_alternatingGroup_eq_top h5,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The commutator subgroup of the permutation group is the alternating group -/
/-
**alternatingGroup.commutator_perm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：alternatingGroup.commutator_perm_eq (h5 : 5 <= Nat.card α) : commutator (P
erm α) = alternatingGroup α
参数：h5 : 5 <= Nat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `alternatingGroup.commutator_perm_le`：alternatingGroup.commutator_perm_le
 : commutator (Perm α) <= alternatingGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `commutator_alternatingGroup_eq_self`：commutator_alternatingGroup_eq_self
 (h5 : 5 <= Nat.card α) : ⁅alternatingGroup α, alternatingGroup α⁆ = alternating
Group α
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
The commutator subgroup of the permutation group is the alternating group
-/
theorem alternatingGroup.commutator_perm_eq (h5 : 5 ≤ Nat.card α) :
    commutator (Perm α) = alternatingGroup α := by
  apply le_antisymm alternatingGroup.commutator_perm_le
  rw [← commutator_alternatingGroup_eq_self h5]
  exact commutator_mono le_top le_top

end Perfect

