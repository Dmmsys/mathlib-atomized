/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Order.Filter.TendstoCofinite

/-!
# Theory of univariate polynomials

We define the multiset of roots of a polynomial, and prove basic results about it.

## Main definitions

* `Polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `Polynomial.rootSet p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

@[expose] public section

assert_not_exists Ideal

open Multiset Finset

noncomputable section

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : Nat}

section CommRing

variable [CommRing R] [IsDomain R] {p q : R[X]}

section Roots

/--
Definition of `roots` / `roots` 的定义

English:
definition roots
  signature: (p : R[X])
  body: haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

中文:
定义 roots
  签名: (p : R[X])
  定义体: haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

Depends on / 依赖: Classical, Classical.choose, Classical.dec, Classical.decEq, exists_multiset_roots
-/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

/--
theorem `roots_def` / 定理 `roots_def`

English:
theorem roots_def
  given: [DecidableEq R] (p : R[X]) [Decidable (p = 0)]
  proof: by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl

@[simp]

中文:
定理 roots_def
  条件: [DecidableEq R] (p : R[X]) [可判定 (p = 0)]
  证明: by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl

@[simp]

Depends on / 依赖: Classical, Classical.dec, Classical.decEq, Subsingleton, Subsingleton.elim, rename_i
-/
theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl

@[simp]
/--
theorem `roots_zero` / 定理 `roots_zero`

English:
theorem roots_zero
  statement: (0 : R[X]).roots = 0
  proof: dif_pos rfl

中文:
定理 roots_zero
  结论: (0 : R[X]).roots = 0
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl

/--
theorem `card_roots` / 定理 `card_roots`

English:
theorem card_roots
  given: (hp0 : p != 0)
  statement: (Multiset.card (roots p) : WithBot Nat) <= degree p
  proof: by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1

中文:
定理 card_roots
  条件: (hp0 : p != 0)
  结论: (Multiset.card (roots p) : WithBot 自然数) <= degree p
  证明: by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, classical, dif_neg, exists_multiset_roots
-/
theorem card_roots (hp0 : p != 0) : (Multiset.card (roots p) : WithBot Nat) <= degree p := by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1

/--
theorem `card_roots'` / 定理 `card_roots'`

English:
theorem card_roots'
  given: (p : R[X])
  statement: Multiset.card p.roots <= natDegree p
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))

中文:
定理 card_roots'
  条件: (p : R[X])
  结论: Multiset.card p.roots <= natDegree p
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))

Depends on / 依赖: WithBot, WithBot.coe_le_coe, card_roots, coe_le_coe, degree_eq_natDegree, le_of_eq, le_trans
-/
theorem card_roots' (p : R[X]) : Multiset.card p.roots <= natDegree p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))

/--
theorem `card_roots_sub_C` / 定理 `card_roots_sub_C`

English:
theorem card_roots_sub_C
  given: {p : R[X]} {a : R} (hp0 : 0 < degree p)
  proof: calc
    (Multiset.card (p - C a).roots : WithBot Nat) <= degree (p - C a) :=
card_roots mt sub_eq_zero.1 fun h => not_le_of_gt hp0 h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

中文:
定理 card_roots_sub_C
  条件: {p : R[X]} {a : R} (hp0 : 0 < degree p)
  证明: calc
    (Multiset.card (p - C a).roots : WithBot Nat) <= degree (p - C a) :=
card_roots mt sub_eq_zero.1 fun h => not_le_of_gt hp0 h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

Depends on / 依赖: C_neg, Multiset, Multiset.card, WithBot, card_roots, degree, degree_C_le, degree_add_C, h.symm, not_le_of_gt, sub_eq_add_neg, sub_eq_zero
-/
theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (Multiset.card (p - C a).roots : WithBot Nat) <= degree p :=
  calc
    (Multiset.card (p - C a).roots : WithBot Nat) <= degree (p - C a) :=
card_roots mt sub_eq_zero.1 fun h => not_le_of_gt hp0 h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

/--
theorem `card_roots_sub_C'` / 定理 `card_roots_sub_C'`

English:
theorem card_roots_sub_C'
  given: {p : R[X]} {a : R} (hp0 : 0 < degree p)
  proof: WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

@[simp]

中文:
定理 card_roots_sub_C'
  条件: {p : R[X]} {a : R} (hp0 : 0 < degree p)
  证明: WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_le_coe, card_roots_sub_C, coe_le_coe, degree_eq_natDegree, le_of_eq, le_trans
-/
theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots <= natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

@[simp]
/--
theorem `count_roots` / 定理 `count_roots`

English:
theorem count_roots
  given: [DecidableEq R] (p : R[X])
  statement: p.roots.count a = rootMultiplicity a p
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def]; rw [dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

@[simp]

中文:
定理 count_roots
  条件: [DecidableEq R] (p : R[X])
  结论: p.roots.count a = rootMultiplicity a p
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def]; rw [dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_neg, exists_multiset_roots, roots_def
-/
theorem count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def]; rw [dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

@[simp]
/--
theorem `mem_roots'` / 定理 `mem_roots'`

English:
theorem mem_roots'
  statement: a in p.roots ↔ p != 0 ∧ IsRoot p a
  proof: by
  classical
  rw [← count_pos]; rw [count_roots p]; rw [rootMultiplicity_pos']

中文:
定理 mem_roots'
  结论: a in p.roots ↔ p != 0 ∧ IsRoot p a
  证明: by
  classical
  rw [← count_pos]; rw [count_roots p]; rw [rootMultiplicity_pos']

Depends on / 依赖: classical, count_pos, count_roots, rootMultiplicity_pos
-/
theorem mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a := by
  classical
  rw [← count_pos]; rw [count_roots p]; rw [rootMultiplicity_pos']

/--
theorem `mem_roots` / 定理 `mem_roots`

English:
theorem mem_roots
  given: (hp : p != 0)
  statement: a in p.roots ↔ IsRoot p a
  proof: mem_roots'.trans and_iff_right hp

中文:
定理 mem_roots
  条件: (hp : p != 0)
  结论: a in p.roots ↔ IsRoot p a
  证明: mem_roots'.trans and_iff_right hp

Depends on / 依赖: and_iff_right, mem_roots
-/
theorem mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p a :=
mem_roots'.trans and_iff_right hp

/--
theorem `ne_zero_of_mem_roots` / 定理 `ne_zero_of_mem_roots`

English:
theorem ne_zero_of_mem_roots
  given: (h : a in p.roots)
  statement: p != 0
  proof: (mem_roots'.1 h).1

中文:
定理 ne_zero_of_mem_roots
  条件: (h : a in p.roots)
  结论: p != 0
  证明: (mem_roots'.1 h).1

Depends on / 依赖: mem_roots
-/
theorem ne_zero_of_mem_roots (h : a in p.roots) : p != 0 :=
  (mem_roots'.1 h).1

/--
theorem `isRoot_of_mem_roots` / 定理 `isRoot_of_mem_roots`

English:
theorem isRoot_of_mem_roots
  given: (h : a in p.roots)
  statement: IsRoot p a
  proof: (mem_roots'.1 h).2

中文:
定理 isRoot_of_mem_roots
  条件: (h : a in p.roots)
  结论: IsRoot p a
  证明: (mem_roots'.1 h).2

Depends on / 依赖: mem_roots
-/
theorem isRoot_of_mem_roots (h : a in p.roots) : IsRoot p a :=
  (mem_roots'.1 h).2

/--
theorem `roots_eq_zero_iff_isRoot_eq_bot` / 定理 `roots_eq_zero_iff_isRoot_eq_bot`

English:
theorem roots_eq_zero_iff_isRoot_eq_bot
  given: (hp0 : p != 0)
  statement: p.roots = 0 ↔ p.IsRoot = ⊥
  proof: by
.mp hx⟩ refine ⟨fun h => ?_, fun h => eq_zero_of_forall_notMem fun x hx => h ▸ mem_roots hp0
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, mem_roots hp0 |>.not.mp <| by simp [h]]

中文:
定理 roots_eq_zero_iff_isRoot_eq_bot
  条件: (hp0 : p != 0)
  结论: p.roots = 0 ↔ p.IsRoot = ⊥
  证明: by
.mp hx⟩ refine ⟨fun h => ?_, fun h => eq_zero_of_forall_notMem fun x hx => h ▸ mem_roots hp0
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, mem_roots hp0 |>.not.mp <| by simp [h]]

Depends on / 依赖: Pi.bot_apply, Prop.bot_eq_false, bot_apply, bot_eq_false, eq_zero_of_forall_notMem, mem_roots, not.mp
-/
theorem roots_eq_zero_iff_isRoot_eq_bot (hp0 : p != 0) : p.roots = 0 ↔ p.IsRoot = ⊥ := by
.mp hx⟩ refine ⟨fun h => ?_, fun h => eq_zero_of_forall_notMem fun x hx => h ▸ mem_roots hp0
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, mem_roots hp0 |>.not.mp <| by simp [h]]

/--
theorem `roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot` / 定理 `roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot`

English:
theorem roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot
  statement: p.roots = 0 ↔ p = 0 ∨ p.IsRoot = ⊥
  proof: by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp [roots_eq_zero_iff_isRoot_eq_bot hp0, hp0]

中文:
定理 roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot
  结论: p.roots = 0 ↔ p = 0 ∨ p.IsRoot = ⊥
  证明: by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp [roots_eq_zero_iff_isRoot_eq_bot hp0, hp0]

Depends on / 依赖: eq_or_ne, roots_eq_zero_iff_isRoot_eq_bot
-/
theorem roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot : p.roots = 0 ↔ p = 0 ∨ p.IsRoot = ⊥ := by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp [roots_eq_zero_iff_isRoot_eq_bot hp0, hp0]

/--
theorem `mem_roots_map_of_injective` / 定理 `mem_roots_map_of_injective`

English:
theorem mem_roots_map_of_injective
  statement: [Semiring S] {p : S[X]} {f : S ->+* R}
  proof: by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp)]; rw [IsRoot]; rw [eval_map]

中文:
定理 mem_roots_map_of_injective
  结论: [半环 S] {p : S[X]} {f : S ->+* R}
  证明: by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp)]; rw [IsRoot]; rw [eval_map]

Depends on / 依赖: IsRoot, Polynomial, Polynomial.map_ne_zero_iff, eval_map, map_ne_zero_iff, mem_roots
-/
theorem mem_roots_map_of_injective [Semiring S] {p : S[X]} {f : S ->+* R}
    (hf : Function.Injective f) {x : R} (hp : p != 0) : x in (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp)]; rw [IsRoot]; rw [eval_map]

/--
lemma `mem_roots_iff_aeval_eq_zero` / 引理 `mem_roots_iff_aeval_eq_zero`

English:
lemma mem_roots_iff_aeval_eq_zero
  given: {x : R} (w : p != 0)
  statement: x in roots p ↔ aeval x p = 0
  proof: by
  rw [aeval_def]; rw [← mem_roots_map_of_injective (FaithfulSMul.algebraMap_injective _ _) w]; rw [Algebra.algebraMap_self]; rw [map_id]

中文:
引理 mem_roots_iff_aeval_eq_zero
  条件: {x : R} (w : p != 0)
  结论: x in roots p ↔ aeval x p = 0
  证明: by
  rw [aeval_def]; rw [← mem_roots_map_of_injective (FaithfulSMul.algebraMap_injective _ _) w]; rw [Algebra.algebraMap_self]; rw [map_id]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, FaithfulSMul, FaithfulSMul.algebraMap_injective, aeval_def, algebraMap_injective, algebraMap_self, map_id, mem_roots_map_of_injective
-/
lemma mem_roots_iff_aeval_eq_zero {x : R} (w : p != 0) : x in roots p ↔ aeval x p = 0 := by
  rw [aeval_def]; rw [← mem_roots_map_of_injective (FaithfulSMul.algebraMap_injective _ _) w]; rw [Algebra.algebraMap_self]; rw [map_id]

/--
theorem `card_le_degree_of_subset_roots` / 定理 `card_le_degree_of_subset_roots`

English:
theorem card_le_degree_of_subset_roots
  given: {p : R[X]} {Z : Finset R} (h : Z.val subseteq p.roots)
  proof: (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

中文:
定理 card_le_degree_of_subset_roots
  条件: {p : R[X]} {Z : 有限集 R} (h : Z.val subseteq p.roots)
  证明: (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

Depends on / 依赖: Finset, Finset.val_le_iff_val_subset, Multiset, Multiset.card_le_card, Polynomial, Polynomial.card_roots, card_le_card, card_roots, val_le_iff_val_subset
-/
theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val subseteq p.roots) :
    #Z <= p.natDegree :=
  (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

/--
theorem `finite_setOfPred_isRoot` / 定理 `finite_setOfPred_isRoot`

English:
theorem finite_setOfPred_isRoot
  given: {p : R[X]} (hp : p != 0)
  statement: Set.Finite { x | IsRoot p x }
  proof: by
  classical
  simpa only [← Finset.setOfPred_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet

@[deprecated (since := "2026-07-09")] alias finite_setOf_isRoot := finite_setOfPred_isRoot

中文:
定理 finite_setOfPred_isRoot
  条件: {p : R[X]} (hp : p != 0)
  结论: 集合.有限 { x | IsRoot p x }
  证明: by
  classical
  simpa only [← Finset.setOfPred_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet

@[deprecated (since := "2026-07-09")] alias finite_setOf_isRoot := finite_setOfPred_isRoot

Depends on / 依赖: Finset, Finset.setOfPred_mem, Multiset, Multiset.mem_toFinset, classical, finite_toSet, mem_roots, mem_toFinset, p.roots.toFinset.finite_toSet, setOfPred_mem, toFinset
-/
theorem finite_setOfPred_isRoot {p : R[X]} (hp : p != 0) : Set.Finite { x | IsRoot p x } := by
  classical
  simpa only [← Finset.setOfPred_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet

@[deprecated (since := "2026-07-09")] alias finite_setOf_isRoot := finite_setOfPred_isRoot

/--
theorem `eq_zero_of_infinite_isRoot` / 定理 `eq_zero_of_infinite_isRoot`

English:
theorem eq_zero_of_infinite_isRoot
  given: (p : R[X]) (h : Set.Infinite { x | IsRoot p x })
  statement: p = 0
  proof: not_imp_comm.mp finite_setOfPred_isRoot h

中文:
定理 eq_zero_of_infinite_isRoot
  条件: (p : R[X]) (h : 集合.无限 { x | IsRoot p x })
  结论: p = 0
  证明: not_imp_comm.mp finite_setOfPred_isRoot h

Depends on / 依赖: finite_setOfPred_isRoot, not_imp_comm, not_imp_comm.mp
-/
theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_setOfPred_isRoot h

/--
theorem `exists_max_root` / 定理 `exists_max_root`

English:
theorem exists_max_root
  given: [LinearOrder R] (p : R[X]) (hp : p != 0)
  statement: exists x₀, forall x, p.IsRoot x -> x <= x₀
  proof: Set.exists_upper_bound_image _ _ finite_setOfPred_isRoot hp

中文:
定理 存在_max_root
  条件: [线性序 R] (p : R[X]) (hp : p != 0)
  结论: 存在 x₀, 对任意 x, p.IsRoot x -> x <= x₀
  证明: Set.exists_upper_bound_image _ _ finite_setOfPred_isRoot hp

Depends on / 依赖: Set.exists_upper_bound_image, exists_upper_bound_image, finite_setOfPred_isRoot
-/
theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p != 0) : exists x₀, forall x, p.IsRoot x -> x <= x₀ :=
Set.exists_upper_bound_image _ _ finite_setOfPred_isRoot hp

/--
theorem `exists_min_root` / 定理 `exists_min_root`

English:
theorem exists_min_root
  given: [LinearOrder R] (p : R[X]) (hp : p != 0)
  statement: exists x₀, forall x, p.IsRoot x -> x₀ <= x
  proof: Set.exists_lower_bound_image _ _ finite_setOfPred_isRoot hp

中文:
定理 存在_min_root
  条件: [线性序 R] (p : R[X]) (hp : p != 0)
  结论: 存在 x₀, 对任意 x, p.IsRoot x -> x₀ <= x
  证明: Set.exists_lower_bound_image _ _ finite_setOfPred_isRoot hp

Depends on / 依赖: Set.exists_lower_bound_image, exists_lower_bound_image, finite_setOfPred_isRoot
-/
theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p != 0) : exists x₀, forall x, p.IsRoot x -> x₀ <= x :=
Set.exists_lower_bound_image _ _ finite_setOfPred_isRoot hp

/--
theorem `eq_of_infinite_eval_eq` / 定理 `eq_of_infinite_eval_eq`

English:
theorem eq_of_infinite_eval_eq
  given: (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q })
  proof: by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]

中文:
定理 eq_of_infinite_eval_eq
  条件: (p q : R[X]) (h : 集合.无限 { x | eval x p = eval x q })
  证明: by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]

Depends on / 依赖: IsRoot, eq_zero_of_infinite_isRoot, eval_sub, sub_eq_zero
-/
theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]

/--
lemma `tendstoCofinite_of_natDegree_ne_zero` / 引理 `tendstoCofinite_of_natDegree_ne_zero`

English:
lemma tendstoCofinite_of_natDegree_ne_zero
  statement: {R : Type} [CommRing R] [IsDomain R] (p : R[X])
  proof: by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro x
  by_contra! hx
  obtain ⟨rfl⟩ : p = C x := p.eq_of_infinite_eval_eq (C x) (by simpa)
  simp at hp

中文:
引理 tendstoCofinite_of_natDegree_ne_zero
  结论: {R : 类型} [交换环 R] [是整环 R] (p : R[X])
  证明: by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro x
  by_contra! hx
  obtain ⟨rfl⟩ : p = C x := p.eq_of_infinite_eval_eq (C x) (by simpa)
  simp at hp

Depends on / 依赖: Filter, Filter.tendstoCofinite_iff_finite_preimage_singleton, eq_of_infinite_eval_eq, p.eq_of_infinite_eval_eq, tendstoCofinite_iff_finite_preimage_singleton
-/
lemma tendstoCofinite_of_natDegree_ne_zero {R : Type} [CommRing R] [IsDomain R] (p : R[X])
    (hp : p.natDegree != 0) : Filter.TendstoCofinite p.eval := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro x
  by_contra! hx
  obtain ⟨rfl⟩ : p = C x := p.eq_of_infinite_eval_eq (C x) (by simpa)
  simp at hp

/--
theorem `roots_mul` / 定理 `roots_mul`

English:
theorem roots_mul
  given: {p q : R[X]} (hpq : p * q != 0)
  statement: (p * q).roots = p.roots + q.roots
  proof: by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add]; rw [count_roots]; rw [count_roots]; rw [count_roots]; rw [rootMultiplicity_mul hpq]

中文:
定理 roots_mul
  条件: {p q : R[X]} (hpq : p * q != 0)
  结论: (p * q).roots = p.roots + q.roots
  证明: by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add]; rw [count_roots]; rw [count_roots]; rw [count_roots]; rw [rootMultiplicity_mul hpq]

Depends on / 依赖: Multiset, Multiset.ext.mpr, classical, count_add, count_roots, rootMultiplicity_mul
-/
theorem roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add]; rw [count_roots]; rw [count_roots]; rw [count_roots]; rw [rootMultiplicity_mul hpq]

/--
theorem `roots.le_of_dvd` / 定理 `roots.le_of_dvd`

English:
theorem roots.le_of_dvd
  given: (h : q != 0)
  statement: p ∣ q -> roots p <= roots q
  proof: by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩

中文:
定理 roots.le_of_dvd
  条件: (h : q != 0)
  结论: p ∣ q -> roots p <= roots q
  证明: by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩

Depends on / 依赖: Multiset, Multiset.le_iff_exists_add.mpr, k.roots, le_iff_exists_add, roots_mul
-/
theorem roots.le_of_dvd (h : q != 0) : p ∣ q -> roots p <= roots q := by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩

/--
theorem `mem_roots_sub_C'` / 定理 `mem_roots_sub_C'`

English:
theorem mem_roots_sub_C'
  given: {p : R[X]} {a x : R}
  statement: x in (p - C a).roots ↔ p != C a ∧ p.eval x = a
  proof: by
  rw [mem_roots']; rw [IsRoot.def]; rw [sub_ne_zero]; rw [eval_sub]; rw [sub_eq_zero]; rw [eval_C]

中文:
定理 mem_roots_sub_C'
  条件: {p : R[X]} {a x : R}
  结论: x in (p - C a).roots ↔ p != C a ∧ p.eval x = a
  证明: by
  rw [mem_roots']; rw [IsRoot.def]; rw [sub_ne_zero]; rw [eval_sub]; rw [sub_eq_zero]; rw [eval_C]

Depends on / 依赖: IsRoot, IsRoot.def, eval_C, eval_sub, mem_roots, sub_eq_zero, sub_ne_zero
-/
theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x in (p - C a).roots ↔ p != C a ∧ p.eval x = a := by
  rw [mem_roots']; rw [IsRoot.def]; rw [sub_ne_zero]; rw [eval_sub]; rw [sub_eq_zero]; rw [eval_C]

/--
theorem `mem_roots_sub_C` / 定理 `mem_roots_sub_C`

English:
theorem mem_roots_sub_C
  given: {p : R[X]} {a x : R} (hp0 : 0 < degree p)
  proof: mem_roots_sub_C'.trans and_iff_right fun hp => hp0.not_ge hp.symm ▸ degree_C_le

@[simp]

中文:
定理 mem_roots_sub_C
  条件: {p : R[X]} {a x : R} (hp0 : 0 < degree p)
  证明: mem_roots_sub_C'.trans and_iff_right fun hp => hp0.not_ge hp.symm ▸ degree_C_le

@[simp]

Depends on / 依赖: and_iff_right, degree_C_le, hp.symm, hp0.not_ge, mem_roots_sub_C, not_ge
-/
theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x in (p - C a).roots ↔ p.eval x = a :=
mem_roots_sub_C'.trans and_iff_right fun hp => hp0.not_ge hp.symm ▸ degree_C_le

@[simp]
/--
theorem `roots_X_sub_C` / 定理 `roots_X_sub_C`

English:
theorem roots_X_sub_C
  given: (r : R)
  statement: roots (X - C r) = {r}
  proof: by
  classical
  ext s
  rw [count_roots]; rw [rootMultiplicity_X_sub_C]; rw [count_singleton]

@[simp]

中文:
定理 roots_X_sub_C
  条件: (r : R)
  结论: roots (X - C r) = {r}
  证明: by
  classical
  ext s
  rw [count_roots]; rw [rootMultiplicity_X_sub_C]; rw [count_singleton]

@[simp]

Depends on / 依赖: classical, count_roots, count_singleton, rootMultiplicity_X_sub_C
-/
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  classical
  ext s
  rw [count_roots]; rw [rootMultiplicity_X_sub_C]; rw [count_singleton]

@[simp]
/--
theorem `roots_X_add_C` / 定理 `roots_X_add_C`

English:
theorem roots_X_add_C
  given: (r : R)
  statement: roots (X + C r) = {-r}
  proof: by simpa using roots_X_sub_C (-r)

@[simp]

中文:
定理 roots_X_add_C
  条件: (r : R)
  结论: roots (X + C r) = {-r}
  证明: by simpa using roots_X_sub_C (-r)

@[simp]

Depends on / 依赖: roots_X_sub_C
-/
theorem roots_X_add_C (r : R) : roots (X + C r) = {-r} := by simpa using roots_X_sub_C (-r)

@[simp]
/--
theorem `roots_X` / 定理 `roots_X`

English:
theorem roots_X
  statement: roots (X : R[X]) = {0}
  proof: by rw [← roots_X_sub_C, C_0, sub_zero]

@[simp]

中文:
定理 roots_X
  结论: roots (X : R[X]) = {0}
  证明: by rw [← roots_X_sub_C, C_0, sub_zero]

@[simp]

Depends on / 依赖: roots_X_sub_C, sub_zero
-/
theorem roots_X : roots (X : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]

@[simp]
/--
theorem `roots_C` / 定理 `roots_C`

English:
theorem roots_C
  given: (x : R)
  statement: (C x).roots = 0
  proof: by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots]; rw [count_zero]; rw [rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])

@[simp]

中文:
定理 roots_C
  条件: (x : R)
  结论: (C x).roots = 0
  证明: by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots]; rw [count_zero]; rw [rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])

@[simp]

Depends on / 依赖: Multiset, Multiset.ext.mpr, classical, count_roots, count_zero, not_isRoot_C, rootMultiplicity_eq_zero, roots_zero
-/
theorem roots_C (x : R) : (C x).roots = 0 := by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots]; rw [count_zero]; rw [rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])

@[simp]
/--
theorem `roots_one` / 定理 `roots_one`

English:
theorem roots_one
  statement: (1 : R[X]).roots = ∅
  proof: roots_C 1

@[simp]

中文:
定理 roots_one
  结论: (1 : R[X]).roots = ∅
  证明: roots_C 1

@[simp]

Depends on / 依赖: roots_C
-/
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1

@[simp]
/--
theorem `roots_C_mul` / 定理 `roots_C_mul`

English:
theorem roots_C_mul
  given: (p : R[X]) (ha : a != 0)
  statement: (C a * p).roots = p.roots
  proof: by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]

中文:
定理 roots_C_mul
  条件: (p : R[X]) (ha : a != 0)
  结论: (C a * p).roots = p.roots
  证明: by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]

Depends on / 依赖: C_eq_zero, mul_eq_zero, mul_zero, not_false_iff, or_self_iff, roots_C, roots_mul, zero_add
-/
theorem roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]

/--
theorem `_root_.Associated.roots_eq` / 定理 `_root_.Associated.roots_eq`

English:
theorem _root_.Associated.roots_eq
  given: {p q : R[X]} (h : Associated p q)
  statement: p.roots = q.roots
  proof: by
  obtain ⟨u, rfl⟩ := h
  rw [eq_C_of_degree_eq_zero <| degree_coe_units u]; rw [mul_comm]; rw [roots_C_mul _ coeff_coe_units_zero_ne_zero u]

@[simp]

中文:
定理 _root_.Associated.roots_eq
  条件: {p q : R[X]} (h : Associated p q)
  结论: p.roots = q.roots
  证明: by
  obtain ⟨u, rfl⟩ := h
  rw [eq_C_of_degree_eq_zero <| degree_coe_units u]; rw [mul_comm]; rw [roots_C_mul _ coeff_coe_units_zero_ne_zero u]

@[simp]

Depends on / 依赖: coeff_coe_units_zero_ne_zero, degree_coe_units, eq_C_of_degree_eq_zero, mul_comm, roots_C_mul
-/
theorem _root_.Associated.roots_eq {p q : R[X]} (h : Associated p q) : p.roots = q.roots := by
  obtain ⟨u, rfl⟩ := h
  rw [eq_C_of_degree_eq_zero <| degree_coe_units u]; rw [mul_comm]; rw [roots_C_mul _ coeff_coe_units_zero_ne_zero u]

@[simp]
/--
theorem `roots_smul_nonzero` / 定理 `roots_smul_nonzero`

English:
theorem roots_smul_nonzero
  given: (p : R[X]) (ha : a != 0)
  statement: (a • p).roots = p.roots
  proof: by
  rw [smul_eq_C_mul]; rw [roots_C_mul _ ha]

@[simp]

中文:
定理 roots_smul_nonzero
  条件: (p : R[X]) (ha : a != 0)
  结论: (a • p).roots = p.roots
  证明: by
  rw [smul_eq_C_mul]; rw [roots_C_mul _ ha]

@[simp]

Depends on / 依赖: roots_C_mul, smul_eq_C_mul
-/
theorem roots_smul_nonzero (p : R[X]) (ha : a != 0) : (a • p).roots = p.roots := by
  rw [smul_eq_C_mul]; rw [roots_C_mul _ ha]

@[simp]
/--
lemma `roots_neg` / 引理 `roots_neg`

English:
lemma roots_neg
  given: (p : R[X])
  statement: (-p).roots = p.roots
  proof: by
  rw [← neg_one_smul R p]; rw [roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

@[simp]

中文:
引理 roots_neg
  条件: (p : R[X])
  结论: (-p).roots = p.roots
  证明: by
  rw [← neg_one_smul R p]; rw [roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

@[simp]

Depends on / 依赖: neg_ne_zero, neg_ne_zero.mpr, neg_one_smul, one_ne_zero, roots_smul_nonzero
-/
lemma roots_neg (p : R[X]) : (-p).roots = p.roots := by
  rw [← neg_one_smul R p]; rw [roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

@[simp]
/--
theorem `map_roots_comp_C_mul_X_add_C` / 定理 `map_roots_comp_C_mul_X_add_C`

English:
theorem map_roots_comp_C_mul_X_add_C
  given: (p : R[X]) (a b : R) (ha : IsUnit a)
  proof: by
  classical
  set f := fun x => a * x + b
  have hf : Function.Bijective f :=
    (AddGroup.addRight_bijective b).comp (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)
  rw [Multiset.ext]
  intro x
  obtain ⟨x, rfl⟩ := hf.surjective x
  rw [count_roots]; rw [count_map_eq_count' f _ hf.injective]; rw [

中文:
定理 map_roots_comp_C_mul_X_add_C
  条件: (p : R[X]) (a b : R) (ha : 是单位 a)
  证明: by
  classical
  set f := fun x => a * x + b
  have hf : Function.Bijective f :=
    (AddGroup.addRight_bijective b).comp (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)
  rw [Multiset.ext]
  intro x
  obtain ⟨x, rfl⟩ := hf.surjective x
  rw [count_roots]; rw [count_map_eq_count' f _ hf.injective]; rw [

Depends on / 依赖: AddGroup, AddGroup.addRight_bijective, Bijective, Function, Function.Bijective, IsUnit, IsUnit.isUnit_iff_mulLeft_bijective.mp, Multiset, Multiset.ext, addRight_bijective, classical, count_map_eq_count, count_roots, hf.injective, hf.surjective, injective, isUnit_iff_mulLeft_bijective, rootMultiplicity_comp_C_mul_X_add_C, surjective
-/
theorem map_roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).roots.map (fun x => a * x + b) = p.roots := by
  classical
  set f := fun x => a * x + b
  have hf : Function.Bijective f :=
    (AddGroup.addRight_bijective b).comp (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)
  rw [Multiset.ext]
  intro x
  obtain ⟨x, rfl⟩ := hf.surjective x
  rw [count_roots]; rw [count_map_eq_count' f _ hf.injective]; rw [count_roots]; rw [rootMultiplicity_comp_C_mul_X_add_C p a b x ha]

open scoped Ring in
/--
theorem `roots_comp_C_mul_X_add_C` / 定理 `roots_comp_C_mul_X_add_C`

English:
theorem roots_comp_C_mul_X_add_C
  given: (p : R[X]) (a b : R) (ha : IsUnit a)
  proof: by
  conv_rhs => rw [← p.map_roots_comp_C_mul_X_add_C a b ha]
  simp [← mul_assoc, Ring.inverse_mul_cancel a ha]

@[simp]

中文:
定理 roots_comp_C_mul_X_add_C
  条件: (p : R[X]) (a b : R) (ha : 是单位 a)
  证明: by
  conv_rhs => rw [← p.map_roots_comp_C_mul_X_add_C a b ha]
  simp [← mul_assoc, Ring.inverse_mul_cancel a ha]

@[simp]

Depends on / 依赖: Ring.inverse_mul_cancel, conv_rhs, inverse_mul_cancel, map_roots_comp_C_mul_X_add_C, mul_assoc, p.map_roots_comp_C_mul_X_add_C
-/
theorem roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).roots = p.roots.map (fun x => a⁻¹ʳ * (x - b)) := by
  conv_rhs => rw [← p.map_roots_comp_C_mul_X_add_C a b ha]
  simp [← mul_assoc, Ring.inverse_mul_cancel a ha]

@[simp]
/--
theorem `roots_comp_neg_X` / 定理 `roots_comp_neg_X`

English:
theorem roots_comp_neg_X
  given: (p : R[X])
  statement: (p.comp (-X)).roots = p.roots.map fun x => -x
  proof: by
  simp [← map_roots_comp_C_mul_X_add_C p (-1) 0 isUnit_neg_one]

@[simp]

中文:
定理 roots_comp_neg_X
  条件: (p : R[X])
  结论: (p.comp (-X)).roots = p.roots.map fun x => -x
  证明: by
  simp [← map_roots_comp_C_mul_X_add_C p (-1) 0 isUnit_neg_one]

@[simp]

Depends on / 依赖: isUnit_neg_one, map_roots_comp_C_mul_X_add_C
-/
theorem roots_comp_neg_X (p : R[X]) : (p.comp (-X)).roots = p.roots.map fun x => -x := by
  simp [← map_roots_comp_C_mul_X_add_C p (-1) 0 isUnit_neg_one]

@[simp]
/--
theorem `roots_C_mul_X_sub_C_of_IsUnit` / 定理 `roots_C_mul_X_sub_C_of_IsUnit`

English:
theorem roots_C_mul_X_sub_C_of_IsUnit
  given: (b : R) (a : Rˣ)
  statement: (C (a : R) * X - C b).roots =
  proof: by
  rw [← roots_C_mul _ (Units.ne_zero a⁻¹)]; rw [mul_sub]; rw [← mul_assoc]; rw [← C_mul]; rw [← C_mul]; rw [Units.inv_mul]; rw [C_1]; rw [one_mul]
  exact roots_X_sub_C (a⁻¹ * b)

@[simp]

中文:
定理 roots_C_mul_X_sub_C_of_IsUnit
  条件: (b : R) (a : Rˣ)
  结论: (C (a : R) * X - C b).roots =
  证明: by
  rw [← roots_C_mul _ (Units.ne_zero a⁻¹)]; rw [mul_sub]; rw [← mul_assoc]; rw [← C_mul]; rw [← C_mul]; rw [Units.inv_mul]; rw [C_1]; rw [one_mul]
  exact roots_X_sub_C (a⁻¹ * b)

@[simp]

Depends on / 依赖: C_mul, Units.inv_mul, Units.ne_zero, inv_mul, mul_assoc, mul_sub, ne_zero, one_mul, roots_C_mul, roots_X_sub_C
-/
theorem roots_C_mul_X_sub_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X - C b).roots =
    {a⁻¹ * b} := by
  rw [← roots_C_mul _ (Units.ne_zero a⁻¹)]; rw [mul_sub]; rw [← mul_assoc]; rw [← C_mul]; rw [← C_mul]; rw [Units.inv_mul]; rw [C_1]; rw [one_mul]
  exact roots_X_sub_C (a⁻¹ * b)

@[simp]
/--
theorem `roots_C_mul_X_add_C_of_IsUnit` / 定理 `roots_C_mul_X_add_C_of_IsUnit`

English:
theorem roots_C_mul_X_add_C_of_IsUnit
  given: (b : R) (a : Rˣ)
  statement: (C (a : R) * X + C b).roots =
  proof: by
  rw [← sub_neg_eq_add]; rw [← C_neg]; rw [roots_C_mul_X_sub_C_of_IsUnit]; rw [mul_neg]

中文:
定理 roots_C_mul_X_add_C_of_IsUnit
  条件: (b : R) (a : Rˣ)
  结论: (C (a : R) * X + C b).roots =
  证明: by
  rw [← sub_neg_eq_add]; rw [← C_neg]; rw [roots_C_mul_X_sub_C_of_IsUnit]; rw [mul_neg]

Depends on / 依赖: C_neg, mul_neg, roots_C_mul_X_sub_C_of_IsUnit, sub_neg_eq_add
-/
theorem roots_C_mul_X_add_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X + C b).roots =
    {-(a⁻¹ * b)} := by
  rw [← sub_neg_eq_add]; rw [← C_neg]; rw [roots_C_mul_X_sub_C_of_IsUnit]; rw [mul_neg]

/--
theorem `roots_list_prod` / 定理 `roots_list_prod`

English:
theorem roots_list_prod
  given: (L : List R[X])
  proof: List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons]; rw [not_or] at H
    rw [List.prod_cons]; rw [roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2)]; rw [←
      Multiset.cons_coe]; rw [Multiset.cons_bind]; rw [ih H.2]

中文:
定理 roots_list_prod
  条件: (L : 列表 R[X])
  证明: List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons]; rw [not_or] at H
    rw [List.prod_cons]; rw [roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2)]; rw [←
      Multiset.cons_coe]; rw [Multiset.cons_bind]; rw [ih H.2]

Depends on / 依赖: List.mem_cons, List.prod_cons, List.prod_ne_zero, List.recOn, Multiset, Multiset.cons_bind, Multiset.cons_coe, Ne.symm, cons_bind, cons_coe, mem_cons, mul_ne_zero, not_or, prod_cons, prod_ne_zero, roots_mul, roots_one
-/
theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L -> L.prod.roots = (L : Multiset R[X]).bind roots :=
  List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons]; rw [not_or] at H
    rw [List.prod_cons]; rw [roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2)]; rw [←
      Multiset.cons_coe]; rw [Multiset.cons_bind]; rw [ih H.2]

/--
theorem `roots_multiset_prod` / 定理 `roots_multiset_prod`

English:
theorem roots_multiset_prod
  given: (m : Multiset R[X])
  statement: (0 : R[X]) ∉ m -> m.prod.roots = m.bind roots
  proof: by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using! roots_list_prod L

中文:
定理 roots_multiset_prod
  条件: (m : Multiset R[X])
  结论: (0 : R[X]) ∉ m -> m.乘积.roots = m.bind roots
  证明: by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using! roots_list_prod L

Depends on / 依赖: Multiset, Multiset.prod_coe, prod_coe, quot_mk_to_coe, roots_list_prod
-/
theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m -> m.prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using! roots_list_prod L

/--
theorem `roots_prod` / 定理 `roots_prod`

English:
theorem roots_prod
  given: {ι : Type*} (f : ι -> R[X]) (s : Finset ι)
  proof: by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)

@[simp]

中文:
定理 roots_prod
  条件: {ι : 类型} (f : ι -> R[X]) (s : 有限集 ι)
  证明: by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)

@[simp]

Depends on / 依赖: Multiset, Multiset.bind_map, Multiset.prod_eq_zero_iff, bind_map, m.map, prod_eq_zero_iff, roots_multiset_prod
-/
theorem roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finset ι) :
    s.prod f != 0 -> (s.prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)

@[simp]
/--
theorem `roots_pow` / 定理 `roots_pow`

English:
theorem roots_pow
  given: (p : R[X]) (n : Nat)
  statement: (p ^ n).roots = n • p.roots
  proof: by
  induction n with
  | zero => rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  | succ n ihn =>
    rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, roots_zero, smul_zero]
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]

中文:
定理 roots_pow
  条件: (p : R[X]) (n : 自然数)
  结论: (p ^ n).roots = n • p.roots
  证明: by
  induction n with
  | zero => rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  | succ n ihn =>
    rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, roots_zero, smul_zero]
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]

Depends on / 依赖: add_smul, empty_eq_zero, eq_or_ne, mul_ne_zero, n.succ_ne_zero, one_smul, pow_ne_zero, pow_succ, pow_zero, roots_mul, roots_one, roots_zero, smul_zero, succ_ne_zero, zero_pow, zero_smul
-/
theorem roots_pow (p : R[X]) (n : Nat) : (p ^ n).roots = n • p.roots := by
  induction n with
  | zero => rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  | succ n ihn =>
    rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, roots_zero, smul_zero]
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]

/--
theorem `roots_X_pow` / 定理 `roots_X_pow`

English:
theorem roots_X_pow
  given: (n : Nat)
  statement: (X ^ n : R[X]).roots = n • ({0} : Multiset R)
  proof: by
  rw [roots_pow]; rw [roots_X]

中文:
定理 roots_X_pow
  条件: (n : 自然数)
  结论: (X ^ n : R[X]).roots = n • ({0} : Multiset R)
  证明: by
  rw [roots_pow]; rw [roots_X]

Depends on / 依赖: roots_X, roots_pow
-/
theorem roots_X_pow (n : Nat) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow]; rw [roots_X]

/--
theorem `roots_C_mul_X_pow` / 定理 `roots_C_mul_X_pow`

English:
theorem roots_C_mul_X_pow
  given: (ha : a != 0) (n : Nat)
  proof: by
  rw [roots_C_mul _ ha]; rw [roots_X_pow]

@[simp]

中文:
定理 roots_C_mul_X_pow
  条件: (ha : a != 0) (n : 自然数)
  证明: by
  rw [roots_C_mul _ ha]; rw [roots_X_pow]

@[simp]

Depends on / 依赖: roots_C_mul, roots_X_pow
-/
theorem roots_C_mul_X_pow (ha : a != 0) (n : Nat) :
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [roots_C_mul _ ha]; rw [roots_X_pow]

@[simp]
/--
theorem `roots_monomial` / 定理 `roots_monomial`

English:
theorem roots_monomial
  given: (ha : a != 0) (n : Nat)
  statement: (monomial n a).roots = n • ({0} : Multiset R)
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [roots_C_mul_X_pow ha]

中文:
定理 roots_monomial
  条件: (ha : a != 0) (n : 自然数)
  结论: (monomial n a).roots = n • ({0} : Multiset R)
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [roots_C_mul_X_pow ha]

Depends on / 依赖: C_mul_X_pow_eq_monomial, roots_C_mul_X_pow
-/
theorem roots_monomial (ha : a != 0) (n : Nat) : (monomial n a).roots = n • ({0} : Multiset R) := by
  rw [← C_mul_X_pow_eq_monomial]; rw [roots_C_mul_X_pow ha]

/--
theorem `roots_prod_X_sub_C` / 定理 `roots_prod_X_sub_C`

English:
theorem roots_prod_X_sub_C
  given: (s : Finset R)
  statement: (s.prod fun a => X - C a).roots = s.val
  proof: by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton]; rw [Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)

@[simp]

中文:
定理 roots_prod_X_sub_C
  条件: (s : 有限集 R)
  结论: (s.乘积 fun a => X - C a).roots = s.val
  证明: by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton]; rw [Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)

@[simp]

Depends on / 依赖: Multiset, Multiset.bind_singleton, Multiset.map_id, X_sub_C_ne_zero, bind_singleton, map_id, prod_ne_zero_iff, prod_ne_zero_iff.mpr, roots_X_sub_C, roots_prod, simp_rw
-/
theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton]; rw [Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)

@[simp]
/--
theorem `roots_multiset_prod_X_sub_C` / 定理 `roots_multiset_prod_X_sub_C`

English:
theorem roots_multiset_prod_X_sub_C
  given: (s : Multiset R)
  statement: (s.map fun a => X - C a).prod.roots = s
  proof: by
  rw [roots_multiset_prod]; rw [Multiset.bind_map]
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton]; rw [Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h

中文:
定理 roots_multiset_prod_X_sub_C
  条件: (s : Multiset R)
  结论: (s.map fun a => X - C a).乘积.roots = s
  证明: by
  rw [roots_multiset_prod]; rw [Multiset.bind_map]
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton]; rw [Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h

Depends on / 依赖: Multiset, Multiset.bind_map, Multiset.bind_singleton, Multiset.map_id, Multiset.mem_map, X_sub_C_ne_zero, bind_map, bind_singleton, map_id, mem_map, roots_X_sub_C, roots_multiset_prod, simp_rw
-/
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).prod.roots = s := by
  rw [roots_multiset_prod]; rw [Multiset.bind_map]
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton]; rw [Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h

/--
theorem `roots_ofMultiset` / 定理 `roots_ofMultiset`

English:
theorem roots_ofMultiset
  given: (s : Multiset R)
  statement: (ofMultiset s).roots = s
  proof: by
  simp

中文:
定理 roots_ofMultiset
  条件: (s : Multiset R)
  结论: (ofMultiset s).roots = s
  证明: by
  simp
-/
theorem roots_ofMultiset (s : Multiset R) : (ofMultiset s).roots = s := by
  simp

variable (R) in
/--
theorem `rightInverse_ofMultiset_roots` / 定理 `rightInverse_ofMultiset_roots`

English:
theorem rightInverse_ofMultiset_roots
  statement: Function.RightInverse (α := R[X]) ofMultiset roots
  proof: roots_ofMultiset

中文:
定理 rightInverse_ofMultiset_roots
  结论: 函数.右逆 (α := R[X]) ofMultiset roots
  证明: roots_ofMultiset

Depends on / 依赖: ofMultiset
-/
theorem rightInverse_ofMultiset_roots : Function.RightInverse (α := R[X]) ofMultiset roots :=
  roots_ofMultiset

variable (R) in
/--
theorem `ofMultiset_injective` / 定理 `ofMultiset_injective`

English:
theorem ofMultiset_injective
  statement: Function.Injective (ofMultiset (R := R))
  proof: .injective rightInverse_ofMultiset_roots R

中文:
定理 ofMultiset_injective
  结论: 函数.单射 (ofMultiset (R := R))
  证明: .injective rightInverse_ofMultiset_roots R
-/
theorem ofMultiset_injective : Function.Injective (ofMultiset (R := R)) :=
.injective rightInverse_ofMultiset_roots R

/--
theorem `card_roots_X_pow_sub_C` / 定理 `card_roots_X_pow_sub_C`

English:
theorem card_roots_X_pow_sub_C
  given: {n : Nat} (hn : 0 < n) (a : R)
  proof: WithBot.coe_le_coe.1
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot Nat) <= degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a

中文:
定理 card_roots_X_pow_sub_C
  条件: {n : 自然数} (hn : 0 < n) (a : R)
  证明: WithBot.coe_le_coe.1
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot Nat) <= degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a

Depends on / 依赖: Multiset, Multiset.card, WithBot, WithBot.coe_le_coe, X_pow_sub_C_ne_zero, card_roots, coe_le_coe, degree, degree_X_pow_sub_C
-/
theorem card_roots_X_pow_sub_C {n : Nat} (hn : 0 < n) (a : R) :
    Multiset.card (roots ((X : R[X]) ^ n - C a)) <= n :=
WithBot.coe_le_coe.1
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot Nat) <= degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a

/--
theorem `roots_eq_of_degree_le_card_of_ne_zero` / 定理 `roots_eq_of_degree_le_card_of_ne_zero`

English:
theorem roots_eq_of_degree_le_card_of_ne_zero
  statement: {S : Finset R}
  proof: by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx => (p.mem_roots hp).mpr (hS x hx)))
  · simpa using (p.card_roots hp).trans hcard

中文:
定理 roots_eq_of_degree_le_card_of_ne_zero
  结论: {S : 有限集 R}
  证明: by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx => (p.mem_roots hp).mpr (hS x hx)))
  · simpa using (p.card_roots hp).trans hcard

Depends on / 依赖: Finset, Finset.val_le_iff_val_subset.mpr, Multiset, Multiset.eq_of_le_of_card_le, card_roots, eq_of_le_of_card_le, mem_roots, p.card_roots, p.mem_roots, val_le_iff_val_subset
-/
theorem roots_eq_of_degree_le_card_of_ne_zero {S : Finset R}
    (hS : forall x in S, p.eval x = 0) (hcard : p.degree <= S.card) (hp : p != 0) : p.roots = S.val := by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx => (p.mem_roots hp).mpr (hS x hx)))
  · simpa using (p.card_roots hp).trans hcard

/--
theorem `roots_eq_of_degree_eq_card` / 定理 `roots_eq_of_degree_eq_card`

English:
theorem roots_eq_of_degree_eq_card
  statement: {S : Finset R}
  proof: roots_eq_of_degree_le_card_of_ne_zero hS (by grind) (by contrapose! hcard; simp [hcard])

中文:
定理 roots_eq_of_degree_eq_card
  结论: {S : 有限集 R}
  证明: roots_eq_of_degree_le_card_of_ne_zero hS (by grind) (by contrapose! hcard; simp [hcard])

Depends on / 依赖: contrapose, roots_eq_of_degree_le_card_of_ne_zero
-/
theorem roots_eq_of_degree_eq_card {S : Finset R}
    (hS : forall x in S, p.eval x = 0) (hcard : S.card = p.degree) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (by grind) (by contrapose! hcard; simp [hcard])

/--
theorem `roots_eq_of_natDegree_le_card_of_ne_zero` / 定理 `roots_eq_of_natDegree_le_card_of_ne_zero`

English:
theorem roots_eq_of_natDegree_le_card_of_ne_zero
  statement: {S : Finset R}
  proof: roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

中文:
定理 roots_eq_of_natDegree_le_card_of_ne_zero
  结论: {S : 有限集 R}
  证明: roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

Depends on / 依赖: degree_le_of_natDegree_le, roots_eq_of_degree_le_card_of_ne_zero
-/
theorem roots_eq_of_natDegree_le_card_of_ne_zero {S : Finset R}
    (hS : forall x in S, p.eval x = 0) (hcard : p.natDegree <= S.card) (hp : p != 0) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

section NthRoots

/--
Definition of `nthRoots` / `nthRoots` 的定义

English:
definition nthRoots
  signature: (n : Nat) (a : R)
  body: roots ((X : R[X]) ^ n - C a)

@[simp]

中文:
定义 nthRoots
  签名: (n : 自然数) (a : R)
  定义体: roots ((X : R[X]) ^ n - C a)

@[simp]
-/
def nthRoots (n : Nat) (a : R) : Multiset R :=
  roots ((X : R[X]) ^ n - C a)

@[simp]
/--
theorem `mem_nthRoots` / 定理 `mem_nthRoots`

English:
theorem mem_nthRoots
  given: {n : Nat} (hn : 0 < n) {a x : R}
  statement: x in nthRoots n a ↔ x ^ n = a
  proof: by
  rw [nthRoots]; rw [mem_roots (X_pow_sub_C_ne_zero hn a)]; rw [IsRoot.def]; rw [eval_sub]; rw [eval_C]; rw [eval_pow]; rw [eval_X]; rw [sub_eq_zero]

@[simp]

中文:
定理 mem_nthRoots
  条件: {n : 自然数} (hn : 0 < n) {a x : R}
  结论: x in nthRoots n a ↔ x ^ n = a
  证明: by
  rw [nthRoots]; rw [mem_roots (X_pow_sub_C_ne_zero hn a)]; rw [IsRoot.def]; rw [eval_sub]; rw [eval_C]; rw [eval_pow]; rw [eval_X]; rw [sub_eq_zero]

@[simp]

Depends on / 依赖: IsRoot, IsRoot.def, X_pow_sub_C_ne_zero, eval_C, eval_X, eval_pow, eval_sub, mem_roots, nthRoots, sub_eq_zero
-/
theorem mem_nthRoots {n : Nat} (hn : 0 < n) {a x : R} : x in nthRoots n a ↔ x ^ n = a := by
  rw [nthRoots]; rw [mem_roots (X_pow_sub_C_ne_zero hn a)]; rw [IsRoot.def]; rw [eval_sub]; rw [eval_C]; rw [eval_pow]; rw [eval_X]; rw [sub_eq_zero]

@[simp]
/--
theorem `nthRoots_zero` / 定理 `nthRoots_zero`

English:
theorem nthRoots_zero
  given: (r : R)
  statement: nthRoots 0 r = 0
  proof: by
  simp only [pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]

@[simp]

中文:
定理 nthRoots_zero
  条件: (r : R)
  结论: nthRoots 0 r = 0
  证明: by
  simp only [pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]

@[simp]

Depends on / 依赖: C_sub, nthRoots, pow_zero, roots_C
-/
theorem nthRoots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]

@[simp]
/--
theorem `nthRoots_zero_right` / 定理 `nthRoots_zero_right`

English:
theorem nthRoots_zero_right
  given: {R} [CommRing R] [IsDomain R] (n : Nat)
  proof: by
  rw [nthRoots]; rw [C.map_zero]; rw [sub_zero]; rw [roots_pow]; rw [roots_X]; rw [Multiset.nsmul_singleton]

中文:
定理 nthRoots_zero_right
  条件: {R} [交换环 R] [是整环 R] (n : 自然数)
  证明: by
  rw [nthRoots]; rw [C.map_zero]; rw [sub_zero]; rw [roots_pow]; rw [roots_X]; rw [Multiset.nsmul_singleton]

Depends on / 依赖: C.map_zero, Multiset, Multiset.nsmul_singleton, map_zero, nsmul_singleton, nthRoots, roots_X, roots_pow, sub_zero
-/
theorem nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : Nat) :
    nthRoots n (0 : R) = Multiset.replicate n 0 := by
  rw [nthRoots]; rw [C.map_zero]; rw [sub_zero]; rw [roots_pow]; rw [roots_X]; rw [Multiset.nsmul_singleton]

/--
theorem `card_nthRoots` / 定理 `card_nthRoots`

English:
theorem card_nthRoots
  given: (n : Nat) (a : R)
  statement: Multiset.card (nthRoots n a) <= n
  proof: by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [nthRoots, roots, h, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn]; rw [pow_zero]; rw [← C_1]; rw [← map_sub]


中文:
定理 card_nthRoots
  条件: (n : 自然数) (a : R)
  结论: Multiset.card (nthRoots n a) <= n
  证明: by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [nthRoots, roots, h, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn]; rw [pow_zero]; rw [← C_1]; rw [← map_sub]


Depends on / 依赖: Multiset, Multiset.card_zero, Nat.cast_le, Nat.pos_of_ne_zero, WithBot, WithBot.coe_le_coe, X_pow_sub_C_ne_zero, card_roots, card_zero, cast_le, classical, coe_le_coe, degree_C_le, degree_X_pow_sub_C, empty_eq_zero, le_trans, map_sub, nthRoots, pos_of_ne_zero, pow_zero
-/
theorem card_nthRoots (n : Nat) (a : R) : Multiset.card (nthRoots n a) <= n := by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [nthRoots, roots, h, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn]; rw [pow_zero]; rw [← C_1]; rw [← map_sub]
            exact degree_C_le))
  else by
    rw [← Nat.cast_le (α := WithBot Nat)]
    rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
    exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))

@[simp]
/--
theorem `nthRoots_two_eq_zero_iff` / 定理 `nthRoots_two_eq_zero_iff`

English:
theorem nthRoots_two_eq_zero_iff
  given: {r : R}
  statement: nthRoots 2 r = 0 ↔ ¬IsSquare r
  proof: by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

中文:
定理 nthRoots_two_eq_zero_iff
  条件: {r : R}
  结论: nthRoots 2 r = 0 ↔ ¬IsSquare r
  证明: by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

Depends on / 依赖: eq_comm, eq_zero_iff_forall_notMem, isSquare_iff_exists_sq, mem_nthRoots, not_exists, simp_rw
-/
theorem nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

/--
Definition of `nthRootsFinset` / `nthRootsFinset` 的定义

English:
definition nthRootsFinset
  signature: (n : Nat) {R : Type*} (a : R) [CommRing R] [IsDomain R]
  body: haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n a)

中文:
定义 nthRootsFinset
  签名: (n : 自然数) {R : 类型} (a : R) [交换环 R] [是整环 R]
  定义体: haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n a)

Depends on / 依赖: Classical, Classical.decEq, Multiset, Multiset.toFinset, NonUnitalNonAssocSemiring, StarRing, StarRing.toStarAddMonoid, nthRoots, toFinset, toStarAddMonoid
-/
def nthRootsFinset (n : Nat) {R : Type*} (a : R) [CommRing R] [IsDomain R] : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n a)

/--
lemma `nthRootsFinset_def` / 引理 `nthRootsFinset_def`

English:
lemma nthRootsFinset_def
  given: (n : Nat) {R : Type*} (a : R) [CommRing R] [IsDomain R] [DecidableEq R]
  proof: by
  unfold nthRootsFinset
  convert! rfl

@[simp]

中文:
引理 nthRootsFinset_def
  条件: (n : 自然数) {R : 类型} (a : R) [交换环 R] [是整环 R] [DecidableEq R]
  证明: by
  unfold nthRootsFinset
  convert! rfl

@[simp]

Depends on / 依赖: convert, nthRootsFinset
-/
lemma nthRootsFinset_def (n : Nat) {R : Type*} (a : R) [CommRing R] [IsDomain R] [DecidableEq R] :
    nthRootsFinset n a = Multiset.toFinset (nthRoots n a) := by
  unfold nthRootsFinset
  convert! rfl

@[simp]
/--
theorem `mem_nthRootsFinset` / 定理 `mem_nthRootsFinset`

English:
theorem mem_nthRootsFinset
  given: {n : Nat} (h : 0 < n) (a : R) {x : R}
  proof: by
  classical
  rw [nthRootsFinset_def]; rw [mem_toFinset]; rw [mem_nthRoots h]

@[simp]

中文:
定理 mem_nthRootsFinset
  条件: {n : 自然数} (h : 0 < n) (a : R) {x : R}
  证明: by
  classical
  rw [nthRootsFinset_def]; rw [mem_toFinset]; rw [mem_nthRoots h]

@[simp]

Depends on / 依赖: classical, mem_nthRoots, mem_toFinset, nthRootsFinset_def
-/
theorem mem_nthRootsFinset {n : Nat} (h : 0 < n) (a : R) {x : R} :
    x in nthRootsFinset n a ↔ x ^ (n : Nat) = a := by
  classical
  rw [nthRootsFinset_def]; rw [mem_toFinset]; rw [mem_nthRoots h]

@[simp]
/--
theorem `nthRootsFinset_zero` / 定理 `nthRootsFinset_zero`

English:
theorem nthRootsFinset_zero
  given: (a : R)
  statement: nthRootsFinset 0 a = ∅
  proof: by
  classical simp [nthRootsFinset_def]

中文:
定理 nthRootsFinset_zero
  条件: (a : R)
  结论: nthRootsFinset 0 a = ∅
  证明: by
  classical simp [nthRootsFinset_def]

Depends on / 依赖: classical, nthRootsFinset_def
-/
theorem nthRootsFinset_zero (a : R) : nthRootsFinset 0 a = ∅ := by
  classical simp [nthRootsFinset_def]

/--
theorem `map_mem_nthRootsFinset` / 定理 `map_mem_nthRootsFinset`

English:
theorem map_mem_nthRootsFinset
  statement: {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
  proof: by
  by_cases hn : n = 0
  · simp [hn] at hx
  · rw [mem_nthRootsFinset <| Nat.pos_of_ne_zero hn, ← map_pow, (mem_nthRootsFinset
      (Nat.pos_of_ne_zero hn) a).1 hx]

中文:
定理 map_mem_nthRootsFinset
  结论: {S F : 类型} [交换环 S] [是整环 S] [函数状 F R S]
  证明: by
  by_cases hn : n = 0
  · simp [hn] at hx
  · rw [mem_nthRootsFinset <| Nat.pos_of_ne_zero hn, ← map_pow, (mem_nthRootsFinset
      (Nat.pos_of_ne_zero hn) a).1 hx]

Depends on / 依赖: Nat.pos_of_ne_zero, map_pow, mem_nthRootsFinset, pos_of_ne_zero
-/
theorem map_mem_nthRootsFinset {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [MonoidHomClass F R S] {a : R} {x : R} (hx : x in nthRootsFinset n a) (f : F) :
    f x in nthRootsFinset n (f a) := by
  by_cases hn : n = 0
  · simp [hn] at hx
  · rw [mem_nthRootsFinset <| Nat.pos_of_ne_zero hn, ← map_pow, (mem_nthRootsFinset
      (Nat.pos_of_ne_zero hn) a).1 hx]

/--
theorem `map_mem_nthRootsFinset_one` / 定理 `map_mem_nthRootsFinset_one`

English:
theorem map_mem_nthRootsFinset_one
  statement: {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
  proof: by
  rw [← (map_one f)]
  exact map_mem_nthRootsFinset hx _

中文:
定理 map_mem_nthRootsFinset_one
  结论: {S F : 类型} [交换环 S] [是整环 S] [函数状 F R S]
  证明: by
  rw [← (map_one f)]
  exact map_mem_nthRootsFinset hx _

Depends on / 依赖: map_mem_nthRootsFinset, map_one
-/
theorem map_mem_nthRootsFinset_one {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [RingHomClass F R S] {x : R} (hx : x in nthRootsFinset n 1) (f : F) :
    f x in nthRootsFinset n 1 := by
  rw [← (map_one f)]
  exact map_mem_nthRootsFinset hx _

/--
theorem `mul_mem_nthRootsFinset` / 定理 `mul_mem_nthRootsFinset`

English:
theorem mul_mem_nthRootsFinset
  proof: by
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη₁
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow]; rw [hη₁]; rw [hη₂]

中文:
定理 mul_mem_nthRootsFinset
  证明: by
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη₁
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow]; rw [hη₁]; rw [hη₂]

Depends on / 依赖: mem_nthRootsFinset, mul_pow, n.succ_pos, notMem_empty, nthRootsFinset_zero, succ_pos
-/
theorem mul_mem_nthRootsFinset
    {η₁ η₂ : R} {a₁ a₂ : R} (hη₁ : η₁ in nthRootsFinset n a₁) (hη₂ : η₂ in nthRootsFinset n a₂) :
    η₁ * η₂ in nthRootsFinset n (a₁ * a₂) := by
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη₁
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow]; rw [hη₁]; rw [hη₂]

/--
theorem `ne_zero_of_mem_nthRootsFinset` / 定理 `ne_zero_of_mem_nthRootsFinset`

English:
theorem ne_zero_of_mem_nthRootsFinset
  given: {η : R} {a : R} (ha : a != 0) (hη : η in nthRootsFinset n a)
  proof: by
  rintro rfl
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos]; rw [zero_pow n.succ_ne_zero] at hη
    exact ha hη.symm

中文:
定理 ne_zero_of_mem_nthRootsFinset
  条件: {η : R} {a : R} (ha : a != 0) (hη : η in nthRootsFinset n a)
  证明: by
  rintro rfl
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos]; rw [zero_pow n.succ_ne_zero] at hη
    exact ha hη.symm

Depends on / 依赖: mem_nthRootsFinset, n.succ_ne_zero, n.succ_pos, notMem_empty, nthRootsFinset_zero, succ_ne_zero, succ_pos, zero_pow
-/
theorem ne_zero_of_mem_nthRootsFinset {η : R} {a : R} (ha : a != 0) (hη : η in nthRootsFinset n a) :
    η != 0 := by
  rintro rfl
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos]; rw [zero_pow n.succ_ne_zero] at hη
    exact ha hη.symm

/--
theorem `one_mem_nthRootsFinset` / 定理 `one_mem_nthRootsFinset`

English:
theorem one_mem_nthRootsFinset
  given: (hn : 0 < n)
  statement: 1 in nthRootsFinset n (1 : R)
  proof: by
  rw [mem_nthRootsFinset hn]; rw [one_pow]

中文:
定理 one_mem_nthRootsFinset
  条件: (hn : 0 < n)
  结论: 1 in nthRootsFinset n (1 : R)
  证明: by
  rw [mem_nthRootsFinset hn]; rw [one_pow]

Depends on / 依赖: mem_nthRootsFinset, one_pow
-/
theorem one_mem_nthRootsFinset (hn : 0 < n) : 1 in nthRootsFinset n (1 : R) := by
  rw [mem_nthRootsFinset hn]; rw [one_pow]

/--
lemma `nthRoots_two_one` / 引理 `nthRoots_two_one`

English:
lemma nthRoots_two_one
  statement: Polynomial.nthRoots 2 (1 : R) = {-1,1}
  proof: by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X ^ 2 - C 1 : R[X]) != 0 := fun h => by simpa using congrArg (coeff · 0) h
  rw [nthRoots]; rw [h₁]; rw [roots_mul (h₁ ▸ h₂)]; rw [roots_X_add_C]; rw [roots_X_sub_C]; rfl

中文:
引理 nthRoots_two_one
  结论: 多项式.nthRoots 2 (1 : R) = {-1,1}
  证明: by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X ^ 2 - C 1 : R[X]) != 0 := fun h => by simpa using congrArg (coeff · 0) h
  rw [nthRoots]; rw [h₁]; rw [roots_mul (h₁ ▸ h₂)]; rw [roots_X_add_C]; rw [roots_X_sub_C]; rfl

Depends on / 依赖: nthRoots, roots_X_add_C, roots_X_sub_C, roots_mul, sq_sub_sq
-/
lemma nthRoots_two_one : Polynomial.nthRoots 2 (1 : R) = {-1,1} := by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X ^ 2 - C 1 : R[X]) != 0 := fun h => by simpa using congrArg (coeff · 0) h
  rw [nthRoots]; rw [h₁]; rw [roots_mul (h₁ ▸ h₂)]; rw [roots_X_add_C]; rw [roots_X_sub_C]; rfl

end NthRoots

/--
theorem `zero_of_eval_zero` / 定理 `zero_of_eval_zero`

English:
theorem zero_of_eval_zero
  given: [Infinite R] (p : R[X]) (h : forall x, p.eval x = 0)
  statement: p = 0
  proof: by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩

中文:
定理 zero_of_eval_zero
  条件: [无限 R] (p : R[X]) (h : 对任意 x, p.eval x = 0)
  结论: p = 0
  证明: by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩

Depends on / 依赖: Fintype, Fintype.false, Multiset, Multiset.mem_toFinset.mpr, classical, mem_roots, mem_toFinset, p.roots.toFinset, toFinset
-/
theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : forall x, p.eval x = 0) : p = 0 := by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩

/--
theorem `funext` / 定理 `funext`

English:
theorem funext
  given: [Infinite R] {p q : R[X]} (ext : forall r : R, p.eval r = q.eval r)
  statement: p = q
  proof: by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub]; rw [sub_eq_zero]; rw [ext]

中文:
定理 funext
  条件: [无限 R] {p q : R[X]} (ext : 对任意 r : R, p.eval r = q.eval r)
  结论: p = q
  证明: by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub]; rw [sub_eq_zero]; rw [ext]

Depends on / 依赖: eval_sub, sub_eq_zero, zero_of_eval_zero
-/
theorem funext [Infinite R] {p q : R[X]} (ext : forall r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub]; rw [sub_eq_zero]; rw [ext]

variable [CommRing T]

/--
Definition of `aroots` / `aroots` 的定义

English:
abbreviation aroots
  signature: (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
  body: (p.map (algebraMap T S)).roots

中文:
缩写 aroots
  签名: (p : T[X]) (S) [交换环 S] [是整环 S] [代数 T S]
  定义体: (p.map (algebraMap T S)).roots

Depends on / 依赖: algebraMap, p.map
-/
noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S :=
  (p.map (algebraMap T S)).roots

/--
theorem `aroots_def` / 定理 `aroots_def`

English:
theorem aroots_def
  given: (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
  proof: rfl

中文:
定理 aroots_def
  条件: (p : T[X]) (S) [交换环 S] [是整环 S] [代数 T S]
  证明: rfl
-/
theorem aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.aroots S = (p.map (algebraMap T S)).roots :=
  rfl

/--
theorem `mem_aroots'` / 定理 `mem_aroots'`

English:
theorem mem_aroots'
  given: [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S}
  proof: by
  rw [mem_roots']; rw [IsRoot.def]; rw [← eval₂_eq_eval_map]; rw [aeval_def]

中文:
定理 mem_aroots'
  条件: [交换环 S] [是整环 S] [代数 T S] {p : T[X]} {a : S}
  证明: by
  rw [mem_roots']; rw [IsRoot.def]; rw [← eval₂_eq_eval_map]; rw [aeval_def]

Depends on / 依赖: IsRoot, IsRoot.def, aeval_def, mem_roots
-/
theorem mem_aroots' [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S} :
    a in p.aroots S ↔ p.map (algebraMap T S) != 0 ∧ aeval a p = 0 := by
  rw [mem_roots']; rw [IsRoot.def]; rw [← eval₂_eq_eval_map]; rw [aeval_def]

/--
theorem `mem_aroots` / 定理 `mem_aroots`

English:
theorem mem_aroots
  statement: [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [mem_aroots']; rw [Polynomial.map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

中文:
定理 mem_aroots
  结论: [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [mem_aroots']; rw [Polynomial.map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_ne_zero_iff, algebraMap_injective, map_ne_zero_iff, mem_aroots
-/
theorem mem_aroots [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔ p != 0 ∧ aeval a p = 0 := by
  rw [mem_aroots']; rw [Polynomial.map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

/--
theorem `aroots_mul` / 定理 `aroots_mul`

English:
theorem aroots_mul
  statement: [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  suffices map (algebraMap T S) p * map (algebraMap T S) q != 0 by
    rw [aroots_def]; rw [Polynomial.map_mul]; rw [roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective T S)]

@[simp]

中文:
定理 aroots_mul
  结论: [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  suffices map (algebraMap T S) p * map (algebraMap T S) q != 0 by
    rw [aroots_def]; rw [Polynomial.map_mul]; rw [roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective T S)]

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_mul, Polynomial.map_ne_zero_iff, algebraMap, algebraMap_injective, aroots_def, map_mul, map_ne_zero_iff, roots_mul
-/
theorem aroots_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q != 0) :
    (p * q).aroots S = p.aroots S + q.aroots S := by
  suffices map (algebraMap T S) p * map (algebraMap T S) q != 0 by
    rw [aroots_def]; rw [Polynomial.map_mul]; rw [roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective T S)]

@[simp]
/--
theorem `aroots_X_sub_C` / 定理 `aroots_X_sub_C`

English:
theorem aroots_X_sub_C
  statement: [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [aroots_def]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [roots_X_sub_C]

@[simp]

中文:
定理 aroots_X_sub_C
  结论: [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [aroots_def]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [roots_X_sub_C]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.map_sub, aroots_def, map_C, map_X, map_sub, roots_X_sub_C
-/
theorem aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S]
    (r : T) : aroots (X - C r) S = {algebraMap T S r} := by
  rw [aroots_def]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [roots_X_sub_C]

@[simp]
/--
theorem `aroots_X` / 定理 `aroots_X`

English:
theorem aroots_X
  given: [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [aroots_def]; rw [map_X]; rw [roots_X]

@[simp]

中文:
定理 aroots_X
  条件: [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [aroots_def]; rw [map_X]; rw [roots_X]

@[simp]

Depends on / 依赖: aroots_def, map_X, roots_X
-/
theorem aroots_X [CommRing S] [IsDomain S] [Algebra T S] :
    aroots (X : T[X]) S = {0} := by
  rw [aroots_def]; rw [map_X]; rw [roots_X]

@[simp]
/--
theorem `aroots_C` / 定理 `aroots_C`

English:
theorem aroots_C
  given: [CommRing S] [IsDomain S] [Algebra T S] (a : T)
  statement: (C a).aroots S = 0
  proof: by
  rw [aroots_def]; rw [map_C]; rw [roots_C]

@[simp]

中文:
定理 aroots_C
  条件: [交换环 S] [是整环 S] [代数 T S] (a : T)
  结论: (C a).aroots S = 0
  证明: by
  rw [aroots_def]; rw [map_C]; rw [roots_C]

@[simp]

Depends on / 依赖: aroots_def, map_C, roots_C
-/
theorem aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).aroots S = 0 := by
  rw [aroots_def]; rw [map_C]; rw [roots_C]

@[simp]
/--
theorem `aroots_zero` / 定理 `aroots_zero`

English:
theorem aroots_zero
  given: (S) [CommRing S] [IsDomain S] [Algebra T S]
  statement: (0 : T[X]).aroots S = 0
  proof: by
  rw [← C_0]; rw [aroots_C]

@[simp]

中文:
定理 aroots_zero
  条件: (S) [交换环 S] [是整环 S] [代数 T S]
  结论: (0 : T[X]).aroots S = 0
  证明: by
  rw [← C_0]; rw [aroots_C]

@[simp]

Depends on / 依赖: aroots_C
-/
theorem aroots_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).aroots S = 0 := by
  rw [← C_0]; rw [aroots_C]

@[simp]
/--
theorem `aroots_one` / 定理 `aroots_one`

English:
theorem aroots_one
  given: [CommRing S] [IsDomain S] [Algebra T S]
  proof: aroots_C 1

@[simp]

中文:
定理 aroots_one
  条件: [交换环 S] [是整环 S] [代数 T S]
  证明: aroots_C 1

@[simp]

Depends on / 依赖: aroots_C
-/
theorem aroots_one [CommRing S] [IsDomain S] [Algebra T S] :
    (1 : T[X]).aroots S = 0 :=
  aroots_C 1

@[simp]
/--
theorem `aroots_neg` / 定理 `aroots_neg`

English:
theorem aroots_neg
  given: [CommRing S] [IsDomain S] [Algebra T S] (p : T[X])
  proof: by
  rw [aroots]; rw [Polynomial.map_neg]; rw [roots_neg]

@[simp]

中文:
定理 aroots_neg
  条件: [交换环 S] [是整环 S] [代数 T S] (p : T[X])
  证明: by
  rw [aroots]; rw [Polynomial.map_neg]; rw [roots_neg]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.map_neg, aroots, map_neg, roots_neg
-/
theorem aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) :
    (-p).aroots S = p.aroots S := by
  rw [aroots]; rw [Polynomial.map_neg]; rw [roots_neg]

@[simp]
/--
theorem `aroots_C_mul` / 定理 `aroots_C_mul`

English:
theorem aroots_C_mul
  statement: [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [aroots_def]; rw [Polynomial.map_mul]; rw [map_C]; rw [roots_C_mul]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

@[simp]

中文:
定理 aroots_C_mul
  结论: [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [aroots_def]; rw [Polynomial.map_mul]; rw [map_C]; rw [roots_C_mul]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_mul, algebraMap_injective, aroots_def, map_C, map_mul, map_ne_zero_iff, roots_C_mul
-/
theorem aroots_C_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) :
    (C a * p).aroots S = p.aroots S := by
  rw [aroots_def]; rw [Polynomial.map_mul]; rw [map_C]; rw [roots_C_mul]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

@[simp]
/--
theorem `aroots_smul_nonzero` / 定理 `aroots_smul_nonzero`

English:
theorem aroots_smul_nonzero
  statement: [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [smul_eq_C_mul]; rw [aroots_C_mul _ ha]

@[simp]

中文:
定理 aroots_smul_nonzero
  结论: [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [smul_eq_C_mul]; rw [aroots_C_mul _ ha]

@[simp]

Depends on / 依赖: aroots_C_mul, smul_eq_C_mul
-/
theorem aroots_smul_nonzero [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) :
    (a • p).aroots S = p.aroots S := by
  rw [smul_eq_C_mul]; rw [aroots_C_mul _ ha]

@[simp]
/--
theorem `aroots_pow` / 定理 `aroots_pow`

English:
theorem aroots_pow
  given: [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : Nat)
  proof: by
  rw [aroots_def]; rw [Polynomial.map_pow]; rw [roots_pow]

中文:
定理 aroots_pow
  条件: [交换环 S] [是整环 S] [代数 T S] (p : T[X]) (n : 自然数)
  证明: by
  rw [aroots_def]; rw [Polynomial.map_pow]; rw [roots_pow]

Depends on / 依赖: Polynomial, Polynomial.map_pow, aroots_def, map_pow, roots_pow
-/
theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : Nat) :
    (p ^ n).aroots S = n • p.aroots S := by
  rw [aroots_def]; rw [Polynomial.map_pow]; rw [roots_pow]

/--
theorem `aroots_X_pow` / 定理 `aroots_X_pow`

English:
theorem aroots_X_pow
  given: [CommRing S] [IsDomain S] [Algebra T S] (n : Nat)
  proof: by
  rw [aroots_pow]; rw [aroots_X]

中文:
定理 aroots_X_pow
  条件: [交换环 S] [是整环 S] [代数 T S] (n : 自然数)
  证明: by
  rw [aroots_pow]; rw [aroots_X]

Depends on / 依赖: aroots_X, aroots_pow
-/
theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : Nat) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_pow]; rw [aroots_X]

/--
theorem `aroots_C_mul_X_pow` / 定理 `aroots_C_mul_X_pow`

English:
theorem aroots_C_mul_X_pow
  statement: [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [aroots_C_mul _ ha]; rw [aroots_X_pow]

@[simp]

中文:
定理 aroots_C_mul_X_pow
  结论: [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [aroots_C_mul _ ha]; rw [aroots_X_pow]

@[simp]

Depends on / 依赖: aroots_C_mul, aroots_X_pow, star_smul
-/
theorem aroots_C_mul_X_pow [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a != 0) (n : Nat) :
    (C a * X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_C_mul _ ha]; rw [aroots_X_pow]

@[simp]
/--
theorem `aroots_monomial` / 定理 `aroots_monomial`

English:
theorem aroots_monomial
  statement: [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [aroots_C_mul_X_pow ha]

中文:
定理 aroots_monomial
  结论: [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [aroots_C_mul_X_pow ha]

Depends on / 依赖: C_mul_X_pow_eq_monomial, aroots_C_mul_X_pow
-/
theorem aroots_monomial [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a != 0) (n : Nat) :
    (monomial n a).aroots S = n • ({0} : Multiset S) := by
  rw [← C_mul_X_pow_eq_monomial]; rw [aroots_C_mul_X_pow ha]

variable (R S) in
@[simp]
/--
theorem `aroots_map` / 定理 `aroots_map`

English:
theorem aroots_map
  statement: (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T R]
  proof: by
  rw [aroots_def]; rw [aroots_def]; rw [map_map]; rw [IsScalarTower.algebraMap_eq T S R]

中文:
定理 aroots_map
  结论: (p : T[X]) [交换环 S] [代数 T S] [代数 S R] [代数 T R]
  证明: by
  rw [aroots_def]; rw [aroots_def]; rw [map_map]; rw [IsScalarTower.algebraMap_eq T S R]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, aroots_def, map_map
-/
theorem aroots_map (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T R]
    [IsScalarTower T S R] :
    (p.map (algebraMap T S)).aroots R = p.aroots R := by
  rw [aroots_def]; rw [aroots_def]; rw [map_map]; rw [IsScalarTower.algebraMap_eq T S R]

/--
Definition of `rootSet` / `rootSet` 的定义

English:
definition rootSet
  signature: (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
  body: haveI := Classical.decEq S
  (p.aroots S).toFinset

中文:
定义 rootSet
  签名: (p : T[X]) (S) [交换环 S] [是整环 S] [代数 T S]
  定义体: haveI := Classical.decEq S
  (p.aroots S).toFinset

Depends on / 依赖: Classical, Classical.decEq, aroots, p.aroots, toFinset
-/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset

/--
theorem `rootSet_def` / 定理 `rootSet_def`

English:
theorem rootSet_def
  given: (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S]
  proof: by
  rw [rootSet]
  convert! rfl

@[simp]

中文:
定理 rootSet_def
  条件: (p : T[X]) (S) [交换环 S] [是整环 S] [代数 T S] [DecidableEq S]
  证明: by
  rw [rootSet]
  convert! rfl

@[simp]

Depends on / 依赖: convert, rootSet
-/
theorem rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S] :
    p.rootSet S = (p.aroots S).toFinset := by
  rw [rootSet]
  convert! rfl

@[simp]
/--
theorem `rootSet_C` / 定理 `rootSet_C`

English:
theorem rootSet_C
  given: [CommRing S] [IsDomain S] [Algebra T S] (a : T)
  statement: (C a).rootSet S = ∅
  proof: by
  classical
  rw [rootSet_def]; rw [aroots_C]; rw [Multiset.toFinset_zero]; rw [Finset.coe_empty]

@[simp]

中文:
定理 rootSet_C
  条件: [交换环 S] [是整环 S] [代数 T S] (a : T)
  结论: (C a).rootSet S = ∅
  证明: by
  classical
  rw [rootSet_def]; rw [aroots_C]; rw [Multiset.toFinset_zero]; rw [Finset.coe_empty]

@[simp]

Depends on / 依赖: Finset, Finset.coe_empty, Multiset, Multiset.toFinset_zero, aroots_C, classical, coe_empty, rootSet_def, toFinset_zero
-/
theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet S = ∅ := by
  classical
  rw [rootSet_def]; rw [aroots_C]; rw [Multiset.toFinset_zero]; rw [Finset.coe_empty]

@[simp]
/--
theorem `rootSet_zero` / 定理 `rootSet_zero`

English:
theorem rootSet_zero
  given: (S) [CommRing S] [IsDomain S] [Algebra T S]
  statement: (0 : T[X]).rootSet S = ∅
  proof: by
  rw [← C_0]; rw [rootSet_C]

@[simp]

中文:
定理 rootSet_zero
  条件: (S) [交换环 S] [是整环 S] [代数 T S]
  结论: (0 : T[X]).rootSet S = ∅
  证明: by
  rw [← C_0]; rw [rootSet_C]

@[simp]

Depends on / 依赖: rootSet_C
-/
theorem rootSet_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).rootSet S = ∅ := by
  rw [← C_0]; rw [rootSet_C]

@[simp]
/--
theorem `rootSet_one` / 定理 `rootSet_one`

English:
theorem rootSet_one
  given: (S) [CommRing S] [IsDomain S] [Algebra T S]
  statement: (1 : T[X]).rootSet S = ∅
  proof: by
  rw [← C_1]; rw [rootSet_C]

@[simp]

中文:
定理 rootSet_one
  条件: (S) [交换环 S] [是整环 S] [代数 T S]
  结论: (1 : T[X]).rootSet S = ∅
  证明: by
  rw [← C_1]; rw [rootSet_C]

@[simp]

Depends on / 依赖: rootSet_C
-/
theorem rootSet_one (S) [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).rootSet S = ∅ := by
  rw [← C_1]; rw [rootSet_C]

@[simp]
/--
theorem `rootSet_neg` / 定理 `rootSet_neg`

English:
theorem rootSet_neg
  given: (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [rootSet]; rw [aroots_neg]; rw [rootSet]

中文:
定理 rootSet_neg
  条件: (p : T[X]) (S) [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [rootSet]; rw [aroots_neg]; rw [rootSet]

Depends on / 依赖: aroots_neg, rootSet
-/
theorem rootSet_neg (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    (-p).rootSet S = p.rootSet S := by
  rw [rootSet]; rw [aroots_neg]; rw [rootSet]

/--
Instance `rootSetFintype` / 实例 `rootSetFintype`

English:
instance rootSetFintype
  signature: (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S]
  body: FinsetCoe.fintype _

中文:
实例 rootSetFintype
  签名: (p : T[X]) (S : 类型) [交换环 S] [是整环 S] [代数 T S]
  定义体: FinsetCoe.fintype _

Depends on / 依赖: FinsetCoe, FinsetCoe.fintype, fintype
-/
instance rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    Fintype (p.rootSet S) :=
  FinsetCoe.fintype _

/--
theorem `rootSet_finite` / 定理 `rootSet_finite`

English:
theorem rootSet_finite
  given: (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S]
  proof: Set.toFinite _

中文:
定理 rootSet_finite
  条件: (p : T[X]) (S : 类型) [交换环 S] [是整环 S] [代数 T S]
  证明: Set.toFinite _

Depends on / 依赖: Set.toFinite, toFinite
-/
theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite :=
  Set.toFinite _

/--
theorem `bUnion_roots_finite` / 定理 `bUnion_roots_finite`

English:
theorem bUnion_roots_finite
  statement: {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
  proof: Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] -> Fin (d + 1) -> R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (

中文:
定理 bUnion_roots_finite
  结论: {R S : 类型} [半环 R] [交换环 S] [是整环 S] [DecidableEq S]
  证明: Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] -> Fin (d + 1) -> R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (

Depends on / 依赖: Finite, Set.Finite.biUnion, biUnion
-/
theorem bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
    (m : R ->+* S) (d : Nat) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (_ : f.natDegree <= d ∧ forall i, f.coeff i in U),
        ((f.map m).roots.toFinset : Set S)).Finite :=
  Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] -> Fin (d + 1) -> R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (?_ : Set.InjOn π _)
      · exact Set.image_subset_iff.2 fun f hf i _ => hf.2 i
      · refine fun x hx y hy hxy => (ext_iff_natDegree_le hx.1 hy.1).2 fun i hi => ?_
        exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩)
    fun _ _ => Finset.finite_toSet _

/--
theorem `mem_rootSet'` / 定理 `mem_rootSet'`

English:
theorem mem_rootSet'
  given: {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
  proof: by
  classical
  rw [rootSet_def]; rw [Finset.mem_coe]; rw [mem_toFinset]; rw [mem_aroots']

中文:
定理 mem_rootSet'
  条件: {p : T[X]} {S : 类型} [交换环 S] [是整环 S] [代数 T S] {a : S}
  证明: by
  classical
  rw [rootSet_def]; rw [Finset.mem_coe]; rw [mem_toFinset]; rw [mem_aroots']

Depends on / 依赖: Finset, Finset.mem_coe, classical, mem_aroots, mem_coe, mem_toFinset, rootSet_def
-/
theorem mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a in p.rootSet S ↔ p.map (algebraMap T S) != 0 ∧ aeval a p = 0 := by
  classical
  rw [rootSet_def]; rw [Finset.mem_coe]; rw [mem_toFinset]; rw [mem_aroots']

/--
theorem `mem_rootSet` / 定理 `mem_rootSet`

English:
theorem mem_rootSet
  statement: {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [mem_rootSet']; rw [Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective T S)]

中文:
定理 mem_rootSet
  结论: {p : T[X]} {S : 类型} [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [mem_rootSet']; rw [Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective T S)]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_ne_zero_iff, algebraMap_injective, map_ne_zero_iff, mem_rootSet
-/
theorem mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : S} : a in p.rootSet S ↔ p != 0 ∧ aeval a p = 0 := by
  rw [mem_rootSet']; rw [Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective T S)]

/--
lemma `mem_rootSet_of_ne` / 引理 `mem_rootSet_of_ne`

English:
lemma mem_rootSet_of_ne
  statement: {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: mem_rootSet.trans and_iff_right hp

中文:
引理 mem_rootSet_of_ne
  结论: {p : T[X]} {S : 类型} [是整环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: mem_rootSet.trans and_iff_right hp

Depends on / 依赖: and_iff_right, mem_rootSet, mem_rootSet.trans, star_smul, unop_injective, x.unop
-/
lemma mem_rootSet_of_ne {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] (hp : p != 0) {a : S} : a in p.rootSet S ↔ aeval a p = 0 :=
mem_rootSet.trans and_iff_right hp

/--
theorem `preimage_eval_singleton` / 定理 `preimage_eval_singleton`

English:
theorem preimage_eval_singleton
  given: (hp : p != C a)
  statement: p.eval ⁻¹' {a} = (p - C a).rootSet R
  proof: by
  ext; simp [mem_rootSet_of_ne (sub_ne_zero.mpr hp), sub_eq_zero]

中文:
定理 preimage_eval_singleton
  条件: (hp : p != C a)
  结论: p.eval ⁻¹' {a} = (p - C a).rootSet R
  证明: by
  ext; simp [mem_rootSet_of_ne (sub_ne_zero.mpr hp), sub_eq_zero]

Depends on / 依赖: mem_rootSet_of_ne, sub_eq_zero, sub_ne_zero, sub_ne_zero.mpr
-/
theorem preimage_eval_singleton (hp : p != C a) : p.eval ⁻¹' {a} = (p - C a).rootSet R := by
  ext; simp [mem_rootSet_of_ne (sub_ne_zero.mpr hp), sub_eq_zero]

/--
theorem `Monic.mem_rootSet` / 定理 `Monic.mem_rootSet`

English:
theorem Monic.mem_rootSet
  statement: {p : T[X]} (hp : Monic p) {S : Type*} [CommRing S] [IsDomain S]
  proof: by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

中文:
定理 Monic.mem_rootSet
  结论: {p : T[X]} (hp : Monic p) {S : 类型} [交换环 S] [是整环 S]
  证明: by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

Depends on / 依赖: Polynomial, Polynomial.mem_rootSet, algebraMap, hp.map, mem_rootSet, ne_zero
-/
theorem Monic.mem_rootSet {p : T[X]} (hp : Monic p) {S : Type*} [CommRing S] [IsDomain S]
    [Algebra T S] {a : S} : a in p.rootSet S ↔ aeval a p = 0 := by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

/--
theorem `rootSet_maps_to'` / 定理 `rootSet_maps_to'`

English:
theorem rootSet_maps_to'
  statement: {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
  proof: fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  rw [aeval_algHom]; rw [AlgHom.comp_apply]; rw [hx.2]; rw [_root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩

中文:
定理 rootSet_maps_to'
  结论: {p : T[X]} {S S'} [交换环 S] [是整环 S] [代数 T S] [交换环 S']
  证明: fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  rw [aeval_algHom]; rw [AlgHom.comp_apply]; rw [hx.2]; rw [_root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩

Depends on / 依赖: AlgHom, AlgHom.comp_apply, _root_, _root_.map_zero, aeval_algHom, comp_apply, map_zero, mem_rootSet
-/
theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 -> p.map (algebraMap T S) = 0)
    (f : S ->ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  rw [aeval_algHom]; rw [AlgHom.comp_apply]; rw [hx.2]; rw [_root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩

/--
theorem `ne_zero_of_mem_rootSet` / 定理 `ne_zero_of_mem_rootSet`

English:
theorem ne_zero_of_mem_rootSet
  statement: {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
  proof: fun hf => by rwa [hf, rootSet_zero] at h

中文:
定理 ne_zero_of_mem_rootSet
  结论: {p : T[X]} [交换环 S] [是整环 S] [代数 T S] {a : S}
  证明: fun hf => by rwa [hf, rootSet_zero] at h

Depends on / 依赖: rootSet_zero
-/
theorem ne_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (h : a in p.rootSet S) : p != 0 := fun hf => by rwa [hf, rootSet_zero] at h

/--
theorem `aeval_eq_zero_of_mem_rootSet` / 定理 `aeval_eq_zero_of_mem_rootSet`

English:
theorem aeval_eq_zero_of_mem_rootSet
  statement: {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
  proof: (mem_rootSet'.1 hx).2

中文:
定理 aeval_eq_zero_of_mem_rootSet
  结论: {p : T[X]} [交换环 S] [是整环 S] [代数 T S] {a : S}
  证明: (mem_rootSet'.1 hx).2

Depends on / 依赖: mem_rootSet
-/
theorem aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (hx : a in p.rootSet S) : aeval a p = 0 :=
  (mem_rootSet'.1 hx).2

/--
lemma `rootSet_mapsTo` / 引理 `rootSet_mapsTo`

English:
lemma rootSet_mapsTo
  statement: {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  refine rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (FaithfulSMul.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _

中文:
引理 rootSet_mapsTo
  结论: {p : T[X]} [是整环 T] {S S' : 类型} [交换环 S] [是整环 S] [代数 T S]
  证明: by
  refine rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (FaithfulSMul.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_zero, algebraMap_injective, map_injective, map_zero, rootSet_maps_to
-/
lemma rootSet_mapsTo {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [CommRing S'] [IsDomain S'] [Algebra T S'] [Module.IsTorsionFree T S'] (f : S ->ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') := by
  refine rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (FaithfulSMul.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _

/--
theorem `mem_rootSet_of_injective` / 定理 `mem_rootSet_of_injective`

English:
theorem mem_rootSet_of_injective
  statement: [CommRing S] {p : S[X]} [Algebra S R]
  proof: by
  classical
  exact Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)

@[simp]

中文:
定理 mem_rootSet_of_injective
  结论: [交换环 S] {p : S[X]} [代数 S R]
  证明: by
  classical
  exact Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_toFinset.trans, classical, mem_roots_map_of_injective, mem_toFinset
-/
theorem mem_rootSet_of_injective [CommRing S] {p : S[X]} [Algebra S R]
    (h : Function.Injective (algebraMap S R)) {x : R} (hp : p != 0) :
    x in p.rootSet R ↔ aeval x p = 0 := by
  classical
  exact Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)

@[simp]
/--
theorem `nthRootsFinset_toSet` / 定理 `nthRootsFinset_toSet`

English:
theorem nthRootsFinset_toSet
  given: {n : Nat} (h : 0 < n) (a : R)
  proof: by
  ext x
  simp_all

中文:
定理 nthRootsFinset_toSet
  条件: {n : 自然数} (h : 0 < n) (a : R)
  证明: by
  ext x
  simp_all
-/
theorem nthRootsFinset_toSet {n : Nat} (h : 0 < n) (a : R) :
    nthRootsFinset n a = {r | r ^ n = a} := by
  ext x
  simp_all

/--
theorem `smul_mem_rootSet` / 定理 `smul_mem_rootSet`

English:
theorem smul_mem_rootSet
  statement: [CommRing S] [Algebra S R] {G : Type*}
  proof: by
  simp [mem_rootSet', aeval_smul, aeval_eq_zero_of_mem_rootSet hx, (mem_rootSet'.mp hx).1]

中文:
定理 smul_mem_rootSet
  结论: [交换环 S] [代数 S R] {G : 类型}
  证明: by
  simp [mem_rootSet', aeval_smul, aeval_eq_zero_of_mem_rootSet hx, (mem_rootSet'.mp hx).1]

Depends on / 依赖: aeval_eq_zero_of_mem_rootSet, aeval_smul, mem_rootSet
-/
theorem smul_mem_rootSet [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    (g : G) {x : R} (hx : x in f.rootSet R) : g • x in f.rootSet R := by
  simp [mem_rootSet', aeval_smul, aeval_eq_zero_of_mem_rootSet hx, (mem_rootSet'.mp hx).1]

/--
theorem `smul_mem_rootSet_iff_of_isUnit` / 定理 `smul_mem_rootSet_iff_of_isUnit`

English:
theorem smul_mem_rootSet_iff_of_isUnit
  statement: [CommRing S] [Algebra S R] {G : Type*}
  proof: by
  refine ⟨?_, smul_mem_rootSet g⟩
  obtain ⟨g, rfl⟩ := hg
  exact fun hx => inv_smul_smul g x ▸ smul_mem_rootSet _ hx

中文:
定理 smul_mem_rootSet_iff_of_isUnit
  结论: [交换环 S] [代数 S R] {G : 类型}
  证明: by
  refine ⟨?_, smul_mem_rootSet g⟩
  obtain ⟨g, rfl⟩ := hg
  exact fun hx => inv_smul_smul g x ▸ smul_mem_rootSet _ hx

Depends on / 依赖: inv_smul_smul, smul_mem_rootSet
-/
theorem smul_mem_rootSet_iff_of_isUnit [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {g : G} (hg : IsUnit g) {x : R} : g • x in f.rootSet R ↔ x in f.rootSet R := by
  refine ⟨?_, smul_mem_rootSet g⟩
  obtain ⟨g, rfl⟩ := hg
  exact fun hx => inv_smul_smul g x ▸ smul_mem_rootSet _ hx

/--
theorem `smul_mem_rootSet_iff` / 定理 `smul_mem_rootSet_iff`

English:
theorem smul_mem_rootSet_iff
  statement: [CommRing S] [Algebra S R] {G : Type*}
  proof: smul_mem_rootSet_iff_of_isUnit (Group.isUnit g)

中文:
定理 smul_mem_rootSet_iff
  结论: [交换环 S] [代数 S R] {G : 类型}
  证明: smul_mem_rootSet_iff_of_isUnit (Group.isUnit g)

Depends on / 依赖: Group.isUnit, isUnit, smul_mem_rootSet_iff_of_isUnit
-/
theorem smul_mem_rootSet_iff [CommRing S] [Algebra S R] {G : Type*}
    [Group G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {g : G} {x : R} : g • x in f.rootSet R ↔ x in f.rootSet R :=
  smul_mem_rootSet_iff_of_isUnit (Group.isUnit g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: S] [Algebra S R] (G
  body: ⟨g • x.1, smul_mem_rootSet g x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp]

中文:
实例 [交换环
  签名: S] [代数 S R] (G
  定义体: ⟨g • x.1, smul_mem_rootSet g x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp]

Depends on / 依赖: smul_mem_rootSet
-/
instance [CommRing S] [Algebra S R] (G : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] (f : S[X]) :
    MulAction G (f.rootSet R) where
  smul g x := ⟨g • x.1, smul_mem_rootSet g x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp]
/--
theorem `rootSet.coe_smul` / 定理 `rootSet.coe_smul`

English:
theorem rootSet.coe_smul
  statement: [CommRing S] [Algebra S R] {G : Type*}
  proof: rfl

中文:
定理 rootSet.coe_smul
  结论: [交换环 S] [代数 S R] {G : 类型}
  证明: rfl
-/
theorem rootSet.coe_smul [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    (g : G) (x : f.rootSet R) : (g • x : f.rootSet R) = g • (x : R) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: S] [Algebra S R] (G H
  body: Subtype.ext smul_comm _ _ _

中文:
实例 [交换环
  签名: S] [代数 S R] (G H
  定义体: Subtype.ext smul_comm _ _ _

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance [CommRing S] [Algebra S R] (G H : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R]
    [Monoid H] [MulSemiringAction H R] [SMulCommClass H S R]
    [SMulCommClass G H R] (f : S[X]) : SMulCommClass G H (f.rootSet R) where
smul_comm _ _ _ := Subtype.ext smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: S] [Algebra S R] (G H
  body: Subtype.ext smul_assoc _ _ _

中文:
实例 [交换环
  签名: S] [代数 S R] (G H
  定义体: Subtype.ext smul_assoc _ _ _

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance [CommRing S] [Algebra S R] (G H : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R]
    [Monoid H] [MulSemiringAction H R] [SMulCommClass H S R]
    [SMul G H] [IsScalarTower G H R] (f : S[X]) : IsScalarTower G H (f.rootSet R) where
smul_assoc _ _ _ := Subtype.ext smul_assoc _ _ _

end Roots

/--
lemma `eq_zero_of_natDegree_lt_card_of_eval_eq_zero` / 引理 `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`

English:
lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero
  statement: {R} [CommRing R] [IsDomain R]
  proof: by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset <= Multiset.card p.roots := Multiset.toFinset_card_le _
    _ <= natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injecti

中文:
引理 eq_zero_of_natDegree_lt_card_of_eval_eq_zero
  结论: {R} [交换环 R] [是整环 R]
  证明: by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset <= Multiset.card p.roots := Multiset.toFinset_card_le _
    _ <= natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injecti

Depends on / 依赖: Finset, Finset.card_mono, Finset.mem_image, Finset.mem_univ, Finset.univ.image, Fintype, Fintype.card, Multiset, Multiset.card, Multiset.mem_toFinset, Multiset.toFinset_card_le, Polynomial, Polynomial.card_roots, Set.card_range_of_injective, Set.range, Set.toFinset_card, Set.toFinset_range, card_mono, card_range_of_injective, card_roots
-/
lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι -> R} (hf : Function.Injective f)
    (heval : forall i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset <= Multiset.card p.roots := Multiset.toFinset_card_le _
    _ <= natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = #(Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ <= #p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, mem_roots', ne_eq,
    IsRoot.def, forall_exists_index, hp, not_false_eq_true]
  rintro x rfl
  exact heval _

/--
lemma `eq_of_natDegree_lt_card_of_eval_eq` / 引理 `eq_of_natDegree_lt_card_of_eval_eq`

English:
lemma eq_of_natDegree_lt_card_of_eval_eq
  statement: {R} [CommRing R] [IsDomain R]
  proof: by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]

中文:
引理 eq_of_natDegree_lt_card_of_eval_eq
  结论: {R} [交换环 R] [是整环 R]
  证明: by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]

Depends on / 依赖: eq_zero_of_natDegree_lt_card_of_eval_eq_zero, natDegree_sub_le, sub_eq_zero
-/
lemma eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R] [IsDomain R]
    (p q : R[X]) {ι} [Fintype ι] {f : ι -> R} (hf : Function.Injective f)
    (heval : forall i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) : p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]

/--
lemma `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` / 引理 `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`

English:
lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
  statement: {R} [CommRing R] [IsDomain R]
  proof: eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s => heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

中文:
引理 eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
  结论: {R} [交换环 R] [是整环 R]
  证明: eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s => heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

Depends on / 依赖: Fintype, Fintype.card_coe, Subtype, Subtype.val_injective, card_coe, eq_zero_of_natDegree_lt_card_of_eval_eq_zero, hcard.trans_eq, i.prop, trans_eq, val_injective
-/
lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R]
    (p : R[X]) (s : Finset R) (heval : forall i in s, p.eval i = 0) (hcard : natDegree p < #s) :
    p = 0 :=
  eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s => heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

/--
lemma `eq_of_natDegree_lt_card_of_eval_eq'` / 引理 `eq_of_natDegree_lt_card_of_eval_eq'`

English:
lemma eq_of_natDegree_lt_card_of_eval_eq'
  statement: {R} [CommRing R] [IsDomain R]
  proof: eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s => heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

中文:
引理 eq_of_natDegree_lt_card_of_eval_eq'
  结论: {R} [交换环 R] [是整环 R]
  证明: eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s => heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

Depends on / 依赖: Fintype, Fintype.card_coe, Subtype, Subtype.val_injective, card_coe, eq_of_natDegree_lt_card_of_eval_eq, hcard.trans_eq, i.prop, trans_eq, val_injective
-/
lemma eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R] [IsDomain R]
    (p q : R[X]) (s : Finset R) (heval : forall i in s, p.eval i = q.eval i)
    (hcard : max p.natDegree q.natDegree < #s) : p = q :=
  eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s => heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

open Cardinal in
/--
lemma `eq_zero_of_forall_eval_zero_of_natDegree_lt_card` / 引理 `eq_zero_of_forall_eval_zero_of_natDegree_lt_card`

English:
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card
  proof: by
  obtain hR | hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

中文:
引理 eq_zero_of_对任意_eval_zero_of_natDegree_lt_card
  证明: by
  obtain hR | hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

Depends on / 依赖: Fintype, Fintype.ofFinite, Function, Function.injective_id, Nat.cast_lt, cast_lt, eq_zero_of_natDegree_lt_card_of_eval_eq_zero, finite_or_infinite, injective_id, mk_fintype, ofFinite, zero_of_eval_zero
-/
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card
    (f : R[X]) (hf : forall r, f.eval r = 0) (hfR : f.natDegree < #R) : f = 0 := by
  obtain hR | hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

open Cardinal in
/--
lemma `exists_eval_ne_zero_of_natDegree_lt_card` / 引理 `exists_eval_ne_zero_of_natDegree_lt_card`

English:
lemma exists_eval_ne_zero_of_natDegree_lt_card
  given: (f : R[X]) (hf : f != 0) (hfR : f.natDegree < #R)
  proof: by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

中文:
引理 存在_eval_ne_zero_of_natDegree_lt_card
  条件: (f : R[X]) (hf : f != 0) (hfR : f.natDegree < #R)
  证明: by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

Depends on / 依赖: contrapose, eq_zero_of_forall_eval_zero_of_natDegree_lt_card
-/
lemma exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f != 0) (hfR : f.natDegree < #R) :
    exists r, f.eval r != 0 := by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

section

omit [IsDomain R]

/--
theorem `monic_multisetProd_X_sub_C` / 定理 `monic_multisetProd_X_sub_C`

English:
theorem monic_multisetProd_X_sub_C
  given: (s : Multiset R)
  statement: Monic (s.map fun a => X - C a).prod
  proof: monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

中文:
定理 monic_multisetProd_X_sub_C
  条件: (s : Multiset R)
  结论: Monic (s.map fun a => X - C a).乘积
  证明: monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

Depends on / 依赖: monic_X_sub_C, monic_multiset_prod_of_monic
-/
theorem monic_multisetProd_X_sub_C (s : Multiset R) : Monic (s.map fun a => X - C a).prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

/--
theorem `monic_prod_X_sub_C` / 定理 `monic_prod_X_sub_C`

English:
theorem monic_prod_X_sub_C
  given: {α : Type*} (b : α -> R) (s : Finset α)
  proof: monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

中文:
定理 monic_prod_X_sub_C
  条件: {α : 类型} (b : α -> R) (s : 有限集 α)
  证明: monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

Depends on / 依赖: monic_X_sub_C, monic_prod_of_monic
-/
theorem monic_prod_X_sub_C {α : Type*} (b : α -> R) (s : Finset α) :
    Monic (∏ a in s, (X - C (b a))) :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

/--
theorem `monic_finprod_X_sub_C` / 定理 `monic_finprod_X_sub_C`

English:
theorem monic_finprod_X_sub_C
  given: {α : Type*} (b : α -> R)
  statement: Monic (∏ᶠ k, (X - C (b k)))
  proof: monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

中文:
定理 monic_finprod_X_sub_C
  条件: {α : 类型} (b : α -> R)
  结论: Monic (∏ᶠ k, (X - C (b k)))
  证明: monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

Depends on / 依赖: monic_X_sub_C, monic_finprod_of_monic
-/
theorem monic_finprod_X_sub_C {α : Type*} (b : α -> R) : Monic (∏ᶠ k, (X - C (b k))) :=
  monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

end

/--
theorem `prod_multiset_root_eq_finset_root` / 定理 `prod_multiset_root_eq_finset_root`

English:
theorem prod_multiset_root_eq_finset_root
  given: [DecidableEq R]
  proof: by
  simp only [count_roots, Finset.prod_multiset_map_count]

中文:
定理 prod_multiset_root_eq_finset_root
  条件: [DecidableEq R]
  证明: by
  simp only [count_roots, Finset.prod_multiset_map_count]

Depends on / 依赖: Finset, Finset.prod_multiset_map_count, count_roots, prod_multiset_map_count
-/
theorem prod_multiset_root_eq_finset_root [DecidableEq R] :
    (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p := by
  simp only [count_roots, Finset.prod_multiset_map_count]

/--
theorem `prod_multiset_X_sub_C_dvd` / 定理 `prod_multiset_X_sub_C_dvd`

English:
theorem prod_multiset_X_sub_C_dvd
  given: (p : R[X])
  statement: (p.roots.map fun a => X - C a).prod ∣ p
  proof: by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (monic_multisetProd_X_sub_C p.roots)]
  rw [prod_multiset_root_eq_finset_root]; rw [Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Po

中文:
定理 prod_multiset_X_sub_C_dvd
  条件: (p : R[X])
  结论: (p.roots.map fun a => X - C a).乘积 ∣ p
  证明: by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (monic_multisetProd_X_sub_C p.roots)]
  rw [prod_multiset_root_eq_finset_root]; rw [Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Po

Depends on / 依赖: Finset, Finset.prod_dvd_of_coprime, FractionRing, IsFractionRing, IsFractionRing.injective, Polynomial, Polynomial.map_dvd, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub, classical, injective, map_C, map_X, map_dvd, map_dvd_map, map_pow, map_prod, map_sub, monic_multisetProd_X_sub_C
-/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (monic_multisetProd_X_sub_C p.roots)]
  rw [prod_multiset_root_eq_finset_root]; rw [Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a)

/--
theorem `_root_.Multiset.prod_X_sub_C_dvd_iff_le_roots` / 定理 `_root_.Multiset.prod_X_sub_C_dvd_iff_le_roots`

English:
theorem _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots
  given: {p : R[X]} (hp : p != 0) (s : Multiset R)
  proof: by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots]; rw [le_rootMultiplicity_iff hp]; rw [← Multiset.prod_replicate]; rw [←
        Multiset.map_replicate fun a => X - C a]; rw [← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.ma

中文:
定理 _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots
  条件: {p : R[X]} (hp : p != 0) (s : Multiset R)
  证明: by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots]; rw [le_rootMultiplicity_iff hp]; rw [← Multiset.prod_replicate]; rw [←
        Multiset.map_replicate fun a => X - C a]; rw [← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.ma

Depends on / 依赖: Multiset, Multiset.filter_eq, Multiset.le_iff_count, Multiset.map_le_map, Multiset.map_replicate, Multiset.prod_dvd_prod_of_le, Multiset.prod_replicate, classical, count_roots, filter_eq, filter_le, le_iff_count, le_rootMultiplicity_iff, map_le_map, map_replicate, p.prod_multiset_X_sub_C_dvd, prod_dvd_prod_of_le, prod_multiset_X_sub_C_dvd, prod_replicate, s.filter_le
-/
theorem _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p != 0) (s : Multiset R) :
    (s.map fun a => X - C a).prod ∣ p ↔ s <= p.roots := by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots]; rw [le_rootMultiplicity_iff hp]; rw [← Multiset.prod_replicate]; rw [←
        Multiset.map_replicate fun a => X - C a]; rw [← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| s.filter_le _).trans h,
    fun h =>
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩

/--
theorem `exists_prod_multiset_X_sub_C_mul` / 定理 `exists_prod_multiset_X_sub_C_mul`

English:
theorem exists_prod_multiset_X_sub_C_mul
  given: (p : R[X])
  proof: by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [(monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq]; rw [natDegree_multiset_prod_X_sub_C_eq_card]
  · 

中文:
定理 存在_prod_multiset_X_sub_C_mul
  条件: (p : R[X])
  证明: by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [(monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq]; rw [natDegree_multiset_prod_X_sub_C_eq_card]
  · 

Depends on / 依赖: add_eq_left, congr_arg, conv_rhs, eq_or_ne, exacts, he.symm, monic_multisetProd_X_sub_C, mul_ne_zero, mul_zero, natDegree_mul, natDegree_multiset_prod_X_sub_C_eq_card, ne_zero, p.prod_multiset_X_sub_C_dvd, p.roots, prod_multiset_X_sub_C_dvd, replace, roots_mul, roots_multiset_prod_X_sub_C
-/
theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    exists q,
      (p.roots.map fun a => X - C a).prod * q = p ∧
        Multiset.card p.roots + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [(monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq]; rw [natDegree_multiset_prod_X_sub_C_eq_card]
  · replace he := congr_arg roots he.symm
    rw [roots_mul]; rw [roots_multiset_prod_X_sub_C] at he
    exacts [add_eq_left.1 he, mul_ne_zero (monic_multisetProd_X_sub_C p.roots).ne_zero hq]

/--
theorem `C_leadingCoeff_mul_prod_multiset_X_sub_C` / 定理 `C_leadingCoeff_mul_prod_multiset_X_sub_C`

English:
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C
  given: (hroots : Multiset.card p.roots = p.natDegree)
  proof: (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_multisetProd_X_sub_C p.roots)
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

中文:
定理 C_leadingCoeff_mul_prod_multiset_X_sub_C
  条件: (hroots : Multiset.card p.roots = p.natDegree)
  证明: (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_multisetProd_X_sub_C p.roots)
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

Depends on / 依赖: eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le, hroots, monic_multisetProd_X_sub_C, natDegree_multiset_prod_X_sub_C_eq_card, p.prod_multiset_X_sub_C_dvd, p.roots, prod_multiset_X_sub_C_dvd
-/
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
  (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_multisetProd_X_sub_C p.roots)
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

/--
theorem `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` / 定理 `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`

English:
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq
  statement: (hp : p.Monic)
  proof: by
  convert! C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff]; rw [C_1]; rw [one_mul]

中文:
定理 prod_multiset_X_sub_C_of_monic_of_roots_card_eq
  结论: (hp : p.Monic)
  证明: by
  convert! C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff]; rw [C_1]; rw [one_mul]

Depends on / 依赖: C_leadingCoeff_mul_prod_multiset_X_sub_C, convert, hp.leadingCoeff, hroots, leadingCoeff, one_mul
-/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert! C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff]; rw [C_1]; rw [one_mul]

/--
theorem `Monic.isUnit_leadingCoeff_of_dvd` / 定理 `Monic.isUnit_leadingCoeff_of_dvd`

English:
theorem Monic.isUnit_leadingCoeff_of_dvd
  given: {a p : R[X]} (hp : Monic p) (hap : a ∣ p)
  proof: isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

中文:
定理 Monic.isUnit_leadingCoeff_of_dvd
  条件: {a p : R[X]} (hp : Monic p) (hap : a ∣ p)
  证明: isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

Depends on / 依赖: hp.leadingCoeff, isUnit_of_dvd_one, leadingCoeff, leadingCoeff_dvd_leadingCoeff
-/
theorem Monic.isUnit_leadingCoeff_of_dvd {a p : R[X]} (hp : Monic p) (hap : a ∣ p) :
    IsUnit a.leadingCoeff :=
  isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

/--
theorem `card_roots_le_one_of_irreducible` / 定理 `card_roots_le_one_of_irreducible`

English:
theorem card_roots_le_one_of_irreducible
  given: (hirr : Irreducible p)
  statement: p.roots.card <= 1
  proof: by
  obtain hp | ⟨x, hx⟩ := p.roots.empty_or_exists_mem
  · simp [hp]
  convert! p.card_roots'
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    isRoot_of_mem_roots hx).symm

中文:
定理 card_roots_le_one_of_irreducible
  条件: (hirr : 不可约 p)
  结论: p.roots.card <= 1
  证明: by
  obtain hp | ⟨x, hx⟩ := p.roots.empty_or_exists_mem
  · simp [hp]
  convert! p.card_roots'
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    isRoot_of_mem_roots hx).symm

Depends on / 依赖: card_roots, convert, degree_eq_one_of_irreducible_of_root, empty_or_exists_mem, isRoot_of_mem_roots, natDegree_eq_of_degree_eq_some, p.card_roots, p.roots.empty_or_exists_mem
-/
theorem card_roots_le_one_of_irreducible (hirr : Irreducible p) : p.roots.card <= 1 := by
  obtain hp | ⟨x, hx⟩ := p.roots.empty_or_exists_mem
  · simp [hp]
  convert! p.card_roots'
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    isRoot_of_mem_roots hx).symm

/--
theorem `roots_eq_zero_of_irreducible_of_natDegree_ne_one` / 定理 `roots_eq_zero_of_irreducible_of_natDegree_ne_one`

English:
theorem roots_eq_zero_of_irreducible_of_natDegree_ne_one
  statement: (hirr : Irreducible p)
  proof: by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
exact hdeg natDegree_eq_of_degree_eq_some
    degree_eq_one_of_irreducible_of_root hirr (mem_roots'.mp hx).right

中文:
定理 roots_eq_zero_of_irreducible_of_natDegree_ne_one
  结论: (hirr : 不可约 p)
  证明: by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
exact hdeg natDegree_eq_of_degree_eq_some
    degree_eq_one_of_irreducible_of_root hirr (mem_roots'.mp hx).right

Depends on / 依赖: degree_eq_one_of_irreducible_of_root, exists_mem_of_ne_zero, hroots, mem_roots, natDegree_eq_of_degree_eq_some
-/
theorem roots_eq_zero_of_irreducible_of_natDegree_ne_one (hirr : Irreducible p)
    (hdeg : p.natDegree != 1) : p.roots = 0 := by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
exact hdeg natDegree_eq_of_degree_eq_some
    degree_eq_one_of_irreducible_of_root hirr (mem_roots'.mp hx).right

/--
theorem `Monic.irreducible_iff_degree_lt` / 定理 `Monic.irreducible_iff_degree_lt`

English:
theorem Monic.irreducible_iff_degree_lt
  given: (p_monic : Monic p) (p_1 : p != 1)
  proof: by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic

中文:
定理 Monic.irreducible_iff_degree_lt
  条件: (p_monic : Monic p) (p_1 : p != 1)
  证明: by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic

Depends on / 依赖: Finset, Finset.mem_Ioc, and_imp, deg_le, degree_pos_of_not_isUnit_of_dvd_monic, degree_smul_of_smul_regular, dvd_trans, irreducible_iff_lt_natDegree_lt, isSMulRegular_of_group, isUnit_leadingCoeff_of_dvd, mem_Ioc, monic_of_isUnit_leadingCoeff_inv_smul, natDegree_le_iff_degree_le, natDegree_pos_iff_degree_pos, p_monic, p_monic.irreducible_iff_lt_natDegree_lt, p_monic.isUnit_leadingCoeff_of_dvd, q_unit
-/
theorem Monic.irreducible_iff_degree_lt (p_monic : Monic p) (p_1 : p != 1) :
    Irreducible p ↔ forall q, degree q <= ↑(p.natDegree / 2) -> q ∣ p -> IsUnit q := by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic.isUnit_leadingCoeff_of_dvd dvd
    refine (h _ (monic_of_isUnit_leadingCoeff_inv_smul hu) ?_ ?_ (dvd_trans ?_ dvd)).elim
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rw [Units.smul_def, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (Units.isUnit _)).mul_left_dvd]
  · rintro h q _ deg_pos deg_le dvd
exact deg_pos.ne' degree_eq_zero_of_isUnit (h q deg_le dvd)

end CommRing

section

variable {A B : Type*} [CommRing A] [CommRing B]

/--
theorem `le_rootMultiplicity_map` / 定理 `le_rootMultiplicity_map`

English:
theorem le_rootMultiplicity_map
  given: {p : A[X]} {f : A ->+* B} (hmap : map f p != 0) (a : A)
  proof: by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f) (pow_rootMultiplicity_dvd p a))
  rw [map_pow]; rw [map_sub]; rw [coe_mapRingHom]; rw [map_X]; rw [map_C]

中文:
定理 le_rootMultiplicity_map
  条件: {p : A[X]} {f : A ->+* B} (hmap : map f p != 0) (a : A)
  证明: by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f) (pow_rootMultiplicity_dvd p a))
  rw [map_pow]; rw [map_sub]; rw [coe_mapRingHom]; rw [map_X]; rw [map_C]

Depends on / 依赖: _root_, _root_.map_dvd, _root_.trans, coe_mapRingHom, le_rootMultiplicity_iff, mapRingHom, map_C, map_X, map_dvd, map_pow, map_sub, pow_rootMultiplicity_dvd
-/
theorem le_rootMultiplicity_map {p : A[X]} {f : A ->+* B} (hmap : map f p != 0) (a : A) :
    rootMultiplicity a p <= rootMultiplicity (f a) (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f) (pow_rootMultiplicity_dvd p a))
  rw [map_pow]; rw [map_sub]; rw [coe_mapRingHom]; rw [map_X]; rw [map_C]

/--
theorem `eq_rootMultiplicity_map` / 定理 `eq_rootMultiplicity_map`

English:
theorem eq_rootMultiplicity_map
  given: {p : A[X]} {f : A ->+* B} (hf : Function.Injective f) (a : A)
  proof: by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_rootMultiplicity_iff hp0]; rw [← map_dvd_map f hf ((monic_X_sub_C a).pow _)]; rw [Polynomial.map_pow]; rw [Polyn

中文:
定理 eq_rootMultiplicity_map
  条件: {p : A[X]} {f : A ->+* B} (hf : 函数.单射 f) (a : A)
  证明: by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_rootMultiplicity_iff hp0]; rw [← map_dvd_map f hf ((monic_X_sub_C a).pow _)]; rw [Polynomial.map_pow]; rw [Polyn

Depends on / 依赖: Polynomial, Polynomial.map_ne_zero_iff, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_zero, le_antisymm, le_rootMultiplicity_iff, le_rootMultiplicity_map, map_C, map_X, map_dvd_map, map_ne_zero_iff, map_pow, map_sub, map_zero, monic_X_sub_C, pow_rootMultiplicity_dvd, rootMultiplicity_zero
-/
theorem eq_rootMultiplicity_map {p : A[X]} {f : A ->+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (p.map f) := by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_rootMultiplicity_iff hp0]; rw [← map_dvd_map f hf ((monic_X_sub_C a).pow _)]; rw [Polynomial.map_pow]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]
  apply pow_rootMultiplicity_dvd

/--
theorem `count_map_roots` / 定理 `count_map_roots`

English:
theorem count_map_roots
  statement: [IsDomain A] [DecidableEq B] {p : A[X]} {f : A ->+* B} (hmap : map f p != 0)
  proof: by
  rw [le_rootMultiplicity_iff hmap]; rw [← Multiset.prod_replicate]; rw [←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert! Polynomial.map_dvd f p.prod_mul

中文:
定理 count_map_roots
  结论: [是整环 A] [DecidableEq B] {p : A[X]} {f : A ->+* B} (hmap : map f p != 0)
  证明: by
  rw [le_rootMultiplicity_iff hmap]; rw [← Multiset.prod_replicate]; rw [←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert! Polynomial.map_dvd f p.prod_mul

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.filter_eq, Multiset.filter_le, Multiset.map_le_map, Multiset.map_map, Multiset.map_replicate, Multiset.prod_dvd_prod_of_le, Multiset.prod_replicate, Polynomial, Polynomial.map_dvd, Polynomial.map_multiset_prod, Polynomial.map_sub, comp_apply, convert, filter_eq, filter_le, le_rootMultiplicity_iff, map_C
-/
theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A ->+* B} (hmap : map f p != 0)
    (b : B) :
    (p.roots.map f).count b <= rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]; rw [← Multiset.prod_replicate]; rw [←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert! Polynomial.map_dvd f p.prod_multiset_X_sub_C_dvd
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.map_sub, map_X, map_C]

/--
theorem `count_map_roots_of_injective` / 定理 `count_map_roots_of_injective`

English:
theorem count_map_roots_of_injective
  statement: [IsDomain A] [DecidableEq B] (p : A[X]) {f : A ->+* B}
  proof: by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b

中文:
定理 count_map_roots_of_injective
  结论: [是整环 A] [DecidableEq B] (p : A[X]) {f : A ->+* B}
  证明: by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b

Depends on / 依赖: Multiset, Multiset.count_zero, Multiset.map_zero, Polynomial, Polynomial.map_ne_zero_iff, Polynomial.map_zero, count_map_roots, count_zero, le_refl, map_ne_zero_iff, map_zero, rootMultiplicity_zero, roots_zero
-/
theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A ->+* B}
    (hf : Function.Injective f) (b : B) :
    (p.roots.map f).count b <= rootMultiplicity b (p.map f) := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b

/--
theorem `map_roots_le` / 定理 `map_roots_le`

English:
theorem map_roots_le
  given: [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} (h : p.map f != 0)
  proof: by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h

中文:
定理 map_roots_le
  条件: [是整环 A] [是整环 B] {p : A[X]} {f : A ->+* B} (h : p.map f != 0)
  证明: by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h

Depends on / 依赖: Multiset, Multiset.le_iff_count, classical, count_map_roots, count_roots, le_iff_count
-/
theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} (h : p.map f != 0) :
    p.roots.map f <= (p.map f).roots := by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h

/--
theorem `map_roots_le_of_injective` / 定理 `map_roots_le_of_injective`

English:
theorem map_roots_le_of_injective
  statement: [IsDomain A] [IsDomain B] (p : A[X]) {f : A ->+* B}
  proof: by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero, le_rfl]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)

中文:
定理 map_roots_le_of_injective
  结论: [是整环 A] [是整环 B] (p : A[X]) {f : A ->+* B}
  证明: by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero, le_rfl]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)

Depends on / 依赖: Multiset, Multiset.map_zero, Polynomial, Polynomial.map_ne_zero_iff, Polynomial.map_zero, le_rfl, map_ne_zero_iff, map_roots_le, map_zero, roots_zero
-/
theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A ->+* B}
    (hf : Function.Injective f) : p.roots.map f <= (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero, le_rfl]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)

/--
theorem `card_roots_map_le_degree` / 定理 `card_roots_map_le_degree`

English:
theorem card_roots_map_le_degree
  statement: {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
  proof: by
  by_cases hpm0 : p.map f = 0
  · simp [hp0, hpm0, zero_le_degree_iff]
.trans degree_map_le exact card_roots hpm0

中文:
定理 card_roots_map_le_degree
  结论: {A B : 类型} [半环 A] [交换环 B] [是整环 B]
  证明: by
  by_cases hpm0 : p.map f = 0
  · simp [hp0, hpm0, zero_le_degree_iff]
.trans degree_map_le exact card_roots hpm0

Depends on / 依赖: card_roots, degree_map_le, p.map, zero_le_degree_iff
-/
theorem card_roots_map_le_degree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A ->+* B} (p : A[X]) (hp0 : p != 0) : (p.map f).roots.card <= p.degree := by
  by_cases hpm0 : p.map f = 0
  · simp [hp0, hpm0, zero_le_degree_iff]
.trans degree_map_le exact card_roots hpm0

/--
theorem `card_roots_map_le_natDegree` / 定理 `card_roots_map_le_natDegree`

English:
theorem card_roots_map_le_natDegree
  statement: {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
  proof: .trans natDegree_map_le card_roots' _

中文:
定理 card_roots_map_le_natDegree
  结论: {A B : 类型} [半环 A] [交换环 B] [是整环 B]
  证明: .trans natDegree_map_le card_roots' _

Depends on / 依赖: card_roots, natDegree_map_le
-/
theorem card_roots_map_le_natDegree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A ->+* B} (p : A[X]) : (p.map f).roots.card <= p.natDegree :=
.trans natDegree_map_le card_roots' _

/--
theorem `ncard_rootSet_le` / 定理 `ncard_rootSet_le`

English:
theorem ncard_rootSet_le
  given: (p : A[X]) (B : Type*) [CommRing B] [IsDomain B] [Algebra A B]
  proof: by
  classical
  grw [rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact p.card_roots_map_le_natDegree

中文:
定理 ncard_rootSet_le
  条件: (p : A[X]) (B : 类型) [交换环 B] [是整环 B] [代数 A B]
  证明: by
  classical
  grw [rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact p.card_roots_map_le_natDegree

Depends on / 依赖: Multiset, Multiset.toFinset_card_le, Set.ncard_coe_finset, card_roots_map_le_natDegree, classical, ncard_coe_finset, p.card_roots_map_le_natDegree, rootSet, toFinset_card_le
-/
theorem ncard_rootSet_le (p : A[X]) (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] :
    Set.ncard (p.rootSet B) <= p.natDegree := by
  classical
  grw [rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact p.card_roots_map_le_natDegree

/--
theorem `filter_roots_map_range_eq_map_roots` / 定理 `filter_roots_map_range_eq_map_roots`

English:
theorem filter_roots_map_range_eq_map_roots
  statement: [IsDomain A] [IsDomain B] {f : A ->+* B}
  proof: by
  classical
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    simp [hf, Multiset.count_map_eq_count', eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' => h ?_).symm
exact Exists.imp (fun _ => And.right) Multiset.mem_map.mp h'

中文:
定理 filter_roots_map_range_eq_map_roots
  结论: [是整环 A] [是整环 B] {f : A ->+* B}
  证明: by
  classical
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    simp [hf, Multiset.count_map_eq_count', eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' => h ?_).symm
exact Exists.imp (fun _ => And.right) Multiset.mem_map.mp h'

Depends on / 依赖: And.right, Exists, Exists.imp, Multiset, Multiset.count_eq_zero.mpr, Multiset.count_filter, Multiset.count_map_eq_count, Multiset.mem_map.mp, classical, count_eq_zero, count_filter, count_map_eq_count, eq_rootMultiplicity_map, mem_map, split_ifs
-/
theorem filter_roots_map_range_eq_map_roots [IsDomain A] [IsDomain B] {f : A ->+* B}
    [DecidablePred (· in f.range)] (hf : Function.Injective f)
    (p : A[X]) : (p.map f).roots.filter (· in f.range) = p.roots.map f := by
  classical
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    simp [hf, Multiset.count_map_eq_count', eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' => h ?_).symm
exact Exists.imp (fun _ => And.right) Multiset.mem_map.mp h'

/--
theorem `card_roots_le_map` / 定理 `card_roots_le_map`

English:
theorem card_roots_le_map
  given: [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} (h : p.map f != 0)
  proof: by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (map_roots_le h)

中文:
定理 card_roots_le_map
  条件: [是整环 A] [是整环 B] {p : A[X]} {f : A ->+* B} (h : p.map f != 0)
  证明: by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (map_roots_le h)

Depends on / 依赖: Multiset, Multiset.card_le_card, card_le_card, card_map, map_roots_le, p.roots.card_map
-/
theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} (h : p.map f != 0) :
    Multiset.card p.roots <= Multiset.card (p.map f).roots := by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (map_roots_le h)

/--
theorem `card_roots_le_map_of_injective` / 定理 `card_roots_le_map_of_injective`

English:
theorem card_roots_le_map_of_injective
  statement: [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B}
  proof: by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero, le_rfl]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)

中文:
定理 card_roots_le_map_of_injective
  结论: [是整环 A] [是整环 B] {p : A[X]} {f : A ->+* B}
  证明: by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero, le_rfl]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)

Depends on / 依赖: Multiset, Multiset.card_zero, Polynomial, Polynomial.map_ne_zero_iff, Polynomial.map_zero, card_roots_le_map, card_zero, le_rfl, map_ne_zero_iff, map_zero, roots_zero
-/
theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B}
    (hf : Function.Injective f) : Multiset.card p.roots <= Multiset.card (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero, le_rfl]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)

/--
theorem `roots_map_of_injective_of_card_eq_natDegree` / 定理 `roots_map_of_injective_of_card_eq_natDegree`

English:
theorem roots_map_of_injective_of_card_eq_natDegree
  statement: [IsDomain A] [IsDomain B] {p : A[X]}
  proof: by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

中文:
定理 roots_map_of_injective_of_card_eq_natDegree
  结论: [是整环 A] [是整环 B] {p : A[X]}
  证明: by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

Depends on / 依赖: Multiset, Multiset.card_map, Multiset.eq_of_le_of_card_le, card_map, card_roots_map_le_natDegree, eq_of_le_of_card_le, hroots, map_roots_le_of_injective
-/
theorem roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A ->+* B} (hf : Function.Injective f) (hroots : Multiset.card p.roots = p.natDegree) :
    p.roots.map f = (p.map f).roots := by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

/--
theorem `roots_map_of_map_ne_zero_of_card_eq_natDegree` / 定理 `roots_map_of_map_ne_zero_of_card_eq_natDegree`

English:
theorem roots_map_of_map_ne_zero_of_card_eq_natDegree
  statement: [IsDomain A] [IsDomain B] {p : A[X]}
  proof: eq_of_le_of_card_le (map_roots_le h) by
    simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

中文:
定理 roots_map_of_map_ne_zero_of_card_eq_natDegree
  结论: [是整环 A] [是整环 B] {p : A[X]}
  证明: eq_of_le_of_card_le (map_roots_le h) by
    simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

Depends on / 依赖: Multiset, Multiset.card_map, card_map, card_roots_map_le_natDegree, eq_of_le_of_card_le, hroots, map_roots_le
-/
theorem roots_map_of_map_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    (f : A ->+* B) (h : p.map f != 0) (hroots : p.roots.card = p.natDegree) :
    p.roots.map f = (p.map f).roots :=
eq_of_le_of_card_le (map_roots_le h) by
    simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

/--
theorem `Monic.roots_map_of_card_eq_natDegree` / 定理 `Monic.roots_map_of_card_eq_natDegree`

English:
theorem Monic.roots_map_of_card_eq_natDegree
  statement: [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic)
  proof: roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

中文:
定理 Monic.roots_map_of_card_eq_natDegree
  结论: [是整环 A] [是整环 B] {p : A[X]} (hm : p.Monic)
  证明: roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

Depends on / 依赖: hroots, map_monic_ne_zero, roots_map_of_map_ne_zero_of_card_eq_natDegree
-/
theorem Monic.roots_map_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic)
    (f : A ->+* B) (hroots : p.roots.card = p.natDegree) : p.roots.map f = (p.map f).roots :=
  roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

end

end Polynomial
