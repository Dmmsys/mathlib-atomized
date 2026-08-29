/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Finite.Prod

/-!
# Finite Exhaustions

This file defines a structure called `FiniteExhaustion` which represents an exhaustion of a
countable set by an increasing sequence of finite sets. Given a countable set `s`,
`FiniteExhaustion.choice s` is a choice of a finite exhaustion.
-/

@[expose] public section

open Set

/--
Definition of `Set.FiniteExhaustion` / `Set.FiniteExhaustion` 的定义

English:
structure Set.FiniteExhaustion
  parameters: {α : Type*} (s : Set α)
  axioms and operations (4):
    - toFun : Nat -> Set α
    - finite' : forall n, Finite (toFun n)
    - subset_succ' : forall n, toFun n subseteq toFun (n + 1)
    - iUnion_eq' : ⋃ n, toFun n = s

中文:
结构 集合.FiniteExhaustion
  参数: {α : 类型} (s : 集合 α)
  公理与运算 (4 个):
    - toFun : 自然数 -> 集合 α
    - finite' : 对任意 n, 有限 (toFun n)
    - subset_succ' : 对任意 n, toFun n subseteq toFun (n + 1)
    - iUnion_eq' : ⋃ n, toFun n = s
-/
structure Set.FiniteExhaustion {α : Type*} (s : Set α) where
  /-- The underlying sequence of a `FiniteExhaustion`. -/
  toFun : Nat -> Set α
  /-- Every set in a `FiniteExhaustion` is finite. -/
  finite' : forall n, Finite (toFun n)
  /-- The sequence of sets in a `FiniteExhaustion` are monotonically increasing. -/
  subset_succ' : forall n, toFun n subseteq toFun (n + 1)
  /-- The union of all sets in a `FiniteExhaustion` equals `s` -/
  iUnion_eq' : ⋃ n, toFun n = s

namespace Set.FiniteExhaustion

instance {α : Type*} {s : Set α} : FunLike (FiniteExhaustion s) Nat (Set α) where
  coe := toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance {α : Type*} {s : Set α} : OrderHomClass (FiniteExhaustion s) Nat (Set α) where
  map_rel K _ _ h := monotone_nat_of_le_succ (fun n => K.subset_succ' n) h

instance {α : Type*} {s : Set α} {K : FiniteExhaustion s} {n : Nat} : Finite (K n) :=
  K.finite' n

variable {α : Type*} {s : Set α} (K : FiniteExhaustion s)

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: K.toFun = K
  proof: rfl

中文:
定理 toFun_eq_coe
  结论: K.toFun = K
  证明: rfl
-/
theorem toFun_eq_coe : K.toFun = K := rfl

/--
theorem `finite` / 定理 `finite`

English:
theorem finite
  given: (n : Nat)
  statement: (K n).Finite
  proof: K.finite' n

中文:
定理 finite
  条件: (n : 自然数)
  结论: (K n).有限
  证明: K.finite' n
-/
protected theorem finite (n : Nat) : (K n).Finite := K.finite' n

/--
theorem `subset_succ` / 定理 `subset_succ`

English:
theorem subset_succ
  given: (n : Nat)
  statement: K n subseteq K (n + 1)
  proof: K.subset_succ' n

@[gcongr]

中文:
定理 subset_succ
  条件: (n : 自然数)
  结论: K n subseteq K (n + 1)
  证明: K.subset_succ' n

@[gcongr]

Depends on / 依赖: K.subset_succ, subset_succ
-/
theorem subset_succ (n : Nat) : K n subseteq K (n + 1) := K.subset_succ' n

@[gcongr]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {m n : Nat} (h : m <= n)
  statement: K m subseteq K n
  proof: OrderHomClass.mono K h

@[simp]

中文:
定理 mono
  条件: {m n : 自然数} (h : m <= n)
  结论: K m subseteq K n
  证明: OrderHomClass.mono K h

@[simp]
-/
protected theorem mono {m n : Nat} (h : m <= n) : K m subseteq K n :=
  OrderHomClass.mono K h

@[simp]
/--
theorem `iUnion_eq` / 定理 `iUnion_eq`

English:
theorem iUnion_eq
  statement: ⋃ n, K n = s
  proof: K.iUnion_eq'

中文:
定理 iUnion_eq
  结论: ⋃ n, K n = s
  证明: K.iUnion_eq'

Depends on / 依赖: K.iUnion_eq, iUnion_eq
-/
theorem iUnion_eq : ⋃ n, K n = s :=
  K.iUnion_eq'

/--
Definition of `_root_.Set.Countable.finiteExhaustion` / `_root_.Set.Countable.finiteExhaustion` 的定义

English:
definition _root_.Set.Countable.finiteExhaustion
  signature: {s : Set α} (hs : s.Countable)
  body: by
  apply Classical.choice
  by_cases h : Nonempty s
  · obtain ⟨f, hf⟩ := @exists_surjective_nat s h hs
    refine ⟨fun n => (Subtype.val ∘ f) '' {i | i <= n}, ?_, ?_, ?_⟩
    · exact fun n => Finite.image _ (finite_le_nat n)
    · grind
    · simp [← image_image, ← image_iUnion, iUnion_le_nat, ra

中文:
定义 _root_.集合.可数.finiteExhaustion
  签名: {s : 集合 α} (hs : s.可数)
  定义体: by
  apply Classical.choice
  by_cases h : Nonempty s
  · obtain ⟨f, hf⟩ := @exists_surjective_nat s h hs
    refine ⟨fun n => (Subtype.val ∘ f) '' {i | i <= n}, ?_, ?_, ?_⟩
    · exact fun n => Finite.image _ (finite_le_nat n)
    · grind
    · simp [← image_image, ← image_iUnion, iUnion_le_nat, ra

Depends on / 依赖: Classical, Classical.choice, Finite, Finite.image, Finite.to_subtype, Nonempty, Set.not_nonempty_iff_eq_empty, Subtype, Subtype.val, choice, exists_surjective_nat, finite_le_nat, iUnion_le_nat, image_iUnion, image_image, not_nonempty_iff_eq_empty, range_eq_univ, range_eq_univ.mpr, to_subtype
-/
noncomputable def _root_.Set.Countable.finiteExhaustion {s : Set α} (hs : s.Countable) :
    FiniteExhaustion s := by
  apply Classical.choice
  by_cases h : Nonempty s
  · obtain ⟨f, hf⟩ := @exists_surjective_nat s h hs
    refine ⟨fun n => (Subtype.val ∘ f) '' {i | i <= n}, ?_, ?_, ?_⟩
    · exact fun n => Finite.image _ (finite_le_nat n)
    · grind
    · simp [← image_image, ← image_iUnion, iUnion_le_nat, range_eq_univ.mpr hf]
  · refine ⟨fun _ => ∅, by simp [Finite.to_subtype], fun n => by simp, ?_⟩
    simp [Set.not_nonempty_iff_eq_empty'.mp h]

/--
lemma `_root_.Set.nonempty_finiteExhaustion_iff` / 引理 `_root_.Set.nonempty_finiteExhaustion_iff`

English:
lemma _root_.Set.nonempty_finiteExhaustion_iff
  given: {s : Set α}
  proof: by
  refine ⟨fun ⟨K⟩ => ?_, fun h => ⟨h.finiteExhaustion⟩⟩
  rw [← K.iUnion_eq]
exact countable_iUnion fun i => (K.finite i).countable

中文:
引理 _root_.集合.nonempty_finiteExhaustion_iff
  条件: {s : 集合 α}
  证明: by
  refine ⟨fun ⟨K⟩ => ?_, fun h => ⟨h.finiteExhaustion⟩⟩
  rw [← K.iUnion_eq]
exact countable_iUnion fun i => (K.finite i).countable

Depends on / 依赖: K.finite, K.iUnion_eq, countable, countable_iUnion, finite, finiteExhaustion, h.finiteExhaustion, iUnion_eq
-/
lemma _root_.Set.nonempty_finiteExhaustion_iff {s : Set α} :
    Nonempty s.FiniteExhaustion ↔ s.Countable := by
  refine ⟨fun ⟨K⟩ => ?_, fun h => ⟨h.finiteExhaustion⟩⟩
  rw [← K.iUnion_eq]
exact countable_iUnion fun i => (K.finite i).countable

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias Set.nonempty_finiteExhaustion_iff := Set.nonempty_finiteExhaustion_iff

section prod

variable {β : Type*} {t : Set β} (K' : FiniteExhaustion t)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: :
  body: { toFun n := K n ×ˢ K' n
    finite' n := (K.finite n).prod (K'.finite n)
    subset_succ' := fun n => Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      rw [Set.iUnion_prod_of_monotone (OrderHomClass.mono K) (OrderHomClass.mono K')]; rw [K.iUnion_eq]; rw [K'.iUnion_eq] }

中文:
定义 乘积
  签名: :
  定义体: { toFun n := K n ×ˢ K' n
    finite' n := (K.finite n).prod (K'.finite n)
    subset_succ' := fun n => Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      rw [Set.iUnion_prod_of_monotone (OrderHomClass.mono K) (OrderHomClass.mono K')]; rw [K.iUnion_eq]; rw [K'.iUnion_eq] }
-/
protected def prod :
    FiniteExhaustion (s ×ˢ t) :=
  { toFun n := K n ×ˢ K' n
    finite' n := (K.finite n).prod (K'.finite n)
    subset_succ' := fun n => Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      rw [Set.iUnion_prod_of_monotone (OrderHomClass.mono K) (OrderHomClass.mono K')]; rw [K.iUnion_eq]; rw [K'.iUnion_eq] }

/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (n : Nat)
  statement: (K.prod K') n = K n ×ˢ K' n
  proof: by rfl

中文:
定理 prod_apply
  条件: (n : 自然数)
  结论: (K.乘积 K') n = K n ×ˢ K' n
  证明: by rfl
-/
protected theorem prod_apply (n : Nat) : (K.prod K') n = K n ×ˢ K' n := by rfl

end prod

end Set.FiniteExhaustion
