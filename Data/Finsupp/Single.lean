/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Finsupp.Defs

/-!
# Finitely supported functions on exactly one point

This file contains definitions and basic results on defining/updating/removing `Finsupp`s
using one point of the domain.

## Main declarations

* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.
-/

@[expose] public section

assert_not_exists CompleteLattice

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `single` -/

section Single

variable [Zero M] {a a' : α} {b : M}

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (a : α) (b : M)
  body: haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by grind

@[grind =]

中文:
定义 single
  签名: (a : α) (b : M)
  定义体: haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by grind

@[grind =]

Depends on / 依赖: Classical, Classical.decEq, Pi.single, mem_support_toFun, single
-/
def single (a : α) (b : M) : α ->₀ M where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by grind

@[grind =]
/--
theorem `single_apply` / 定理 `single_apply`

English:
theorem single_apply
  given: [Decidable (a = a')]
  statement: single a b a' = if a = a' then b else 0
  proof: by
  classical
  simp_rw [@eq_comm _ a a', single, coe_mk, Pi.single_apply]

中文:
定理 single_apply
  条件: [可判定 (a = a')]
  结论: single a b a' = if a = a' then b else 0
  证明: by
  classical
  simp_rw [@eq_comm _ a a', single, coe_mk, Pi.single_apply]

Depends on / 依赖: Pi.single_apply, classical, coe_mk, eq_comm, simp_rw, single, single_apply
-/
theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  classical
  simp_rw [@eq_comm _ a a', single, coe_mk, Pi.single_apply]

/--
theorem `single_apply_left` / 定理 `single_apply_left`

English:
theorem single_apply_left
  given: {f : α -> β} (hf : Function.Injective f) (x z : α) (y : M)
  proof: by classical simp only [single_apply, hf.eq_iff]

中文:
定理 single_apply_left
  条件: {f : α -> β} (hf : 函数.单射 f) (x z : α) (y : M)
  证明: by classical simp only [single_apply, hf.eq_iff]

Depends on / 依赖: classical, eq_iff, hf.eq_iff, mk_eq_normalize, mul_def, single_apply
-/
theorem single_apply_left {f : α -> β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]

/--
theorem `single_eq_pi_single` / 定理 `single_eq_pi_single`

English:
theorem single_eq_pi_single
  given: [DecidableEq α] (a : α) (b : M)
  statement: ⇑(single a b) = Pi.single a b
  proof: by
  ext; simp [single_apply, Pi.single_apply, eq_comm]

中文:
定理 single_eq_pi_single
  条件: [DecidableEq α] (a : α) (b : M)
  结论: ⇑(single a b) = 依赖函数类型.single a b
  证明: by
  ext; simp [single_apply, Pi.single_apply, eq_comm]

Depends on / 依赖: Pi.single_apply, eq_comm, single_apply
-/
theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b := by
  ext; simp [single_apply, Pi.single_apply, eq_comm]

/--
theorem `set_indicator_singleton` / 定理 `set_indicator_singleton`

English:
theorem set_indicator_singleton
  given: (a : α) (f : α -> M)
  proof: by
  classical rw [Set.indicator_singleton, single_eq_pi_single]

@[deprecated set_indicator_singleton (since := "2026-04-27")]

中文:
定理 set_indicator_singleton
  条件: (a : α) (f : α -> M)
  证明: by
  classical rw [Set.indicator_singleton, single_eq_pi_single]

@[deprecated set_indicator_singleton (since := "2026-04-27")]

Depends on / 依赖: Set.indicator_singleton, classical, indicator_singleton, single_eq_pi_single
-/
theorem set_indicator_singleton (a : α) (f : α -> M) :
    Set.indicator {a} f = ⇑(single a (f a)) := by
  classical rw [Set.indicator_singleton, single_eq_pi_single]

@[deprecated set_indicator_singleton (since := "2026-04-27")]
/--
theorem `single_eq_set_indicator` / 定理 `single_eq_set_indicator`

English:
theorem single_eq_set_indicator
  statement: ⇑(single a b) = Set.indicator {a} fun _ => b
  proof: (set_indicator_singleton a (fun _ => b)).symm

@[simp]

中文:
定理 single_eq_set_indicator
  结论: ⇑(single a b) = 集合.indicator {a} fun _ => b
  证明: (set_indicator_singleton a (fun _ => b)).symm

@[simp]

Depends on / 依赖: set_indicator_singleton
-/
theorem single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b :=
  (set_indicator_singleton a (fun _ => b)).symm

@[simp]
/--
theorem `single_eq_same` / 定理 `single_eq_same`

English:
theorem single_eq_same
  statement: (single a b : α ->₀ M) a = b
  proof: by
  classical exact Pi.single_eq_same (M := fun _ => M) a b

@[simp]

中文:
定理 single_eq_same
  结论: (single a b : α ->₀ M) a = b
  证明: by
  classical exact Pi.single_eq_same (M := fun _ => M) a b

@[simp]

Depends on / 依赖: Pi.single_eq_same, classical, single_eq_same
-/
theorem single_eq_same : (single a b : α ->₀ M) a = b := by
  classical exact Pi.single_eq_same (M := fun _ => M) a b

@[simp]
/--
theorem `single_eq_of_ne` / 定理 `single_eq_of_ne`

English:
theorem single_eq_of_ne
  given: (h : a' != a)
  statement: (single a b : α ->₀ M) a' = 0
  proof: by
  classical exact Pi.single_eq_of_ne h _

@[simp]

中文:
定理 single_eq_of_ne
  条件: (h : a' != a)
  结论: (single a b : α ->₀ M) a' = 0
  证明: by
  classical exact Pi.single_eq_of_ne h _

@[simp]

Depends on / 依赖: Pi.single_eq_of_ne, classical, single_eq_of_ne
-/
theorem single_eq_of_ne (h : a' != a) : (single a b : α ->₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne h _

@[simp]
/--
theorem `single_eq_of_ne'` / 定理 `single_eq_of_ne'`

English:
theorem single_eq_of_ne'
  given: (h : a != a')
  statement: (single a b : α ->₀ M) a' = 0
  proof: by
  classical exact Pi.single_eq_of_ne' h _

中文:
定理 single_eq_of_ne'
  条件: (h : a != a')
  结论: (single a b : α ->₀ M) a' = 0
  证明: by
  classical exact Pi.single_eq_of_ne' h _

Depends on / 依赖: Pi.single_eq_of_ne, classical, single_eq_of_ne
-/
theorem single_eq_of_ne' (h : a != a') : (single a b : α ->₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne' h _

/--
theorem `single_eq_update` / 定理 `single_eq_update`

English:
theorem single_eq_update
  given: [DecidableEq α] (a : α) (b : M)
  proof: single_eq_pi_single a b

@[simp, grind =]

中文:
定理 single_eq_update
  条件: [DecidableEq α] (a : α) (b : M)
  证明: single_eq_pi_single a b

@[simp, grind =]

Depends on / 依赖: single_eq_pi_single
-/
theorem single_eq_update [DecidableEq α] (a : α) (b : M) :
    ⇑(single a b) = Function.update (0 : _) a b :=
  single_eq_pi_single a b

@[simp, grind =]
/--
theorem `single_zero` / 定理 `single_zero`

English:
theorem single_zero
  given: (a : α)
  statement: (single a 0 : α ->₀ M) = 0
  proof: DFunLike.coe_injective by
    classical simpa only [single_eq_update, coe_zero] using! Function.update_eq_self a (0 : α -> M)

中文:
定理 single_zero
  条件: (a : α)
  结论: (single a 0 : α ->₀ M) = 0
  证明: DFunLike.coe_injective by
    classical simpa only [single_eq_update, coe_zero] using! Function.update_eq_self a (0 : α -> M)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.update_eq_self, classical, coe_injective, coe_zero, single_eq_update, update_eq_self
-/
theorem single_zero (a : α) : (single a 0 : α ->₀ M) = 0 :=
DFunLike.coe_injective by
    classical simpa only [single_eq_update, coe_zero] using! Function.update_eq_self a (0 : α -> M)

/--
theorem `single_of_single_apply` / 定理 `single_of_single_apply`

English:
theorem single_of_single_apply
  given: (a a' : α) (b : M)
  proof: by
  classical
  grind

中文:
定理 single_of_single_apply
  条件: (a a' : α) (b : M)
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
  grind

/--
lemma `support_single` / 引理 `support_single`

English:
lemma support_single
  given: (a : α) (hb : b != 0)
  statement: (single a b).support = {a}
  proof: if_neg hb

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

中文:
引理 support_single
  条件: (a : α) (hb : b != 0)
  结论: (single a b).support = {a}
  证明: if_neg hb

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single
-/
@[simp] lemma support_single (a : α) (hb : b != 0) : (single a b).support = {a} :=
  if_neg hb

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

/--
theorem `support_single_subset` / 定理 `support_single_subset`

English:
theorem support_single_subset
  statement: (single a b).support subseteq {a}
  proof: by
  classical
  grind

中文:
定理 support_single_subset
  结论: (single a b).support subseteq {a}
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
theorem support_single_subset : (single a b).support subseteq {a} := by
  classical
  grind

/--
theorem `single_apply_mem` / 定理 `single_apply_mem`

English:
theorem single_apply_mem
  given: (x)
  statement: single a b x in ({0, b} : Set M)
  proof: by
  classical
  grind

中文:
定理 single_apply_mem
  条件: (x)
  结论: single a b x in ({0, b} : 集合 M)
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
theorem single_apply_mem (x) : single a b x in ({0, b} : Set M) := by
  classical
  grind

/--
theorem `range_single_subset` / 定理 `range_single_subset`

English:
theorem range_single_subset
  statement: Set.range (single a b) subseteq {0, b}
  proof: Set.range_subset_iff.2 single_apply_mem

中文:
定理 range_single_subset
  结论: 集合.range (single a b) subseteq {0, b}
  证明: Set.range_subset_iff.2 single_apply_mem

Depends on / 依赖: Set.range_subset_iff, range_subset_iff, single_apply_mem
-/
theorem range_single_subset : Set.range (single a b) subseteq {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/--
theorem `single_injective` / 定理 `single_injective`

English:
theorem single_injective
  given: (a : α)
  statement: Function.Injective (single a : M -> α ->₀ M)
  proof: fun b₁ b₂ eq => by
  have : (single a b₁ : α ->₀ M) a = (single a b₂ : α ->₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

中文:
定理 single_injective
  条件: (a : α)
  结论: 函数.单射 (single a : M -> α ->₀ M)
  证明: fun b₁ b₂ eq => by
  have : (single a b₁ : α ->₀ M) a = (single a b₂ : α ->₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

Depends on / 依赖: single, single_eq_same
-/
theorem single_injective (a : α) : Function.Injective (single a : M -> α ->₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α ->₀ M) a = (single a b₂ : α ->₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

/--
theorem `single_apply_eq_zero` / 定理 `single_apply_eq_zero`

English:
theorem single_apply_eq_zero
  given: {a x : α} {b : M}
  statement: single a b x = 0 ↔ x = a -> b = 0
  proof: by
  classical simp [single_apply, eq_comm]

中文:
定理 single_apply_eq_zero
  条件: {a x : α} {b : M}
  结论: single a b x = 0 ↔ x = a -> b = 0
  证明: by
  classical simp [single_apply, eq_comm]

Depends on / 依赖: classical, eq_comm, single_apply
-/
theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a -> b = 0 := by
  classical simp [single_apply, eq_comm]

/--
theorem `single_apply_ne_zero` / 定理 `single_apply_ne_zero`

English:
theorem single_apply_ne_zero
  given: {a x : α} {b : M}
  statement: single a b x != 0 ↔ x = a ∧ b != 0
  proof: by
  simp [single_apply_eq_zero]

中文:
定理 single_apply_ne_zero
  条件: {a x : α} {b : M}
  结论: single a b x != 0 ↔ x = a ∧ b != 0
  证明: by
  simp [single_apply_eq_zero]

Depends on / 依赖: single_apply_eq_zero
-/
theorem single_apply_ne_zero {a x : α} {b : M} : single a b x != 0 ↔ x = a ∧ b != 0 := by
  simp [single_apply_eq_zero]

/--
theorem `mem_support_single` / 定理 `mem_support_single`

English:
theorem mem_support_single
  given: (a a' : α) (b : M)
  statement: a in (single a' b).support ↔ a = a' ∧ b != 0
  proof: by
  simp [single_apply_eq_zero]

中文:
定理 mem_support_single
  条件: (a a' : α) (b : M)
  结论: a in (single a' b).support ↔ a = a' ∧ b != 0
  证明: by
  simp [single_apply_eq_zero]

Depends on / 依赖: single_apply_eq_zero
-/
theorem mem_support_single (a a' : α) (b : M) : a in (single a' b).support ↔ a = a' ∧ b != 0 := by
  simp [single_apply_eq_zero]

/--
theorem `eq_single_iff` / 定理 `eq_single_iff`

English:
theorem eq_single_iff
  given: {f : α ->₀ M} {a b}
  statement: f = single a b ↔ f.support subseteq {a} ∧ f a = b
  proof: by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?_⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : x = a <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact notMem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx))) hx)

中文:
定理 eq_single_iff
  条件: {f : α ->₀ M} {a b}
  结论: f = single a b ↔ f.support subseteq {a} ∧ f a = b
  证明: by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?_⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : x = a <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact notMem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx))) hx)

Depends on / 依赖: h.symm, mem_singleton, notMem_support_iff, not_false_iff, single_eq_of_ne, single_eq_same, support_single_subset
-/
theorem eq_single_iff {f : α ->₀ M} {a b} : f = single a b ↔ f.support subseteq {a} ∧ f a = b := by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?_⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : x = a <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact notMem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx))) hx)

/--
theorem `single_eq_single_iff` / 定理 `single_eq_single_iff`

English:
theorem single_eq_single_iff
  given: (a₁ a₂ : α) (b₁ b₂ : M)
  proof: by
  classical
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?_⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      grind
  · grind

中文:
定理 single_eq_single_iff
  条件: (a₁ a₂ : α) (b₁ b₂ : M)
  证明: by
  classical
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?_⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      grind
  · grind

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Or.inl, classical, eq_iff, ext_iff, single_injective
-/
theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  classical
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?_⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      grind
  · grind

/--
theorem `single_left_injective` / 定理 `single_left_injective`

English:
theorem single_left_injective
  given: (h : b != 0)
  statement: Function.Injective fun a : α => single a b
  proof: fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

中文:
定理 single_left_injective
  条件: (h : b != 0)
  结论: 函数.单射 fun a : α => single a b
  证明: fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

Depends on / 依赖: resolve_right, single_eq_single_iff
-/
theorem single_left_injective (h : b != 0) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

/--
theorem `single_left_inj` / 定理 `single_left_inj`

English:
theorem single_left_inj
  given: (h : b != 0)
  statement: single a b = single a' b ↔ a = a'
  proof: (single_left_injective h).eq_iff

中文:
定理 single_left_inj
  条件: (h : b != 0)
  结论: single a b = single a' b ↔ a = a'
  证明: (single_left_injective h).eq_iff

Depends on / 依赖: eq_iff, single_left_injective
-/
theorem single_left_inj (h : b != 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

/--
lemma `apply_surjective` / 引理 `apply_surjective`

English:
lemma apply_surjective
  given: (a : α)
  statement: Surjective fun f : α ->₀ M => f a
  proof: RightInverse.surjective fun _ => single_eq_same

中文:
引理 apply_surjective
  条件: (a : α)
  结论: 满射 fun f : α ->₀ M => f a
  证明: RightInverse.surjective fun _ => single_eq_same

Depends on / 依赖: RightInverse, RightInverse.surjective, single_eq_same, surjective
-/
lemma apply_surjective (a : α) : Surjective fun f : α ->₀ M => f a :=
  RightInverse.surjective fun _ => single_eq_same

/--
theorem `support_single_ne_bot` / 定理 `support_single_ne_bot`

English:
theorem support_single_ne_bot
  given: (i : α) (h : b != 0)
  statement: (single i b).support != ⊥
  proof: by
  simpa only [support_single _ h] using! singleton_ne_empty _

中文:
定理 support_single_ne_bot
  条件: (i : α) (h : b != 0)
  结论: (single i b).support != ⊥
  证明: by
  simpa only [support_single _ h] using! singleton_ne_empty _

Depends on / 依赖: singleton_ne_empty, support_single
-/
theorem support_single_ne_bot (i : α) (h : b != 0) : (single i b).support != ⊥ := by
  simpa only [support_single _ h] using! singleton_ne_empty _

/--
theorem `support_single_disjoint` / 定理 `support_single_disjoint`

English:
theorem support_single_disjoint
  given: {b' : M} (hb : b != 0) (hb' : b' != 0) {i j : α}
  proof: by
  rw [support_single _ hb]; rw [support_single _ hb']; rw [disjoint_singleton]

@[simp]

中文:
定理 support_single_disjoint
  条件: {b' : M} (hb : b != 0) (hb' : b' != 0) {i j : α}
  证明: by
  rw [support_single _ hb]; rw [support_single _ hb']; rw [disjoint_singleton]

@[simp]

Depends on / 依赖: disjoint_singleton, support_single
-/
theorem support_single_disjoint {b' : M} (hb : b != 0) (hb' : b' != 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i != j := by
  rw [support_single _ hb]; rw [support_single _ hb']; rw [disjoint_singleton]

@[simp]
/--
theorem `single_eq_zero` / 定理 `single_eq_zero`

English:
theorem single_eq_zero
  statement: single a b = 0 ↔ b = 0
  proof: by
  classical simp [DFunLike.ext_iff, single_apply]

中文:
定理 single_eq_zero
  结论: single a b = 0 ↔ b = 0
  证明: by
  classical simp [DFunLike.ext_iff, single_apply]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, classical, ext_iff, single_apply
-/
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  classical simp [DFunLike.ext_iff, single_apply]

/--
theorem `single_ne_zero` / 定理 `single_ne_zero`

English:
theorem single_ne_zero
  statement: single a b != 0 ↔ b != 0
  proof: single_eq_zero.not

中文:
定理 single_ne_zero
  结论: single a b != 0 ↔ b != 0
  证明: single_eq_zero.not

Depends on / 依赖: single_eq_zero, single_eq_zero.not
-/
theorem single_ne_zero : single a b != 0 ↔ b != 0 :=
  single_eq_zero.not

/--
theorem `single_swap` / 定理 `single_swap`

English:
theorem single_swap
  given: (a₁ a₂ : α) (b : M)
  statement: single a₁ b a₂ = single a₂ b a₁
  proof: by
  classical simp only [single_apply, eq_comm]

中文:
定理 single_swap
  条件: (a₁ a₂ : α) (b : M)
  结论: single a₁ b a₂ = single a₂ b a₁
  证明: by
  classical simp only [single_apply, eq_comm]

Depends on / 依赖: classical, eq_comm, single_apply
-/
theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  classical simp only [single_apply, eq_comm]

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nonempty α] [Nontrivial M]
  body: by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

中文:
实例 instNontrivial
  签名: [非空 α] [非平凡 M]
  定义体: by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

Depends on / 依赖: exists_ne, inhabit, nontrivial_of_ne, single, single_eq_zero
-/
instance instNontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α ->₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

/--
lemma `nontrivial_iff` / 引理 `nontrivial_iff`

English:
lemma nontrivial_iff
  statement: Nontrivial (α ->₀ M) ↔ Nonempty α ∧ Nontrivial M where
  proof: by
    rintro ⟨f, g, hfg⟩
    obtain ⟨a, ha⟩ := ne_iff.mp hfg
    exact ⟨⟨a⟩, _, _, ha⟩
  mpr | ⟨_, _⟩ => inferInstance

中文:
引理 nontrivial_iff
  结论: 非平凡 (α ->₀ M) ↔ 非空 α ∧ 非平凡 M where
  证明: by
    rintro ⟨f, g, hfg⟩
    obtain ⟨a, ha⟩ := ne_iff.mp hfg
    exact ⟨⟨a⟩, _, _, ha⟩
  mpr | ⟨_, _⟩ => inferInstance

Depends on / 依赖: ne_iff, ne_iff.mp
-/
lemma nontrivial_iff : Nontrivial (α ->₀ M) ↔ Nonempty α ∧ Nontrivial M where
  mp := by
    rintro ⟨f, g, hfg⟩
    obtain ⟨a, ha⟩ := ne_iff.mp hfg
    exact ⟨⟨a⟩, _, _, ha⟩
  mpr | ⟨_, _⟩ => inferInstance

/--
theorem `unique_single` / 定理 `unique_single`

English:
theorem unique_single
  given: [Unique α] (x : α ->₀ M)
  statement: x = single default (x default)
  proof: ext Unique.forall_iff.2 single_eq_same.symm

@[simp]

中文:
定理 unique_single
  条件: [唯一 α] (x : α ->₀ M)
  结论: x = single default (x default)
  证明: ext Unique.forall_iff.2 single_eq_same.symm

@[simp]

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff, single_eq_same, single_eq_same.symm
-/
theorem unique_single [Unique α] (x : α ->₀ M) : x = single default (x default) :=
ext Unique.forall_iff.2 single_eq_same.symm

@[simp]
/--
theorem `unique_single_eq_iff` / 定理 `unique_single_eq_iff`

English:
theorem unique_single_eq_iff
  given: [Unique α] {b' : M}
  statement: single a b = single a' b' ↔ b = b'
  proof: by
  rw [Finsupp.unique_ext_iff]; rw [Unique.eq_default a]; rw [Unique.eq_default a']; rw [single_eq_same]; rw [single_eq_same]

中文:
定理 unique_single_eq_iff
  条件: [唯一 α] {b' : M}
  结论: single a b = single a' b' ↔ b = b'
  证明: by
  rw [Finsupp.unique_ext_iff]; rw [Unique.eq_default a]; rw [Unique.eq_default a']; rw [single_eq_same]; rw [single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.unique_ext_iff, Unique, Unique.eq_default, eq_default, single_eq_same, unique_ext_iff
-/
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [Finsupp.unique_ext_iff]; rw [Unique.eq_default a]; rw [Unique.eq_default a']; rw [single_eq_same]; rw [single_eq_same]

/--
lemma `apply_single'` / 引理 `apply_single'`

English:
lemma apply_single'
  given: [Zero N] [Zero P] (e : N -> P) (he : e 0 = 0) (a : α) (n : N) (b : α)
  proof: by
  classical
  grind

中文:
引理 apply_single'
  条件: [零 N] [零 P] (e : N -> P) (he : e 0 = 0) (a : α) (n : N) (b : α)
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
lemma apply_single' [Zero N] [Zero P] (e : N -> P) (he : e 0 = 0) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b := by
  classical
  grind

/--
theorem `support_eq_singleton` / 定理 `support_eq_singleton`

English:
theorem support_eq_singleton
  given: {f : α ->₀ M} {a : α}
  proof: ⟨fun h =>
⟨mem_support_iff.1 h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single _ h.1⟩

中文:
定理 support_eq_singleton
  条件: {f : α ->₀ M} {a : α}
  证明: ⟨fun h =>
⟨mem_support_iff.1 h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single _ h.1⟩

Depends on / 依赖: Finset, Finset.mem_singleton_self, eq_single_iff, h.symm, mem_singleton_self, mem_support_iff, subset_of_eq, support_single
-/
theorem support_eq_singleton {f : α ->₀ M} {a : α} :
    f.support = {a} ↔ f a != 0 ∧ f = single a (f a) :=
  ⟨fun h =>
⟨mem_support_iff.1 h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single _ h.1⟩

/--
theorem `support_eq_singleton'` / 定理 `support_eq_singleton'`

English:
theorem support_eq_singleton'
  given: {f : α ->₀ M} {a : α}
  proof: ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single _ hb⟩

中文:
定理 support_eq_singleton'
  条件: {f : α ->₀ M} {a : α}
  证明: ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single _ hb⟩

Depends on / 依赖: hf.symm, support_eq_singleton, support_single
-/
theorem support_eq_singleton' {f : α ->₀ M} {a : α} :
    f.support = {a} ↔ exists b != 0, f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single _ hb⟩

/--
theorem `card_support_eq_one` / 定理 `card_support_eq_one`

English:
theorem card_support_eq_one
  given: {f : α ->₀ M}
  proof: by
  simp only [card_eq_one, support_eq_singleton]

中文:
定理 card_support_eq_one
  条件: {f : α ->₀ M}
  证明: by
  simp only [card_eq_one, support_eq_singleton]

Depends on / 依赖: card_eq_one, support_eq_singleton
-/
theorem card_support_eq_one {f : α ->₀ M} :
    #f.support = 1 ↔ exists a, f a != 0 ∧ f = single a (f a) := by
  simp only [card_eq_one, support_eq_singleton]

/--
theorem `card_support_eq_one'` / 定理 `card_support_eq_one'`

English:
theorem card_support_eq_one'
  given: {f : α ->₀ M}
  proof: by
  simp only [card_eq_one, support_eq_singleton']

中文:
定理 card_support_eq_one'
  条件: {f : α ->₀ M}
  证明: by
  simp only [card_eq_one, support_eq_singleton']

Depends on / 依赖: card_eq_one, support_eq_singleton
-/
theorem card_support_eq_one' {f : α ->₀ M} :
    #f.support = 1 ↔ exists a, exists b != 0, f = single a b := by
  simp only [card_eq_one, support_eq_singleton']

/--
theorem `support_subset_singleton` / 定理 `support_subset_singleton`

English:
theorem support_subset_singleton
  given: {f : α ->₀ M} {a : α}
  statement: f.support subseteq {a} ↔ f = single a (f a)
  proof: ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

中文:
定理 support_subset_singleton
  条件: {f : α ->₀ M} {a : α}
  结论: f.support subseteq {a} ↔ f = single a (f a)
  证明: ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

Depends on / 依赖: eq_single_iff, eq_single_iff.mp, eq_single_iff.mpr
-/
theorem support_subset_singleton {f : α ->₀ M} {a : α} : f.support subseteq {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

/--
theorem `support_subset_singleton'` / 定理 `support_subset_singleton'`

English:
theorem support_subset_singleton'
  given: {f : α ->₀ M} {a : α}
  statement: f.support subseteq {a} ↔ exists b, f = single a b
  proof: ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb]; rw [support_subset_singleton]; rw [single_eq_same]⟩

中文:
定理 support_subset_singleton'
  条件: {f : α ->₀ M} {a : α}
  结论: f.support subseteq {a} ↔ 存在 b, f = single a b
  证明: ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb]; rw [support_subset_singleton]; rw [single_eq_same]⟩

Depends on / 依赖: single_eq_same, support_subset_singleton, support_subset_singleton.mp
-/
theorem support_subset_singleton' {f : α ->₀ M} {a : α} : f.support subseteq {a} ↔ exists b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb]; rw [support_subset_singleton]; rw [single_eq_same]⟩

/--
theorem `card_support_le_one` / 定理 `card_support_le_one`

English:
theorem card_support_le_one
  given: [Nonempty α] {f : α ->₀ M}
  proof: by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

中文:
定理 card_support_le_one
  条件: [非空 α] {f : α ->₀ M}
  证明: by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

Depends on / 依赖: card_le_one_iff_subset_singleton, support_subset_singleton
-/
theorem card_support_le_one [Nonempty α] {f : α ->₀ M} :
    #f.support <= 1 ↔ exists a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

/--
theorem `card_support_le_one'` / 定理 `card_support_le_one'`

English:
theorem card_support_le_one'
  given: [Nonempty α] {f : α ->₀ M}
  proof: by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

中文:
定理 card_support_le_one'
  条件: [非空 α] {f : α ->₀ M}
  证明: by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

Depends on / 依赖: card_le_one_iff_subset_singleton, support_subset_singleton
-/
theorem card_support_le_one' [Nonempty α] {f : α ->₀ M} :
    #f.support <= 1 ↔ exists a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

/-- If `α` has a unique term, then finitely supported functions `α →₀ M` are in bijection with `M`.
-/
@[simps]
/--
Definition of `uniqueEquiv` / `uniqueEquiv` 的定义

English:
definition uniqueEquiv
  signature: (a : α) [Subsingleton α]
  body: f a
  invFun := single a
  left_inv f := by ext b; simp [Subsingleton.elim b a]
  right_inv x := by simp

中文:
定义 uniqueEquiv
  签名: (a : α) [子单例 α]
  定义体: f a
  invFun := single a
  left_inv f := by ext b; simp [Subsingleton.elim b a]
  right_inv x := by simp
-/
noncomputable def uniqueEquiv (a : α) [Subsingleton α] : (α ->₀ M) ≃ M where
  toFun f := f a
  invFun := single a
  left_inv f := by ext b; simp [Subsingleton.elim b a]
  right_inv x := by simp

-- We want this lemma to fire before `uniqueEquiv_symm_apply`.
/--
lemma `uniqueEquiv_symm_apply_apply` / 引理 `uniqueEquiv_symm_apply_apply`

English:
lemma uniqueEquiv_symm_apply_apply
  given: (a : α) [Subsingleton α] (m : M) (b : α)
  proof: by simp [Subsingleton.elim b a]

中文:
引理 uniqueEquiv_symm_apply_apply
  条件: (a : α) [子单例 α] (m : M) (b : α)
  证明: by simp [Subsingleton.elim b a]
-/
@[simp↓ high] lemma uniqueEquiv_symm_apply_apply (a : α) [Subsingleton α] (m : M) (b : α) :
    (uniqueEquiv a).symm m b = m := by simp [Subsingleton.elim b a]

/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps!, deprecated uniqueEquiv (since := "2026-05-06")]
/--
Definition of `_root_.Equiv.finsuppUnique` / `_root_.Equiv.finsuppUnique` 的定义

English:
definition _root_.Equiv.finsuppUnique
  signature: {ι : Type*} [Unique ι]
  body: Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[simp]

中文:
定义 _root_.等价.finsuppUnique
  签名: {ι : 类型} [唯一 ι]
  定义体: Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[simp]

Depends on / 依赖: Equiv.funUnique, Finsupp, Finsupp.equivFunOnFinite.trans, equivFunOnFinite, funUnique
-/
noncomputable def _root_.Equiv.finsuppUnique {ι : Type*} [Unique ι] : (ι ->₀ M) ≃ M :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[simp]
/--
theorem `equivFunOnFinite_single` / 定理 `equivFunOnFinite_single`

English:
theorem equivFunOnFinite_single
  given: [DecidableEq α] [Finite α] (x : α) (m : M)
  proof: by
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]

中文:
定理 equivFunOnFinite_single
  条件: [DecidableEq α] [有限 α] (x : α) (m : M)
  证明: by
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_eq_pi_single, equivFunOnFinite, single_eq_pi_single
-/
theorem equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m := by
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]
/--
theorem `equivFunOnFinite_symm_single` / 定理 `equivFunOnFinite_symm_single`

English:
theorem equivFunOnFinite_symm_single
  given: [DecidableEq α] [Finite α] (x : α) (m : M)
  proof: by
  rw [← equivFunOnFinite_single]; rw [Equiv.symm_apply_apply]

中文:
定理 equivFunOnFinite_symm_single
  条件: [DecidableEq α] [有限 α] (x : α) (m : M)
  证明: by
  rw [← equivFunOnFinite_single]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, equivFunOnFinite_single, symm_apply_apply
-/
theorem equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFinite_single]; rw [Equiv.symm_apply_apply]

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α ->₀ M) (a : α) (b : M) (i : α)

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: (f : α ->₀ M) (a : α) (b : M)
  body: by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    grind

@[grind =]

中文:
定义 update
  签名: (f : α ->₀ M) (a : α) (b : M)
  定义体: by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    grind

@[grind =]

Depends on / 依赖: Classical, Classical.decEq, Function, Function.update, classical, f.support, f.support.erase, insert, mem_support_toFun, support, update
-/
def update (f : α ->₀ M) (a : α) (b : M) : α ->₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    grind

@[grind =]
/--
theorem `update_apply` / 定理 `update_apply`

English:
theorem update_apply
  given: [DecidableEq α]
  statement: (f.update a b) i = if i = a then b else f i
  proof: by
  delta update Function.update
  grind

@[simp, norm_cast]

中文:
定理 update_apply
  条件: [DecidableEq α]
  结论: (f.update a b) i = if i = a then b else f i
  证明: by
  delta update Function.update
  grind

@[simp, norm_cast]

Depends on / 依赖: Function, Function.update, update
-/
theorem update_apply [DecidableEq α] : (f.update a b) i = if i = a then b else f i := by
  delta update Function.update
  grind

@[simp, norm_cast]
/--
theorem `coe_update` / 定理 `coe_update`

English:
theorem coe_update
  given: [DecidableEq α]
  statement: (f.update a b : α -> M) = Function.update f a b
  proof: by
  grind

@[simp]

中文:
定理 coe_update
  条件: [DecidableEq α]
  结论: (f.update a b : α -> M) = 函数.update f a b
  证明: by
  grind

@[simp]
-/
theorem coe_update [DecidableEq α] : (f.update a b : α -> M) = Function.update f a b := by
  grind

@[simp]
/--
theorem `update_self` / 定理 `update_self`

English:
theorem update_self
  statement: f.update a (f a) = f
  proof: by
  classical
  grind

@[simp]

中文:
定理 update_self
  结论: f.update a (f a) = f
  证明: by
  classical
  grind

@[simp]

Depends on / 依赖: classical
-/
theorem update_self : f.update a (f a) = f := by
  classical
  grind

@[simp]
/--
theorem `zero_update` / 定理 `zero_update`

English:
theorem zero_update
  statement: update 0 a b = single a b
  proof: rfl

中文:
定理 zero_update
  结论: update 0 a b = single a b
  证明: rfl
-/
theorem zero_update : update 0 a b = single a b := rfl

/--
theorem `support_update` / 定理 `support_update`

English:
theorem support_update
  given: [DecidableEq α] [DecidableEq M]
  proof: by
  grind

@[simp]

中文:
定理 support_update
  条件: [DecidableEq α] [DecidableEq M]
  证明: by
  grind

@[simp]
-/
theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  grind

@[simp]
/--
theorem `support_update_zero` / 定理 `support_update_zero`

English:
theorem support_update_zero
  given: [DecidableEq α]
  statement: support (f.update a 0) = f.support.erase a
  proof: by
  grind

中文:
定理 support_update_zero
  条件: [DecidableEq α]
  结论: support (f.update a 0) = f.support.erase a
  证明: by
  grind
-/
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.erase a := by
  grind

variable {b}

/--
theorem `support_update_ne_zero` / 定理 `support_update_ne_zero`

English:
theorem support_update_ne_zero
  given: [DecidableEq α] (h : b != 0)
  proof: by
  grind

中文:
定理 support_update_ne_zero
  条件: [DecidableEq α] (h : b != 0)
  证明: by
  grind
-/
theorem support_update_ne_zero [DecidableEq α] (h : b != 0) :
    support (f.update a b) = insert a f.support := by
  grind

/--
theorem `support_update_subset` / 定理 `support_update_subset`

English:
theorem support_update_subset
  given: [DecidableEq α]
  proof: by
  grind

中文:
定理 support_update_subset
  条件: [DecidableEq α]
  证明: by
  grind
-/
theorem support_update_subset [DecidableEq α] :
    support (f.update a b) subseteq insert a f.support := by
  grind

/--
theorem `update_comm` / 定理 `update_comm`

English:
theorem update_comm
  given: (f : α ->₀ M) {a₁ a₂ : α} (h : a₁ != a₂) (m₁ m₂ : M)
  proof: by
  classical
  grind

中文:
定理 update_comm
  条件: (f : α ->₀ M) {a₁ a₂ : α} (h : a₁ != a₂) (m₁ m₂ : M)
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
theorem update_comm (f : α ->₀ M) {a₁ a₂ : α} (h : a₁ != a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ := by
  classical
  grind

/--
theorem `update_idem` / 定理 `update_idem`

English:
theorem update_idem
  given: (f : α ->₀ M) (a : α) (b c : M)
  proof: by
  classical
  grind

中文:
定理 update_idem
  条件: (f : α ->₀ M) (a : α) (b c : M)
  证明: by
  classical
  grind
-/
@[simp] theorem update_idem (f : α ->₀ M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c := by
  classical
  grind

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (a : α) (f : α ->₀ M)
  body: haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    grind

@[grind =]

中文:
定义 erase
  签名: (a : α) (f : α ->₀ M)
  定义体: haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    grind

@[grind =]

Depends on / 依赖: Classical, Classical.decEq, f.support.erase, mem_support_toFun, support
-/
def erase (a : α) (f : α ->₀ M) : α ->₀ M where
  support :=
    haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    grind

@[grind =]
/--
theorem `erase_apply` / 定理 `erase_apply`

English:
theorem erase_apply
  given: [DecidableEq α] {a a' : α} {f : α ->₀ M}
  proof: by
  rw [erase]; rw [coe_mk]
  simp only [ite_eq_ite]

@[simp]

中文:
定理 erase_apply
  条件: [DecidableEq α] {a a' : α} {f : α ->₀ M}
  证明: by
  rw [erase]; rw [coe_mk]
  simp only [ite_eq_ite]

@[simp]

Depends on / 依赖: coe_mk, ite_eq_ite
-/
theorem erase_apply [DecidableEq α] {a a' : α} {f : α ->₀ M} :
    f.erase a a' = if a' = a then 0 else f a' := by
  rw [erase]; rw [coe_mk]
  simp only [ite_eq_ite]

@[simp]
/--
theorem `support_erase` / 定理 `support_erase`

English:
theorem support_erase
  given: [DecidableEq α] {a : α} {f : α ->₀ M}
  proof: by
  grind

@[simp]

中文:
定理 support_erase
  条件: [DecidableEq α] {a : α} {f : α ->₀ M}
  证明: by
  grind

@[simp]
-/
theorem support_erase [DecidableEq α] {a : α} {f : α ->₀ M} :
    (f.erase a).support = f.support.erase a := by
  grind

@[simp]
/--
theorem `erase_same` / 定理 `erase_same`

English:
theorem erase_same
  given: {a : α} {f : α ->₀ M}
  statement: (f.erase a) a = 0
  proof: by classical grind

@[simp]

中文:
定理 erase_same
  条件: {a : α} {f : α ->₀ M}
  结论: (f.erase a) a = 0
  证明: by classical grind

@[simp]

Depends on / 依赖: classical
-/
theorem erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0 := by classical grind

@[simp]
/--
theorem `erase_ne` / 定理 `erase_ne`

English:
theorem erase_ne
  given: {a a' : α} {f : α ->₀ M} (h : a' != a)
  statement: (f.erase a) a' = f a'
  proof: by classical grind

@[simp]

中文:
定理 erase_ne
  条件: {a a' : α} {f : α ->₀ M} (h : a' != a)
  结论: (f.erase a) a' = f a'
  证明: by classical grind

@[simp]

Depends on / 依赖: classical
-/
theorem erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.erase a) a' = f a' := by classical grind

@[simp]
/--
theorem `erase_single` / 定理 `erase_single`

English:
theorem erase_single
  given: {a : α} {b : M}
  statement: erase a (single a b) = 0
  proof: by classical grind

中文:
定理 erase_single
  条件: {a : α} {b : M}
  结论: erase a (single a b) = 0
  证明: by classical grind

Depends on / 依赖: classical
-/
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by classical grind

/--
theorem `erase_single_ne` / 定理 `erase_single_ne`

English:
theorem erase_single_ne
  given: {a a' : α} {b : M} (h : a != a')
  statement: erase a (single a' b) = single a' b
  proof: by
  classical grind

@[simp]

中文:
定理 erase_single_ne
  条件: {a a' : α} {b : M} (h : a != a')
  结论: erase a (single a' b) = single a' b
  证明: by
  classical grind

@[simp]

Depends on / 依赖: classical
-/
theorem erase_single_ne {a a' : α} {b : M} (h : a != a') : erase a (single a' b) = single a' b := by
  classical grind

@[simp]
/--
theorem `erase_of_notMem_support` / 定理 `erase_of_notMem_support`

English:
theorem erase_of_notMem_support
  given: {f : α ->₀ M} {a} (haf : a ∉ f.support)
  statement: erase a f = f
  proof: by
  classical grind

中文:
定理 erase_of_notMem_support
  条件: {f : α ->₀ M} {a} (haf : a ∉ f.support)
  结论: erase a f = f
  证明: by
  classical grind

Depends on / 依赖: classical
-/
theorem erase_of_notMem_support {f : α ->₀ M} {a} (haf : a ∉ f.support) : erase a f = f := by
  classical grind

/--
theorem `erase_zero` / 定理 `erase_zero`

English:
theorem erase_zero
  given: (a : α)
  statement: erase a (0 : α ->₀ M) = 0
  proof: by
  simp

中文:
定理 erase_zero
  条件: (a : α)
  结论: erase a (0 : α ->₀ M) = 0
  证明: by
  simp
-/
theorem erase_zero (a : α) : erase a (0 : α ->₀ M) = 0 := by
  simp

/--
theorem `erase_eq_update_zero` / 定理 `erase_eq_update_zero`

English:
theorem erase_eq_update_zero
  given: (f : α ->₀ M) (a : α)
  statement: f.erase a = update f a 0
  proof: by classical grind

中文:
定理 erase_eq_update_zero
  条件: (f : α ->₀ M) (a : α)
  结论: f.erase a = update f a 0
  证明: by classical grind

Depends on / 依赖: classical
-/
theorem erase_eq_update_zero (f : α ->₀ M) (a : α) : f.erase a = update f a 0 := by classical grind

-- The name matches `Finset.erase_insert_of_ne`
/--
theorem `erase_update_of_ne` / 定理 `erase_update_of_ne`

English:
theorem erase_update_of_ne
  given: (f : α ->₀ M) {a a' : α} (ha : a != a') (b : M)
  proof: by classical grind

中文:
定理 erase_update_of_ne
  条件: (f : α ->₀ M) {a a' : α} (ha : a != a') (b : M)
  证明: by classical grind

Depends on / 依赖: classical
-/
theorem erase_update_of_ne (f : α ->₀ M) {a a' : α} (ha : a != a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by classical grind

-- not `simp` as `erase_of_notMem_support` can prove this
/--
theorem `erase_idem` / 定理 `erase_idem`

English:
theorem erase_idem
  given: (f : α ->₀ M) (a : α)
  proof: by classical grind

中文:
定理 erase_idem
  条件: (f : α ->₀ M) (a : α)
  证明: by classical grind

Depends on / 依赖: classical
-/
theorem erase_idem (f : α ->₀ M) (a : α) :
    erase a (erase a f) = erase a f := by classical grind

/--
theorem `update_erase_eq_update` / 定理 `update_erase_eq_update`

English:
theorem update_erase_eq_update
  given: (f : α ->₀ M) (a : α) (b : M)
  proof: by classical grind

中文:
定理 update_erase_eq_update
  条件: (f : α ->₀ M) (a : α) (b : M)
  证明: by classical grind
-/
@[simp] theorem update_erase_eq_update (f : α ->₀ M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by classical grind

/--
theorem `erase_update_eq_erase` / 定理 `erase_update_eq_erase`

English:
theorem erase_update_eq_erase
  given: (f : α ->₀ M) (a : α) (b : M)
  proof: by classical grind

中文:
定理 erase_update_eq_erase
  条件: (f : α ->₀ M) (a : α) (b : M)
  证明: by classical grind
-/
@[simp] theorem erase_update_eq_erase (f : α ->₀ M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by classical grind

end Erase

/-! ### Declarations about `mapRange` -/

section MapRange

variable [Zero M] [Zero N] [Zero P]

@[simp]
/--
theorem `mapRange_single` / 定理 `mapRange_single`

English:
theorem mapRange_single
  given: {f : M -> N} {hf : f 0 = 0} {a : α} {b : M}
  proof: by
  classical grind

中文:
定理 mapRange_single
  条件: {f : M -> N} {hf : f 0 = 0} {a : α} {b : M}
  证明: by
  classical grind

Depends on / 依赖: classical
-/
theorem mapRange_single {f : M -> N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) := by
  classical grind

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

/--
theorem `single_of_embDomain_single` / 定理 `single_of_embDomain_single`

English:
theorem single_of_embDomain_single
  statement: (l : α ->₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b != 0)
  proof: by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain]; rw [h]; rw [support_single _ hb]
    have ha : a in Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply_self f l]; rw [h]
      grind
    · exact hc₂

@[simp]

中文:
定理 single_of_embDomain_single
  结论: (l : α ->₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b != 0)
  证明: by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain]; rw [h]; rw [support_single _ hb]
    have ha : a in Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply_self f l]; rw [h]
      grind
    · exact hc₂

@[simp]

Depends on / 依赖: Finset, Finset.map, Finset.mem_map, Finset.mem_singleton, classical, embDomain_apply_self, h_map_support, l.support, mem_map, mem_singleton, support, support_embDomain, support_single
-/
theorem single_of_embDomain_single (l : α ->₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b != 0)
    (h : l.embDomain f = single a b) : exists x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain]; rw [h]; rw [support_single _ hb]
    have ha : a in Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply_self f l]; rw [h]
      grind
    · exact hc₂

@[simp]
/--
theorem `embDomain_single` / 定理 `embDomain_single`

English:
theorem embDomain_single
  given: (f : α ↪ β) (a : α) (m : M)
  proof: by
  classical
    ext b
    by_cases h : b in Set.range f <;> grind

中文:
定理 embDomain_single
  条件: (f : α ↪ β) (a : α) (m : M)
  证明: by
  classical
    ext b
    by_cases h : b in Set.range f <;> grind

Depends on / 依赖: Set.range, classical
-/
theorem embDomain_single (f : α ↪ β) (a : α) (m : M) :
    embDomain f (single a m) = single (f a) m := by
  classical
    ext b
    by_cases h : b in Set.range f <;> grind

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

@[simp]
/--
theorem `zipWith_single_single` / 定理 `zipWith_single_single`

English:
theorem zipWith_single_single
  given: (f : M -> N -> P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N)
  proof: by
  classical
  grind

中文:
定理 zipWith_single_single
  条件: (f : M -> N -> P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N)
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
theorem zipWith_single_single (f : M -> N -> P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N) :
    zipWith f hf (single a m) (single a n) = single a (f m n) := by
  classical
  grind

end ZipWith
end Finsupp
