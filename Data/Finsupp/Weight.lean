/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Group.TypeTags.Pointwise

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require classifying these exponents according to their total sum
`∑ i, f i`, or variants, and this file provides some API for that.

## Weight

We fix a type `σ`, a semiring `R`, an `R`-module `M`,
as well as a function `w : σ → M`. (The important case is `R = ℕ`.)

- `Finsupp.weight` of a finitely supported function `f : σ →₀ R`
  with respect to `w`: it is the sum `∑ (f i) • (w i)`.
  It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight` says that `f s ≤ f.weight w` when `M = ℕ`

- `Finsupp.le_weight_of_ne_zero` says that `w s ≤ f.weight w`
  for `IsOrderedAddMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight_of_ne_zero'` is the same statement for `CanonicallyOrderedAdd M`.

- `NonTorsionWeight`: all values `w s` are nontorsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
  `f = 0` for `NonTorsionWeight w` and `CanonicallyOrderedAddCommMonoid M`.

- For `w : σ → ℕ` and `Finite σ`, `Finsupp.finite_of_nat_weight_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded weight.

## Degree

- `Finsupp.degree f` is the sum of all `f s`, for `s ∈ f.support`.
  The present choice is to have it defined as a plain function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1` when `R` is a semiring.
  This is useful to access the additivity properties of `Finsupp.degree`

- For `Finite σ`, `Finsupp.finite_of_degree_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded degree.


## TODO

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
  both `AddMonoidHom` or both functions.

-/

@[expose] public section

open Module

variable {σ M R : Type*} [Semiring R] (w : σ -> M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]
/--
Definition of `weight` / `weight` 的定义

English:
definition weight
  signature: : (σ ->₀ R) ->+ M
  body: (Finsupp.linearCombination R w).toAddMonoidHom

中文:
定义 weight
  签名: : (σ ->₀ R) ->+ M
  定义体: (Finsupp.linearCombination R w).toAddMonoidHom

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination, toAddMonoidHom
-/
noncomputable def weight : (σ ->₀ R) ->+ M :=
  (Finsupp.linearCombination R w).toAddMonoidHom

/--
theorem `weight_apply` / 定理 `weight_apply`

English:
theorem weight_apply
  given: (f : σ ->₀ R)
  proof: rfl

中文:
定理 weight_apply
  条件: (f : σ ->₀ R)
  证明: rfl
-/
theorem weight_apply (f : σ ->₀ R) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl

/--
theorem `weight_single_index` / 定理 `weight_single_index`

English:
theorem weight_single_index
  given: [DecidableEq σ] (s : σ) (c : M) (f : σ ->₀ R)
  proof: linearCombination_single_index σ M R c s f

中文:
定理 weight_single_index
  条件: [DecidableEq σ] (s : σ) (c : M) (f : σ ->₀ R)
  证明: linearCombination_single_index σ M R c s f

Depends on / 依赖: linearCombination_single_index
-/
theorem weight_single_index [DecidableEq σ] (s : σ) (c : M) (f : σ ->₀ R) :
    weight (Pi.single s c) f = f s • c :=
  linearCombination_single_index σ M R c s f

/--
theorem `weight_single_one_apply` / 定理 `weight_single_one_apply`

English:
theorem weight_single_one_apply
  given: [DecidableEq σ] (s : σ) (f : σ ->₀ R)
  proof: by
  rw [weight_single_index]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 weight_single_one_apply
  条件: [DecidableEq σ] (s : σ) (f : σ ->₀ R)
  证明: by
  rw [weight_single_index]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: mul_one, smul_eq_mul, weight_single_index
-/
theorem weight_single_one_apply [DecidableEq σ] (s : σ) (f : σ ->₀ R) :
    weight (Pi.single s 1) f = f s := by
  rw [weight_single_index]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `weight_single` / 定理 `weight_single`

English:
theorem weight_single
  given: (s : σ) (r : R)
  proof: Finsupp.linearCombination_single _ _ _

中文:
定理 weight_single
  条件: (s : σ) (r : R)
  证明: Finsupp.linearCombination_single _ _ _

Depends on / 依赖: Finsupp, Finsupp.linearCombination_single, linearCombination_single
-/
theorem weight_single (s : σ) (r : R) :
    weight w (Finsupp.single s r) = r • w s :=
  Finsupp.linearCombination_single _ _ _

/--
theorem `weight_eq_sum` / 定理 `weight_eq_sum`

English:
theorem weight_eq_sum
  given: [Fintype σ] (f : σ ->₀ R)
  statement: weight w f = ∑ i, f i • w i
  proof: by
  rw [weight_apply]; rw [f.sum_fintype (fun i c => c • w i) fun _ => zero_smul _ _]

中文:
定理 weight_eq_sum
  条件: [Fintype σ] (f : σ ->₀ R)
  结论: weight w f = ∑ i, f i • w i
  证明: by
  rw [weight_apply]; rw [f.sum_fintype (fun i c => c • w i) fun _ => zero_smul _ _]

Depends on / 依赖: f.sum_fintype, sum_fintype, weight_apply, zero_smul
-/
theorem weight_eq_sum [Fintype σ] (f : σ ->₀ R) : weight w f = ∑ i, f i • w i := by
  rw [weight_apply]; rw [f.sum_fintype (fun i c => c • w i) fun _ => zero_smul _ _]

variable (R) in
/--
Definition of `NonTorsionWeight` / `NonTorsionWeight` 的定义

English:
class NonTorsionWeight
  parameters: (w : σ -> M)
  axioms and operations (1):
    - eq_zero_of_smul_eq_zero({r : R} {s : σ} (h : r • w s = 0)) : r = 0

中文:
类 NonTorsionWeight
  参数: (w : σ -> M)
  公理与运算 (1 个):
    - eq_zero_of_smul_eq_zero({r : R} {s : σ} (h : r • w s = 0)) : r = 0
-/
class NonTorsionWeight (w : σ -> M) : Prop where
  eq_zero_of_smul_eq_zero {r : R} {s : σ} (h : r • w s = 0) : r = 0

variable (R) in
/--
theorem `nonTorsionWeight_of` / 定理 `nonTorsionWeight_of`

English:
theorem nonTorsionWeight_of
  given: [IsDomain R] [IsTorsionFree R M] (hw : forall i : σ, w i != 0)
  proof: by
    rw [smul_eq_zero]; rw [or_iff_not_imp_right] at h
    exact h (hw s)

中文:
定理 nonTorsionWeight_of
  条件: [IsDomain R] [IsTorsionFree R M] (hw : 对任意 i : σ, w i != 0)
  证明: by
    rw [smul_eq_zero]; rw [or_iff_not_imp_right] at h
    exact h (hw s)

Depends on / 依赖: or_iff_not_imp_right, smul_eq_zero
-/
theorem nonTorsionWeight_of [IsDomain R] [IsTorsionFree R M] (hw : forall i : σ, w i != 0) :
    NonTorsionWeight R w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero]; rw [or_iff_not_imp_right] at h
    exact h (hw s)

variable (R) in
/--
theorem `NonTorsionWeight.ne_zero` / 定理 `NonTorsionWeight.ne_zero`

English:
theorem NonTorsionWeight.ne_zero
  given: [Nontrivial R] [NonTorsionWeight R w] (s : σ)
  proof: fun h => by
  rw [← one_smul R (w s)] at h
  apply zero_ne_one.symm (α := R)
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

中文:
定理 NonTorsionWeight.ne_zero
  条件: [Nontrivial R] [NonTorsionWeight R w] (s : σ)
  证明: fun h => by
  rw [← one_smul R (w s)] at h
  apply zero_ne_one.symm (α := R)
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

Depends on / 依赖: NonTorsionWeight, NonTorsionWeight.eq_zero_of_smul_eq_zero, eq_zero_of_smul_eq_zero, one_smul, zero_ne_one, zero_ne_one.symm
-/
theorem NonTorsionWeight.ne_zero [Nontrivial R] [NonTorsionWeight R w] (s : σ) :
    w s != 0 := fun h => by
  rw [← one_smul R (w s)] at h
  apply zero_ne_one.symm (α := R)
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

variable {w} in
/--
lemma `weight_sub_single_add` / 引理 `weight_sub_single_add`

English:
lemma weight_sub_single_add
  given: {f : σ ->₀ Nat} {i : σ} (hi : f i != 0)
  proof: by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weight_apply]
  rw [sum_add_index']; rw [sum_single_index]; rw [one_smul]; rw [weight_apply]
  exacts [zero_smul .., fun _ => zero_smul .., fun _ _ _ => add_smul ..]

中文:
引理 weight_sub_single_add
  条件: {f : σ ->₀ 自然数} {i : σ} (hi : f i != 0)
  证明: by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weight_apply]
  rw [sum_add_index']; rw [sum_single_index]; rw [one_smul]; rw [weight_apply]
  exacts [zero_smul .., fun _ => zero_smul .., fun _ _ _ => add_smul ..]

Depends on / 依赖: add_smul, conv_rhs, exacts, one_smul, sub_add_single_one_cancel, sum_add_index, sum_single_index, weight_apply, zero_smul
-/
lemma weight_sub_single_add {f : σ ->₀ Nat} {i : σ} (hi : f i != 0) :
    (f - single i 1).weight w + w i = f.weight w := by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weight_apply]
  rw [sum_add_index']; rw [sum_single_index]; rw [one_smul]; rw [weight_apply]
  exacts [zero_smul .., fun _ => zero_smul .., fun _ _ _ => add_smul ..]

end AddCommMonoid

section OrderedAddCommMonoid

/--
theorem `le_weight` / 定理 `le_weight`

English:
theorem le_weight
  given: (w : σ -> Nat) {s : σ} (hs : w s != 0) (f : σ ->₀ Nat)
  proof: by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s in f.support
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [notMem_support_iff] at h
   

中文:
定理 le_weight
  条件: (w : σ -> 自然数) {s : σ} (hs : w s != 0) (f : σ ->₀ 自然数)
  证明: by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s in f.support
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [notMem_support_iff] at h
   

Depends on / 依赖: Finset, Finset.sum_eq_add_sum_sdiff_singleton_of_mem, Finsupp, Finsupp.sum, Nat.le_add_right, Nat.le_mul_of_pos_right, Nat.zero_lt_of_ne_zero, classical, f.support, le_add_right, le_mul_of_pos_right, le_trans, notMem_support_iff, sum_eq_add_sum_sdiff_singleton_of_mem, support, weight_apply, zero_le, zero_lt_of_ne_zero
-/
theorem le_weight (w : σ -> Nat) {s : σ} (hs : w s != 0) (f : σ ->₀ Nat) :
    f s <= weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s in f.support
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [notMem_support_iff] at h
    rw [h]
    apply zero_le

variable [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] (w : σ -> M)
  {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Module R M]

variable {w} in
/--
theorem `le_weight_of_ne_zero` / 定理 `le_weight_of_ne_zero`

English:
theorem le_weight_of_ne_zero
  given: (hw : forall s, 0 <= w s) {s : σ} {f : σ ->₀ Nat} (hs : f s != 0)
  proof: by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hs]
exact le_add_of_nonneg_right Finset.sum_nonneg
  

中文:
定理 le_weight_of_ne_zero
  条件: (hw : 对任意 s, 0 <= w s) {s : σ} {f : σ ->₀ 自然数} (hs : f s != 0)
  证明: by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hs]
exact le_add_of_nonneg_right Finset.sum_nonneg
  

Depends on / 依赖: Finset, Finset.sum_eq_add_sum_sdiff_singleton_of_mem, Finset.sum_nonneg, Finsupp, Finsupp.mem_support_iff, Finsupp.sum, Nat.one_le_iff_ne_zero.mpr, classical, le_add_of_nonneg_right, le_smul_of_one_le_left, mem_support_iff, nsmul_nonneg, one_le_iff_ne_zero, sum_eq_add_sum_sdiff_singleton_of_mem, sum_nonneg, weight_apply
-/
theorem le_weight_of_ne_zero (hw : forall s, 0 <= w s) {s : σ} {f : σ ->₀ Nat} (hs : f s != 0) :
    w s <= weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hs]
exact le_add_of_nonneg_right Finset.sum_nonneg
      fun i _ => nsmul_nonneg (hw i) (f i)

end OrderedAddCommMonoid

section CanonicallyOrderedAddCommMonoid

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [CanonicallyOrderedAdd M] (w : σ -> M)

/--
theorem `le_weight_of_ne_zero'` / 定理 `le_weight_of_ne_zero'`

English:
theorem le_weight_of_ne_zero'
  given: {s : σ} {f : σ ->₀ Nat} (hs : f s != 0)
  statement: w s <= weight w f
  proof: le_weight_of_ne_zero (fun _ => zero_le) hs

中文:
定理 le_weight_of_ne_zero'
  条件: {s : σ} {f : σ ->₀ 自然数} (hs : f s != 0)
  结论: w s <= weight w f
  证明: le_weight_of_ne_zero (fun _ => zero_le) hs

Depends on / 依赖: le_weight_of_ne_zero, zero_le
-/
theorem le_weight_of_ne_zero' {s : σ} {f : σ ->₀ Nat} (hs : f s != 0) : w s <= weight w f :=
  le_weight_of_ne_zero (fun _ => zero_le) hs

/--
theorem `weight_eq_zero_iff_eq_zero` / 定理 `weight_eq_zero_iff_eq_zero`

English:
theorem weight_eq_zero_iff_eq_zero
  proof: by
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero Nat w s
    rw [← nonpos_iff_eq_zero]; rw [← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h]; rw [map_zero]

中文:
定理 weight_eq_zero_iff_eq_zero
  证明: by
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero Nat w s
    rw [← nonpos_iff_eq_zero]; rw [← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h]; rw [map_zero]

Depends on / 依赖: Finsupp, Finsupp.coe_zero, NonTorsionWeight, NonTorsionWeight.ne_zero, Pi.zero_apply, coe_zero, le_weight_of_ne_zero, map_zero, ne_zero, nonpos_iff_eq_zero, zero_apply
-/
theorem weight_eq_zero_iff_eq_zero
    (w : σ -> M) [NonTorsionWeight Nat w] {f : σ ->₀ Nat} :
    weight w f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero Nat w s
    rw [← nonpos_iff_eq_zero]; rw [← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h]; rw [map_zero]

/--
theorem `finite_of_nat_weight_le` / 定理 `finite_of_nat_weight_le`

English:
theorem finite_of_nat_weight_le
  given: [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0) (n : Nat)
  proof: by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ ->₀ Nat | weight w d <= n} subseteq ↑(fg.image fun uv => uv.fst) by
    exact Set.Finite.subset (Finset.finite_toSet _) this
  intro d hd
  rw [hfg]
  simp only [Finset.coe_

中文:
定理 finite_of_nat_weight_le
  条件: [Finite σ] (w : σ -> 自然数) (hw : 对任意 x, w x != 0) (n : 自然数)
  证明: by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ ->₀ Nat | weight w d <= n} subseteq ↑(fg.image fun uv => uv.fst) by
    exact Set.Finite.subset (Finset.finite_toSet _) this
  intro d hd
  rw [hfg]
  simp only [Finset.coe_

Depends on / 依赖: Finite, Finset, Finset.antidiagonal, Finset.coe_image, Finset.finite_toSet, Finset.mem_antidiagonal, Finset.mem_coe, Finsupp, Finsupp.equivFunOnFinite.symm, Function, Function.const, Prod.exists, Set.Finite.subset, Set.mem_image, antidiagonal, classical, coe_image, equivFunOnFinite, exists_and_right, exists_eq_right
-/
theorem finite_of_nat_weight_le [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0) (n : Nat) :
    {d : σ ->₀ Nat | weight w d <= n}.Finite := by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ ->₀ Nat | weight w d <= n} subseteq ↑(fg.image fun uv => uv.fst) by
    exact Set.Finite.subset (Finset.finite_toSet _) this
  intro d hd
  rw [hfg]
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_antidiagonal, Prod.exists, exists_and_right, exists_eq_right]
  use Finsupp.equivFunOnFinite.symm (Function.const σ n) - d
  ext x
  dsimp at hd
  grw [← le_weight _ (hw x)] at hd
  simp [*]

/--
theorem `finite_of_nat_weight_lt` / 定理 `finite_of_nat_weight_lt`

English:
theorem finite_of_nat_weight_lt
  given: [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0) (n : Nat)
  proof: Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

中文:
定理 finite_of_nat_weight_lt
  条件: [Finite σ] (w : σ -> 自然数) (hw : 对任意 x, w x != 0) (n : 自然数)
  证明: Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

Depends on / 依赖: Finite, Set.Finite.subset, finite_of_nat_weight_le, subset
-/
theorem finite_of_nat_weight_lt [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0) (n : Nat) :
    {d : σ ->₀ Nat | weight w d < n}.Finite :=
  Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

/--
theorem `finite_of_nat_weight_eq` / 定理 `finite_of_nat_weight_eq`

English:
theorem finite_of_nat_weight_eq
  given: [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0) (n : Nat)
  proof: Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

中文:
定理 finite_of_nat_weight_eq
  条件: [Finite σ] (w : σ -> 自然数) (hw : 对任意 x, w x != 0) (n : 自然数)
  证明: Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

Depends on / 依赖: Finite, Set.Finite.subset, finite_of_nat_weight_le, subset
-/
theorem finite_of_nat_weight_eq [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0) (n : Nat) :
    {d : σ ->₀ Nat | weight w d = n}.Finite :=
  Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

end CanonicallyOrderedAddCommMonoid

variable {R : Type*} [AddCommMonoid R]

/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: : (σ ->₀ R) ->+ R where
  body: fun d => ∑ i in d.support, d i
  map_zero' := by simp
  map_add' := fun _ _ => sum_add_index' (h := fun _ => id) (congrFun rfl) fun _ _ => congrFun rfl

中文:
定义 degree
  签名: : (σ ->₀ R) ->+ R where
  定义体: fun d => ∑ i in d.support, d i
  map_zero' := by simp
  map_add' := fun _ _ => sum_add_index' (h := fun _ => id) (congrFun rfl) fun _ _ => congrFun rfl

Depends on / 依赖: d.support, support
-/
def degree : (σ ->₀ R) ->+ R where
  toFun := fun d => ∑ i in d.support, d i
  map_zero' := by simp
  map_add' := fun _ _ => sum_add_index' (h := fun _ => id) (congrFun rfl) fun _ _ => congrFun rfl

/--
theorem `degree_apply` / 定理 `degree_apply`

English:
theorem degree_apply
  given: (d : σ ->₀ R)
  statement: degree d = ∑ i in d.support, d i
  proof: rfl

中文:
定理 degree_apply
  条件: (d : σ ->₀ R)
  结论: degree d = ∑ i in d.support, d i
  证明: rfl
-/
theorem degree_apply (d : σ ->₀ R) : degree d = ∑ i in d.support, d i := rfl

/--
theorem `degree_eq_sum` / 定理 `degree_eq_sum`

English:
theorem degree_eq_sum
  given: [Fintype σ] (f : σ ->₀ R)
  statement: f.degree = ∑ i, f i
  proof: by
  rw [degree_apply]; rw [Finset.sum_subset] <;> simp

@[simp]

中文:
定理 degree_eq_sum
  条件: [Fintype σ] (f : σ ->₀ R)
  结论: f.degree = ∑ i, f i
  证明: by
  rw [degree_apply]; rw [Finset.sum_subset] <;> simp

@[simp]

Depends on / 依赖: Finset, Finset.sum_subset, degree_apply, sum_subset
-/
theorem degree_eq_sum [Fintype σ] (f : σ ->₀ R) : f.degree = ∑ i, f i := by
  rw [degree_apply]; rw [Finset.sum_subset] <;> simp

@[simp]
/--
theorem `degree_single` / 定理 `degree_single`

English:
theorem degree_single
  given: (a : σ) (r : R)
  statement: (Finsupp.single a r).degree = r
  proof: Finsupp.sum_single_index (h := fun _ => id) rfl

中文:
定理 degree_single
  条件: (a : σ) (r : R)
  结论: (Finsupp.single a r).degree = r
  证明: Finsupp.sum_single_index (h := fun _ => id) rfl

Depends on / 依赖: Finsupp, Finsupp.sum_single_index, sum_single_index
-/
theorem degree_single (a : σ) (r : R) : (Finsupp.single a r).degree = r :=
  Finsupp.sum_single_index (h := fun _ => id) rfl

/--
lemma `degree_eq_zero_iff` / 引理 `degree_eq_zero_iff`

English:
lemma degree_eq_zero_iff
  statement: {R : Type*}
  proof: by
  simp only [degree_apply, Finset.sum_eq_zero_iff, mem_support_iff, ne_eq, _root_.not_imp_self,
    DFunLike.ext_iff, coe_zero, Pi.zero_apply]

中文:
引理 degree_eq_zero_iff
  结论: {R : 类型}
  证明: by
  simp only [degree_apply, Finset.sum_eq_zero_iff, mem_support_iff, ne_eq, _root_.not_imp_self,
    DFunLike.ext_iff, coe_zero, Pi.zero_apply]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Finset, Finset.sum_eq_zero_iff, Pi.zero_apply, _root_, _root_.not_imp_self, coe_zero, degree_apply, ext_iff, mem_support_iff, ne_eq, not_imp_self, sum_eq_zero_iff, zero_apply
-/
lemma degree_eq_zero_iff {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
    (d : σ ->₀ R) :
    degree d = 0 ↔ d = 0 := by
  simp only [degree_apply, Finset.sum_eq_zero_iff, mem_support_iff, ne_eq, _root_.not_imp_self,
    DFunLike.ext_iff, coe_zero, Pi.zero_apply]

/--
theorem `le_degree` / 定理 `le_degree`

English:
theorem le_degree
  statement: {R : Type*}
  proof: by
  by_cases h : s in f.support
  · exact Finset.single_le_sum_of_canonicallyOrdered h
  · simp only [notMem_support_iff] at h
    simp only [h, zero_le]

中文:
定理 le_degree
  结论: {R : 类型}
  证明: by
  by_cases h : s in f.support
  · exact Finset.single_le_sum_of_canonicallyOrdered h
  · simp only [notMem_support_iff] at h
    simp only [h, zero_le]

Depends on / 依赖: Finset, Finset.single_le_sum_of_canonicallyOrdered, f.support, notMem_support_iff, single_le_sum_of_canonicallyOrdered, support, zero_le
-/
theorem le_degree {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
    (s : σ) (f : σ ->₀ R) :
    f s <= degree f := by
  by_cases h : s in f.support
  · exact Finset.single_le_sum_of_canonicallyOrdered h
  · simp only [notMem_support_iff] at h
    simp only [h, zero_le]

/--
theorem `degree_eq_weight_one` / 定理 `degree_eq_weight_one`

English:
theorem degree_eq_weight_one
  given: {R : Type*} [Semiring R]
  proof: by
  ext d
  simp [weight_apply, smul_eq_mul, mul_one]

中文:
定理 degree_eq_weight_one
  条件: {R : 类型} [Semiring R]
  证明: by
  ext d
  simp [weight_apply, smul_eq_mul, mul_one]

Depends on / 依赖: mul_one, smul_eq_mul, weight, weight_apply
-/
theorem degree_eq_weight_one {R : Type*} [Semiring R] :
    degree (R := R) (σ := σ) = weight (fun _ => 1) := by
  ext d
  simp [weight_apply, smul_eq_mul, mul_one]

/--
theorem `finite_of_degree_le` / 定理 `finite_of_degree_le`

English:
theorem finite_of_degree_le
  given: [Finite σ] (n : Nat)
  proof: by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

中文:
定理 finite_of_degree_le
  条件: [Finite σ] (n : 自然数)
  证明: by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

Depends on / 依赖: Function, Function.const, Function.const_apply, const_apply, degree_eq_weight_one, finite_of_nat_weight_le, ne_eq, not_false_eq_true, one_ne_zero, simp_rw
-/
theorem finite_of_degree_le [Finite σ] (n : Nat) :
    {f : σ ->₀ Nat | degree f <= n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

/--
lemma `finite_of_degree_lt` / 引理 `finite_of_degree_lt`

English:
lemma finite_of_degree_lt
  given: [Finite σ] (n : Nat)
  statement: {f : σ ->₀ Nat | degree f < n}.Finite
  proof: Set.Finite.subset (finite_of_degree_le n) (by grind)

中文:
引理 finite_of_degree_lt
  条件: [Finite σ] (n : 自然数)
  结论: {f : σ ->₀ 自然数 | degree f < n}.Finite
  证明: Set.Finite.subset (finite_of_degree_le n) (by grind)

Depends on / 依赖: Finite, Set.Finite.subset, finite_of_degree_le, subset
-/
lemma finite_of_degree_lt [Finite σ] (n : Nat) : {f : σ ->₀ Nat | degree f < n}.Finite :=
  Set.Finite.subset (finite_of_degree_le n) (by grind)

/--
lemma `finite_of_degree_eq` / 引理 `finite_of_degree_eq`

English:
lemma finite_of_degree_eq
  given: [Finite σ] (n : Nat)
  statement: {f : σ ->₀ Nat | f.degree = n}.Finite
  proof: Set.Finite.subset (finite_of_degree_le n) (by grind)

中文:
引理 finite_of_degree_eq
  条件: [Finite σ] (n : 自然数)
  结论: {f : σ ->₀ 自然数 | f.degree = n}.Finite
  证明: Set.Finite.subset (finite_of_degree_le n) (by grind)

Depends on / 依赖: Finite, Set.Finite.subset, finite_of_degree_le, subset
-/
lemma finite_of_degree_eq [Finite σ] (n : Nat) : {f : σ ->₀ Nat | f.degree = n}.Finite :=
  Set.Finite.subset (finite_of_degree_le n) (by grind)

/--
lemma `range_single_one` / 引理 `range_single_one`

English:
lemma range_single_one
  proof: by
  refine subset_antisymm ?_ ?_
  · simp [Set.range_subset_iff]
  · intro p (hp : p.sum (fun a k => k) = 1)
    obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hp
    use a

@[simp]

中文:
引理 range_single_one
  证明: by
  refine subset_antisymm ?_ ?_
  · simp [Set.range_subset_iff]
  · intro p (hp : p.sum (fun a k => k) = 1)
    obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hp
    use a

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_eq_one_iff, Set.range_subset_iff, p.sum, range_subset_iff, subset_antisymm, sum_eq_one_iff
-/
lemma range_single_one :
    Set.range (fun a : σ => Finsupp.single a 1) = { d | d.degree = 1 } := by
  refine subset_antisymm ?_ ?_
  · simp [Set.range_subset_iff]
  · intro p (hp : p.sum (fun a k => k) = 1)
    obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hp
    use a

@[simp]
/--
theorem `degree_mapDomain` / 定理 `degree_mapDomain`

English:
theorem degree_mapDomain
  given: {τ : Type*} (f : σ -> τ) [AddCommMonoid M] (x : σ ->₀ M)
  proof: by
  simp [mapDomain, sum]
  dsimp [degree_apply]

@[deprecated (since := "2026-04-27")]
alias degree_mapDomain_eq_of_subsingletonAddUnits := degree_mapDomain

中文:
定理 degree_mapDomain
  条件: {τ : 类型} (f : σ -> τ) [AddCommMonoid M] (x : σ ->₀ M)
  证明: by
  simp [mapDomain, sum]
  dsimp [degree_apply]

@[deprecated (since := "2026-04-27")]
alias degree_mapDomain_eq_of_subsingletonAddUnits := degree_mapDomain

Depends on / 依赖: degree_apply, mapDomain
-/
theorem degree_mapDomain {τ : Type*} (f : σ -> τ) [AddCommMonoid M] (x : σ ->₀ M) :
    degree (x.mapDomain f) = degree x := by
  simp [mapDomain, sum]
  dsimp [degree_apply]

@[deprecated (since := "2026-04-27")]
alias degree_mapDomain_eq_of_subsingletonAddUnits := degree_mapDomain

set_option backward.isDefEq.respectTransparency false in
/--
theorem `degree_comapDomain_le_of_canonicallyOrderedAdd` / 定理 `degree_comapDomain_le_of_canonicallyOrderedAdd`

English:
theorem degree_comapDomain_le_of_canonicallyOrderedAdd
  statement: {τ : Type*} {f : σ -> τ} [AddCommMonoid M]
  proof: by
  classical
  simpa [degree, comapDomain, Finset.sum_preimage' f x.support hf x] using
    Finset.sum_le_sum_of_subset (Finset.filter_subset ..)

中文:
定理 degree_comapDomain_le_of_canonicallyOrderedAdd
  结论: {τ : 类型} {f : σ -> τ} [AddCommMonoid M]
  证明: by
  classical
  simpa [degree, comapDomain, Finset.sum_preimage' f x.support hf x] using
    Finset.sum_le_sum_of_subset (Finset.filter_subset ..)

Depends on / 依赖: Finset, Finset.filter_subset, Finset.sum_le_sum_of_subset, Finset.sum_preimage, classical, comapDomain, degree, filter_subset, sum_le_sum_of_subset, sum_preimage, support, x.support
-/
theorem degree_comapDomain_le_of_canonicallyOrderedAdd {τ : Type*} {f : σ -> τ} [AddCommMonoid M]
    [PartialOrder M] [CanonicallyOrderedAdd M] {x : τ ->₀ M} (hf : Set.InjOn f (f ⁻¹' x.support)) :
      degree (x.comapDomain f hf) <= degree x := by
  classical
  simpa [degree, comapDomain, Finset.sum_preimage' f x.support hf x] using
    Finset.sum_le_sum_of_subset (Finset.filter_subset ..)

/--
lemma `degree_mono` / 引理 `degree_mono`

English:
lemma degree_mono
  given: {R : Type*} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
  proof: fun _ _ e =>
    (Finset.sum_le_sum_of_subset (support_mono e)).trans (Finset.sum_le_sum fun _ _ => e _)

中文:
引理 degree_mono
  条件: {R : 类型} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
  证明: fun _ _ e =>
    (Finset.sum_le_sum_of_subset (support_mono e)).trans (Finset.sum_le_sum fun _ _ => e _)
-/
lemma degree_mono {R : Type*} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R] :
    Monotone (Finsupp.degree (σ := σ) (R := R)) :=
  fun _ _ e =>
    (Finset.sum_le_sum_of_subset (support_mono e)).trans (Finset.sum_le_sum fun _ _ => e _)

/--
lemma `exists_le_degree_eq` / 引理 `exists_le_degree_eq`

English:
lemma exists_le_degree_eq
  given: {σ : Type*} (f : σ ->₀ Nat) (n : Nat) (hn : n <= f.degree)
  proof: by
  induction n with
  | zero => simp [degree_eq_zero_iff]
  | succ n IH =>
    obtain ⟨g, hgf, rfl⟩ := IH (by lia)
    obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    exact ⟨g + .single i 1, add_le_add_right (by simp; grind) _, by simp⟩

中文:
引理 exists_le_degree_eq
  条件: {σ : 类型} (f : σ ->₀ 自然数) (n : 自然数) (hn : n <= f.degree)
  证明: by
  induction n with
  | zero => simp [degree_eq_zero_iff]
  | succ n IH =>
    obtain ⟨g, hgf, rfl⟩ := IH (by lia)
    obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    exact ⟨g + .single i 1, add_le_add_right (by simp; grind) _, by simp⟩

Depends on / 依赖: Nonempty, add_le_add_right, degree_eq_zero_iff, f.support.Nonempty, le_iff_exists_add, le_iff_exists_add.mp, single, support
-/
lemma exists_le_degree_eq {σ : Type*} (f : σ ->₀ Nat) (n : Nat) (hn : n <= f.degree) :
    exists g <= f, g.degree = n := by
  induction n with
  | zero => simp [degree_eq_zero_iff]
  | succ n IH =>
    obtain ⟨g, hgf, rfl⟩ := IH (by lia)
    obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    exact ⟨g + .single i 1, add_le_add_right (by simp; grind) _, by simp⟩

open scoped Pointwise in
/--
lemma `degree_preimage_add` / 引理 `degree_preimage_add`

English:
lemma degree_preimage_add
  given: {σ : Type*} (s t : Set Nat)
  proof: by
  refine (Set.preimage_add_preimage_subset ..).antisymm' ?_
  rintro f ⟨m, hm, n, hn, e : m + n = _⟩
  obtain ⟨g, hgf, rfl⟩ := exists_le_degree_eq f m (by grind)
  obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
  exact Set.add_mem_add hm (by simp_all)

中文:
引理 degree_preimage_add
  条件: {σ : 类型} (s t : Set 自然数)
  证明: by
  refine (Set.preimage_add_preimage_subset ..).antisymm' ?_
  rintro f ⟨m, hm, n, hn, e : m + n = _⟩
  obtain ⟨g, hgf, rfl⟩ := exists_le_degree_eq f m (by grind)
  obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
  exact Set.add_mem_add hm (by simp_all)

Depends on / 依赖: Set.add_mem_add, Set.preimage_add_preimage_subset, add_mem_add, antisymm, degree, exists_le_degree_eq, le_iff_exists_add, le_iff_exists_add.mp, preimage_add_preimage_subset
-/
lemma degree_preimage_add {σ : Type*} (s t : Set Nat) :
    degree (σ := σ) ⁻¹' (s + t) = degree (σ := σ) ⁻¹' s + degree (σ := σ) ⁻¹' t := by
  refine (Set.preimage_add_preimage_subset ..).antisymm' ?_
  rintro f ⟨m, hm, n, hn, e : m + n = _⟩
  obtain ⟨g, hgf, rfl⟩ := exists_le_degree_eq f m (by grind)
  obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
  exact Set.add_mem_add hm (by simp_all)

open scoped Pointwise in
/--
lemma `degree_preimage_nsmul` / 引理 `degree_preimage_nsmul`

English:
lemma degree_preimage_nsmul
  given: {σ : Type*} (s : Set Nat) (n : Nat) (hn : n != 0)
  proof: by
  obtain (_ | n) := n; · contradiction
  induction n <;> simp_all [succ_nsmul, degree_preimage_add]

中文:
引理 degree_preimage_nsmul
  条件: {σ : 类型} (s : Set 自然数) (n : 自然数) (hn : n != 0)
  证明: by
  obtain (_ | n) := n; · contradiction
  induction n <;> simp_all [succ_nsmul, degree_preimage_add]

Depends on / 依赖: degree, degree_preimage_add, succ_nsmul
-/
lemma degree_preimage_nsmul {σ : Type*} (s : Set Nat) (n : Nat) (hn : n != 0) :
    degree (σ := σ) ⁻¹' (n • s) = n • degree (σ := σ) ⁻¹' s := by
  obtain (_ | n) := n; · contradiction
  induction n <;> simp_all [succ_nsmul, degree_preimage_add]

open scoped Pointwise in
/--
lemma `nsmul_single_one_image` / 引理 `nsmul_single_one_image`

English:
lemma nsmul_single_one_image
  given: {α : Type*} {n : Nat} {s : Set α}
  proof: by
  classical
  induction n with
  | zero => aesop (add simp degree_eq_zero_iff)
  | succ n ih =>
    rw [succ_nsmul]; rw [ih]
    refine subset_antisymm ?_ fun f ⟨f_deg, f_supp⟩ => ?_
    · simp [Set.subset_def, Set.mem_add, @forall_comm (α ->₀ Nat)]; grind
    obtain ⟨i, hi⟩ : f.support.Nonempty 

中文:
引理 nsmul_single_one_image
  条件: {α : 类型} {n : 自然数} {s : Set α}
  证明: by
  classical
  induction n with
  | zero => aesop (add simp degree_eq_zero_iff)
  | succ n ih =>
    rw [succ_nsmul]; rw [ih]
    refine subset_antisymm ?_ fun f ⟨f_deg, f_supp⟩ => ?_
    · simp [Set.subset_def, Set.mem_add, @forall_comm (α ->₀ Nat)]; grind
    obtain ⟨i, hi⟩ : f.support.Nonempty 

Depends on / 依赖: Nat.one_le_iff_ne_zero, Nonempty, Set.mem_add, Set.subset_def, classical, degree_eq_zero_iff, f.support.Nonempty, f_deg, f_supp, forall_comm, hx.symm, le_iff_exists_add, mem_add, one_le_iff_ne_zero, single, subset_antisymm, subset_def, succ_nsmul, support
-/
lemma nsmul_single_one_image {α : Type*} {n : Nat} {s : Set α} :
    n • (single · 1) '' s = {x : α ->₀ Nat | x.degree = n ∧ ↑x.support subseteq s} := by
  classical
  induction n with
  | zero => aesop (add simp degree_eq_zero_iff)
  | succ n ih =>
    rw [succ_nsmul]; rw [ih]
    refine subset_antisymm ?_ fun f ⟨f_deg, f_supp⟩ => ?_
    · simp [Set.subset_def, Set.mem_add, @forall_comm (α ->₀ Nat)]; grind
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    obtain ⟨x, hx⟩ := le_iff_exists_add'.mp
      (show single i 1 <= f by simpa [Nat.one_le_iff_ne_zero] using hi)
    exact ⟨x, by aesop (add simp Set.subset_def), _, ⟨_, f_supp (by simp_all), rfl⟩, hx.symm⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Pointwise in
/--
theorem `image_pow_eq_finsuppProd_image` / 定理 `image_pow_eq_finsuppProd_image`

English:
theorem image_pow_eq_finsuppProd_image
  given: {α β : Type*} [CommMonoid β] {f : α -> β} {n} {s : Set α}
  proof: by
  classical
  suffices forall (s : Set (α ->₀ Nat)), ((·.prod (f · ^ ·)) '' s) ^ n = (·.prod (f · ^ ·)) '' (n • s) by
    simp [← nsmul_single_one_image, ← this, Set.image_image]
  intro s
  refine (Set.image_pow (⟨⟨(·.prod (f · ^ ·)) ∘ Multiplicative.toAdd, by simp⟩,
    by simp [Finsupp.prod_ad

中文:
定理 image_pow_eq_finsuppProd_image
  条件: {α β : 类型} [CommMonoid β] {f : α -> β} {n} {s : Set α}
  证明: by
  classical
  suffices forall (s : Set (α ->₀ Nat)), ((·.prod (f · ^ ·)) '' s) ^ n = (·.prod (f · ^ ·)) '' (n • s) by
    simp [← nsmul_single_one_image, ← this, Set.image_image]
  intro s
  refine (Set.image_pow (⟨⟨(·.prod (f · ^ ·)) ∘ Multiplicative.toAdd, by simp⟩,
    by simp [Finsupp.prod_ad

Depends on / 依赖: Finsupp, Finsupp.prod_add_index, Function, Function.comp_apply, Multiplicative, Multiplicative.toAdd, Set.image_comp, Set.image_id, Set.image_image, Set.image_pow, classical, comp_apply, image_comp, image_id, image_image, image_pow, nsmul_single_one_image, pow_add, prod_add_index, symm.trans
-/
theorem image_pow_eq_finsuppProd_image {α β : Type*} [CommMonoid β] {f : α -> β} {n} {s : Set α} :
    (f '' s) ^ n = (·.prod (f · ^ ·)) '' {x : α ->₀ Nat | x.degree = n ∧ ↑x.support subseteq s} := by
  classical
  suffices forall (s : Set (α ->₀ Nat)), ((·.prod (f · ^ ·)) '' s) ^ n = (·.prod (f · ^ ·)) '' (n • s) by
    simp [← nsmul_single_one_image, ← this, Set.image_image]
  intro s
  refine (Set.image_pow (⟨⟨(·.prod (f · ^ ·)) ∘ Multiplicative.toAdd, by simp⟩,
    by simp [Finsupp.prod_add_index, pow_add]⟩ : Multiplicative (α ->₀ Nat) ->* β) _ _).symm.trans ?_
  simp [-Function.comp_apply, Set.image_comp, show Multiplicative.toAdd '' s = s from
    Set.image_id _]

end Finsupp
