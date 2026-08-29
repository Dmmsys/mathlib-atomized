/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.WittVector.Truncated

/-!
# Leading terms of Witt vector multiplication

The goal of this file is to study the leading terms of the formula for the `n+1`st coefficient
of a product of Witt vectors `x` and `y` over a ring of characteristic `p`.
We aim to isolate the `n+1`st coefficients of `x` and `y`, and express the rest of the product
in terms of a function of the lower coefficients.

For most of this file we work with terms of type `MvPolynomial (Fin 2 × ℕ) ℤ`.
We will eventually evaluate them in `k`, but first we must take care of a calculation
that needs to happen in characteristic 0.

## Main declarations

* `WittVector.nth_mul_coeff`: expresses the coefficient of a product of Witt vectors
  in terms of the previous coefficients of the multiplicands.

-/

@[expose] public section


noncomputable section

namespace WittVector

variable (p : Nat) [hp : Fact p.Prime]
variable {k : Type*} [CommRing k]

local notation "𝕎" => WittVector p

local notation "𝕄" => MvPolynomial (Fin 2 × Nat) Int

open Finset MvPolynomial

/--
Definition of `wittPolyProd` / `wittPolyProd` 的定义

English:
definition wittPolyProd
  signature: (n : Nat)
  body: rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int n)

中文:
定义 wittPolyProd
  签名: (n : 自然数)
  定义体: rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int n)

Depends on / 依赖: Prod.mk, wittPolynomial
-/
def wittPolyProd (n : Nat) : 𝕄 :=
  rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int n)

/--
theorem `wittPolyProd_vars` / 定理 `wittPolyProd_vars`

English:
theorem wittPolyProd_vars
  given: (n : Nat)
  statement: (wittPolyProd p n).vars subseteq univ ×ˢ range (n + 1)
  proof: by
  rw [wittPolyProd]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_rename _ _) ?_
    simp [wittPolynomial_vars, image_subset_iff]

中文:
定理 wittPolyProd_vars
  条件: (n : 自然数)
  结论: (wittPolyProd p n).vars subseteq univ ×ˢ range (n + 1)
  证明: by
  rw [wittPolyProd]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_rename _ _) ?_
    simp [wittPolynomial_vars, image_subset_iff]

Depends on / 依赖: Subset, Subset.trans, image_subset_iff, union_subset, vars_mul, vars_rename, wittPolyProd, wittPolynomial_vars
-/
theorem wittPolyProd_vars (n : Nat) : (wittPolyProd p n).vars subseteq univ ×ˢ range (n + 1) := by
  rw [wittPolyProd]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_rename _ _) ?_
    simp [wittPolynomial_vars, image_subset_iff]

/--
Definition of `wittPolyProdRemainder` / `wittPolyProdRemainder` 的定义

English:
definition wittPolyProdRemainder
  signature: (n : Nat)
  body: ∑ i in range n, (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i)

中文:
定义 wittPolyProdRemainder
  签名: (n : 自然数)
  定义体: ∑ i in range n, (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i)

Depends on / 依赖: wittMul
-/
def wittPolyProdRemainder (n : Nat) : 𝕄 :=
  ∑ i in range n, (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i)

/--
theorem `wittPolyProdRemainder_vars` / 定理 `wittPolyProdRemainder_vars`

English:
theorem wittPolyProdRemainder_vars
  given: (n : Nat)
  proof: by
  rw [wittPolyProdRemainder]
  refine Subset.trans (vars_sum_subset _ _) ?_
  rw [biUnion_subset]
  intro x hx
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_
  · apply Subset.trans (vars_pow _ _)
    have : (p : 𝕄) = C (p : Int) := by simp only [Int.cast_natCast, eq_intCast]
    

中文:
定理 wittPolyProdRemainder_vars
  条件: (n : 自然数)
  证明: by
  rw [wittPolyProdRemainder]
  refine Subset.trans (vars_sum_subset _ _) ?_
  rw [biUnion_subset]
  intro x hx
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_
  · apply Subset.trans (vars_pow _ _)
    have : (p : 𝕄) = C (p : Int) := by simp only [Int.cast_natCast, eq_intCast]
    

Depends on / 依赖: Int.cast_natCast, Subset, Subset.refl, Subset.trans, biUnion_subset, cast_natCast, empty_subset, eq_intCast, h.symm, product_subset_product, union_subset, vars_C, vars_mul, vars_pow, vars_sum_subset, wittMul_vars, wittPolyProdRemainder
-/
theorem wittPolyProdRemainder_vars (n : Nat) :
    (wittPolyProdRemainder p n).vars subseteq univ ×ˢ range n := by
  rw [wittPolyProdRemainder]
  refine Subset.trans (vars_sum_subset _ _) ?_
  rw [biUnion_subset]
  intro x hx
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_
  · apply Subset.trans (vars_pow _ _)
    have : (p : 𝕄) = C (p : Int) := by simp only [Int.cast_natCast, eq_intCast]
    rw [this]; rw [vars_C]
    apply empty_subset
  · apply Subset.trans (vars_pow _ _)
    apply Subset.trans (wittMul_vars _ _)
    apply product_subset_product (Subset.refl _)
    simpa using hx

/--
Definition of `remainder` / `remainder` 的定义

English:
definition remainder
  signature: (n : Nat)
  body: (∑ x in range (n + 1),
    (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : Int) ^ x))) *
   ∑ x in range (n + 1),
    (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : Int) ^ x))

中文:
定义 remainder
  签名: (n : 自然数)
  定义体: (∑ x in range (n + 1),
    (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : Int) ^ x))) *
   ∑ x in range (n + 1),
    (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : Int) ^ x))

Depends on / 依赖: Finsupp, Finsupp.single, Prod.mk, monomial, single
-/
def remainder (n : Nat) : 𝕄 :=
  (∑ x in range (n + 1),
    (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : Int) ^ x))) *
   ∑ x in range (n + 1),
    (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : Int) ^ x))

/--
theorem `remainder_vars` / 定理 `remainder_vars`

English:
theorem remainder_vars
  given: (n : Nat)
  statement: (remainder p n).vars subseteq univ ×ˢ range (n + 1)
  proof: by
  rw [remainder]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_sum_subset _ _) ?_
    rw [biUnion_subset]
    intro x hx
    rw [rename_monomial]; rw [vars_monomial]; rw [Finsupp.mapDomain_single]
    · apply Subset.trans Finsupp.support_single_

中文:
定理 remainder_vars
  条件: (n : 自然数)
  结论: (remainder p n).vars subseteq univ ×ˢ range (n + 1)
  证明: by
  rw [remainder]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_sum_subset _ _) ?_
    rw [biUnion_subset]
    intro x hx
    rw [rename_monomial]; rw [vars_monomial]; rw [Finsupp.mapDomain_single]
    · apply Subset.trans Finsupp.support_single_

Depends on / 依赖: Finsupp, Finsupp.mapDomain_single, Finsupp.support_single_subset, Subset, Subset.trans, biUnion_subset, hp.out.ne_zero, mapDomain_single, mem_range, mem_range.mp, mod_cast, ne_zero, pow_ne_zero, remainder, rename_monomial, support_single_subset, union_subset, vars_monomial, vars_mul, vars_sum_subset
-/
theorem remainder_vars (n : Nat) : (remainder p n).vars subseteq univ ×ˢ range (n + 1) := by
  rw [remainder]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_sum_subset _ _) ?_
    rw [biUnion_subset]
    intro x hx
    rw [rename_monomial]; rw [vars_monomial]; rw [Finsupp.mapDomain_single]
    · apply Subset.trans Finsupp.support_single_subset
      simpa using mem_range.mp hx
    · apply pow_ne_zero
      exact mod_cast hp.out.ne_zero

/--
Definition of `polyOfInterest` / `polyOfInterest` 的定义

English:
definition polyOfInterest
  signature: (n : Nat)
  body: wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
    X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) -
    X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1))

中文:
定义 polyOf整数erest
  签名: (n : 自然数)
  定义体: wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
    X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) -
    X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1))

Depends on / 依赖: Prod.mk, wittMul, wittPolynomial
-/
def polyOfInterest (n : Nat) : 𝕄 :=
  wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
    X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) -
    X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1))

/--
theorem `mul_polyOfInterest_aux1` / 定理 `mul_polyOfInterest_aux1`

English:
theorem mul_polyOfInterest_aux1
  given: (n : Nat)
  proof: by
  simp only [wittPolyProd]
  convert! wittStructureInt_prop p (X (0 : Fin 2) * X 1) n using 1
  · simp only [wittPolynomial, wittMul]
    rw [map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
     

中文:
定理 mul_polyOf整数erest_aux1
  条件: (n : 自然数)
  证明: by
  simp only [wittPolyProd]
  convert! wittStructureInt_prop p (X (0 : Fin 2) * X 1) n using 1
  · simp only [wittPolynomial, wittMul]
    rw [map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
     

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.single_eq_same, Finsupp.support_eq_singleton, Int.cast_natCast, Int.cast_pow, and_true, cast_natCast, cast_pow, convert, eq_intCast, hp.out.ne_zero, map_mul, map_sum, ne_zero, pow_ne_zero, prod_singleton, single, single_eq_same, support
-/
theorem mul_polyOfInterest_aux1 (n : Nat) :
    ∑ i in range (n + 1), (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i) = wittPolyProd p n := by
  simp only [wittPolyProd]
  convert! wittStructureInt_prop p (X (0 : Fin 2) * X 1) n using 1
  · simp only [wittPolynomial, wittMul]
    rw [map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
      simp only [and_true, Finsupp.single_eq_same, Ne]
      exact pow_ne_zero _ hp.out.ne_zero
    simp only [bind₁_monomial, hsupp, Int.cast_natCast, prod_singleton, eq_intCast,
      Finsupp.single_eq_same, Int.cast_pow]
  · simp only [map_mul, bind₁_X_right]

/--
theorem `mul_polyOfInterest_aux2` / 定理 `mul_polyOfInterest_aux2`

English:
theorem mul_polyOfInterest_aux2
  given: (n : Nat)
  proof: by
  convert! mul_polyOfInterest_aux1 p n
  rw [sum_range_succ]; rw [add_comm]; rw [Nat.sub_self]; rw [pow_zero]; rw [pow_one]
  rfl

中文:
定理 mul_polyOf整数erest_aux2
  条件: (n : 自然数)
  证明: by
  convert! mul_polyOfInterest_aux1 p n
  rw [sum_range_succ]; rw [add_comm]; rw [Nat.sub_self]; rw [pow_zero]; rw [pow_one]
  rfl

Depends on / 依赖: Nat.sub_self, add_comm, convert, mul_polyOfInterest_aux1, pow_one, pow_zero, sub_self, sum_range_succ
-/
theorem mul_polyOfInterest_aux2 (n : Nat) :
    (p : 𝕄) ^ n * wittMul p n + wittPolyProdRemainder p n = wittPolyProd p n := by
  convert! mul_polyOfInterest_aux1 p n
  rw [sum_range_succ]; rw [add_comm]; rw [Nat.sub_self]; rw [pow_zero]; rw [pow_one]
  rfl

-- We redeclare `p` here to locally discard the unneeded `p.Prime` hypothesis.
/--
theorem `mul_polyOfInterest_aux3` / 定理 `mul_polyOfInterest_aux3`

English:
theorem mul_polyOfInterest_aux3
  given: (p n : Nat)
  statement: wittPolyProd p (n + 1) =
  proof: by
  -- a useful auxiliary fact
  have mvpz : (p : 𝕄) ^ (n + 1) = MvPolynomial.C ((p : Int) ^ (n + 1)) := by norm_cast
  rw [wittPolyProd]; rw [wittPolynomial]; rw [map_sum]; rw [map_sum]
  conv_lhs =>
    arg 1
    rw [sum_range_succ]; rw [← C_mul_X_pow_eq_monomial]; rw [tsub_self]; rw [pow_zero]; 

中文:
定理 mul_polyOf整数erest_aux3
  条件: (p n : 自然数)
  结论: wittPolyProd p (n + 1) =
  证明: by
  -- a useful auxiliary fact
  have mvpz : (p : 𝕄) ^ (n + 1) = MvPolynomial.C ((p : Int) ^ (n + 1)) := by norm_cast
  rw [wittPolyProd]; rw [wittPolynomial]; rw [map_sum]; rw [map_sum]
  conv_lhs =>
    arg 1
    rw [sum_range_succ]; rw [← C_mul_X_pow_eq_monomial]; rw [tsub_self]; rw [pow_zero]; 
-/
theorem mul_polyOfInterest_aux3 (p n : Nat) : wittPolyProd p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1)) +
    remainder p n := by
  -- a useful auxiliary fact
  have mvpz : (p : 𝕄) ^ (n + 1) = MvPolynomial.C ((p : Int) ^ (n + 1)) := by norm_cast
  rw [wittPolyProd]; rw [wittPolynomial]; rw [map_sum]; rw [map_sum]
  conv_lhs =>
    arg 1
    rw [sum_range_succ]; rw [← C_mul_X_pow_eq_monomial]; rw [tsub_self]; rw [pow_zero]; rw [pow_one]; rw [map_mul]; rw [rename_C]; rw [rename_X]; rw [← mvpz]
  conv_lhs =>
    arg 2
    rw [sum_range_succ]; rw [← C_mul_X_pow_eq_monomial]; rw [tsub_self]; rw [pow_zero]; rw [pow_one]; rw [map_mul]; rw [rename_C]; rw [rename_X]; rw [← mvpz]
  conv_rhs =>
    enter [1, 1, 2, 2]
    rw [sum_range_succ]; rw [← C_mul_X_pow_eq_monomial]; rw [tsub_self]; rw [pow_zero]; rw [pow_one]; rw [map_mul]; rw [rename_C]; rw [rename_X]; rw [← mvpz]
  conv_rhs =>
    enter [1, 2, 2]
    rw [sum_range_succ]; rw [← C_mul_X_pow_eq_monomial]; rw [tsub_self]; rw [pow_zero]; rw [pow_one]; rw [map_mul]; rw [rename_C]; rw [rename_X]; rw [← mvpz]
  simp only [add_mul, mul_add]
  rw [add_comm _ (remainder p n)]
  simp only [add_assoc]
  apply congrArg (Add.add _)
  ring

/--
theorem `mul_polyOfInterest_aux4` / 定理 `mul_polyOfInterest_aux4`

English:
theorem mul_polyOfInterest_aux4
  given: (n : Nat)
  proof: by
  rw [← add_sub_assoc]; rw [eq_sub_iff_add_eq]; rw [mul_polyOfInterest_aux2]
  exact mul_polyOfInterest_aux3 _ _

中文:
定理 mul_polyOf整数erest_aux4
  条件: (n : 自然数)
  证明: by
  rw [← add_sub_assoc]; rw [eq_sub_iff_add_eq]; rw [mul_polyOfInterest_aux2]
  exact mul_polyOfInterest_aux3 _ _

Depends on / 依赖: add_sub_assoc, eq_sub_iff_add_eq, mul_polyOfInterest_aux2, mul_polyOfInterest_aux3
-/
theorem mul_polyOfInterest_aux4 (n : Nat) :
    (p : 𝕄) ^ (n + 1) * wittMul p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1)) +
    (remainder p n - wittPolyProdRemainder p (n + 1)) := by
  rw [← add_sub_assoc]; rw [eq_sub_iff_add_eq]; rw [mul_polyOfInterest_aux2]
  exact mul_polyOfInterest_aux3 _ _

/--
theorem `mul_polyOfInterest_aux5` / 定理 `mul_polyOfInterest_aux5`

English:
theorem mul_polyOfInterest_aux5
  given: (n : Nat)
  proof: by
  simp only [polyOfInterest, mul_sub, mul_add, sub_eq_iff_eq_add']
  rw [mul_polyOfInterest_aux4 p n]
  ring

中文:
定理 mul_polyOf整数erest_aux5
  条件: (n : 自然数)
  证明: by
  simp only [polyOfInterest, mul_sub, mul_add, sub_eq_iff_eq_add']
  rw [mul_polyOfInterest_aux4 p n]
  ring

Depends on / 依赖: mul_add, mul_polyOfInterest_aux4, mul_sub, polyOfInterest, sub_eq_iff_eq_add
-/
theorem mul_polyOfInterest_aux5 (n : Nat) :
    (p : 𝕄) ^ (n + 1) * polyOfInterest p n = remainder p n - wittPolyProdRemainder p (n + 1) := by
  simp only [polyOfInterest, mul_sub, mul_add, sub_eq_iff_eq_add']
  rw [mul_polyOfInterest_aux4 p n]
  ring

/--
theorem `mul_polyOfInterest_vars` / 定理 `mul_polyOfInterest_vars`

English:
theorem mul_polyOfInterest_vars
  given: (n : Nat)
  proof: by
  rw [mul_polyOfInterest_aux5]
  apply Subset.trans (vars_sub_subset _)
  refine union_subset ?_ ?_
  · apply remainder_vars
  · apply wittPolyProdRemainder_vars

中文:
定理 mul_polyOf整数erest_vars
  条件: (n : 自然数)
  证明: by
  rw [mul_polyOfInterest_aux5]
  apply Subset.trans (vars_sub_subset _)
  refine union_subset ?_ ?_
  · apply remainder_vars
  · apply wittPolyProdRemainder_vars

Depends on / 依赖: Subset, Subset.trans, mul_polyOfInterest_aux5, remainder_vars, union_subset, vars_sub_subset, wittPolyProdRemainder_vars
-/
theorem mul_polyOfInterest_vars (n : Nat) :
    ((p : 𝕄) ^ (n + 1) * polyOfInterest p n).vars subseteq univ ×ˢ range (n + 1) := by
  rw [mul_polyOfInterest_aux5]
  apply Subset.trans (vars_sub_subset _)
  refine union_subset ?_ ?_
  · apply remainder_vars
  · apply wittPolyProdRemainder_vars

/--
theorem `polyOfInterest_vars_eq` / 定理 `polyOfInterest_vars_eq`

English:
theorem polyOfInterest_vars_eq
  given: (n : Nat)
  statement: (polyOfInterest p n).vars =
  proof: by
  have : (p : 𝕄) ^ (n + 1) = C ((p : Int) ^ (n + 1)) := by norm_cast
  rw [polyOfInterest]; rw [this]; rw [vars_C_mul]
  apply pow_ne_zero
  exact mod_cast hp.out.ne_zero

中文:
定理 polyOf整数erest_vars_eq
  条件: (n : 自然数)
  结论: (polyOf整数erest p n).vars =
  证明: by
  have : (p : 𝕄) ^ (n + 1) = C ((p : Int) ^ (n + 1)) := by norm_cast
  rw [polyOfInterest]; rw [this]; rw [vars_C_mul]
  apply pow_ne_zero
  exact mod_cast hp.out.ne_zero

Depends on / 依赖: hp.out.ne_zero, mod_cast, ne_zero, polyOfInterest, pow_ne_zero, vars_C_mul
-/
theorem polyOfInterest_vars_eq (n : Nat) : (polyOfInterest p n).vars =
    ((p : 𝕄) ^ (n + 1) * (wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
      X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) -
      X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1)))).vars := by
  have : (p : 𝕄) ^ (n + 1) = C ((p : Int) ^ (n + 1)) := by norm_cast
  rw [polyOfInterest]; rw [this]; rw [vars_C_mul]
  apply pow_ne_zero
  exact mod_cast hp.out.ne_zero

/--
theorem `polyOfInterest_vars` / 定理 `polyOfInterest_vars`

English:
theorem polyOfInterest_vars
  given: (n : Nat)
  statement: (polyOfInterest p n).vars subseteq univ ×ˢ range (n + 1)
  proof: by
  rw [polyOfInterest_vars_eq]; apply mul_polyOfInterest_vars

中文:
定理 polyOf整数erest_vars
  条件: (n : 自然数)
  结论: (polyOf整数erest p n).vars subseteq univ ×ˢ range (n + 1)
  证明: by
  rw [polyOfInterest_vars_eq]; apply mul_polyOfInterest_vars

Depends on / 依赖: mul_polyOfInterest_vars, polyOfInterest_vars_eq
-/
theorem polyOfInterest_vars (n : Nat) : (polyOfInterest p n).vars subseteq univ ×ˢ range (n + 1) := by
  rw [polyOfInterest_vars_eq]; apply mul_polyOfInterest_vars

/--
theorem `peval_polyOfInterest` / 定理 `peval_polyOfInterest`

English:
theorem peval_polyOfInterest
  given: (n : Nat) (x y : 𝕎 k)
  proof: by
  simp only [polyOfInterest, peval,
    Function.uncurry_apply_pair, aeval_X, Matrix.cons_val_one, map_mul, Matrix.cons_val_zero,
    map_sub]
  rw [sub_sub]; rw [add_comm (_ * _)]; rw [← sub_sub]
  simp [wittPolynomial_eq_sum_C_mul_X_pow, aeval, mul_coeff, peval, map_natCast,
    map_add, map_po

中文:
定理 peval_polyOf整数erest
  条件: (n : 自然数) (x y : 𝕎 k)
  证明: by
  simp only [polyOfInterest, peval,
    Function.uncurry_apply_pair, aeval_X, Matrix.cons_val_one, map_mul, Matrix.cons_val_zero,
    map_sub]
  rw [sub_sub]; rw [add_comm (_ * _)]; rw [← sub_sub]
  simp [wittPolynomial_eq_sum_C_mul_X_pow, aeval, mul_coeff, peval, map_natCast,
    map_add, map_po

Depends on / 依赖: Function, Function.uncurry_apply_pair, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, add_comm, aeval_X, cons_val_one, cons_val_zero, map_add, map_mul, map_natCast, map_pow, map_sub, mul_coeff, polyOfInterest, sub_sub, uncurry_apply_pair, wittPolynomial_eq_sum_C_mul_X_pow
-/
theorem peval_polyOfInterest (n : Nat) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
    (x * y).coeff (n + 1) + p ^ (n + 1) * x.coeff (n + 1) * y.coeff (n + 1) -
      y.coeff (n + 1) * ∑ i in range (n + 1 + 1), p ^ i * x.coeff i ^ p ^ (n + 1 - i) -
      x.coeff (n + 1) * ∑ i in range (n + 1 + 1), p ^ i * y.coeff i ^ p ^ (n + 1 - i) := by
  simp only [polyOfInterest, peval,
    Function.uncurry_apply_pair, aeval_X, Matrix.cons_val_one, map_mul, Matrix.cons_val_zero,
    map_sub]
  rw [sub_sub]; rw [add_comm (_ * _)]; rw [← sub_sub]
  simp [wittPolynomial_eq_sum_C_mul_X_pow, aeval, mul_coeff, peval, map_natCast,
    map_add, map_pow, map_mul]

variable [CharP k p]

/--
theorem `peval_polyOfInterest'` / 定理 `peval_polyOfInterest'`

English:
theorem peval_polyOfInterest'
  given: (n : Nat) (x y : 𝕎 k)
  proof: by
  rw [peval_polyOfInterest]
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  simp only [this, ne_eq, add_eq_zero, and_false, zero_pow, zero_mul, add_zero,
    not_false_eq_true, reduceCtorEq]
  have sum_zero_pow_mul_pow_p (y : 𝕎 k) : ∑ x in range (n + 1 + 1),
      (0 : k) ^ x * y.coeff x ^ p ^ (

中文:
定理 peval_polyOf整数erest'
  条件: (n : 自然数) (x y : 𝕎 k)
  证明: by
  rw [peval_polyOfInterest]
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  simp only [this, ne_eq, add_eq_zero, and_false, zero_pow, zero_mul, add_zero,
    not_false_eq_true, reduceCtorEq]
  have sum_zero_pow_mul_pow_p (y : 𝕎 k) : ∑ x in range (n + 1 + 1),
      (0 : k) ^ x * y.coeff x ^ p ^ (

Depends on / 依赖: CharP.cast_eq_zero, Finset, Finset.sum_eq_single_of_mem, add_eq_zero, add_zero, and_false, cast_eq_zero, contextual, ne_eq, not_false_eq_true, peval_polyOfInterest, reduceCtorEq, sum_eq_single_of_mem, sum_zero_pow_mul_pow_p, y.coeff, zero_mul, zero_pow
-/
theorem peval_polyOfInterest' (n : Nat) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  rw [peval_polyOfInterest]
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  simp only [this, ne_eq, add_eq_zero, and_false, zero_pow, zero_mul, add_zero,
    not_false_eq_true, reduceCtorEq]
  have sum_zero_pow_mul_pow_p (y : 𝕎 k) : ∑ x in range (n + 1 + 1),
      (0 : k) ^ x * y.coeff x ^ p ^ (n + 1 - x) = y.coeff 0 ^ p ^ (n + 1) := by
    rw [Finset.sum_eq_single_of_mem 0] <;> simp +contextual
  congr <;> apply sum_zero_pow_mul_pow_p

variable (k)

/--
theorem `nth_mul_coeff'` / 定理 `nth_mul_coeff'`

English:
theorem nth_mul_coeff'
  given: (n : Nat)
  proof: by
  simp only [← peval_polyOfInterest']
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars (s := SetLike.coe (univ ×ˢ range (n + 1))) k
    (polyOfInterest_vars p n)
  let f : TruncatedWittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    

中文:
定理 nth_mul_coeff'
  条件: (n : 自然数)
  证明: by
  simp only [← peval_polyOfInterest']
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars (s := SetLike.coe (univ ×ˢ range (n + 1))) k
    (polyOfInterest_vars p n)
  let f : TruncatedWittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    

Depends on / 依赖: Function, Function.uncurry, SetLike, SetLike.coe, TruncatedWittVector, a.fst, a.snd, exists_restrict_to_vars, peval_polyOfInterest, polyOfInterest_vars, uncurry
-/
theorem nth_mul_coeff' (n : Nat) :
    exists f : TruncatedWittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k,
    forall x y : 𝕎 k, f (truncateFun (n + 1) x) (truncateFun (n + 1) y) =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  simp only [← peval_polyOfInterest']
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars (s := SetLike.coe (univ ×ˢ range (n + 1))) k
    (polyOfInterest_vars p n)
  let f : TruncatedWittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    apply Function.uncurry ![x, y]
    let S : Set (Fin 2 × Nat) := { a | a.2 = n ∨ a.2 < n }
    have ha' : a in S := by grind
    refine ⟨a.fst, ⟨a.snd, ?_⟩⟩
    obtain ⟨ha, ha⟩ := ha' <;> lia
  use f
  intro x y
  dsimp [f, peval]
  rw [← hf₀]
  congr
  ext a
  obtain ⟨a, ha⟩ := a
  obtain ⟨i, m⟩ := a
  fin_cases i <;> rfl -- surely this case split is not necessary

/--
theorem `nth_mul_coeff` / 定理 `nth_mul_coeff`

English:
theorem nth_mul_coeff
  given: (n : Nat)
  proof: by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  use f
  intro x y
  rw [hf x y]
  ring

中文:
定理 nth_mul_coeff
  条件: (n : 自然数)
  证明: by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  use f
  intro x y
  rw [hf x y]
  ring

Depends on / 依赖: nth_mul_coeff
-/
theorem nth_mul_coeff (n : Nat) :
    exists f : TruncatedWittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k,
    forall x y : 𝕎 k, (x * y).coeff (n + 1) =
      x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
      f (truncateFun (n + 1) x) (truncateFun (n + 1) y) := by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  use f
  intro x y
  rw [hf x y]
  ring

variable {k}

/--
Definition of `nthRemainder` / `nthRemainder` 的定义

English:
definition nthRemainder
  signature: (n : Nat)
  body: Classical.choose (nth_mul_coeff p k n)

中文:
定义 nthRemainder
  签名: (n : 自然数)
  定义体: Classical.choose (nth_mul_coeff p k n)

Depends on / 依赖: Classical, Classical.choose, nth_mul_coeff
-/
def nthRemainder (n : Nat) : (Fin (n + 1) -> k) -> (Fin (n + 1) -> k) -> k :=
  Classical.choose (nth_mul_coeff p k n)

/--
theorem `nthRemainder_spec` / 定理 `nthRemainder_spec`

English:
theorem nthRemainder_spec
  given: (n : Nat) (x y : 𝕎 k)
  statement: (x * y).coeff (n + 1) =
  proof: Classical.choose_spec (nth_mul_coeff p k n) _ _

中文:
定理 nthRemainder_spec
  条件: (n : 自然数) (x y : 𝕎 k)
  结论: (x * y).coeff (n + 1) =
  证明: Classical.choose_spec (nth_mul_coeff p k n) _ _

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, nth_mul_coeff
-/
theorem nthRemainder_spec (n : Nat) (x y : 𝕎 k) : (x * y).coeff (n + 1) =
    x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
    nthRemainder p n (truncateFun (n + 1) x) (truncateFun (n + 1) y) :=
  Classical.choose_spec (nth_mul_coeff p k n) _ _

end WittVector
