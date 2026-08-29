/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# The arithmetic function `ζ`

We define `ζ` to be the arithmetic function with `ζ n = 1` for `0 < n` (whose Dirichlet series
is the Riemann zeta function).

## Main Definitions

* `ArithmeticFunction.zeta` is the arithmetic function such that `ζ x = 1` for `0 < x`. The notation
  `ζ` for this function is available by opening `ArithmeticFunction.zeta`.
* `ArithmeticFunction.pmul` and `ArithmeticFunction.pdiv` are the pointwise multiplication and
  division on `ArithmeticFunction`s (for which `ζ` is the identity). These are not the same as
  the multiplication instance defined by Dirichlet convolution.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

/--
Definition of `zeta` / `zeta` 的定义

English:
definition zeta
  signature: : ArithmeticFunction Nat
  body: ⟨fun x => ite (x = 0) 0 1, rfl⟩

@[inherit_doc]
scoped[ArithmeticFunction.zeta] notation "ζ" => ArithmeticFunction.zeta

中文:
定义 zeta
  签名: : ArithmeticFunction 自然数
  定义体: ⟨fun x => ite (x = 0) 0 1, rfl⟩

@[inherit_doc]
scoped[ArithmeticFunction.zeta] notation "ζ" => ArithmeticFunction.zeta
-/
def zeta : ArithmeticFunction Nat :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩

@[inherit_doc]
scoped[ArithmeticFunction.zeta] notation "ζ" => ArithmeticFunction.zeta

open scoped zeta

section Zeta

@[simp]
/--
theorem `zeta_apply` / 定理 `zeta_apply`

English:
theorem zeta_apply
  given: {x : Nat}
  statement: ζ x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 zeta_apply
  条件: {x : 自然数}
  结论: ζ x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem zeta_apply {x : Nat} : ζ x = if x = 0 then 0 else 1 :=
  rfl

/--
theorem `zeta_apply_ne` / 定理 `zeta_apply_ne`

English:
theorem zeta_apply_ne
  given: {x : Nat} (h : x != 0)
  statement: ζ x = 1
  proof: if_neg h

中文:
定理 zeta_apply_ne
  条件: {x : 自然数} (h : x != 0)
  结论: ζ x = 1
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem zeta_apply_ne {x : Nat} (h : x != 0) : ζ x = 1 :=
  if_neg h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `zeta_eq_zero` / 定理 `zeta_eq_zero`

English:
theorem zeta_eq_zero
  given: {x : Nat}
  statement: ζ x = 0 ↔ x = 0
  proof: by simp [zeta]

中文:
定理 zeta_eq_zero
  条件: {x : 自然数}
  结论: ζ x = 0 ↔ x = 0
  证明: by simp [zeta]
-/
theorem zeta_eq_zero {x : Nat} : ζ x = 0 ↔ x = 0 := by simp [zeta]

/--
theorem `zeta_pos` / 定理 `zeta_pos`

English:
theorem zeta_pos
  given: {x : Nat}
  statement: 0 < ζ x ↔ 0 < x
  proof: by simp [pos_iff_ne_zero]

中文:
定理 zeta_pos
  条件: {x : 自然数}
  结论: 0 < ζ x ↔ 0 < x
  证明: by simp [pos_iff_ne_zero]

Depends on / 依赖: pos_iff_ne_zero
-/
theorem zeta_pos {x : Nat} : 0 < ζ x ↔ 0 < x := by simp [pos_iff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_zeta_smul_apply` / 定理 `coe_zeta_smul_apply`

English:
theorem coe_zeta_smul_apply
  statement: {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
  proof: by
  rw [smul_apply]
  trans ∑ i in divisorsAntidiagonal x, f i.snd
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply]; rw [zeta_apply_ne (left_ne_zero_of_mul h)]; rw [cast_one]; rw [one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]

中文:
定理 coe_zeta_smul_apply
  结论: {M} [半环 R] [加法交换幺半群 M] [乘法作用 R M]
  证明: by
  rw [smul_apply]
  trans ∑ i in divisorsAntidiagonal x, f i.snd
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply]; rw [zeta_apply_ne (left_ne_zero_of_mul h)]; rw [cast_one]; rw [one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, cast_one, coeFn_mk, divisorsAntidiagonal, i.snd, left_ne_zero_of_mul, map_div_left_divisors, mem_divisorsAntidiagonal, natCoe_apply, one_smul, smul_apply, sum_congr, sum_map, zeta_apply_ne
-/
theorem coe_zeta_smul_apply {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
    {f : ArithmeticFunction M} {x : Nat} :
    ((↑ζ : ArithmeticFunction R) • f) x = ∑ i in divisors x, f i := by
  rw [smul_apply]
  trans ∑ i in divisorsAntidiagonal x, f i.snd
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply]; rw [zeta_apply_ne (left_ne_zero_of_mul h)]; rw [cast_one]; rw [one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]

/-- `@[simp]`-normal form of `coe_zeta_smul_apply`. -/
@[simp]
/--
theorem `sum_divisorsAntidiagonal_eq_sum_divisors` / 定理 `sum_divisorsAntidiagonal_eq_sum_divisors`

English:
theorem sum_divisorsAntidiagonal_eq_sum_divisors
  statement: {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
  proof: by
  simp [← coe_zeta_smul_apply (R := R)]

中文:
定理 sum_divisorsAntidiagonal_eq_sum_divisors
  结论: {M} [半环 R] [加法交换幺半群 M] [乘法作用 R M]
  证明: by
  simp [← coe_zeta_smul_apply (R := R)]

Depends on / 依赖: coe_zeta_smul_apply
-/
theorem sum_divisorsAntidiagonal_eq_sum_divisors {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
    {f : ArithmeticFunction M} {x : Nat} :
    (∑ x in x.divisorsAntidiagonal, if x.1 = 0 then (0 : R) • f x.2 else f x.2) =
      ∑ i in divisors x, f i := by
  simp [← coe_zeta_smul_apply (R := R)]

/--
theorem `coe_zeta_mul_comm` / 定理 `coe_zeta_mul_comm`

English:
theorem coe_zeta_mul_comm
  given: [Semiring R] {f : ArithmeticFunction R}
  statement: ζ * f = f * ζ
  proof: by
  ext n
  simp_rw [mul_apply, natCoe_apply, (cast_commute ..).eq]
  rw [sum_divisorsAntidiagonal fun x y => f y * ζ x]; rw [sum_divisorsAntidiagonal' fun x y => f x * ζ y]

中文:
定理 coe_zeta_mul_comm
  条件: [半环 R] {f : ArithmeticFunction R}
  结论: ζ * f = f * ζ
  证明: by
  ext n
  simp_rw [mul_apply, natCoe_apply, (cast_commute ..).eq]
  rw [sum_divisorsAntidiagonal fun x y => f y * ζ x]; rw [sum_divisorsAntidiagonal' fun x y => f x * ζ y]

Depends on / 依赖: cast_commute, mul_apply, natCoe_apply, simp_rw, sum_divisorsAntidiagonal
-/
theorem coe_zeta_mul_comm [Semiring R] {f : ArithmeticFunction R} : ζ * f = f * ζ := by
  ext n
  simp_rw [mul_apply, natCoe_apply, (cast_commute ..).eq]
  rw [sum_divisorsAntidiagonal fun x y => f y * ζ x]; rw [sum_divisorsAntidiagonal' fun x y => f x * ζ y]

/--
theorem `coe_zeta_mul_apply` / 定理 `coe_zeta_mul_apply`

English:
theorem coe_zeta_mul_apply
  given: [Semiring R] {f : ArithmeticFunction R} {x : Nat}
  proof: coe_zeta_smul_apply

中文:
定理 coe_zeta_mul_apply
  条件: [半环 R] {f : ArithmeticFunction R} {x : 自然数}
  证明: coe_zeta_smul_apply

Depends on / 依赖: coe_zeta_smul_apply
-/
theorem coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : Nat} :
    (ζ * f) x = ∑ i in divisors x, f i :=
  coe_zeta_smul_apply

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_mul_zeta_apply` / 定理 `coe_mul_zeta_apply`

English:
theorem coe_mul_zeta_apply
  given: [Semiring R] {f : ArithmeticFunction R} {x : Nat}
  proof: by
  rw [← coe_zeta_mul_comm]; rw [coe_zeta_mul_apply]

中文:
定理 coe_mul_zeta_apply
  条件: [半环 R] {f : ArithmeticFunction R} {x : 自然数}
  证明: by
  rw [← coe_zeta_mul_comm]; rw [coe_zeta_mul_apply]

Depends on / 依赖: coe_zeta_mul_apply, coe_zeta_mul_comm
-/
theorem coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : Nat} :
    (f * ζ) x = ∑ i in divisors x, f i := by
  rw [← coe_zeta_mul_comm]; rw [coe_zeta_mul_apply]

/--
theorem `zeta_mul_apply` / 定理 `zeta_mul_apply`

English:
theorem zeta_mul_apply
  given: {f : ArithmeticFunction Nat} {x : Nat}
  statement: (ζ * f) x = ∑ i in divisors x, f i
  proof: by
  rw [← natCoe_nat ζ]; rw [coe_zeta_mul_apply]

中文:
定理 zeta_mul_apply
  条件: {f : ArithmeticFunction 自然数} {x : 自然数}
  结论: (ζ * f) x = ∑ i in divisors x, f i
  证明: by
  rw [← natCoe_nat ζ]; rw [coe_zeta_mul_apply]

Depends on / 依赖: coe_zeta_mul_apply, natCoe_nat
-/
theorem zeta_mul_apply {f : ArithmeticFunction Nat} {x : Nat} : (ζ * f) x = ∑ i in divisors x, f i := by
  rw [← natCoe_nat ζ]; rw [coe_zeta_mul_apply]

/--
theorem `mul_zeta_apply` / 定理 `mul_zeta_apply`

English:
theorem mul_zeta_apply
  given: {f : ArithmeticFunction Nat} {x : Nat}
  statement: (f * ζ) x = ∑ i in divisors x, f i
  proof: by
  rw [← natCoe_nat ζ]; rw [coe_mul_zeta_apply]

中文:
定理 mul_zeta_apply
  条件: {f : ArithmeticFunction 自然数} {x : 自然数}
  结论: (f * ζ) x = ∑ i in divisors x, f i
  证明: by
  rw [← natCoe_nat ζ]; rw [coe_mul_zeta_apply]

Depends on / 依赖: coe_mul_zeta_apply, natCoe_nat
-/
theorem mul_zeta_apply {f : ArithmeticFunction Nat} {x : Nat} : (f * ζ) x = ∑ i in divisors x, f i := by
  rw [← natCoe_nat ζ]; rw [coe_mul_zeta_apply]

/--
theorem `zeta_mul_comm` / 定理 `zeta_mul_comm`

English:
theorem zeta_mul_comm
  given: {f : ArithmeticFunction Nat}
  statement: ζ * f = f * ζ
  proof: by
  rw [← natCoe_nat ζ]; rw [coe_zeta_mul_comm]

中文:
定理 zeta_mul_comm
  条件: {f : ArithmeticFunction 自然数}
  结论: ζ * f = f * ζ
  证明: by
  rw [← natCoe_nat ζ]; rw [coe_zeta_mul_comm]

Depends on / 依赖: coe_zeta_mul_comm, natCoe_nat
-/
theorem zeta_mul_comm {f : ArithmeticFunction Nat} : ζ * f = f * ζ := by
  rw [← natCoe_nat ζ]; rw [coe_zeta_mul_comm]

end Zeta

section Pmul

/--
Definition of `pmul` / `pmul` 的定义

English:
definition pmul
  signature: [MulZeroClass R] (f g : ArithmeticFunction R)
  body: ⟨fun x => f x * g x, by simp⟩

@[simp]

中文:
定义 pmul
  签名: [乘零类 R] (f g : ArithmeticFunction R)
  定义体: ⟨fun x => f x * g x, by simp⟩

@[simp]
-/
def pmul [MulZeroClass R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun x => f x * g x, by simp⟩

@[simp]
/--
theorem `pmul_apply` / 定理 `pmul_apply`

English:
theorem pmul_apply
  given: [MulZeroClass R] {f g : ArithmeticFunction R} {x : Nat}
  statement: f.pmul g x = f x * g x
  proof: rfl

中文:
定理 pmul_apply
  条件: [乘零类 R] {f g : ArithmeticFunction R} {x : 自然数}
  结论: f.pmul g x = f x * g x
  证明: rfl
-/
theorem pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : Nat} : f.pmul g x = f x * g x :=
  rfl

/--
theorem `pmul_comm` / 定理 `pmul_comm`

English:
theorem pmul_comm
  given: [CommMonoidWithZero R] (f g : ArithmeticFunction R)
  statement: f.pmul g = g.pmul f
  proof: by
  ext
  simp [mul_comm]

中文:
定理 pmul_comm
  条件: [带零交换幺半群 R] (f g : ArithmeticFunction R)
  结论: f.pmul g = g.pmul f
  证明: by
  ext
  simp [mul_comm]

Depends on / 依赖: mul_comm
-/
theorem pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g = g.pmul f := by
  ext
  simp [mul_comm]

/--
lemma `pmul_assoc` / 引理 `pmul_assoc`

English:
lemma pmul_assoc
  given: [SemigroupWithZero R] (f₁ f₂ f₃ : ArithmeticFunction R)
  proof: by
  ext
  simp only [pmul_apply, mul_assoc]

中文:
引理 pmul_assoc
  条件: [带零半群 R] (f₁ f₂ f₃ : ArithmeticFunction R)
  证明: by
  ext
  simp only [pmul_apply, mul_assoc]

Depends on / 依赖: mul_assoc, pmul_apply
-/
lemma pmul_assoc [SemigroupWithZero R] (f₁ f₂ f₃ : ArithmeticFunction R) :
    pmul (pmul f₁ f₂) f₃ = pmul f₁ (pmul f₂ f₃) := by
  ext
  simp only [pmul_apply, mul_assoc]

section NonAssocSemiring

variable [NonAssocSemiring R]

@[simp]
/--
theorem `pmul_zeta` / 定理 `pmul_zeta`

English:
theorem pmul_zeta
  given: (f : ArithmeticFunction R)
  statement: f.pmul ↑ζ = f
  proof: by
  ext x
  cases x <;> simp

@[simp]

中文:
定理 pmul_zeta
  条件: (f : ArithmeticFunction R)
  结论: f.pmul ↑ζ = f
  证明: by
  ext x
  cases x <;> simp

@[simp]
-/
theorem pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f := by
  ext x
  cases x <;> simp

@[simp]
/--
theorem `zeta_pmul` / 定理 `zeta_pmul`

English:
theorem zeta_pmul
  given: (f : ArithmeticFunction R)
  statement: (ζ : ArithmeticFunction R).pmul f = f
  proof: by
  ext x
  cases x <;> simp

中文:
定理 zeta_pmul
  条件: (f : ArithmeticFunction R)
  结论: (ζ : ArithmeticFunction R).pmul f = f
  证明: by
  ext x
  cases x <;> simp
-/
theorem zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f = f := by
  ext x
  cases x <;> simp

end NonAssocSemiring

variable [Semiring R]

open scoped zeta

/--
Definition of `ppow` / `ppow` 的定义

English:
definition ppow
  signature: (f : ArithmeticFunction R) (k : Nat)
  body: if h0 : k = 0 then ζ else ⟨fun x => f x ^ k, by simp_rw [map_zero, zero_pow h0]⟩

中文:
定义 ppow
  签名: (f : ArithmeticFunction R) (k : 自然数)
  定义体: if h0 : k = 0 then ζ else ⟨fun x => f x ^ k, by simp_rw [map_zero, zero_pow h0]⟩

Depends on / 依赖: map_zero, simp_rw, zero_pow
-/
def ppow (f : ArithmeticFunction R) (k : Nat) : ArithmeticFunction R :=
  if h0 : k = 0 then ζ else ⟨fun x => f x ^ k, by simp_rw [map_zero, zero_pow h0]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ppow_zero` / 定理 `ppow_zero`

English:
theorem ppow_zero
  given: {f : ArithmeticFunction R}
  statement: f.ppow 0 = ζ
  proof: by rw [ppow, dif_pos rfl]

@[simp]

中文:
定理 ppow_zero
  条件: {f : ArithmeticFunction R}
  结论: f.ppow 0 = ζ
  证明: by rw [ppow, dif_pos rfl]

@[simp]

Depends on / 依赖: dif_pos
-/
theorem ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ := by rw [ppow, dif_pos rfl]

@[simp]
/--
theorem `ppow_one` / 定理 `ppow_one`

English:
theorem ppow_one
  given: {f : ArithmeticFunction R}
  statement: f.ppow 1 = f
  proof: by
  ext; simp [ppow]

中文:
定理 ppow_one
  条件: {f : ArithmeticFunction R}
  结论: f.ppow 1 = f
  证明: by
  ext; simp [ppow]
-/
theorem ppow_one {f : ArithmeticFunction R} : f.ppow 1 = f := by
  ext; simp [ppow]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ppow_apply` / 定理 `ppow_apply`

English:
theorem ppow_apply
  given: {f : ArithmeticFunction R} {k x : Nat} (kpos : 0 < k)
  statement: f.ppow k x = f x ^ k
  proof: by
  rw [ppow]; rw [dif_neg (Nat.ne_of_gt kpos)]; rw [coe_mk]

中文:
定理 ppow_apply
  条件: {f : ArithmeticFunction R} {k x : 自然数} (kpos : 0 < k)
  结论: f.ppow k x = f x ^ k
  证明: by
  rw [ppow]; rw [dif_neg (Nat.ne_of_gt kpos)]; rw [coe_mk]

Depends on / 依赖: Nat.ne_of_gt, coe_mk, dif_neg, ne_of_gt
-/
theorem ppow_apply {f : ArithmeticFunction R} {k x : Nat} (kpos : 0 < k) : f.ppow k x = f x ^ k := by
  rw [ppow]; rw [dif_neg (Nat.ne_of_gt kpos)]; rw [coe_mk]

/--
theorem `ppow_succ'` / 定理 `ppow_succ'`

English:
theorem ppow_succ'
  given: {f : ArithmeticFunction R} {k : Nat}
  statement: f.ppow (k + 1) = f.pmul (f.ppow k)
  proof: by
  ext x
  rw [ppow_apply (succ_pos k)]; rw [_root_.pow_succ']
  induction k <;> simp

中文:
定理 ppow_succ'
  条件: {f : ArithmeticFunction R} {k : 自然数}
  结论: f.ppow (k + 1) = f.pmul (f.ppow k)
  证明: by
  ext x
  rw [ppow_apply (succ_pos k)]; rw [_root_.pow_succ']
  induction k <;> simp

Depends on / 依赖: _root_, _root_.pow_succ, pow_succ, ppow_apply, succ_pos
-/
theorem ppow_succ' {f : ArithmeticFunction R} {k : Nat} : f.ppow (k + 1) = f.pmul (f.ppow k) := by
  ext x
  rw [ppow_apply (succ_pos k)]; rw [_root_.pow_succ']
  induction k <;> simp

/--
theorem `ppow_succ` / 定理 `ppow_succ`

English:
theorem ppow_succ
  given: {f : ArithmeticFunction R} {k : Nat} {kpos : 0 < k}
  proof: by
  ext x
  rw [ppow_apply (succ_pos k)]; rw [_root_.pow_succ]
  induction k <;> simp

中文:
定理 ppow_succ
  条件: {f : ArithmeticFunction R} {k : 自然数} {kpos : 0 < k}
  证明: by
  ext x
  rw [ppow_apply (succ_pos k)]; rw [_root_.pow_succ]
  induction k <;> simp

Depends on / 依赖: _root_, _root_.pow_succ, pow_succ, ppow_apply, succ_pos
-/
theorem ppow_succ {f : ArithmeticFunction R} {k : Nat} {kpos : 0 < k} :
    f.ppow (k + 1) = (f.ppow k).pmul f := by
  ext x
  rw [ppow_apply (succ_pos k)]; rw [_root_.pow_succ]
  induction k <;> simp

end Pmul

section Pdiv

/--
Definition of `pdiv` / `pdiv` 的定义

English:
definition pdiv
  signature: [GroupWithZero R] (f g : ArithmeticFunction R)
  body: ⟨fun n => f n / g n, by simp only [map_zero, div_zero]⟩

@[simp]

中文:
定义 pdiv
  签名: [带零群 R] (f g : ArithmeticFunction R)
  定义体: ⟨fun n => f n / g n, by simp only [map_zero, div_zero]⟩

@[simp]

Depends on / 依赖: div_zero, map_zero
-/
def pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n / g n, by simp only [map_zero, div_zero]⟩

@[simp]
/--
theorem `pdiv_apply` / 定理 `pdiv_apply`

English:
theorem pdiv_apply
  given: [GroupWithZero R] (f g : ArithmeticFunction R) (n : Nat)
  proof: rfl

中文:
定理 pdiv_apply
  条件: [带零群 R] (f g : ArithmeticFunction R) (n : 自然数)
  证明: rfl
-/
theorem pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : Nat) :
    pdiv f g n = f n / g n := rfl

/-- This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s because zeta takes
values in ℕ, and hence the coercion requires an `AddMonoidWithOne`. TODO: Generalise zeta -/
@[simp]
/--
theorem `pdiv_zeta` / 定理 `pdiv_zeta`

English:
theorem pdiv_zeta
  given: [DivisionSemiring R] (f : ArithmeticFunction R)
  proof: by
  ext n
  cases n <;> simp

中文:
定理 pdiv_zeta
  条件: [除半环 R] (f : ArithmeticFunction R)
  证明: by
  ext n
  cases n <;> simp
-/
theorem pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f zeta = f := by
  ext n
  cases n <;> simp

end Pdiv

@[arith_mult]
/--
theorem `isMultiplicative_zeta` / 定理 `isMultiplicative_zeta`

English:
theorem isMultiplicative_zeta
  statement: IsMultiplicative ζ
  proof: IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp +contextual⟩

中文:
定理 isMultiplicative_zeta
  结论: 是Multiplicative ζ
  证明: IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp +contextual⟩

Depends on / 依赖: IsMultiplicative, IsMultiplicative.iff_ne_zero, contextual, iff_ne_zero
-/
theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp +contextual⟩

namespace IsMultiplicative

@[arith_mult]
/--
theorem `pmul` / 定理 `pmul`

English:
theorem pmul
  statement: [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
  proof: ⟨by simp [hf, hg], fun cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩

@[arith_mult]

中文:
定理 pmul
  结论: [交换半环 R] {f g : ArithmeticFunction R} (hf : f.是Multiplicative)
  证明: ⟨by simp [hf, hg], fun cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩

@[arith_mult]

Depends on / 依赖: hf.map_mul_of_coprime, hg.map_mul_of_coprime, map_mul_of_coprime, pmul_apply
-/
theorem pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g) :=
  ⟨by simp [hf, hg], fun cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩

@[arith_mult]
/--
theorem `pdiv` / 定理 `pdiv`

English:
theorem pdiv
  statement: [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
  proof: ⟨by simp [hf, hg], fun cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop, div_eq_mul_inv,
      mul_inv]
    apply mul_mul_mul_comm ⟩

@[arith_mult]

中文:
定理 pdiv
  结论: [带零交换群 R] {f g : ArithmeticFunction R} (hf : 是Multiplicative f)
  证明: ⟨by simp [hf, hg], fun cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop, div_eq_mul_inv,
      mul_inv]
    apply mul_mul_mul_comm ⟩

@[arith_mult]

Depends on / 依赖: div_eq_mul_inv, map_mul_of_coprime, mul_inv, mul_mul_mul_comm, pdiv_apply
-/
theorem pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
    (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g) :=
  ⟨by simp [hf, hg], fun cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop, div_eq_mul_inv,
      mul_inv]
    apply mul_mul_mul_comm ⟩

@[arith_mult]
/--
theorem `ppow` / 定理 `ppow`

English:
theorem ppow
  statement: [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
  proof: by
  induction k with
  | zero => exact isMultiplicative_zeta.natCast
  | succ k hi => rw [ppow_succ']; apply hf.pmul hi

中文:
定理 ppow
  结论: [交换半环 R] {f : ArithmeticFunction R} (hf : f.是Multiplicative)
  证明: by
  induction k with
  | zero => exact isMultiplicative_zeta.natCast
  | succ k hi => rw [ppow_succ']; apply hf.pmul hi

Depends on / 依赖: hf.pmul, isMultiplicative_zeta, isMultiplicative_zeta.natCast, natCast, ppow_succ
-/
theorem ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : Nat} : IsMultiplicative (f.ppow k) := by
  induction k with
  | zero => exact isMultiplicative_zeta.natCast
  | succ k hi => rw [ppow_succ']; apply hf.pmul hi

end IsMultiplicative

end ArithmeticFunction

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.zeta`. -/
@[positivity ArithmeticFunction.zeta _]
meta def evalArithmeticFunctionZeta : PositivityExt where eval {u α} z p? e :=
  match p? with | none => throwError "no PartialOrder instance" | some p => do
  match u, α, e with
  | 0, ~q(Nat), ~q(ArithmeticFunction.zeta $n) =>
    assumeInstancesCommute
    let rn ← core z p n
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.zeta_pos $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.zeta"

end Mathlib.Meta.Positivity
