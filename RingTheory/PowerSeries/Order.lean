/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order

/-! # Formal power series (in one variable) - Order

The `PowerSeries.order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `PowerSeries.order` is an
additive valuation (`PowerSeries.order_mul`, `PowerSeries.min_order_le_order_add`).

We prove that if the commutative ring `R` of coefficients is an integral domain,
then the ring `R⟦X⟧` of formal power series in one variable over `R`
is an integral domain.

Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order. This is useful when
proving that `R⟦X⟧` is a normalization monoid, which is done in `PowerSeries.Inverse`.

-/

@[expose] public section
noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section OrderBasic

variable [Semiring R] {φ : R⟦X⟧}

/--
theorem `exists_coeff_ne_zero_iff_ne_zero` / 定理 `exists_coeff_ne_zero_iff_ne_zero`

English:
theorem exists_coeff_ne_zero_iff_ne_zero
  statement: (exists n : Nat, coeff n φ != 0) ↔ φ != 0
  proof: by
  contrapose!
  simp

中文:
定理 存在_coeff_ne_zero_iff_ne_zero
  结论: (存在 n : 自然数, coeff n φ != 0) ↔ φ != 0
  证明: by
  contrapose!
  simp

Depends on / 依赖: contrapose
-/
theorem exists_coeff_ne_zero_iff_ne_zero : (exists n : Nat, coeff n φ != 0) ↔ φ != 0 := by
  contrapose!
  simp

/--
Definition of `order` / `order` 的定义

English:
definition order
  signature: (φ : R⟦X⟧)
  body: letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

中文:
定义 order
  签名: (φ : R⟦X⟧)
  定义体: letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

Depends on / 依赖: Classical, Classical.decEq, Nat.find, exists_coeff_ne_zero_iff_ne_zero, exists_coeff_ne_zero_iff_ne_zero.mpr
-/
def order (φ : R⟦X⟧) : Nat∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

/-- The order of the `0` power series is infinite. -/
@[simp]
/--
theorem `order_zero` / 定理 `order_zero`

English:
theorem order_zero
  statement: order (0 : R⟦X⟧) = ⊤
  proof: dif_pos rfl

中文:
定理 order_zero
  结论: order (0 : R⟦X⟧) = ⊤
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
theorem order_zero : order (0 : R⟦X⟧) = ⊤ :=
  dif_pos rfl

/--
theorem `order_finite_iff_ne_zero` / 定理 `order_finite_iff_ne_zero`

English:
theorem order_finite_iff_ne_zero
  statement: (order φ < ⊤) ↔ φ != 0
  proof: by
  simp only [order]
  split_ifs with h <;> simpa

中文:
定理 order_finite_iff_ne_zero
  结论: (order φ < ⊤) ↔ φ != 0
  证明: by
  simp only [order]
  split_ifs with h <;> simpa

Depends on / 依赖: split_ifs
-/
theorem order_finite_iff_ne_zero : (order φ < ⊤) ↔ φ != 0 := by
  simp only [order]
  split_ifs with h <;> simpa

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
/--
theorem `order_eq_top` / 定理 `order_eq_top`

English:
theorem order_eq_top
  given: {φ : R⟦X⟧}
  statement: φ.order = ⊤ ↔ φ = 0
  proof: by
  simpa using order_finite_iff_ne_zero.not_left

中文:
定理 order_eq_top
  条件: {φ : R⟦X⟧}
  结论: φ.order = ⊤ ↔ φ = 0
  证明: by
  simpa using order_finite_iff_ne_zero.not_left

Depends on / 依赖: not_left, order_finite_iff_ne_zero, order_finite_iff_ne_zero.not_left
-/
theorem order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0 := by
  simpa using order_finite_iff_ne_zero.not_left

/--
theorem `coe_toNat_order` / 定理 `coe_toNat_order`

English:
theorem coe_toNat_order
  given: {φ : R⟦X⟧} (hf : φ != 0)
  statement: φ.order.toNat = φ.order
  proof: by
  rw [ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hf)]

中文:
定理 coe_to自然数_order
  条件: {φ : R⟦X⟧} (hf : φ != 0)
  结论: φ.order.to自然数 = φ.order
  证明: by
  rw [ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hf)]

Depends on / 依赖: ENat.natCast_toNat_eq_self.mpr, natCast_toNat_eq_self, order_eq_top, order_eq_top.not.mpr
-/
theorem coe_toNat_order {φ : R⟦X⟧} (hf : φ != 0) : φ.order.toNat = φ.order := by
  rw [ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hf)]

/--
theorem `coeff_order` / 定理 `coeff_order`

English:
theorem coeff_order
  given: (h : φ != 0)
  statement: coeff φ.order.toNat φ != 0
  proof: by
  classical
  simp only [order, h, not_false_iff, dif_neg]
  generalize_proofs h
  exact Nat.find_spec h

中文:
定理 coeff_order
  条件: (h : φ != 0)
  结论: coeff φ.order.to自然数 φ != 0
  证明: by
  classical
  simp only [order, h, not_false_iff, dif_neg]
  generalize_proofs h
  exact Nat.find_spec h

Depends on / 依赖: Nat.find_spec, classical, dif_neg, find_spec, generalize_proofs, not_false_iff
-/
theorem coeff_order (h : φ != 0) : coeff φ.order.toNat φ != 0 := by
  classical
  simp only [order, h, not_false_iff, dif_neg]
  generalize_proofs h
  exact Nat.find_spec h

/--
theorem `order_le` / 定理 `order_le`

English:
theorem order_le
  given: (n : Nat) (h : coeff n φ != 0)
  statement: order φ <= n
  proof: by
  rw [order]; rw [dif_neg]
  · simpa using ⟨n, le_rfl, h⟩
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩

中文:
定理 order_le
  条件: (n : 自然数) (h : coeff n φ != 0)
  结论: order φ <= n
  证明: by
  rw [order]; rw [dif_neg]
  · simpa using ⟨n, le_rfl, h⟩
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩

Depends on / 依赖: dif_neg, exists_coeff_ne_zero_iff_ne_zero, exists_coeff_ne_zero_iff_ne_zero.mp, le_rfl
-/
theorem order_le (n : Nat) (h : coeff n φ != 0) : order φ <= n := by
  rw [order]; rw [dif_neg]
  · simpa using ⟨n, le_rfl, h⟩
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩

/--
theorem `coeff_of_lt_order` / 定理 `coeff_of_lt_order`

English:
theorem coeff_of_lt_order
  given: (n : Nat) (h : ↑n < order φ)
  statement: coeff n φ = 0
  proof: by
  contrapose! h
  exact order_le _ h

中文:
定理 coeff_of_lt_order
  条件: (n : 自然数) (h : ↑n < order φ)
  结论: coeff n φ = 0
  证明: by
  contrapose! h
  exact order_le _ h

Depends on / 依赖: contrapose, order_le
-/
theorem coeff_of_lt_order (n : Nat) (h : ↑n < order φ) : coeff n φ = 0 := by
  contrapose! h
  exact order_le _ h

/--
theorem `coeff_of_lt_order_toNat` / 定理 `coeff_of_lt_order_toNat`

English:
theorem coeff_of_lt_order_toNat
  given: (n : Nat) (h : n < φ.order.toNat)
  statement: coeff n φ = 0
  proof: by
  by_cases h' : φ = 0
  · simp [h']
  · refine coeff_of_lt_order _ ?_
    rwa [← coe_toNat_order h', ENat.natCast_lt_natCast]

中文:
定理 coeff_of_lt_order_to自然数
  条件: (n : 自然数) (h : n < φ.order.to自然数)
  结论: coeff n φ = 0
  证明: by
  by_cases h' : φ = 0
  · simp [h']
  · refine coeff_of_lt_order _ ?_
    rwa [← coe_toNat_order h', ENat.natCast_lt_natCast]

Depends on / 依赖: ENat.natCast_lt_natCast, coe_toNat_order, coeff_of_lt_order, natCast_lt_natCast
-/
theorem coeff_of_lt_order_toNat (n : Nat) (h : n < φ.order.toNat) : coeff n φ = 0 := by
  by_cases h' : φ = 0
  · simp [h']
  · refine coeff_of_lt_order _ ?_
    rwa [← coe_toNat_order h', ENat.natCast_lt_natCast]

/--
theorem `nat_le_order` / 定理 `nat_le_order`

English:
theorem nat_le_order
  given: (φ : R⟦X⟧) (n : Nat) (h : forall i < n, coeff i φ = 0)
  statement: ↑n <= order φ
  proof: by
  simp only [order]
  split_ifs
  · simp
  · simpa [Nat.le_find_iff]

中文:
定理 nat_le_order
  条件: (φ : R⟦X⟧) (n : 自然数) (h : 对任意 i < n, coeff i φ = 0)
  结论: ↑n <= order φ
  证明: by
  simp only [order]
  split_ifs
  · simp
  · simpa [Nat.le_find_iff]

Depends on / 依赖: Nat.le_find_iff, le_find_iff, split_ifs
-/
theorem nat_le_order (φ : R⟦X⟧) (n : Nat) (h : forall i < n, coeff i φ = 0) : ↑n <= order φ := by
  simp only [order]
  split_ifs
  · simp
  · simpa [Nat.le_find_iff]

/--
theorem `le_order` / 定理 `le_order`

English:
theorem le_order
  given: (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat, ↑i < n -> coeff i φ = 0)
  proof: by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert! nat_le_order φ n _
    simpa using h

中文:
定理 le_order
  条件: (φ : R⟦X⟧) (n : 自然数∞) (h : 对任意 i : 自然数, ↑i < n -> coeff i φ = 0)
  证明: by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert! nat_le_order φ n _
    simpa using h

Depends on / 依赖: convert, nat_le_order
-/
theorem le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat, ↑i < n -> coeff i φ = 0) :
    n <= order φ := by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert! nat_le_order φ n _
    simpa using h

/--
theorem `order_eq_nat` / 定理 `order_eq_nat`

English:
theorem order_eq_nat
  given: {φ : R⟦X⟧} {n : Nat}
  proof: by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  simp [order, dif_neg hφ, Nat.find_eq_iff]

中文:
定理 order_eq_nat
  条件: {φ : R⟦X⟧} {n : 自然数}
  证明: by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  simp [order, dif_neg hφ, Nat.find_eq_iff]

Depends on / 依赖: Nat.find_eq_iff, dif_neg, eq_or_ne, find_eq_iff
-/
theorem order_eq_nat {φ : R⟦X⟧} {n : Nat} :
    order φ = n ↔ coeff n φ != 0 ∧ forall i, i < n -> coeff i φ = 0 := by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  simp [order, dif_neg hφ, Nat.find_eq_iff]

/--
theorem `order_eq` / 定理 `order_eq`

English:
theorem order_eq
  given: {φ : R⟦X⟧} {n : Nat∞}
  proof: by
  cases n with
  | top => simp
  | coe n => simp [order_eq_nat]

中文:
定理 order_eq
  条件: {φ : R⟦X⟧} {n : 自然数∞}
  证明: by
  cases n with
  | top => simp
  | coe n => simp [order_eq_nat]

Depends on / 依赖: order_eq_nat
-/
theorem order_eq {φ : R⟦X⟧} {n : Nat∞} :
    order φ = n ↔ (forall i : Nat, ↑i = n -> coeff i φ != 0) ∧ forall i : Nat, ↑i < n -> coeff i φ = 0 := by
  cases n with
  | top => simp
  | coe n => simp [order_eq_nat]

/--
theorem `order_eq_order` / 定理 `order_eq_order`

English:
theorem order_eq_order
  given: {φ : R⟦X⟧}
  statement: φ.order = MvPowerSeries.order φ
  proof: by
  refine eq_of_le_of_ge ?_ ?_
  · refine MvPowerSeries.le_order fun d hd => by
      have : coeff ↑(Finsupp.degree d) φ = 0 := coeff_of_lt_order _ hd
      have eq_aux : d.degree = d () := Finset.sum_eq_single _ (by simp) (by simp)
      exact (PowerSeries.coeff_def rfl (R := R)) ▸ (eq_aux ▸ this)
  · refine le_order φ (MvPowerSeries.order φ) fun i hi => by
      rw [← Finsupp.degree_single () i] at hi
      exact MvPowerSeries.coeff_of_lt_order hi

中文:
定理 order_eq_order
  条件: {φ : R⟦X⟧}
  结论: φ.order = MvPowerSeries.order φ
  证明: by
  refine eq_of_le_of_ge ?_ ?_
  · refine MvPowerSeries.le_order fun d hd => by
      have : coeff ↑(Finsupp.degree d) φ = 0 := coeff_of_lt_order _ hd
      have eq_aux : d.degree = d () := Finset.sum_eq_single _ (by simp) (by simp)
      exact (PowerSeries.coeff_def rfl (R := R)) ▸ (eq_aux ▸ this)
  · refine le_order φ (MvPowerSeries.order φ) fun i hi => by
      rw [← Finsupp.degree_single () i] at hi
      exact MvPowerSeries.coeff_of_lt_order hi

Depends on / 依赖: Finset, Finset.sum_eq_single, Finsupp, Finsupp.degree, Finsupp.degree_single, MvPowerSeries, MvPowerSeries.coeff_of_lt_order, MvPowerSeries.le_order, MvPowerSeries.order, PowerSeries, PowerSeries.coeff_def, coeff_def, coeff_of_lt_order, d.degree, degree, degree_single, eq_aux, eq_of_le_of_ge, le_order, sum_eq_single
-/
theorem order_eq_order {φ : R⟦X⟧} : φ.order = MvPowerSeries.order φ := by
  refine eq_of_le_of_ge ?_ ?_
  · refine MvPowerSeries.le_order fun d hd => by
      have : coeff ↑(Finsupp.degree d) φ = 0 := coeff_of_lt_order _ hd
      have eq_aux : d.degree = d () := Finset.sum_eq_single _ (by simp) (by simp)
      exact (PowerSeries.coeff_def rfl (R := R)) ▸ (eq_aux ▸ this)
  · refine le_order φ (MvPowerSeries.order φ) fun i hi => by
      rw [← Finsupp.degree_single () i] at hi
      exact MvPowerSeries.coeff_of_lt_order hi

/--
theorem `min_order_le_order_add` / 定理 `min_order_le_order_add`

English:
theorem min_order_le_order_add
  given: (φ ψ : R⟦X⟧)
  statement: min (order φ) (order ψ) <= order (φ + ψ)
  proof: by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]

中文:
定理 min_order_le_order_add
  条件: (φ ψ : R⟦X⟧)
  结论: 最小值 (order φ) (order ψ) <= order (φ + ψ)
  证明: by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]

Depends on / 依赖: coeff_of_lt_order, contextual, le_order
-/
theorem min_order_le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) <= order (φ + ψ) := by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]

/--
theorem `order_add_of_order_ne.aux` / 定理 `order_add_of_order_ne.aux`

English:
theorem order_add_of_order_ne.aux
  statement: (φ ψ : R⟦X⟧)
  proof: by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff]; rw [this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _).map_add]; rw [coeff_of_lt_order i H]; rw [add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _).map_add]; rw [coeff_of_lt_order i hi]; rw [coeff_of_lt_order i (lt_trans hi H)]; rw [zero_add]

中文:
定理 order_add_of_order_ne.aux
  结论: (φ ψ : R⟦X⟧)
  证明: by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff]; rw [this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _).map_add]; rw [coeff_of_lt_order i H]; rw [add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _).map_add]; rw [coeff_of_lt_order i hi]; rw [coeff_of_lt_order i (lt_trans hi H)]; rw [zero_add]
-/
private theorem order_add_of_order_ne.aux (φ ψ : R⟦X⟧)
    (H : order φ < order ψ) : order (φ + ψ) <= order φ ⊓ order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff]; rw [this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _).map_add]; rw [coeff_of_lt_order i H]; rw [add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _).map_add]; rw [coeff_of_lt_order i hi]; rw [coeff_of_lt_order i (lt_trans hi H)]; rw [zero_add]

/--
theorem `order_add_of_order_ne` / 定理 `order_add_of_order_ne`

English:
theorem order_add_of_order_ne
  given: (φ ψ : R⟦X⟧) (h : order φ != order ψ)
  proof: by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  rcases h.lt_or_gt with (φ_lt_ψ | ψ_lt_φ)
  · apply order_add_of_order_ne.aux _ _ φ_lt_ψ
  · simpa only [add_comm, inf_comm] using order_add_of_order_ne.aux _ _ ψ_lt_φ

中文:
定理 order_add_of_order_ne
  条件: (φ ψ : R⟦X⟧) (h : order φ != order ψ)
  证明: by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  rcases h.lt_or_gt with (φ_lt_ψ | ψ_lt_φ)
  · apply order_add_of_order_ne.aux _ _ φ_lt_ψ
  · simpa only [add_comm, inf_comm] using order_add_of_order_ne.aux _ _ ψ_lt_φ

Depends on / 依赖: add_comm, h.lt_or_gt, inf_comm, le_antisymm, lt_or_gt, min_order_le_order_add, order_add_of_order_ne, order_add_of_order_ne.aux
-/
theorem order_add_of_order_ne (φ ψ : R⟦X⟧) (h : order φ != order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  rcases h.lt_or_gt with (φ_lt_ψ | ψ_lt_φ)
  · apply order_add_of_order_ne.aux _ _ φ_lt_ψ
  · simpa only [add_comm, inf_comm] using order_add_of_order_ne.aux _ _ ψ_lt_φ

/--
theorem `le_order_map` / 定理 `le_order_map`

English:
theorem le_order_map
  given: {S : Type*} [Semiring S] (f : R ->+* S)
  proof: le_order _ _ fun i hi => by simp [coeff_of_lt_order i hi]

中文:
定理 le_order_map
  条件: {S : 类型} [半环 S] (f : R ->+* S)
  证明: le_order _ _ fun i hi => by simp [coeff_of_lt_order i hi]

Depends on / 依赖: coeff_of_lt_order, le_order
-/
theorem le_order_map {S : Type*} [Semiring S] (f : R ->+* S) :
    φ.order <= (φ.map f).order :=
  le_order _ _ fun i hi => by simp [coeff_of_lt_order i hi]

/--
theorem `le_order_smul` / 定理 `le_order_smul`

English:
theorem le_order_smul
  given: {a : R}
  proof: le_order _ φ.order fun i hi => by simp [coeff_of_lt_order i hi]

中文:
定理 le_order_smul
  条件: {a : R}
  证明: le_order _ φ.order fun i hi => by simp [coeff_of_lt_order i hi]

Depends on / 依赖: coeff_of_lt_order, le_order
-/
theorem le_order_smul {a : R} :
    φ.order <= (a • φ).order :=
  le_order _ φ.order fun i hi => by simp [coeff_of_lt_order i hi]

/--
theorem `le_order_mul` / 定理 `le_order_mul`

English:
theorem le_order_mul
  given: (φ ψ : R⟦X⟧)
  statement: order φ + order ψ <= order (φ * ψ)
  proof: by
  apply le_order
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
  by_cases! hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
  rw [mem_antidiagonal] at hij
  exfalso
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  rw [← Nat.cast_add]; rw [hij]

中文:
定理 le_order_mul
  条件: (φ ψ : R⟦X⟧)
  结论: order φ + order ψ <= order (φ * ψ)
  证明: by
  apply le_order
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
  by_cases! hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
  rw [mem_antidiagonal] at hij
  exfalso
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  rw [← Nat.cast_add]; rw [hij]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Nat.cast_add, add_le_add, cast_add, coeff_mul, coeff_of_lt_order, le_order, lt_of_lt_of_le, mem_antidiagonal, mul_zero, ne_of_lt, sum_eq_zero, zero_mul
-/
theorem le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ <= order (φ * ψ) := by
  apply le_order
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
  by_cases! hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
  rw [mem_antidiagonal] at hij
  exfalso
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  rw [← Nat.cast_add]; rw [hij]

/--
theorem `le_order_pow` / 定理 `le_order_pow`

English:
theorem le_order_pow
  given: (φ : R⟦X⟧) (n : Nat)
  statement: n • order φ <= order (φ ^ n)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => grw [add_smul, one_smul, pow_succ, ih, le_order_mul]

中文:
定理 le_order_pow
  条件: (φ : R⟦X⟧) (n : 自然数)
  结论: n • order φ <= order (φ ^ n)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => grw [add_smul, one_smul, pow_succ, ih, le_order_mul]

Depends on / 依赖: add_smul, le_order_mul, one_smul, pow_succ
-/
theorem le_order_pow (φ : R⟦X⟧) (n : Nat) : n • order φ <= order (φ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => grw [add_smul, one_smul, pow_succ, ih, le_order_mul]

/--
theorem `le_order_prod` / 定理 `le_order_prod`

English:
theorem le_order_prod
  given: {R : Type*} [CommSemiring R] {ι : Type*} (φ : ι -> R⟦X⟧) (s : Finset ι)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_order_mul]

alias order_mul_ge := le_order_mul

中文:
定理 le_order_prod
  条件: {R : 类型} [交换半环 R] {ι : 类型} (φ : ι -> R⟦X⟧) (s : 有限集 ι)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_order_mul]

alias order_mul_ge := le_order_mul

Depends on / 依赖: CompHausLike, Finset, Finset.cons_induction, Finset.prod_cons, Finset.sum_cons, cons_induction, le_order_mul, prod_cons, sum_cons
-/
theorem le_order_prod {R : Type*} [CommSemiring R] {ι : Type*} (φ : ι -> R⟦X⟧) (s : Finset ι) :
    ∑ i in s, (φ i).order <= (∏ i in s, φ i).order := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_order_mul]

alias order_mul_ge := le_order_mul

/--
theorem `one_le_order_iff_constCoeff_eq_zero` / 定理 `one_le_order_iff_constCoeff_eq_zero`

English:
theorem one_le_order_iff_constCoeff_eq_zero
  proof: by
  constructor
  · intro h
    rw [← coeff_zero_eq_constantCoeff]
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine le_order _ _ fun d hd => ?_
    rw [Nat.cast_lt_one] at hd
    simp [hd, h]

中文:
定理 one_le_order_iff_constCoeff_eq_zero
  证明: by
  constructor
  · intro h
    rw [← coeff_zero_eq_constantCoeff]
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine le_order _ _ fun d hd => ?_
    rw [Nat.cast_lt_one] at hd
    simp [hd, h]

Depends on / 依赖: Nat.cast_lt_one, Order.one_le_iff_pos.mp, cast_lt_one, coeff_of_lt_order, coeff_zero_eq_constantCoeff, le_order, one_le_iff_pos
-/
theorem one_le_order_iff_constCoeff_eq_zero :
    1 <= φ.order ↔ φ.constantCoeff = 0 := by
  constructor
  · intro h
    rw [← coeff_zero_eq_constantCoeff]
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine le_order _ _ fun d hd => ?_
    rw [Nat.cast_lt_one] at hd
    simp [hd, h]

/--
theorem `order_ne_zero_iff_constCoeff_eq_zero` / 定理 `order_ne_zero_iff_constCoeff_eq_zero`

English:
theorem order_ne_zero_iff_constCoeff_eq_zero
  given: {φ : R⟦X⟧}
  proof: by
  rw [← Order.one_le_iff_ne_zero]; rw [one_le_order_iff_constCoeff_eq_zero]

中文:
定理 order_ne_zero_iff_constCoeff_eq_zero
  条件: {φ : R⟦X⟧}
  证明: by
  rw [← Order.one_le_iff_ne_zero]; rw [one_le_order_iff_constCoeff_eq_zero]

Depends on / 依赖: Order.one_le_iff_ne_zero, one_le_iff_ne_zero, one_le_order_iff_constCoeff_eq_zero
-/
theorem order_ne_zero_iff_constCoeff_eq_zero {φ : R⟦X⟧} :
    φ.order != 0 ↔ φ.constantCoeff = 0 := by
  rw [← Order.one_le_iff_ne_zero]; rw [one_le_order_iff_constCoeff_eq_zero]

/--
theorem `le_order_pow_of_constantCoeff_eq_zero` / 定理 `le_order_pow_of_constantCoeff_eq_zero`

English:
theorem le_order_pow_of_constantCoeff_eq_zero
  given: (n : Nat) (hf : φ.constantCoeff = 0)
  proof: by
  refine .trans ?_ (le_order_pow _ n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

中文:
定理 le_order_pow_of_constantCoeff_eq_zero
  条件: (n : 自然数) (hf : φ.constantCoeff = 0)
  证明: by
  refine .trans ?_ (le_order_pow _ n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

Depends on / 依赖: le_mul_of_one_le_right, le_order_pow, one_le_order_iff_constCoeff_eq_zero, one_le_order_iff_constCoeff_eq_zero.mpr
-/
theorem le_order_pow_of_constantCoeff_eq_zero (n : Nat) (hf : φ.constantCoeff = 0) :
    n <= (φ ^ n).order := by
  refine .trans ?_ (le_order_pow _ n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

/--
theorem `order_monomial` / 定理 `order_monomial`

English:
theorem order_monomial
  given: (n : Nat) (a : R) [Decidable (a = 0)]
  proof: by
  split_ifs with h
  · rw [h, order_eq_top, map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · simp only [Nat.cast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · simp only [Nat.cast_lt] at hi
      rw [coeff_monomial]; rw [if_neg]
      exact ne_of_lt hi

中文:
定理 order_monomial
  条件: (n : 自然数) (a : R) [可判定 (a = 0)]
  证明: by
  split_ifs with h
  · rw [h, order_eq_top, map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · simp only [Nat.cast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · simp only [Nat.cast_lt] at hi
      rw [coeff_monomial]; rw [if_neg]
      exact ne_of_lt hi

Depends on / 依赖: Nat.cast_inj, Nat.cast_lt, cast_inj, cast_lt, coeff_monomial, coeff_monomial_same, if_neg, map_zero, ne_of_lt, order_eq, order_eq_top, split_ifs
-/
theorem order_monomial (n : Nat) (a : R) [Decidable (a = 0)] :
    order (monomial n a) = if a = 0 then (⊤ : Nat∞) else n := by
  split_ifs with h
  · rw [h, order_eq_top, map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · simp only [Nat.cast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · simp only [Nat.cast_lt] at hi
      rw [coeff_monomial]; rw [if_neg]
      exact ne_of_lt hi

/--
theorem `order_monomial_of_ne_zero` / 定理 `order_monomial_of_ne_zero`

English:
theorem order_monomial_of_ne_zero
  given: (n : Nat) (a : R) (h : a != 0)
  statement: order (monomial n a) = n
  proof: by
  classical
  rw [order_monomial]; rw [if_neg h]

中文:
定理 order_monomial_of_ne_zero
  条件: (n : 自然数) (a : R) (h : a != 0)
  结论: order (monomial n a) = n
  证明: by
  classical
  rw [order_monomial]; rw [if_neg h]

Depends on / 依赖: classical, if_neg, order_monomial
-/
theorem order_monomial_of_ne_zero (n : Nat) (a : R) (h : a != 0) : order (monomial n a) = n := by
  classical
  rw [order_monomial]; rw [if_neg h]

/--
theorem `coeff_mul_of_lt_order` / 定理 `coeff_mul_of_lt_order`

English:
theorem coeff_mul_of_lt_order
  given: {φ ψ : R⟦X⟧} {n : Nat} (h : ↑n < ψ.order)
  proof: by
  suffices coeff n (φ * ψ) = ∑ p in antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  lia

中文:
定理 coeff_mul_of_lt_order
  条件: {φ ψ : R⟦X⟧} {n : 自然数} (h : ↑n < ψ.order)
  证明: by
  suffices coeff n (φ * ψ) = ∑ p in antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  lia

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_const_zero, antidiagonal, coeff_mul, coeff_of_lt_order, lt_of_le_of_lt, mem_antidiagonal, mul_eq_zero_of_right, sum_congr, sum_const_zero, x.fst, x.snd
-/
theorem coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n : Nat} (h : ↑n < ψ.order) :
    coeff n (φ * ψ) = 0 := by
  suffices coeff n (φ * ψ) = ∑ p in antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  lia

/--
theorem `coeff_mul_one_sub_of_lt_order` / 定理 `coeff_mul_one_sub_of_lt_order`

English:
theorem coeff_mul_one_sub_of_lt_order
  statement: {R : Type*} [Ring R] {φ ψ : R⟦X⟧} (n : Nat)
  proof: by
  simp [coeff_mul_of_lt_order h, mul_sub]

中文:
定理 coeff_mul_one_sub_of_lt_order
  结论: {R : 类型} [环 R] {φ ψ : R⟦X⟧} (n : 自然数)
  证明: by
  simp [coeff_mul_of_lt_order h, mul_sub]

Depends on / 依赖: coeff_mul_of_lt_order, mul_sub
-/
theorem coeff_mul_one_sub_of_lt_order {R : Type*} [Ring R] {φ ψ : R⟦X⟧} (n : Nat)
    (h : ↑n < ψ.order) : coeff n (φ * (1 - ψ)) = coeff n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]

/--
theorem `coeff_mul_prod_one_sub_of_lt_order` / 定理 `coeff_mul_prod_one_sub_of_lt_order`

English:
theorem coeff_mul_prod_one_sub_of_lt_order
  statement: {R ι : Type*} [CommRing R] (k : Nat) (s : Finset ι)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha]; rw [← mul_assoc]; rw [mul_right_comm]; rw [coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

@[simp]

中文:
定理 coeff_mul_prod_one_sub_of_lt_order
  结论: {R ι : 类型} [交换环 R] (k : 自然数) (s : 有限集 ι)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha]; rw [← mul_assoc]; rw [mul_right_comm]; rw [coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

@[simp]

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.prod_insert, classical, coeff_mul_one_sub_of_lt_order, forall_eq_or_imp, induction_on, insert, mem_insert, mul_assoc, mul_right_comm, prod_insert
-/
theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : Nat) (s : Finset ι)
    (φ : R⟦X⟧) (f : ι -> R⟦X⟧) :
    (forall i in s, ↑k < (f i).order) -> coeff k (φ * ∏ i in s, (1 - f i)) = coeff k φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha]; rw [← mul_assoc]; rw [mul_right_comm]; rw [coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

@[simp]
/--
theorem `order_neg` / 定理 `order_neg`

English:
theorem order_neg
  given: {R : Type*} [Ring R] (φ : PowerSeries R)
  statement: (-φ).order = φ.order
  proof: by
  by_contra! h
  have : φ = 0 := by simpa using (order_add_of_order_ne _ _ h).symm
  simp [this] at h

中文:
定理 order_neg
  条件: {R : 类型} [环 R] (φ : 幂级数 R)
  结论: (-φ).order = φ.order
  证明: by
  by_contra! h
  have : φ = 0 := by simpa using (order_add_of_order_ne _ _ h).symm
  simp [this] at h

Depends on / 依赖: order_add_of_order_ne
-/
theorem order_neg {R : Type*} [Ring R] (φ : PowerSeries R) : (-φ).order = φ.order := by
  by_contra! h
  have : φ = 0 := by simpa using (order_add_of_order_ne _ _ h).symm
  simp [this] at h

/--
Definition of `divXPowOrder` / `divXPowOrder` 的定义

English:
definition divXPowOrder
  signature: (f : R⟦X⟧)
  body: .mk fun n => coeff (n + f.order.toNat) f

@[simp]

中文:
定义 divXPowOrder
  签名: (f : R⟦X⟧)
  定义体: .mk fun n => coeff (n + f.order.toNat) f

@[simp]

Depends on / 依赖: f.order.toNat
-/
def divXPowOrder (f : R⟦X⟧) : R⟦X⟧ :=
  .mk fun n => coeff (n + f.order.toNat) f

@[simp]
/--
lemma `coeff_divXPowOrder` / 引理 `coeff_divXPowOrder`

English:
lemma coeff_divXPowOrder
  given: {f : R⟦X⟧} {n : Nat}
  proof: coeff_mk _ _

@[simp]

中文:
引理 coeff_divXPowOrder
  条件: {f : R⟦X⟧} {n : 自然数}
  证明: coeff_mk _ _

@[simp]

Depends on / 依赖: coeff_mk
-/
lemma coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} :
    coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f :=
  coeff_mk _ _

@[simp]
/--
lemma `divXPowOrder_zero` / 引理 `divXPowOrder_zero`

English:
lemma divXPowOrder_zero
  proof: by
  ext
  simp

中文:
引理 divXPowOrder_zero
  证明: by
  ext
  simp
-/
lemma divXPowOrder_zero :
    divXPowOrder (0 : R⟦X⟧) = 0 := by
  ext
  simp

/--
lemma `constantCoeff_divXPowOrder` / 引理 `constantCoeff_divXPowOrder`

English:
lemma constantCoeff_divXPowOrder
  given: {f : R⟦X⟧}
  proof: by
  simp [← coeff_zero_eq_constantCoeff]

中文:
引理 constantCoeff_divXPowOrder
  条件: {f : R⟦X⟧}
  证明: by
  simp [← coeff_zero_eq_constantCoeff]

Depends on / 依赖: coeff_zero_eq_constantCoeff
-/
lemma constantCoeff_divXPowOrder {f : R⟦X⟧} :
    constantCoeff (divXPowOrder f) = coeff f.order.toNat f := by
  simp [← coeff_zero_eq_constantCoeff]

/--
lemma `constantCoeff_divXPowOrder_eq_zero_iff` / 引理 `constantCoeff_divXPowOrder_eq_zero_iff`

English:
lemma constantCoeff_divXPowOrder_eq_zero_iff
  given: {f : R⟦X⟧}
  proof: by
  by_cases h : f = 0
  · simp [h]
  · simp [constantCoeff_divXPowOrder, coeff_order h, h]

中文:
引理 constantCoeff_divXPowOrder_eq_zero_iff
  条件: {f : R⟦X⟧}
  证明: by
  by_cases h : f = 0
  · simp [h]
  · simp [constantCoeff_divXPowOrder, coeff_order h, h]

Depends on / 依赖: coeff_order, constantCoeff_divXPowOrder
-/
lemma constantCoeff_divXPowOrder_eq_zero_iff {f : R⟦X⟧} :
    constantCoeff (divXPowOrder f) = 0 ↔ f = 0 := by
  by_cases h : f = 0
  · simp [h]
  · simp [constantCoeff_divXPowOrder, coeff_order h, h]

/--
theorem `X_pow_order_mul_divXPowOrder` / 定理 `X_pow_order_mul_divXPowOrder`

English:
theorem X_pow_order_mul_divXPowOrder
  given: {f : R⟦X⟧}
  proof: by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [h]
  · push Not at h
    rw [coeff_of_lt_order_toNat _ h]

中文:
定理 X_pow_order_mul_divXPowOrder
  条件: {f : R⟦X⟧}
  证明: by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [h]
  · push Not at h
    rw [coeff_of_lt_order_toNat _ h]

Depends on / 依赖: coeff_X_pow_mul, coeff_of_lt_order_toNat, split_ifs
-/
theorem X_pow_order_mul_divXPowOrder {f : R⟦X⟧} :
    X ^ f.order.toNat * divXPowOrder f = f := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [h]
  · push Not at h
    rw [coeff_of_lt_order_toNat _ h]

/--
theorem `X_pow_order_dvd` / 定理 `X_pow_order_dvd`

English:
theorem X_pow_order_dvd
  statement: X ^ φ.order.toNat ∣ φ
  proof: by
  simpa only [X_pow_dvd_iff] using coeff_of_lt_order_toNat

中文:
定理 X_pow_order_dvd
  结论: X ^ φ.order.to自然数 ∣ φ
  证明: by
  simpa only [X_pow_dvd_iff] using coeff_of_lt_order_toNat

Depends on / 依赖: X_pow_dvd_iff, coeff_of_lt_order_toNat
-/
theorem X_pow_order_dvd : X ^ φ.order.toNat ∣ φ := by
  simpa only [X_pow_dvd_iff] using coeff_of_lt_order_toNat

/--
theorem `order_eq_emultiplicity_X` / 定理 `order_eq_emultiplicity_X`

English:
theorem order_eq_emultiplicity_X
  given: {R : Type*} [Semiring R] (φ : R⟦X⟧)
  proof: by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.toNat = n := by simp [ho]
    rw [← hn]; rw [eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff n) H
      rw [X_pow_mul]; rw [coeff_mul_of_lt_order]; rw [← hn] at this
      · exact coeff_order hφ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.natCast_lt_natCast]
          simp

中文:
定理 order_eq_emultiplicity_X
  条件: {R : 类型} [半环 R] (φ : R⟦X⟧)
  证明: by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.toNat = n := by simp [ho]
    rw [← hn]; rw [eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff n) H
      rw [X_pow_mul]; rw [coeff_mul_of_lt_order]; rw [← hn] at this
      · exact coeff_order hφ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.natCast_lt_natCast]
          simp

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Order.le_of_lt_add_one, X_pow_mul, X_pow_order_dvd, cast_add, cast_one, classical, coeff_mul_of_lt_order, congr_arg, eq_comm, eq_or_ne, le_antisymm, le_emultiplicity_of_pow_dvd, le_of_lt_add_one, not_le, order.toNat, pow_dvd_iff_le_emultiplicity
-/
theorem order_eq_emultiplicity_X {R : Type*} [Semiring R] (φ : R⟦X⟧) :
    order φ = emultiplicity X φ := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.toNat = n := by simp [ho]
    rw [← hn]; rw [eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff n) H
      rw [X_pow_mul]; rw [coeff_mul_of_lt_order]; rw [← hn] at this
      · exact coeff_order hφ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.natCast_lt_natCast]
          simp

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`. -/
@[simp]
/--
theorem `order_one` / 定理 `order_one`

English:
theorem order_one
  statement: order (1 : R⟦X⟧) = 0
  proof: by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

中文:
定理 order_one
  结论: order (1 : R⟦X⟧) = 0
  证明: by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

Depends on / 依赖: one_ne_zero, order_monomial_of_ne_zero
-/
theorem order_one : order (1 : R⟦X⟧) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

/--
theorem `order_zero_of_unit` / 定理 `order_zero_of_unit`

English:
theorem order_zero_of_unit
  given: {f : R⟦X⟧}
  statement: IsUnit f -> f.order = 0
  proof: by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero]; rw [← hf]; rw [← nonpos_iff_eq_zero]; rw [← @order_one R _ _]; rw [← hu]
  exact order_mul_ge _ _

中文:
定理 order_zero_of_unit
  条件: {f : R⟦X⟧}
  结论: 是单位 f -> f.order = 0
  证明: by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero]; rw [← hf]; rw [← nonpos_iff_eq_zero]; rw [← @order_one R _ _]; rw [← hu]
  exact order_mul_ge _ _

Depends on / 依赖: And.left, CompactSpace, X.toTop, add_eq_zero, nonpos_iff_eq_zero, order_mul_ge, order_one
-/
theorem order_zero_of_unit {f : R⟦X⟧} : IsUnit f -> f.order = 0 := by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero]; rw [← hf]; rw [← nonpos_iff_eq_zero]; rw [← @order_one R _ _]; rw [← hu]
  exact order_mul_ge _ _

/-- The order of the formal power series `X` is `1`. -/
@[simp]
/--
theorem `order_X` / 定理 `order_X`

English:
theorem order_X
  statement: order (X : R⟦X⟧) = 1
  proof: by
  simpa only [Nat.cast_one] using! order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

中文:
定理 order_X
  结论: order (X : R⟦X⟧) = 1
  证明: by
  simpa only [Nat.cast_one] using! order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

Depends on / 依赖: Nat.cast_one, T2Space, X.toTop, cast_one, one_ne_zero, order_monomial_of_ne_zero
-/
theorem order_X : order (X : R⟦X⟧) = 1 := by
  simpa only [Nat.cast_one] using! order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

/-- The order of the formal power series `X^n` is `n`. -/
@[simp]
/--
theorem `order_X_pow` / 定理 `order_X_pow`

English:
theorem order_X_pow
  given: (n : Nat)
  statement: order ((X : R⟦X⟧) ^ n) = n
  proof: by
  rw [X_pow_eq]; rw [order_monomial_of_ne_zero]
  exact one_ne_zero

中文:
定理 order_X_pow
  条件: (n : 自然数)
  结论: order ((X : R⟦X⟧) ^ n) = n
  证明: by
  rw [X_pow_eq]; rw [order_monomial_of_ne_zero]
  exact one_ne_zero

Depends on / 依赖: X_pow_eq, one_ne_zero, order_monomial_of_ne_zero
-/
theorem order_X_pow (n : Nat) : order ((X : R⟦X⟧) ^ n) = n := by
  rw [X_pow_eq]; rw [order_monomial_of_ne_zero]
  exact one_ne_zero

/-- Dividing `X` by the maximal power of `X` dividing it leaves `1`. -/
@[simp]
/--
theorem `divXPowOrder_X` / 定理 `divXPowOrder_X`

English:
theorem divXPowOrder_X
  proof: by
  ext n
  simp [coeff_X]

中文:
定理 divXPowOrder_X
  证明: by
  ext n
  simp [coeff_X]

Depends on / 依赖: coeff_X
-/
theorem divXPowOrder_X :
    divXPowOrder X = (1 : R⟦X⟧) := by
  ext n
  simp [coeff_X]

/--
theorem `divXPowOrder_one` / 定理 `divXPowOrder_one`

English:
theorem divXPowOrder_one
  statement: divXPowOrder 1 = (1 : R⟦X⟧)
  proof: by
  ext k
  simp

中文:
定理 divXPowOrder_one
  结论: divXPowOrder 1 = (1 : R⟦X⟧)
  证明: by
  ext k
  simp
-/
theorem divXPowOrder_one : divXPowOrder 1 = (1 : R⟦X⟧) := by
  ext k
  simp

end OrderZeroNeOne

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R]

/--
theorem `order_mul` / 定理 `order_mul`

English:
theorem order_mul
  given: (φ ψ : R⟦X⟧)
  statement: order (φ * ψ) = order φ + order ψ
  proof: by
  apply le_antisymm _ (le_order_mul _ _)
  by_cases! h : φ = 0 ∨ ψ = 0
  · rcases h with h | h <;> simp [h]
  · rw [← coe_toNat_order h.1, ← coe_toNat_order h.2, ← ENat.natCast_add]
    apply order_le
    rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem ⟨φ.order.toNat]; rw [ψ.order.toNat⟩ (by simp)]
    · exact mul_ne_zero (coeff_order h.1) (coeff_order h.2)
    · intro ij hij h
      rcases trichotomy_of_add_eq_add (mem_antidiagonal.mp hij) with h' | h' | h'
      · exact False.elim (h (by simp [Prod.ext_iff, h'.1, h'.2]))
      · rw [coeff_of_lt_order_toNat ij.1 h', zero_mul]
      · rw [coeff_of_lt_order_toNat ij.2 h', mul_zero]

中文:
定理 order_mul
  条件: (φ ψ : R⟦X⟧)
  结论: order (φ * ψ) = order φ + order ψ
  证明: by
  apply le_antisymm _ (le_order_mul _ _)
  by_cases! h : φ = 0 ∨ ψ = 0
  · rcases h with h | h <;> simp [h]
  · rw [← coe_toNat_order h.1, ← coe_toNat_order h.2, ← ENat.natCast_add]
    apply order_le
    rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem ⟨φ.order.toNat]; rw [ψ.order.toNat⟩ (by simp)]
    · exact mul_ne_zero (coeff_order h.1) (coeff_order h.2)
    · intro ij hij h
      rcases trichotomy_of_add_eq_add (mem_antidiagonal.mp hij) with h' | h' | h'
      · exact False.elim (h (by simp [Prod.ext_iff, h'.1, h'.2]))
      · rw [coeff_of_lt_order_toNat ij.1 h', zero_mul]
      · rw [coeff_of_lt_order_toNat ij.2 h', mul_zero]

Depends on / 依赖: ENat.natCast_add, False.elim, Finset, Finset.sum_eq_single_of_mem, Prod.ext_iff, coe_toNat_order, coeff_mul, coeff_order, ext_iff, le_antisymm, le_order_mul, mem_antidiagonal, mem_antidiagonal.mp, mul_ne_zero, natCast_add, order.toNat, order_le, sum_eq_single_of_mem, trichotomy_of_add_eq_add
-/
theorem order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ := by
  apply le_antisymm _ (le_order_mul _ _)
  by_cases! h : φ = 0 ∨ ψ = 0
  · rcases h with h | h <;> simp [h]
  · rw [← coe_toNat_order h.1, ← coe_toNat_order h.2, ← ENat.natCast_add]
    apply order_le
    rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem ⟨φ.order.toNat]; rw [ψ.order.toNat⟩ (by simp)]
    · exact mul_ne_zero (coeff_order h.1) (coeff_order h.2)
    · intro ij hij h
      rcases trichotomy_of_add_eq_add (mem_antidiagonal.mp hij) with h' | h' | h'
      · exact False.elim (h (by simp [Prod.ext_iff, h'.1, h'.2]))
      · rw [coeff_of_lt_order_toNat ij.1 h', zero_mul]
      · rw [coeff_of_lt_order_toNat ij.2 h', mul_zero]

/--
theorem `divXPowOrder_mul` / 定理 `divXPowOrder_mul`

English:
theorem divXPowOrder_mul
  given: {f g : R⟦X⟧}
  proof: by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with (h | h) <;> simp [h]
  apply X_pow_mul_cancel (k := f.order.toNat + g.order.toNat)
  calc
    _ = X ^ ((f * g).order.toNat) * (f * g).divXPowOrder := by
        rw [order_mul]; rw [ENat.toNat_add (order_eq_top.not.mpr h.1) (order_eq_top.not.mpr h.2)]
    _ = f * g := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = (X ^ f.order.toNat * f.divXPowOrder) * (X ^ g.order.toNat * g.divXPowOrder) := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = f.divXPowOrder * g.divXPowOrder * X ^ (g.order.toNat + f.order.toNat) := by
        rw [mul_assoc]; rw [X_pow_mul]; rw [X_pow_mul]; rw [← mul_assoc]; rw [mul_assoc]; rw [← pow_add]
    _ = X ^ (f.order.toNat + g.order.toNat) * (f.divXPowOrder * g.divXPowOrder) := by
        rw [X_pow_mul]; rw [add_comm]

中文:
定理 divXPowOrder_mul
  条件: {f g : R⟦X⟧}
  证明: by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with (h | h) <;> simp [h]
  apply X_pow_mul_cancel (k := f.order.toNat + g.order.toNat)
  calc
    _ = X ^ ((f * g).order.toNat) * (f * g).divXPowOrder := by
        rw [order_mul]; rw [ENat.toNat_add (order_eq_top.not.mpr h.1) (order_eq_top.not.mpr h.2)]
    _ = f * g := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = (X ^ f.order.toNat * f.divXPowOrder) * (X ^ g.order.toNat * g.divXPowOrder) := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = f.divXPowOrder * g.divXPowOrder * X ^ (g.order.toNat + f.order.toNat) := by
        rw [mul_assoc]; rw [X_pow_mul]; rw [X_pow_mul]; rw [← mul_assoc]; rw [mul_assoc]; rw [← pow_add]
    _ = X ^ (f.order.toNat + g.order.toNat) * (f.divXPowOrder * g.divXPowOrder) := by
        rw [X_pow_mul]; rw [add_comm]

Depends on / 依赖: ENat.toNat_add, X_pow_mul_cancel, X_pow_order_mul_divXPowOrder, divXPowOrder, f.divXPowOrder, f.order.toNat, g.divXPowOrder, g.order.toNat, order.toNat, order_eq_top, order_eq_top.not.mpr, order_mul, toNat_add
-/
theorem divXPowOrder_mul {f g : R⟦X⟧} :
    divXPowOrder (f * g) = divXPowOrder f * divXPowOrder g := by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with (h | h) <;> simp [h]
  apply X_pow_mul_cancel (k := f.order.toNat + g.order.toNat)
  calc
    _ = X ^ ((f * g).order.toNat) * (f * g).divXPowOrder := by
        rw [order_mul]; rw [ENat.toNat_add (order_eq_top.not.mpr h.1) (order_eq_top.not.mpr h.2)]
    _ = f * g := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = (X ^ f.order.toNat * f.divXPowOrder) * (X ^ g.order.toNat * g.divXPowOrder) := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = f.divXPowOrder * g.divXPowOrder * X ^ (g.order.toNat + f.order.toNat) := by
        rw [mul_assoc]; rw [X_pow_mul]; rw [X_pow_mul]; rw [← mul_assoc]; rw [mul_assoc]; rw [← pow_add]
    _ = X ^ (f.order.toNat + g.order.toNat) * (f.divXPowOrder * g.divXPowOrder) := by
        rw [X_pow_mul]; rw [add_comm]

variable [Nontrivial R]

/--
Definition of `orderHom` / `orderHom` 的定义

English:
definition orderHom
  signature: : R⟦X⟧ ->* Multiplicative Nat∞ where
  body: .ofAdd g.order
  map_one' := order_one
  map_mul' := order_mul

@[simp, norm_cast]

中文:
定义 orderHom
  签名: : R⟦X⟧ ->* Multiplicative 自然数∞ where
  定义体: .ofAdd g.order
  map_one' := order_one
  map_mul' := order_mul

@[simp, norm_cast]

Depends on / 依赖: g.order
-/
def orderHom : R⟦X⟧ ->* Multiplicative Nat∞ where
  toFun g := .ofAdd g.order
  map_one' := order_one
  map_mul' := order_mul

@[simp, norm_cast]
/--
lemma `coe_orderHom` / 引理 `coe_orderHom`

English:
lemma coe_orderHom
  statement: (orderHom : R⟦X⟧ -> Nat∞) = order
  proof: rfl

中文:
引理 coe_orderHom
  结论: (orderHom : R⟦X⟧ -> 自然数∞) = order
  证明: rfl
-/
lemma coe_orderHom : (orderHom : R⟦X⟧ -> Nat∞) = order := rfl

/--
theorem `order_pow` / 定理 `order_pow`

English:
theorem order_pow
  given: (φ : R⟦X⟧) (n : Nat)
  statement: order (φ ^ n) = n • order φ
  proof: map_pow orderHom φ n

中文:
定理 order_pow
  条件: (φ : R⟦X⟧) (n : 自然数)
  结论: order (φ ^ n) = n • order φ
  证明: map_pow orderHom φ n

Depends on / 依赖: map_pow, orderHom
-/
theorem order_pow (φ : R⟦X⟧) (n : Nat) : order (φ ^ n) = n • order φ :=
  map_pow orderHom φ n

/--
theorem `order_prod` / 定理 `order_prod`

English:
theorem order_prod
  statement: {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
  proof: map_prod orderHom φ s

中文:
定理 order_prod
  结论: {R : 类型} [交换半环 R] [无零因子 R] [非平凡 R] {ι : 类型}
  证明: map_prod orderHom φ s

Depends on / 依赖: map_prod, orderHom
-/
theorem order_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
    (φ : ι -> R⟦X⟧) (s : Finset ι) : (∏ i in s, φ i).order = ∑ i in s, (φ i).order :=
  map_prod orderHom φ s

/--
Definition of `divXPowOrderHom` / `divXPowOrderHom` 的定义

English:
definition divXPowOrderHom
  signature: : R⟦X⟧ ->* R⟦X⟧ where
  body: g.divXPowOrder
  map_one' := divXPowOrder_one
  map_mul' f g := divXPowOrder_mul (f := f) (g := g)

@[simp, norm_cast]

中文:
定义 divXPowOrderHom
  签名: : R⟦X⟧ ->* R⟦X⟧ where
  定义体: g.divXPowOrder
  map_one' := divXPowOrder_one
  map_mul' f g := divXPowOrder_mul (f := f) (g := g)

@[simp, norm_cast]

Depends on / 依赖: divXPowOrder, g.divXPowOrder
-/
def divXPowOrderHom : R⟦X⟧ ->* R⟦X⟧ where
  toFun g := g.divXPowOrder
  map_one' := divXPowOrder_one
  map_mul' f g := divXPowOrder_mul (f := f) (g := g)

@[simp, norm_cast]
/--
lemma `coe_divXPowOrderHom` / 引理 `coe_divXPowOrderHom`

English:
lemma coe_divXPowOrderHom
  statement: (divXPowOrderHom : R⟦X⟧ -> R⟦X⟧) = divXPowOrder
  proof: rfl

中文:
引理 coe_divXPowOrderHom
  结论: (divXPowOrderHom : R⟦X⟧ -> R⟦X⟧) = divXPowOrder
  证明: rfl
-/
lemma coe_divXPowOrderHom : (divXPowOrderHom : R⟦X⟧ -> R⟦X⟧) = divXPowOrder := rfl

/--
theorem `divXPowOrder_pow` / 定理 `divXPowOrder_pow`

English:
theorem divXPowOrder_pow
  given: (φ : R⟦X⟧) (n : Nat)
  statement: divXPowOrder (φ ^ n) = (divXPowOrder φ) ^ n
  proof: map_pow divXPowOrderHom φ n

中文:
定理 divXPowOrder_pow
  条件: (φ : R⟦X⟧) (n : 自然数)
  结论: divXPowOrder (φ ^ n) = (divXPowOrder φ) ^ n
  证明: map_pow divXPowOrderHom φ n

Depends on / 依赖: divXPowOrderHom, map_pow
-/
theorem divXPowOrder_pow (φ : R⟦X⟧) (n : Nat) : divXPowOrder (φ ^ n) = (divXPowOrder φ) ^ n :=
  map_pow divXPowOrderHom φ n

/--
theorem `divXPowOrder_prod` / 定理 `divXPowOrder_prod`

English:
theorem divXPowOrder_prod
  statement: {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
  proof: map_prod divXPowOrderHom φ s

中文:
定理 divXPowOrder_prod
  结论: {R : 类型} [交换半环 R] [无零因子 R] [非平凡 R] {ι : 类型}
  证明: map_prod divXPowOrderHom φ s

Depends on / 依赖: divXPowOrderHom, map_prod
-/
theorem divXPowOrder_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
    (φ : ι -> R⟦X⟧) (s : Finset ι) : (∏ i in s, φ i).divXPowOrder = ∏ i in s, (φ i).divXPowOrder :=
  map_prod divXPowOrderHom φ s

end NoZeroDivisors

section Ring

variable [Ring R] (p : PowerSeries R) (T : Subring R) (hp : forall n, p.coeff n in T)

@[simp]
/--
theorem `order_toSubring` / 定理 `order_toSubring`

English:
theorem order_toSubring
  statement: (p.toSubring T hp).order = p.order
  proof: by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_order _ _ fun d hd => by simp [coeff_of_lt_order d hd, ← coeff_toSubring p T hp]
  · exact le_order _ _ fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order d hd)

中文:
定理 order_toSubring
  结论: (p.toSubring T hp).order = p.order
  证明: by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_order _ _ fun d hd => by simp [coeff_of_lt_order d hd, ← coeff_toSubring p T hp]
  · exact le_order _ _ fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order d hd)

Depends on / 依赖: coeff_of_lt_order, coeff_toSubring, eq_of_le_of_ge, le_order
-/
theorem order_toSubring : (p.toSubring T hp).order = p.order := by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_order _ _ fun d hd => by simp [coeff_of_lt_order d hd, ← coeff_toSubring p T hp]
  · exact le_order _ _ fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order d hd)

end Ring

end PowerSeries

end
