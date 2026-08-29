/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.UniformSpace.DiscreteUniformity


/-!
# Laurent Series

In this file we define `LaurentSeries R`, the formal Laurent series over `R`, here an *arbitrary*
type with a zero. They are denoted `R⸨X⸩`.

## Main Definitions

* Defines `LaurentSeries` as an abbreviation for `HahnSeries ℤ`.
* Defines `hasseDeriv` of a Laurent series with coefficients in a module over a ring.
* Provides a coercion from power series `R⟦X⟧` into `R⸨X⸩` given by `HahnSeries.ofPowerSeries`.
* Defines `LaurentSeries.powerSeriesPart`
* Defines the localization map `LaurentSeries.of_powerSeries_localization` which evaluates to
  `HahnSeries.ofPowerSeries`.
* Embedding of rational functions into Laurent series, provided as a coercion, utilizing
  the underlying `RatFunc.coeAlgHom`.
* Study of the `X`-Adic valuation on the ring of Laurent series over a field
* In `LaurentSeries.uniformContinuous_coeff` we show that sending a Laurent series to its `d`th
  coefficient is uniformly continuous, ensuring that it sends a Cauchy filter `ℱ` in `K⸨X⸩`
  to a Cauchy filter in `K`: since this latter is given the discrete topology, this provides an
  element `LaurentSeries.Cauchy.coeff ℱ d` in `K` that serves as `d`th coefficient of the Laurent
  series to which the filter `ℱ` converges.

## Main Results

* Basic properties of Hasse derivatives

### About the `X`-Adic valuation:
* The (integral) valuation of a power series is the order of the first non-zero coefficient, see
  `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`.
* The valuation of a Laurent series is the order of the first non-zero coefficient, see
  `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`.
* Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power series, see
  `LaurentSeries.val_le_one_iff_eq_coe`.
* The uniform space of `LaurentSeries` over a field is complete, formalized in the instance
  `instLaurentSeriesComplete`.
* The field of rational functions is dense in `LaurentSeries`: this is the declaration
  `LaurentSeries.coe_range_dense` and relies principally upon `LaurentSeries.exists_ratFunc_val_lt`,
  stating that for every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational function `Q`
  such that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`.
* In `LaurentSeries.valuation_compare` we prove that the extension of the `X`-adic valuation from
  `K⟮X⟯` up to its abstract completion coincides, modulo the isomorphism with `K⸨X⸩`, with the
  `X`-adic valuation on `K⸨X⸩`.
* The two declarations `LaurentSeries.mem_integers_of_powerSeries` and
  `LaurentSeries.exists_powerSeries_of_memIntegers` show that an element in the completion of
  `K⟮X⟯` is in the unit ball if and only if it comes from a power series through the
  isomorphism `LaurentSeriesRingEquiv`.
* `LaurentSeries.powerSeriesAlgEquiv` is the `K`-algebra isomorphism between `K⟦X⟧`
  and the unit ball inside the `X`-adic completion of `K⟮X⟯`.

## Implementation details

* Since `LaurentSeries` is just an abbreviation of `HahnSeries ℤ`, the definition of the
  coefficients is given in terms of `HahnSeries.coeff` and this forces sometimes to go
  back-and-forth from `X : R⸨X⸩` to `single 1 1 : R⟦ℤ⟧`.
* To prove the isomorphism between the `X`-adic completion of `K⟮X⟯` and `K⸨X⸩` we construct
  two completions of `K⟮X⟯`: the first (`LaurentSeries.ratfuncAdicComplPkg`) is its abstract
  uniform completion; the second (`LaurentSeries.LaurentSeriesPkg`) is simply `K⸨X⸩`, once we prove
  that it is complete and contains `K⟮X⟯` as a dense subspace. The isomorphism is the
  comparison equivalence, expressing the mathematical idea that the completion "is unique". It is
  `LaurentSeries.comparePkg`.
* For applications to `K⟦X⟧` it is actually more handy to use the *inverse* of the above
  equivalence: `LaurentSeries.LaurentSeriesAlgEquiv` is the *topological, algebra equivalence*
  `K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K`.
* In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion of
  `K⟮X⟯` we consider its alias `LaurentSeries.powerSeries_as_subring` as a subring of `K⸨X⸩`,
  that is itself clearly isomorphic (via the inverse of `LaurentSeries.powerSeriesEquivSubring`)
  to `K⟦X⟧`.

-/

@[expose] public section
universe u

open scoped PowerSeries
open HahnSeries Polynomial

noncomputable section

/--
Definition of `LaurentSeries` / `LaurentSeries` 的定义

English:
abbreviation LaurentSeries
  signature: (R : Type u) [Zero R]
  body: R⟦Int⟧

中文:
缩写 Laurent级数
  签名: (R : 类型u) [零 R]
  定义体: R⟦Int⟧
-/
abbrev LaurentSeries (R : Type u) [Zero R] := R⟦Int⟧

variable {R : Type*}

namespace LaurentSeries

section

/-- `R⸨X⸩` is notation for `LaurentSeries R`. -/
scoped notation:9000 R "⸨X⸩" => LaurentSeries R

end

section HasseDeriv

/--
Definition of `hasseDeriv` / `hasseDeriv` 的定义

English:
definition hasseDeriv
  signature: (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] (k : Nat)
  body: HahnSeries.ofSuppBddBelow (fun n => Ring.choose (n + k) k • f.coeff (n + k)) by
    refine ⟨f.order - k, fun x h => ?_⟩
    contrapose! h
    rw [Function.notMem_support]; rw [coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h]; rw [smul_zero]
  map_add' f g := by
    ext
    simp only [ofSuppBddBe

中文:
定义 hasseDeriv
  签名: (R : 类型) {V : 类型} [加法交换群 V] [半环 R] [模 R V] (k : 自然数)
  定义体: HahnSeries.ofSuppBddBelow (fun n => Ring.choose (n + k) k • f.coeff (n + k)) by
    refine ⟨f.order - k, fun x h => ?_⟩
    contrapose! h
    rw [Function.notMem_support]; rw [coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h]; rw [smul_zero]
  map_add' f g := by
    ext
    simp only [ofSuppBddBe

Depends on / 依赖: Function, Function.notMem_support, HahnSeries, HahnSeries.coeff_smul, HahnSeries.ofSuppBddBelow, Pi.add_apply, Ring.choose, RingHom, RingHom.id_apply, add_apply, coeff_add, coeff_eq_zero_of_lt_order, coeff_smul, contrapose, f.coeff, f.order, id_apply, lt_sub_iff_add_lt, lt_sub_iff_add_lt.mp, map_add
-/
def hasseDeriv (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] (k : Nat) :
    V⸨X⸩ ->ₗ[R] V⸨X⸩ where
toFun f := HahnSeries.ofSuppBddBelow (fun n => Ring.choose (n + k) k • f.coeff (n + k)) by
    refine ⟨f.order - k, fun x h => ?_⟩
    contrapose! h
    rw [Function.notMem_support]; rw [coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h]; rw [smul_zero]
  map_add' f g := by
    ext
    simp only [ofSuppBddBelow, coeff_add', Pi.add_apply, smul_add]
  map_smul' r f := by
    ext
    simp only [ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply, smul_comm r]

variable [Semiring R] {V : Type*} [AddCommGroup V] [Module R V]

@[simp]
/--
theorem `hasseDeriv_coeff` / 定理 `hasseDeriv_coeff`

English:
theorem hasseDeriv_coeff
  given: (k : Nat) (f : LaurentSeries V) (n : Int)
  proof: rfl

@[simp]

中文:
定理 hasseDeriv_coeff
  条件: (k : 自然数) (f : Laurent级数 V) (n : 整数)
  证明: rfl

@[simp]
-/
theorem hasseDeriv_coeff (k : Nat) (f : LaurentSeries V) (n : Int) :
    (hasseDeriv R k f).coeff n = Ring.choose (n + k) k • f.coeff (n + k) :=
  rfl

@[simp]
/--
theorem `hasseDeriv_zero` / 定理 `hasseDeriv_zero`

English:
theorem hasseDeriv_zero
  statement: hasseDeriv R 0 = LinearMap.id (M := LaurentSeries V)
  proof: by
  ext f n
  simp

中文:
定理 hasseDeriv_zero
  结论: hasseDeriv R 0 = 线性映射.id (M := Laurent级数 V)
  证明: by
  ext f n
  simp

Depends on / 依赖: LaurentSeries
-/
theorem hasseDeriv_zero : hasseDeriv R 0 = LinearMap.id (M := LaurentSeries V) := by
  ext f n
  simp

/--
theorem `hasseDeriv_single_add` / 定理 `hasseDeriv_single_add`

English:
theorem hasseDeriv_single_add
  given: (k : Nat) (n : Int) (x : V)
  proof: by
  ext m
  dsimp only [hasseDeriv_coeff]
  by_cases h : m = n
  · simp [h]
  · simp [h, show m + k != n + k by lia]

@[simp]

中文:
定理 hasseDeriv_single_add
  条件: (k : 自然数) (n : 整数) (x : V)
  证明: by
  ext m
  dsimp only [hasseDeriv_coeff]
  by_cases h : m = n
  · simp [h]
  · simp [h, show m + k != n + k by lia]

@[simp]

Depends on / 依赖: hasseDeriv_coeff
-/
theorem hasseDeriv_single_add (k : Nat) (n : Int) (x : V) :
    hasseDeriv R k (single (n + k) x) = single n ((Ring.choose (n + k) k) • x) := by
  ext m
  dsimp only [hasseDeriv_coeff]
  by_cases h : m = n
  · simp [h]
  · simp [h, show m + k != n + k by lia]

@[simp]
/--
theorem `hasseDeriv_single` / 定理 `hasseDeriv_single`

English:
theorem hasseDeriv_single
  given: (k : Nat) (n : Int) (x : V)
  proof: by
  rw [← Int.sub_add_cancel n k]; rw [hasseDeriv_single_add]; rw [Int.sub_add_cancel n k]

中文:
定理 hasseDeriv_single
  条件: (k : 自然数) (n : 整数) (x : V)
  证明: by
  rw [← Int.sub_add_cancel n k]; rw [hasseDeriv_single_add]; rw [Int.sub_add_cancel n k]

Depends on / 依赖: Int.sub_add_cancel, hasseDeriv_single_add, sub_add_cancel
-/
theorem hasseDeriv_single (k : Nat) (n : Int) (x : V) :
    hasseDeriv R k (single n x) = single (n - k) ((Ring.choose n k) • x) := by
  rw [← Int.sub_add_cancel n k]; rw [hasseDeriv_single_add]; rw [Int.sub_add_cancel n k]

/--
theorem `hasseDeriv_comp_coeff` / 定理 `hasseDeriv_comp_coeff`

English:
theorem hasseDeriv_comp_coeff
  given: (k l : Nat) (f : LaurentSeries V) (n : Int)
  proof: by
  rw [coeff_nsmul]
  simp only [hasseDeriv_coeff, Pi.smul_apply, Nat.cast_add]
  rw [smul_smul]; rw [mul_comm]; rw [← Ring.choose_add_smul_choose (n + k)]; rw [add_assoc]; rw [Nat.choose_symm_add]; rw [smul_assoc]

@[simp]

中文:
定理 hasseDeriv_comp_coeff
  条件: (k l : 自然数) (f : Laurent级数 V) (n : 整数)
  证明: by
  rw [coeff_nsmul]
  simp only [hasseDeriv_coeff, Pi.smul_apply, Nat.cast_add]
  rw [smul_smul]; rw [mul_comm]; rw [← Ring.choose_add_smul_choose (n + k)]; rw [add_assoc]; rw [Nat.choose_symm_add]; rw [smul_assoc]

@[simp]

Depends on / 依赖: Nat.cast_add, Nat.choose_symm_add, Pi.smul_apply, Ring.choose_add_smul_choose, add_assoc, cast_add, choose_add_smul_choose, choose_symm_add, coeff_nsmul, hasseDeriv_coeff, mul_comm, smul_apply, smul_assoc, smul_smul
-/
theorem hasseDeriv_comp_coeff (k l : Nat) (f : LaurentSeries V) (n : Int) :
    (hasseDeriv R k (hasseDeriv R l f)).coeff n =
      ((Nat.choose (k + l) k) • hasseDeriv R (k + l) f).coeff n := by
  rw [coeff_nsmul]
  simp only [hasseDeriv_coeff, Pi.smul_apply, Nat.cast_add]
  rw [smul_smul]; rw [mul_comm]; rw [← Ring.choose_add_smul_choose (n + k)]; rw [add_assoc]; rw [Nat.choose_symm_add]; rw [smul_assoc]

@[simp]
/--
theorem `hasseDeriv_comp` / 定理 `hasseDeriv_comp`

English:
theorem hasseDeriv_comp
  given: (k l : Nat) (f : LaurentSeries V)
  proof: by
  ext n
  simp [hasseDeriv_comp_coeff k l f n]

中文:
定理 hasseDeriv_comp
  条件: (k l : 自然数) (f : Laurent级数 V)
  证明: by
  ext n
  simp [hasseDeriv_comp_coeff k l f n]

Depends on / 依赖: hasseDeriv_comp_coeff
-/
theorem hasseDeriv_comp (k l : Nat) (f : LaurentSeries V) :
    hasseDeriv R k (hasseDeriv R l f) = (k + l).choose k • hasseDeriv R (k + l) f := by
  ext n
  simp [hasseDeriv_comp_coeff k l f n]

/--
Definition of `derivative` / `derivative` 的定义

English:
definition derivative
  signature: (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V]
  body: hasseDeriv R 1

@[simp]

中文:
定义 derivative
  签名: (R : 类型) {V : 类型} [加法交换群 V] [半环 R] [模 R V]
  定义体: hasseDeriv R 1

@[simp]

Depends on / 依赖: hasseDeriv
-/
def derivative (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] :
    LaurentSeries V ->ₗ[R] LaurentSeries V :=
  hasseDeriv R 1

@[simp]
/--
theorem `derivative_apply` / 定理 `derivative_apply`

English:
theorem derivative_apply
  given: (f : LaurentSeries V)
  statement: derivative R f = hasseDeriv R 1 f
  proof: by
  exact rfl

中文:
定理 derivative_apply
  条件: (f : Laurent级数 V)
  结论: derivative R f = hasseDeriv R 1 f
  证明: by
  exact rfl
-/
theorem derivative_apply (f : LaurentSeries V) : derivative R f = hasseDeriv R 1 f := by
  exact rfl

/--
theorem `derivative_iterate` / 定理 `derivative_iterate`

English:
theorem derivative_iterate
  given: (k : Nat) (f : LaurentSeries V)
  proof: by
  ext n
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ]; rw [Function.comp_apply]; rw [ih]; rw [derivative_apply]; rw [hasseDeriv_comp]; rw [Nat.choose_symm_add]; rw [Nat.choose_one_right]; rw [Nat.factorial]; rw [mul_nsmul]

@[simp]

中文:
定理 derivative_iterate
  条件: (k : 自然数) (f : Laurent级数 V)
  证明: by
  ext n
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ]; rw [Function.comp_apply]; rw [ih]; rw [derivative_apply]; rw [hasseDeriv_comp]; rw [Nat.choose_symm_add]; rw [Nat.choose_one_right]; rw [Nat.factorial]; rw [mul_nsmul]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Nat.choose_one_right, Nat.choose_symm_add, Nat.factorial, choose_one_right, choose_symm_add, comp_apply, derivative_apply, factorial, generalizing, hasseDeriv_comp, iterate_succ, mul_nsmul
-/
theorem derivative_iterate (k : Nat) (f : LaurentSeries V) :
    (derivative R)^[k] f = k.factorial • (hasseDeriv R k f) := by
  ext n
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ]; rw [Function.comp_apply]; rw [ih]; rw [derivative_apply]; rw [hasseDeriv_comp]; rw [Nat.choose_symm_add]; rw [Nat.choose_one_right]; rw [Nat.factorial]; rw [mul_nsmul]

@[simp]
/--
theorem `derivative_iterate_coeff` / 定理 `derivative_iterate_coeff`

English:
theorem derivative_iterate_coeff
  given: (k : Nat) (f : LaurentSeries V) (n : Int)
  proof: by
  rw [derivative_iterate]; rw [coeff_nsmul]; rw [Pi.smul_apply]; rw [hasseDeriv_coeff]; rw [Ring.descPochhammer_eq_factorial_smul_choose]; rw [smul_assoc]

中文:
定理 derivative_iterate_coeff
  条件: (k : 自然数) (f : Laurent级数 V) (n : 整数)
  证明: by
  rw [derivative_iterate]; rw [coeff_nsmul]; rw [Pi.smul_apply]; rw [hasseDeriv_coeff]; rw [Ring.descPochhammer_eq_factorial_smul_choose]; rw [smul_assoc]

Depends on / 依赖: Pi.smul_apply, Ring.descPochhammer_eq_factorial_smul_choose, coeff_nsmul, derivative_iterate, descPochhammer_eq_factorial_smul_choose, hasseDeriv_coeff, smul_apply, smul_assoc
-/
theorem derivative_iterate_coeff (k : Nat) (f : LaurentSeries V) (n : Int) :
    ((derivative R)^[k] f).coeff n = (descPochhammer Int k).smeval (n + k) • f.coeff (n + k) := by
  rw [derivative_iterate]; rw [coeff_nsmul]; rw [Pi.smul_apply]; rw [hasseDeriv_coeff]; rw [Ring.descPochhammer_eq_factorial_smul_choose]; rw [smul_assoc]

end HasseDeriv

section Semiring

variable [Semiring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe R⟦X⟧ R⸨X⸩
  body: ⟨HahnSeries.ofPowerSeries Int R⟩

@[simp]

中文:
实例 :
  签名: Coe R⟦X⟧ R⸨X⸩
  定义体: ⟨HahnSeries.ofPowerSeries Int R⟩

@[simp]

Depends on / 依赖: HahnSeries, HahnSeries.ofPowerSeries, ofPowerSeries
-/
instance : Coe R⟦X⟧ R⸨X⸩ :=
  ⟨HahnSeries.ofPowerSeries Int R⟩

@[simp]
/--
theorem `coeff_coe_powerSeries` / 定理 `coeff_coe_powerSeries`

English:
theorem coeff_coe_powerSeries
  given: (x : R⟦X⟧) (n : Nat)
  proof: by
  rw [ofPowerSeries_apply_coeff]

中文:
定理 coeff_coe_powerSeries
  条件: (x : R⟦X⟧) (n : 自然数)
  证明: by
  rw [ofPowerSeries_apply_coeff]

Depends on / 依赖: ofPowerSeries_apply_coeff
-/
theorem coeff_coe_powerSeries (x : R⟦X⟧) (n : Nat) :
    HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x := by
  rw [ofPowerSeries_apply_coeff]

/--
Definition of `powerSeriesPart` / `powerSeriesPart` 的定义

English:
definition powerSeriesPart
  signature: (x : R⸨X⸩)
  body: PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]

中文:
定义 powerSeriesPart
  签名: (x : R⸨X⸩)
  定义体: PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.mk, x.coeff, x.order
-/
def powerSeriesPart (x : R⸨X⸩) : R⟦X⟧ :=
  PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]
/--
theorem `powerSeriesPart_coeff` / 定理 `powerSeriesPart_coeff`

English:
theorem powerSeriesPart_coeff
  given: (x : R⸨X⸩) (n : Nat)
  proof: PowerSeries.coeff_mk _ _

@[simp]

中文:
定理 powerSeriesPart_coeff
  条件: (x : R⸨X⸩) (n : 自然数)
  证明: PowerSeries.coeff_mk _ _

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_mk, coeff_mk
-/
theorem powerSeriesPart_coeff (x : R⸨X⸩) (n : Nat) :
    PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _

@[simp]
/--
theorem `powerSeriesPart_zero` / 定理 `powerSeriesPart_zero`

English:
theorem powerSeriesPart_zero
  statement: powerSeriesPart (0 : R⸨X⸩) = 0
  proof: by
  ext
  simp

@[simp]

中文:
定理 powerSeriesPart_zero
  结论: powerSeriesPart (0 : R⸨X⸩) = 0
  证明: by
  ext
  simp

@[simp]
-/
theorem powerSeriesPart_zero : powerSeriesPart (0 : R⸨X⸩) = 0 := by
  ext
  simp

@[simp]
/--
theorem `powerSeriesPart_eq_zero` / 定理 `powerSeriesPart_eq_zero`

English:
theorem powerSeriesPart_eq_zero
  given: (x : R⸨X⸩)
  statement: x.powerSeriesPart = 0 ↔ x = 0
  proof: by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff]; rw [not_forall]
    use 0
    simpa
  · rintro rfl
    simp

@[simp]

中文:
定理 powerSeriesPart_eq_zero
  条件: (x : R⸨X⸩)
  结论: x.powerSeriesPart = 0 ↔ x = 0
  证明: by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff]; rw [not_forall]
    use 0
    simpa
  · rintro rfl
    simp

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, contrapose, ext_iff, ne_eq, not_forall
-/
theorem powerSeriesPart_eq_zero (x : R⸨X⸩) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff]; rw [not_forall]
    use 0
    simpa
  · rintro rfl
    simp

@[simp]
/--
theorem `single_order_mul_powerSeriesPart` / 定理 `single_order_mul_powerSeriesPart`

English:
theorem single_order_mul_powerSeriesPart
  given: (x : R⸨X⸩)
  proof: by
  ext n
  rw [← sub_add_cancel n x.order]; rw [coeff_single_mul_add]; rw [sub_add_cancel]; rw [one_mul]
  by_cases h : x.order <= n
  · rw [Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h),
      add_s

中文:
定理 single_order_mul_powerSeriesPart
  条件: (x : R⸨X⸩)
  证明: by
  ext n
  rw [← sub_add_cancel n x.order]; rw [coeff_single_mul_add]; rw [sub_add_cancel]; rw [one_mul]
  by_cases h : x.order <= n
  · rw [Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h),
      add_s

Depends on / 依赖: Int.eq_natAbs_of_nonneg, Nat.castOrderEmbedding_apply, Set.mem_range, add_sub_cancel, castOrderEmbedding_apply, coeff_coe_powerSeries, coeff_single_mul_add, contrapose, embDomain_of_notMem_range, eq_natAbs_of_nonneg, h.symm, mem_range, ofPowerSeries_apply, one_mul, order_le_of_coeff_ne_zero, powerSeriesPart_coeff, sub_add_cancel, sub_nonneg_of_le, x.order
-/
theorem single_order_mul_powerSeriesPart (x : R⸨X⸩) :
    (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x := by
  ext n
  rw [← sub_add_cancel n x.order]; rw [coeff_single_mul_add]; rw [sub_add_cancel]; rw [one_mul]
  by_cases h : x.order <= n
  · rw [Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h),
      add_sub_cancel]
  · rw [ofPowerSeries_apply, embDomain_of_notMem_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose h
      simp only [Nat.castOrderEmbedding_apply, Set.mem_range] at h
      lia

/--
theorem `ofPowerSeries_powerSeriesPart` / 定理 `ofPowerSeries_powerSeriesPart`

English:
theorem ofPowerSeries_powerSeriesPart
  given: (x : R⸨X⸩)
  proof: by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc]; rw [single_mul_single]; rw [neg_add_cancel]; rw [mul_one]; rw [← C_apply]; rw [C_one]; rw [one_mul]

中文:
定理 ofPowerSeries_powerSeriesPart
  条件: (x : R⸨X⸩)
  证明: by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc]; rw [single_mul_single]; rw [neg_add_cancel]; rw [mul_one]; rw [← C_apply]; rw [C_one]; rw [one_mul]

Depends on / 依赖: C_apply, C_one, Eq.trans, mul_assoc, mul_one, neg_add_cancel, one_mul, single_mul_single, single_order_mul_powerSeriesPart, x.single_order_mul_powerSeriesPart
-/
theorem ofPowerSeries_powerSeriesPart (x : R⸨X⸩) :
    ofPowerSeries Int R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc]; rw [single_mul_single]; rw [neg_add_cancel]; rw [mul_one]; rw [← C_apply]; rw [C_one]; rw [one_mul]

/--
theorem `X_order_mul_powerSeriesPart` / 定理 `X_order_mul_powerSeriesPart`

English:
theorem X_order_mul_powerSeriesPart
  given: {n : Nat} {f : R⸨X⸩} (hn : n = f.order)
  proof: by
  simp only [map_mul, map_pow, ofPowerSeries_X, single_pow, nsmul_eq_mul, mul_one, one_pow, hn,
    single_order_mul_powerSeriesPart]

中文:
定理 X_order_mul_powerSeriesPart
  条件: {n : 自然数} {f : R⸨X⸩} (hn : n = f.order)
  证明: by
  simp only [map_mul, map_pow, ofPowerSeries_X, single_pow, nsmul_eq_mul, mul_one, one_pow, hn,
    single_order_mul_powerSeriesPart]

Depends on / 依赖: map_mul, map_pow, mul_one, nsmul_eq_mul, ofPowerSeries_X, one_pow, single_order_mul_powerSeriesPart, single_pow
-/
theorem X_order_mul_powerSeriesPart {n : Nat} {f : R⸨X⸩} (hn : n = f.order) :
    (PowerSeries.X ^ n * f.powerSeriesPart : R⟦X⟧) = f := by
  simp only [map_mul, map_pow, ofPowerSeries_X, single_pow, nsmul_eq_mul, mul_one, one_pow, hn,
    single_order_mul_powerSeriesPart]

end Semiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] : Algebra R⟦X⟧ R⸨X⸩
  body: (HahnSeries.ofPowerSeries Int R).toAlgebra

@[simp]

中文:
实例 [交换半环
  签名: R] : 代数 R⟦X⟧ R⸨X⸩
  定义体: (HahnSeries.ofPowerSeries Int R).toAlgebra

@[simp]

Depends on / 依赖: HahnSeries, HahnSeries.ofPowerSeries, ofPowerSeries, toAlgebra
-/
instance [CommSemiring R] : Algebra R⟦X⟧ R⸨X⸩ := (HahnSeries.ofPowerSeries Int R).toAlgebra

@[simp]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  given: [CommSemiring R]
  proof: rfl

中文:
定理 coe_algebraMap
  条件: [交换半环 R]
  证明: rfl
-/
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries Int R :=
  rfl

/-- The localization map from power series to Laurent series. -/
@[simps (rhsMd := .all) +simpRhs]
/--
Instance `of_powerSeries_localization` / 实例 `of_powerSeries_localization`

English:
instance of_powerSeries_localization
  signature: [CommRing R]
  body: by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : Int) 1, single (-n : Int) 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · dsimp; rw [ofPowerSeries_X_pow]
  surj z := by
    by_cases! h : 0 <= z.order
    · refine ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, ?_⟩
      simp only [map_o

中文:
实例 of_powerSeries_localization
  签名: [交换环 R]
  定义体: by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : Int) 1, single (-n : Int) 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · dsimp; rw [ofPowerSeries_X_pow]
  surj z := by
    by_cases! h : 0 <= z.order
    · refine ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, ?_⟩
      simp only [map_o

Depends on / 依赖: Int.natAbs, Int.natAbs_of_nonneg, PowerSeries, PowerSeries.X, Submonoid, Submonoid.coe_one, coe_algebraMap, coe_one, map_mul, map_one, mul_one, natAbs, natAbs_of_nonneg, ofPowerSeries_X_pow, powerSeriesPart, single, single_order_mul_powerSeriesPart, z.order
-/
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : R⟦X⟧)) R⸨X⸩ where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : Int) 1, single (-n : Int) 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · dsimp; rw [ofPowerSeries_X_pow]
  surj z := by
    by_cases! h : 0 <= z.order
    · refine ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, ?_⟩
      simp only [map_one, mul_one, map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h]; rw [single_order_mul_powerSeriesPart]
    · refine ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, ?_⟩
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      rw [mul_comm _ z]
      refine congr rfl ?_
      rw [ofPowerSeries_X_pow]; rw [Int.ofNat_natAbs_of_nonpos]
      exact h.le
  exists_of_eq {x y} := by
    rw [coe_algebraMap]; rw [ofPowerSeries_injective.eq_iff]
    rintro rfl
    exact ⟨1, rfl⟩

instance {K : Type*} [Field K] : IsFractionRing K⟦X⟧ K⸨X⸩ :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : K⟦X⟧)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun _ hf =>
isUnit_of_mem_nonZeroDivisors map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type*} [Semiring R] [Ring R'] (f g : R⟦X⟧) (f' g' : R'⟦X⟧)

@[norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : R⟦X⟧) : R⸨X⸩) = 0
  proof: (ofPowerSeries Int R).map_zero

@[norm_cast]

中文:
定理 coe_zero
  结论: ((0 : R⟦X⟧) : R⸨X⸩) = 0
  证明: (ofPowerSeries Int R).map_zero

@[norm_cast]

Depends on / 依赖: map_zero, ofPowerSeries
-/
theorem coe_zero : ((0 : R⟦X⟧) : R⸨X⸩) = 0 :=
  (ofPowerSeries Int R).map_zero

@[norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : R⟦X⟧) : R⸨X⸩) = 1
  proof: (ofPowerSeries Int R).map_one

@[norm_cast]

中文:
定理 coe_one
  结论: ((1 : R⟦X⟧) : R⸨X⸩) = 1
  证明: (ofPowerSeries Int R).map_one

@[norm_cast]

Depends on / 依赖: map_one, ofPowerSeries
-/
theorem coe_one : ((1 : R⟦X⟧) : R⸨X⸩) = 1 :=
  (ofPowerSeries Int R).map_one

@[norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ((f + g : R⟦X⟧) : R⸨X⸩) = f + g
  proof: (ofPowerSeries Int R).map_add _ _

@[norm_cast]

中文:
定理 coe_add
  结论: ((f + g : R⟦X⟧) : R⸨X⸩) = f + g
  证明: (ofPowerSeries Int R).map_add _ _

@[norm_cast]

Depends on / 依赖: map_add, ofPowerSeries
-/
theorem coe_add : ((f + g : R⟦X⟧) : R⸨X⸩) = f + g :=
  (ofPowerSeries Int R).map_add _ _

@[norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ((f' - g' : R'⟦X⟧) : R'⸨X⸩) = f' - g'
  proof: (ofPowerSeries Int R').map_sub _ _

@[norm_cast]

中文:
定理 coe_sub
  结论: ((f' - g' : R'⟦X⟧) : R'⸨X⸩) = f' - g'
  证明: (ofPowerSeries Int R').map_sub _ _

@[norm_cast]

Depends on / 依赖: map_sub, ofPowerSeries
-/
theorem coe_sub : ((f' - g' : R'⟦X⟧) : R'⸨X⸩) = f' - g' :=
  (ofPowerSeries Int R').map_sub _ _

@[norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ((-f' : R'⟦X⟧) : R'⸨X⸩) = -f'
  proof: (ofPowerSeries Int R').map_neg _

@[norm_cast]

中文:
定理 coe_neg
  结论: ((-f' : R'⟦X⟧) : R'⸨X⸩) = -f'
  证明: (ofPowerSeries Int R').map_neg _

@[norm_cast]

Depends on / 依赖: map_neg, ofPowerSeries
-/
theorem coe_neg : ((-f' : R'⟦X⟧) : R'⸨X⸩) = -f' :=
  (ofPowerSeries Int R').map_neg _

@[norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ((f * g : R⟦X⟧) : R⸨X⸩) = f * g
  proof: (ofPowerSeries Int R).map_mul _ _

中文:
定理 coe_mul
  结论: ((f * g : R⟦X⟧) : R⸨X⸩) = f * g
  证明: (ofPowerSeries Int R).map_mul _ _

Depends on / 依赖: map_mul, ofPowerSeries
-/
theorem coe_mul : ((f * g : R⟦X⟧) : R⸨X⸩) = f * g :=
  (ofPowerSeries Int R).map_mul _ _

/--
theorem `coeff_coe` / 定理 `coeff_coe`

English:
theorem coeff_coe
  given: (i : Int)
  proof: by
  cases i
  · rw [Int.ofNat_eq_natCast, coeff_coe_powerSeries, if_neg (Int.natCast_nonneg _).not_gt,
      Int.natAbs_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp

中文:
定理 coeff_coe
  条件: (i : 整数)
  证明: by
  cases i
  · rw [Int.ofNat_eq_natCast, coeff_coe_powerSeries, if_neg (Int.natCast_nonneg _).not_gt,
      Int.natAbs_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp

Depends on / 依赖: Int.natAbs_natCast, Int.natCast_nonneg, Int.negSucc_lt_zero, Int.ofNat_eq_natCast, coeff_coe_powerSeries, embDomain_notin_image_support, if_neg, if_pos, natAbs_natCast, natCast_nonneg, negSucc_lt_zero, not_gt, ofNat_eq_natCast, ofPowerSeries_apply
-/
theorem coeff_coe (i : Int) :
    ((f : R⟦X⟧) : R⸨X⸩).coeff i =
      if i < 0 then 0 else PowerSeries.coeff i.natAbs f := by
  cases i
  · rw [Int.ofNat_eq_natCast, coeff_coe_powerSeries, if_neg (Int.natCast_nonneg _).not_gt,
      Int.natAbs_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp

/--
theorem `coe_C` / 定理 `coe_C`

English:
theorem coe_C
  given: (r : R)
  statement: ((C r : R⟦X⟧) : R⸨X⸩) = HahnSeries.C r
  proof: ofPowerSeries_C _

中文:
定理 coe_C
  条件: (r : R)
  结论: ((C r : R⟦X⟧) : R⸨X⸩) = Hahn级数.C r
  证明: ofPowerSeries_C _

Depends on / 依赖: ofPowerSeries_C
-/
theorem coe_C (r : R) : ((C r : R⟦X⟧) : R⸨X⸩) = HahnSeries.C r :=
  ofPowerSeries_C _

/--
theorem `coe_X` / 定理 `coe_X`

English:
theorem coe_X
  statement: ((X : R⟦X⟧) : R⸨X⸩) = single 1 1
  proof: ofPowerSeries_X

@[simp, norm_cast]

中文:
定理 coe_X
  结论: ((X : R⟦X⟧) : R⸨X⸩) = single 1 1
  证明: ofPowerSeries_X

@[simp, norm_cast]

Depends on / 依赖: ofPowerSeries_X
-/
theorem coe_X : ((X : R⟦X⟧) : R⸨X⸩) = single 1 1 :=
  ofPowerSeries_X

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: {S : Type*} [Semiring S] [Module R S] (r : R) (x : S⟦X⟧)
  proof: by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]

@[norm_cast]

中文:
定理 coe_smul
  条件: {S : 类型} [半环 S] [模 R S] (r : R) (x : S⟦X⟧)
  证明: by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]

@[norm_cast]

Depends on / 依赖: coeff_coe, coeff_smul, smul_ite
-/
theorem coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : S⟦X⟧) :
    ((r • x : S⟦X⟧) : S⸨X⸩) = r • (ofPowerSeries Int S x) := by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]

@[norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (n : Nat)
  statement: ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPowerSeries Int R f) ^ n
  proof: (ofPowerSeries Int R).map_pow _ _

中文:
定理 coe_pow
  条件: (n : 自然数)
  结论: ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPowerSeries 整数 R f) ^ n
  证明: (ofPowerSeries Int R).map_pow _ _

Depends on / 依赖: map_pow, ofPowerSeries
-/
theorem coe_pow (n : Nat) : ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPowerSeries Int R f) ^ n :=
  (ofPowerSeries Int R).map_pow _ _

end PowerSeries

namespace RatFunc

open scoped LaurentSeries

variable {F : Type u} [Field F] (p q : F[X]) (f g : RatFunc F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul F[X] F⸨X⸩
  body: by
  refine (faithfulSMul_iff_algebraMap_injective F[X] F⸨X⸩).mpr ?_
  exact algebraMap_hahnSeries_injective Int

中文:
实例 :
  签名: 忠实标量乘法 F[X] F⸨X⸩
  定义体: by
  refine (faithfulSMul_iff_algebraMap_injective F[X] F⸨X⸩).mpr ?_
  exact algebraMap_hahnSeries_injective Int

Depends on / 依赖: algebraMap_hahnSeries_injective, faithfulSMul_iff_algebraMap_injective
-/
instance : FaithfulSMul F[X] F⸨X⸩ := by
  refine (faithfulSMul_iff_algebraMap_injective F[X] F⸨X⸩).mpr ?_
  exact algebraMap_hahnSeries_injective Int

/--
Instance `coeToLaurentSeries` / 实例 `coeToLaurentSeries`

English:
instance coeToLaurentSeries
  signature: : Coe (RatFunc F) F⸨X⸩
  body: ⟨algebraMap (RatFunc F) F⸨X⸩⟩

中文:
实例 coeToLaurentSeries
  签名: : Coe (有理函数 F) F⸨X⸩
  定义体: ⟨algebraMap (RatFunc F) F⸨X⸩⟩

Depends on / 依赖: RatFunc, algebraMap
-/
instance coeToLaurentSeries : Coe (RatFunc F) F⸨X⸩ :=
  ⟨algebraMap (RatFunc F) F⸨X⸩⟩

/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (P : Polynomial F)
  statement: ((P : F⟦X⟧) : F⸨X⸩) = (P : RatFunc F)
  proof: by
  simp [coePolynomial, coe_def, ← IsScalarTower.algebraMap_apply]

中文:
定理 coe_coe
  条件: (P : 多项式 F)
  结论: ((P : F⟦X⟧) : F⸨X⸩) = (P : 有理函数 F)
  证明: by
  simp [coePolynomial, coe_def, ← IsScalarTower.algebraMap_apply]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, coePolynomial, coe_def
-/
theorem coe_coe (P : Polynomial F) : ((P : F⟦X⟧) : F⸨X⸩) = (P : RatFunc F) := by
  simp [coePolynomial, coe_def, ← IsScalarTower.algebraMap_apply]

-- Porting note: removed `norm_cast` because "badly shaped lemma, rhs can't start with coe"
-- even though `single 1 1` is a bundled function application, not a "real" coercion
@[simp]
/--
theorem `coe_X` / 定理 `coe_X`

English:
theorem coe_X
  statement: ((X : RatFunc F) : F⸨X⸩) = single 1 1
  proof: by
  simp [← algebraMap_X, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

中文:
定理 coe_X
  结论: ((X : 有理函数 F) : F⸨X⸩) = single 1 1
  证明: by
  simp [← algebraMap_X, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, RatFunc, algebraMap_X, algebraMap_apply
-/
theorem coe_X : ((X : RatFunc F) : F⸨X⸩) = single 1 1 := by
  simp [← algebraMap_X, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

/--
theorem `single_one_eq_pow` / 定理 `single_one_eq_pow`

English:
theorem single_one_eq_pow
  given: {R : Type*} [Semiring R] (n : Nat)
  proof: by
  simp

中文:
定理 single_one_eq_pow
  条件: {R : 类型} [半环 R] (n : 自然数)
  证明: by
  simp
-/
theorem single_one_eq_pow {R : Type*} [Semiring R] (n : Nat) :
    single (n : Int) (1 : R) = single (1 : Int) 1 ^ n := by
  simp

/--
theorem `single_zpow` / 定理 `single_zpow`

English:
theorem single_zpow
  given: (n : Int)
  proof: by
  match n with
  | (n : Nat) => apply single_one_eq_pow
  | -(n + 1 : Nat) =>
    rw [← Nat.cast_one]; rw [← inv_one]; rw [← HahnSeries.inv_single]; rw [zpow_neg]; rw [← Nat.cast_one]; rw [Nat.cast_one]; rw [inv_inj]; rw [zpow_natCast]; rw [single_one_eq_pow]; rw [inv_one]

中文:
定理 single_zpow
  条件: (n : 整数)
  证明: by
  match n with
  | (n : Nat) => apply single_one_eq_pow
  | -(n + 1 : Nat) =>
    rw [← Nat.cast_one]; rw [← inv_one]; rw [← HahnSeries.inv_single]; rw [zpow_neg]; rw [← Nat.cast_one]; rw [Nat.cast_one]; rw [inv_inj]; rw [zpow_natCast]; rw [single_one_eq_pow]; rw [inv_one]

Depends on / 依赖: HahnSeries, HahnSeries.inv_single, Nat.cast_one, cast_one, inv_inj, inv_one, inv_single, single_one_eq_pow, zpow_natCast, zpow_neg
-/
theorem single_zpow (n : Int) :
    single (n : Int) (1 : F) = single (1 : Int) 1 ^ n := by
  match n with
  | (n : Nat) => apply single_one_eq_pow
  | -(n + 1 : Nat) =>
    rw [← Nat.cast_one]; rw [← inv_one]; rw [← HahnSeries.inv_single]; rw [zpow_neg]; rw [← Nat.cast_one]; rw [Nat.cast_one]; rw [inv_inj]; rw [zpow_natCast]; rw [single_one_eq_pow]; rw [inv_one]

/--
theorem `algebraMap_apply_div` / 定理 `algebraMap_apply_div`

English:
theorem algebraMap_apply_div
  proof: by
  simp only [map_div₀, IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

中文:
定理 algebraMap_apply_div
  证明: by
  simp only [map_div₀, IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, RatFunc, algebraMap_apply
-/
theorem algebraMap_apply_div :
    algebraMap (RatFunc F) F⸨X⸩ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap F[X] F⸨X⸩ p / algebraMap _ _ q := by
  simp only [map_div₀, IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

end RatFunc

section AdicValuation

open scoped WithZero

variable (K : Type*) [Field K]
namespace PowerSeries

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `idealX` / `idealX` 的定义

English:
definition idealX
  signature: : IsDedekindDomain.HeightOneSpectrum K⟦X⟧ where
  body: Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

中文:
定义 idealX
  签名: : 是Dedekind整环.高一谱 K⟦X⟧ where
  定义体: Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

Depends on / 依赖: Ideal.span, hasSmallInductiveDimensionLT_zero_iff, zero_le
-/
def idealX : IsDedekindDomain.HeightOneSpectrum K⟦X⟧ where
  asIdeal := Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

open IsDedekindDomain.HeightOneSpectrum RatFunc WithZero

variable {K}

/--
theorem `intValuation_eq_of_coe` / 定理 `intValuation_eq_of_coe`

English:
theorem intValuation_eq_of_coe
  given: (P : K[X])
  proof: by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  rw [intValuation_if_neg _ hP]; rw [intValuation_if_neg _ <| (by simp [hP])]
  simp only [idealX_span, exp_neg, inv_inj, exp_inj, Nat.cast_inj]
  have span_ne_zero :
    (Ideal.span {P} : Ideal K[X]) !

中文:
定理 intValuation_eq_of_coe
  条件: (P : K[X])
  证明: by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  rw [intValuation_if_neg _ hP]; rw [intValuation_if_neg _ <| (by simp [hP])]
  simp only [idealX_span, exp_neg, inv_inj, exp_inj, Nat.cast_inj]
  have span_ne_zero :
    (Ideal.span {P} : Ideal K[X]) !

Depends on / 依赖: Ideal.span, Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot, Nat.cast_inj, Polynomial, Polynomial.X, Polynomial.X_ne_zero, Polynomial.coe_zero, Valuation, Valuation.map_zero, X_ne_zero, and_self_iff, cast_inj, coe_zero, exp_inj, exp_neg, idealX_span, intValuation_if_neg, inv_inj, map_zero
-/
theorem intValuation_eq_of_coe (P : K[X]) :
    (Polynomial.idealX K).intValuation P = (idealX K).intValuation (P : K⟦X⟧) := by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  rw [intValuation_if_neg _ hP]; rw [intValuation_if_neg _ <| (by simp [hP])]
  simp only [idealX_span, exp_neg, inv_inj, exp_inj, Nat.cast_inj]
  have span_ne_zero :
    (Ideal.span {P} : Ideal K[X]) != 0 ∧ (Ideal.span {Polynomial.X} : Ideal K[X]) != 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hP, Polynomial.X_ne_zero,
      not_false_iff, and_self_iff]
  have span_ne_zero' :
    (Ideal.span {↑P} : Ideal K⟦X⟧) != 0 ∧ ((idealX K).asIdeal : Ideal K⟦X⟧) != 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, coe_eq_zero_iff, hP,
      not_false_eq_true, true_and, (idealX K).3]
  classical
  rw [Ideal.count_associates_factors_eq span_ne_zero.1
    (Ideal.span_singleton_prime Polynomial.X_ne_zero |>.mpr prime_X) span_ne_zero.2]; rw [Ideal.count_associates_factors_eq]
  on_goal 1 => convert! (normalized_count_X_eq_of_coe hP).symm
  exacts [Ideal.count_span_normalizedFactors_eq_of_normUnit hP Polynomial.normUnit_X prime_X,
    Ideal.count_span_normalizedFactors_eq_of_normUnit (by simp [hP]) normUnit_X X_prime,
    span_ne_zero'.1, (idealX K).isPrime, span_ne_zero'.2]

/-- The integral valuation of the power series `X : K⟦X⟧` equals `(ofAdd -1) : ℤᵐ⁰`. -/
@[simp]
/--
theorem `intValuation_X` / 定理 `intValuation_X`

English:
theorem intValuation_X
  statement: (idealX K).intValuation X = exp (-1 : Int)
  proof: by
  rw [← Polynomial.coe_X]; rw [← intValuation_eq_of_coe]
  exact intValuation_singleton _ Polynomial.X_ne_zero (idealX_span _)

中文:
定理 intValuation_X
  结论: (idealX K).intValuation X = exp (-1 : 整数)
  证明: by
  rw [← Polynomial.coe_X]; rw [← intValuation_eq_of_coe]
  exact intValuation_singleton _ Polynomial.X_ne_zero (idealX_span _)

Depends on / 依赖: Polynomial, Polynomial.X_ne_zero, Polynomial.coe_X, X_ne_zero, coe_X, idealX_span, intValuation_eq_of_coe, intValuation_singleton
-/
theorem intValuation_X : (idealX K).intValuation X = exp (-1 : Int) := by
  rw [← Polynomial.coe_X]; rw [← intValuation_eq_of_coe]
  exact intValuation_singleton _ Polynomial.X_ne_zero (idealX_span _)

end PowerSeries

namespace RatFunc

open IsDedekindDomain.HeightOneSpectrum PowerSeries
open scoped LaurentSeries

/--
Definition of `polynomialValuationX` / `polynomialValuationX` 的定义

English:
abbreviation polynomialValuationX
  signature: : Valuation K⟮X⟯ Intᵐ⁰
  body: (Polynomial.idealX K).valuation _

中文:
缩写 polynomialValuationX
  签名: : 赋值 K⟮X⟯ 整数ᵐ⁰
  定义体: (Polynomial.idealX K).valuation _

Depends on / 依赖: Polynomial, Polynomial.idealX, idealX, valuation
-/
abbrev polynomialValuationX : Valuation K⟮X⟯ Intᵐ⁰ :=
  (Polynomial.idealX K).valuation _

/--
theorem `valuation_eq_LaurentSeries_valuation` / 定理 `valuation_eq_LaurentSeries_valuation`

English:
theorem valuation_eq_LaurentSeries_valuation
  given: (P : K⟮X⟯)
  proof: by
  refine RatFunc.induction_on' P ?_
  intro f g h
  rw [Polynomial.valuation_of_mk K f h]; rw [RatFunc.mk_eq_mk' f h]; rw [Eq.comm]
  convert!
    @valuation_of_mk' K⟦X⟧ _ _ K⸨X⸩ _ _ _ (PowerSeries.idealX K) f
⟨g, mem_nonZeroDivisors_iff_ne_zero.2 (by simp [h])⟩
  · simp [← IsScalarTower.algebraM

中文:
定理 valuation_eq_LaurentSeries_valuation
  条件: (P : K⟮X⟯)
  证明: by
  refine RatFunc.induction_on' P ?_
  intro f g h
  rw [Polynomial.valuation_of_mk K f h]; rw [RatFunc.mk_eq_mk' f h]; rw [Eq.comm]
  convert!
    @valuation_of_mk' K⟦X⟧ _ _ K⸨X⸩ _ _ _ (PowerSeries.idealX K) f
⟨g, mem_nonZeroDivisors_iff_ne_zero.2 (by simp [h])⟩
  · simp [← IsScalarTower.algebraM

Depends on / 依赖: Eq.comm, IsScalarTower, IsScalarTower.algebraMap_apply, Polynomial, Polynomial.valuation_of_mk, PowerSeries, PowerSeries.idealX, RatFunc, RatFunc.induction_on, RatFunc.mk_eq_mk, algebraMap_apply, convert, exacts, idealX, induction_on, intValuation_eq_of_coe, mem_nonZeroDivisors_iff_ne_zero, mk_eq_mk, valuation_of_mk
-/
theorem valuation_eq_LaurentSeries_valuation (P : K⟮X⟯) :
    polynomialValuationX K P = (PowerSeries.idealX K).valuation K⸨X⸩ P := by
  refine RatFunc.induction_on' P ?_
  intro f g h
  rw [Polynomial.valuation_of_mk K f h]; rw [RatFunc.mk_eq_mk' f h]; rw [Eq.comm]
  convert!
    @valuation_of_mk' K⟦X⟧ _ _ K⸨X⸩ _ _ _ (PowerSeries.idealX K) f
⟨g, mem_nonZeroDivisors_iff_ne_zero.2 (by simp [h])⟩
  · simp [← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ K⸨X⸩]
  exacts [intValuation_eq_of_coe _, intValuation_eq_of_coe _]

end RatFunc

namespace LaurentSeries


open IsDedekindDomain.HeightOneSpectrum PowerSeries RatFunc WithZero

/--
Instance `valued` / 实例 `valued`

English:
instance valued
  signature: : Valued K⸨X⸩ Intᵐ⁰
  body: Valued.mk' ((PowerSeries.idealX K).valuation _)

中文:
实例 valued
  签名: : 赋值 K⸨X⸩ 整数ᵐ⁰
  定义体: Valued.mk' ((PowerSeries.idealX K).valuation _)

Depends on / 依赖: PowerSeries, PowerSeries.idealX, Valued, Valued.mk, idealX, valuation
-/
instance valued : Valued K⸨X⸩ Intᵐ⁰ := Valued.mk' ((PowerSeries.idealX K).valuation _)

/--
lemma `valuation_def` / 引理 `valuation_def`

English:
lemma valuation_def
  statement: (Valued.v : Valuation K⸨X⸩ Intᵐ⁰) = (PowerSeries.idealX K).valuation _
  proof: rfl

中文:
引理 valuation_def
  结论: (赋值.v : 赋值 K⸨X⸩ 整数ᵐ⁰) = (幂级数.idealX K).valuation _
  证明: rfl
-/
lemma valuation_def : (Valued.v : Valuation K⸨X⸩ Intᵐ⁰) = (PowerSeries.idealX K).valuation _ := rfl

/--
lemma `valuation_coe_ratFunc` / 引理 `valuation_coe_ratFunc`

English:
lemma valuation_coe_ratFunc
  given: (f : K⟮X⟯)
  proof: by
  simp [adicValued_apply, ← valuation_eq_LaurentSeries_valuation]

中文:
引理 valuation_coe_ratFunc
  条件: (f : K⟮X⟯)
  证明: by
  simp [adicValued_apply, ← valuation_eq_LaurentSeries_valuation]

Depends on / 依赖: adicValued_apply, valuation_eq_LaurentSeries_valuation
-/
lemma valuation_coe_ratFunc (f : K⟮X⟯) :
    Valued.v (f : K⸨X⸩) = Valued.v f := by
  simp [adicValued_apply, ← valuation_eq_LaurentSeries_valuation]

/--
theorem `valuation_X_pow` / 定理 `valuation_X_pow`

English:
theorem valuation_X_pow
  given: (s : Nat)
  proof: by
  rw [map_pow]; rw [valuation_def]; rw [← LaurentSeries.coe_algebraMap]; rw [valuation_of_algebraMap]; rw [intValuation_X]; rw [← exp_nsmul]; rw [smul_neg]; rw [nsmul_one]

中文:
定理 valuation_X_pow
  条件: (s : 自然数)
  证明: by
  rw [map_pow]; rw [valuation_def]; rw [← LaurentSeries.coe_algebraMap]; rw [valuation_of_algebraMap]; rw [intValuation_X]; rw [← exp_nsmul]; rw [smul_neg]; rw [nsmul_one]

Depends on / 依赖: LaurentSeries, LaurentSeries.coe_algebraMap, coe_algebraMap, exp_nsmul, intValuation_X, map_pow, nsmul_one, smul_neg, valuation_def, valuation_of_algebraMap
-/
theorem valuation_X_pow (s : Nat) :
    Valued.v (((X : K⟦X⟧) : K⸨X⸩) ^ s) = exp (-(s : Int)) := by
  rw [map_pow]; rw [valuation_def]; rw [← LaurentSeries.coe_algebraMap]; rw [valuation_of_algebraMap]; rw [intValuation_X]; rw [← exp_nsmul]; rw [smul_neg]; rw [nsmul_one]

/--
theorem `valuation_single_zpow` / 定理 `valuation_single_zpow`

English:
theorem valuation_single_zpow
  given: (s : Int)
  proof: by
  obtain s | s := s
  · rw [Int.ofNat_eq_natCast, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
      valuation_X_pow]
  · rw [Int.negSucc_eq, ← inv_inj, ← map_inv₀, inv_single, neg_neg, ← Int.natCast_succ, inv_one,
      ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow, valuation_X

中文:
定理 valuation_single_zpow
  条件: (s : 整数)
  证明: by
  obtain s | s := s
  · rw [Int.ofNat_eq_natCast, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
      valuation_X_pow]
  · rw [Int.negSucc_eq, ← inv_inj, ← map_inv₀, inv_single, neg_neg, ← Int.natCast_succ, inv_one,
      ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow, valuation_X

Depends on / 依赖: HahnSeries, HahnSeries.ofPowerSeries_X_pow, Int.natCast_succ, Int.negSucc_eq, Int.ofNat_eq_natCast, PowerSeries, PowerSeries.coe_pow, coe_pow, exp_neg, inv_inj, inv_one, inv_single, natCast_succ, negSucc_eq, neg_neg, ofNat_eq_natCast, ofPowerSeries_X_pow, valuation_X_pow
-/
theorem valuation_single_zpow (s : Int) :
    Valued.v (HahnSeries.single s (1 : K) : K⸨X⸩) = exp (-(s : Int)) := by
  obtain s | s := s
  · rw [Int.ofNat_eq_natCast, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
      valuation_X_pow]
  · rw [Int.negSucc_eq, ← inv_inj, ← map_inv₀, inv_single, neg_neg, ← Int.natCast_succ, inv_one,
      ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow, valuation_X_pow, exp_neg]

/--
theorem `coeff_zero_of_lt_intValuation` / 定理 `coeff_zero_of_lt_intValuation`

English:
theorem coeff_zero_of_lt_intValuation
  statement: {n d : Nat} {f : K⟦X⟧}
  proof: by
  intro hnd
  apply (PowerSeries.X_pow_dvd_iff).mp _ n hnd
  rwa [← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    intValuation_le_pow_iff_dvd (PowerSeries.idealX K) f d, PowerSeries.idealX,
    Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] 

中文:
定理 coeff_zero_of_lt_intValuation
  结论: {n d : 自然数} {f : K⟦X⟧}
  证明: by
  intro hnd
  apply (PowerSeries.X_pow_dvd_iff).mp _ n hnd
  rwa [← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    intValuation_le_pow_iff_dvd (PowerSeries.idealX K) f d, PowerSeries.idealX,
    Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] 

Depends on / 依赖: Ideal.span_singleton_dvd_span_singleton_iff_dvd, Ideal.span_singleton_pow, LaurentSeries, LaurentSeries.coe_algebraMap, PowerSeries, PowerSeries.X_pow_dvd_iff, PowerSeries.idealX, X_pow_dvd_iff, coe_algebraMap, idealX, intValuation_le_pow_iff_dvd, span_singleton_dvd_span_singleton_iff_dvd, span_singleton_pow, valuation_def, valuation_of_algebraMap
-/
theorem coeff_zero_of_lt_intValuation {n d : Nat} {f : K⟦X⟧}
    (H : Valued.v (f : K⸨X⸩) <= exp (-d : Int)) :
    n < d -> coeff n f = 0 := by
  intro hnd
  apply (PowerSeries.X_pow_dvd_iff).mp _ n hnd
  rwa [← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    intValuation_le_pow_iff_dvd (PowerSeries.idealX K) f d, PowerSeries.idealX,
    Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at H

/--
theorem `intValuation_le_iff_coeff_lt_eq_zero` / 定理 `intValuation_le_iff_coeff_lt_eq_zero`

English:
theorem intValuation_le_iff_coeff_lt_eq_zero
  given: {d : Nat} (f : K⟦X⟧)
  proof: by
  have : PowerSeries.X ^ d ∣ f ↔ forall n : Nat, n < d -> (PowerSeries.coeff n) f = 0 :=
    ⟨PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr⟩
  rw [← this]; rw [← LaurentSeries.coe_algebraMap]; rw [valuation_def]; rw [valuation_of_algebraMap]; rw [← Ideal.span_singleton_dvd_span_sing

中文:
定理 intValuation_le_iff_coeff_lt_eq_zero
  条件: {d : 自然数} (f : K⟦X⟧)
  证明: by
  have : PowerSeries.X ^ d ∣ f ↔ forall n : Nat, n < d -> (PowerSeries.coeff n) f = 0 :=
    ⟨PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr⟩
  rw [← this]; rw [← LaurentSeries.coe_algebraMap]; rw [valuation_def]; rw [valuation_of_algebraMap]; rw [← Ideal.span_singleton_dvd_span_sing

Depends on / 依赖: Ideal.span_singleton_dvd_span_singleton_iff_dvd, Ideal.span_singleton_pow, LaurentSeries, LaurentSeries.coe_algebraMap, PowerSeries, PowerSeries.X, PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr, PowerSeries.coeff, X_pow_dvd_iff, coe_algebraMap, intValuation_le_pow_iff_dvd, span_singleton_dvd_span_singleton_iff_dvd, span_singleton_pow, valuation_def, valuation_of_algebraMap
-/
theorem intValuation_le_iff_coeff_lt_eq_zero {d : Nat} (f : K⟦X⟧) :
    Valued.v (f : K⸨X⸩) <= exp (-d : Int) ↔
      forall n : Nat, n < d -> coeff n f = 0 := by
  have : PowerSeries.X ^ d ∣ f ↔ forall n : Nat, n < d -> (PowerSeries.coeff n) f = 0 :=
    ⟨PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr⟩
  rw [← this]; rw [← LaurentSeries.coe_algebraMap]; rw [valuation_def]; rw [valuation_of_algebraMap]; rw [← Ideal.span_singleton_dvd_span_singleton_iff_dvd]; rw [← Ideal.span_singleton_pow]
  apply intValuation_le_pow_iff_dvd

/--
theorem `coeff_zero_of_lt_valuation` / 定理 `coeff_zero_of_lt_valuation`

English:
theorem coeff_zero_of_lt_valuation
  statement: {n D : Int} {f : K⸨X⸩}
  proof: by
  intro hnd
  by_cases! h_n_ord : n < f.order
  · exact coeff_eq_zero_of_lt_order h_n_ord
  set F := powerSeriesPart f with hF
  by_cases! ord_nonpos : f.order <= 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp (hs

中文:
定理 coeff_zero_of_lt_valuation
  结论: {n D : 整数} {f : K⸨X⸩}
  证明: by
  intro hnd
  by_cases! h_n_ord : n < f.order
  · exact coeff_eq_zero_of_lt_order h_n_ord
  set F := powerSeriesPart f with hF
  by_cases! ord_nonpos : f.order <= 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp (hs

Depends on / 依赖: Int.eq_ofNat_of_zero_le, Int.exists_eq_neg_ofNat, add_comm, coeff_eq_zero_of_lt_order, eq_add_neg_of_add_eq, eq_ofNat_of_zero_le, exists_eq_neg_ofNat, f.order, h_n_ord, intValuation_le_iff_coeff_lt_eq_zero, neg_le_iff_add_nonneg, neg_le_iff_add_nonneg.mp, ord_nonpos, powerSeriesPart, powerSeriesPart_coeff
-/
theorem coeff_zero_of_lt_valuation {n D : Int} {f : K⸨X⸩}
    (H : Valued.v f <= exp (-D)) : n < D -> f.coeff n = 0 := by
  intro hnd
  by_cases! h_n_ord : n < f.order
  · exact coeff_eq_zero_of_lt_order h_n_ord
  set F := powerSeriesPart f with hF
  by_cases! ord_nonpos : f.order <= 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp (hs ▸ h_n_ord))
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D + s) (by lia)
    rw [eq_add_neg_of_add_eq hm]; rw [add_comm]; rw [← hs]; rw [← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rw [hF]; rw [ofPowerSeries_powerSeriesPart f]; rw [hs]; rw [neg_neg]; rw [← hd]; rw [neg_add_rev]; rw [exp_add]; rw [map_mul]; rw [← ofPowerSeries_X_pow s]; rw [PowerSeries.coe_pow]; rw [valuation_X_pow K s]
    gcongr
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos))
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := n - s) (by grind)
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D - s) (by lia)
    rw [sub_eq_iff_eq_add.mp hm]; rw [add_comm]; rw [← neg_neg (s : Int)]; rw [← hs]; rw [neg_neg]; rw [← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rw [hF]; rw [ofPowerSeries_powerSeriesPart f]; rw [map_mul]; rw [← hd]; rw [hs]; rw [neg_sub]; rw [sub_eq_add_neg]; rw [exp_add]; rw [valuation_single_zpow]; rw [neg_neg]
    gcongr

/--
theorem `valuation_le_iff_coeff_lt_eq_zero` / 定理 `valuation_le_iff_coeff_lt_eq_zero`

English:
theorem valuation_le_iff_coeff_lt_eq_zero
  given: {D : Int} {f : K⸨X⸩}
  proof: by
  refine ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => ?_⟩
  let F := powerSeriesPart f
  by_cases! ord_nonpos : f.order <= 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    rw [← f.single_order_mul_powerSeriesPart]; rw [hs]; rw [map_mul]; rw [valuation_single_

中文:
定理 valuation_le_iff_coeff_lt_eq_zero
  条件: {D : 整数} {f : K⸨X⸩}
  证明: by
  refine ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => ?_⟩
  let F := powerSeriesPart f
  by_cases! ord_nonpos : f.order <= 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    rw [← f.single_order_mul_powerSeriesPart]; rw [hs]; rw [map_mul]; rw [valuation_single_

Depends on / 依赖: Int.exists_eq_neg_ofNat, PowerSeries, PowerSeries.idealX, coeff_zero_of_lt_valuation, exists_eq_neg_ofNat, exp_add, exp_neg, f.order, f.single_order_mul_powerSeriesPart, h_val_f, idealX, le_trans, map_mul, mul_comm, mul_inv, neg_neg, ord_nonpos, powerSeriesPart, single_order_mul_powerSeriesPart, valuation_le_one
-/
theorem valuation_le_iff_coeff_lt_eq_zero {D : Int} {f : K⸨X⸩} :
    Valued.v f <= exp (-D : Int) ↔ forall n : Int, n < D -> f.coeff n = 0 := by
  refine ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => ?_⟩
  let F := powerSeriesPart f
  by_cases! ord_nonpos : f.order <= 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    rw [← f.single_order_mul_powerSeriesPart]; rw [hs]; rw [map_mul]; rw [valuation_single_zpow]; rw [neg_neg]; rw [mul_comm]; rw [← le_mul_inv_iff₀]; rw [exp_neg]; rw [← mul_inv]; rw [← exp_add]; rw [← exp_neg]
    · by_cases! hDs : D + s <= 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rwa [← log_le_iff_le_exp one_ne_zero, le_neg, log_one, neg_zero]
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hDs.le
        rw [hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n]; rw [hs]
        apply h_val_f
        lia
    · simp [ne_eq, zero_lt_iff]
· obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat neg_nonpos_of_nonneg ord_nonpos.le
    rw [neg_inj] at hs
    rw [← f.single_order_mul_powerSeriesPart]; rw [hs]; rw [map_mul]; rw [valuation_single_zpow]; rw [mul_comm]; rw [← le_mul_inv_iff₀]; rw [← exp_neg]; rw [← exp_add]; rw [neg_neg]
    · by_cases! hDs : D - s <= 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rw [← log_le_iff_le_exp one_ne_zero]; rw [log_one]
        lia
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hDs.le
        rw [← neg_neg (-D + ↑s)]; rw [← sub_eq_neg_add]; rw [neg_sub]; rw [hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n]; rw [hs]
        apply h_val_f (s + n)
        lia
    · simp [ne_eq, zero_lt_iff]

/--
theorem `valuation_le_iff_coeff_lt_log_eq_zero` / 定理 `valuation_le_iff_coeff_lt_log_eq_zero`

English:
theorem valuation_le_iff_coeff_lt_log_eq_zero
  given: {D : Intᵐ⁰} (hD : D != 0) {f : K⸨X⸩}
  proof: by
  cases D
  · simp_all
  · rename_i D
    cases D
    rename_i D
    rw [← exp]; rw [← neg_neg D]; rw [valuation_le_iff_coeff_lt_eq_zero]; rw [log_exp]; rw [neg_neg]

中文:
定理 valuation_le_iff_coeff_lt_log_eq_zero
  条件: {D : 整数ᵐ⁰} (hD : D != 0) {f : K⸨X⸩}
  证明: by
  cases D
  · simp_all
  · rename_i D
    cases D
    rename_i D
    rw [← exp]; rw [← neg_neg D]; rw [valuation_le_iff_coeff_lt_eq_zero]; rw [log_exp]; rw [neg_neg]

Depends on / 依赖: log_exp, neg_neg, rename_i, valuation_le_iff_coeff_lt_eq_zero
-/
theorem valuation_le_iff_coeff_lt_log_eq_zero {D : Intᵐ⁰} (hD : D != 0) {f : K⸨X⸩} :
    Valued.v f <= D ↔ forall n : Int, n < -log D -> f.coeff n = 0 := by
  cases D
  · simp_all
  · rename_i D
    cases D
    rename_i D
    rw [← exp]; rw [← neg_neg D]; rw [valuation_le_iff_coeff_lt_eq_zero]; rw [log_exp]; rw [neg_neg]

/--
theorem `eq_coeff_of_valuation_sub_lt` / 定理 `eq_coeff_of_valuation_sub_lt`

English:
theorem eq_coeff_of_valuation_sub_lt
  statement: {d n : Int} {f g : K⸨X⸩}
  proof: by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    rw [← HahnSeries.coeff_sub]
    apply coeff_zero_of_lt_valuation K H hn

中文:
定理 eq_coeff_of_valuation_sub_lt
  结论: {d n : 整数} {f g : K⸨X⸩}
  证明: by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    rw [← HahnSeries.coeff_sub]
    apply coeff_zero_of_lt_valuation K H hn

Depends on / 依赖: HahnSeries, HahnSeries.coeff_sub, coeff_sub, coeff_zero_of_lt_valuation, eq_of_sub_eq_zero
-/
theorem eq_coeff_of_valuation_sub_lt {d n : Int} {f g : K⸨X⸩}
    (H : Valued.v (g - f) <= exp (-d)) : n < d -> g.coeff n = f.coeff n := by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    rw [← HahnSeries.coeff_sub]
    apply coeff_zero_of_lt_valuation K H hn

/--
theorem `val_le_one_iff_eq_coe` / 定理 `val_le_one_iff_eq_coe`

English:
theorem val_le_one_iff_eq_coe
  given: (f : K⸨X⸩)
  statement: Valued.v f <= (1 : Intᵐ⁰) ↔
  proof: by
  rw [valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero]; rw [log_one]; rw [neg_zero]
  refine ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, ?_⟩, ?_⟩
  on_goal 1 => ext (_ | n)
  · simp only [Int.ofNat_eq_natCast, coeff_coe_powerSeries, coeff_mk]
  on_goal 1 => simp only [h (Int.negSucc n) (Int

中文:
定理 val_le_one_iff_eq_coe
  条件: (f : K⸨X⸩)
  结论: 赋值.v f <= (1 : 整数ᵐ⁰) ↔
  证明: by
  rw [valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero]; rw [log_one]; rw [neg_zero]
  refine ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, ?_⟩, ?_⟩
  on_goal 1 => ext (_ | n)
  · simp only [Int.ofNat_eq_natCast, coeff_coe_powerSeries, coeff_mk]
  on_goal 1 => simp only [h (Int.negSucc n) (Int

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, HahnSeries, HahnSeries.embDomain_of_notMem_range, Int.negSucc, Int.negSucc_lt_zero, Int.ofNat_eq_natCast, Nat.coe_castAddMonoidHom, PowerSeries, PowerSeries.mk, RelEmbedding, RelEmbedding.coe_mk, Set.mem_range, all_goals, coeFn_mk, coe_castAddMonoidHom, coe_mk, coeff_coe_powerSeries, coeff_mk
-/
theorem val_le_one_iff_eq_coe (f : K⸨X⸩) : Valued.v f <= (1 : Intᵐ⁰) ↔
    exists F : K⟦X⟧, F = f := by
  rw [valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero]; rw [log_one]; rw [neg_zero]
  refine ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, ?_⟩, ?_⟩
  on_goal 1 => ext (_ | n)
  · simp only [Int.ofNat_eq_natCast, coeff_coe_powerSeries, coeff_mk]
  on_goal 1 => simp only [h (Int.negSucc n) (Int.negSucc_lt_zero n)]
  on_goal 2 => rintro ⟨F, rfl⟩ _ _
  all_goals
    apply HahnSeries.embDomain_of_notMem_range
    simp only [Nat.coe_castAddMonoidHom, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.mem_range, not_exists, reduceCtorEq]
    intro
  · simp only [not_false_eq_true]
  · lia

end LaurentSeries

end AdicValuation

namespace LaurentSeries

variable {K : Type*} [Field K]

section Complete

open Filter WithZero PowerSeries

variable (K) in
/--
lemma `valuation_surjective` / 引理 `valuation_surjective`

English:
lemma valuation_surjective
  statement: Function.Surjective (Valued.v (R := K⸨X⸩))
  proof: by
  intro n
  by_cases hn0 : n = 0
  · use 0; simp [hn0]
  · use ((HahnSeries.single (-WithZero.log n)) 1)
    simp [LaurentSeries.valuation_single_zpow, exp_log hn0]

中文:
引理 valuation_surjective
  结论: 函数.满射 (赋值.v (R := K⸨X⸩))
  证明: by
  intro n
  by_cases hn0 : n = 0
  · use 0; simp [hn0]
  · use ((HahnSeries.single (-WithZero.log n)) 1)
    simp [LaurentSeries.valuation_single_zpow, exp_log hn0]

Depends on / 依赖: HahnSeries, HahnSeries.single, LaurentSeries, LaurentSeries.valuation_single_zpow, WithZero, WithZero.log, exp_log, single, valuation_single_zpow
-/
lemma valuation_surjective : Function.Surjective (Valued.v (R := K⸨X⸩)) := by
  intro n
  by_cases hn0 : n = 0
  · use 0; simp [hn0]
  · use ((HahnSeries.single (-WithZero.log n)) 1)
    simp [LaurentSeries.valuation_single_zpow, exp_log hn0]

/--
theorem `uniformContinuous_coeff` / 定理 `uniformContinuous_coeff`

English:
theorem uniformContinuous_coeff
  given: {uK : UniformSpace K} (d : Int)
  proof: by
  refine uniformContinuous_iff_eventually.mpr fun S hS => eventually_iff_exists_mem.mpr ?_
  let γ : (Intᵐ⁰)ˣ := Units.mk0 (exp (-(d + 1))) coe_ne_zero
  use {P | Valued.v (P.snd - P.fst) < ↑γ}
  refine ⟨?_, fun _ hP => ?_⟩
  · obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective K γ
have : Value

中文:
定理 uniformContinuous_coeff
  条件: {uK : 一致空间 K} (d : 整数)
  证明: by
  refine uniformContinuous_iff_eventually.mpr fun S hS => eventually_iff_exists_mem.mpr ?_
  let γ : (Intᵐ⁰)ˣ := Units.mk0 (exp (-(d + 1))) coe_ne_zero
  use {P | Valued.v (P.snd - P.fst) < ↑γ}
  refine ⟨?_, fun _ hP => ?_⟩
  · obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective K γ
have : Value

Depends on / 依赖: LaurentSeries, LaurentSeries.valuation_surjective, MonoidWithZeroHom, MonoidWithZeroHom.ValueGroup, NeZero, NeZero.ne, P.fst, P.snd, Units.mk0, Valuation, Valuation.coe_ofClass, Valued, Valued.v, Valued.v.restrict, coe_ne_zero, coe_ofClass, eventually_iff_exists_mem, eventually_iff_exists_mem.mpr, nth_rw, restrict
-/
theorem uniformContinuous_coeff {uK : UniformSpace K} (d : Int) :
    UniformContinuous fun f : K⸨X⸩ => f.coeff d := by
  refine uniformContinuous_iff_eventually.mpr fun S hS => eventually_iff_exists_mem.mpr ?_
  let γ : (Intᵐ⁰)ˣ := Units.mk0 (exp (-(d + 1))) coe_ne_zero
  use {P | Valued.v (P.snd - P.fst) < ↑γ}
  refine ⟨?_, fun _ hP => ?_⟩
  · obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective K γ
have : Valued.v.restrict x != 0 := fun h => NeZero.ne γ.1
      hx ▸ MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.1 h
    rw [← hx]
    nth_rw 2 [← Valuation.coe_ofClass]
    rw [← MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding]
    exact (Valued.hasBasis_uniformity K⸨X⸩ Intᵐ⁰).mem_of_mem
      (i := Units.mk0 (Valued.v.restrict x) this) (by tauto)
  · simpa [eq_coeff_of_valuation_sub_lt K hP.le (lt_add_one _)] using mem_uniformity_of_eq hS rfl

/--
Definition of `Cauchy.coeff` / `Cauchy.coeff` 的定义

English:
definition Cauchy.coeff
  signature: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  body: let _ : UniformSpace K := ⊥
fun d => DiscreteUniformity.cauchyConst hℱ.map (uniformContinuous_coeff d)

中文:
定义 Cauchy.coeff
  签名: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  定义体: let _ : UniformSpace K := ⊥
fun d => DiscreteUniformity.cauchyConst hℱ.map (uniformContinuous_coeff d)

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.cauchyConst, UniformSpace, cauchyConst, uniformContinuous_coeff
-/
def Cauchy.coeff {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) : Int -> K :=
  let _ : UniformSpace K := ⊥
fun d => DiscreteUniformity.cauchyConst hℱ.map (uniformContinuous_coeff d)

/--
theorem `Cauchy.coeff_tendsto` / 定理 `Cauchy.coeff_tendsto`

English:
theorem Cauchy.coeff_tendsto
  given: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) (D : Int)
  proof: let _ : UniformSpace K := ⊥
le_of_eq DiscreteUniformity.eq_pure_cauchyConst
    (hℱ.map (uniformContinuous_coeff D)) ▸ (principal_singleton _).symm

中文:
定理 Cauchy.coeff_tendsto
  条件: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ) (D : 整数)
  证明: let _ : UniformSpace K := ⊥
le_of_eq DiscreteUniformity.eq_pure_cauchyConst
    (hℱ.map (uniformContinuous_coeff D)) ▸ (principal_singleton _).symm

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_pure_cauchyConst, UniformSpace, eq_pure_cauchyConst, le_of_eq, principal_singleton, uniformContinuous_coeff
-/
theorem Cauchy.coeff_tendsto {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) (D : Int) :
    Tendsto (fun f : K⸨X⸩ => f.coeff D) ℱ (𝓟 {coeff hℱ D}) :=
  let _ : UniformSpace K := ⊥
le_of_eq DiscreteUniformity.eq_pure_cauchyConst
    (hℱ.map (uniformContinuous_coeff D)) ▸ (principal_singleton _).symm

/--
lemma `Cauchy.exists_lb_eventual_support` / 引理 `Cauchy.exists_lb_eventual_support`

English:
lemma Cauchy.exists_lb_eventual_support
  given: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  proof: by
  let entourage : Set (K⸨X⸩ × K⸨X⸩) := {P : K⸨X⸩ × K⸨X⸩ | Valued.v.restrict (P.snd - P.fst) < 1}
  let ζ : (MonoidWithZeroHom.ValueGroup₀ <| .ofClass (Valued.v (R := K⸨X⸩)))ˣ :=
    Units.mk0 1 (zero_ne_one.symm)
obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp Filter.le_def.mp hℱ.2 entourage
 (

中文:
引理 Cauchy.存在_lb_eventual_support
  条件: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  证明: by
  let entourage : Set (K⸨X⸩ × K⸨X⸩) := {P : K⸨X⸩ × K⸨X⸩ | Valued.v.restrict (P.snd - P.fst) < 1}
  let ζ : (MonoidWithZeroHom.ValueGroup₀ <| .ofClass (Valued.v (R := K⸨X⸩)))ˣ :=
    Units.mk0 1 (zero_ne_one.symm)
obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp Filter.le_def.mp hℱ.2 entourage
 (

Depends on / 依赖: Filter, Filter.le_def.mp, MonoidWithZeroHom, MonoidWithZeroHom.ValueGroup, P.fst, P.snd, Units.mk0, Valued, Valued.hasBasis_uniformity, Valued.v, Valued.v.restrict, entourage, forall_mem_nonempty_iff_neBot, forall_mem_nonempty_iff_neBot.mpr, hasBasis_uniformity, inter_mem_iff, inter_mem_iff.mpr, le_def, mem_of_mem, mem_prod_iff
-/
lemma Cauchy.exists_lb_eventual_support {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    exists N, forallᶠ f : K⸨X⸩ in ℱ, forall n < N, f.coeff n = (0 : K) := by
  let entourage : Set (K⸨X⸩ × K⸨X⸩) := {P : K⸨X⸩ × K⸨X⸩ | Valued.v.restrict (P.snd - P.fst) < 1}
  let ζ : (MonoidWithZeroHom.ValueGroup₀ <| .ofClass (Valued.v (R := K⸨X⸩)))ˣ :=
    Units.mk0 1 (zero_ne_one.symm)
obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp Filter.le_def.mp hℱ.2 entourage
 (Valued.hasBasis_uniformity K⸨X⸩ Intᵐ⁰).mem_of_mem (i := ζ) (by tauto)
  obtain ⟨f, hf⟩ := forall_mem_nonempty_iff_neBot.mpr hℱ.1 (S inter T) (inter_mem_iff.mpr ⟨hS, hT⟩)
  obtain ⟨N, hN⟩ : exists N : Int, forall g : K⸨X⸩,
    Valued.v (g - f) <= 1 -> forall n < N, g.coeff n = 0 := by
    by_cases hf : f = 0
    · refine ⟨0, fun x hg => ?_⟩
      rw [hf]; rw [sub_zero] at hg
      exact (valuation_le_iff_coeff_lt_eq_zero K).mp hg
    · refine ⟨min (f.2.isWF.min (HahnSeries.support_nonempty_iff.mpr hf)) 0 - 1, fun _ hg n hn => ?_⟩
      rw [eq_coeff_of_valuation_sub_lt K hg (d := 0)]
      · exact Function.notMem_support.mp fun h =>
        f.2.isWF.not_lt_min (HahnSeries.support_nonempty_iff.mpr hf) h
 lt_trans hn Int.sub_one_lt_iff.mpr min_le_left _ _
exact lt_of_lt_of_le hn le_of_lt (Int.sub_one_lt_of_le <| min_le_right _ _)
  use N
  apply mem_of_superset (inter_mem hS hT)
  intro g hg
  have h_prod : (f, g) in S ×ˢ T := by simp [hf.1, hg.2]
  refine hN g (le_of_lt ?_)
  simpa [Valuation.restrict_def, ← Valuation.restrict_lt_one_iff] using! H h_prod

/--
theorem `Cauchy.exists_lb_support` / 定理 `Cauchy.exists_lb_support`

English:
theorem Cauchy.exists_lb_support
  given: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  proof: by
  let _ : UniformSpace K := ⊥
  obtain ⟨N, hN⟩ := exists_lb_eventual_support hℱ
  refine ⟨N, fun n hn => Ultrafilter.eq_of_le_pure (hℱ.map (uniformContinuous_coeff n)).1
      ((principal_singleton _).symm ▸ coeff_tendsto _ _) ?_⟩
  simp only [pure_zero, nonpos_iff]
  apply Filter.mem_of_superset

中文:
定理 Cauchy.存在_lb_support
  条件: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  证明: by
  let _ : UniformSpace K := ⊥
  obtain ⟨N, hN⟩ := exists_lb_eventual_support hℱ
  refine ⟨N, fun n hn => Ultrafilter.eq_of_le_pure (hℱ.map (uniformContinuous_coeff n)).1
      ((principal_singleton _).symm ▸ coeff_tendsto _ _) ?_⟩
  simp only [pure_zero, nonpos_iff]
  apply Filter.mem_of_superset

Depends on / 依赖: Filter, Filter.mem_of_superset, Ultrafilter, Ultrafilter.eq_of_le_pure, UniformSpace, coeff_tendsto, eq_of_le_pure, exists_lb_eventual_support, mem_of_superset, nonpos_iff, principal_singleton, pure_zero, uniformContinuous_coeff
-/
theorem Cauchy.exists_lb_support {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    exists N, forall n, n < N -> coeff hℱ n = 0 := by
  let _ : UniformSpace K := ⊥
  obtain ⟨N, hN⟩ := exists_lb_eventual_support hℱ
  refine ⟨N, fun n hn => Ultrafilter.eq_of_le_pure (hℱ.map (uniformContinuous_coeff n)).1
      ((principal_singleton _).symm ▸ coeff_tendsto _ _) ?_⟩
  simp only [pure_zero, nonpos_iff]
  apply Filter.mem_of_superset hN (fun _ ha => ha _ hn)

/--
theorem `Cauchy.coeff_support_bddBelow` / 定理 `Cauchy.coeff_support_bddBelow`

English:
theorem Cauchy.coeff_support_bddBelow
  given: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  proof: by
  refine ⟨(exists_lb_support hℱ).choose, fun d hd => ?_⟩
  by_contra hNd
  exact hd ((exists_lb_support hℱ).choose_spec d (not_le.mp hNd))

中文:
定理 Cauchy.coeff_support_bddBelow
  条件: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  证明: by
  refine ⟨(exists_lb_support hℱ).choose, fun d hd => ?_⟩
  by_contra hNd
  exact hd ((exists_lb_support hℱ).choose_spec d (not_le.mp hNd))

Depends on / 依赖: choose_spec, exists_lb_support, not_le, not_le.mp
-/
theorem Cauchy.coeff_support_bddBelow {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    BddBelow (coeff hℱ).support := by
  refine ⟨(exists_lb_support hℱ).choose, fun d hd => ?_⟩
  by_contra hNd
  exact hd ((exists_lb_support hℱ).choose_spec d (not_le.mp hNd))

/--
Definition of `Cauchy.limit` / `Cauchy.limit` 的定义

English:
definition Cauchy.limit
  signature: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  body: HahnSeries.mk (coeff hℱ) Set.IsWF.isPWO (coeff_support_bddBelow _).wellFoundedOn_lt

中文:
定义 Cauchy.limit
  签名: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  定义体: HahnSeries.mk (coeff hℱ) Set.IsWF.isPWO (coeff_support_bddBelow _).wellFoundedOn_lt

Depends on / 依赖: HahnSeries, HahnSeries.mk, Set.IsWF.isPWO, coeff_support_bddBelow, wellFoundedOn_lt
-/
def Cauchy.limit {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) : K⸨X⸩ :=
HahnSeries.mk (coeff hℱ) Set.IsWF.isPWO (coeff_support_bddBelow _).wellFoundedOn_lt

/--
theorem `Cauchy.exists_lb_coeff_ne` / 定理 `Cauchy.exists_lb_coeff_ne`

English:
theorem Cauchy.exists_lb_coeff_ne
  given: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  proof: by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := exists_lb_eventual_support hℱ, exists_lb_support hℱ
  refine ⟨min N₁ N₂, ℱ.3 hN₁ fun _ hf d hd => ?_⟩
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _))]; rw [hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))]

中文:
定理 Cauchy.存在_lb_coeff_ne
  条件: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  证明: by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := exists_lb_eventual_support hℱ, exists_lb_support hℱ
  refine ⟨min N₁ N₂, ℱ.3 hN₁ fun _ hf d hd => ?_⟩
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _))]; rw [hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))]

Depends on / 依赖: exists_lb_eventual_support, exists_lb_support, lt_of_lt_of_le, min_le_left, min_le_right
-/
theorem Cauchy.exists_lb_coeff_ne {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    exists N, forallᶠ f : K⸨X⸩ in ℱ, forall d < N, coeff hℱ d = f.coeff d := by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := exists_lb_eventual_support hℱ, exists_lb_support hℱ
  refine ⟨min N₁ N₂, ℱ.3 hN₁ fun _ hf d hd => ?_⟩
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _))]; rw [hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))]

/--
theorem `Cauchy.coeff_eventually_equal` / 定理 `Cauchy.coeff_eventually_equal`

English:
theorem Cauchy.coeff_eventually_equal
  given: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) {D : Int}
  proof: by
  -- `φ` sends `d` to the set of Laurent Series having `d`th coefficient equal to `ℱ.coeff`.
  let φ : Int -> Set K⸨X⸩ := fun d => {f | coeff hℱ d = f.coeff d}
  have intersec₁ :
    (⋂ n in Set.Iio D, φ n) subseteq {x : K⸨X⸩ | forall d : Int, d < D -> coeff hℱ d = x.coeff d} := by
    intro _ hf

中文:
定理 Cauchy.coeff_eventually_equal
  条件: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ) {D : 整数}
  证明: by
  -- `φ` sends `d` to the set of Laurent Series having `d`th coefficient equal to `ℱ.coeff`.
  let φ : Int -> Set K⸨X⸩ := fun d => {f | coeff hℱ d = f.coeff d}
  have intersec₁ :
    (⋂ n in Set.Iio D, φ n) subseteq {x : K⸨X⸩ | forall d : Int, d < D -> coeff hℱ d = x.coeff d} := by
    intro _ hf
-/
theorem Cauchy.coeff_eventually_equal {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) {D : Int} :
    forallᶠ f : K⸨X⸩ in ℱ, forall d, d < D -> coeff hℱ d = f.coeff d := by
  -- `φ` sends `d` to the set of Laurent Series having `d`th coefficient equal to `ℱ.coeff`.
  let φ : Int -> Set K⸨X⸩ := fun d => {f | coeff hℱ d = f.coeff d}
  have intersec₁ :
    (⋂ n in Set.Iio D, φ n) subseteq {x : K⸨X⸩ | forall d : Int, d < D -> coeff hℱ d = x.coeff d} := by
    intro _ hf
    simpa only [Set.mem_iInter] using! hf
  -- The goal is now to show that the intersection of all `φ d` (for `d < D`) is in `ℱ`.
  let ℓ := (exists_lb_coeff_ne hℱ).choose
  let N := max ℓ D
  have intersec₂ : ⋂ n in Set.Iio D, φ n ⊇ (⋂ n in Set.Iio ℓ, φ n) inter (⋂ n in Set.Icc ℓ N, φ n) := by
    simp only [Set.mem_Iio, Set.mem_Icc, Set.subset_iInter_iff]
    intro i hi x hx
    simp only [Set.mem_inter_iff, Set.mem_iInter, and_imp] at hx
    by_cases! H : i < ℓ
    exacts [hx.1 _ H, hx.2 _ H <| le_of_lt <| lt_max_of_lt_right hi]
  suffices (⋂ n in Set.Iio ℓ, φ n) inter (⋂ n in Set.Icc ℓ N, φ n) in ℱ by
exact ℱ.sets_of_superset this intersec₂.trans intersec₁
  /- To show that the intersection we have in sight is in `ℱ`, we use that it contains a double
  intersection (an infinite and a finite one): by general properties of filters, we are reduced
  to show that both terms are in `ℱ`, which is easy in light of their definition. -/
  · simp only [Set.mem_Iio, inter_mem_iff]
    constructor
    · have := (exists_lb_coeff_ne hℱ).choose_spec
      rw [Filter.eventually_iff] at this
      convert! this
      ext
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]; rfl
    · rw [biInter_mem (Set.finite_Icc ℓ N)]
      intro i _
      apply (coeff_tendsto hℱ _).eventually
      simp

open scoped Topology
open MonoidWithZeroHom.ValueGroup₀

/--
theorem `Cauchy.eventually_mem_nhds` / 定理 `Cauchy.eventually_mem_nhds`

English:
theorem Cauchy.eventually_mem_nhds
  statement: {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
  proof: by
  obtain ⟨γ, hU₁⟩ := Valued.mem_nhds.mp hU
  suffices forallᶠ f in ℱ, f in {y : K⸨X⸩ | Valued.v (y - limit hℱ) < embedding γ.1} by
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding] at this
    apply this.mono fun _ hf => hU₁ hf
  set D := -(log (embedding γ.1) - 1) with hD₀
  have hD : exp (-

中文:
定理 Cauchy.eventually_mem_nhds
  结论: {ℱ : 滤子 K⸨X⸩} (hℱ : Cauchy ℱ)
  证明: by
  obtain ⟨γ, hU₁⟩ := Valued.mem_nhds.mp hU
  suffices forallᶠ f in ℱ, f in {y : K⸨X⸩ | Valued.v (y - limit hℱ) < embedding γ.1} by
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding] at this
    apply this.mono fun _ hf => hU₁ hf
  set D := -(log (embedding γ.1) - 1) with hD₀
  have hD : exp (-

Depends on / 依赖: Valued, Valued.mem_nhds.mp, Valued.v, Valued.v.restrict_lt_iff_lt_embedding, coeff_eventually_equal, embedding, lt_log_iff_exp_lt, lt_of_le_of_lt, mem_nhds, restrict_lt_iff_lt_embedding, simp_rw, this.mono, valuation_le_iff_coeff_lt_eq_zero
-/
theorem Cauchy.eventually_mem_nhds {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
    {U : Set K⸨X⸩} (hU : U in 𝓝 (Cauchy.limit hℱ)) : forallᶠ f in ℱ, f in U := by
  obtain ⟨γ, hU₁⟩ := Valued.mem_nhds.mp hU
  suffices forallᶠ f in ℱ, f in {y : K⸨X⸩ | Valued.v (y - limit hℱ) < embedding γ.1} by
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding] at this
    apply this.mono fun _ hf => hU₁ hf
  set D := -(log (embedding γ.1) - 1) with hD₀
  have hD : exp (-D) < embedding γ.1 := by
    rw [← lt_log_iff_exp_lt (by simp)]; rw [hD₀]
    simp
.mono apply coeff_eventually_equal (D := D) hℱ
  intro _ hf
  apply lt_of_le_of_lt (valuation_le_iff_coeff_lt_eq_zero K |>.mpr _) hD
  intro n hn
  rw [HahnSeries.coeff_sub]; rw [sub_eq_zero]; rw [eq_comm]
  exact hf _ hn

/--
Instance `instLaurentSeriesComplete` / 实例 `instLaurentSeriesComplete`

English:
instance instLaurentSeriesComplete
  signature: : CompleteSpace K⸨X⸩
  body: ⟨fun hℱ => ⟨Cauchy.limit hℱ, fun _ hS => Cauchy.eventually_mem_nhds hℱ hS⟩⟩

中文:
实例 instLaurentSeriesComplete
  签名: : 完备空间 K⸨X⸩
  定义体: ⟨fun hℱ => ⟨Cauchy.limit hℱ, fun _ hS => Cauchy.eventually_mem_nhds hℱ hS⟩⟩

Depends on / 依赖: Cauchy, Cauchy.eventually_mem_nhds, Cauchy.limit, eventually_mem_nhds
-/
instance instLaurentSeriesComplete : CompleteSpace K⸨X⸩ :=
  ⟨fun hℱ => ⟨Cauchy.limit hℱ, fun _ hS => Cauchy.eventually_mem_nhds hℱ hS⟩⟩

end Complete

section Dense

open scoped Multiplicative

open LaurentSeries PowerSeries IsDedekindDomain.HeightOneSpectrum WithZero RatFunc

/--
theorem `exists_Polynomial_intValuation_lt` / 定理 `exists_Polynomial_intValuation_lt`

English:
theorem exists_Polynomial_intValuation_lt
  given: (F : K⟦X⟧) (η : Intᵐ⁰ˣ)
  proof: by
  by_cases! h_neg : 1 < η
  · use 0
    simpa using (intValuation_le_one (PowerSeries.idealX K) F).trans_lt h_neg
  · rw [← Units.val_le_val, Units.val_one, ← WithZero.coe_one, ← coe_unzero η.ne_zero,
      coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one] at h_neg
    obtain ⟨d, hd⟩ := Int.exist

中文:
定理 存在_Polynomial_intValuation_lt
  条件: (F : K⟦X⟧) (η : 整数ᵐ⁰ˣ)
  证明: by
  by_cases! h_neg : 1 < η
  · use 0
    simpa using (intValuation_le_one (PowerSeries.idealX K) F).trans_lt h_neg
  · rw [← Units.val_le_val, Units.val_one, ← WithZero.coe_one, ← coe_unzero η.ne_zero,
      coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one] at h_neg
    obtain ⟨d, hd⟩ := Int.exist

Depends on / 依赖: F.trunc, Int.exists_eq_neg_ofNat, Multiplicative, Multiplicative.ofAdd, Multiplicative.toAdd_le, PowerSeries, PowerSeries.idealX, Units.val_le_val, Units.val_one, Valued, Valued.v, WithZero, WithZero.coe_one, coe_le_coe, coe_one, coe_unzero, exists_eq_neg_ofNat, h_neg, idealX, intValuation_le_iff_coeff_lt_eq_zero
-/
theorem exists_Polynomial_intValuation_lt (F : K⟦X⟧) (η : Intᵐ⁰ˣ) :
    exists P : K[X], (PowerSeries.idealX K).intValuation (F - P) < η := by
  by_cases! h_neg : 1 < η
  · use 0
    simpa using (intValuation_le_one (PowerSeries.idealX K) F).trans_lt h_neg
  · rw [← Units.val_le_val, Units.val_one, ← WithZero.coe_one, ← coe_unzero η.ne_zero,
      coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one] at h_neg
    obtain ⟨d, hd⟩ := Int.exists_eq_neg_ofNat h_neg
    use F.trunc (d + 1)
    have : Valued.v ((ofPowerSeries Int K) (F - (trunc (d + 1) F))) <=
      (Multiplicative.ofAdd (-(d + 1 : Int))) := by
      apply (intValuation_le_iff_coeff_lt_eq_zero K _).mpr
      simpa only [map_sub, sub_eq_zero, Polynomial.coeff_coe, coeff_trunc] using
        fun _ h => (if_pos h).symm
    rw [neg_add]; rw [ofAdd_add]; rw [← hd]; rw [ofAdd_toAdd]; rw [WithZero.coe_mul]; rw [coe_unzero]; rw [← coe_algebraMap] at this
    rw [← valuation_of_algebraMap (K := K⸨X⸩) (PowerSeries.idealX K) (F - F.trunc (d + 1))]
    apply lt_of_le_of_lt this
    rw [← mul_one (η : Intᵐ⁰)]; rw [mul_assoc]; rw [one_mul]
    gcongr
    · exact zero_lt_iff.2 η.ne_zero
    rw [← WithZero.coe_one]; rw [coe_lt_coe]; rw [ofAdd_neg]; rw [Right.inv_lt_one_iff]; rw [← ofAdd_zero]; rw [Multiplicative.ofAdd_lt]
    exact Int.zero_lt_one

/--
theorem `exists_ratFunc_val_lt` / 定理 `exists_ratFunc_val_lt`

English:
theorem exists_ratFunc_val_lt
  given: (f : K⸨X⸩) (γ : Intᵐ⁰ˣ)
  proof: by
  set F := f.powerSeriesPart with hF
  by_cases! ord_nonpos : f.order < 0
  · set η : Intᵐ⁰ˣ := Units.mk0 (exp f.order) coe_ne_zero
      with hη
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt F (η * γ)
    use RatFunc.X ^ f.order * (P : K⟮X⟯)
    have F_mul := f.ofPowerSeries_powerSerie

中文:
定理 存在_ratFunc_val_lt
  条件: (f : K⸨X⸩) (γ : 整数ᵐ⁰ˣ)
  证明: by
  set F := f.powerSeriesPart with hF
  by_cases! ord_nonpos : f.order < 0
  · set η : Intᵐ⁰ˣ := Units.mk0 (exp f.order) coe_ne_zero
      with hη
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt F (η * γ)
    use RatFunc.X ^ f.order * (P : K⟮X⟯)
    have F_mul := f.ofPowerSeries_powerSerie

Depends on / 依赖: F_mul, Int.exists_eq_neg_ofNat, RatFunc, RatFunc.X, Units.mk0, algebraMap, coe_ne_zero, exists_Polynomial_intValuation_lt, exists_eq_neg_ofNat, f.ofPowerSeries_powerSeriesPart, f.order, f.powerSeriesPart, le_of_lt, neg_neg, ofPowerSeries_X_pow, ofPowerSeries_powerSeriesPart, ord_nonpos, powerSeriesPart
-/
theorem exists_ratFunc_val_lt (f : K⸨X⸩) (γ : Intᵐ⁰ˣ) :
    exists Q : K⟮X⟯, Valued.v (f - Q) < γ := by
  set F := f.powerSeriesPart with hF
  by_cases! ord_nonpos : f.order < 0
  · set η : Intᵐ⁰ˣ := Units.mk0 (exp f.order) coe_ne_zero
      with hη
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt F (η * γ)
    use RatFunc.X ^ f.order * (P : K⟮X⟯)
    have F_mul := f.ofPowerSeries_powerSeriesPart
    obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (le_of_lt ord_nonpos)
    rw [← hF]; rw [hs]; rw [neg_neg]; rw [← ofPowerSeries_X_pow s]; rw [← inv_mul_eq_iff_eq_mul₀] at F_mul
    · have : (algebraMap K⟮X⟯ K⸨X⸩) 1 = 1 := by exact algebraMap.coe_one
      rw [hs]; rw [← F_mul]; rw [PowerSeries.coe_pow]; rw [PowerSeries.coe_X]; rw [map_mul]; rw [zpow_neg]; rw [zpow_natCast]; rw [inv_eq_one_div (RatFunc.X ^ s)]; rw [map_div₀]; rw [map_pow]; rw [RatFunc.coe_X]
      simp only [map_one]
      rw [← inv_eq_one_div]; rw [← mul_sub]; rw [map_mul]; rw [map_inv₀]; rw [← PowerSeries.coe_X]; rw [valuation_X_pow]; rw [← hs]; rw [← RatFunc.coe_coe]; rw [← PowerSeries.coe_sub]; rw [← coe_algebraMap]; rw [adicValued_apply]; rw [valuation_of_algebraMap]; rw [← Units.val_mk0 (a := exp f.order) exp_ne_zero]; rw [← hη]
      apply inv_mul_lt_of_lt_mul₀
      rwa [← Units.val_mul]
    · simp
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg ord_nonpos)
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt (PowerSeries.X ^ s * F) γ
    use P
    rw [← X_order_mul_powerSeriesPart (neg_inj.1 hs).symm]; rw [← RatFunc.coe_coe]; rw [← PowerSeries.coe_sub]; rw [← coe_algebraMap]; rw [adicValued_apply]; rw [valuation_of_algebraMap]
    exact hP

open MonoidWithZeroHom.ValueGroup₀

/--
theorem `coe_range_dense` / 定理 `coe_range_dense`

English:
theorem coe_range_dense
  statement: DenseRange ((↑) : K⟮X⟯ -> K⸨X⸩)
  proof: by
  rw [denseRange_iff_closure_range]
  ext f
  simp only [UniformSpace.mem_closure_iff_symm_ball, Set.mem_univ, iff_true, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_range, exists_exists_eq_and]
  intro V hV h_symm
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV
  obtain ⟨T, hT₀, hT₁⟩ 

中文:
定理 coe_range_dense
  结论: DenseRange ((↑) : K⟮X⟯ -> K⸨X⸩)
  证明: by
  rw [denseRange_iff_closure_range]
  ext f
  simp only [UniformSpace.mem_closure_iff_symm_ball, Set.mem_univ, iff_true, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_range, exists_exists_eq_and]
  intro V hV h_symm
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV
  obtain ⟨T, hT₀, hT₁⟩ 

Depends on / 依赖: Nonempty, Set.Nonempty, Set.mem_inter_iff, Set.mem_range, Set.mem_univ, UniformSpace, UniformSpace.mem_closure_iff_symm_ball, Units.coe_map, Valued, Valued.mem_nhds_zero.mp, coe_map, denseRange_iff_closure_range, embedding, exists_exists_eq_and, exists_ratFunc_val_lt, h_symm, iff_true, mem_closure_iff_symm_ball, mem_inter_iff, mem_nhds_zero
-/
theorem coe_range_dense : DenseRange ((↑) : K⟮X⟯ -> K⸨X⸩) := by
  rw [denseRange_iff_closure_range]
  ext f
  simp only [UniformSpace.mem_closure_iff_symm_ball, Set.mem_univ, iff_true, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_range, exists_exists_eq_and]
  intro V hV h_symm
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV
  obtain ⟨T, hT₀, hT₁⟩ := hV
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hT₀
  have := (embedding γ.1)
  obtain ⟨P, hP⟩ := exists_ratFunc_val_lt f
 γ.map (embedding (f := .ofClass (valued K).v))
  use P
  apply hT₁
  apply hγ
  simpa only [Units.coe_map, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe, OneHom.coe_mk, add_comm,
    MonoidWithZeroHom.toZeroHom_coe, ← sub_eq_add_neg, Set.mem_ofPred_eq,
    Valuation.restrict_lt_iff_lt_embedding]

end Dense

section Comparison

open RatFunc AbstractCompletion IsDedekindDomain.HeightOneSpectrum WithZero

/--
lemma `exists_ratFunc_eq_v` / 引理 `exists_ratFunc_eq_v`

English:
lemma exists_ratFunc_eq_v
  given: (x : K⸨X⸩)
  statement: exists f : K⟮X⟯, Valued.v f = Valued.v x
  proof: by
  by_cases hx : Valued.v x = 0
  · use 0
    simp [hx]
  use RatFunc.X ^ (-log (Valued.v x))
  rw [zpow_neg]; rw [map_inv₀]; rw [map_zpow₀]; rw [v_def]; rw [valuation_X_eq_neg_one]; rw [← exp_zsmul]; rw [← exp_neg]
  simp [exp_log, hx]

中文:
引理 存在_ratFunc_eq_v
  条件: (x : K⸨X⸩)
  结论: 存在 f : K⟮X⟯, 赋值.v f = 赋值.v x
  证明: by
  by_cases hx : Valued.v x = 0
  · use 0
    simp [hx]
  use RatFunc.X ^ (-log (Valued.v x))
  rw [zpow_neg]; rw [map_inv₀]; rw [map_zpow₀]; rw [v_def]; rw [valuation_X_eq_neg_one]; rw [← exp_zsmul]; rw [← exp_neg]
  simp [exp_log, hx]

Depends on / 依赖: RatFunc, RatFunc.X, Valued, Valued.v, exp_log, exp_neg, exp_zsmul, v_def, valuation_X_eq_neg_one, zpow_neg
-/
lemma exists_ratFunc_eq_v (x : K⸨X⸩) : exists f : K⟮X⟯, Valued.v f = Valued.v x := by
  by_cases hx : Valued.v x = 0
  · use 0
    simp [hx]
  use RatFunc.X ^ (-log (Valued.v x))
  rw [zpow_neg]; rw [map_inv₀]; rw [map_zpow₀]; rw [v_def]; rw [valuation_X_eq_neg_one]; rw [← exp_zsmul]; rw [← exp_neg]
  simp [exp_log, hx]

open MonoidWithZeroHom.ValueGroup₀

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `inducing_coe` / 定理 `inducing_coe`

English:
theorem inducing_coe
  statement: IsUniformInducing ((↑) : K⟮X⟯ -> K⸨X⸩)
  proof: by
  rw [isUniformInducing_iff]; rw [Filter.comap]
  ext S
  simp only [Filter.mem_mk, Set.mem_ofPred_eq, uniformity_eq_comap_nhds_zero,
    Filter.mem_comap]
  constructor
  · rintro ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hR
    use {P : K⟮X⟯ | Valued.v P < embeddin

中文:
定理 inducing_coe
  结论: 是UniformInducing ((↑) : K⟮X⟯ -> K⸨X⸩)
  证明: by
  rw [isUniformInducing_iff]; rw [Filter.comap]
  ext S
  simp only [Filter.mem_mk, Set.mem_ofPred_eq, uniformity_eq_comap_nhds_zero,
    Filter.mem_comap]
  constructor
  · rintro ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hR
    use {P : K⟮X⟯ | Valued.v P < embeddin

Depends on / 依赖: Filter, Filter.comap, Filter.mem_comap, Filter.mem_mk, RatFunc, RatFunc.valuation_surjective, Set.mem_ofPred_eq, Units.mk0, Valuation, Valuation.re, Valued, Valued.mem_nhds, Valued.mem_nhds.mp, Valued.v, Valued.v.restrict, embedding, isUniformInducing_iff, mem_comap, mem_mk, mem_nhds
-/
theorem inducing_coe : IsUniformInducing ((↑) : K⟮X⟯ -> K⸨X⸩) := by
  rw [isUniformInducing_iff]; rw [Filter.comap]
  ext S
  simp only [Filter.mem_mk, Set.mem_ofPred_eq, uniformity_eq_comap_nhds_zero,
    Filter.mem_comap]
  constructor
  · rintro ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hR
    use {P : K⟮X⟯ | Valued.v P < embedding d.1}
    simp only [Valued.mem_nhds, sub_zero]
    refine ⟨?_, subset_trans (fun _ _ => pre_R ?_) pre_T⟩
    · obtain ⟨x, hx⟩ := RatFunc.valuation_surjective K (embedding d.1)
      use Units.mk0 (Valued.v.restrict x) (by
        rw [Valuation.restrict_def]; rw [ne_eq]; rw [restrict₀_eq_zero_iff]; simp [hx])
      simp [v_def, Valuation.restrict_lt_iff, ← hx]
    apply hd
    simp only [sub_zero, Set.mem_ofPred_eq]
    rw [← map_sub]; rw [Valuation.restrict_lt_iff_lt_embedding]
    simp only [valuation_def]
    rwa [← valuation_eq_LaurentSeries_valuation]
  · rintro ⟨_, ⟨hT, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hT
    set X := {f : K⸨X⸩ | Valued.v f < embedding d.1} with X_def
    refine ⟨(fun x : K⸨X⸩ × K⸨X⸩ => x.snd - x.fst) ⁻¹' X, ⟨X, ?_⟩, ?_⟩
    · refine ⟨?_, Set.Subset.refl _⟩
      · simp only [Valued.mem_nhds, sub_zero, Valuation.restrict_lt_iff_lt_embedding]
        obtain ⟨x, hx⟩ := restrict₀_surjective _ d.1
        use Units.mk0 (Valued.v.restrict (x : K⸨X⸩)) (by
          simp only [ne_eq, map_eq_zero]
          intro h
          simp only [h, map_zero] at hx
          exact Units.ne_zero _ hx.symm)
        simp only [Units.val_mk0, ← Valuation.restrict_lt_iff_lt_embedding,
          X_def, Set.ofPred_subset_ofPred, Valuation.restrict_lt_iff]
        rw [← hx]; rw [embedding_restrict₀]
        simp [v_def, valuation_coe_ratFunc]
    · refine subset_trans (fun _ _ => ?_) pre_T
      apply hd
      rw [Set.mem_ofPred_eq]; rw [sub_zero]; rw [Valuation.restrict_lt_iff_lt_embedding]; rw [v_def]; rw [valuation_eq_LaurentSeries_valuation]; rw [map_sub]
      assumption

/--
theorem `uniformContinuous_withVal_equiv` / 定理 `uniformContinuous_withVal_equiv`

English:
theorem uniformContinuous_withVal_equiv
  proof: (Valuation.IsEquiv.refl).uniformContinuous_equiv rfl

中文:
定理 uniformContinuous_withVal_equiv
  证明: (Valuation.IsEquiv.refl).uniformContinuous_equiv rfl

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.refl, uniformContinuous_equiv
-/
theorem uniformContinuous_withVal_equiv :
    UniformContinuous (WithVal.equiv (polynomialValuationX K)) :=
  (Valuation.IsEquiv.refl).uniformContinuous_equiv rfl

/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : K⟮X⟯ -> K⸨X⸩)
  proof: (isUniformInducing_iff'.1 (inducing_coe)).1.continuous

中文:
定理 continuous_coe
  结论: 连续 ((↑) : K⟮X⟯ -> K⸨X⸩)
  证明: (isUniformInducing_iff'.1 (inducing_coe)).1.continuous

Depends on / 依赖: QuasiSober, R1Space, R1Space.quasiSober, continuous, inducing_coe, isUniformInducing_iff, quasiSober
-/
theorem continuous_coe : Continuous ((↑) : K⟮X⟯ -> K⸨X⸩) :=
  (isUniformInducing_iff'.1 (inducing_coe)).1.continuous

variable (K) in
/--
Definition of `RatFuncAdicCompl` / `RatFuncAdicCompl` 的定义

English:
abbreviation RatFuncAdicCompl
  body: adicCompletion K⟮X⟯ (idealX K)

中文:
缩写 RatFuncAdicCompl
  定义体: adicCompletion K⟮X⟯ (idealX K)

Depends on / 依赖: adicCompletion, idealX
-/
abbrev RatFuncAdicCompl := adicCompletion K⟮X⟯ (idealX K)

/--
Definition of `ratfuncAdicComplPkg` / `ratfuncAdicComplPkg` 的定义

English:
abbreviation ratfuncAdicComplPkg
  signature: : AbstractCompletion (WithVal (polynomialValuationX K))
  body: UniformSpace.Completion.cPkg

中文:
缩写 ratfuncAdicComplPkg
  签名: : AbstractCompletion (WithVal (polynomialValuationX K))
  定义体: UniformSpace.Completion.cPkg

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.cPkg
-/
abbrev ratfuncAdicComplPkg : AbstractCompletion (WithVal (polynomialValuationX K)) :=
  UniformSpace.Completion.cPkg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (ratfuncAdicComplPkg (K := K).space)
  body: inferInstanceAs (Field ((polynomialValuationX K).Completion))

中文:
实例 :
  签名: 域 (ratfuncAdicComplPkg (K := K).space)
  定义体: inferInstanceAs (Field ((polynomialValuationX K).Completion))
-/
instance : Field (ratfuncAdicComplPkg (K := K).space) :=
  inferInstanceAs (Field ((polynomialValuationX K).Completion))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valued (ratfuncAdicComplPkg (K := K).space) (WithZero (Multiplicative Int))
  body: inferInstanceAs (Valued ((polynomialValuationX K).Completion) (WithZero (Multiplicative Int)))

中文:
实例 :
  签名: 赋值 (ratfuncAdicComplPkg (K := K).space) (WithZero (Multiplicative 整数))
  定义体: inferInstanceAs (Valued ((polynomialValuationX K).Completion) (WithZero (Multiplicative Int)))

Depends on / 依赖: Multiplicative, WithZero
-/
instance : Valued (ratfuncAdicComplPkg (K := K).space) (WithZero (Multiplicative Int)) :=
  inferInstanceAs (Valued ((polynomialValuationX K).Completion) (WithZero (Multiplicative Int)))

variable (K)
/--
Definition of `LaurentSeriesPkg` / `LaurentSeriesPkg` 的定义

English:
definition LaurentSeriesPkg
  signature: :
  body: K⸨X⸩
  coe := (↑) ∘ WithVal.equiv _
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    inducing_coe.comp (WithVal.uniformEquiv rfl Valuation.IsEquiv.refl).isUniformInducing
  dense := .comp coe_range_dense (WithVal.equiv _).surjectiv

中文:
定义 LaurentSeriesPkg
  签名: :
  定义体: K⸨X⸩
  coe := (↑) ∘ WithVal.equiv _
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    inducing_coe.comp (WithVal.uniformEquiv rfl Valuation.IsEquiv.refl).isUniformInducing
  dense := .comp coe_range_dense (WithVal.equiv _).surjectiv
-/
noncomputable def LaurentSeriesPkg :
    AbstractCompletion (WithVal (polynomialValuationX K)) where
  space := K⸨X⸩
  coe := (↑) ∘ WithVal.equiv _
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    inducing_coe.comp (WithVal.uniformEquiv rfl Valuation.IsEquiv.refl).isUniformInducing
  dense := .comp coe_range_dense (WithVal.equiv _).surjective.denseRange continuous_coe

/--
theorem `continuous_coe'` / 定理 `continuous_coe'`

English:
theorem continuous_coe'
  proof: continuous_coe.comp uniformContinuous_withVal_equiv.continuous

中文:
定理 continuous_coe'
  证明: continuous_coe.comp uniformContinuous_withVal_equiv.continuous

Depends on / 依赖: continuous, continuous_coe, continuous_coe.comp, uniformContinuous_withVal_equiv, uniformContinuous_withVal_equiv.continuous
-/
theorem continuous_coe' :
    Continuous (((↑) : K⟮X⟯ -> K⸨X⸩) ∘ WithVal.equiv (polynomialValuationX K)) :=
  continuous_coe.comp uniformContinuous_withVal_equiv.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (LaurentSeriesPkg K).space
  body: (LaurentSeriesPkg K).uniformStruct.toTopologicalSpace

@[simp]

中文:
实例 :
  签名: 拓扑空间 (LaurentSeriesPkg K).space
  定义体: (LaurentSeriesPkg K).uniformStruct.toTopologicalSpace

@[simp]

Depends on / 依赖: LaurentSeriesPkg, toTopologicalSpace, uniformStruct, uniformStruct.toTopologicalSpace
-/
instance : TopologicalSpace (LaurentSeriesPkg K).space :=
  (LaurentSeriesPkg K).uniformStruct.toTopologicalSpace

@[simp]
/--
theorem `LaurentSeries_coe` / 定理 `LaurentSeries_coe`

English:
theorem LaurentSeries_coe
  given: (x : K⟮X⟯)
  proof: by
  rfl

中文:
定理 LaurentSeries_coe
  条件: (x : K⟮X⟯)
  证明: by
  rfl
-/
theorem LaurentSeries_coe (x : K⟮X⟯) :
    (LaurentSeriesPkg K).coe (WithVal.toVal _ x) = (x : K⸨X⸩) := by
  rfl

/--
Definition of `extensionAsRingHom` / `extensionAsRingHom` 的定义

English:
abbreviation extensionAsRingHom
  body: UniformSpace.Completion.extensionHom
    (algebraMap K⟮X⟯ K⸨X⸩).comp (WithVal.equiv (polynomialValuationX K)).toRingHom

中文:
缩写 extensionAsRingHom
  定义体: UniformSpace.Completion.extensionHom
    (algebraMap K⟮X⟯ K⸨X⸩).comp (WithVal.equiv (polynomialValuationX K)).toRingHom

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.extensionHom, WithVal, WithVal.equiv, algebraMap, extensionHom, polynomialValuationX, toRingHom
-/
abbrev extensionAsRingHom :=
UniformSpace.Completion.extensionHom
    (algebraMap K⟮X⟯ K⸨X⸩).comp (WithVal.equiv (polynomialValuationX K)).toRingHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (RatFuncAdicCompl K)
  body: inferInstance

中文:
实例 :
  签名: 一致空间 (RatFuncAdicCompl K)
  定义体: inferInstance
-/
instance : UniformSpace (RatFuncAdicCompl K) := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace K⸨X⸩
  body: inferInstance

中文:
实例 :
  签名: 一致空间 K⸨X⸩
  定义体: inferInstance
-/
instance : UniformSpace K⸨X⸩ := inferInstance

/--
Definition of `comparePkg` / `comparePkg` 的定义

English:
abbreviation comparePkg
  signature: : RatFuncAdicCompl K ≃ᵤ K⸨X⸩
  body: (adicCompletion.uniformEquiv _ _).trans compareEquiv ratfuncAdicComplPkg (LaurentSeriesPkg K)

中文:
缩写 comparePkg
  签名: : RatFuncAdicCompl K ≃ᵤ K⸨X⸩
  定义体: (adicCompletion.uniformEquiv _ _).trans compareEquiv ratfuncAdicComplPkg (LaurentSeriesPkg K)

Depends on / 依赖: LaurentSeriesPkg, adicCompletion, adicCompletion.uniformEquiv, compareEquiv, ratfuncAdicComplPkg, uniformEquiv
-/
abbrev comparePkg : RatFuncAdicCompl K ≃ᵤ K⸨X⸩ :=
(adicCompletion.uniformEquiv _ _).trans compareEquiv ratfuncAdicComplPkg (LaurentSeriesPkg K)

/--
lemma `comparePkg_eq_extension` / 引理 `comparePkg_eq_extension`

English:
lemma comparePkg_eq_extension
  given: (x : RatFuncAdicCompl K)
  proof: rfl

中文:
引理 comparePkg_eq_extension
  条件: (x : RatFuncAdicCompl K)
  证明: rfl
-/
lemma comparePkg_eq_extension (x : RatFuncAdicCompl K) :
    (comparePkg K) x =
      (extensionAsRingHom K (continuous_coe' _)) (adicCompletion.toCompletion x) := rfl

/--
Definition of `ratfuncAdicComplRingEquiv` / `ratfuncAdicComplRingEquiv` 的定义

English:
abbreviation ratfuncAdicComplRingEquiv
  signature: : RatFuncAdicCompl K ≃+* K⸨X⸩
  body: { comparePkg K with
    map_mul' x y :=
(comparePkg_eq_extension K (x * y)).trans
(map_mul _ x.toCompletion y.toCompletion).trans
        (congrArg₂ (· * ·) (comparePkg_eq_extension K x) (comparePkg_eq_extension K y)).symm
    map_add' x y :=
(comparePkg_eq_extension K (x + y)).trans
(map_add _ x.to

中文:
缩写 ratfuncAdicComplRingEquiv
  签名: : RatFuncAdicCompl K ≃+* K⸨X⸩
  定义体: { comparePkg K with
    map_mul' x y :=
(comparePkg_eq_extension K (x * y)).trans
(map_mul _ x.toCompletion y.toCompletion).trans
        (congrArg₂ (· * ·) (comparePkg_eq_extension K x) (comparePkg_eq_extension K y)).symm
    map_add' x y :=
(comparePkg_eq_extension K (x + y)).trans
(map_add _ x.to

Depends on / 依赖: comparePkg, comparePkg_eq_extension, map_add, map_mul, toCompletion, x.toCompletion, y.toCompletion
-/
abbrev ratfuncAdicComplRingEquiv : RatFuncAdicCompl K ≃+* K⸨X⸩ :=
  { comparePkg K with
    map_mul' x y :=
(comparePkg_eq_extension K (x * y)).trans
(map_mul _ x.toCompletion y.toCompletion).trans
        (congrArg₂ (· * ·) (comparePkg_eq_extension K x) (comparePkg_eq_extension K y)).symm
    map_add' x y :=
(comparePkg_eq_extension K (x + y)).trans
(map_add _ x.toCompletion y.toCompletion).trans
        (congrArg₂ (· + ·) (comparePkg_eq_extension K x) (comparePkg_eq_extension K y)).symm }

/--
Definition of `LaurentSeriesRingEquiv` / `LaurentSeriesRingEquiv` 的定义

English:
abbreviation LaurentSeriesRingEquiv
  signature: : K⸨X⸩ ≃+* RatFuncAdicCompl K
  body: (ratfuncAdicComplRingEquiv K).symm

中文:
缩写 LaurentSeriesRingEquiv
  签名: : K⸨X⸩ ≃+* RatFuncAdicCompl K
  定义体: (ratfuncAdicComplRingEquiv K).symm

Depends on / 依赖: ratfuncAdicComplRingEquiv
-/
abbrev LaurentSeriesRingEquiv : K⸨X⸩ ≃+* RatFuncAdicCompl K :=
  (ratfuncAdicComplRingEquiv K).symm

/--
lemma `LaurentSeriesRingEquiv_def` / 引理 `LaurentSeriesRingEquiv_def`

English:
lemma LaurentSeriesRingEquiv_def
  given: (f : K⟦X⟧)
  proof: rfl

@[simp]

中文:
引理 LaurentSeriesRingEquiv_def
  条件: (f : K⟦X⟧)
  证明: rfl

@[simp]
-/
lemma LaurentSeriesRingEquiv_def (f : K⟦X⟧) :
    (LaurentSeriesRingEquiv K) f = adicCompletion.ofCompletion
      ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg (f : K⸨X⸩)) :=
  rfl

@[simp]
/--
theorem `ratfuncAdicComplRingEquiv_apply` / 定理 `ratfuncAdicComplRingEquiv_apply`

English:
theorem ratfuncAdicComplRingEquiv_apply
  given: (x : RatFuncAdicCompl K)
  proof: rfl

中文:
定理 ratfuncAdicComplRingEquiv_apply
  条件: (x : RatFuncAdicCompl K)
  证明: rfl
-/
theorem ratfuncAdicComplRingEquiv_apply (x : RatFuncAdicCompl K) :
    ratfuncAdicComplRingEquiv K x =
      ratfuncAdicComplPkg.compare (LaurentSeriesPkg K) (adicCompletion.toCompletion x) := rfl

/--
theorem `coe_X_compare` / 定理 `coe_X_compare`

English:
theorem coe_X_compare
  proof: by
  rw [ratfuncAdicComplRingEquiv_apply]; rw [PowerSeries.coe_X]; rw [← RatFunc.coe_X]; rw [← LaurentSeries_coe]; rw [← compare_coe]
  rfl

中文:
定理 coe_X_compare
  证明: by
  rw [ratfuncAdicComplRingEquiv_apply]; rw [PowerSeries.coe_X]; rw [← RatFunc.coe_X]; rw [← LaurentSeries_coe]; rw [← compare_coe]
  rfl

Depends on / 依赖: LaurentSeries_coe, PowerSeries, PowerSeries.coe_X, RatFunc, RatFunc.coe_X, coe_X, compare_coe, ratfuncAdicComplRingEquiv_apply
-/
theorem coe_X_compare :
    (ratfuncAdicComplRingEquiv K) ((RatFunc.X : K⟮X⟯) : RatFuncAdicCompl K) =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
  rw [ratfuncAdicComplRingEquiv_apply]; rw [PowerSeries.coe_X]; rw [← RatFunc.coe_X]; rw [← LaurentSeries_coe]; rw [← compare_coe]
  rfl

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (a : K)
  statement: algebraMap K K⸨X⸩ a = HahnSeries.C a
  proof: by
  simp [RingHom.algebraMap_toAlgebra]

中文:
定理 algebraMap_apply
  条件: (a : K)
  结论: algebraMap K K⸨X⸩ a = Hahn级数.C a
  证明: by
  simp [RingHom.algebraMap_toAlgebra]

Depends on / 依赖: RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra
-/
theorem algebraMap_apply (a : K) : algebraMap K K⸨X⸩ a = HahnSeries.C a := by
  simp [RingHom.algebraMap_toAlgebra]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra K (RatFuncAdicCompl K)
  body: RingHom.toAlgebra ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C)

中文:
实例 :
  签名: 代数 K (RatFuncAdicCompl K)
  定义体: RingHom.toAlgebra ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C)

Depends on / 依赖: HahnSeries, HahnSeries.C, LaurentSeriesRingEquiv, RingHom, RingHom.toAlgebra, toAlgebra, toRingHom, toRingHom.comp
-/
instance : Algebra K (RatFuncAdicCompl K) :=
  RingHom.toAlgebra ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C)

/--
Definition of `LaurentSeriesAlgEquiv` / `LaurentSeriesAlgEquiv` 的定义

English:
definition LaurentSeriesAlgEquiv
  signature: : K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K
  body: AlgEquiv.ofRingEquiv (f := LaurentSeriesRingEquiv K)
    (fun a => by simp [RingHom.algebraMap_toAlgebra])

中文:
定义 LaurentSeriesAlgEquiv
  签名: : K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K
  定义体: AlgEquiv.ofRingEquiv (f := LaurentSeriesRingEquiv K)
    (fun a => by simp [RingHom.algebraMap_toAlgebra])

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, LaurentSeriesRingEquiv, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra, ofRingEquiv
-/
def LaurentSeriesAlgEquiv : K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K :=
  AlgEquiv.ofRingEquiv (f := LaurentSeriesRingEquiv K)
    (fun a => by simp [RingHom.algebraMap_toAlgebra])

open Filter WithZero

open scoped WithZeroTopology Topology Multiplicative

/--
theorem `valuation_LaurentSeries_equal_extension` / 定理 `valuation_LaurentSeries_equal_extension`

English:
theorem valuation_LaurentSeries_equal_extension
  proof: by
  apply IsDenseInducing.extend_unique
  · intro x
    rw [← WithVal.apply_ofVal]; rw [valuation_eq_LaurentSeries_valuation K]
    rfl
  · exact Valued.continuous_valuation_of_surjective (valuation_surjective K)

中文:
定理 valuation_LaurentSeries_equal_extension
  证明: by
  apply IsDenseInducing.extend_unique
  · intro x
    rw [← WithVal.apply_ofVal]; rw [valuation_eq_LaurentSeries_valuation K]
    rfl
  · exact Valued.continuous_valuation_of_surjective (valuation_surjective K)

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extend_unique, Valued, Valued.continuous_valuation_of_surjective, WithVal, WithVal.apply_ofVal, apply_ofVal, continuous_valuation_of_surjective, extend_unique, valuation_eq_LaurentSeries_valuation, valuation_surjective
-/
theorem valuation_LaurentSeries_equal_extension :
    (LaurentSeriesPkg K).isDenseInducing.extend Valued.v = (Valued.v : K⸨X⸩ -> Intᵐ⁰) := by
  apply IsDenseInducing.extend_unique
  · intro x
    rw [← WithVal.apply_ofVal]; rw [valuation_eq_LaurentSeries_valuation K]
    rfl
  · exact Valued.continuous_valuation_of_surjective (valuation_surjective K)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tendsto_valuation` / 定理 `tendsto_valuation`

English:
theorem tendsto_valuation
  given: (a : (idealX K).adicCompletion K⟮X⟯)
  proof: by
  have := Valued.is_topological_valuation (R := (idealX K).adicCompletion K⟮X⟯)
  by_cases ha : a = 0
  · rw [tendsto_def]
    intro S hS
    rw [ha]; rw [map_zero]; rw [WithZeroTopology.hasBasis_nhds_zero.1 S] at hS
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS
    use {t | Valued.v t < γ}
    construct

中文:
定理 tendsto_valuation
  条件: (a : (idealX K).adicCompletion K⟮X⟯)
  证明: by
  have := Valued.is_topological_valuation (R := (idealX K).adicCompletion K⟮X⟯)
  by_cases ha : a = 0
  · rw [tendsto_def]
    intro S hS
    rw [ha]; rw [map_zero]; rw [WithZeroTopology.hasBasis_nhds_zero.1 S] at hS
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS
    use {t | Valued.v t < γ}
    construct

Depends on / 依赖: Units.mk0, Valuation, Valuation.restrict_def, Valued, Valued.is_topological_valuation, Valued.v, Valued.v.restrict, WithZeroTopology, WithZeroTopology.hasBasis_nhds_zero, adicCompletion, hasBasis_nhds_zero, idealX, is_topological_valuation, map_eq_zero, map_zero, ne_eq, restrict, restrict_def, tendsto_def, valuedAdicCompletion_surjective
-/
theorem tendsto_valuation (a : (idealX K).adicCompletion K⟮X⟯) :
    Tendsto (Valued.v : K⟮X⟯ -> Intᵐ⁰) (comap (↑) (𝓝 a)) (𝓝 (Valued.v a : Intᵐ⁰)) := by
  have := Valued.is_topological_valuation (R := (idealX K).adicCompletion K⟮X⟯)
  by_cases ha : a = 0
  · rw [tendsto_def]
    intro S hS
    rw [ha]; rw [map_zero]; rw [WithZeroTopology.hasBasis_nhds_zero.1 S] at hS
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS
    use {t | Valued.v t < γ}
    constructor
    · rw [ha, this]
      obtain ⟨x, hx⟩ := valuedAdicCompletion_surjective K⟮X⟯ (idealX K) γ
      use Units.mk0 (Valued.v.restrict x) (by
        simp only [Valuation.restrict_def, ne_eq, map_eq_zero]
        intro h
        simp only [h, map_zero] at hx
        tauto)
      simp [Units.val_mk0, Valuation.restrict_lt_iff, hx]
    · refine Set.Subset.trans (fun a _ => ?_) (Set.preimage_mono γ_le)
      rw [Set.mem_preimage]; rw [Set.mem_Iio]; rw [← Valued.valuedCompletion_apply a]
      simp_all
  · rw [WithZeroTopology.tendsto_of_ne_zero ((Valuation.ne_zero_iff Valued.v).mpr ha),
      Filter.eventually_comap, Filter.Eventually, Valued.mem_nhds]
    use Units.mk0 (Valued.v.restrict a) (by simp [Valuation.restrict_def, ha])
    simp only [Units.val_mk0, v_def, Set.ofPred_subset_ofPred]
    rintro y val_y b rfl
    rw [← valuedAdicCompletion_eq_valuation']
exact (Valuation.restrict_inj _).mp Valuation.map_eq_of_sub_lt Valued.v.restrict val_y

set_option backward.isDefEq.respectTransparency false in
/--
theorem `valuation_compare` / 定理 `valuation_compare`

English:
theorem valuation_compare
  given: (f : K⸨X⸩)
  proof: by
  change Valued.v (adicCompletion.ofCompletion
    ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg f)) = Valued.v f
  rw [adicCompletion.valued_ofCompletion]
  let : UniformSpace (ratfuncAdicComplPkg (K := K).space) :=
      ratfuncAdicComplPkg.uniformStruct
  have raw_surj : Function.Surjectiv

中文:
定理 valuation_compare
  条件: (f : K⸨X⸩)
  证明: by
  change Valued.v (adicCompletion.ofCompletion
    ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg f)) = Valued.v f
  rw [adicCompletion.valued_ofCompletion]
  let : UniformSpace (ratfuncAdicComplPkg (K := K).space) :=
      ratfuncAdicComplPkg.uniformStruct
  have raw_surj : Function.Surjectiv

Depends on / 依赖: Completion, Function, Function.Surjective, LaurentSeriesPkg, Surjective, UniformSpace, Valued, Valued.v, Valued.valuedCompletion_surjective_iff.mpr, adicCompletion, adicCompletion.ofCompletion, adicCompletion.valued_ofCompletion, compare, compare_co, idealX, ofCompletion, of_comp, polynomialValuationX, ratfuncAdicComplPkg, ratfuncAdicComplPkg.uniformStruct
-/
theorem valuation_compare (f : K⸨X⸩) :
    Valued.v (LaurentSeriesRingEquiv K f) = Valued.v f := by
  change Valued.v (adicCompletion.ofCompletion
    ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg f)) = Valued.v f
  rw [adicCompletion.valued_ofCompletion]
  let : UniformSpace (ratfuncAdicComplPkg (K := K).space) :=
      ratfuncAdicComplPkg.uniformStruct
  have raw_surj : Function.Surjective (Valued.v : (polynomialValuationX K).Completion -> Intᵐ⁰) :=
Valued.valuedCompletion_surjective_iff.mpr .of_comp ((idealX K).valuation_surjective K⟮X⟯)
  rw [← valuation_LaurentSeries_equal_extension]; rw [← compare_comp_eq_compare ratfuncAdicComplPkg _]
  · exact congr_fun (ratfuncAdicComplPkg.isDenseInducing.extend_unique
      Valued.valuedCompletion_apply (Valued.continuous_valuation_of_surjective raw_surj)).symm _
  · refine Valued.continuous_valuation_of_surjective (fun x => ?_)
    obtain ⟨y, rfl⟩ := RatFunc.valuation_surjective K x
    exact ⟨.toVal _ y, rfl⟩
  · intro x
    have h_cont := Valued.continuous_valuation_of_surjective raw_surj
    rw [ratfuncAdicComplPkg.isDenseInducing.extend_unique
        Valued.valuedCompletion_apply h_cont]
    exact (h_cont.continuousAt.tendsto.comp tendsto_comap).congr
      Valued.valuedCompletion_apply

section PowerSeries

/--
Definition of `powerSeries_as_subring` / `powerSeries_as_subring` 的定义

English:
abbreviation powerSeries_as_subring
  signature: : Subring K⸨X⸩
  body: Subring.map (HahnSeries.ofPowerSeries Int K) ⊤

中文:
缩写 powerSeries_as_subring
  签名: : 子环 K⸨X⸩
  定义体: Subring.map (HahnSeries.ofPowerSeries Int K) ⊤

Depends on / 依赖: HahnSeries, HahnSeries.ofPowerSeries, Subring, Subring.map, ofPowerSeries
-/
abbrev powerSeries_as_subring : Subring K⸨X⸩ :=
  Subring.map (HahnSeries.ofPowerSeries Int K) ⊤

/--
Definition of `powerSeriesEquivSubring` / `powerSeriesEquivSubring` 的定义

English:
abbreviation powerSeriesEquivSubring
  signature: : K⟦X⟧ ≃+* powerSeries_as_subring K
  body: ((Subring.topEquiv).symm).trans (Subring.equivMapOfInjective ⊤ (ofPowerSeries Int K)
    ofPowerSeries_injective)

中文:
缩写 powerSeriesEquivSubring
  签名: : K⟦X⟧ ≃+* powerSeries_as_subring K
  定义体: ((Subring.topEquiv).symm).trans (Subring.equivMapOfInjective ⊤ (ofPowerSeries Int K)
    ofPowerSeries_injective)

Depends on / 依赖: Subring, Subring.equivMapOfInjective, Subring.topEquiv, equivMapOfInjective, ofPowerSeries, ofPowerSeries_injective, topEquiv
-/
abbrev powerSeriesEquivSubring : K⟦X⟧ ≃+* powerSeries_as_subring K :=
  ((Subring.topEquiv).symm).trans (Subring.equivMapOfInjective ⊤ (ofPowerSeries Int K)
    ofPowerSeries_injective)

/--
lemma `powerSeriesEquivSubring_apply` / 引理 `powerSeriesEquivSubring_apply`

English:
lemma powerSeriesEquivSubring_apply
  given: (f : K⟦X⟧)
  proof: rfl

中文:
引理 powerSeriesEquivSubring_apply
  条件: (f : K⟦X⟧)
  证明: rfl
-/
lemma powerSeriesEquivSubring_apply (f : K⟦X⟧) :
    powerSeriesEquivSubring K f =
      ⟨HahnSeries.ofPowerSeries Int K f, Subring.mem_map.mpr ⟨f, trivial, rfl⟩⟩ :=
  rfl

/--
lemma `powerSeriesEquivSubring_coe_apply` / 引理 `powerSeriesEquivSubring_coe_apply`

English:
lemma powerSeriesEquivSubring_coe_apply
  given: (f : K⟦X⟧)
  proof: rfl

中文:
引理 powerSeriesEquivSubring_coe_apply
  条件: (f : K⟦X⟧)
  证明: rfl
-/
lemma powerSeriesEquivSubring_coe_apply (f : K⟦X⟧) :
    (powerSeriesEquivSubring K f : K⸨X⸩) = ofPowerSeries Int K f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mem_integers_of_powerSeries` / 定理 `mem_integers_of_powerSeries`

English:
theorem mem_integers_of_powerSeries
  given: (F : K⟦X⟧)
  proof: by
  rw [mem_adicCompletionIntegers]; rw [valuation_compare]; rw [val_le_one_iff_eq_coe]
  exact ⟨F, rfl⟩

中文:
定理 mem_integers_of_powerSeries
  条件: (F : K⟦X⟧)
  证明: by
  rw [mem_adicCompletionIntegers]; rw [valuation_compare]; rw [val_le_one_iff_eq_coe]
  exact ⟨F, rfl⟩

Depends on / 依赖: mem_adicCompletionIntegers, val_le_one_iff_eq_coe, valuation_compare
-/
theorem mem_integers_of_powerSeries (F : K⟦X⟧) :
    (LaurentSeriesRingEquiv K) F in (idealX K).adicCompletionIntegers K⟮X⟯ := by
  rw [mem_adicCompletionIntegers]; rw [valuation_compare]; rw [val_le_one_iff_eq_coe]
  exact ⟨F, rfl⟩

/--
theorem `exists_powerSeries_of_memIntegers` / 定理 `exists_powerSeries_of_memIntegers`

English:
theorem exists_powerSeries_of_memIntegers
  statement: {x : RatFuncAdicCompl K}
  proof: by
  set f := (ratfuncAdicComplRingEquiv K) x with hf
  have hval : Valued.v f <= 1 := by
    rw [← valuation_compare (K := K) f]; rw [hf]; rw [RingEquiv.symm_apply_apply]; rw [← mem_adicCompletionIntegers]
    exact hx
  obtain ⟨F, hF⟩ := (val_le_one_iff_eq_coe K f).mp hval
  exact ⟨F, by rw [hF, h

中文:
定理 存在_powerSeries_of_mem整数egers
  结论: {x : RatFuncAdicCompl K}
  证明: by
  set f := (ratfuncAdicComplRingEquiv K) x with hf
  have hval : Valued.v f <= 1 := by
    rw [← valuation_compare (K := K) f]; rw [hf]; rw [RingEquiv.symm_apply_apply]; rw [← mem_adicCompletionIntegers]
    exact hx
  obtain ⟨F, hF⟩ := (val_le_one_iff_eq_coe K f).mp hval
  exact ⟨F, by rw [hF, h

Depends on / 依赖: RingEquiv, RingEquiv.symm_apply_apply, Valued, Valued.v, mem_adicCompletionIntegers, ratfuncAdicComplRingEquiv, symm_apply_apply, val_le_one_iff_eq_coe, valuation_compare
-/
theorem exists_powerSeries_of_memIntegers {x : RatFuncAdicCompl K}
    (hx : x in (idealX K).adicCompletionIntegers K⟮X⟯) :
    exists F : K⟦X⟧, (LaurentSeriesRingEquiv K) F = x := by
  set f := (ratfuncAdicComplRingEquiv K) x with hf
  have hval : Valued.v f <= 1 := by
    rw [← valuation_compare (K := K) f]; rw [hf]; rw [RingEquiv.symm_apply_apply]; rw [← mem_adicCompletionIntegers]
    exact hx
  obtain ⟨F, hF⟩ := (val_le_one_iff_eq_coe K f).mp hval
  exact ⟨F, by rw [hF, hf, RingEquiv.symm_apply_apply]⟩

/--
theorem `powerSeries_ext_subring` / 定理 `powerSeries_ext_subring`

English:
theorem powerSeries_ext_subring
  proof: by
  ext x
  refine ⟨fun ⟨f, ⟨F, _, coe_F⟩, hF⟩ => ?_, fun H => ?_⟩
  · simp only [ValuationSubring.mem_toSubring, ← hF, ← coe_F]
    apply mem_integers_of_powerSeries
  · obtain ⟨F, hF⟩ := exists_powerSeries_of_memIntegers K H
    simp only [Subring.mem_map]
    exact ⟨F, ⟨F, trivial, rfl⟩, hF⟩

中文:
定理 powerSeries_ext_subring
  证明: by
  ext x
  refine ⟨fun ⟨f, ⟨F, _, coe_F⟩, hF⟩ => ?_, fun H => ?_⟩
  · simp only [ValuationSubring.mem_toSubring, ← hF, ← coe_F]
    apply mem_integers_of_powerSeries
  · obtain ⟨F, hF⟩ := exists_powerSeries_of_memIntegers K H
    simp only [Subring.mem_map]
    exact ⟨F, ⟨F, trivial, rfl⟩, hF⟩

Depends on / 依赖: Subring, Subring.mem_map, ValuationSubring, ValuationSubring.mem_toSubring, coe_F, exists_powerSeries_of_memIntegers, mem_integers_of_powerSeries, mem_map, mem_toSubring
-/
theorem powerSeries_ext_subring :
    Subring.map (LaurentSeriesRingEquiv K).toRingHom (powerSeries_as_subring K) =
      ((idealX K).adicCompletionIntegers K⟮X⟯).toSubring := by
  ext x
  refine ⟨fun ⟨f, ⟨F, _, coe_F⟩, hF⟩ => ?_, fun H => ?_⟩
  · simp only [ValuationSubring.mem_toSubring, ← hF, ← coe_F]
    apply mem_integers_of_powerSeries
  · obtain ⟨F, hF⟩ := exists_powerSeries_of_memIntegers K H
    simp only [Subring.mem_map]
    exact ⟨F, ⟨F, trivial, rfl⟩, hF⟩

/--
Definition of `powerSeriesRingEquiv` / `powerSeriesRingEquiv` 的定义

English:
abbreviation powerSeriesRingEquiv
  signature: : K⟦X⟧ ≃+* (idealX K).adicCompletionIntegers K⟮X⟯
  body: ((powerSeriesEquivSubring K).trans (LaurentSeriesRingEquiv K).subringMap).trans
 RingEquiv.subringCongr (powerSeries_ext_subring K)

中文:
缩写 powerSeriesRingEquiv
  签名: : K⟦X⟧ ≃+* (idealX K).adicCompletion整数egers K⟮X⟯
  定义体: ((powerSeriesEquivSubring K).trans (LaurentSeriesRingEquiv K).subringMap).trans
 RingEquiv.subringCongr (powerSeries_ext_subring K)

Depends on / 依赖: LaurentSeriesRingEquiv, RingEquiv, RingEquiv.subringCongr, powerSeriesEquivSubring, powerSeries_ext_subring, subringCongr, subringMap
-/
abbrev powerSeriesRingEquiv : K⟦X⟧ ≃+* (idealX K).adicCompletionIntegers K⟮X⟯ :=
  ((powerSeriesEquivSubring K).trans (LaurentSeriesRingEquiv K).subringMap).trans
 RingEquiv.subringCongr (powerSeries_ext_subring K)

/--
lemma `powerSeriesRingEquiv_coe_apply` / 引理 `powerSeriesRingEquiv_coe_apply`

English:
lemma powerSeriesRingEquiv_coe_apply
  given: (f : K⟦X⟧)
  proof: rfl

中文:
引理 powerSeriesRingEquiv_coe_apply
  条件: (f : K⟦X⟧)
  证明: rfl
-/
lemma powerSeriesRingEquiv_coe_apply (f : K⟦X⟧) :
    powerSeriesRingEquiv K f = LaurentSeriesRingEquiv K (f : K⸨X⸩) :=
  rfl

/--
lemma `LaurentSeriesRingEquiv_mem_valuationSubring` / 引理 `LaurentSeriesRingEquiv_mem_valuationSubring`

English:
lemma LaurentSeriesRingEquiv_mem_valuationSubring
  given: (f : K⟦X⟧)
  proof: by
  simp only [Valuation.mem_valuationSubring_iff]
  rw [valuation_compare]; rw [val_le_one_iff_eq_coe]
  use f

中文:
引理 LaurentSeriesRingEquiv_mem_valuationSubring
  条件: (f : K⟦X⟧)
  证明: by
  simp only [Valuation.mem_valuationSubring_iff]
  rw [valuation_compare]; rw [val_le_one_iff_eq_coe]
  use f

Depends on / 依赖: Valuation, Valuation.mem_valuationSubring_iff, mem_valuationSubring_iff, val_le_one_iff_eq_coe, valuation_compare
-/
lemma LaurentSeriesRingEquiv_mem_valuationSubring (f : K⟦X⟧) :
    LaurentSeriesRingEquiv K f in Valued.v.valuationSubring := by
  simp only [Valuation.mem_valuationSubring_iff]
  rw [valuation_compare]; rw [val_le_one_iff_eq_coe]
  use f

/--
lemma `algebraMap_C_mem_adicCompletionIntegers` / 引理 `algebraMap_C_mem_adicCompletionIntegers`

English:
lemma algebraMap_C_mem_adicCompletionIntegers
  given: (x : K)
  proof: by
  have : HahnSeries.C x = ofPowerSeries Int K (PowerSeries.C x) := by
    simp [C_apply, ofPowerSeries_C]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
  apply LaurentSeriesRingEquiv_mem_valuationSubring

中文:
引理 algebraMap_C_mem_adicCompletion整数egers
  条件: (x : K)
  证明: by
  have : HahnSeries.C x = ofPowerSeries Int K (PowerSeries.C x) := by
    simp [C_apply, ofPowerSeries_C]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
  apply LaurentSeriesRingEquiv_mem_valuationSubring

Depends on / 依赖: C_apply, HahnSeries, HahnSeries.C, LaurentSeriesRingEquiv_mem_valuationSubring, PowerSeries, PowerSeries.C, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_coe, RingHom.comp_apply, coe_coe, comp_apply, ofPowerSeries, ofPowerSeries_C, toRingHom_eq_coe
-/
lemma algebraMap_C_mem_adicCompletionIntegers (x : K) :
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C) x in
      adicCompletionIntegers K⟮X⟯ (idealX K) := by
  have : HahnSeries.C x = ofPowerSeries Int K (PowerSeries.C x) := by
    simp [C_apply, ofPowerSeries_C]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
  apply LaurentSeriesRingEquiv_mem_valuationSubring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra K ((idealX K).adicCompletionIntegers K⟮X⟯)
  body: RingHom.toAlgebra
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C).codRestrict _
      (algebraMap_C_mem_adicCompletionIntegers K)

中文:
实例 :
  签名: 代数 K ((idealX K).adicCompletion整数egers K⟮X⟯)
  定义体: RingHom.toAlgebra
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C).codRestrict _
      (algebraMap_C_mem_adicCompletionIntegers K)

Depends on / 依赖: HahnSeries, HahnSeries.C, LaurentSeriesRingEquiv, RingHom, RingHom.toAlgebra, algebraMap_C_mem_adicCompletionIntegers, codRestrict, toAlgebra, toRingHom, toRingHom.comp
-/
instance : Algebra K ((idealX K).adicCompletionIntegers K⟮X⟯) :=
RingHom.toAlgebra
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C).codRestrict _
      (algebraMap_C_mem_adicCompletionIntegers K)

/--
Definition of `powerSeriesAlgEquiv` / `powerSeriesAlgEquiv` 的定义

English:
definition powerSeriesAlgEquiv
  signature: : K⟦X⟧ ≃ₐ[K] (idealX K).adicCompletionIntegers K⟮X⟯
  body: by
  apply AlgEquiv.ofRingEquiv (f := powerSeriesRingEquiv K)
  intro a
  rw [PowerSeries.algebraMap_eq]; rw [RingHom.algebraMap_toAlgebra]; rw [← Subtype.coe_inj]; rw [powerSeriesRingEquiv_coe_apply]; rw [RingHom.codRestrict_apply _ _ (algebraMap_C_mem_adicCompletionIntegers K)]
  simp

中文:
定义 powerSeriesAlgEquiv
  签名: : K⟦X⟧ ≃ₐ[K] (idealX K).adicCompletion整数egers K⟮X⟯
  定义体: by
  apply AlgEquiv.ofRingEquiv (f := powerSeriesRingEquiv K)
  intro a
  rw [PowerSeries.algebraMap_eq]; rw [RingHom.algebraMap_toAlgebra]; rw [← Subtype.coe_inj]; rw [powerSeriesRingEquiv_coe_apply]; rw [RingHom.codRestrict_apply _ _ (algebraMap_C_mem_adicCompletionIntegers K)]
  simp

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, PowerSeries, PowerSeries.algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply, Subtype, Subtype.coe_inj, algebraMap_C_mem_adicCompletionIntegers, algebraMap_eq, algebraMap_toAlgebra, codRestrict_apply, coe_inj, ofRingEquiv, powerSeriesRingEquiv, powerSeriesRingEquiv_coe_apply
-/
def powerSeriesAlgEquiv : K⟦X⟧ ≃ₐ[K] (idealX K).adicCompletionIntegers K⟮X⟯ := by
  apply AlgEquiv.ofRingEquiv (f := powerSeriesRingEquiv K)
  intro a
  rw [PowerSeries.algebraMap_eq]; rw [RingHom.algebraMap_toAlgebra]; rw [← Subtype.coe_inj]; rw [powerSeriesRingEquiv_coe_apply]; rw [RingHom.codRestrict_apply _ _ (algebraMap_C_mem_adicCompletionIntegers K)]
  simp

end PowerSeries

end Comparison

end LaurentSeries
