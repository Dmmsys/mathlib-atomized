/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.HEval
public import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Binomial expansions of powers of Hahn Series

We introduce binomial expansions using `embDomain`.

## Main Definitions
  * `HahnSeries.binomialFamily`

## Main results
  * coefficients of powers of binomials

-/

@[expose] public section

noncomputable section

namespace HahnSeries

variable {Γ R A : Type*}

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [BinomialRing R]

namespace SummableFamily

variable [CommRing A] [Algebra R A]

/--
Definition of `binomialFamily` / `binomialFamily` 的定义

English:
definition binomialFamily
  signature: (x : A⟦Γ⟧) (r : R)
  body: powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)

@[simp]

中文:
定义 binomialFamily
  签名: (x : A⟦Γ⟧) (r : R)
  定义体: powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.binomialSeries, binomialSeries, powerSeriesFamily
-/
def binomialFamily (x : A⟦Γ⟧) (r : R) :
    SummableFamily Γ A Nat :=
  powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)

@[simp]
/--
theorem `binomialFamily_apply` / 定理 `binomialFamily_apply`

English:
theorem binomialFamily_apply
  given: {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat)
  proof: by
  simp [hx, binomialFamily]

@[simp]

中文:
定理 binomialFamily_apply
  条件: {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : 自然数)
  证明: by
  simp [hx, binomialFamily]

@[simp]

Depends on / 依赖: binomialFamily
-/
theorem binomialFamily_apply {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat) :
    binomialFamily x r n = Ring.choose r n • (x - 1) ^ n := by
  simp [hx, binomialFamily]

@[simp]
/--
theorem `binomialFamily_apply_of_orderTop_nonpos` / 定理 `binomialFamily_apply_of_orderTop_nonpos`

English:
theorem binomialFamily_apply_of_orderTop_nonpos
  statement: {x : A⟦Γ⟧} (hx : ¬ 0 < (x - 1).orderTop)
  proof: by
  rw [binomialFamily]; rw [powerSeriesFamily_of_not_orderTop_pos hx]
  by_cases hn : n = 0 <;> simp [hn]

中文:
定理 binomialFamily_apply_of_orderTop_nonpos
  结论: {x : A⟦Γ⟧} (hx : ¬ 0 < (x - 1).orderTop)
  证明: by
  rw [binomialFamily]; rw [powerSeriesFamily_of_not_orderTop_pos hx]
  by_cases hn : n = 0 <;> simp [hn]

Depends on / 依赖: binomialFamily, powerSeriesFamily_of_not_orderTop_pos
-/
theorem binomialFamily_apply_of_orderTop_nonpos {x : A⟦Γ⟧} (hx : ¬ 0 < (x - 1).orderTop)
    (r : R) (n : Nat) :
    binomialFamily x r n = 0 ^ n := by
  rw [binomialFamily]; rw [powerSeriesFamily_of_not_orderTop_pos hx]
  by_cases hn : n = 0 <;> simp [hn]

/--
theorem `binomialFamily_orderTop_pos` / 定理 `binomialFamily_orderTop_pos`

English:
theorem binomialFamily_orderTop_pos
  statement: {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : Nat}
  proof: by
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.binomialSeries_coeff, powers_toFun, hx,
    ↓reduceIte, smul_assoc, one_smul]
  have : n != 0 := by exact Nat.ne_zero_of_lt hn
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.ne_zero_of_lt hn)).mpr hx
    _ <= ((x - 1) ^ n).ord

中文:
定理 binomialFamily_orderTop_pos
  结论: {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : 自然数}
  证明: by
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.binomialSeries_coeff, powers_toFun, hx,
    ↓reduceIte, smul_assoc, one_smul]
  have : n != 0 := by exact Nat.ne_zero_of_lt hn
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.ne_zero_of_lt hn)).mpr hx
    _ <= ((x - 1) ^ n).ord

Depends on / 依赖: Nat.ne_zero_of_lt, PowerSeries, PowerSeries.binomialSeries_coeff, Ring.choose, binomialFamily, binomialSeries_coeff, ne_zero_of_lt, nsmul_pos_iff, one_smul, orderTop, orderTop_le_orderTop_smul, orderTop_nsmul_le_orderTop_pow, powers_toFun, reduceIte, smulFamily_toFun, smul_assoc
-/
theorem binomialFamily_orderTop_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : Nat}
    (hn : 0 < n) :
    0 < (binomialFamily x r n).orderTop := by
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.binomialSeries_coeff, powers_toFun, hx,
    ↓reduceIte, smul_assoc, one_smul]
  have : n != 0 := by exact Nat.ne_zero_of_lt hn
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.ne_zero_of_lt hn)).mpr hx
    _ <= ((x - 1) ^ n).orderTop := orderTop_nsmul_le_orderTop_pow
    _ <= ((Ring.choose r n) • ((x - 1) ^ n)).orderTop :=
      orderTop_le_orderTop_smul (Ring.choose r n) ((x - 1) ^ n)

/--
theorem `binomialFamily_mem_support` / 定理 `binomialFamily_mem_support`

English:
theorem binomialFamily_mem_support
  statement: {x : A⟦Γ⟧}
  proof: by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))

中文:
定理 binomialFamily_mem_support
  结论: {x : A⟦Γ⟧}
  证明: by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))

Depends on / 依赖: Nat.pos_of_ne_zero, WithTop, WithTop.coe_pos.mp, binomialFamily_orderTop_pos, coe_pos, le_of_lt, lt_of_lt_of_le, orderTop_le_of_coeff_ne_zero, pos_of_ne_zero
-/
theorem binomialFamily_mem_support {x : A⟦Γ⟧}
    (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat) {g : Γ}
    (hg : g in (binomialFamily x r n).support) : 0 <= g := by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))

/--
theorem `orderTop_hsum_binomialFamily_pos` / 定理 `orderTop_hsum_binomialFamily_pos`

English:
theorem orderTop_hsum_binomialFamily_pos
  statement: {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop)
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.eq_zero ((binomialFamily x r).hsum - 1)]
  · refine (orderTop_self_sub_one_pos_iff (binomialFamily x r).hsum).mpr ?_
    constructor
    · exact hsum_orderTop_of_le (by simp [hx]) (fun b g hg => binomialFamily_mem_support
   

中文:
定理 orderTop_hsum_binomialFamily_pos
  结论: {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop)
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.eq_zero ((binomialFamily x r).hsum - 1)]
  · refine (orderTop_self_sub_one_pos_iff (binomialFamily x r).hsum).mpr ?_
    constructor
    · exact hsum_orderTop_of_le (by simp [hx]) (fun b g hg => binomialFamily_mem_support
   

Depends on / 依赖: Nat.zero_lt_of_ne_zero, Subsingleton, Subsingleton.eq_zero, binomialFamily, binomialFamily_mem_support, binomialFamily_orderTop_pos, coeff_eq_zero_of_lt_orderTop, eq_zero, hsum_leadingCoeff_of_, hsum_orderTop_of_le, orderTop_self_sub_one_pos_iff, subsingleton_or_nontrivial, zero_lt_of_ne_zero
-/
theorem orderTop_hsum_binomialFamily_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop)
    (r : R) : (0 : WithTop Γ) < (SummableFamily.hsum (binomialFamily x r) - 1).orderTop := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.eq_zero ((binomialFamily x r).hsum - 1)]
  · refine (orderTop_self_sub_one_pos_iff (binomialFamily x r).hsum).mpr ?_
    constructor
    · exact hsum_orderTop_of_le (by simp [hx]) (fun b g hg => binomialFamily_mem_support
        hx r b hg) fun b hb => coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos hx r <|
        Nat.zero_lt_of_ne_zero hb
    · have : (binomialFamily x r 0).coeff 0 = 1 := by simp [hx]
      rw [← this]
      refine hsum_leadingCoeff_of_le (g := 0) (a := 0) (by simp [hx]) ?_ ?_
      · intro b g' hg'
        exact binomialFamily_mem_support hx r b hg'
      · intro b hb
exact coeff_eq_zero_of_lt_orderTop binomialFamily_orderTop_pos hx r
        Nat.zero_lt_of_ne_zero hb

end SummableFamily

open SummableFamily

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (orderTopSubOnePos Γ R) R
  body: toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r)

@[simp]

中文:
实例 :
  签名: 幂 (orderTopSubOnePos Γ R) R
  定义体: toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r)

@[simp]

Depends on / 依赖: orderTop_hsum_binomialFamily_pos, toOrderTopSubOnePos
-/
instance : Pow (orderTopSubOnePos Γ R) R where
  pow x r := toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r)

@[simp]
/--
theorem `binomial_power` / 定理 `binomial_power`

English:
theorem binomial_power
  given: {x : orderTopSubOnePos Γ R} {r : R}
  proof: rfl

中文:
定理 binomial_power
  条件: {x : orderTopSubOnePos Γ R} {r : R}
  证明: rfl
-/
theorem binomial_power {x : orderTopSubOnePos Γ R} {r : R} :
    x ^ r = toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r) :=
  rfl

/--
theorem `pow_add` / 定理 `pow_add`

English:
theorem pow_add
  given: {x : orderTopSubOnePos Γ R} {r s : R}
  statement: x ^ (r + s) = x ^ r * x ^ s
  proof: by
  suffices (x ^ (r + s)).val = (x ^ r * x ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r + s)).val.val = (x ^ r * x ^ s).val.val by exact Units.val_inj.mp this
  simp [binomialFamily, hsum_powerSeriesFamily_mul, hsum_mul]

中文:
定理 pow_add
  条件: {x : orderTopSubOnePos Γ R} {r s : R}
  结论: x ^ (r + s) = x ^ r * x ^ s
  证明: by
  suffices (x ^ (r + s)).val = (x ^ r * x ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r + s)).val.val = (x ^ r * x ^ s).val.val by exact Units.val_inj.mp this
  simp [binomialFamily, hsum_powerSeriesFamily_mul, hsum_mul]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe.mp, Units.val_inj.mp, binomialFamily, coe_eq_coe, hsum_mul, hsum_powerSeriesFamily_mul, val.val, val_inj
-/
theorem pow_add {x : orderTopSubOnePos Γ R} {r s : R} : x ^ (r + s) = x ^ r * x ^ s := by
  suffices (x ^ (r + s)).val = (x ^ r * x ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r + s)).val.val = (x ^ r * x ^ s).val.val by exact Units.val_inj.mp this
  simp [binomialFamily, hsum_powerSeriesFamily_mul, hsum_mul]

/--
theorem `coeff_toOrderTopSubOnePos_pow` / 定理 `coeff_toOrderTopSubOnePos_pow`

English:
theorem coeff_toOrderTopSubOnePos_pow
  given: {g : Γ} (hg : 0 < g) (r s : R) (k : Nat)
  proof: by
  simp only [val_toOrderTopSubOnePos_coe, binomial_power, coeff_hsum, smul_eq_mul]
  rw [finsum_eq_single _ k]; rw [binomialFamily_apply (orderTop_sub_pos hg r)]; rw [add_sub_cancel_left]; rw [single_pow]; rw [coeff_smul]; rw [coeff_single_same (k • g) (r ^ k)]; rw [smul_eq_mul]
  intro n hn
  rw

中文:
定理 coeff_toOrderTopSubOnePos_pow
  条件: {g : Γ} (hg : 0 < g) (r s : R) (k : 自然数)
  证明: by
  simp only [val_toOrderTopSubOnePos_coe, binomial_power, coeff_hsum, smul_eq_mul]
  rw [finsum_eq_single _ k]; rw [binomialFamily_apply (orderTop_sub_pos hg r)]; rw [add_sub_cancel_left]; rw [single_pow]; rw [coeff_smul]; rw [coeff_single_same (k • g) (r ^ k)]; rw [smul_eq_mul]
  intro n hn
  rw

Depends on / 依赖: StrictMono, StrictMono.injective, add_sub_cancel_left, binomialFamily_apply, binomial_power, coeff_hsum, coeff_single_of_ne, coeff_single_same, coeff_smul, contrapose, finsum_eq_single, hn.symm, injective, nsmul_left_strictMono, orderTop_sub_pos, single_pow, smul_eq_mul, smul_zero, val_toOrderTopSubOnePos_coe
-/
theorem coeff_toOrderTopSubOnePos_pow {g : Γ} (hg : 0 < g) (r s : R) (k : Nat) :
    HahnSeries.coeff (toOrderTopSubOnePos (orderTop_sub_pos hg r) ^ s).val (k • g) =
      Ring.choose s k • r ^ k := by
  simp only [val_toOrderTopSubOnePos_coe, binomial_power, coeff_hsum, smul_eq_mul]
  rw [finsum_eq_single _ k]; rw [binomialFamily_apply (orderTop_sub_pos hg r)]; rw [add_sub_cancel_left]; rw [single_pow]; rw [coeff_smul]; rw [coeff_single_same (k • g) (r ^ k)]; rw [smul_eq_mul]
  intro n hn
  rw [binomialFamily_apply]; rw [add_sub_cancel_left]; rw [coeff_smul]; rw [single_pow]; rw [coeff_single_of_ne]; rw [smul_zero]
  · contrapose hn
    apply (StrictMono.injective (nsmul_left_strictMono hg)) hn.symm
  · by_cases hr : r = 0 <;> simp [hr, hg]

end HahnSeries
