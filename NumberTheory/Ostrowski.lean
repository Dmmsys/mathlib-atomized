/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabrizio Barroero, Laura Capuano, Nirvana Coppola,
María Inés de Frutos-Fernández, Sam van Gool, Silvain Rideau-Kikuchi, Amos Turchet,
Francesco Veneziano
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Ostrowski’s Theorem

Ostrowski's Theorem for the field `ℚ`: every absolute value on `ℚ` is equivalent to either a
`p`-adic absolute value or to the standard Archimedean (Euclidean) absolute value.

## Main results

- `Rat.AbsoluteValue.equiv_real_or_padic`: given an absolute value on `ℚ`, it is equivalent
  to the standard Archimedean (Euclidean) absolute value `Rat.AbsoluteValue.real` or to a `p`-adic
  absolute value `Rat.AbsoluteValue.padic p` for a unique prime number `p`.

## TODO

Extend to arbitrary number fields.

## References

* [K. Conrad, *Ostrowski's Theorem for Q*][conradQ]
* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]
* [J. W. S. Cassels, *Local fields*][cassels1986local]

## Tags

absolute value, Ostrowski's theorem
-/

@[expose] public section

open Filter Nat Real Topology

-- For any `C > 0`, the limit of `C ^ (1/k)` is 1 as `k → ∞`
/--
lemma `tendsto_const_rpow_inv` / 引理 `tendsto_const_rpow_inv`

English:
lemma tendsto_const_rpow_inv
  given: {C : Real} (hC : 0 < C)
  proof: ((continuous_iff_continuousAt.mpr fun _ => continuousAt_const_rpow hC.ne').tendsto'
    0 1 (rpow_zero C)).comp <| tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_const_rpow_inv
  条件: {C : 实数} (hC : 0 < C)
  证明: ((continuous_iff_continuousAt.mpr fun _ => continuousAt_const_rpow hC.ne').tendsto'
    0 1 (rpow_zero C)).comp <| tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
-/
private lemma tendsto_const_rpow_inv {C : Real} (hC : 0 < C) :
    Tendsto (fun k : Nat => C ^ (k : Real)⁻¹) atTop (𝓝 1) :=
  ((continuous_iff_continuousAt.mpr fun _ => continuousAt_const_rpow hC.ne').tendsto'
    0 1 (rpow_zero C)).comp <| tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

--extends the lemma `tendsto_rpow_div` when the function has natural input
/--
lemma `tendsto_nat_rpow_inv` / 引理 `tendsto_nat_rpow_inv`

English:
lemma tendsto_nat_rpow_inv
  proof: by
  simp_rw [← one_div]
  exact Tendsto.comp tendsto_rpow_div tendsto_natCast_atTop_atTop

中文:
引理 tendsto_nat_rpow_inv
  证明: by
  simp_rw [← one_div]
  exact Tendsto.comp tendsto_rpow_div tendsto_natCast_atTop_atTop
-/
private lemma tendsto_nat_rpow_inv :
    Tendsto (fun k : Nat => (k : Real) ^ (k : Real)⁻¹) atTop (𝓝 1) := by
  simp_rw [← one_div]
  exact Tendsto.comp tendsto_rpow_div tendsto_natCast_atTop_atTop

-- Multiplication by a constant moves in a List.sum
/--
lemma `list_mul_sum` / 引理 `list_mul_sum`

English:
lemma list_mul_sum
  given: {R : Type*} [Semiring R] {T : Type*} (l : List T) (y : R) (x : R)
  proof: by
  simp_rw [← smul_eq_mul, List.smul_sum, List.mapIdx_eq_zipIdx_map]
  congr 1
  simp

中文:
引理 list_mul_sum
  条件: {R : 类型} [Semiring R] {T : 类型} (l : List T) (y : R) (x : R)
  证明: by
  simp_rw [← smul_eq_mul, List.smul_sum, List.mapIdx_eq_zipIdx_map]
  congr 1
  simp
-/
private lemma list_mul_sum {R : Type*} [Semiring R] {T : Type*} (l : List T) (y : R) (x : R) :
    (l.mapIdx fun i _ => x * y ^ i).sum = x * (l.mapIdx fun i _ => y ^ i).sum := by
  simp_rw [← smul_eq_mul, List.smul_sum, List.mapIdx_eq_zipIdx_map]
  congr 1
  simp

-- Geometric sum for lists
/--
lemma `list_geom` / 引理 `list_geom`

English:
lemma list_geom
  given: {T : Type*} {F : Type*} [DivisionRing F] (l : List T) {y : F} (hy : y != 1)
  proof: by
  rw [← geom_sum_eq hy l.length]; rw [List.mapIdx_eq_zipIdx_map]; rw [Finset.sum_range]; rw [← Fin.sum_univ_fun_getElem]
  simp only
  let e : Fin l.zipIdx.length ≃ Fin l.length := finCongr List.length_zipIdx
  exact Fintype.sum_bijective e e.bijective _ _ fun _ => by simp [e]

中文:
引理 list_geom
  条件: {T : 类型} {F : 类型} [DivisionRing F] (l : List T) {y : F} (hy : y != 1)
  证明: by
  rw [← geom_sum_eq hy l.length]; rw [List.mapIdx_eq_zipIdx_map]; rw [Finset.sum_range]; rw [← Fin.sum_univ_fun_getElem]
  simp only
  let e : Fin l.zipIdx.length ≃ Fin l.length := finCongr List.length_zipIdx
  exact Fintype.sum_bijective e e.bijective _ _ fun _ => by simp [e]
-/
private lemma list_geom {T : Type*} {F : Type*} [DivisionRing F] (l : List T) {y : F} (hy : y != 1) :
    (l.mapIdx fun i _ => y ^ i).sum = (y ^ l.length - 1) / (y - 1) := by
  rw [← geom_sum_eq hy l.length]; rw [List.mapIdx_eq_zipIdx_map]; rw [Finset.sum_range]; rw [← Fin.sum_univ_fun_getElem]
  simp only
  let e : Fin l.zipIdx.length ≃ Fin l.length := finCongr List.length_zipIdx
  exact Fintype.sum_bijective e e.bijective _ _ fun _ => by simp [e]

open AbsoluteValue -- does not work as intended after `namespace Rat.AbsoluteValue`

namespace Rat.AbsoluteValue

/-!
### Preliminary lemmas
-/

open Int

variable {f g : AbsoluteValue Rat Real}

/--
lemma `eq_on_nat_iff_eq` / 引理 `eq_on_nat_iff_eq`

English:
lemma eq_on_nat_iff_eq
  statement: (forall n : Nat, f n = g n) ↔ f = g
  proof: by
  refine ⟨fun h => ?_, fun h n => congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext1 z
  rw [← Rat.num_div_den z]; rw [map_div₀]; rw [map_div₀]; rw [h]; rw [eq_on_nat_iff_eq_on_int.mp h]

中文:
引理 eq_on_nat_iff_eq
  结论: (对任意 n : 自然数, f n = g n) ↔ f = g
  证明: by
  refine ⟨fun h => ?_, fun h n => congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext1 z
  rw [← Rat.num_div_den z]; rw [map_div₀]; rw [map_div₀]; rw [h]; rw [eq_on_nat_iff_eq_on_int.mp h]

Depends on / 依赖: DFunLike, DFunLike.coe, Rat.num_div_den, eq_on_nat_iff_eq_on_int, eq_on_nat_iff_eq_on_int.mp, num_div_den
-/
lemma eq_on_nat_iff_eq : (forall n : Nat, f n = g n) ↔ f = g := by
  refine ⟨fun h => ?_, fun h n => congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext1 z
  rw [← Rat.num_div_den z]; rw [map_div₀]; rw [map_div₀]; rw [h]; rw [eq_on_nat_iff_eq_on_int.mp h]

/--
lemma `exists_nat_rpow_iff_isEquiv` / 引理 `exists_nat_rpow_iff_isEquiv`

English:
lemma exists_nat_rpow_iff_isEquiv
  statement: (exists c : Real, 0 < c ∧ forall n : Nat, f n ^ c = g n) ↔ f.IsEquiv g
  proof: by
  rw [isEquiv_iff_exists_rpow_eq]
  refine ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, ?_⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, (congrFun h ·)⟩⟩
  ext1 x
  rw [← Rat.num_div_den x]; rw [map_div₀]; rw [map_div₀]; rw [div_rpow (by positivity) (by positivity)]; rw [h x.den]; rw [← apply_natAbs_eq]; rw [← apply_natAbs_eq]; rw 

中文:
引理 exists_nat_rpow_iff_isEquiv
  结论: (存在 c : 实数, 0 < c ∧ 对任意 n : 自然数, f n ^ c = g n) ↔ f.IsEquiv g
  证明: by
  rw [isEquiv_iff_exists_rpow_eq]
  refine ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, ?_⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, (congrFun h ·)⟩⟩
  ext1 x
  rw [← Rat.num_div_den x]; rw [map_div₀]; rw [map_div₀]; rw [div_rpow (by positivity) (by positivity)]; rw [h x.den]; rw [← apply_natAbs_eq]; rw [← apply_natAbs_eq]; rw 

Depends on / 依赖: Rat.num_div_den, apply_natAbs_eq, div_rpow, isEquiv_iff_exists_rpow_eq, natAbs, num_div_den, x.den, x.num
-/
lemma exists_nat_rpow_iff_isEquiv : (exists c : Real, 0 < c ∧ forall n : Nat, f n ^ c = g n) ↔ f.IsEquiv g := by
  rw [isEquiv_iff_exists_rpow_eq]
  refine ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, ?_⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, (congrFun h ·)⟩⟩
  ext1 x
  rw [← Rat.num_div_den x]; rw [map_div₀]; rw [map_div₀]; rw [div_rpow (by positivity) (by positivity)]; rw [h x.den]; rw [← apply_natAbs_eq]; rw [← apply_natAbs_eq]; rw [h (natAbs x.num)]

section Non_archimedean

/-!
### The non-archimedean case

Every bounded absolute value on `ℚ` is equivalent to a `p`-adic absolute value.
-/

/--
Definition of `padic` / `padic` 的定义

English:
definition padic
  signature: (p : Nat) [Fact p.Prime]
  body: (padicNorm p x : Real)
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
nonneg' x := cast_nonneg.mpr padicNorm.nonneg x
  eq_zero' _ :=
⟨fun H => padicNorm.zero_of_padicNorm_eq_zero cast_eq_zero.mp H,
fun H => cast_eq_zero.mpr H ▸ padicNorm.zero (p := p)⟩
  add_le' := mod_cast 

中文:
定义 padic
  签名: (p : 自然数) [Fact p.Prime]
  定义体: (padicNorm p x : Real)
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
nonneg' x := cast_nonneg.mpr padicNorm.nonneg x
  eq_zero' _ :=
⟨fun H => padicNorm.zero_of_padicNorm_eq_zero cast_eq_zero.mp H,
fun H => cast_eq_zero.mpr H ▸ padicNorm.zero (p := p)⟩
  add_le' := mod_cast 

Depends on / 依赖: padicNorm
-/
def padic (p : Nat) [Fact p.Prime] : AbsoluteValue Rat Real where
  toFun x := (padicNorm p x : Real)
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
nonneg' x := cast_nonneg.mpr padicNorm.nonneg x
  eq_zero' _ :=
⟨fun H => padicNorm.zero_of_padicNorm_eq_zero cast_eq_zero.mp H,
fun H => cast_eq_zero.mpr H ▸ padicNorm.zero (p := p)⟩
  add_le' := mod_cast padicNorm.triangle_ineq

/--
lemma `padic_eq_padicNorm` / 引理 `padic_eq_padicNorm`

English:
lemma padic_eq_padicNorm
  given: (p : Nat) [Fact p.Prime] (r : Rat)
  statement: padic p r = padicNorm p r
  proof: rfl

中文:
引理 padic_eq_padicNorm
  条件: (p : 自然数) [Fact p.Prime] (r : Rat)
  结论: padic p r = padicNorm p r
  证明: rfl
-/
@[simp] lemma padic_eq_padicNorm (p : Nat) [Fact p.Prime] (r : Rat) : padic p r = padicNorm p r := rfl

/--
lemma `padic_le_one` / 引理 `padic_le_one`

English:
lemma padic_le_one
  given: (p : Nat) [Fact p.Prime] (n : Int)
  statement: padic p n <= 1
  proof: by
  simp only [padic_eq_padicNorm]
  exact_mod_cast padicNorm.of_int n

中文:
引理 padic_le_one
  条件: (p : 自然数) [Fact p.Prime] (n : 整数)
  结论: padic p n <= 1
  证明: by
  simp only [padic_eq_padicNorm]
  exact_mod_cast padicNorm.of_int n

Depends on / 依赖: of_int, padicNorm, padicNorm.of_int, padic_eq_padicNorm
-/
lemma padic_le_one (p : Nat) [Fact p.Prime] (n : Int) : padic p n <= 1 := by
  simp only [padic_eq_padicNorm]
  exact_mod_cast padicNorm.of_int n

-- ## Step 1: define `p = minimal n s. t. 0 < f n < 1`

variable (hf_nontriv : f.IsNontrivial) (bdd : forall n : Nat, f n <= 1)

include hf_nontriv bdd in
/--
lemma `exists_minimal_nat_zero_lt_and_lt_one` / 引理 `exists_minimal_nat_zero_lt_and_lt_one`

English:
lemma exists_minimal_nat_zero_lt_and_lt_one
  proof: by
  -- There is a positive integer with absolute value different from one.
  obtain ⟨n, hn1, hn2⟩ : exists n : Nat, n != 0 ∧ f n != 1 := by
    contrapose! hf_nontriv
refine (isNontrivial_iff_ne_trivial f).not_left.mpr eq_on_nat_iff_eq.mp fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp

中文:
引理 exists_minimal_nat_zero_lt_and_lt_one
  证明: by
  -- There is a positive integer with absolute value different from one.
  obtain ⟨n, hn1, hn2⟩ : exists n : Nat, n != 0 ∧ f n != 1 := by
    contrapose! hf_nontriv
refine (isNontrivial_iff_ne_trivial f).not_left.mpr eq_on_nat_iff_eq.mp fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
-/
lemma exists_minimal_nat_zero_lt_and_lt_one :
    exists p : Nat, (0 < f p ∧ f p < 1) ∧ forall m : Nat, 0 < f m ∧ f m < 1 -> p <= m := by
  -- There is a positive integer with absolute value different from one.
  obtain ⟨n, hn1, hn2⟩ : exists n : Nat, n != 0 ∧ f n != 1 := by
    contrapose! hf_nontriv
refine (isNontrivial_iff_ne_trivial f).not_left.mpr eq_on_nat_iff_eq.mp fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hf_nontriv, hn]
  set P := {m : Nat | 0 < f ↑m ∧ f ↑m < 1} -- p is going to be the minimum of this set.
  have hP : P.Nonempty :=
    ⟨n, map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  exact ⟨sInf P, Nat.sInf_mem hP, fun _ hm => Nat.sInf_le hm⟩

-- ## Step 2: p is prime

variable {p : Nat} (hp0 : 0 < f p) (hp1 : f p < 1) (hmin : forall m : Nat, 0 < f m ∧ f m < 1 -> p <= m)

include hp0 hp1 hmin in
/--
lemma `is_prime_of_minimal_nat_zero_lt_and_lt_one` / 引理 `is_prime_of_minimal_nat_zero_lt_and_lt_one`

English:
lemma is_prime_of_minimal_nat_zero_lt_and_lt_one
  statement: p.Prime
  proof: by
  have hp2 : 2 <= p := by
    by_contra! hp
    interval_cases p <;> grind
  rw [Nat.prime_iff_not_exists_mul_eq]
  refine ⟨hp2, ?_⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  obtain ⟨ha₀, hb₀⟩ := mul_ne_zero_iff.mp (by omega : a * b != 0)
  have h {n : Nat} (hn₀ : n != 0) (hn : n < a * b) : 1 <= f n := by
 

中文:
引理 is_prime_of_minimal_nat_zero_lt_and_lt_one
  结论: p.Prime
  证明: by
  have hp2 : 2 <= p := by
    by_contra! hp
    interval_cases p <;> grind
  rw [Nat.prime_iff_not_exists_mul_eq]
  refine ⟨hp2, ?_⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  obtain ⟨ha₀, hb₀⟩ := mul_ne_zero_iff.mp (by omega : a * b != 0)
  have h {n : Nat} (hn₀ : n != 0) (hn : n < a * b) : 1 <= f n := by
 

Depends on / 依赖: Nat.cast_mul, Nat.prime_iff_not_exists_mul_eq, cast_mul, interval_cases, map_mul, map_pos_of_ne_zero, mod_cast, mul_ne_zero_iff, mul_ne_zero_iff.mp, not_le_of_gt, one_le_mul_of_one_le_of_one_le, prime_iff_not_exists_mul_eq
-/
lemma is_prime_of_minimal_nat_zero_lt_and_lt_one : p.Prime := by
  have hp2 : 2 <= p := by
    by_contra! hp
    interval_cases p <;> grind
  rw [Nat.prime_iff_not_exists_mul_eq]
  refine ⟨hp2, ?_⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  obtain ⟨ha₀, hb₀⟩ := mul_ne_zero_iff.mp (by omega : a * b != 0)
  have h {n : Nat} (hn₀ : n != 0) (hn : n < a * b) : 1 <= f n := by
    by_contra! hn₁
exact (not_le_of_gt hn) hmin n ⟨map_pos_of_ne_zero f (mod_cast hn₀), hn₁⟩
  rw [Nat.cast_mul]; rw [map_mul] at hp1
exact not_le_of_gt hp1 one_le_mul_of_one_le_of_one_le (h ha₀ ha) (h hb₀ hb)

-- ## Step 3: if p does not divide m, then f m = 1

open Real

include hp0 hp1 hmin bdd in
/--
lemma `eq_one_of_not_dvd` / 引理 `eq_one_of_not_dvd`

English:
lemma eq_one_of_not_dvd
  given: {m : Nat} (hpm : ¬ p ∣ m)
  statement: f m = 1
  proof: by
  apply le_antisymm (bdd m)
  by_contra! hm
  set M := f p ⊔ f m with hM
  set k := Nat.ceil (M.logb (1 / 2)) + 1 with hk
  obtain ⟨a, b, bezout⟩ : IsCoprime (p ^ k : Int) (m ^ k) :=
    is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
.pow .isCoprime .mpr hpm .coprime_iff_not_dvd
  have l

中文:
引理 eq_one_of_not_dvd
  条件: {m : 自然数} (hpm : ¬ p ∣ m)
  结论: f m = 1
  证明: by
  apply le_antisymm (bdd m)
  by_contra! hm
  set M := f p ⊔ f m with hM
  set k := Nat.ceil (M.logb (1 / 2)) + 1 with hk
  obtain ⟨a, b, bezout⟩ : IsCoprime (p ^ k : Int) (m ^ k) :=
    is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
.pow .isCoprime .mpr hpm .coprime_iff_not_dvd
  have l

Depends on / 依赖: IsCoprime, M.logb, Nat.ceil, bezout, coprime_iff_not_dvd, isCoprime, is_prime_of_minimal_nat_zero_lt_and_lt_one, le_antisymm, le_half, push_c, rpow_lt_rpow_of_exponent_gt, rpow_natCast
-/
lemma eq_one_of_not_dvd {m : Nat} (hpm : ¬ p ∣ m) : f m = 1 := by
  apply le_antisymm (bdd m)
  by_contra! hm
  set M := f p ⊔ f m with hM
  set k := Nat.ceil (M.logb (1 / 2)) + 1 with hk
  obtain ⟨a, b, bezout⟩ : IsCoprime (p ^ k : Int) (m ^ k) :=
    is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
.pow .isCoprime .mpr hpm .coprime_iff_not_dvd
  have le_half {x} (hx0 : 0 < x) (hx1 : x < 1) (hxM : x <= M) : x ^ k < 1 / 2 := by
    calc
    x ^ k = x ^ (k : Real) := (rpow_natCast x k).symm
    _ < x ^ M.logb (1 / 2) := by
      apply rpow_lt_rpow_of_exponent_gt hx0 hx1
      rw [hk]
      push_cast
      exact lt_add_of_le_of_pos (Nat.le_ceil _) zero_lt_one
    _ <= x ^ x.logb (1 / 2) := by
      apply rpow_le_rpow_of_exponent_ge hx0 hx1.le
      simp only [one_div, ← log_div_log, log_inv, neg_div, ← div_neg, hM]
      gcongr
      simp only [Left.neg_pos_iff]
      exact log_neg (lt_sup_iff.mpr <| .inl hp0) (sup_lt_iff.mpr ⟨hp1, hm⟩)
    _ = 1 / 2 := rpow_logb hx0 hx1.ne one_half_pos
  apply lt_irrefl (1 : Real)
  calc
  1 = f 1 := (map_one f).symm
  _ = f (a * p ^ k + b * m ^ k) := by rw_mod_cast [bezout]; norm_cast
  _ <= f (a * p ^ k) + f (b * m ^ k) := f.add_le' ..
  _ <= 1 * (f p) ^ k + 1 * (f m) ^ k := by
    simp only [map_mul, map_pow]
    gcongr <;> simpa only [← apply_natAbs_eq] using bdd _
  _ < 1 := by
have hm₀ : 0 < f m := f.pos Nat.cast_ne_zero.mpr fun H => hpm H ▸ dvd_zero p
    linarith only [le_half hp0 hp1 le_sup_left, le_half hm₀ hm le_sup_right]

-- ## Step 4: f p = p ^ (-t) for some positive real t

include hp0 hp1 hmin in
/--
lemma `exists_pos_eq_pow_neg` / 引理 `exists_pos_eq_pow_neg`

English:
lemma exists_pos_eq_pow_neg
  statement: exists t : Real, 0 < t ∧ f p = p ^ (-t)
  proof: by
  have hp : (1 : Real) < p :=
    mod_cast (is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin).one_lt
exact ⟨-logb p (f p), neg_pos.mpr logb_neg hp hp0 hp1, by
    simpa using (rpow_logb (zero_lt_one.trans hp) hp.ne' hp0).symm⟩

中文:
引理 exists_pos_eq_pow_neg
  结论: 存在 t : 实数, 0 < t ∧ f p = p ^ (-t)
  证明: by
  have hp : (1 : Real) < p :=
    mod_cast (is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin).one_lt
exact ⟨-logb p (f p), neg_pos.mpr logb_neg hp hp0 hp1, by
    simpa using (rpow_logb (zero_lt_one.trans hp) hp.ne' hp0).symm⟩

Depends on / 依赖: hp.ne, is_prime_of_minimal_nat_zero_lt_and_lt_one, logb_neg, mod_cast, neg_pos, neg_pos.mpr, one_lt, rpow_logb, zero_lt_one, zero_lt_one.trans
-/
lemma exists_pos_eq_pow_neg : exists t : Real, 0 < t ∧ f p = p ^ (-t) := by
  have hp : (1 : Real) < p :=
    mod_cast (is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin).one_lt
exact ⟨-logb p (f p), neg_pos.mpr logb_neg hp hp0 hp1, by
    simpa using (rpow_logb (zero_lt_one.trans hp) hp.ne' hp0).symm⟩

-- ## Non-archimedean case: end goal

include hf_nontriv bdd in
/--
theorem `equiv_padic_of_bounded` / 定理 `equiv_padic_of_bounded`

English:
theorem equiv_padic_of_bounded
  proof: by
  obtain ⟨p, ⟨hp0, hp1⟩, hmin⟩ := exists_minimal_nat_zero_lt_and_lt_one hf_nontriv bdd
  have hp := is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, hpt⟩ := exists_pos_eq_pow_neg hp0 hp1 hmin
  simp_rw [← exists_nat_rpow_iff_isEquiv]
  refine 

中文:
定理 equiv_padic_of_bounded
  证明: by
  obtain ⟨p, ⟨hp0, hp1⟩, hmin⟩ := exists_minimal_nat_zero_lt_and_lt_one hf_nontriv bdd
  have hp := is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, hpt⟩ := exists_pos_eq_pow_neg hp0 hp1 hmin
  simp_rw [← exists_nat_rpow_iff_isEquiv]
  refine 

Depends on / 依赖: Nat.exists_eq_pow_mul_and_not_dvd, eq_or_ne, exists_eq_pow_mul_and_not_dvd, exists_minimal_nat_zero_lt_and_lt_one, exists_nat_rpow_iff_isEquiv, exists_pos_eq_pow_neg, hf_nontriv, hp.ne_one, ht.ne, inv_pos, inv_pos.mpr, is_prime_of_minimal_nat_zero_lt_and_lt_one, ne_one, p.Prime, simp_rw
-/
theorem equiv_padic_of_bounded :
    exists! p, exists (_ : Fact p.Prime), f.IsEquiv (padic p) := by
  obtain ⟨p, ⟨hp0, hp1⟩, hmin⟩ := exists_minimal_nat_zero_lt_and_lt_one hf_nontriv bdd
  have hp := is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, hpt⟩ := exists_pos_eq_pow_neg hp0 hp1 hmin
  simp_rw [← exists_nat_rpow_iff_isEquiv]
  refine ⟨p, ⟨inferInstance, t⁻¹, inv_pos.mpr ht, fun n => ?_⟩, fun q ⟨hq, heq⟩ => ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [ht.ne']
    · rcases Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one with ⟨_, m, hpm, rfl⟩
      have := (padicNorm.nat_eq_one_iff m).mpr hpm
      simp_all [← rpow_natCast, ← rpow_mul, mul_comm t, mul_inv_cancel_right₀ ht.ne',
        eq_one_of_not_dvd bdd hp0 hp1 hmin hpm]
  · by_contra! hpq
    apply hq.elim.ne_one
    rw [ne_comm]; rw [← Nat.coprime_primes hp hq.elim]; rw [hp.coprime_iff_not_dvd] at hpq
    rcases heq with ⟨_, _, heq⟩
    simpa [eq_one_of_not_dvd bdd hp0 hp1 hmin hpq] using heq q

end Non_archimedean

section Archimedean

/-!
### Archimedean case

Every unbounded absolute value on `ℚ` is equivalent to the standard absolute value.
-/

/--
Definition of `real` / `real` 的定义

English:
definition real
  signature: : AbsoluteValue Rat Real where
  body: |x|
  map_mul' := by simp
  nonneg' := by simp
  eq_zero' := by simp
  add_le' := by simp [abs_add_le]

中文:
定义 real
  签名: : AbsoluteValue Rat 实数 where
  定义体: |x|
  map_mul' := by simp
  nonneg' := by simp
  eq_zero' := by simp
  add_le' := by simp [abs_add_le]
-/
def real : AbsoluteValue Rat Real where
  toFun x := |x|
  map_mul' := by simp
  nonneg' := by simp
  eq_zero' := by simp
  add_le' := by simp [abs_add_le]

/--
lemma `real_eq_abs` / 引理 `real_eq_abs`

English:
lemma real_eq_abs
  given: (r : Rat)
  statement: real r = |r|
  proof: (cast_abs r).symm

中文:
引理 real_eq_abs
  条件: (r : Rat)
  结论: real r = |r|
  证明: (cast_abs r).symm
-/
@[simp] lemma real_eq_abs (r : Rat) : real r = |r| := (cast_abs r).symm

-- ## Preliminary result

/--
lemma `apply_le_sum_digits` / 引理 `apply_le_sum_digits`

English:
lemma apply_le_sum_digits
  given: (n : Nat) {m : Nat} (hm : 1 < m)
  proof: by
  set L := Nat.digits m n
  set L' : List Rat := List.map Nat.cast (L.mapIdx fun i a => a * m ^ i)
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : Nat} (hc : c in Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (f.apply_nat_le_self c) (mo

中文:
引理 apply_le_sum_digits
  条件: (n : 自然数) {m : 自然数} (hm : 1 < m)
  证明: by
  set L := Nat.digits m n
  set L' : List Rat := List.map Nat.cast (L.mapIdx fun i a => a * m ^ i)
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : Nat} (hc : c in Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (f.apply_nat_le_self c) (mo

Depends on / 依赖: L.mapIdx, List.map, Nat.cast, Nat.digits, digits, mapIdx
-/
lemma apply_le_sum_digits (n : Nat) {m : Nat} (hm : 1 < m) :
    f n <= ((Nat.digits m n).mapIdx fun i _ => m * (f m) ^ i).sum := by
  set L := Nat.digits m n
  set L' : List Rat := List.map Nat.cast (L.mapIdx fun i a => a * m ^ i)
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : Nat} (hc : c in Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (f.apply_nat_le_self c) (mod_cast Nat.digits_lt_base hm hc)
  calc
  f n = f ((Nat.ofDigits m L : Nat) : Rat) := by rw [Nat.ofDigits_digits m n]
    _ = f L'.sum := by simp [L', Nat.ofDigits_eq_sum_mapIdx]
    _ <= (L'.map f).sum := listSum_le f L'
    _ <= (L.mapIdx fun i _ => m * (f m) ^ i).sum := ?_
  simp only [List.mapIdx_eq_zipIdx_map, List.map_map, L']
  refine List.sum_le_sum fun ⟨a, i⟩ hia => ?_
  replace hia := List.mem_zipIdx hia
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_pow, AbsoluteValue.map_mul,
    AbsoluteValue.map_pow]
refine mul_le_mul_of_nonneg_right ?_ pow_nonneg (f.nonneg _) i
  simp only [zero_le, zero_add, true_and] at hia
  exact (hcoef (List.mem_iff_get.mpr ⟨⟨i, hia.1⟩, hia.2.symm⟩)).le

-- ## Step 1: if f is an AbsoluteValue and f n > 1 for some natural n, then f n > 1 for all n ≥ 2

/--
lemma `one_lt_of_not_bounded` / 引理 `one_lt_of_not_bounded`

English:
lemma one_lt_of_not_bounded
  given: (notbdd : ¬ forall n : Nat, f n <= 1) {n₀ : Nat} (hn₀ : 1 < n₀)
  statement: 1 < f n₀
  proof: by
  contrapose! notbdd with h
  intro n
  have h_ineq1 {m : Nat} (hm : 1 <= m) : f m <= n₀ * (logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀` -/
    set L := Nat.digits n₀ m
    calc
    f m <= (L.mapIdx fun i _ => n₀ * f n₀ ^ i).sum := apply_le_sum_digits m hn₀
    _ 

中文:
引理 one_lt_of_not_bounded
  条件: (notbdd : ¬ 对任意 n : 自然数, f n <= 1) {n₀ : 自然数} (hn₀ : 1 < n₀)
  结论: 1 < f n₀
  证明: by
  contrapose! notbdd with h
  intro n
  have h_ineq1 {m : Nat} (hm : 1 <= m) : f m <= n₀ * (logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀` -/
    set L := Nat.digits n₀ m
    calc
    f m <= (L.mapIdx fun i _ => n₀ * f n₀ ^ i).sum := apply_le_sum_digits m hn₀
    _ 

Depends on / 依赖: contrapose, h_ineq1, notbdd
-/
lemma one_lt_of_not_bounded (notbdd : ¬ forall n : Nat, f n <= 1) {n₀ : Nat} (hn₀ : 1 < n₀) : 1 < f n₀ := by
  contrapose! notbdd with h
  intro n
  have h_ineq1 {m : Nat} (hm : 1 <= m) : f m <= n₀ * (logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀` -/
    set L := Nat.digits n₀ m
    calc
    f m <= (L.mapIdx fun i _ => n₀ * f n₀ ^ i).sum := apply_le_sum_digits m hn₀
    _ <= (L.mapIdx fun _ _ => (n₀ : Real)).sum := by
      simp only [List.mapIdx_eq_zipIdx_map]
      refine List.sum_le_sum fun ⟨i, a⟩ _ => ?_
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) h)
    _ = n₀ * (Nat.log n₀ m + 1) := by
      rw [List.mapIdx_eq_zipIdx_map]; rw [List.eq_replicate_of_mem (a := (n₀ : Real)) (l := L.zipIdx.map _)]; rw [List.sum_replicate]; rw [List.length_map]; rw [List.length_zipIdx]; rw [nsmul_eq_mul]; rw [mul_comm]; rw [Nat.length_digits n₀ m hn₀ (ne_zero_of_lt hm)]; rw [Nat.cast_add_one]
      simp +contextual
    _ <= n₀ * (logb n₀ m + 1) := by
      gcongr
      exact natLog_le_logb ..
  -- For h_ineq2 we need to exclude the case n = 0.
  rcases eq_or_ne n 0 with rfl | h₀
  · simp
  have h_ineq2 (k : Nat) (hk : 0 < k) :
      f n <= (n₀ * (logb n₀ n + 1)) ^ (k : Real)⁻¹ * k ^ (k : Real)⁻¹ := by
    have : 0 <= logb n₀ n := logb_nonneg (mod_cast hn₀) (mod_cast one_le_iff_ne_zero.mpr h₀)
    calc
    f n = (f ↑(n ^ k)) ^ (k : Real)⁻¹ := by
      rw [Nat.cast_pow]; rw [map_pow]; rw [← rpow_natCast]; rw [rpow_rpow_inv (by positivity) (by positivity)]
    _ <= (n₀ * (logb n₀ ↑(n ^ k) + 1)) ^ (k : Real)⁻¹ := by
      gcongr
exact h_ineq1 one_le_pow₀ (one_le_iff_ne_zero.mpr h₀)
    _ = (n₀ * (k * logb n₀ n + 1)) ^ (k : Real)⁻¹ := by
      rw [Nat.cast_pow]; rw [logb_pow]
    _ <= (n₀ * (k * logb n₀ n + k)) ^ (k : Real)⁻¹ := by
      gcongr
      exact one_le_cast.mpr hk
    _ = (n₀ * (logb n₀ n + 1)) ^ (k : Real)⁻¹ * k ^ (k : Real)⁻¹ := by
      rw [← mul_rpow (by positivity) (by positivity)]; rw [mul_assoc]; rw [add_mul]; rw [one_mul]; rw [mul_comm _ (k : Real)]
-- For 0 < logb n₀ n below we also need to exclude n = 1.
  rcases eq_or_ne n 1 with rfl | h₁
  · simp
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ (eventually_atTop.mpr ⟨1, h_ineq2⟩)
  have : 0 < logb n₀ n := logb_pos (mod_cast hn₀) (by norm_cast; lia)
  simpa using (tendsto_const_rpow_inv (by positivity)).mul tendsto_nat_rpow_inv

-- ## Step 2: given m, n ≥ 2 and |m| = m^s, |n| = n^t for s, t > 0, we have t ≤ s

variable {m n : Nat} (hm : 1 < m) (hn : 1 < n) (notbdd : ¬ forall n : Nat, f n <= 1)

include hm notbdd in
/--
lemma `expr_pos` / 引理 `expr_pos`

English:
lemma expr_pos
  statement: 0 < m * f m / (f m - 1)
  proof: by
  apply div_pos (mul_pos (mod_cast hm.pos) (map_pos_of_ne_zero f (mod_cast hm.ne_zero)))
  linarith only [one_lt_of_not_bounded notbdd hm]

include hn hm notbdd in

中文:
引理 expr_pos
  结论: 0 < m * f m / (f m - 1)
  证明: by
  apply div_pos (mul_pos (mod_cast hm.pos) (map_pos_of_ne_zero f (mod_cast hm.ne_zero)))
  linarith only [one_lt_of_not_bounded notbdd hm]

include hn hm notbdd in
-/
private lemma expr_pos : 0 < m * f m / (f m - 1) := by
  apply div_pos (mul_pos (mod_cast hm.pos) (map_pos_of_ne_zero f (mod_cast hm.ne_zero)))
  linarith only [one_lt_of_not_bounded notbdd hm]

include hn hm notbdd in
/--
lemma `param_upperbound` / 引理 `param_upperbound`

English:
lemma param_upperbound
  given: {k : Nat} (hk : k != 0)
  proof: by
  have h_ineq1 {m n : Nat} (hm : 1 < m) (hn : 1 < n) :
      f n <= (m * f m / (f m - 1)) * f m ^ logb m n := by
    let d := Nat.log m n
    have hfm := one_lt_of_not_bounded notbdd hm
    calc
    f n <= ((Nat.digits m n).mapIdx fun i _ => m * f m ^ i).sum := apply_le_sum_digits n hm
    _ = m 

中文:
引理 param_upperbound
  条件: {k : 自然数} (hk : k != 0)
  证明: by
  have h_ineq1 {m n : Nat} (hm : 1 < m) (hn : 1 < n) :
      f n <= (m * f m / (f m - 1)) * f m ^ logb m n := by
    let d := Nat.log m n
    have hfm := one_lt_of_not_bounded notbdd hm
    calc
    f n <= ((Nat.digits m n).mapIdx fun i _ => m * f m ^ i).sum := apply_le_sum_digits n hm
    _ = m 
-/
private lemma param_upperbound {k : Nat} (hk : k != 0) :
    f n <= (m * f m / (f m - 1)) ^ (k : Real)⁻¹ * f m ^ logb m n := by
  have h_ineq1 {m n : Nat} (hm : 1 < m) (hn : 1 < n) :
      f n <= (m * f m / (f m - 1)) * f m ^ logb m n := by
    let d := Nat.log m n
    have hfm := one_lt_of_not_bounded notbdd hm
    calc
    f n <= ((Nat.digits m n).mapIdx fun i _ => m * f m ^ i).sum := apply_le_sum_digits n hm
    _ = m * ((Nat.digits m n).mapIdx fun i _ => f m ^ i).sum := list_mul_sum (m.digits n) (f m) m
    _ = m * ((f m ^ (d + 1) - 1) / (f m - 1)) := by
      rw [list_geom _ hfm.ne']; rw [← Nat.length_digits m n hm (ne_zero_of_lt hn)]
    _ <= m * ((f m ^ (d + 1)) / (f m - 1)) := by
      gcongr; linarith
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ <= ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      gcongr
      rw [← rpow_natCast]; rw [rpow_le_rpow_left_iff hfm]
      exact natLog_le_logb n m
  have he := expr_pos hm notbdd
  apply le_of_pow_le_pow_left₀ hk (by positivity)
  nth_rewrite 2 [← rpow_natCast]
  rw [mul_rpow (by positivity) (by positivity)]; rw [← rpow_mul he.le]; rw [← rpow_mul (apply_nonneg f ↑m)]; rw [inv_mul_cancel₀ (mod_cast hk)]; rw [rpow_one]; rw [mul_comm (logb ..)]
  calc
    (f n) ^ k = f ↑(n ^ k) := by simp
    _ <= (m * f m / (f m - 1)) * f m ^ logb m ↑(n ^ k) := h_ineq1 hm (Nat.one_lt_pow hk hn)
    _ = (m * f m / (f m - 1)) * f m ^ (k * logb m n) := by rw [Nat.cast_pow, logb_pow]

include hm hn notbdd in
/--
lemma `le_pow_log` / 引理 `le_pow_log`

English:
lemma le_pow_log
  statement: f n <= f m ^ logb m n
  proof: by
  have : Tendsto (fun k : Nat => (m * f m / (f m - 1)) ^ (k : Real)⁻¹ * f m ^ logb m n)
      atTop (𝓝 (f m ^ logb m n)) := by
    nth_rw 2 [← one_mul (f ↑m ^ logb ↑m ↑n)]
    exact (tendsto_const_rpow_inv (expr_pos hm notbdd)).mul_const _
exact le_of_tendsto_of_tendsto (tendsto_const_nhds (x := 

中文:
引理 le_pow_log
  结论: f n <= f m ^ logb m n
  证明: by
  have : Tendsto (fun k : Nat => (m * f m / (f m - 1)) ^ (k : Real)⁻¹ * f m ^ logb m n)
      atTop (𝓝 (f m ^ logb m n)) := by
    nth_rw 2 [← one_mul (f ↑m ^ logb ↑m ↑n)]
    exact (tendsto_const_rpow_inv (expr_pos hm notbdd)).mul_const _
exact le_of_tendsto_of_tendsto (tendsto_const_nhds (x := 

Depends on / 依赖: Tendsto, eventually_atTop, eventually_atTop.mpr, expr_pos, le_of_tendsto_of_tendsto, mul_const, ne_zero_of_lt, notbdd, nth_rw, one_mul, param_upperbound, tendsto_const_nhds, tendsto_const_rpow_inv
-/
lemma le_pow_log : f n <= f m ^ logb m n := by
  have : Tendsto (fun k : Nat => (m * f m / (f m - 1)) ^ (k : Real)⁻¹ * f m ^ logb m n)
      atTop (𝓝 (f m ^ logb m n)) := by
    nth_rw 2 [← one_mul (f ↑m ^ logb ↑m ↑n)]
    exact (tendsto_const_rpow_inv (expr_pos hm notbdd)).mul_const _
exact le_of_tendsto_of_tendsto (tendsto_const_nhds (x := f ↑n)) this
    eventually_atTop.mpr ⟨2, fun b hb => param_upperbound hm hn notbdd (ne_zero_of_lt hb)⟩

include hm hn notbdd in
/--
lemma `le_of_eq_pow` / 引理 `le_of_eq_pow`

English:
lemma le_of_eq_pow
  given: {s t : Real} (hfm : f m = m ^ s) (hfn : f n = n ^ t)
  statement: t <= s
  proof: by
  rw [← rpow_le_rpow_left_iff (x := n) (mod_cast hn)]; rw [← hfn]
apply le_trans le_pow_log hm hn notbdd
  rw [hfm]; rw [← rpow_mul (Nat.cast_nonneg m)]; rw [mul_comm]; rw [rpow_mul (Nat.cast_nonneg m)]; rw [rpow_logb (mod_cast zero_lt_of_lt hm) (mod_cast hm.ne') (mod_cast zero_lt_of_lt hn)]

inc

中文:
引理 le_of_eq_pow
  条件: {s t : 实数} (hfm : f m = m ^ s) (hfn : f n = n ^ t)
  结论: t <= s
  证明: by
  rw [← rpow_le_rpow_left_iff (x := n) (mod_cast hn)]; rw [← hfn]
apply le_trans le_pow_log hm hn notbdd
  rw [hfm]; rw [← rpow_mul (Nat.cast_nonneg m)]; rw [mul_comm]; rw [rpow_mul (Nat.cast_nonneg m)]; rw [rpow_logb (mod_cast zero_lt_of_lt hm) (mod_cast hm.ne') (mod_cast zero_lt_of_lt hn)]

inc
-/
private lemma le_of_eq_pow {s t : Real} (hfm : f m = m ^ s) (hfn : f n = n ^ t) : t <= s := by
  rw [← rpow_le_rpow_left_iff (x := n) (mod_cast hn)]; rw [← hfn]
apply le_trans le_pow_log hm hn notbdd
  rw [hfm]; rw [← rpow_mul (Nat.cast_nonneg m)]; rw [mul_comm]; rw [rpow_mul (Nat.cast_nonneg m)]; rw [rpow_logb (mod_cast zero_lt_of_lt hm) (mod_cast hm.ne') (mod_cast zero_lt_of_lt hn)]

include hm hn notbdd in
/--
lemma `eq_of_eq_pow` / 引理 `eq_of_eq_pow`

English:
lemma eq_of_eq_pow
  given: {s t : Real} (hfm : f m = m ^ s) (hfn : f n = n ^ t)
  statement: s = t
  proof: le_antisymm (le_of_eq_pow hn hm notbdd hfn hfm) (le_of_eq_pow hm hn notbdd hfm hfn)

中文:
引理 eq_of_eq_pow
  条件: {s t : 实数} (hfm : f m = m ^ s) (hfn : f n = n ^ t)
  结论: s = t
  证明: le_antisymm (le_of_eq_pow hn hm notbdd hfn hfm) (le_of_eq_pow hm hn notbdd hfm hfn)
-/
private lemma eq_of_eq_pow {s t : Real} (hfm : f m = m ^ s) (hfn : f n = n ^ t) : s = t :=
  le_antisymm (le_of_eq_pow hn hm notbdd hfn hfm) (le_of_eq_pow hm hn notbdd hfm hfn)

-- ## Archimedean case: end goal

include notbdd in
/--
theorem `equiv_real_of_unbounded` / 定理 `equiv_real_of_unbounded`

English:
theorem equiv_real_of_unbounded
  statement: f.IsEquiv real
  proof: by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have hfm1 : 1 < f m := lt_of_not_ge hm
  have oneltm : 1 < m := by
    contrapose! hm
    rcases le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  rw [← exists_nat_rpow_iff_isEquiv]
  set s := logb m (f m) with hs
  have h

中文:
定理 equiv_real_of_unbounded
  结论: f.IsEquiv real
  证明: by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have hfm1 : 1 < f m := lt_of_not_ge hm
  have oneltm : 1 < m := by
    contrapose! hm
    rcases le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  rw [← exists_nat_rpow_iff_isEquiv]
  set s := logb m (f m) with hs
  have h

Depends on / 依赖: Classical, Classical.exists_not_of_not_forall, abs_c, contrapose, exists_nat_rpow_iff_isEquiv, exists_not_of_not_forall, hs0.ne, inv_pos, inv_pos.mpr, le_one_iff_eq_zero_or_eq_one, le_one_iff_eq_zero_or_eq_one.mp, logb_pos, lt_of_not_ge, lt_trichotomy, mod_cast, notbdd, oneltm, real_eq_abs
-/
theorem equiv_real_of_unbounded : f.IsEquiv real := by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have hfm1 : 1 < f m := lt_of_not_ge hm
  have oneltm : 1 < m := by
    contrapose! hm
    rcases le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  rw [← exists_nat_rpow_iff_isEquiv]
  set s := logb m (f m) with hs
  have hs0 : 0 < s := hs ▸ logb_pos (mod_cast oneltm) hfm1
  refine ⟨s⁻¹, inv_pos.mpr hs0, fun n => ?_⟩
  rcases lt_trichotomy n 1 with h | rfl | h
  · obtain rfl : n = 0 := by lia
    simp [hs0.ne']
  · simp
  · simp only [real_eq_abs, abs_cast, Rat.cast_natCast]
    rw [rpow_inv_eq (by positivity) (by positivity) hs0.ne']
    have hfm : f m = m ^ s := by
      rw [rpow_logb (by positivity) (by norm_cast; omega) (zero_lt_one.trans hfm1)]
    have hfn : f n = n ^ logb n (f n) := by
      rw [rpow_logb (by positivity) (by norm_cast; omega)
        (map_pos_of_ne_zero f (by exact_mod_cast ne_zero_of_lt h))]
    rw [hfn]; rw [← eq_of_eq_pow oneltm h notbdd hfm hfn]

end Archimedean

/-!
### The main result
-/

/--
theorem `equiv_real_or_padic` / 定理 `equiv_real_or_padic`

English:
theorem equiv_real_or_padic
  given: (f : AbsoluteValue Rat Real) (hf_nontriv : f.IsNontrivial)
  proof: by
  by_cases bdd : forall n : Nat, f n <= 1
· exact .inr equiv_padic_of_bounded hf_nontriv bdd
· exact .inl equiv_real_of_unbounded bdd

中文:
定理 equiv_real_or_padic
  条件: (f : AbsoluteValue Rat 实数) (hf_nontriv : f.IsNontrivial)
  证明: by
  by_cases bdd : forall n : Nat, f n <= 1
· exact .inr equiv_padic_of_bounded hf_nontriv bdd
· exact .inl equiv_real_of_unbounded bdd

Depends on / 依赖: equiv_padic_of_bounded, equiv_real_of_unbounded, hf_nontriv
-/
theorem equiv_real_or_padic (f : AbsoluteValue Rat Real) (hf_nontriv : f.IsNontrivial) :
    f ≈ real ∨ exists! p, exists (_ : Fact p.Prime), f ≈ (padic p) := by
  by_cases bdd : forall n : Nat, f n <= 1
· exact .inr equiv_padic_of_bounded hf_nontriv bdd
· exact .inl equiv_real_of_unbounded bdd

/--
lemma `not_real_isEquiv_padic` / 引理 `not_real_isEquiv_padic`

English:
lemma not_real_isEquiv_padic
  given: (p : Nat) [Fact p.Prime]
  statement: ¬ real.IsEquiv (padic p)
  proof: by
  rw [isEquiv_iff_exists_rpow_eq]
  rintro ⟨c, hc₀, hc⟩
  apply_fun (· 2) at hc
  simp only [real_eq_abs, abs_ofNat, cast_ofNat] at hc
  exact ((padic_le_one p 2).trans_lt <| one_lt_rpow one_lt_two hc₀).ne' hc

中文:
引理 not_real_isEquiv_padic
  条件: (p : 自然数) [Fact p.Prime]
  结论: ¬ real.IsEquiv (padic p)
  证明: by
  rw [isEquiv_iff_exists_rpow_eq]
  rintro ⟨c, hc₀, hc⟩
  apply_fun (· 2) at hc
  simp only [real_eq_abs, abs_ofNat, cast_ofNat] at hc
  exact ((padic_le_one p 2).trans_lt <| one_lt_rpow one_lt_two hc₀).ne' hc

Depends on / 依赖: abs_ofNat, apply_fun, cast_ofNat, isEquiv_iff_exists_rpow_eq, one_lt_rpow, one_lt_two, padic_le_one, real_eq_abs, trans_lt
-/
lemma not_real_isEquiv_padic (p : Nat) [Fact p.Prime] : ¬ real.IsEquiv (padic p) := by
  rw [isEquiv_iff_exists_rpow_eq]
  rintro ⟨c, hc₀, hc⟩
  apply_fun (· 2) at hc
  simp only [real_eq_abs, abs_ofNat, cast_ofNat] at hc
  exact ((padic_le_one p 2).trans_lt <| one_lt_rpow one_lt_two hc₀).ne' hc

end Rat.AbsoluteValue
