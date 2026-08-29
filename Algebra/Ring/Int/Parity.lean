/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Group.Int.Even

/-!
# Basic parity lemmas for the ring `ℤ`

See note [foundational algebra order theory].
-/

public section

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/-! #### Parity -/

variable {m n : Int}

@[grind =]
/--
lemma `odd_iff` / 引理 `odd_iff`

English:
lemma odd_iff
  statement: Odd n ↔ n % 2 = 1 where
  proof: fun ⟨m, hm⟩ => by grind
  mpr h := ⟨n / 2, by grind⟩

中文:
引理 odd_iff
  结论: Odd n ↔ n % 2 = 1 where
  证明: fun ⟨m, hm⟩ => by grind
  mpr h := ⟨n / 2, by grind⟩
-/
lemma odd_iff : Odd n ↔ n % 2 = 1 where
  mp := fun ⟨m, hm⟩ => by grind
  mpr h := ⟨n / 2, by grind⟩

/--
lemma `not_odd_iff` / 引理 `not_odd_iff`

English:
lemma not_odd_iff
  statement: ¬Odd n ↔ n % 2 = 0
  proof: by grind

中文:
引理 not_odd_iff
  结论: ¬Odd n ↔ n % 2 = 0
  证明: by grind

Depends on / 依赖: IsLocallyNoetherian, Scheme
-/
lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind

/--
lemma `not_odd_zero` / 引理 `not_odd_zero`

English:
lemma not_odd_zero
  statement: ¬Odd (0 : Int)
  proof: by grind

中文:
引理 not_odd_zero
  结论: ¬Odd (0 : 整数)
  证明: by grind

Depends on / 依赖: IsLocallyNoetherian, IsLocallyNoetherian.quasiSeparatedSpace, quasiSeparatedSpace
-/
@[simp] lemma not_odd_zero : ¬Odd (0 : Int) := by grind

/--
lemma `not_odd_iff_even` / 引理 `not_odd_iff_even`

English:
lemma not_odd_iff_even
  statement: ¬Odd n ↔ Even n
  proof: by grind

中文:
引理 not_odd_iff_even
  结论: ¬Odd n ↔ Even n
  证明: by grind
-/
@[simp, grind =] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by grind
/--
lemma `not_even_iff_odd` / 引理 `not_even_iff_odd`

English:
lemma not_even_iff_odd
  statement: ¬Even n ↔ Odd n
  proof: by grind

中文:
引理 not_even_iff_odd
  结论: ¬Even n ↔ Odd n
  证明: by grind

Depends on / 依赖: Limits, Limits.pullback.snd, LocallyOfFiniteType, LocallyOfFiniteType.isLocallyNoetherian, isLocallyNoetherian, pullback
-/
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by grind

/--
lemma `even_or_odd` / 引理 `even_or_odd`

English:
lemma even_or_odd
  given: (n : Int)
  statement: Even n ∨ Odd n
  proof: by grind

中文:
引理 even_or_odd
  条件: (n : 整数)
  结论: Even n ∨ Odd n
  证明: by grind

Depends on / 依赖: Limits, Limits.pullback.fst, LocallyOfFiniteType, LocallyOfFiniteType.isLocallyNoetherian, isLocallyNoetherian, pullback
-/
lemma even_or_odd (n : Int) : Even n ∨ Odd n := by grind

/--
lemma `even_or_odd'` / 引理 `even_or_odd'`

English:
lemma even_or_odd'
  given: (n : Int)
  statement: exists k, n = 2 * k ∨ n = 2 * k + 1
  proof: by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n

中文:
引理 even_or_odd'
  条件: (n : 整数)
  结论: 存在 k, n = 2 * k ∨ n = 2 * k + 1
  证明: by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n

Depends on / 依赖: Scheme, even_or_odd, exists_or, two_mul
-/
lemma even_or_odd' (n : Int) : exists k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n

/--
lemma `even_xor_odd` / 引理 `even_xor_odd`

English:
lemma even_xor_odd
  given: (n : Int)
  statement: Xor (Even n) (Odd n)
  proof: by
  grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd := even_xor_odd

中文:
引理 even_xor_odd
  条件: (n : 整数)
  结论: Xor (Even n) (Odd n)
  证明: by
  grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd := even_xor_odd
-/
lemma even_xor_odd (n : Int) : Xor (Even n) (Odd n) := by
  grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd := even_xor_odd

/--
lemma `even_xor_odd'` / 引理 `even_xor_odd'`

English:
lemma even_xor_odd'
  given: (n : Int)
  statement: exists k, Xor (n = 2 * k) (n = 2 * k + 1)
  proof: by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
  · use k
    grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd' := even_xor_odd'

中文:
引理 even_xor_odd'
  条件: (n : 整数)
  结论: 存在 k, Xor (n = 2 * k) (n = 2 * k + 1)
  证明: by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
  · use k
    grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd' := even_xor_odd'

Depends on / 依赖: even_or_odd
-/
lemma even_xor_odd' (n : Int) : exists k, Xor (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
  · use k
    grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd' := even_xor_odd'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (Odd : Int -> Prop)
  body: fun _ => decidable_of_iff _ not_even_iff_odd

中文:
实例 :
  签名: DecidablePred (Odd : 整数 -> 命题)
  定义体: fun _ => decidable_of_iff _ not_even_iff_odd

Depends on / 依赖: decidable_of_iff, not_even_iff_odd
-/
instance : DecidablePred (Odd : Int -> Prop) := fun _ => decidable_of_iff _ not_even_iff_odd

/--
lemma `even_add'` / 引理 `even_add'`

English:
lemma even_add'
  statement: Even (m + n) ↔ (Odd m ↔ Odd n)
  proof: by grind

中文:
引理 even_add'
  结论: Even (m + n) ↔ (Odd m ↔ Odd n)
  证明: by grind

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherianSpace, noetherianSpace
-/
lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind

/--
lemma `not_even_two_mul_add_one` / 引理 `not_even_two_mul_add_one`

English:
lemma not_even_two_mul_add_one
  given: (n : Int)
  statement: ¬ Even (2 * n + 1)
  proof: by grind

中文:
引理 not_even_two_mul_add_one
  条件: (n : 整数)
  结论: ¬ Even (2 * n + 1)
  证明: by grind

Depends on / 依赖: Scheme, quasiCompact_of_noetherianSpace_source
-/
lemma not_even_two_mul_add_one (n : Int) : ¬ Even (2 * n + 1) := by grind

/--
lemma `even_sub'` / 引理 `even_sub'`

English:
lemma even_sub'
  statement: Even (m - n) ↔ (Odd m ↔ Odd n)
  proof: by grind

中文:
引理 even_sub'
  结论: Even (m - n) ↔ (Odd m ↔ Odd n)
  证明: by grind

Depends on / 依赖: CommRingCat, CommRingCat.of, IsNoetherianRing, infer_instance
-/
lemma even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind

/--
lemma `odd_mul` / 引理 `odd_mul`

English:
lemma odd_mul
  statement: Odd (m * n) ↔ Odd m ∧ Odd n
  proof: by simp [← not_even_iff_odd, not_or, parity_simps]

中文:
引理 odd_mul
  结论: Odd (m * n) ↔ Odd m ∧ Odd n
  证明: by simp [← not_even_iff_odd, not_or, parity_simps]

Depends on / 依赖: not_even_iff_odd, not_or, parity_simps
-/
lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [← not_even_iff_odd, not_or, parity_simps]

/--
lemma `Odd.of_mul_left` / 引理 `Odd.of_mul_left`

English:
lemma Odd.of_mul_left
  given: (h : Odd (m * n))
  statement: Odd m
  proof: (odd_mul.mp h).1

中文:
引理 Odd.of_mul_left
  条件: (h : Odd (m * n))
  结论: Odd m
  证明: (odd_mul.mp h).1
-/
lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m := (odd_mul.mp h).1

/--
lemma `Odd.of_mul_right` / 引理 `Odd.of_mul_right`

English:
lemma Odd.of_mul_right
  given: (h : Odd (m * n))
  statement: Odd n
  proof: (odd_mul.mp h).2

中文:
引理 Odd.of_mul_right
  条件: (h : Odd (m * n))
  结论: Odd n
  证明: (odd_mul.mp h).2
-/
lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n := (odd_mul.mp h).2

/--
lemma `odd_pow` / 引理 `odd_pow`

English:
lemma odd_pow
  given: {n : Nat}
  statement: Odd (m ^ n) ↔ Odd m ∨ n = 0
  proof: by grind

中文:
引理 odd_pow
  条件: {n : 自然数}
  结论: Odd (m ^ n) ↔ Odd m ∨ n = 0
  证明: by grind
-/
@[parity_simps] lemma odd_pow {n : Nat} : Odd (m ^ n) ↔ Odd m ∨ n = 0 := by grind

/--
lemma `odd_pow'` / 引理 `odd_pow'`

English:
lemma odd_pow'
  given: {n : Nat} (h : n != 0)
  statement: Odd (m ^ n) ↔ Odd m
  proof: by grind

中文:
引理 odd_pow'
  条件: {n : 自然数} (h : n != 0)
  结论: Odd (m ^ n) ↔ Odd m
  证明: by grind
-/
lemma odd_pow' {n : Nat} (h : n != 0) : Odd (m ^ n) ↔ Odd m := by grind

/--
lemma `odd_add` / 引理 `odd_add`

English:
lemma odd_add
  statement: Odd (m + n) ↔ (Odd m ↔ Even n)
  proof: by grind

中文:
引理 odd_add
  结论: Odd (m + n) ↔ (Odd m ↔ Even n)
  证明: by grind
-/
@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by grind

/--
lemma `odd_add'` / 引理 `odd_add'`

English:
lemma odd_add'
  statement: Odd (m + n) ↔ (Odd n ↔ Even m)
  proof: by grind

中文:
引理 odd_add'
  结论: Odd (m + n) ↔ (Odd n ↔ Even m)
  证明: by grind
-/
lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind

/--
lemma `ne_of_odd_add` / 引理 `ne_of_odd_add`

English:
lemma ne_of_odd_add
  given: (h : Odd (m + n))
  statement: m != n
  proof: by grind

中文:
引理 ne_of_odd_add
  条件: (h : Odd (m + n))
  结论: m != n
  证明: by grind
-/
lemma ne_of_odd_add (h : Odd (m + n)) : m != n := by grind

/--
lemma `odd_sub` / 引理 `odd_sub`

English:
lemma odd_sub
  statement: Odd (m - n) ↔ (Odd m ↔ Even n)
  proof: by grind

中文:
引理 odd_sub
  结论: Odd (m - n) ↔ (Odd m ↔ Even n)
  证明: by grind
-/
@[parity_simps] lemma odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by grind

/--
lemma `odd_sub'` / 引理 `odd_sub'`

English:
lemma odd_sub'
  statement: Odd (m - n) ↔ (Odd n ↔ Even m)
  proof: by grind

中文:
引理 odd_sub'
  结论: Odd (m - n) ↔ (Odd n ↔ Even m)
  证明: by grind
-/
lemma odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind

/--
lemma `even_mul_succ_self` / 引理 `even_mul_succ_self`

English:
lemma even_mul_succ_self
  given: (n : Int)
  statement: Even (n * (n + 1))
  proof: by grind

中文:
引理 even_mul_succ_self
  条件: (n : 整数)
  结论: Even (n * (n + 1))
  证明: by grind
-/
lemma even_mul_succ_self (n : Int) : Even (n * (n + 1)) := by grind

/--
lemma `even_mul_pred_self` / 引理 `even_mul_pred_self`

English:
lemma even_mul_pred_self
  given: (n : Int)
  statement: Even (n * (n - 1))
  proof: by grind

中文:
引理 even_mul_pred_self
  条件: (n : 整数)
  结论: Even (n * (n - 1))
  证明: by grind
-/
lemma even_mul_pred_self (n : Int) : Even (n * (n - 1)) := by grind

/--
lemma `odd_coe_nat` / 引理 `odd_coe_nat`

English:
lemma odd_coe_nat
  given: (n : Nat)
  statement: Odd (n : Int) ↔ Odd n
  proof: by grind

中文:
引理 odd_coe_nat
  条件: (n : 自然数)
  结论: Odd (n : 整数) ↔ Odd n
  证明: by grind
-/
@[simp, norm_cast] lemma odd_coe_nat (n : Nat) : Odd (n : Int) ↔ Odd n := by grind

/--
lemma `natAbs_even` / 引理 `natAbs_even`

English:
lemma natAbs_even
  statement: Even n.natAbs ↔ Even n
  proof: by grind

@[simp]

中文:
引理 natAbs_even
  结论: Even n.natAbs ↔ Even n
  证明: by grind

@[simp]
-/
@[simp] lemma natAbs_even : Even n.natAbs ↔ Even n := by grind

@[simp]
/--
lemma `natAbs_odd` / 引理 `natAbs_odd`

English:
lemma natAbs_odd
  statement: Odd n.natAbs ↔ Odd n
  proof: by grind

protected alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
protected alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd

中文:
引理 natAbs_odd
  结论: Odd n.natAbs ↔ Odd n
  证明: by grind

protected alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
protected alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd
-/
lemma natAbs_odd : Odd n.natAbs ↔ Odd n := by grind

protected alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
protected alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd

/--
lemma `four_dvd_add_or_sub_of_odd` / 引理 `four_dvd_add_or_sub_of_odd`

English:
lemma four_dvd_add_or_sub_of_odd
  given: {a b : Int} (ha : Odd a) (hb : Odd b)
  proof: by grind

中文:
引理 four_dvd_add_or_sub_of_odd
  条件: {a b : 整数} (ha : Odd a) (hb : Odd b)
  证明: by grind
-/
lemma four_dvd_add_or_sub_of_odd {a b : Int} (ha : Odd a) (hb : Odd b) :
    4 ∣ a + b ∨ 4 ∣ a - b := by grind

/--
lemma `two_dvd_mul_add_one` / 引理 `two_dvd_mul_add_one`

English:
lemma two_dvd_mul_add_one
  given: (k : Int)
  statement: 2 ∣ k * (k + 1)
  proof: even_iff_two_dvd.mp (even_mul_succ_self k)

中文:
引理 two_dvd_mul_add_one
  条件: (k : 整数)
  结论: 2 ∣ k * (k + 1)
  证明: even_iff_two_dvd.mp (even_mul_succ_self k)

Depends on / 依赖: even_iff_two_dvd, even_iff_two_dvd.mp, even_mul_succ_self
-/
lemma two_dvd_mul_add_one (k : Int) : 2 ∣ k * (k + 1) :=
  even_iff_two_dvd.mp (even_mul_succ_self k)

/--
lemma `two_mul_ediv_two_add_one_of_odd` / 引理 `two_mul_ediv_two_add_one_of_odd`

English:
lemma two_mul_ediv_two_add_one_of_odd
  statement: Odd n -> 2 * (n / 2) + 1 = n
  proof: by grind

中文:
引理 two_mul_ediv_two_add_one_of_odd
  结论: Odd n -> 2 * (n / 2) + 1 = n
  证明: by grind
-/
lemma two_mul_ediv_two_add_one_of_odd : Odd n -> 2 * (n / 2) + 1 = n := by grind

/--
lemma `ediv_two_mul_two_add_one_of_odd` / 引理 `ediv_two_mul_two_add_one_of_odd`

English:
lemma ediv_two_mul_two_add_one_of_odd
  statement: Odd n -> n / 2 * 2 + 1 = n
  proof: by grind

中文:
引理 ediv_two_mul_two_add_one_of_odd
  结论: Odd n -> n / 2 * 2 + 1 = n
  证明: by grind
-/
lemma ediv_two_mul_two_add_one_of_odd : Odd n -> n / 2 * 2 + 1 = n := by grind

/--
lemma `add_one_ediv_two_mul_two_of_odd` / 引理 `add_one_ediv_two_mul_two_of_odd`

English:
lemma add_one_ediv_two_mul_two_of_odd
  statement: Odd n -> 1 + n / 2 * 2 = n
  proof: by grind

中文:
引理 add_one_ediv_two_mul_two_of_odd
  结论: Odd n -> 1 + n / 2 * 2 = n
  证明: by grind
-/
lemma add_one_ediv_two_mul_two_of_odd : Odd n -> 1 + n / 2 * 2 = n := by grind

/--
lemma `two_mul_ediv_two_of_odd` / 引理 `two_mul_ediv_two_of_odd`

English:
lemma two_mul_ediv_two_of_odd
  given: (h : Odd n)
  statement: 2 * (n / 2) = n - 1
  proof: by grind

@[simp]

中文:
引理 two_mul_ediv_two_of_odd
  条件: (h : Odd n)
  结论: 2 * (n / 2) = n - 1
  证明: by grind

@[simp]
-/
lemma two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 := by grind

@[simp]
/--
theorem `even_sign_iff` / 定理 `even_sign_iff`

English:
theorem even_sign_iff
  given: {z : Int}
  statement: Even z.sign ↔ z = 0
  proof: by grind

@[simp]

中文:
定理 even_sign_iff
  条件: {z : 整数}
  结论: Even z.sign ↔ z = 0
  证明: by grind

@[simp]
-/
theorem even_sign_iff {z : Int} : Even z.sign ↔ z = 0 := by grind

@[simp]
/--
theorem `odd_sign_iff` / 定理 `odd_sign_iff`

English:
theorem odd_sign_iff
  given: {z : Int}
  statement: Odd z.sign ↔ z != 0
  proof: by grind

@[norm_cast, simp]

中文:
定理 odd_sign_iff
  条件: {z : 整数}
  结论: Odd z.sign ↔ z != 0
  证明: by grind

@[norm_cast, simp]
-/
theorem odd_sign_iff {z : Int} : Odd z.sign ↔ z != 0 := by grind

@[norm_cast, simp]
/--
theorem `isSquare_natCast_iff` / 定理 `isSquare_natCast_iff`

English:
theorem isSquare_natCast_iff
  given: {n : Nat}
  statement: IsSquare (n : Int) ↔ IsSquare n
  proof: by
  constructor <;> rintro ⟨x, h⟩
  · exact ⟨x.natAbs, (natAbs_mul_natAbs_eq h.symm).symm⟩
  · exact ⟨x, mod_cast h⟩

@[simp]

中文:
定理 isSquare_natCast_iff
  条件: {n : 自然数}
  结论: IsSquare (n : 整数) ↔ IsSquare n
  证明: by
  constructor <;> rintro ⟨x, h⟩
  · exact ⟨x.natAbs, (natAbs_mul_natAbs_eq h.symm).symm⟩
  · exact ⟨x, mod_cast h⟩

@[simp]

Depends on / 依赖: h.symm, mod_cast, natAbs, natAbs_mul_natAbs_eq, x.natAbs
-/
theorem isSquare_natCast_iff {n : Nat} : IsSquare (n : Int) ↔ IsSquare n := by
  constructor <;> rintro ⟨x, h⟩
  · exact ⟨x.natAbs, (natAbs_mul_natAbs_eq h.symm).symm⟩
  · exact ⟨x, mod_cast h⟩

@[simp]
/--
theorem `isSquare_ofNat_iff` / 定理 `isSquare_ofNat_iff`

English:
theorem isSquare_ofNat_iff
  given: {n : Nat}
  proof: isSquare_natCast_iff

中文:
定理 isSquare_of自然数_iff
  条件: {n : 自然数}
  证明: isSquare_natCast_iff

Depends on / 依赖: isSquare_natCast_iff
-/
theorem isSquare_ofNat_iff {n : Nat} :
    IsSquare (ofNat(n) : Int) ↔ IsSquare (ofNat(n) : Nat) :=
  isSquare_natCast_iff

-- These next two don't make good `norm_cast` lemmas.
/--
theorem `natCast_pow_pred` / 定理 `natCast_pow_pred`

English:
theorem natCast_pow_pred
  given: (b p : Nat) (w : 0 < b)
  statement: ((b ^ p - 1 : Nat) : Int) = (b : Int) ^ p - 1
  proof: by
  have : 1 <= b ^ p := Nat.one_le_pow p b w
  norm_cast

中文:
定理 natCast_pow_pred
  条件: (b p : 自然数) (w : 0 < b)
  结论: ((b ^ p - 1 : 自然数) : 整数) = (b : 整数) ^ p - 1
  证明: by
  have : 1 <= b ^ p := Nat.one_le_pow p b w
  norm_cast

Depends on / 依赖: Nat.one_le_pow, one_le_pow
-/
theorem natCast_pow_pred (b p : Nat) (w : 0 < b) : ((b ^ p - 1 : Nat) : Int) = (b : Int) ^ p - 1 := by
  have : 1 <= b ^ p := Nat.one_le_pow p b w
  norm_cast

/--
theorem `coe_nat_two_pow_pred` / 定理 `coe_nat_two_pow_pred`

English:
theorem coe_nat_two_pow_pred
  given: (p : Nat)
  statement: ((2 ^ p - 1 : Nat) : Int) = (2 ^ p - 1 : Int)
  proof: natCast_pow_pred 2 p (by decide)

中文:
定理 coe_nat_two_pow_pred
  条件: (p : 自然数)
  结论: ((2 ^ p - 1 : 自然数) : 整数) = (2 ^ p - 1 : 整数)
  证明: natCast_pow_pred 2 p (by decide)

Depends on / 依赖: natCast_pow_pred
-/
theorem coe_nat_two_pow_pred (p : Nat) : ((2 ^ p - 1 : Nat) : Int) = (2 ^ p - 1 : Int) :=
  natCast_pow_pred 2 p (by decide)

end Int

section DivisionMonoid

variable {α : Type*} [DivisionMonoid α] [HasDistribNeg α] {n : Int}

/--
theorem `Odd.neg_zpow` / 定理 `Odd.neg_zpow`

English:
theorem Odd.neg_zpow
  given: (h : Odd n) (a : α)
  statement: (-a) ^ n = -a ^ n
  proof: by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast]
    norm_cast
    simp [pow_add]
  | negSucc k =>
    simp_rw [Int.negSucc_eq, show 2 * -(↑k + 1) + (1 : Int) = - (1 + k*2) by grind, _root_.zpow_neg]
    norm_cast
    simp [pow_add]

中文:
定理 Odd.neg_zpow
  条件: (h : Odd n) (a : α)
  结论: (-a) ^ n = -a ^ n
  证明: by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast]
    norm_cast
    simp [pow_add]
  | negSucc k =>
    simp_rw [Int.negSucc_eq, show 2 * -(↑k + 1) + (1 : Int) = - (1 + k*2) by grind, _root_.zpow_neg]
    norm_cast
    simp [pow_add]

Depends on / 依赖: Int.negSucc_eq, Int.ofNat_eq_natCast, _root_, _root_.zpow_neg, negSucc, negSucc_eq, ofNat_eq_natCast, pow_add, simp_rw, zpow_neg
-/
theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast]
    norm_cast
    simp [pow_add]
  | negSucc k =>
    simp_rw [Int.negSucc_eq, show 2 * -(↑k + 1) + (1 : Int) = - (1 + k*2) by grind, _root_.zpow_neg]
    norm_cast
    simp [pow_add]

/--
theorem `Odd.neg_one_zpow` / 定理 `Odd.neg_one_zpow`

English:
theorem Odd.neg_one_zpow
  given: (h : Odd n)
  statement: (-1 : α) ^ n = -1
  proof: by rw [h.neg_zpow, one_zpow]

中文:
定理 Odd.neg_one_zpow
  条件: (h : Odd n)
  结论: (-1 : α) ^ n = -1
  证明: by rw [h.neg_zpow, one_zpow]

Depends on / 依赖: h.neg_zpow, neg_zpow, one_zpow
-/
theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end DivisionMonoid
