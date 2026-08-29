/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic

/-!
# Facts about `ℤ` as an (unbundled) ordered group

See note [foundational algebra order theory].

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton Ring

open Function Nat

namespace Int

/--
theorem `natCast_strictMono` / 定理 `natCast_strictMono`

English:
theorem natCast_strictMono
  statement: StrictMono (· : Nat -> Int)
  proof: fun _ _ => Int.ofNat_lt.2

中文:
定理 natCast_strictMono
  结论: StrictMono (· : 自然数 -> 整数)
  证明: fun _ _ => Int.ofNat_lt.2

Depends on / 依赖: Int.ofNat_lt, ofNat_lt
-/
theorem natCast_strictMono : StrictMono (· : Nat -> Int) := fun _ _ => Int.ofNat_lt.2


/--
theorem `abs_eq_natAbs` / 定理 `abs_eq_natAbs`

English:
theorem abs_eq_natAbs
  statement: forall a : Int, |a| = natAbs a

中文:
定理 abs_eq_natAbs
  结论: 对任意 a : 整数, |a| = natAbs a
-/
theorem abs_eq_natAbs : forall a : Int, |a| = natAbs a
| (n : Nat) => abs_of_nonneg natCast_nonneg _
| -[_+1] => abs_of_nonpos le_of_lt negSucc_lt_zero _

/--
lemma `natCast_natAbs` / 引理 `natCast_natAbs`

English:
lemma natCast_natAbs
  given: (n : Int)
  statement: (n.natAbs : Int) = |n|
  proof: n.abs_eq_natAbs.symm

中文:
引理 natCast_natAbs
  条件: (n : 整数)
  结论: (n.natAbs : 整数) = |n|
  证明: n.abs_eq_natAbs.symm
-/
@[norm_cast] lemma natCast_natAbs (n : Int) : (n.natAbs : Int) = |n| := n.abs_eq_natAbs.symm

/--
theorem `natAbs_abs` / 定理 `natAbs_abs`

English:
theorem natAbs_abs
  given: (a : Int)
  statement: natAbs |a| = natAbs a
  proof: by grind

中文:
定理 natAbs_abs
  条件: (a : 整数)
  结论: natAbs |a| = natAbs a
  证明: by grind
-/
theorem natAbs_abs (a : Int) : natAbs |a| = natAbs a := by grind

/--
theorem `sign_mul_abs` / 定理 `sign_mul_abs`

English:
theorem sign_mul_abs
  given: (a : Int)
  statement: sign a * |a| = a
  proof: by
  rw [abs_eq_natAbs]; rw [sign_mul_natAbs a]

中文:
定理 sign_mul_abs
  条件: (a : 整数)
  结论: sign a * |a| = a
  证明: by
  rw [abs_eq_natAbs]; rw [sign_mul_natAbs a]

Depends on / 依赖: abs_eq_natAbs, sign_mul_natAbs
-/
theorem sign_mul_abs (a : Int) : sign a * |a| = a := by
  rw [abs_eq_natAbs]; rw [sign_mul_natAbs a]

/--
theorem `sign_mul_self_eq_abs` / 定理 `sign_mul_self_eq_abs`

English:
theorem sign_mul_self_eq_abs
  given: (a : Int)
  statement: sign a * a = |a|
  proof: by
  rw [abs_eq_natAbs]; rw [sign_mul_self_eq_natAbs]

中文:
定理 sign_mul_self_eq_abs
  条件: (a : 整数)
  结论: sign a * a = |a|
  证明: by
  rw [abs_eq_natAbs]; rw [sign_mul_self_eq_natAbs]

Depends on / 依赖: abs_eq_natAbs, sign_mul_self_eq_natAbs
-/
theorem sign_mul_self_eq_abs (a : Int) : sign a * a = |a| := by
  rw [abs_eq_natAbs]; rw [sign_mul_self_eq_natAbs]

/--
lemma `natAbs_le_self_sq` / 引理 `natAbs_le_self_sq`

English:
lemma natAbs_le_self_sq
  given: (a : Int)
  statement: (Int.natAbs a : Int) <= a ^ 2
  proof: by
  rw [← Int.natAbs_sq a]; rw [sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq

中文:
引理 natAbs_le_self_sq
  条件: (a : 整数)
  结论: (整数.natAbs a : 整数) <= a ^ 2
  证明: by
  rw [← Int.natAbs_sq a]; rw [sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq

Depends on / 依赖: Int.natAbs_sq, Nat.le_mul_self, le_mul_self, natAbs_sq
-/
lemma natAbs_le_self_sq (a : Int) : (Int.natAbs a : Int) <= a ^ 2 := by
  rw [← Int.natAbs_sq a]; rw [sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq

/--
lemma `le_self_sq` / 引理 `le_self_sq`

English:
lemma le_self_sq
  given: (b : Int)
  statement: b <= b ^ 2
  proof: le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

中文:
引理 le_self_sq
  条件: (b : 整数)
  结论: b <= b ^ 2
  证明: le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

Depends on / 依赖: le_natAbs, le_trans, natAbs_le_self_sq
-/
lemma le_self_sq (b : Int) : b <= b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

/--
lemma `abs_natCast` / 引理 `abs_natCast`

English:
lemma abs_natCast
  given: (n : Nat)
  statement: |(n : Int)| = n
  proof: abs_of_nonneg (natCast_nonneg n)

中文:
引理 abs_natCast
  条件: (n : 自然数)
  结论: |(n : 整数)| = n
  证明: abs_of_nonneg (natCast_nonneg n)
-/
@[norm_cast] lemma abs_natCast (n : Nat) : |(n : Int)| = n := abs_of_nonneg (natCast_nonneg n)

/--
theorem `natAbs_sub_pos_iff` / 定理 `natAbs_sub_pos_iff`

English:
theorem natAbs_sub_pos_iff
  given: {i j : Int}
  statement: 0 < natAbs (i - j) ↔ i != j
  proof: by
  grind

中文:
定理 natAbs_sub_pos_iff
  条件: {i j : 整数}
  结论: 0 < natAbs (i - j) ↔ i != j
  证明: by
  grind
-/
theorem natAbs_sub_pos_iff {i j : Int} : 0 < natAbs (i - j) ↔ i != j := by
  grind

/--
theorem `natAbs_sub_ne_zero_iff` / 定理 `natAbs_sub_ne_zero_iff`

English:
theorem natAbs_sub_ne_zero_iff
  given: {i j : Int}
  statement: natAbs (i - j) != 0 ↔ i != j
  proof: Nat.ne_zero_iff_zero_lt.trans natAbs_sub_pos_iff

@[simp]

中文:
定理 natAbs_sub_ne_zero_iff
  条件: {i j : 整数}
  结论: natAbs (i - j) != 0 ↔ i != j
  证明: Nat.ne_zero_iff_zero_lt.trans natAbs_sub_pos_iff

@[simp]

Depends on / 依赖: Nat.ne_zero_iff_zero_lt.trans, natAbs_sub_pos_iff, ne_zero_iff_zero_lt
-/
theorem natAbs_sub_ne_zero_iff {i j : Int} : natAbs (i - j) != 0 ↔ i != j :=
  Nat.ne_zero_iff_zero_lt.trans natAbs_sub_pos_iff

@[simp]
/--
theorem `abs_lt_one_iff` / 定理 `abs_lt_one_iff`

English:
theorem abs_lt_one_iff
  given: {a : Int}
  statement: |a| < 1 ↔ a = 0
  proof: by
  grind

中文:
定理 abs_lt_one_iff
  条件: {a : 整数}
  结论: |a| < 1 ↔ a = 0
  证明: by
  grind
-/
theorem abs_lt_one_iff {a : Int} : |a| < 1 ↔ a = 0 := by
  grind

/--
theorem `abs_le_one_iff` / 定理 `abs_le_one_iff`

English:
theorem abs_le_one_iff
  given: {a : Int}
  statement: |a| <= 1 ↔ a = 0 ∨ a = 1 ∨ a = -1
  proof: by
  grind

中文:
定理 abs_le_one_iff
  条件: {a : 整数}
  结论: |a| <= 1 ↔ a = 0 ∨ a = 1 ∨ a = -1
  证明: by
  grind
-/
theorem abs_le_one_iff {a : Int} : |a| <= 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 := by
  grind

/--
theorem `one_le_abs` / 定理 `one_le_abs`

English:
theorem one_le_abs
  given: {z : Int} (h₀ : z != 0)
  statement: 1 <= |z|
  proof: add_one_le_iff.mpr (abs_pos.mpr h₀)

中文:
定理 one_le_abs
  条件: {z : 整数} (h₀ : z != 0)
  结论: 1 <= |z|
  证明: add_one_le_iff.mpr (abs_pos.mpr h₀)

Depends on / 依赖: abs_pos, abs_pos.mpr, add_one_le_iff, add_one_le_iff.mpr
-/
theorem one_le_abs {z : Int} (h₀ : z != 0) : 1 <= |z| :=
  add_one_le_iff.mpr (abs_pos.mpr h₀)

/--
lemma `eq_zero_of_abs_lt_dvd` / 引理 `eq_zero_of_abs_lt_dvd`

English:
lemma eq_zero_of_abs_lt_dvd
  given: {m x : Int} (h1 : m ∣ x) (h2 : |x| < m)
  statement: x = 0
  proof: by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  lia

中文:
引理 eq_zero_of_abs_lt_dvd
  条件: {m x : 整数} (h1 : m ∣ x) (h2 : |x| < m)
  结论: x = 0
  证明: by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  lia

Depends on / 依赖: Int.abs_eq_natAbs, Int.natAbs_le_of_dvd_ne_zero, abs_eq_natAbs, natAbs_le_of_dvd_ne_zero
-/
lemma eq_zero_of_abs_lt_dvd {m x : Int} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  lia

/--
lemma `abs_sub_lt_of_lt_lt` / 引理 `abs_sub_lt_of_lt_lt`

English:
lemma abs_sub_lt_of_lt_lt
  given: {m a b : Nat} (ha : a < m) (hb : b < m)
  statement: |(b : Int) - a| < m
  proof: by
  grind

中文:
引理 abs_sub_lt_of_lt_lt
  条件: {m a b : 自然数} (ha : a < m) (hb : b < m)
  结论: |(b : 整数) - a| < m
  证明: by
  grind
-/
lemma abs_sub_lt_of_lt_lt {m a b : Nat} (ha : a < m) (hb : b < m) : |(b : Int) - a| < m := by
  grind


/--
theorem `ediv_eq_zero_of_lt_abs` / 定理 `ediv_eq_zero_of_lt_abs`

English:
theorem ediv_eq_zero_of_lt_abs
  given: {a b : Int} (H1 : 0 <= a) (H2 : a < |b|)
  statement: a / b = 0
  proof: match b, |b|, abs_eq_natAbs b, H2 with
  | (n : Nat), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
| -[n+1], _, rfl, H2 => neg_injective by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

中文:
定理 ediv_eq_zero_of_lt_abs
  条件: {a b : 整数} (H1 : 0 <= a) (H2 : a < |b|)
  结论: a / b = 0
  证明: match b, |b|, abs_eq_natAbs b, H2 with
  | (n : Nat), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
| -[n+1], _, rfl, H2 => neg_injective by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

Depends on / 依赖: Int.ediv_neg, abs_eq_natAbs, ediv_eq_zero_of_lt, ediv_neg, neg_injective
-/
theorem ediv_eq_zero_of_lt_abs {a b : Int} (H1 : 0 <= a) (H2 : a < |b|) : a / b = 0 :=
  match b, |b|, abs_eq_natAbs b, H2 with
  | (n : Nat), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
| -[n+1], _, rfl, H2 => neg_injective by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

/-! #### mod -/

@[simp]
/--
theorem `emod_abs` / 定理 `emod_abs`

English:
theorem emod_abs
  given: (a b : Int)
  statement: a % |b| = a % b
  proof: abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)

中文:
定理 emod_abs
  条件: (a b : 整数)
  结论: a % |b| = a % b
  证明: abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)

Depends on / 依赖: abs_by_cases, emod_neg
-/
theorem emod_abs (a b : Int) : a % |b| = a % b :=
  abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)

/--
theorem `emod_lt_abs` / 定理 `emod_lt_abs`

English:
theorem emod_lt_abs
  given: (a : Int) {b : Int} (H : b != 0)
  statement: a % b < |b|
  proof: by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)

中文:
定理 emod_lt_abs
  条件: (a : 整数) {b : 整数} (H : b != 0)
  结论: a % b < |b|
  证明: by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)

Depends on / 依赖: abs_pos, emod_abs, emod_lt_of_pos
-/
theorem emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < |b| := by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)


/--
theorem `abs_ediv_le_abs` / 定理 `abs_ediv_le_abs`

English:
theorem abs_ediv_le_abs
  statement: forall a b : Int, |a / b| <= |a|
  proof: suffices forall (a : Int) (n : Nat), |a / n| <= |a| from fun a b =>
    match b, Int.eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs]; rw [abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le


中文:
定理 abs_ediv_le_abs
  结论: 对任意 a b : 整数, |a / b| <= |a|
  证明: suffices forall (a : Int) (n : Nat), |a / n| <= |a| from fun a b =>
    match b, Int.eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs]; rw [abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le


Depends on / 依赖: Int.ediv_neg, Int.eq_nat_or_neg, Nat.div_le_self, Nat.succ_le_succ, Nat.zero_le, Or.inl, Or.inr, abs_eq_natAbs, abs_neg, div_le_self, ediv_neg, eq_nat_or_neg, ofNat_le_ofNat_of_le, succ_le_succ, zero_le
-/
theorem abs_ediv_le_abs : forall a b : Int, |a / b| <= |a| :=
  suffices forall (a : Int) (n : Nat), |a / n| <= |a| from fun a b =>
    match b, Int.eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs]; rw [abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le
    (match a, n with
      | (m : Nat), n => Nat.div_le_self _ _
      | -[m+1], 0 => Nat.zero_le _
      | -[m+1], n + 1 => Nat.succ_le_succ (Nat.div_le_self _ _))

/--
theorem `abs_sign_of_ne_zero` / 定理 `abs_sign_of_ne_zero`

English:
theorem abs_sign_of_ne_zero
  given: {z : Int} (hz : z != 0)
  statement: |z.sign| = 1
  proof: by
  rw [abs_eq_natAbs]; rw [natAbs_sign_of_ne_zero hz]; rw [Int.ofNat_one]

中文:
定理 abs_sign_of_ne_zero
  条件: {z : 整数} (hz : z != 0)
  结论: |z.sign| = 1
  证明: by
  rw [abs_eq_natAbs]; rw [natAbs_sign_of_ne_zero hz]; rw [Int.ofNat_one]

Depends on / 依赖: Int.ofNat_one, abs_eq_natAbs, natAbs_sign_of_ne_zero, ofNat_one
-/
theorem abs_sign_of_ne_zero {z : Int} (hz : z != 0) : |z.sign| = 1 := by
  rw [abs_eq_natAbs]; rw [natAbs_sign_of_ne_zero hz]; rw [Int.ofNat_one]

/--
theorem `sign_eq_ediv_abs'` / 定理 `sign_eq_ediv_abs'`

English:
theorem sign_eq_ediv_abs'
  given: (a : Int)
  statement: sign a = a / |a|
  proof: if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm

中文:
定理 sign_eq_ediv_abs'
  条件: (a : 整数)
  结论: sign a = a / |a|
  证明: if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm
-/
protected theorem sign_eq_ediv_abs' (a : Int) : sign a = a / |a| :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm

/--
theorem `sign_eq_abs_ediv` / 定理 `sign_eq_abs_ediv`

English:
theorem sign_eq_abs_ediv
  given: (a : Int)
  statement: sign a = |a| / a
  proof: if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (sign_mul_self_eq_abs _).symm).symm

中文:
定理 sign_eq_abs_ediv
  条件: (a : 整数)
  结论: sign a = |a| / a
  证明: if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (sign_mul_self_eq_abs _).symm).symm
-/
protected theorem sign_eq_abs_ediv (a : Int) : sign a = |a| / a :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (sign_mul_self_eq_abs _).symm).symm

end Int

section Group
variable {G : Type*} [Group G]

@[to_additive (attr := simp) abs_zsmul_eq_zero]
/--
lemma `zpow_abs_eq_one` / 引理 `zpow_abs_eq_one`

English:
lemma zpow_abs_eq_one
  given: (a : G) (n : Int)
  statement: a ^ |n| = 1 ↔ a ^ n = 1
  proof: by
  rw [← Int.natCast_natAbs]; rw [zpow_natCast]; rw [pow_natAbs_eq_one]

中文:
引理 zpow_abs_eq_one
  条件: (a : G) (n : 整数)
  结论: a ^ |n| = 1 ↔ a ^ n = 1
  证明: by
  rw [← Int.natCast_natAbs]; rw [zpow_natCast]; rw [pow_natAbs_eq_one]

Depends on / 依赖: Int.natCast_natAbs, natCast_natAbs, pow_natAbs_eq_one, zpow_natCast
-/
lemma zpow_abs_eq_one (a : G) (n : Int) : a ^ |n| = 1 ↔ a ^ n = 1 := by
  rw [← Int.natCast_natAbs]; rw [zpow_natCast]; rw [pow_natAbs_eq_one]

end Group
