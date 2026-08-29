/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Common

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib/Algebra/Field/Rat.lean`
once the `Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notation

- `/.` is infix notation for `Rat.divInt`.

-/

@[expose] public section

-- TODO: If `Inv` was defined earlier than `Algebra.Group.Defs`, we could have
-- assert_not_exists Monoid
assert_not_exists MonoidWithZero Lattice PNat Nat.gcd_greatest

open Function

namespace Rat
variable {q : Rat}

/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  given: (a : Rat)
  statement: 0 < a.den
  proof: Nat.pos_of_ne_zero a.den_nz

中文:
定理 pos
  条件: (a : Rat)
  结论: 0 < a.den
  证明: Nat.pos_of_ne_zero a.den_nz

Depends on / 依赖: Nat.pos_of_ne_zero, a.den_nz, den_nz, pos_of_ne_zero
-/
theorem pos (a : Rat) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz

/--
lemma `mk'_num_den` / 引理 `mk'_num_den`

English:
lemma mk'_num_den
  given: (q : Rat)
  statement: mk' q.num q.den q.den_nz q.reduced = q
  proof: rfl

@[simp]

中文:
引理 mk'_num_den
  条件: (q : Rat)
  结论: mk' q.num q.den q.den_nz q.reduced = q
  证明: rfl

@[simp]
-/
lemma mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
/--
theorem `ofInt_eq_cast` / 定理 `ofInt_eq_cast`

English:
theorem ofInt_eq_cast
  given: (n : Int)
  statement: ofInt n = Int.cast n
  proof: rfl

中文:
定理 ofInt_eq_cast
  条件: (n : 整数)
  结论: of整数 n = 整数.cast n
  证明: rfl
-/
theorem ofInt_eq_cast (n : Int) : ofInt n = Int.cast n :=
  rfl

/--
lemma `intCast_injective` / 引理 `intCast_injective`

English:
lemma intCast_injective
  statement: Injective (Int.cast : Int -> Rat)
  proof: fun _ _ => congr_arg num

中文:
引理 intCast_injective
  结论: Injective (整数.cast : 整数 -> Rat)
  证明: fun _ _ => congr_arg num

Depends on / 依赖: congr_arg
-/
lemma intCast_injective : Injective (Int.cast : Int -> Rat) := fun _ _ => congr_arg num
/--
lemma `natCast_injective` / 引理 `natCast_injective`

English:
lemma natCast_injective
  statement: Injective (Nat.cast : Nat -> Rat)
  proof: intCast_injective.comp fun _ _ => Int.natCast_inj.1

中文:
引理 natCast_injective
  结论: Injective (自然数.cast : 自然数 -> Rat)
  证明: intCast_injective.comp fun _ _ => Int.natCast_inj.1

Depends on / 依赖: Int.natCast_inj, intCast_injective, intCast_injective.comp, natCast_inj
-/
lemma natCast_injective : Injective (Nat.cast : Nat -> Rat) :=
  intCast_injective.comp fun _ _ => Int.natCast_inj.1

/--
lemma `intCast_eq_one_iff` / 引理 `intCast_eq_one_iff`

English:
lemma intCast_eq_one_iff
  given: {n : Int}
  statement: (n : Rat) = 1 ↔ n = 1
  proof: intCast_inj

中文:
引理 intCast_eq_one_iff
  条件: {n : 整数}
  结论: (n : Rat) = 1 ↔ n = 1
  证明: intCast_inj
-/
@[simp high, norm_cast] lemma intCast_eq_one_iff {n : Int} : (n : Rat) = 1 ↔ n = 1 := intCast_inj

/--
lemma `natCast_eq_one_iff` / 引理 `natCast_eq_one_iff`

English:
lemma natCast_eq_one_iff
  given: {n : Nat}
  statement: (n : Rat) = 1 ↔ n = 1
  proof: natCast_inj

中文:
引理 natCast_eq_one_iff
  条件: {n : 自然数}
  结论: (n : Rat) = 1 ↔ n = 1
  证明: natCast_inj
-/
@[simp high, norm_cast] lemma natCast_eq_one_iff {n : Nat} : (n : Rat) = 1 ↔ n = 1 := natCast_inj

/--
lemma `mkRat_eq_divInt` / 引理 `mkRat_eq_divInt`

English:
lemma mkRat_eq_divInt
  given: (n d)
  statement: mkRat n d = n /. d
  proof: rfl

中文:
引理 mkRat_eq_divInt
  条件: (n d)
  结论: mkRat n d = n /. d
  证明: rfl
-/
lemma mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl

/--
lemma `mk'_zero` / 引理 `mk'_zero`

English:
lemma mk'_zero
  given: (d) (h : d != 0) (w)
  statement: mk' 0 d h w = 0
  proof: by congr; simp_all

中文:
引理 mk'_zero
  条件: (d) (h : d != 0) (w)
  结论: mk' 0 d h w = 0
  证明: by congr; simp_all
-/
@[simp] lemma mk'_zero (d) (h : d != 0) (w) : mk' 0 d h w = 0 := by congr; simp_all

/--
lemma `num_ne_zero` / 引理 `num_ne_zero`

English:
lemma num_ne_zero
  given: {q : Rat}
  statement: q.num != 0 ↔ q != 0
  proof: num_eq_zero.not

中文:
引理 num_ne_zero
  条件: {q : Rat}
  结论: q.num != 0 ↔ q != 0
  证明: num_eq_zero.not

Depends on / 依赖: num_eq_zero, num_eq_zero.not
-/
lemma num_ne_zero {q : Rat} : q.num != 0 ↔ q != 0 := num_eq_zero.not

/--
lemma `den_ne_zero` / 引理 `den_ne_zero`

English:
lemma den_ne_zero
  given: (q : Rat)
  statement: q.den != 0
  proof: q.den_pos.ne'

@[simp]

中文:
引理 den_ne_zero
  条件: (q : Rat)
  结论: q.den != 0
  证明: q.den_pos.ne'

@[simp]
-/
@[simp] lemma den_ne_zero (q : Rat) : q.den != 0 := q.den_pos.ne'

@[simp]
/--
theorem `divInt_eq_zero` / 定理 `divInt_eq_zero`

English:
theorem divInt_eq_zero
  given: {a b : Int} (b0 : b != 0)
  statement: a /. b = 0 ↔ a = 0
  proof: by
  rw [← zero_divInt b]; rw [divInt_eq_divInt_iff b0 b0]; rw [Int.zero_mul]; rw [Int.mul_eq_zero]; rw [or_iff_left b0]

中文:
定理 divInt_eq_zero
  条件: {a b : 整数} (b0 : b != 0)
  结论: a /. b = 0 ↔ a = 0
  证明: by
  rw [← zero_divInt b]; rw [divInt_eq_divInt_iff b0 b0]; rw [Int.zero_mul]; rw [Int.mul_eq_zero]; rw [or_iff_left b0]

Depends on / 依赖: Int.mul_eq_zero, Int.zero_mul, divInt_eq_divInt_iff, mul_eq_zero, or_iff_left, zero_divInt, zero_mul
-/
theorem divInt_eq_zero {a b : Int} (b0 : b != 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b]; rw [divInt_eq_divInt_iff b0 b0]; rw [Int.zero_mul]; rw [Int.mul_eq_zero]; rw [or_iff_left b0]

/--
theorem `divInt_ne_zero` / 定理 `divInt_ne_zero`

English:
theorem divInt_ne_zero
  given: {a b : Int} (b0 : b != 0)
  statement: a /. b != 0 ↔ a != 0
  proof: (divInt_eq_zero b0).not

中文:
定理 divInt_ne_zero
  条件: {a b : 整数} (b0 : b != 0)
  结论: a /. b != 0 ↔ a != 0
  证明: (divInt_eq_zero b0).not

Depends on / 依赖: divInt_eq_zero
-/
theorem divInt_ne_zero {a b : Int} (b0 : b != 0) : a /. b != 0 ↔ a != 0 :=
  (divInt_eq_zero b0).not

-- TODO: Rename `mkRat_num_den` in Lean core
alias mkRat_num_den' := mkRat_self

/--
theorem `intCast_eq_divInt` / 定理 `intCast_eq_divInt`

English:
theorem intCast_eq_divInt
  given: (z : Int)
  statement: (z : Rat) = z /. 1
  proof: mk_eq_divInt

中文:
定理 intCast_eq_divInt
  条件: (z : 整数)
  结论: (z : Rat) = z /. 1
  证明: mk_eq_divInt

Depends on / 依赖: mk_eq_divInt
-/
theorem intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1 := mk_eq_divInt

/--
theorem `lift_binop_eq` / 定理 `lift_binop_eq`

English:
theorem lift_binop_eq
  statement: (f : Rat -> Rat -> Rat) (f₁ : Int -> Int -> Int -> Int -> Int) (f₂ : Int -> Int -> Int -> Int -> Int)
  proof: by
  generalize ha : a /. b = x; obtain ⟨n₁, d₁, h₁, c₁⟩ := x; rw [mk_eq_divInt] at ha
  generalize hc : c /. d = x; obtain ⟨n₂, d₂, h₂, c₂⟩ := x; rw [mk_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_divInt_iff (f0 d₁0 d₂0) (f

中文:
定理 lift_binop_eq
  结论: (f : Rat -> Rat -> Rat) (f₁ : 整数 -> 整数 -> 整数 -> 整数 -> 整数) (f₂ : 整数 -> 整数 -> 整数 -> 整数 -> 整数)
  证明: by
  generalize ha : a /. b = x; obtain ⟨n₁, d₁, h₁, c₁⟩ := x; rw [mk_eq_divInt] at ha
  generalize hc : c /. d = x; obtain ⟨n₂, d₂, h₂, c₂⟩ := x; rw [mk_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_divInt_iff (f0 d₁0 d₂0) (f

Depends on / 依赖: Int.ofNat_ne_zero, divInt_eq_divInt_iff, generalize, mk_eq_divInt, ofNat_ne_zero
-/
theorem lift_binop_eq (f : Rat -> Rat -> Rat) (f₁ : Int -> Int -> Int -> Int -> Int) (f₂ : Int -> Int -> Int -> Int -> Int)
    (fv :
      forall {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
        f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
    (f0 : forall {n₁ d₁ n₂ d₂}, d₁ != 0 -> d₂ != 0 -> f₂ n₁ d₁ n₂ d₂ != 0) (a b c d : Int)
    (b0 : b != 0) (d0 : d != 0)
    (H :
      forall {n₁ d₁ n₂ d₂}, a * d₁ = n₁ * b -> c * d₂ = n₂ * d ->
        f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
    f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d := by
  generalize ha : a /. b = x; obtain ⟨n₁, d₁, h₁, c₁⟩ := x; rw [mk_eq_divInt] at ha
  generalize hc : c /. d = x; obtain ⟨n₂, d₂, h₂, c₂⟩ := x; rw [mk_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_divInt_iff (f0 d₁0 d₂0) (f0 b0 d0)).2
    (H ((divInt_eq_divInt_iff b0 d₁0).1 ha) ((divInt_eq_divInt_iff d0 d₂0).1 hc))

/--
lemma `neg_def` / 引理 `neg_def`

English:
lemma neg_def
  given: (q : Rat)
  statement: -q = -q.num /. q.den
  proof: by rw [← neg_divInt, num_divInt_den]

中文:
引理 neg_def
  条件: (q : Rat)
  结论: -q = -q.num /. q.den
  证明: by rw [← neg_divInt, num_divInt_den]

Depends on / 依赖: neg_divInt, num_divInt_den
-/
lemma neg_def (q : Rat) : -q = -q.num /. q.den := by rw [← neg_divInt, num_divInt_den]

/--
lemma `divInt_neg` / 引理 `divInt_neg`

English:
lemma divInt_neg
  given: (n d : Int)
  statement: n /. -d = -n /. d
  proof: divInt_neg' ..

中文:
引理 divInt_neg
  条件: (n d : 整数)
  结论: n /. -d = -n /. d
  证明: divInt_neg' ..
-/
@[simp] lemma divInt_neg (n d : Int) : n /. -d = -n /. d := divInt_neg' ..

/--
lemma `mk'_mul_mk'` / 引理 `mk'_mul_mk'`

English:
lemma mk'_mul_mk'
  statement: (n₁ n₂ : Int) (d₁ d₂ : Nat) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
  proof: by
  rw [mul_def]; simp [mk_eq_normalize]

中文:
引理 mk'_mul_mk'
  结论: (n₁ n₂ : 整数) (d₁ d₂ : 自然数) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
  证明: by
  rw [mul_def]; simp [mk_eq_normalize]
-/
lemma mk'_mul_mk' (n₁ n₂ : Int) (d₁ d₂ : Nat) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul_left h₂₁).mul_right (h₁₂.mul_left hnd₂)) := by
  rw [mul_def]; simp [mk_eq_normalize]

/--
lemma `mul_eq_mkRat` / 引理 `mul_eq_mkRat`

English:
lemma mul_eq_mkRat
  given: (q r : Rat)
  statement: q * r = mkRat (q.num * r.num) (q.den * r.den)
  proof: by
  rw [mul_def]; rw [normalize_eq_mkRat]

中文:
引理 mul_eq_mkRat
  条件: (q r : Rat)
  结论: q * r = mkRat (q.num * r.num) (q.den * r.den)
  证明: by
  rw [mul_def]; rw [normalize_eq_mkRat]

Depends on / 依赖: mul_def, normalize_eq_mkRat
-/
lemma mul_eq_mkRat (q r : Rat) : q * r = mkRat (q.num * r.num) (q.den * r.den) := by
  rw [mul_def]; rw [normalize_eq_mkRat]

/--
lemma `pow_eq_mkRat` / 引理 `pow_eq_mkRat`

English:
lemma pow_eq_mkRat
  given: (q : Rat) (n : Nat)
  statement: q ^ n = mkRat (q.num ^ n) (q.den ^ n)
  proof: by
  rw [pow_def]; rw [mk_eq_mkRat]

中文:
引理 pow_eq_mkRat
  条件: (q : Rat) (n : 自然数)
  结论: q ^ n = mkRat (q.num ^ n) (q.den ^ n)
  证明: by
  rw [pow_def]; rw [mk_eq_mkRat]

Depends on / 依赖: mk_eq_mkRat, pow_def
-/
lemma pow_eq_mkRat (q : Rat) (n : Nat) : q ^ n = mkRat (q.num ^ n) (q.den ^ n) := by
  rw [pow_def]; rw [mk_eq_mkRat]

/--
lemma `pow_eq_divInt` / 引理 `pow_eq_divInt`

English:
lemma pow_eq_divInt
  given: (q : Rat) (n : Nat)
  statement: q ^ n = q.num ^ n /. q.den ^ n
  proof: by
  rw [pow_def]; rw [mk_eq_divInt]; rw [Int.natCast_pow]

中文:
引理 pow_eq_divInt
  条件: (q : Rat) (n : 自然数)
  结论: q ^ n = q.num ^ n /. q.den ^ n
  证明: by
  rw [pow_def]; rw [mk_eq_divInt]; rw [Int.natCast_pow]

Depends on / 依赖: Int.natCast_pow, mk_eq_divInt, natCast_pow, pow_def
-/
lemma pow_eq_divInt (q : Rat) (n : Nat) : q ^ n = q.num ^ n /. q.den ^ n := by
  rw [pow_def]; rw [mk_eq_divInt]; rw [Int.natCast_pow]

/--
lemma `mk'_pow` / 引理 `mk'_pow`

English:
lemma mk'_pow
  given: (num : Int) (den : Nat) (hd hdn) (n : Nat)
  proof: rfl

中文:
引理 mk'_pow
  条件: (num : 整数) (den : 自然数) (hd hdn) (n : 自然数)
  证明: rfl
-/
@[simp] lemma mk'_pow (num : Int) (den : Nat) (hd hdn) (n : Nat) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

/--
lemma `inv_mkRat` / 引理 `inv_mkRat`

English:
lemma inv_mkRat
  given: (a : Int) (b : Nat)
  statement: (mkRat a b)⁻¹ = b /. a
  proof: by
  rw [mkRat_eq_divInt]; rw [inv_divInt]

中文:
引理 inv_mkRat
  条件: (a : 整数) (b : 自然数)
  结论: (mkRat a b)⁻¹ = b /. a
  证明: by
  rw [mkRat_eq_divInt]; rw [inv_divInt]
-/
@[simp] lemma inv_mkRat (a : Int) (b : Nat) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt]; rw [inv_divInt]

/--
lemma `divInt_div_divInt` / 引理 `divInt_div_divInt`

English:
lemma divInt_div_divInt
  given: (n₁ d₁ n₂ d₂)
  proof: by
  rw [div_def]; rw [inv_divInt]; rw [divInt_mul_divInt]

中文:
引理 divInt_div_divInt
  条件: (n₁ d₁ n₂ d₂)
  证明: by
  rw [div_def]; rw [inv_divInt]; rw [divInt_mul_divInt]
-/
@[simp] lemma divInt_div_divInt (n₁ d₁ n₂ d₂) :
    (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂) := by
  rw [div_def]; rw [inv_divInt]; rw [divInt_mul_divInt]

/--
lemma `div_def'` / 引理 `div_def'`

English:
lemma div_def'
  given: (q r : Rat)
  statement: q / r = (q.num * r.den) /. (q.den * r.num)
  proof: by
  rw [← divInt_div_divInt]; rw [num_divInt_den]; rw [num_divInt_den]

中文:
引理 div_def'
  条件: (q r : Rat)
  结论: q / r = (q.num * r.den) /. (q.den * r.num)
  证明: by
  rw [← divInt_div_divInt]; rw [num_divInt_den]; rw [num_divInt_den]

Depends on / 依赖: divInt_div_divInt, num_divInt_den
-/
lemma div_def' (q r : Rat) : q / r = (q.num * r.den) /. (q.den * r.num) := by
  rw [← divInt_div_divInt]; rw [num_divInt_den]; rw [num_divInt_den]

variable (a b c : Rat)

/--
lemma `divInt_one` / 引理 `divInt_one`

English:
lemma divInt_one
  given: (n : Int)
  statement: n /. 1 = n
  proof: by simp [divInt, mkRat, normalize]

中文:
引理 divInt_one
  条件: (n : 整数)
  结论: n /. 1 = n
  证明: by simp [divInt, mkRat, normalize]
-/
@[simp] lemma divInt_one (n : Int) : n /. 1 = n := by simp [divInt, mkRat, normalize]

/--
lemma `divInt_one_one` / 引理 `divInt_one_one`

English:
lemma divInt_one_one
  statement: 1 /. 1 = 1
  proof: by rw [divInt_one, Rat.intCast_one]

中文:
引理 divInt_one_one
  结论: 1 /. 1 = 1
  证明: by rw [divInt_one, Rat.intCast_one]

Depends on / 依赖: Rat.intCast_one, divInt_one, intCast_one
-/
lemma divInt_one_one : 1 /. 1 = 1 := by rw [divInt_one, Rat.intCast_one]

/--
theorem `zero_ne_one` / 定理 `zero_ne_one`

English:
theorem zero_ne_one
  statement: 0 != (1 : Rat)
  proof: by
  rw [ne_comm]; rw [← divInt_one_one]; rw [divInt_ne_zero] <;> lia

中文:
定理 zero_ne_one
  结论: 0 != (1 : Rat)
  证明: by
  rw [ne_comm]; rw [← divInt_one_one]; rw [divInt_ne_zero] <;> lia
-/
protected theorem zero_ne_one : 0 != (1 : Rat) := by
  rw [ne_comm]; rw [← divInt_one_one]; rw [divInt_ne_zero] <;> lia

attribute [simp] mkRat_eq_zero

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Data.Real.Basic
/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: : Nontrivial Rat where exists_pair_ne
  body: ⟨1, 0, by decide⟩

中文:
实例 nontrivial
  签名: : Nontrivial Rat where 存在_pair_ne
  定义体: ⟨1, 0, by decide⟩
-/
instance nontrivial : Nontrivial Rat where exists_pair_ne := ⟨1, 0, by decide⟩


/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup Rat where
  body: Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := (· * ·)
  zsmul := (· * ·)
  nsmul_zero := Rat.zero_mul
  nsmul_succ n q := by
    change ((n + 1 : Int) : Rat) * q

中文:
实例 addCommGroup
  签名: : AddCommGroup Rat where
  定义体: Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := (· * ·)
  zsmul := (· * ·)
  nsmul_zero := Rat.zero_mul
  nsmul_succ n q := by
    change ((n + 1 : Int) : Rat) * q

Depends on / 依赖: Rat.zero_add, zero_add
-/
instance addCommGroup : AddCommGroup Rat where
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := (· * ·)
  zsmul := (· * ·)
  nsmul_zero := Rat.zero_mul
  nsmul_succ n q := by
    change ((n + 1 : Int) : Rat) * q = _
    rw [Rat.intCast_add]; rw [Rat.add_mul]; rw [Rat.intCast_one]; rw [Rat.one_mul]
    rfl
  zsmul_zero' := Rat.zero_mul
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; simp [Rat.add_mul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Int.negSucc_eq]; rw [Rat.intCast_neg]; rw [Rat.neg_mul]; rfl

/--
Instance `addGroup` / 实例 `addGroup`

English:
instance addGroup
  signature: : AddGroup Rat
  body: by infer_instance

中文:
实例 addGroup
  签名: : AddGroup Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addGroup : AddGroup Rat := by infer_instance

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid Rat
  body: by infer_instance

中文:
实例 addCommMonoid
  签名: : AddCommMonoid Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addCommMonoid : AddCommMonoid Rat := by infer_instance

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid Rat
  body: by infer_instance

中文:
实例 addMonoid
  签名: : AddMonoid Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addMonoid : AddMonoid Rat := by infer_instance

/--
Instance `addLeftCancelSemigroup` / 实例 `addLeftCancelSemigroup`

English:
instance addLeftCancelSemigroup
  signature: : AddLeftCancelSemigroup Rat
  body: by infer_instance

中文:
实例 addLeftCancelSemigroup
  签名: : AddLeftCancelSemigroup Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addLeftCancelSemigroup : AddLeftCancelSemigroup Rat := by infer_instance

/--
Instance `addRightCancelSemigroup` / 实例 `addRightCancelSemigroup`

English:
instance addRightCancelSemigroup
  signature: : AddRightCancelSemigroup Rat
  body: by infer_instance

中文:
实例 addRightCancelSemigroup
  签名: : AddRightCancelSemigroup Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addRightCancelSemigroup : AddRightCancelSemigroup Rat := by infer_instance

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: : AddCommSemigroup Rat
  body: by infer_instance

中文:
实例 addCommSemigroup
  签名: : AddCommSemigroup Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addCommSemigroup : AddCommSemigroup Rat := by infer_instance

/--
Instance `addSemigroup` / 实例 `addSemigroup`

English:
instance addSemigroup
  signature: : AddSemigroup Rat
  body: by infer_instance

中文:
实例 addSemigroup
  签名: : AddSemigroup Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance addSemigroup : AddSemigroup Rat := by infer_instance

/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: : CommMonoid Rat where
  body: Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := Rat.pow_zero
  npow_succ n q := Rat.pow_succ q n

中文:
实例 commMonoid
  签名: : CommMonoid Rat where
  定义体: Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := Rat.pow_zero
  npow_succ n q := Rat.pow_succ q n

Depends on / 依赖: Rat.mul_one, mul_one
-/
instance commMonoid : CommMonoid Rat where
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := Rat.pow_zero
  npow_succ n q := Rat.pow_succ q n

/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: : Monoid Rat
  body: by infer_instance

中文:
实例 monoid
  签名: : Monoid Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance monoid : Monoid Rat := by infer_instance

/--
Instance `commSemigroup` / 实例 `commSemigroup`

English:
instance commSemigroup
  signature: : CommSemigroup Rat
  body: by infer_instance

中文:
实例 commSemigroup
  签名: : CommSemigroup Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance commSemigroup : CommSemigroup Rat := by infer_instance

/--
Instance `semigroup` / 实例 `semigroup`

English:
instance semigroup
  signature: : Semigroup Rat
  body: by infer_instance

@[simp]

中文:
实例 semigroup
  签名: : Semigroup Rat
  定义体: by infer_instance

@[simp]

Depends on / 依赖: infer_instance
-/
instance semigroup : Semigroup Rat := by infer_instance

@[simp]
/--
theorem `den_neg_eq_den` / 定理 `den_neg_eq_den`

English:
theorem den_neg_eq_den
  given: (q : Rat)
  statement: (-q).den = q.den
  proof: rfl

@[simp]

中文:
定理 den_neg_eq_den
  条件: (q : Rat)
  结论: (-q).den = q.den
  证明: rfl

@[simp]
-/
theorem den_neg_eq_den (q : Rat) : (-q).den = q.den :=
  rfl

@[simp]
/--
theorem `num_neg_eq_neg_num` / 定理 `num_neg_eq_neg_num`

English:
theorem num_neg_eq_neg_num
  given: (q : Rat)
  statement: (-q).num = -q.num
  proof: rfl

中文:
定理 num_neg_eq_neg_num
  条件: (q : Rat)
  结论: (-q).num = -q.num
  证明: rfl
-/
theorem num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num :=
  rfl

-- Not `@[simp]` as `num_ofNat` is stronger.
/--
theorem `num_zero` / 定理 `num_zero`

English:
theorem num_zero
  statement: Rat.num 0 = 0
  proof: rfl

中文:
定理 num_zero
  结论: Rat.num 0 = 0
  证明: rfl
-/
theorem num_zero : Rat.num 0 = 0 :=
  rfl

-- Not `@[simp]` as `den_ofNat` is stronger.
/--
theorem `den_zero` / 定理 `den_zero`

English:
theorem den_zero
  statement: Rat.den 0 = 1
  proof: rfl

中文:
定理 den_zero
  结论: Rat.den 0 = 1
  证明: rfl
-/
theorem den_zero : Rat.den 0 = 1 :=
  rfl

/--
lemma `zero_of_num_zero` / 引理 `zero_of_num_zero`

English:
lemma zero_of_num_zero
  given: {q : Rat} (hq : q.num = 0)
  statement: q = 0
  proof: by simpa [hq] using q.num_divInt_den.symm

中文:
引理 zero_of_num_zero
  条件: {q : Rat} (hq : q.num = 0)
  结论: q = 0
  证明: by simpa [hq] using q.num_divInt_den.symm

Depends on / 依赖: num_divInt_den, q.num_divInt_den.symm
-/
lemma zero_of_num_zero {q : Rat} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.num_divInt_den.symm

/--
theorem `zero_iff_num_zero` / 定理 `zero_iff_num_zero`

English:
theorem zero_iff_num_zero
  given: {q : Rat}
  statement: q = 0 ↔ q.num = 0
  proof: ⟨fun _ => by simp [*], zero_of_num_zero⟩

中文:
定理 zero_iff_num_zero
  条件: {q : Rat}
  结论: q = 0 ↔ q.num = 0
  证明: ⟨fun _ => by simp [*], zero_of_num_zero⟩

Depends on / 依赖: zero_of_num_zero
-/
theorem zero_iff_num_zero {q : Rat} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

-- `Not `@[simp]` as `num_ofNat` is stronger.
/--
theorem `num_one` / 定理 `num_one`

English:
theorem num_one
  statement: (1 : Rat).num = 1
  proof: rfl

@[simp]

中文:
定理 num_one
  结论: (1 : Rat).num = 1
  证明: rfl

@[simp]
-/
theorem num_one : (1 : Rat).num = 1 :=
  rfl

@[simp]
/--
theorem `den_one` / 定理 `den_one`

English:
theorem den_one
  statement: (1 : Rat).den = 1
  proof: rfl

中文:
定理 den_one
  结论: (1 : Rat).den = 1
  证明: rfl
-/
theorem den_one : (1 : Rat).den = 1 :=
  rfl

/--
theorem `mk_num_ne_zero_of_ne_zero` / 定理 `mk_num_ne_zero_of_ne_zero`

English:
theorem mk_num_ne_zero_of_ne_zero
  given: {q : Rat} {n d : Int} (hq : q != 0) (hqnd : q = n /. d)
  statement: n != 0
  proof: fun this => hq by simpa [this] using hqnd

中文:
定理 mk_num_ne_zero_of_ne_zero
  条件: {q : Rat} {n d : 整数} (hq : q != 0) (hqnd : q = n /. d)
  结论: n != 0
  证明: fun this => hq by simpa [this] using hqnd
-/
theorem mk_num_ne_zero_of_ne_zero {q : Rat} {n d : Int} (hq : q != 0) (hqnd : q = n /. d) : n != 0 :=
fun this => hq by simpa [this] using hqnd

/--
theorem `mk_denom_ne_zero_of_ne_zero` / 定理 `mk_denom_ne_zero_of_ne_zero`

English:
theorem mk_denom_ne_zero_of_ne_zero
  given: {q : Rat} {n d : Int} (hq : q != 0) (hqnd : q = n /. d)
  statement: d != 0
  proof: fun this => hq by simpa [this] using hqnd

中文:
定理 mk_denom_ne_zero_of_ne_zero
  条件: {q : Rat} {n d : 整数} (hq : q != 0) (hqnd : q = n /. d)
  结论: d != 0
  证明: fun this => hq by simpa [this] using hqnd
-/
theorem mk_denom_ne_zero_of_ne_zero {q : Rat} {n d : Int} (hq : q != 0) (hqnd : q = n /. d) : d != 0 :=
fun this => hq by simpa [this] using hqnd

/--
theorem `divInt_ne_zero_of_ne_zero` / 定理 `divInt_ne_zero_of_ne_zero`

English:
theorem divInt_ne_zero_of_ne_zero
  given: {n d : Int} (h : n != 0) (hd : d != 0)
  statement: n /. d != 0
  proof: (divInt_ne_zero hd).mpr h

中文:
定理 divInt_ne_zero_of_ne_zero
  条件: {n d : 整数} (h : n != 0) (hd : d != 0)
  结论: n /. d != 0
  证明: (divInt_ne_zero hd).mpr h

Depends on / 依赖: divInt_ne_zero
-/
theorem divInt_ne_zero_of_ne_zero {n d : Int} (h : n != 0) (hd : d != 0) : n /. d != 0 :=
  (divInt_ne_zero hd).mpr h

section Casts

/--
theorem `add_divInt` / 定理 `add_divInt`

English:
theorem add_divInt
  given: (a b c : Int)
  statement: (a + b) /. c = a /. c + b /. c
  proof: if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h]; rw [divInt_eq_divInt_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]

中文:
定理 add_divInt
  条件: (a b c : 整数)
  结论: (a + b) /. c = a /. c + b /. c
  证明: if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h]; rw [divInt_eq_divInt_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]
-/
protected theorem add_divInt (a b c : Int) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h]; rw [divInt_eq_divInt_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]

/--
lemma `intCast_div_eq_divInt` / 引理 `intCast_div_eq_divInt`

English:
lemma intCast_div_eq_divInt
  given: (n d : Int)
  statement: (n : Rat) / d = n /. d
  proof: by rw [divInt_eq_div]

中文:
引理 intCast_div_eq_divInt
  条件: (n d : 整数)
  结论: (n : Rat) / d = n /. d
  证明: by rw [divInt_eq_div]

Depends on / 依赖: divInt_eq_div
-/
lemma intCast_div_eq_divInt (n d : Int) : (n : Rat) / d = n /. d := by rw [divInt_eq_div]

/--
theorem `natCast_div_eq_divInt` / 定理 `natCast_div_eq_divInt`

English:
theorem natCast_div_eq_divInt
  given: (n d : Nat)
  statement: (n : Rat) / d = n /. d
  proof: Rat.intCast_div_eq_divInt n d

中文:
定理 natCast_div_eq_divInt
  条件: (n d : 自然数)
  结论: (n : Rat) / d = n /. d
  证明: Rat.intCast_div_eq_divInt n d

Depends on / 依赖: Rat.intCast_div_eq_divInt, intCast_div_eq_divInt
-/
theorem natCast_div_eq_divInt (n d : Nat) : (n : Rat) / d = n /. d := Rat.intCast_div_eq_divInt n d

/--
theorem `divInt_mul_divInt_cancel` / 定理 `divInt_mul_divInt_cancel`

English:
theorem divInt_mul_divInt_cancel
  given: {x : Int} (hx : x != 0) (n d : Int)
  statement: n /. x * (x /. d) = n /. d
  proof: by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt]; rw [x.mul_comm]; rw [divInt_mul_right hx]

中文:
定理 divInt_mul_divInt_cancel
  条件: {x : 整数} (hx : x != 0) (n d : 整数)
  结论: n /. x * (x /. d) = n /. d
  证明: by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt]; rw [x.mul_comm]; rw [divInt_mul_right hx]

Depends on / 依赖: divInt_mul_divInt, divInt_mul_right, mul_comm, x.mul_comm
-/
theorem divInt_mul_divInt_cancel {x : Int} (hx : x != 0) (n d : Int) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt]; rw [x.mul_comm]; rw [divInt_mul_right hx]

/--
theorem `coe_int_num_of_den_eq_one` / 定理 `coe_int_num_of_den_eq_one`

English:
theorem coe_int_num_of_den_eq_one
  given: {q : Rat} (hq : q.den = 1)
  statement: (q.num : Rat) = q
  proof: by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl

中文:
定理 coe_int_num_of_den_eq_one
  条件: {q : Rat} (hq : q.den = 1)
  结论: (q.num : Rat) = q
  证明: by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl

Depends on / 依赖: conv_rhs, intCast_eq_divInt, num_divInt_den
-/
theorem coe_int_num_of_den_eq_one {q : Rat} (hq : q.den = 1) : (q.num : Rat) = q := by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl

/--
lemma `eq_num_of_isInt` / 引理 `eq_num_of_isInt`

English:
lemma eq_num_of_isInt
  given: {q : Rat} (h : q.isInt)
  statement: q = q.num
  proof: by
  rw [Rat.isInt]; rw [Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

中文:
引理 eq_num_of_isInt
  条件: {q : Rat} (h : q.is整数)
  结论: q = q.num
  证明: by
  rw [Rat.isInt]; rw [Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

Depends on / 依赖: Nat.beq_eq_true_eq, Rat.coe_int_num_of_den_eq_one, Rat.isInt, beq_eq_true_eq, coe_int_num_of_den_eq_one
-/
lemma eq_num_of_isInt {q : Rat} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt]; rw [Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

/--
theorem `den_eq_one_iff` / 定理 `den_eq_one_iff`

English:
theorem den_eq_one_iff
  given: (r : Rat)
  statement: r.den = 1 ↔ ↑r.num = r
  proof: ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

中文:
定理 den_eq_one_iff
  条件: (r : Rat)
  结论: r.den = 1 ↔ ↑r.num = r
  证明: ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

Depends on / 依赖: Rat.coe_int_num_of_den_eq_one, Rat.den_intCast, coe_int_num_of_den_eq_one, den_intCast, r.num
-/
theorem den_eq_one_iff (r : Rat) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Rat Int (↑) fun q => q.den = 1
  body: ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

@[deprecated (since := "2026-06-06")] alias coe_int_inj := intCast_inj

中文:
实例 canLift
  签名: : CanLift Rat 整数 (↑) fun q => q.den = 1
  定义体: ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

@[deprecated (since := "2026-06-06")] alias coe_int_inj := intCast_inj

Depends on / 依赖: coe_int_num_of_den_eq_one, q.num
-/
instance canLift : CanLift Rat Int (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

@[deprecated (since := "2026-06-06")] alias coe_int_inj := intCast_inj

end Casts

/--
A version of `Rat.casesOn` that uses `/` instead of `Rat.mk'`. Use as
```lean
cases r with
| div p q nonzero coprime =>
```
-/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `divCasesOn` / `divCasesOn` 的定义

English:
definition divCasesOn
  signature: {C : Rat -> Sort*} (a : Rat)
  body: a.casesOn fun n d nz red => by rw [Rat.mk_eq_divInt, Rat.divInt_eq_div]; exact div n d nz red

中文:
定义 divCasesOn
  签名: {C : Rat -> Sort*} (a : Rat)
  定义体: a.casesOn fun n d nz red => by rw [Rat.mk_eq_divInt, Rat.divInt_eq_div]; exact div n d nz red

Depends on / 依赖: Rat.divInt_eq_div, Rat.mk_eq_divInt, a.casesOn, casesOn, divInt_eq_div, mk_eq_divInt
-/
def divCasesOn {C : Rat -> Sort*} (a : Rat)
    (div : forall (n : Int) (d : Nat), d != 0 -> n.natAbs.Coprime d -> C (n / d)) : C a :=
  a.casesOn fun n d nz red => by rw [Rat.mk_eq_divInt, Rat.divInt_eq_div]; exact div n d nz red

end Rat
