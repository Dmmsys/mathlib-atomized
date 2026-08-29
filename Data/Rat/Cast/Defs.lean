/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Order.Nat

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

@[expose] public section

assert_not_exists MulAction IsOrderedMonoid

variable {F ι α β : Type*}

namespace NNRat
variable [DivisionSemiring α] {q r : Rat>=0}

/--
lemma `cast_natCast` / 引理 `cast_natCast`

English:
lemma cast_natCast
  given: (n : Nat)
  statement: ((n : Rat>=0) : α) = n
  proof: by simp [cast_def]

中文:
引理 cast_natCast
  条件: (n : 自然数)
  结论: ((n : 有理数>=0) : α) = n
  证明: by simp [cast_def]
-/
@[simp, norm_cast] lemma cast_natCast (n : Nat) : ((n : Rat>=0) : α) = n := by simp [cast_def]

/--
lemma `cast_ofNat` / 引理 `cast_ofNat`

English:
lemma cast_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: cast_natCast _

中文:
引理 cast_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: cast_natCast _
-/
@[simp, norm_cast] lemma cast_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : Rat>=0) = (ofNat(n) : α) := cast_natCast _

/--
lemma `cast_zero` / 引理 `cast_zero`

English:
lemma cast_zero
  statement: ((0 : Rat>=0) : α) = 0
  proof: (cast_natCast _).trans Nat.cast_zero

中文:
引理 cast_zero
  结论: ((0 : 有理数>=0) : α) = 0
  证明: (cast_natCast _).trans Nat.cast_zero
-/
@[simp, norm_cast] lemma cast_zero : ((0 : Rat>=0) : α) = 0 := (cast_natCast _).trans Nat.cast_zero
/--
lemma `cast_one` / 引理 `cast_one`

English:
lemma cast_one
  statement: ((1 : Rat>=0) : α) = 1
  proof: (cast_natCast _).trans Nat.cast_one

中文:
引理 cast_one
  结论: ((1 : 有理数>=0) : α) = 1
  证明: (cast_natCast _).trans Nat.cast_one
-/
@[simp, norm_cast] lemma cast_one : ((1 : Rat>=0) : α) = 1 := (cast_natCast _).trans Nat.cast_one

/--
lemma `cast_commute` / 引理 `cast_commute`

English:
lemma cast_commute
  given: (q : Rat>=0) (a : α)
  statement: Commute (↑q) a
  proof: by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)

中文:
引理 cast_commute
  条件: (q : 有理数>=0) (a : α)
  结论: Commute (↑q) a
  证明: by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)

Depends on / 依赖: cast_commute, cast_def, div_left, q.den.cast_commute, q.num.cast_commute
-/
lemma cast_commute (q : Rat>=0) (a : α) : Commute (↑q) a := by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)

/--
lemma `commute_cast` / 引理 `commute_cast`

English:
lemma commute_cast
  given: (a : α) (q : Rat>=0)
  statement: Commute a q
  proof: (cast_commute ..).symm

中文:
引理 commute_cast
  条件: (a : α) (q : 有理数>=0)
  结论: Commute a q
  证明: (cast_commute ..).symm

Depends on / 依赖: cast_commute
-/
lemma commute_cast (a : α) (q : Rat>=0) : Commute a q := (cast_commute ..).symm

/--
lemma `cast_comm` / 引理 `cast_comm`

English:
lemma cast_comm
  given: (q : Rat>=0) (a : α)
  statement: q * a = a * q
  proof: cast_commute _ _

中文:
引理 cast_comm
  条件: (q : 有理数>=0) (a : α)
  结论: q * a = a * q
  证明: cast_commute _ _

Depends on / 依赖: cast_commute
-/
lemma cast_comm (q : Rat>=0) (a : α) : q * a = a * q := cast_commute _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cast_divNat_of_ne_zero` / 引理 `cast_divNat_of_ne_zero`

English:
lemma cast_divNat_of_ne_zero
  given: (a : Nat) {b : Nat} (hb : (b : α) != 0)
  proof: by
  rcases e : divNat a b with ⟨⟨n, d, h, c⟩, hn⟩
  rw [← Rat.num_nonneg] at hn
  lift n to Nat using hn
  have hd : (d : α) != 0 := by
    refine fun hd => hb ?_
    have : Rat.divInt a b = _ := congr_arg NNRat.cast e
    obtain ⟨k, rfl⟩ : d ∣ b := by simpa [Int.natCast_dvd_natCast, this] using Rat.den_dvd a b
    simp [*]
  have hb' : b != 0 := by rintro rfl; exact hb Nat.cast_zero
  simp_rw [Rat.mk_eq_divInt, mk_divInt, divNat_inj hb' h] at e
  rw [cast_def]
  dsimp
  rw [Commute.div_eq_div_iff _ hd hb]
  · norm_cast
    rw [e]
  exact b.commute_cast _

@[norm_cast]

中文:
引理 cast_div自然数_of_ne_zero
  条件: (a : 自然数) {b : 自然数} (hb : (b : α) != 0)
  证明: by
  rcases e : divNat a b with ⟨⟨n, d, h, c⟩, hn⟩
  rw [← Rat.num_nonneg] at hn
  lift n to Nat using hn
  have hd : (d : α) != 0 := by
    refine fun hd => hb ?_
    have : Rat.divInt a b = _ := congr_arg NNRat.cast e
    obtain ⟨k, rfl⟩ : d ∣ b := by simpa [Int.natCast_dvd_natCast, this] using Rat.den_dvd a b
    simp [*]
  have hb' : b != 0 := by rintro rfl; exact hb Nat.cast_zero
  simp_rw [Rat.mk_eq_divInt, mk_divInt, divNat_inj hb' h] at e
  rw [cast_def]
  dsimp
  rw [Commute.div_eq_div_iff _ hd hb]
  · norm_cast
    rw [e]
  exact b.commute_cast _

@[norm_cast]
-/
@[norm_cast] lemma cast_divNat_of_ne_zero (a : Nat) {b : Nat} (hb : (b : α) != 0) :
    divNat a b = (a / b : α) := by
  rcases e : divNat a b with ⟨⟨n, d, h, c⟩, hn⟩
  rw [← Rat.num_nonneg] at hn
  lift n to Nat using hn
  have hd : (d : α) != 0 := by
    refine fun hd => hb ?_
    have : Rat.divInt a b = _ := congr_arg NNRat.cast e
    obtain ⟨k, rfl⟩ : d ∣ b := by simpa [Int.natCast_dvd_natCast, this] using Rat.den_dvd a b
    simp [*]
  have hb' : b != 0 := by rintro rfl; exact hb Nat.cast_zero
  simp_rw [Rat.mk_eq_divInt, mk_divInt, divNat_inj hb' h] at e
  rw [cast_def]
  dsimp
  rw [Commute.div_eq_div_iff _ hd hb]
  · norm_cast
    rw [e]
  exact b.commute_cast _

@[norm_cast]
/--
lemma `cast_add_of_ne_zero` / 引理 `cast_add_of_ne_zero`

English:
lemma cast_add_of_ne_zero
  given: (hq : (q.den : α) != 0) (hr : (r.den : α) != 0)
  proof: by
  rw [add_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [mul_comm _ q.den]; rw [(Nat.commute_cast _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]

中文:
引理 cast_add_of_ne_zero
  条件: (hq : (q.den : α) != 0) (hr : (r.den : α) != 0)
  证明: by
  rw [add_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [mul_comm _ q.den]; rw [(Nat.commute_cast _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]

Depends on / 依赖: Nat.commute_cast, add_def, cast_def, cast_divNat_of_ne_zero, commute_cast, div_add_div, mul_comm, mul_ne_zero, q.den
-/
lemma cast_add_of_ne_zero (hq : (q.den : α) != 0) (hr : (r.den : α) != 0) :
    ↑(q + r) = (q + r : α) := by
  rw [add_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [mul_comm _ q.den]; rw [(Nat.commute_cast _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]
/--
lemma `cast_mul_of_ne_zero` / 引理 `cast_mul_of_ne_zero`

English:
lemma cast_mul_of_ne_zero
  given: (hq : (q.den : α) != 0) (hr : (r.den : α) != 0)
  proof: by
  rw [mul_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]

中文:
引理 cast_mul_of_ne_zero
  条件: (hq : (q.den : α) != 0) (hr : (r.den : α) != 0)
  证明: by
  rw [mul_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]

Depends on / 依赖: Nat.commute_cast, cast_def, cast_divNat_of_ne_zero, commute_cast, div_mul_div_comm, mul_def, mul_ne_zero
-/
lemma cast_mul_of_ne_zero (hq : (q.den : α) != 0) (hr : (r.den : α) != 0) :
    ↑(q * r) = (q * r : α) := by
  rw [mul_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]
/--
lemma `cast_inv_of_ne_zero` / 引理 `cast_inv_of_ne_zero`

English:
lemma cast_inv_of_ne_zero
  given: (hq : (q.num : α) != 0)
  statement: (q⁻¹ : Rat>=0) = (q⁻¹ : α)
  proof: by
  rw [inv_def]; rw [cast_divNat_of_ne_zero _ hq]; rw [cast_def]; rw [inv_div]

@[norm_cast]

中文:
引理 cast_inv_of_ne_zero
  条件: (hq : (q.num : α) != 0)
  结论: (q⁻¹ : 有理数>=0) = (q⁻¹ : α)
  证明: by
  rw [inv_def]; rw [cast_divNat_of_ne_zero _ hq]; rw [cast_def]; rw [inv_div]

@[norm_cast]

Depends on / 依赖: cast_def, cast_divNat_of_ne_zero, inv_def, inv_div
-/
lemma cast_inv_of_ne_zero (hq : (q.num : α) != 0) : (q⁻¹ : Rat>=0) = (q⁻¹ : α) := by
  rw [inv_def]; rw [cast_divNat_of_ne_zero _ hq]; rw [cast_def]; rw [inv_div]

@[norm_cast]
/--
lemma `cast_div_of_ne_zero` / 引理 `cast_div_of_ne_zero`

English:
lemma cast_div_of_ne_zero
  given: (hq : (q.den : α) != 0) (hr : (r.num : α) != 0)
  proof: by
  rw [div_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [div_eq_mul_inv (_ / _)]; rw [inv_div]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

中文:
引理 cast_div_of_ne_zero
  条件: (hq : (q.den : α) != 0) (hr : (r.num : α) != 0)
  证明: by
  rw [div_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [div_eq_mul_inv (_ / _)]; rw [inv_div]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

Depends on / 依赖: Nat.commute_cast, cast_def, cast_divNat_of_ne_zero, commute_cast, div_def, div_eq_mul_inv, div_mul_div_comm, inv_div, mul_ne_zero
-/
lemma cast_div_of_ne_zero (hq : (q.den : α) != 0) (hr : (r.num : α) != 0) :
    ↑(q / r) = (q / r : α) := by
  rw [div_def]; rw [cast_divNat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [div_eq_mul_inv (_ / _)]; rw [inv_div]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

end NNRat

namespace Rat

variable [DivisionRing α] {p q : Rat}

@[simp, norm_cast]
/--
theorem `cast_intCast` / 定理 `cast_intCast`

English:
theorem cast_intCast
  given: (n : Int)
  statement: ((n : Rat) : α) = n
  proof: (cast_def _).trans show (n / (1 : Nat) : α) = n by rw [Nat.cast_one, div_one]

@[simp, norm_cast]

中文:
定理 cast_intCast
  条件: (n : 整数)
  结论: ((n : 有理数) : α) = n
  证明: (cast_def _).trans show (n / (1 : Nat) : α) = n by rw [Nat.cast_one, div_one]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_one, cast_def, cast_one, div_one
-/
theorem cast_intCast (n : Int) : ((n : Rat) : α) = n :=
(cast_def _).trans show (n / (1 : Nat) : α) = n by rw [Nat.cast_one, div_one]

@[simp, norm_cast]
/--
theorem `cast_natCast` / 定理 `cast_natCast`

English:
theorem cast_natCast
  given: (n : Nat)
  statement: ((n : Rat) : α) = n
  proof: by
  rw [← Int.cast_natCast]; rw [cast_intCast]; rw [Int.cast_natCast]

中文:
定理 cast_natCast
  条件: (n : 自然数)
  结论: ((n : 有理数) : α) = n
  证明: by
  rw [← Int.cast_natCast]; rw [cast_intCast]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, cast_intCast, cast_natCast
-/
theorem cast_natCast (n : Nat) : ((n : Rat) : α) = n := by
  rw [← Int.cast_natCast]; rw [cast_intCast]; rw [Int.cast_natCast]


/--
lemma `cast_ofNat` / 引理 `cast_ofNat`

English:
lemma cast_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: by
  simp [cast_def]

@[simp, norm_cast]

中文:
引理 cast_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: by
  simp [cast_def]

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma cast_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : Rat) : α) = (ofNat(n) : α) := by
  simp [cast_def]

@[simp, norm_cast]
/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  statement: ((0 : Rat) : α) = 0
  proof: (cast_intCast _).trans Int.cast_zero

@[simp, norm_cast]

中文:
定理 cast_zero
  结论: ((0 : 有理数) : α) = 0
  证明: (cast_intCast _).trans Int.cast_zero

@[simp, norm_cast]

Depends on / 依赖: Int.cast_zero, cast_intCast, cast_zero
-/
theorem cast_zero : ((0 : Rat) : α) = 0 :=
  (cast_intCast _).trans Int.cast_zero

@[simp, norm_cast]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  statement: ((1 : Rat) : α) = 1
  proof: (cast_intCast _).trans Int.cast_one

中文:
定理 cast_one
  结论: ((1 : 有理数) : α) = 1
  证明: (cast_intCast _).trans Int.cast_one

Depends on / 依赖: Int.cast_one, cast_intCast, cast_one
-/
theorem cast_one : ((1 : Rat) : α) = 1 :=
  (cast_intCast _).trans Int.cast_one

/--
theorem `cast_commute` / 定理 `cast_commute`

English:
theorem cast_commute
  given: (r : Rat) (a : α)
  statement: Commute (↑r) a
  proof: by
  simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)

中文:
定理 cast_commute
  条件: (r : 有理数) (a : α)
  结论: Commute (↑r) a
  证明: by
  simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)

Depends on / 依赖: cast_commute, cast_def, div_left
-/
theorem cast_commute (r : Rat) (a : α) : Commute (↑r) a := by
  simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)

/--
theorem `cast_comm` / 定理 `cast_comm`

English:
theorem cast_comm
  given: (r : Rat) (a : α)
  statement: (r : α) * a = a * r
  proof: (cast_commute r a).eq

中文:
定理 cast_comm
  条件: (r : 有理数) (a : α)
  结论: (r : α) * a = a * r
  证明: (cast_commute r a).eq

Depends on / 依赖: cast_commute
-/
theorem cast_comm (r : Rat) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).eq

/--
theorem `commute_cast` / 定理 `commute_cast`

English:
theorem commute_cast
  given: (a : α) (r : Rat)
  statement: Commute a r
  proof: (r.cast_commute a).symm

@[norm_cast]

中文:
定理 commute_cast
  条件: (a : α) (r : 有理数)
  结论: Commute a r
  证明: (r.cast_commute a).symm

@[norm_cast]

Depends on / 依赖: cast_commute, r.cast_commute
-/
theorem commute_cast (a : α) (r : Rat) : Commute a r :=
  (r.cast_commute a).symm

@[norm_cast]
/--
lemma `cast_divInt_of_ne_zero` / 引理 `cast_divInt_of_ne_zero`

English:
lemma cast_divInt_of_ne_zero
  given: (a : Int) {b : Int} (b0 : (b : α) != 0)
  statement: (a /. b : α) = a / b
  proof: by
  have b0' : b != 0 := by
    refine mt ?_ b0
    simp +contextual
  rcases e : a /. b with ⟨n, d, h, c⟩
  have d0 : (d : α) != 0 := by
    intro d0
    have dd := den_dvd a b
    rcases show (d : Int) ∣ b by rwa [e] at dd with ⟨k, ke⟩
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_natCast]
    rw [d0]; rw [zero_mul] at this
    contradiction
  rw [mk_eq_divInt] at e
  have := congr_arg ((↑) : Int -> α)
    ((divInt_eq_divInt_iff b0' <| ne_of_gt <| Int.natCast_pos.2 h.bot_lt).1 e)
  rw [Int.cast_mul]; rw [Int.cast_mul]; rw [Int.cast_natCast] at this
  rw [eq_comm]; rw [cast_def]; rw [div_eq_mul_inv]; rw [eq_div_iff_mul_eq d0]; rw [mul_assoc]; rw [(d.commute_cast _).eq]; rw [← mul_assoc]; rw [this]; rw [mul_assoc]; rw [mul_inv_cancel₀ b0]; rw [mul_one]

@[norm_cast]

中文:
引理 cast_div整数_of_ne_zero
  条件: (a : 整数) {b : 整数} (b0 : (b : α) != 0)
  结论: (a /. b : α) = a / b
  证明: by
  have b0' : b != 0 := by
    refine mt ?_ b0
    simp +contextual
  rcases e : a /. b with ⟨n, d, h, c⟩
  have d0 : (d : α) != 0 := by
    intro d0
    have dd := den_dvd a b
    rcases show (d : Int) ∣ b by rwa [e] at dd with ⟨k, ke⟩
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_natCast]
    rw [d0]; rw [zero_mul] at this
    contradiction
  rw [mk_eq_divInt] at e
  have := congr_arg ((↑) : Int -> α)
    ((divInt_eq_divInt_iff b0' <| ne_of_gt <| Int.natCast_pos.2 h.bot_lt).1 e)
  rw [Int.cast_mul]; rw [Int.cast_mul]; rw [Int.cast_natCast] at this
  rw [eq_comm]; rw [cast_def]; rw [div_eq_mul_inv]; rw [eq_div_iff_mul_eq d0]; rw [mul_assoc]; rw [(d.commute_cast _).eq]; rw [← mul_assoc]; rw [this]; rw [mul_assoc]; rw [mul_inv_cancel₀ b0]; rw [mul_one]

@[norm_cast]

Depends on / 依赖: Int.c, Int.cast_mul, Int.cast_natCast, Int.natCast_pos, bot_lt, cast_mul, cast_natCast, congr_arg, contextual, den_dvd, divInt_eq_divInt_iff, h.bot_lt, mk_eq_divInt, natCast_pos, ne_of_gt, zero_mul
-/
lemma cast_divInt_of_ne_zero (a : Int) {b : Int} (b0 : (b : α) != 0) : (a /. b : α) = a / b := by
  have b0' : b != 0 := by
    refine mt ?_ b0
    simp +contextual
  rcases e : a /. b with ⟨n, d, h, c⟩
  have d0 : (d : α) != 0 := by
    intro d0
    have dd := den_dvd a b
    rcases show (d : Int) ∣ b by rwa [e] at dd with ⟨k, ke⟩
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_natCast]
    rw [d0]; rw [zero_mul] at this
    contradiction
  rw [mk_eq_divInt] at e
  have := congr_arg ((↑) : Int -> α)
    ((divInt_eq_divInt_iff b0' <| ne_of_gt <| Int.natCast_pos.2 h.bot_lt).1 e)
  rw [Int.cast_mul]; rw [Int.cast_mul]; rw [Int.cast_natCast] at this
  rw [eq_comm]; rw [cast_def]; rw [div_eq_mul_inv]; rw [eq_div_iff_mul_eq d0]; rw [mul_assoc]; rw [(d.commute_cast _).eq]; rw [← mul_assoc]; rw [this]; rw [mul_assoc]; rw [mul_inv_cancel₀ b0]; rw [mul_one]

@[norm_cast]
/--
lemma `cast_mkRat_of_ne_zero` / 引理 `cast_mkRat_of_ne_zero`

English:
lemma cast_mkRat_of_ne_zero
  given: (a : Int) {b : Nat} (hb : (b : α) != 0)
  statement: (mkRat a b : α) = a / b
  proof: by
  rw [Rat.mkRat_eq_divInt]; rw [cast_divInt_of_ne_zero]; rw [Int.cast_natCast]; rwa [Int.cast_natCast]

@[norm_cast]

中文:
引理 cast_mkRat_of_ne_zero
  条件: (a : 整数) {b : 自然数} (hb : (b : α) != 0)
  结论: (mkRat a b : α) = a / b
  证明: by
  rw [Rat.mkRat_eq_divInt]; rw [cast_divInt_of_ne_zero]; rw [Int.cast_natCast]; rwa [Int.cast_natCast]

@[norm_cast]

Depends on / 依赖: Int.cast_natCast, Rat.mkRat_eq_divInt, cast_divInt_of_ne_zero, cast_natCast, mkRat_eq_divInt
-/
lemma cast_mkRat_of_ne_zero (a : Int) {b : Nat} (hb : (b : α) != 0) : (mkRat a b : α) = a / b := by
  rw [Rat.mkRat_eq_divInt]; rw [cast_divInt_of_ne_zero]; rw [Int.cast_natCast]; rwa [Int.cast_natCast]

@[norm_cast]
/--
lemma `cast_add_of_ne_zero` / 引理 `cast_add_of_ne_zero`

English:
lemma cast_add_of_ne_zero
  given: {q r : Rat} (hq : (q.den : α) != 0) (hr : (r.den : α) != 0)
  proof: by
  rw [add_def']; rw [cast_mkRat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [mul_comm r.num]; rw [(Nat.cast_commute _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

中文:
引理 cast_add_of_ne_zero
  条件: {q r : 有理数} (hq : (q.den : α) != 0) (hr : (r.den : α) != 0)
  证明: by
  rw [add_def']; rw [cast_mkRat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [mul_comm r.num]; rw [(Nat.cast_commute _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

Depends on / 依赖: Nat.cast_commute, Nat.commute_cast, add_def, cast_commute, cast_def, cast_mkRat_of_ne_zero, commute_cast, div_add_div, mul_comm, mul_ne_zero, r.num
-/
lemma cast_add_of_ne_zero {q r : Rat} (hq : (q.den : α) != 0) (hr : (r.den : α) != 0) :
    (q + r : Rat) = (q + r : α) := by
  rw [add_def']; rw [cast_mkRat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [mul_comm r.num]; rw [(Nat.cast_commute _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

/--
lemma `cast_neg` / 引理 `cast_neg`

English:
lemma cast_neg
  given: (q : Rat)
  statement: ↑(-q) = (-q : α)
  proof: by simp [cast_def, neg_div]

中文:
引理 cast_neg
  条件: (q : 有理数)
  结论: ↑(-q) = (-q : α)
  证明: by simp [cast_def, neg_div]
-/
@[simp, norm_cast] lemma cast_neg (q : Rat) : ↑(-q) = (-q : α) := by simp [cast_def, neg_div]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cast_sub_of_ne_zero` / 引理 `cast_sub_of_ne_zero`

English:
lemma cast_sub_of_ne_zero
  given: (hp : (p.den : α) != 0) (hq : (q.den : α) != 0)
  proof: by simp [sub_eq_add_neg, cast_add_of_ne_zero, hp, hq]

中文:
引理 cast_sub_of_ne_zero
  条件: (hp : (p.den : α) != 0) (hq : (q.den : α) != 0)
  证明: by simp [sub_eq_add_neg, cast_add_of_ne_zero, hp, hq]
-/
@[norm_cast] lemma cast_sub_of_ne_zero (hp : (p.den : α) != 0) (hq : (q.den : α) != 0) :
    ↑(p - q) = (p - q : α) := by simp [sub_eq_add_neg, cast_add_of_ne_zero, hp, hq]

/--
lemma `cast_mul_of_ne_zero` / 引理 `cast_mul_of_ne_zero`

English:
lemma cast_mul_of_ne_zero
  given: (hp : (p.den : α) != 0) (hq : (q.den : α) != 0)
  proof: by
  rw [mul_eq_mkRat]; rw [cast_mkRat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Int.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

@[norm_cast]

中文:
引理 cast_mul_of_ne_zero
  条件: (hp : (p.den : α) != 0) (hq : (q.den : α) != 0)
  证明: by
  rw [mul_eq_mkRat]; rw [cast_mkRat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Int.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

@[norm_cast]
-/
@[norm_cast] lemma cast_mul_of_ne_zero (hp : (p.den : α) != 0) (hq : (q.den : α) != 0) :
    ↑(p * q) = (p * q : α) := by
  rw [mul_eq_mkRat]; rw [cast_mkRat_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [(Nat.commute_cast _ _).div_mul_div_comm (Int.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

@[norm_cast]
/--
lemma `cast_inv_of_ne_zero` / 引理 `cast_inv_of_ne_zero`

English:
lemma cast_inv_of_ne_zero
  given: (hq : (q.num : α) != 0)
  statement: ↑(q⁻¹) = (q⁻¹ : α)
  proof: by
  rw [inv_def]; rw [cast_divInt_of_ne_zero _ hq]; rw [cast_def]; rw [inv_div]; rw [Int.cast_natCast]

中文:
引理 cast_inv_of_ne_zero
  条件: (hq : (q.num : α) != 0)
  结论: ↑(q⁻¹) = (q⁻¹ : α)
  证明: by
  rw [inv_def]; rw [cast_divInt_of_ne_zero _ hq]; rw [cast_def]; rw [inv_div]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, cast_def, cast_divInt_of_ne_zero, cast_natCast, inv_def, inv_div
-/
lemma cast_inv_of_ne_zero (hq : (q.num : α) != 0) : ↑(q⁻¹) = (q⁻¹ : α) := by
  rw [inv_def]; rw [cast_divInt_of_ne_zero _ hq]; rw [cast_def]; rw [inv_div]; rw [Int.cast_natCast]

/--
lemma `cast_div_of_ne_zero` / 引理 `cast_div_of_ne_zero`

English:
lemma cast_div_of_ne_zero
  given: (hp : (p.den : α) != 0) (hq : (q.num : α) != 0)
  proof: by
  rw [div_def']; rw [cast_divInt_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [div_eq_mul_inv (_ / _)]; rw [inv_div]; rw [(Int.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

中文:
引理 cast_div_of_ne_zero
  条件: (hp : (p.den : α) != 0) (hq : (q.num : α) != 0)
  证明: by
  rw [div_def']; rw [cast_divInt_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [div_eq_mul_inv (_ / _)]; rw [inv_div]; rw [(Int.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq
-/
@[norm_cast] lemma cast_div_of_ne_zero (hp : (p.den : α) != 0) (hq : (q.num : α) != 0) :
    ↑(p / q) = (p / q : α) := by
  rw [div_def']; rw [cast_divInt_of_ne_zero]; rw [cast_def]; rw [cast_def]; rw [div_eq_mul_inv (_ / _)]; rw [inv_div]; rw [(Int.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

end Rat

open Rat

variable [FunLike F α β]

/--
lemma `map_nnratCast` / 引理 `map_nnratCast`

English:
lemma map_nnratCast
  statement: [DivisionSemiring α] [DivisionSemiring β] [RingHomClass F α β] (f : F)
  proof: by simp_rw [NNRat.cast_def, map_div₀, map_natCast]

@[simp]

中文:
引理 map_nnratCast
  结论: [除半环 α] [除半环 β] [环态射类 F α β] (f : F)
  证明: by simp_rw [NNRat.cast_def, map_div₀, map_natCast]

@[simp]
-/
@[simp] lemma map_nnratCast [DivisionSemiring α] [DivisionSemiring β] [RingHomClass F α β] (f : F)
    (q : Rat>=0) : f q = q := by simp_rw [NNRat.cast_def, map_div₀, map_natCast]

@[simp]
/--
lemma `eq_nnratCast` / 引理 `eq_nnratCast`

English:
lemma eq_nnratCast
  given: [DivisionSemiring α] [FunLike F Rat>=0 α] [RingHomClass F Rat>=0 α] (f : F) (q : Rat>=0)
  proof: by rw [← map_nnratCast f, NNRat.cast_id]

@[simp]

中文:
引理 eq_nnratCast
  条件: [除半环 α] [函数状 F 有理数>=0 α] [环态射类 F 有理数>=0 α] (f : F) (q : 有理数>=0)
  证明: by rw [← map_nnratCast f, NNRat.cast_id]

@[simp]

Depends on / 依赖: NNRat.cast_id, cast_id, map_nnratCast
-/
lemma eq_nnratCast [DivisionSemiring α] [FunLike F Rat>=0 α] [RingHomClass F Rat>=0 α] (f : F) (q : Rat>=0) :
    f q = q := by rw [← map_nnratCast f, NNRat.cast_id]

@[simp]
/--
theorem `map_ratCast` / 定理 `map_ratCast`

English:
theorem map_ratCast
  given: [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : Rat)
  proof: by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]

中文:
定理 map_ratCast
  条件: [除环 α] [除环 β] [环态射类 F α β] (f : F) (q : 有理数)
  证明: by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]

Depends on / 依赖: cast_def, map_intCast, map_natCast
-/
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : Rat) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]

/--
lemma `eq_ratCast` / 引理 `eq_ratCast`

English:
lemma eq_ratCast
  given: [DivisionRing α] [FunLike F Rat α] [RingHomClass F Rat α] (f : F) (q : Rat)
  proof: by rw [← map_ratCast f, Rat.cast_id]

中文:
引理 eq_ratCast
  条件: [除环 α] [函数状 F 有理数 α] [环态射类 F 有理数 α] (f : F) (q : 有理数)
  证明: by rw [← map_ratCast f, Rat.cast_id]
-/
@[simp] lemma eq_ratCast [DivisionRing α] [FunLike F Rat α] [RingHomClass F Rat α] (f : F) (q : Rat) :
    f q = q := by rw [← map_ratCast f, Rat.cast_id]

namespace MonoidWithZeroHomClass

variable {M₀ : Type*} [MonoidWithZero M₀]

section NNRat
variable [FunLike F Rat>=0 M₀] [MonoidWithZeroHomClass F Rat>=0 M₀] {f g : F}

/--
lemma `ext_nnrat'` / 引理 `ext_nnrat'`

English:
lemma ext_nnrat'
  given: (h : forall n : Nat, f n = g n)
  statement: f = g
  proof: (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den]; rw [div_eq_mul_inv]; rw [map_mul]; rw [map_mul]; rw [h]; rw [eq_on_inv₀ f g]
    apply h

中文:
引理 ext_nnrat'
  条件: (h : 对任意 n : 自然数, f n = g n)
  结论: f = g
  证明: (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den]; rw [div_eq_mul_inv]; rw [map_mul]; rw [map_mul]; rw [h]; rw [eq_on_inv₀ f g]
    apply h

Depends on / 依赖: DFunLike, DFunLike.ext, div_eq_mul_inv, map_mul, num_div_den, r.num_div_den
-/
lemma ext_nnrat' (h : forall n : Nat, f n = g n) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den]; rw [div_eq_mul_inv]; rw [map_mul]; rw [map_mul]; rw [h]; rw [eq_on_inv₀ f g]
    apply h

/-- If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the naturals then they are equal.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
/--
lemma `ext_nnrat` / 引理 `ext_nnrat`

English:
lemma ext_nnrat
  statement: {f g : Rat>=0 ->*₀ M₀} (h : f.comp (.ofClass (Nat.castRingHom Rat>=0)) =
  proof: ext_nnrat' DFunLike.congr_fun h

中文:
引理 ext_nnrat
  结论: {f g : 有理数>=0 ->*₀ M₀} (h : f.comp (.ofClass (自然数.castRingHom 有理数>=0)) =
  证明: ext_nnrat' DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, ext_nnrat
-/
lemma ext_nnrat {f g : Rat>=0 ->*₀ M₀} (h : f.comp (.ofClass (Nat.castRingHom Rat>=0)) =
    g.comp (.ofClass (Nat.castRingHom Rat>=0))) : f = g :=
ext_nnrat' DFunLike.congr_fun h

/--
lemma `ext_nnrat_on_pnat` / 引理 `ext_nnrat_on_pnat`

English:
lemma ext_nnrat_on_pnat
  given: (same_on_pnat : forall n : Nat, 0 < n -> f n = g n)
  statement: f = g
  proof: ext_nnrat' DFunLike.congr_fun ext_nat''
    ((.ofClass f : Rat>=0 ->*₀ M₀).comp (.ofClass (Nat.castRingHom Rat>=0)))
    ((.ofClass g : Rat>=0 ->*₀ M₀).comp (.ofClass (Nat.castRingHom Rat>=0))) (by simpa)

中文:
引理 ext_nnrat_on_pnat
  条件: (same_on_pnat : 对任意 n : 自然数, 0 < n -> f n = g n)
  结论: f = g
  证明: ext_nnrat' DFunLike.congr_fun ext_nat''
    ((.ofClass f : Rat>=0 ->*₀ M₀).comp (.ofClass (Nat.castRingHom Rat>=0)))
    ((.ofClass g : Rat>=0 ->*₀ M₀).comp (.ofClass (Nat.castRingHom Rat>=0))) (by simpa)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Nat.castRingHom, castRingHom, congr_fun, ext_nat, ext_nnrat, ofClass
-/
lemma ext_nnrat_on_pnat (same_on_pnat : forall n : Nat, 0 < n -> f n = g n) : f = g :=
ext_nnrat' DFunLike.congr_fun ext_nat''
    ((.ofClass f : Rat>=0 ->*₀ M₀).comp (.ofClass (Nat.castRingHom Rat>=0)))
    ((.ofClass g : Rat>=0 ->*₀ M₀).comp (.ofClass (Nat.castRingHom Rat>=0))) (by simpa)

end NNRat

section Rat
variable [FunLike F Rat M₀] [MonoidWithZeroHomClass F Rat M₀] {f g : F}

/--
theorem `ext_rat'` / 定理 `ext_rat'`

English:
theorem ext_rat'
  given: (h : forall m : Int, f m = g m)
  statement: f = g
  proof: (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den]; rw [div_eq_mul_inv]; rw [map_mul]; rw [map_mul]; rw [h]; rw [← Int.cast_natCast]; rw [eq_on_inv₀ f g]
    apply h

中文:
定理 ext_rat'
  条件: (h : 对任意 m : 整数, f m = g m)
  结论: f = g
  证明: (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den]; rw [div_eq_mul_inv]; rw [map_mul]; rw [map_mul]; rw [h]; rw [← Int.cast_natCast]; rw [eq_on_inv₀ f g]
    apply h

Depends on / 依赖: DFunLike, DFunLike.ext, Int.cast_natCast, cast_natCast, div_eq_mul_inv, map_mul, num_div_den, r.num_div_den
-/
theorem ext_rat' (h : forall m : Int, f m = g m) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den]; rw [div_eq_mul_inv]; rw [map_mul]; rw [map_mul]; rw [h]; rw [← Int.cast_natCast]; rw [eq_on_inv₀ f g]
    apply h

/-- If monoid with zero homs `f` and `g` from `ℚ` agree on the integers then they are equal.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
/--
theorem `ext_rat` / 定理 `ext_rat`

English:
theorem ext_rat
  statement: {f g : Rat ->*₀ M₀}
  proof: ext_rat' DFunLike.congr_fun h

中文:
定理 ext_rat
  结论: {f g : 有理数 ->*₀ M₀}
  证明: ext_rat' DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, ext_rat
-/
theorem ext_rat {f g : Rat ->*₀ M₀}
    (h : f.comp (.ofClass (Int.castRingHom Rat)) = g.comp (.ofClass (Int.castRingHom Rat))) : f = g :=
ext_rat' DFunLike.congr_fun h

/--
theorem `ext_rat_on_pnat` / 定理 `ext_rat_on_pnat`

English:
theorem ext_rat_on_pnat
  statement: (same_on_neg_one : f (-1) = g (-1))
  proof: ext_rat'
DFunLike.congr_fun
      show
        (.ofClass f : Rat ->*₀ M₀).comp (.ofClass (Int.castRingHom Rat)) =
          (.ofClass g : Rat ->*₀ M₀).comp (.ofClass (Int.castRingHom Rat))
        from ext_int' (by simpa) (by simpa)

中文:
定理 ext_rat_on_pnat
  结论: (same_on_neg_one : f (-1) = g (-1))
  证明: ext_rat'
DFunLike.congr_fun
      show
        (.ofClass f : Rat ->*₀ M₀).comp (.ofClass (Int.castRingHom Rat)) =
          (.ofClass g : Rat ->*₀ M₀).comp (.ofClass (Int.castRingHom Rat))
        from ext_int' (by simpa) (by simpa)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Int.castRingHom, castRingHom, congr_fun, ext_int, ext_rat, ofClass
-/
theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : forall n : Nat, 0 < n -> f n = g n) : f = g :=
ext_rat'
DFunLike.congr_fun
      show
        (.ofClass f : Rat ->*₀ M₀).comp (.ofClass (Int.castRingHom Rat)) =
          (.ofClass g : Rat ->*₀ M₀).comp (.ofClass (Int.castRingHom Rat))
        from ext_int' (by simpa) (by simpa)

end Rat
end MonoidWithZeroHomClass

/--
theorem `RingHom.ext_rat` / 定理 `RingHom.ext_rat`

English:
theorem RingHom.ext_rat
  given: {R : Type*} [Semiring R] [FunLike F Rat R] [RingHomClass F Rat R] (f g : F)
  proof: MonoidWithZeroHomClass.ext_rat'
RingHom.congr_fun
      ((f : Rat ->+* R).comp (Int.castRingHom Rat)).ext_int ((g : Rat ->+* R).comp (Int.castRingHom Rat))

中文:
定理 环态射.ext_rat
  条件: {R : 类型} [半环 R] [函数状 F 有理数 R] [环态射类 F 有理数 R] (f g : F)
  证明: MonoidWithZeroHomClass.ext_rat'
RingHom.congr_fun
      ((f : Rat ->+* R).comp (Int.castRingHom Rat)).ext_int ((g : Rat ->+* R).comp (Int.castRingHom Rat))

Depends on / 依赖: Int.castRingHom, MonoidWithZeroHomClass, MonoidWithZeroHomClass.ext_rat, RingHom, RingHom.congr_fun, castRingHom, congr_fun, ext_int, ext_rat
-/
theorem RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F Rat R] [RingHomClass F Rat R] (f g : F) :
    f = g :=
MonoidWithZeroHomClass.ext_rat'
RingHom.congr_fun
      ((f : Rat ->+* R).comp (Int.castRingHom Rat)).ext_int ((g : Rat ->+* R).comp (Int.castRingHom Rat))

/--
Instance `NNRat.subsingleton_ringHom` / 实例 `NNRat.subsingleton_ringHom`

English:
instance NNRat.subsingleton_ringHom
  signature: {R : Type*} [Semiring R]
  body: MonoidWithZeroHomClass.ext_nnrat' by simp

中文:
实例 NNRat.subsingleton_ringHom
  签名: {R : 类型} [半环 R]
  定义体: MonoidWithZeroHomClass.ext_nnrat' by simp

Depends on / 依赖: MonoidWithZeroHomClass, MonoidWithZeroHomClass.ext_nnrat, ext_nnrat
-/
instance NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (Rat>=0 ->+* R) where
allEq f g := MonoidWithZeroHomClass.ext_nnrat' by simp

/--
Instance `Rat.subsingleton_ringHom` / 实例 `Rat.subsingleton_ringHom`

English:
instance Rat.subsingleton_ringHom
  signature: {R : Type*} [Semiring R]
  body: ⟨RingHom.ext_rat⟩

中文:
实例 有理数.subsingleton_ringHom
  签名: {R : 类型} [半环 R]
  定义体: ⟨RingHom.ext_rat⟩

Depends on / 依赖: RingHom, RingHom.ext_rat, ext_rat
-/
instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (Rat ->+* R) :=
  ⟨RingHom.ext_rat⟩
