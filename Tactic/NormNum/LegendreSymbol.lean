/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# A `norm_num` extension for Jacobi and Legendre symbols

We extend the `norm_num` tactic so that it can be used to provably compute
the value of the Jacobi symbol `J(a | b)` or the Legendre symbol `legendreSym p a` when
the arguments are numerals.

## Implementation notes

We use the Law of Quadratic Reciprocity for the Jacobi symbol to compute the value of `J(a | b)`
efficiently, roughly comparable in effort with the Euclidean algorithm for the computation
of the gcd of `a` and `b`. More precisely, the computation is done in the following steps.

* Use `J(a | 0) = 1` (an artifact of the definition) and `J(a | 1) = 1` to deal
  with corner cases.

* Use `J(a | b) = J(a % b | b)` to reduce to the case that `a` is a natural number.
  We define a version of the Jacobi symbol restricted to natural numbers for use in
  the following steps; see `NormNum.jacobiSymNat`. (But we'll continue to write `J(a | b)`
  in this description.)

* Remove powers of two from `b`. This is done via `J(2a | 2b) = 0` and
  `J(2a+1 | 2b) = J(2a+1 | b)` (another artifact of the definition).

* Now `0 ≤ a < b` and `b` is odd. If `b = 1`, then the value is `1`.
  If `a = 0` (and `b > 1`), then the value is `0`. Otherwise, we remove powers of two from `a`
  via `J(4a | b) = J(a | b)` and `J(2a | b) = ±J(a | b)`, where the sign is determined
  by the residue class of `b` mod 8, to reduce to `a` odd.

* Once `a` is odd, we use Quadratic Reciprocity (QR) in the form
  `J(a | b) = ±J(b % a | a)`, where the sign is determined by the residue classes
  of `a` and `b` mod 4. We are then back in the previous case.

We provide customized versions of these results for the various reduction steps,
where we encode the residue classes mod 2, mod 4, or mod 8 by using hypotheses like
`a % n = b`. In this way, the only divisions we have to compute and prove
are the ones occurring in the use of QR above.
-/

public section


section Lemmas

namespace Mathlib.Meta.NormNum

/--
Definition of `jacobiSymNat` / `jacobiSymNat` 的定义

English:
definition jacobiSymNat
  signature: (a b : Nat)
  body: jacobiSym a b

中文:
定义 jacobiSymNat
  签名: (a b : 自然数)
  定义体: jacobiSym a b

Depends on / 依赖: jacobiSym
-/
def jacobiSymNat (a b : Nat) : Int :=
  jacobiSym a b

/-!
### API Lemmas

We repeat part of the API for `jacobiSym` with `NormNum.jacobiSymNat` and without implicit
arguments, in a form that is suitable for constructing proofs in `norm_num`.
-/


/--
theorem `jacobiSymNat.zero_right` / 定理 `jacobiSymNat.zero_right`

English:
theorem jacobiSymNat.zero_right
  given: (a : Nat)
  statement: jacobiSymNat a 0 = 1
  proof: by
  rw [jacobiSymNat]; rw [jacobiSym.zero_right]

中文:
定理 jacobiSymNat.zero_right
  条件: (a : 自然数)
  结论: jacobiSym自然数 a 0 = 1
  证明: by
  rw [jacobiSymNat]; rw [jacobiSym.zero_right]

Depends on / 依赖: jacobiSym, jacobiSym.zero_right, jacobiSymNat, zero_right
-/
theorem jacobiSymNat.zero_right (a : Nat) : jacobiSymNat a 0 = 1 := by
  rw [jacobiSymNat]; rw [jacobiSym.zero_right]

/--
theorem `jacobiSymNat.one_right` / 定理 `jacobiSymNat.one_right`

English:
theorem jacobiSymNat.one_right
  given: (a : Nat)
  statement: jacobiSymNat a 1 = 1
  proof: by
  rw [jacobiSymNat]; rw [jacobiSym.one_right]

中文:
定理 jacobiSymNat.one_right
  条件: (a : 自然数)
  结论: jacobiSym自然数 a 1 = 1
  证明: by
  rw [jacobiSymNat]; rw [jacobiSym.one_right]

Depends on / 依赖: jacobiSym, jacobiSym.one_right, jacobiSymNat, one_right
-/
theorem jacobiSymNat.one_right (a : Nat) : jacobiSymNat a 1 = 1 := by
  rw [jacobiSymNat]; rw [jacobiSym.one_right]

/--
theorem `jacobiSymNat.zero_left` / 定理 `jacobiSymNat.zero_left`

English:
theorem jacobiSymNat.zero_left
  given: (b : Nat) (hb : Nat.beq (b / 2) 0 = false)
  statement: jacobiSymNat 0 b = 0
  proof: by
  rw [jacobiSymNat]; rw [Nat.cast_zero]; rw [jacobiSym.zero_left ?_]
  calc
    1 < 2 * 1 := by decide
    _ <= 2 * (b / 2) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)))
    _ <= b := Nat.mul_div_le b 2

中文:
定理 jacobiSymNat.zero_left
  条件: (b : 自然数) (hb : 自然数.beq (b / 2) 0 = false)
  结论: jacobiSym自然数 0 b = 0
  证明: by
  rw [jacobiSymNat]; rw [Nat.cast_zero]; rw [jacobiSym.zero_left ?_]
  calc
    1 < 2 * 1 := by decide
    _ <= 2 * (b / 2) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)))
    _ <= b := Nat.mul_div_le b 2

Depends on / 依赖: Nat.cast_zero, Nat.mul_div_le, Nat.mul_le_mul_left, Nat.ne_of_beq_eq_false, Nat.pos_of_ne_zero, Nat.succ_le_of_lt, cast_zero, jacobiSym, jacobiSym.zero_left, jacobiSymNat, mul_div_le, mul_le_mul_left, ne_of_beq_eq_false, pos_of_ne_zero, succ_le_of_lt, zero_left
-/
theorem jacobiSymNat.zero_left (b : Nat) (hb : Nat.beq (b / 2) 0 = false) : jacobiSymNat 0 b = 0 := by
  rw [jacobiSymNat]; rw [Nat.cast_zero]; rw [jacobiSym.zero_left ?_]
  calc
    1 < 2 * 1 := by decide
    _ <= 2 * (b / 2) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)))
    _ <= b := Nat.mul_div_le b 2

/--
theorem `jacobiSymNat.one_left` / 定理 `jacobiSymNat.one_left`

English:
theorem jacobiSymNat.one_left
  given: (b : Nat)
  statement: jacobiSymNat 1 b = 1
  proof: by
  rw [jacobiSymNat]; rw [Nat.cast_one]; rw [jacobiSym.one_left]

中文:
定理 jacobiSymNat.one_left
  条件: (b : 自然数)
  结论: jacobiSym自然数 1 b = 1
  证明: by
  rw [jacobiSymNat]; rw [Nat.cast_one]; rw [jacobiSym.one_left]

Depends on / 依赖: Nat.cast_one, cast_one, jacobiSym, jacobiSym.one_left, jacobiSymNat, one_left
-/
theorem jacobiSymNat.one_left (b : Nat) : jacobiSymNat 1 b = 1 := by
  rw [jacobiSymNat]; rw [Nat.cast_one]; rw [jacobiSym.one_left]

/--
theorem `LegendreSym.to_jacobiSym` / 定理 `LegendreSym.to_jacobiSym`

English:
theorem LegendreSym.to_jacobiSym
  statement: (p : Nat) (pp : Fact p.Prime) (a r : Int)
  proof: by
  rwa [@jacobiSym.legendreSym.to_jacobiSym p pp a]

中文:
定理 LegendreSym.to_jacobiSym
  结论: (p : 自然数) (pp : Fact p.Prime) (a r : 整数)
  证明: by
  rwa [@jacobiSym.legendreSym.to_jacobiSym p pp a]

Depends on / 依赖: jacobiSym, jacobiSym.legendreSym.to_jacobiSym, legendreSym, to_jacobiSym
-/
theorem LegendreSym.to_jacobiSym (p : Nat) (pp : Fact p.Prime) (a r : Int)
    (hr : IsInt (jacobiSym a p) r) : IsInt (legendreSym p a) r := by
  rwa [@jacobiSym.legendreSym.to_jacobiSym p pp a]

/--
theorem `JacobiSym.mod_left` / 定理 `JacobiSym.mod_left`

English:
theorem JacobiSym.mod_left
  statement: (a : Int) (b ab' : Nat) (ab r b' : Int) (hb' : (b : Int) = b')
  proof: by
  rw [← hr]; rw [jacobiSymNat]; rw [jacobiSym.mod_left]; rw [hb']; rw [hab]; rw [← h]

中文:
定理 JacobiSym.mod_left
  结论: (a : 整数) (b ab' : 自然数) (ab r b' : 整数) (hb' : (b : 整数) = b')
  证明: by
  rw [← hr]; rw [jacobiSymNat]; rw [jacobiSym.mod_left]; rw [hb']; rw [hab]; rw [← h]

Depends on / 依赖: jacobiSym, jacobiSym.mod_left, jacobiSymNat, mod_left
-/
theorem JacobiSym.mod_left (a : Int) (b ab' : Nat) (ab r b' : Int) (hb' : (b : Int) = b')
    (hab : a % b' = ab) (h : (ab' : Int) = ab) (hr : jacobiSymNat ab' b = r) : jacobiSym a b = r := by
  rw [← hr]; rw [jacobiSymNat]; rw [jacobiSym.mod_left]; rw [hb']; rw [hab]; rw [← h]

/--
theorem `jacobiSymNat.mod_left` / 定理 `jacobiSymNat.mod_left`

English:
theorem jacobiSymNat.mod_left
  given: (a b ab : Nat) (r : Int) (hab : a % b = ab) (hr : jacobiSymNat ab b = r)
  proof: by
  rw [← hr]; rw [jacobiSymNat]; rw [jacobiSymNat]; rw [_root_.jacobiSym.mod_left a b]; rw [← hab]; rfl

中文:
定理 jacobiSymNat.mod_left
  条件: (a b ab : 自然数) (r : 整数) (hab : a % b = ab) (hr : jacobiSym自然数 ab b = r)
  证明: by
  rw [← hr]; rw [jacobiSymNat]; rw [jacobiSymNat]; rw [_root_.jacobiSym.mod_left a b]; rw [← hab]; rfl

Depends on / 依赖: _root_, _root_.jacobiSym.mod_left, jacobiSym, jacobiSymNat, mod_left
-/
theorem jacobiSymNat.mod_left (a b ab : Nat) (r : Int) (hab : a % b = ab) (hr : jacobiSymNat ab b = r) :
    jacobiSymNat a b = r := by
  rw [← hr]; rw [jacobiSymNat]; rw [jacobiSymNat]; rw [_root_.jacobiSym.mod_left a b]; rw [← hab]; rfl

/--
theorem `jacobiSymNat.even_even` / 定理 `jacobiSymNat.even_even`

English:
theorem jacobiSymNat.even_even
  statement: (a b : Nat) (hb₀ : Nat.beq (b / 2) 0 = false) (ha : a % 2 = 0)
  proof: by
  refine jacobiSym.eq_zero_iff.mpr
    ⟨ne_of_gt ((Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb₀)).trans_le (Nat.div_le_self b 2)),
      fun hf => ?_⟩
  have h : 2 ∣ a.gcd b := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb₁)
  change 2 ∣ (a : Int).gcd b at h
  rw [hf]; rw [

中文:
定理 jacobiSymNat.even_even
  结论: (a b : 自然数) (hb₀ : 自然数.beq (b / 2) 0 = false) (ha : a % 2 = 0)
  证明: by
  refine jacobiSym.eq_zero_iff.mpr
    ⟨ne_of_gt ((Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb₀)).trans_le (Nat.div_le_self b 2)),
      fun hf => ?_⟩
  have h : 2 ∣ a.gcd b := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb₁)
  change 2 ∣ (a : Int).gcd b at h
  rw [hf]; rw [

Depends on / 依赖: Nat.div_le_self, Nat.dvd_gcd, Nat.dvd_of_mod_eq_zero, Nat.ne_of_beq_eq_false, Nat.not_even_one, Nat.pos_of_ne_zero, a.gcd, div_le_self, dvd_gcd, dvd_of_mod_eq_zero, eq_zero_iff, even_iff_two_dvd, jacobiSym, jacobiSym.eq_zero_iff.mpr, ne_of_beq_eq_false, ne_of_gt, not_even_one, pos_of_ne_zero, trans_le
-/
theorem jacobiSymNat.even_even (a b : Nat) (hb₀ : Nat.beq (b / 2) 0 = false) (ha : a % 2 = 0)
    (hb₁ : b % 2 = 0) : jacobiSymNat a b = 0 := by
  refine jacobiSym.eq_zero_iff.mpr
    ⟨ne_of_gt ((Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb₀)).trans_le (Nat.div_le_self b 2)),
      fun hf => ?_⟩
  have h : 2 ∣ a.gcd b := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb₁)
  change 2 ∣ (a : Int).gcd b at h
  rw [hf]; rw [← even_iff_two_dvd] at h
  exact Nat.not_even_one h

/--
theorem `jacobiSymNat.odd_even` / 定理 `jacobiSymNat.odd_even`

English:
theorem jacobiSymNat.odd_even
  statement: (a b c : Nat) (r : Int) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : b / 2 = c)
  proof: by
  have ha' : legendreSym 2 a = 1 := by
    simp only [legendreSym.mod 2 a, Int.ofNat_mod_ofNat, ha]
    decide
  rcases eq_or_ne c 0 with (rfl | hc')
  · rw [← hr, Nat.eq_zero_of_dvd_of_div_eq_zero (Nat.dvd_of_mod_eq_zero hb) hc]
  · have : NeZero c := ⟨hc'⟩
    -- for `jacobiSym.mul_right`
    r

中文:
定理 jacobiSymNat.odd_even
  结论: (a b c : 自然数) (r : 整数) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : b / 2 = c)
  证明: by
  have ha' : legendreSym 2 a = 1 := by
    simp only [legendreSym.mod 2 a, Int.ofNat_mod_ofNat, ha]
    decide
  rcases eq_or_ne c 0 with (rfl | hc')
  · rw [← hr, Nat.eq_zero_of_dvd_of_div_eq_zero (Nat.dvd_of_mod_eq_zero hb) hc]
  · have : NeZero c := ⟨hc'⟩
    -- for `jacobiSym.mul_right`
    r

Depends on / 依赖: Int.ofNat_mod_ofNat, Nat.dvd_of_mod_eq_zero, Nat.eq_zero_of_dvd_of_div_eq_zero, NeZero, dvd_of_mod_eq_zero, eq_or_ne, eq_zero_of_dvd_of_div_eq_zero, legendreSym, legendreSym.mod, ofNat_mod_ofNat
-/
theorem jacobiSymNat.odd_even (a b c : Nat) (r : Int) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : b / 2 = c)
    (hr : jacobiSymNat a c = r) : jacobiSymNat a b = r := by
  have ha' : legendreSym 2 a = 1 := by
    simp only [legendreSym.mod 2 a, Int.ofNat_mod_ofNat, ha]
    decide
  rcases eq_or_ne c 0 with (rfl | hc')
  · rw [← hr, Nat.eq_zero_of_dvd_of_div_eq_zero (Nat.dvd_of_mod_eq_zero hb) hc]
  · have : NeZero c := ⟨hc'⟩
    -- for `jacobiSym.mul_right`
    rwa [← Nat.mod_add_div b 2, hb, hc, Nat.zero_add, jacobiSymNat, jacobiSym.mul_right,
      ← jacobiSym.legendreSym.to_jacobiSym, ha', one_mul]

/--
theorem `jacobiSymNat.double_even` / 定理 `jacobiSymNat.double_even`

English:
theorem jacobiSymNat.double_even
  statement: (a b c : Nat) (r : Int) (ha : a % 4 = 0) (hb : b % 2 = 1)
  proof: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  exact (jacobiSym.div_four_left (mod_cast ha) hb).symm

中文:
定理 jacobiSymNat.double_even
  结论: (a b c : 自然数) (r : 整数) (ha : a % 4 = 0) (hb : b % 2 = 1)
  证明: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  exact (jacobiSym.div_four_left (mod_cast ha) hb).symm

Depends on / 依赖: Int.natCast_ediv, Nat.cast_ofNat, cast_ofNat, div_four_left, jacobiSym, jacobiSym.div_four_left, jacobiSymNat, mod_cast, natCast_ediv
-/
theorem jacobiSymNat.double_even (a b c : Nat) (r : Int) (ha : a % 4 = 0) (hb : b % 2 = 1)
    (hc : a / 4 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  exact (jacobiSym.div_four_left (mod_cast ha) hb).symm

/--
theorem `jacobiSymNat.even_odd₁` / 定理 `jacobiSymNat.even_odd₁`

English:
theorem jacobiSymNat.even_odd₁
  statement: (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 1)
  proof: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

中文:
定理 jacobiSymNat.even_odd₁
  结论: (a b c : 自然数) (r : 整数) (ha : a % 2 = 0) (hb : b % 8 = 1)
  证明: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

Depends on / 依赖: Int.natCast_ediv, Nat.cast_ofNat, Nat.mod_mod_of_dvd, cast_ofNat, even_odd, if_neg, jacobiSym, jacobiSym.even_odd, jacobiSymNat, mod_cast, mod_mod_of_dvd, natCast_ediv
-/
theorem jacobiSymNat.even_odd₁ (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 1)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

/--
theorem `jacobiSymNat.even_odd₇` / 定理 `jacobiSymNat.even_odd₇`

English:
theorem jacobiSymNat.even_odd₇
  statement: (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 7)
  proof: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

中文:
定理 jacobiSymNat.even_odd₇
  结论: (a b c : 自然数) (r : 整数) (ha : a % 2 = 0) (hb : b % 8 = 7)
  证明: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

Depends on / 依赖: Int.natCast_ediv, Nat.cast_ofNat, Nat.mod_mod_of_dvd, cast_ofNat, even_odd, if_neg, jacobiSym, jacobiSym.even_odd, jacobiSymNat, mod_cast, mod_mod_of_dvd, natCast_ediv
-/
theorem jacobiSymNat.even_odd₇ (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 7)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

/--
theorem `jacobiSymNat.even_odd₃` / 定理 `jacobiSymNat.even_odd₃`

English:
theorem jacobiSymNat.even_odd₃
  statement: (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 3)
  proof: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

中文:
定理 jacobiSymNat.even_odd₃
  结论: (a b c : 自然数) (r : 整数) (ha : a % 2 = 0) (hb : b % 8 = 3)
  证明: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

Depends on / 依赖: Int.natCast_ediv, Nat.cast_ofNat, Nat.mod_mod_of_dvd, cast_ofNat, even_odd, if_pos, jacobiSym, jacobiSym.even_odd, jacobiSymNat, mod_cast, mod_mod_of_dvd, natCast_ediv
-/
theorem jacobiSymNat.even_odd₃ (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 3)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

/--
theorem `jacobiSymNat.even_odd₅` / 定理 `jacobiSymNat.even_odd₅`

English:
theorem jacobiSymNat.even_odd₅
  statement: (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 5)
  proof: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

中文:
定理 jacobiSymNat.even_odd₅
  结论: (a b c : 自然数) (r : 整数) (ha : a % 2 = 0) (hb : b % 8 = 5)
  证明: by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

Depends on / 依赖: Int.natCast_ediv, Nat.cast_ofNat, Nat.mod_mod_of_dvd, cast_ofNat, even_odd, if_pos, jacobiSym, jacobiSym.even_odd, jacobiSymNat, mod_cast, mod_mod_of_dvd, natCast_ediv
-/
theorem jacobiSymNat.even_odd₅ (a b c : Nat) (r : Int) (ha : a % 2 = 0) (hb : b % 8 = 5)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha)]; rw [if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd]; rw [hb]; simp

/--
theorem `jacobiSymNat.qr₁` / 定理 `jacobiSymNat.qr₁`

English:
theorem jacobiSymNat.qr₁
  statement: (a b : Nat) (r : Int) (ha : a % 4 = 1) (hb : b % 2 = 1)
  proof: by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_one_mod_four ha (Nat.odd_iff.mpr hb)]

中文:
定理 jacobiSymNat.qr₁
  结论: (a b : 自然数) (r : 整数) (ha : a % 4 = 1) (hb : b % 2 = 1)
  证明: by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_one_mod_four ha (Nat.odd_iff.mpr hb)]

Depends on / 依赖: Nat.odd_iff.mpr, jacobiSym, jacobiSym.quadratic_reciprocity_one_mod_four, jacobiSymNat, odd_iff, quadratic_reciprocity_one_mod_four
-/
theorem jacobiSymNat.qr₁ (a b : Nat) (r : Int) (ha : a % 4 = 1) (hb : b % 2 = 1)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_one_mod_four ha (Nat.odd_iff.mpr hb)]

/--
theorem `jacobiSymNat.qr₁_mod` / 定理 `jacobiSymNat.qr₁_mod`

English:
theorem jacobiSymNat.qr₁_mod
  statement: (a b ab : Nat) (r : Int) (ha : a % 4 = 1) (hb : b % 2 = 1)
  proof: jacobiSymNat.qr₁ _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

中文:
定理 jacobiSymNat.qr₁_mod
  结论: (a b ab : 自然数) (r : 整数) (ha : a % 4 = 1) (hb : b % 2 = 1)
  证明: jacobiSymNat.qr₁ _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

Depends on / 依赖: jacobiSymNat, jacobiSymNat.mod_left, jacobiSymNat.qr, mod_left
-/
theorem jacobiSymNat.qr₁_mod (a b ab : Nat) (r : Int) (ha : a % 4 = 1) (hb : b % 2 = 1)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
jacobiSymNat.qr₁ _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

/--
theorem `jacobiSymNat.qr₁'` / 定理 `jacobiSymNat.qr₁'`

English:
theorem jacobiSymNat.qr₁'
  statement: (a b : Nat) (r : Int) (ha : a % 2 = 1) (hb : b % 4 = 1)
  proof: by
  rwa [jacobiSymNat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (Nat.odd_iff.mpr ha)]

中文:
定理 jacobiSymNat.qr₁'
  结论: (a b : 自然数) (r : 整数) (ha : a % 2 = 1) (hb : b % 4 = 1)
  证明: by
  rwa [jacobiSymNat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (Nat.odd_iff.mpr ha)]

Depends on / 依赖: Nat.odd_iff.mpr, jacobiSym, jacobiSym.quadratic_reciprocity_one_mod_four, jacobiSymNat, odd_iff, quadratic_reciprocity_one_mod_four
-/
theorem jacobiSymNat.qr₁' (a b : Nat) (r : Int) (ha : a % 2 = 1) (hb : b % 4 = 1)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
  rwa [jacobiSymNat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (Nat.odd_iff.mpr ha)]

/--
theorem `jacobiSymNat.qr₁'_mod` / 定理 `jacobiSymNat.qr₁'_mod`

English:
theorem jacobiSymNat.qr₁'_mod
  statement: (a b ab : Nat) (r : Int) (ha : a % 2 = 1) (hb : b % 4 = 1)
  proof: jacobiSymNat.qr₁' _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

中文:
定理 jacobiSymNat.qr₁'_mod
  结论: (a b ab : 自然数) (r : 整数) (ha : a % 2 = 1) (hb : b % 4 = 1)
  证明: jacobiSymNat.qr₁' _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr
-/
theorem jacobiSymNat.qr₁'_mod (a b ab : Nat) (r : Int) (ha : a % 2 = 1) (hb : b % 4 = 1)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
jacobiSymNat.qr₁' _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

/--
theorem `jacobiSymNat.qr₃` / 定理 `jacobiSymNat.qr₃`

English:
theorem jacobiSymNat.qr₃
  statement: (a b : Nat) (r : Int) (ha : a % 4 = 3) (hb : b % 4 = 3)
  proof: by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]

中文:
定理 jacobiSymNat.qr₃
  结论: (a b : 自然数) (r : 整数) (ha : a % 4 = 3) (hb : b % 4 = 3)
  证明: by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]

Depends on / 依赖: jacobiSym, jacobiSym.quadratic_reciprocity_three_mod_four, jacobiSymNat, neg_inj, quadratic_reciprocity_three_mod_four
-/
theorem jacobiSymNat.qr₃ (a b : Nat) (r : Int) (ha : a % 4 = 3) (hb : b % 4 = 3)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = -r := by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]

/--
theorem `jacobiSymNat.qr₃_mod` / 定理 `jacobiSymNat.qr₃_mod`

English:
theorem jacobiSymNat.qr₃_mod
  statement: (a b ab : Nat) (r : Int) (ha : a % 4 = 3) (hb : b % 4 = 3)
  proof: jacobiSymNat.qr₃ _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

中文:
定理 jacobiSymNat.qr₃_mod
  结论: (a b ab : 自然数) (r : 整数) (ha : a % 4 = 3) (hb : b % 4 = 3)
  证明: jacobiSymNat.qr₃ _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

Depends on / 依赖: jacobiSymNat, jacobiSymNat.mod_left, jacobiSymNat.qr, mod_left
-/
theorem jacobiSymNat.qr₃_mod (a b ab : Nat) (r : Int) (ha : a % 4 = 3) (hb : b % 4 = 3)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = -r :=
jacobiSymNat.qr₃ _ _ _ ha hb jacobiSymNat.mod_left _ _ ab r hab hr

/--
theorem `isInt_jacobiSym` / 定理 `isInt_jacobiSym`

English:
theorem isInt_jacobiSym
  statement: {a na : Int} -> {b nb : Nat} -> {r : Int} ->

中文:
定理 isInt_jacobiSym
  结论: {a na : 整数} -> {b nb : 自然数} -> {r : 整数} ->
-/
theorem isInt_jacobiSym : {a na : Int} -> {b nb : Nat} -> {r : Int} ->
    IsInt a na -> IsNat b nb -> jacobiSym na nb = r -> IsInt (jacobiSym a b) r
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
theorem `isInt_jacobiSymNat` / 定理 `isInt_jacobiSymNat`

English:
theorem isInt_jacobiSymNat
  statement: {a na : Nat} -> {b nb : Nat} -> {r : Int} ->

中文:
定理 isInt_jacobiSymNat
  结论: {a na : 自然数} -> {b nb : 自然数} -> {r : 整数} ->
-/
theorem isInt_jacobiSymNat : {a na : Nat} -> {b nb : Nat} -> {r : Int} ->
    IsNat a na -> IsNat b nb -> jacobiSymNat na nb = r -> IsInt (jacobiSymNat a b) r
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩


end Mathlib.Meta.NormNum

end Lemmas

meta section

section Evaluation

/-!
### Certified evaluation of the Jacobi symbol

The following functions recursively evaluate a Jacobi symbol and construct the
corresponding proof term.
-/


namespace Mathlib.Meta.NormNum

open Lean Elab Tactic Qq

-- TODO: redefined here for reduction; should this be special-handled in quote4?
/--
Definition of `mkRawIntLit'` / `mkRawIntLit'` 的定义

English:
definition mkRawIntLit'
  signature: (n : Int)
  body: let lit : Q(Nat) := .lit .natVal n.natAbs
  if 0 <= n then q(.ofNat $lit) else q(.negOfNat $lit)

中文:
定义 mkRawIntLit'
  签名: (n : 整数)
  定义体: let lit : Q(Nat) := .lit .natVal n.natAbs
  if 0 <= n then q(.ofNat $lit) else q(.negOfNat $lit)
-/
private def mkRawIntLit' (n : Int) : Q(Int) :=
let lit : Q(Nat) := .lit .natVal n.natAbs
  if 0 <= n then q(.ofNat $lit) else q(.negOfNat $lit)

/--
Definition of `proveJacobiSymOdd` / `proveJacobiSymOdd` 的定义

English:
definition proveJacobiSymOdd
  signature: (ea eb : Q(Nat))
  body: match eb.natLit! with
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match ea.natLit! with
    | 0 =>
haveI : ea =Q 0 := ⟨⟩
      have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
      ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb

中文:
定义 proveJacobiSymOdd
  签名: (ea eb : Q(自然数))
  定义体: match eb.natLit! with
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match ea.natLit! with
    | 0 =>
haveI : ea =Q 0 := ⟨⟩
      have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
      ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb

Depends on / 依赖: TotallyDisconnectedSpace, TotallySeparatedSpace
-/
partial def proveJacobiSymOdd (ea eb : Q(Nat)) : (er : Q(Int)) × Q(jacobiSymNat $ea $eb = $er) :=
  match eb.natLit! with
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match ea.natLit! with
    | 0 =>
haveI : ea =Q 0 := ⟨⟩
      have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
      ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb $hb)⟩
    | 1 =>
haveI : ea =Q 1 := ⟨⟩
      ⟨mkRawIntLit' 1, q(jacobiSymNat.one_left $eb)⟩
    | a =>
      match a % 2 with
      | 0 =>
        match a % 4 with
        | 0 =>
          have ha : Q(Nat.mod $ea 4 = 0) := (q(Eq.refl 0) : Expr)
          have hb : Q(Nat.mod $eb 2 = 1) := (q(Eq.refl 1) : Expr)
          have ec : Q(Nat) := mkRawNatLit (a / 4)
          have hc : Q(Nat.div $ea 4 = $ec) := (q(Eq.refl $ec) : Expr)
          have ⟨er, p⟩ := proveJacobiSymOdd ec eb
          ⟨er, q(jacobiSymNat.double_even $ea $eb $ec $er $ha $hb $hc $p)⟩
        | _ =>
          have ha : Q(Nat.mod $ea 2 = 0) := (q(Eq.refl 0) : Expr)
          have ec : Q(Nat) := mkRawNatLit (a / 2)
          have hc : Q(Nat.div $ea 2 = $ec) := (q(Eq.refl $ec) : Expr)
          have ⟨er, p⟩ := proveJacobiSymOdd ec eb
          match b % 8 with
          | 1 =>
            have hb : Q(Nat.mod $eb 8 = 1) := (q(Eq.refl 1) : Expr)
            ⟨er, q(jacobiSymNat.even_odd₁ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | 3 =>
            have er' := mkRawIntLit (-er.intLit!)
            have hb : Q(Nat.mod $eb 8 = 3) := (q(Eq.refl 3) : Expr)
            show (_ : Q(Int)) × Q(jacobiSymNat $ea $eb = -$er) from
              ⟨er', q(jacobiSymNat.even_odd₃ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | 5 =>
            have er' := mkRawIntLit (-er.intLit!)
haveI : er' =Q - er := ⟨⟩
            have hb : Q(Nat.mod $eb 8 = 5) := (q(Eq.refl 5) : Expr)
            ⟨er', q(jacobiSymNat.even_odd₅ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | _ =>
            have hb : Q(Nat.mod $eb 8 = 7) := (q(Eq.refl 7) : Expr)
            ⟨er, q(jacobiSymNat.even_odd₇ $ea $eb $ec $er $ha $hb $hc $p)⟩
      | _ =>
        have eab : Q(Nat) := mkRawNatLit (b % a)
        have hab : Q(Nat.mod $eb $ea = $eab) := (q(Eq.refl $eab) : Expr)
        have ⟨er, p⟩ := proveJacobiSymOdd eab ea
        match a % 4 with
        | 1 =>
          have ha : Q(Nat.mod $ea 4 = 1) := (q(Eq.refl 1) : Expr)
          have hb : Q(Nat.mod $eb 2 = 1) := (q(Eq.refl 1) : Expr)
          ⟨er, q(jacobiSymNat.qr₁_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
        | _ =>
          match b % 4 with
          | 1 =>
            have ha : Q(Nat.mod $ea 2 = 1) := (q(Eq.refl 1) : Expr)
            have hb : Q(Nat.mod $eb 4 = 1) := (q(Eq.refl 1) : Expr)
            ⟨er, q(jacobiSymNat.qr₁'_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
          | _ =>
            have er' := mkRawIntLit (-er.intLit!)
haveI : er' =Q - er := ⟨⟩
            have ha : Q(Nat.mod $ea 4 = 3) := (q(Eq.refl 3) : Expr)
            have hb : Q(Nat.mod $eb 4 = 3) := (q(Eq.refl 3) : Expr)
            ⟨er', q(jacobiSymNat.qr₃_mod $ea $eb $eab $er $ha $hb $hab $p)⟩

/--
Definition of `proveJacobiSymNat` / `proveJacobiSymNat` 的定义

English:
definition proveJacobiSymNat
  signature: (ea eb : Q(Nat))
  body: match eb.natLit! with
  | 0 =>
haveI : eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.zero_right $ea)⟩
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match b % 2 with
    | 0 =>
      match ea.natLit! with
      | 0 =>
        have hb : Q(Nat.beq (

中文:
定义 proveJacobiSymNat
  签名: (ea eb : Q(自然数))
  定义体: match eb.natLit! with
  | 0 =>
haveI : eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.zero_right $ea)⟩
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match b % 2 with
    | 0 =>
      match ea.natLit! with
      | 0 =>
        have hb : Q(Nat.beq (
-/
partial def proveJacobiSymNat (ea eb : Q(Nat)) : (er : Q(Int)) × Q(jacobiSymNat $ea $eb = $er) :=
  match eb.natLit! with
  | 0 =>
haveI : eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.zero_right $ea)⟩
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match b % 2 with
    | 0 =>
      match ea.natLit! with
      | 0 =>
        have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
        show (er : Q(Int)) × Q(jacobiSymNat 0 $eb = $er) from
          ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb $hb)⟩
      | 1 =>
        show (er : Q(Int)) × Q(jacobiSymNat 1 $eb = $er) from
          ⟨mkRawIntLit' 1, q(jacobiSymNat.one_left $eb)⟩
      | a =>
        match a % 2 with
        | 0 =>
          have hb₀ : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
          have ha : Q(Nat.mod $ea 2 = 0) := (q(Eq.refl 0) : Expr)
          have hb₁ : Q(Nat.mod $eb 2 = 0) := (q(Eq.refl 0) : Expr)
          ⟨mkRawIntLit' 0, q(jacobiSymNat.even_even $ea $eb $hb₀ $ha $hb₁)⟩
        | _ =>
          have ha : Q(Nat.mod $ea 2 = 1) := (q(Eq.refl 1) : Expr)
          have hb : Q(Nat.mod $eb 2 = 0) := (q(Eq.refl 0) : Expr)
          have ec : Q(Nat) := mkRawNatLit (b / 2)
          have hc : Q(Nat.div $eb 2 = $ec) := (q(Eq.refl $ec) : Expr)
          have ⟨er, p⟩ := proveJacobiSymOdd ea ec
          ⟨er, q(jacobiSymNat.odd_even $ea $eb $ec $er $ha $hb $hc $p)⟩
    | _ =>
      have a := ea.natLit!
      if b <= a then
        have eab : Q(Nat) := mkRawNatLit (a % b)
        have hab : Q(Nat.mod $ea $eb = $eab) := (q(Eq.refl $eab) : Expr)
        have ⟨er, p⟩ := proveJacobiSymOdd eab eb
        ⟨er, q(jacobiSymNat.mod_left $ea $eb $eab $er $hab $p)⟩
      else
        proveJacobiSymOdd ea eb

/--
Definition of `proveJacobiSym` / `proveJacobiSym` 的定义

English:
definition proveJacobiSym
  signature: (ea : Q(Int)) (eb : Q(Nat))
  body: match eb.natLit! with
  | 0 =>
haveI : eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.zero_right $ea)⟩
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.one_right $ea)⟩
  | b =>
    have eb' := mkRawIntLit b
    have hb' : Q(($eb : Int) = $eb') := (q(Eq.refl $eb') : Expr)
    have ab :

中文:
定义 proveJacobiSym
  签名: (ea : Q(整数)) (eb : Q(自然数))
  定义体: match eb.natLit! with
  | 0 =>
haveI : eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.zero_right $ea)⟩
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.one_right $ea)⟩
  | b =>
    have eb' := mkRawIntLit b
    have hb' : Q(($eb : Int) = $eb') := (q(Eq.refl $eb') : Expr)
    have ab :
-/
partial def proveJacobiSym (ea : Q(Int)) (eb : Q(Nat)) : (er : Q(Int)) × Q(jacobiSym $ea $eb = $er) :=
  match eb.natLit! with
  | 0 =>
haveI : eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.zero_right $ea)⟩
  | 1 =>
haveI : eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.one_right $ea)⟩
  | b =>
    have eb' := mkRawIntLit b
    have hb' : Q(($eb : Int) = $eb') := (q(Eq.refl $eb') : Expr)
    have ab := ea.intLit! % b
    have eab := mkRawIntLit ab
    have hab : Q(Int.emod $ea $eb' = $eab) := (q(Eq.refl $eab) : Expr)
    have eab' : Q(Nat) := mkRawNatLit ab.toNat
    have hab' : Q(($eab' : Int) = $eab) := (q(Eq.refl $eab) : Expr)
    have ⟨er, p⟩ := proveJacobiSymNat eab' eb
    ⟨er, q(JacobiSym.mod_left $ea $eb $eab' $eab $er $eb' $hb' $hab $hab' $p)⟩

end Mathlib.Meta.NormNum

end Evaluation

section Tactic

/-!
### The `norm_num` plug-in
-/


namespace Tactic

namespace NormNum

open Lean Elab Tactic Qq Mathlib.Meta.NormNum

/-- This is the `norm_num` plug-in that evaluates Jacobi symbols. -/
@[norm_num jacobiSym _ _]
/--
Definition of `evalJacobiSym` / `evalJacobiSym` 的定义

English:
definition evalJacobiSym
  signature: : NormNumExt where eval {u α} e
  body: do
    let .app (.app _ (a : Q(Int))) (b : Q(Nat)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨eb, pb⟩ ← deriveNat b _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea eb
haveI' : e =Q jacobiSym a b := ⟨⟩
    return .isInt _ er er.intLit! q

中文:
定义 evalJacobiSym
  签名: : NormNumExt where eval {u α} e
  定义体: do
    let .app (.app _ (a : Q(Int))) (b : Q(Nat)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨eb, pb⟩ ← deriveNat b _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea eb
haveI' : e =Q jacobiSym a b := ⟨⟩
    return .isInt _ er er.intLit! q
-/
def evalJacobiSym : NormNumExt where eval {u α} e := do
    let .app (.app _ (a : Q(Int))) (b : Q(Nat)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨eb, pb⟩ ← deriveNat b _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea eb
haveI' : e =Q jacobiSym a b := ⟨⟩
    return .isInt _ er er.intLit! q(isInt_jacobiSym $pa $pb $pr)

/-- This is the `norm_num` plug-in that evaluates Jacobi symbols on natural numbers. -/
@[norm_num jacobiSymNat _ _]
/--
Definition of `evalJacobiSymNat` / `evalJacobiSymNat` 的定义

English:
definition evalJacobiSymNat
  signature: : NormNumExt where eval {u α} e
  body: do
    let .app (.app _ (a : Q(Nat))) (b : Q(Nat)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveNat a _
    let ⟨eb, pb⟩ ← deriveNat b _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSymNat ea eb
haveI' : e =Q jacobiSymNat a b := ⟨⟩
    return .isInt _ er er.int

中文:
定义 evalJacobiSymNat
  签名: : NormNumExt where eval {u α} e
  定义体: do
    let .app (.app _ (a : Q(Nat))) (b : Q(Nat)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveNat a _
    let ⟨eb, pb⟩ ← deriveNat b _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSymNat ea eb
haveI' : e =Q jacobiSymNat a b := ⟨⟩
    return .isInt _ er er.int
-/
def evalJacobiSymNat : NormNumExt where eval {u α} e := do
    let .app (.app _ (a : Q(Nat))) (b : Q(Nat)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveNat a _
    let ⟨eb, pb⟩ ← deriveNat b _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSymNat ea eb
haveI' : e =Q jacobiSymNat a b := ⟨⟩
    return .isInt _ er er.intLit! q(isInt_jacobiSymNat $pa $pb $pr)

/-- This is the `norm_num` plug-in that evaluates Legendre symbols. -/
@[norm_num legendreSym _ _]
/--
Definition of `evalLegendreSym` / `evalLegendreSym` 的定义

English:
definition evalLegendreSym
  signature: : NormNumExt where eval {u α} e
  body: do
    let .app (.app (.app _ (p : Q(Nat))) (fp : Q(Fact (Nat.Prime $p)))) (a : Q(Int)) ← Meta.whnfR e |
      failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨ep, pp⟩ ← deriveNat p _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea ep
haveI' : e =Q legendreSym 

中文:
定义 evalLegendreSym
  签名: : NormNumExt where eval {u α} e
  定义体: do
    let .app (.app (.app _ (p : Q(Nat))) (fp : Q(Fact (Nat.Prime $p)))) (a : Q(Int)) ← Meta.whnfR e |
      failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨ep, pp⟩ ← deriveNat p _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea ep
haveI' : e =Q legendreSym 

Depends on / 依赖: Iff.mpr, regularSpace_TFAE
-/
def evalLegendreSym : NormNumExt where eval {u α} e := do
    let .app (.app (.app _ (p : Q(Nat))) (fp : Q(Fact (Nat.Prime $p)))) (a : Q(Int)) ← Meta.whnfR e |
      failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨ep, pp⟩ ← deriveNat p _
haveI' : u =QL 0 := ⟨⟩ haveI' : α =Q Int := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea ep
haveI' : e =Q legendreSym p a := ⟨⟩
    return .isInt _ er er.intLit!
      q(LegendreSym.to_jacobiSym $p $fp $a $er (isInt_jacobiSym $pa $pp $pr))

end NormNum

end Tactic

end Tactic
