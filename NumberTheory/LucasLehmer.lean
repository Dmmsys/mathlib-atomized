/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Alastair Irving, Kim Morrison, Ainsley Pahljina
-/
module

public import Mathlib.NumberTheory.Fermat
public import Mathlib.RingTheory.Fintype

/-!
# The Lucas-Lehmer test for Mersenne primes

We define `lucasLehmerResidue : Π p : ℕ, ZMod (2^p - 1)`, and
prove `lucasLehmerResidue p = 0 ↔ Prime (mersenne p)`.

We construct a `norm_num` extension to calculate this residue to certify primality of Mersenne
primes using `lucas_lehmer_sufficiency`.


## TODO

- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Kim Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
This tactic was ported by Thomas Murrills to Lean 4, and then it was converted to a `norm_num`
extension and made to use kernel reductions by Kyle Miller.
-/

@[expose] public section

/--
Definition of `mersenne` / `mersenne` 的定义

English:
definition mersenne
  signature: (p : Nat)
  body: 2 ^ p - 1

中文:
定义 mersenne
  签名: (p : 自然数)
  定义体: 2 ^ p - 1
-/
def mersenne (p : Nat) : Nat :=
  2 ^ p - 1

/--
theorem `strictMono_mersenne` / 定理 `strictMono_mersenne`

English:
theorem strictMono_mersenne
  statement: StrictMono mersenne
  proof: fun m n h =>
(Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 by gcongr; norm_num1

@[simp, gcongr]

中文:
定理 strictMono_mersenne
  结论: StrictMono mersenne
  证明: fun m n h =>
(Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 by gcongr; norm_num1

@[simp, gcongr]
-/
theorem strictMono_mersenne : StrictMono mersenne := fun m n h =>
(Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 by gcongr; norm_num1

@[simp, gcongr]
/--
theorem `mersenne_lt_mersenne` / 定理 `mersenne_lt_mersenne`

English:
theorem mersenne_lt_mersenne
  given: {p q : Nat}
  statement: mersenne p < mersenne q ↔ p < q
  proof: strictMono_mersenne.lt_iff_lt

@[simp, gcongr]

中文:
定理 mersenne_lt_mersenne
  条件: {p q : 自然数}
  结论: mersenne p < mersenne q ↔ p < q
  证明: strictMono_mersenne.lt_iff_lt

@[simp, gcongr]

Depends on / 依赖: lt_iff_lt, strictMono_mersenne, strictMono_mersenne.lt_iff_lt
-/
theorem mersenne_lt_mersenne {p q : Nat} : mersenne p < mersenne q ↔ p < q :=
  strictMono_mersenne.lt_iff_lt

@[simp, gcongr]
/--
theorem `mersenne_le_mersenne` / 定理 `mersenne_le_mersenne`

English:
theorem mersenne_le_mersenne
  given: {p q : Nat}
  statement: mersenne p <= mersenne q ↔ p <= q
  proof: strictMono_mersenne.le_iff_le

中文:
定理 mersenne_le_mersenne
  条件: {p q : 自然数}
  结论: mersenne p <= mersenne q ↔ p <= q
  证明: strictMono_mersenne.le_iff_le

Depends on / 依赖: le_iff_le, strictMono_mersenne, strictMono_mersenne.le_iff_le
-/
theorem mersenne_le_mersenne {p q : Nat} : mersenne p <= mersenne q ↔ p <= q :=
  strictMono_mersenne.le_iff_le

/--
theorem `mersenne_zero` / 定理 `mersenne_zero`

English:
theorem mersenne_zero
  statement: mersenne 0 = 0
  proof: rfl

中文:
定理 mersenne_zero
  结论: mersenne 0 = 0
  证明: rfl
-/
@[simp] theorem mersenne_zero : mersenne 0 = 0 := rfl

/--
lemma `mersenne_odd` / 引理 `mersenne_odd`

English:
lemma mersenne_odd
  statement: forall {p : Nat}, Odd (mersenne p) ↔ p != 0

中文:
引理 mersenne_odd
  结论: 对任意 {p : 自然数}, Odd (mersenne p) ↔ p != 0
-/
@[simp] lemma mersenne_odd : forall {p : Nat}, Odd (mersenne p) ↔ p != 0
  | 0 => by simp
  | p + 1 => by
    simpa using! Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero p.succ_ne_zero) odd_one

/--
theorem `mersenne_pos` / 定理 `mersenne_pos`

English:
theorem mersenne_pos
  given: {p : Nat}
  statement: 0 < mersenne p ↔ 0 < p
  proof: mersenne_lt_mersenne (p := 0)

中文:
定理 mersenne_pos
  条件: {p : 自然数}
  结论: 0 < mersenne p ↔ 0 < p
  证明: mersenne_lt_mersenne (p := 0)
-/
@[simp] theorem mersenne_pos {p : Nat} : 0 < mersenne p ↔ 0 < p := mersenne_lt_mersenne (p := 0)

/--
lemma `mersenne_succ` / 引理 `mersenne_succ`

English:
lemma mersenne_succ
  given: (n : Nat)
  statement: mersenne (n + 1) = 2 * mersenne n + 1
  proof: by
  dsimp [mersenne]
  have := Nat.one_le_pow n 2 two_pos
  lia

中文:
引理 mersenne_succ
  条件: (n : 自然数)
  结论: mersenne (n + 1) = 2 * mersenne n + 1
  证明: by
  dsimp [mersenne]
  have := Nat.one_le_pow n 2 two_pos
  lia

Depends on / 依赖: Nat.one_le_pow, mersenne, one_le_pow, two_pos
-/
lemma mersenne_succ (n : Nat) : mersenne (n + 1) = 2 * mersenne n + 1 := by
  dsimp [mersenne]
  have := Nat.one_le_pow n 2 two_pos
  lia

/--
lemma `Nat.Prime.of_mersenne` / 引理 `Nat.Prime.of_mersenne`

English:
lemma Nat.Prime.of_mersenne
  given: {p : Nat} (h : (mersenne p).Prime)
  statement: Nat.Prime p
  proof: by
.2 apply Nat.prime_of_pow_sub_one_prime _ h
  rintro rfl
  apply Nat.not_prime_one h

中文:
引理 Nat.Prime.of_mersenne
  条件: {p : 自然数} (h : (mersenne p).Prime)
  结论: 自然数.Prime p
  证明: by
.2 apply Nat.prime_of_pow_sub_one_prime _ h
  rintro rfl
  apply Nat.not_prime_one h

Depends on / 依赖: Nat.not_prime_one, Nat.prime_of_pow_sub_one_prime, not_prime_one, prime_of_pow_sub_one_prime
-/
lemma Nat.Prime.of_mersenne {p : Nat} (h : (mersenne p).Prime) : Nat.Prime p := by
.2 apply Nat.prime_of_pow_sub_one_prime _ h
  rintro rfl
  apply Nat.not_prime_one h

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

alias ⟨_, mersenne_pos_of_pos⟩ := mersenne_pos

/-- Extension for the `positivity` tactic: `mersenne`. -/
@[positivity mersenne _]
meta def evalMersenne : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(mersenne $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(mersenne_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Nat.zero_le (mersenne $a)))
  | _, _, _ => throwError "not mersenne"

end Mathlib.Meta.Positivity

@[simp]
/--
theorem `one_lt_mersenne` / 定理 `one_lt_mersenne`

English:
theorem one_lt_mersenne
  given: {p : Nat}
  statement: 1 < mersenne p ↔ 1 < p
  proof: mersenne_lt_mersenne (p := 1)

@[simp]

中文:
定理 one_lt_mersenne
  条件: {p : 自然数}
  结论: 1 < mersenne p ↔ 1 < p
  证明: mersenne_lt_mersenne (p := 1)

@[simp]

Depends on / 依赖: mersenne_lt_mersenne
-/
theorem one_lt_mersenne {p : Nat} : 1 < mersenne p ↔ 1 < p :=
  mersenne_lt_mersenne (p := 1)

@[simp]
/--
theorem `succ_mersenne` / 定理 `succ_mersenne`

English:
theorem succ_mersenne
  given: (k : Nat)
  statement: mersenne k + 1 = 2 ^ k
  proof: by
  rw [mersenne]; rw [tsub_add_cancel_of_le]
  exact one_le_pow₀ (by simp)

中文:
定理 succ_mersenne
  条件: (k : 自然数)
  结论: mersenne k + 1 = 2 ^ k
  证明: by
  rw [mersenne]; rw [tsub_add_cancel_of_le]
  exact one_le_pow₀ (by simp)

Depends on / 依赖: mersenne, tsub_add_cancel_of_le
-/
theorem succ_mersenne (k : Nat) : mersenne k + 1 = 2 ^ k := by
  rw [mersenne]; rw [tsub_add_cancel_of_le]
  exact one_le_pow₀ (by simp)

/--
lemma `mersenne_mod_four` / 引理 `mersenne_mod_four`

English:
lemma mersenne_mod_four
  given: {n : Nat} (h : 2 <= n)
  statement: mersenne n % 4 = 3
  proof: by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

中文:
引理 mersenne_mod_four
  条件: {n : 自然数} (h : 2 <= n)
  结论: mersenne n % 4 = 3
  证明: by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

Depends on / 依赖: Nat.le_induction, le_induction, mersenne_succ
-/
lemma mersenne_mod_four {n : Nat} (h : 2 <= n) : mersenne n % 4 = 3 := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

/--
lemma `mersenne_mod_three` / 引理 `mersenne_mod_three`

English:
lemma mersenne_mod_three
  given: {n : Nat} (odd : Odd n) (h : 3 <= n)
  statement: mersenne n % 3 = 1
  proof: by
  obtain ⟨k, rfl⟩ := odd
  replace h : 1 <= k := by lia
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ j _ _ =>
    rw [mersenne_succ]; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by lia]; rw [mersenne_succ]
    lia

中文:
引理 mersenne_mod_three
  条件: {n : 自然数} (odd : Odd n) (h : 3 <= n)
  结论: mersenne n % 3 = 1
  证明: by
  obtain ⟨k, rfl⟩ := odd
  replace h : 1 <= k := by lia
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ j _ _ =>
    rw [mersenne_succ]; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by lia]; rw [mersenne_succ]
    lia

Depends on / 依赖: Nat.le_induction, le_induction, mersenne_succ, replace
-/
lemma mersenne_mod_three {n : Nat} (odd : Odd n) (h : 3 <= n) : mersenne n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := odd
  replace h : 1 <= k := by lia
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ j _ _ =>
    rw [mersenne_succ]; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by lia]; rw [mersenne_succ]
    lia

/--
lemma `mersenne_mod_eight` / 引理 `mersenne_mod_eight`

English:
lemma mersenne_mod_eight
  given: {n : Nat} (h : 3 <= n)
  statement: mersenne n % 8 = 7
  proof: by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

中文:
引理 mersenne_mod_eight
  条件: {n : 自然数} (h : 3 <= n)
  结论: mersenne n % 8 = 7
  证明: by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

Depends on / 依赖: Nat.le_induction, le_induction, mersenne_succ
-/
lemma mersenne_mod_eight {n : Nat} (h : 3 <= n) : mersenne n % 8 = 7 := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

/--
lemma `legendreSym_mersenne_two` / 引理 `legendreSym_mersenne_two`

English:
lemma legendreSym_mersenne_two
  given: {p : Nat} [Fact (mersenne p).Prime] (hp : 3 <= p)
  proof: by
  have := mersenne_mod_eight hp
  rw [legendreSym.at_two (by lia)]; rw [ZMod.χ₈_nat_eq_if_mod_eight]
  lia

中文:
引理 legendreSym_mersenne_two
  条件: {p : 自然数} [Fact (mersenne p).Prime] (hp : 3 <= p)
  证明: by
  have := mersenne_mod_eight hp
  rw [legendreSym.at_two (by lia)]; rw [ZMod.χ₈_nat_eq_if_mod_eight]
  lia

Depends on / 依赖: at_two, legendreSym, legendreSym.at_two, mersenne_mod_eight
-/
lemma legendreSym_mersenne_two {p : Nat} [Fact (mersenne p).Prime] (hp : 3 <= p) :
    legendreSym (mersenne p) 2 = 1 := by
  have := mersenne_mod_eight hp
  rw [legendreSym.at_two (by lia)]; rw [ZMod.χ₈_nat_eq_if_mod_eight]
  lia

/--
lemma `legendreSym_mersenne_three` / 引理 `legendreSym_mersenne_three`

English:
lemma legendreSym_mersenne_three
  given: {p : Nat} [Fact (mersenne p).Prime] (hp : 3 <= p) (odd : Odd p)
  proof: by
  rw [(by rfl : (3 : Int) = (3 : Nat))]; rw [legendreSym.quadratic_reciprocity_three_mod_four (by norm_num)
    (mersenne_mod_four (by lia))]; rw [legendreSym.mod]
  rw_mod_cast [mersenne_mod_three odd hp]
  simp

中文:
引理 legendreSym_mersenne_three
  条件: {p : 自然数} [Fact (mersenne p).Prime] (hp : 3 <= p) (odd : Odd p)
  证明: by
  rw [(by rfl : (3 : Int) = (3 : Nat))]; rw [legendreSym.quadratic_reciprocity_three_mod_four (by norm_num)
    (mersenne_mod_four (by lia))]; rw [legendreSym.mod]
  rw_mod_cast [mersenne_mod_three odd hp]
  simp

Depends on / 依赖: legendreSym, legendreSym.mod, legendreSym.quadratic_reciprocity_three_mod_four, mersenne_mod_four, mersenne_mod_three, quadratic_reciprocity_three_mod_four, rw_mod_cast
-/
lemma legendreSym_mersenne_three {p : Nat} [Fact (mersenne p).Prime] (hp : 3 <= p) (odd : Odd p) :
    legendreSym (mersenne p) 3 = -1 := by
  rw [(by rfl : (3 : Int) = (3 : Nat))]; rw [legendreSym.quadratic_reciprocity_three_mod_four (by norm_num)
    (mersenne_mod_four (by lia))]; rw [legendreSym.mod]
  rw_mod_cast [mersenne_mod_three odd hp]
  simp

namespace LucasLehmer

open Nat

/-!
We now define three(!) different versions of the recurrence
`s (i+1) = (s i)^2 - 2`.

These versions take values either in `ℤ`, in `ZMod (2^p - 1)`, or
in `ℤ` but applying `% (2^p - 1)` at each step.

They are each useful at different points in the proof,
so we take a moment setting up the lemmas relating them.
-/

/--
Definition of `s` / `s` 的定义

English:
definition s
  signature: : Nat -> Int

中文:
定义 s
  签名: : 自然数 -> 整数
-/
def s : Nat -> Int
  | 0 => 4
  | i + 1 => s i ^ 2 - 2

/--
Definition of `sZMod` / `sZMod` 的定义

English:
definition sZMod
  signature: (p : Nat)

中文:
定义 sZMod
  签名: (p : 自然数)
-/
def sZMod (p : Nat) : Nat -> ZMod (2 ^ p - 1)
  | 0 => 4
  | i + 1 => sZMod p i ^ 2 - 2

/--
Definition of `sMod` / `sMod` 的定义

English:
definition sMod
  signature: (p : Nat)

中文:
定义 sMod
  签名: (p : 自然数)
-/
def sMod (p : Nat) : Nat -> Int
  | 0 => 4 % (2 ^ p - 1)
  | i + 1 => (sMod p i ^ 2 - 2) % (2 ^ p - 1)

/--
theorem `mersenne_int_pos` / 定理 `mersenne_int_pos`

English:
theorem mersenne_int_pos
  given: {p : Nat} (hp : p != 0)
  statement: (0 : Int) < 2 ^ p - 1
  proof: sub_pos.2 mod_cast Nat.one_lt_two_pow hp

中文:
定理 mersenne_int_pos
  条件: {p : 自然数} (hp : p != 0)
  结论: (0 : 整数) < 2 ^ p - 1
  证明: sub_pos.2 mod_cast Nat.one_lt_two_pow hp

Depends on / 依赖: Nat.one_lt_two_pow, mod_cast, one_lt_two_pow, sub_pos
-/
theorem mersenne_int_pos {p : Nat} (hp : p != 0) : (0 : Int) < 2 ^ p - 1 :=
sub_pos.2 mod_cast Nat.one_lt_two_pow hp

/--
theorem `mersenne_int_ne_zero` / 定理 `mersenne_int_ne_zero`

English:
theorem mersenne_int_ne_zero
  given: (p : Nat) (hp : p != 0)
  statement: (2 ^ p - 1 : Int) != 0
  proof: (mersenne_int_pos hp).ne'

中文:
定理 mersenne_int_ne_zero
  条件: (p : 自然数) (hp : p != 0)
  结论: (2 ^ p - 1 : 整数) != 0
  证明: (mersenne_int_pos hp).ne'

Depends on / 依赖: mersenne_int_pos
-/
theorem mersenne_int_ne_zero (p : Nat) (hp : p != 0) : (2 ^ p - 1 : Int) != 0 :=
  (mersenne_int_pos hp).ne'

/--
theorem `sMod_nonneg` / 定理 `sMod_nonneg`

English:
theorem sMod_nonneg
  given: (p : Nat) (hp : p != 0) (i : Nat)
  statement: 0 <= sMod p i
  proof: by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp

中文:
定理 sMod_nonneg
  条件: (p : 自然数) (hp : p != 0) (i : 自然数)
  结论: 0 <= sMod p i
  证明: by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp

Depends on / 依赖: Int.emod_nonneg, emod_nonneg, mersenne_int_ne_zero, sup_eq_right, sup_eq_right.mp
-/
theorem sMod_nonneg (p : Nat) (hp : p != 0) (i : Nat) : 0 <= sMod p i := by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp

/--
theorem `sMod_mod` / 定理 `sMod_mod`

English:
theorem sMod_mod
  given: (p i : Nat)
  statement: sMod p i % (2 ^ p - 1) = sMod p i
  proof: by cases i <;> simp [sMod]

中文:
定理 sMod_mod
  条件: (p i : 自然数)
  结论: sMod p i % (2 ^ p - 1) = sMod p i
  证明: by cases i <;> simp [sMod]
-/
theorem sMod_mod (p i : Nat) : sMod p i % (2 ^ p - 1) = sMod p i := by cases i <;> simp [sMod]

/--
theorem `sMod_lt` / 定理 `sMod_lt`

English:
theorem sMod_lt
  given: (p : Nat) (hp : p != 0) (i : Nat)
  statement: sMod p i < 2 ^ p - 1
  proof: by
  rw [← sMod_mod]
  refine (Int.emod_lt_abs _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le

中文:
定理 sMod_lt
  条件: (p : 自然数) (hp : p != 0) (i : 自然数)
  结论: sMod p i < 2 ^ p - 1
  证明: by
  rw [← sMod_mod]
  refine (Int.emod_lt_abs _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le

Depends on / 依赖: Int.emod_lt_abs, abs_of_nonneg, emod_lt_abs, mersenne_int_ne_zero, mersenne_int_pos, sMod_mod, trans_eq
-/
theorem sMod_lt (p : Nat) (hp : p != 0) (i : Nat) : sMod p i < 2 ^ p - 1 := by
  rw [← sMod_mod]
  refine (Int.emod_lt_abs _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le

/--
theorem `sZMod_eq_s` / 定理 `sZMod_eq_s`

English:
theorem sZMod_eq_s
  given: (p' : Nat) (i : Nat)
  statement: sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1))
  proof: by
  induction i with
  | zero => dsimp [s, sZMod]; simp
  | succ i ih => push_cast [s, sZMod, ih]; rfl

中文:
定理 sZMod_eq_s
  条件: (p' : 自然数) (i : 自然数)
  结论: sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1))
  证明: by
  induction i with
  | zero => dsimp [s, sZMod]; simp
  | succ i ih => push_cast [s, sZMod, ih]; rfl
-/
theorem sZMod_eq_s (p' : Nat) (i : Nat) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1)) := by
  induction i with
  | zero => dsimp [s, sZMod]; simp
  | succ i ih => push_cast [s, sZMod, ih]; rfl

/--
theorem `sZMod_eq_sMod` / 定理 `sZMod_eq_sMod`

English:
theorem sZMod_eq_sMod
  given: (p : Nat) (i : Nat)
  statement: sZMod p i = (sMod p i : ZMod (2 ^ p - 1))
  proof: by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl

中文:
定理 sZMod_eq_sMod
  条件: (p : 自然数) (i : 自然数)
  结论: sZMod p i = (sMod p i : ZMod (2 ^ p - 1))
  证明: by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl

Depends on / 依赖: Int.coe_nat_two_pow_pred, coe_nat_two_pow_pred
-/
theorem sZMod_eq_sMod (p : Nat) (i : Nat) : sZMod p i = (sMod p i : ZMod (2 ^ p - 1)) := by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl

/--
Definition of `lucasLehmerResidue` / `lucasLehmerResidue` 的定义

English:
definition lucasLehmerResidue
  signature: (p : Nat)
  body: sZMod p (p - 2)

中文:
定义 lucasLehmerResidue
  签名: (p : 自然数)
  定义体: sZMod p (p - 2)
-/
def lucasLehmerResidue (p : Nat) : ZMod (2 ^ p - 1) :=
  sZMod p (p - 2)

/--
theorem `residue_eq_zero_iff_sMod_eq_zero` / 定理 `residue_eq_zero_iff_sMod_eq_zero`

English:
theorem residue_eq_zero_iff_sMod_eq_zero
  given: (p : Nat) (w : 1 < p)
  proof: by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _
      (by simpa [ZMod.intCast_zmod_e

中文:
定理 residue_eq_zero_iff_sMod_eq_zero
  条件: (p : 自然数) (w : 1 < p)
  证明: by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _
      (by simpa [ZMod.intCast_zmod_e

Depends on / 依赖: lucasLehmerResidue, sZMod_eq_sMod, s_mod
-/
theorem residue_eq_zero_iff_sMod_eq_zero (p : Nat) (w : 1 < p) :
    lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _
      (by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h) <;> clear h
    · exact sMod_nonneg _ (by positivity) _
    · exact sMod_lt _ (by positivity) _
  · intro h
    rw [h]
    simp

/--
Definition of `LucasLehmerTest` / `LucasLehmerTest` 的定义

English:
definition LucasLehmerTest
  signature: (p : Nat)
  body: lucasLehmerResidue p = 0

中文:
定义 LucasLehmerTest
  签名: (p : 自然数)
  定义体: lucasLehmerResidue p = 0

Depends on / 依赖: lucasLehmerResidue
-/
def LucasLehmerTest (p : Nat) : Prop :=
  lucasLehmerResidue p = 0

/--
Definition of `q` / `q` 的定义

English:
definition q
  signature: (p : Nat)
  body: ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩

中文:
定义 q
  签名: (p : 自然数)
  定义体: ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩

Depends on / 依赖: Nat.minFac, Nat.minFac_pos, mersenne, minFac, minFac_pos
-/
def q (p : Nat) : Nat+ :=
  ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩

-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),
-- obtaining the ring structure for free,
-- but that seems to be more trouble than it's worth;
-- if it were easy to make the definition,
-- cardinality calculations would be somewhat more involved, too.
/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: (q : Nat)
  body: ZMod q × ZMod q

中文:
定义 X
  签名: (q : 自然数)
  定义体: ZMod q × ZMod q
-/
def X (q : Nat) : Type :=
  ZMod q × ZMod q

namespace X

variable {q : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (X q)
  body: inferInstanceAs (Inhabited (ZMod q × ZMod q))

中文:
实例 :
  签名: Inhabited (X q)
  定义体: inferInstanceAs (Inhabited (ZMod q × ZMod q))

Depends on / 依赖: Inhabited
-/
instance : Inhabited (X q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (X q)
  body: inferInstanceAs (DecidableEq (ZMod q × ZMod q))

中文:
实例 :
  签名: DecidableEq (X q)
  定义体: inferInstanceAs (DecidableEq (ZMod q × ZMod q))

Depends on / 依赖: DecidableEq
-/
instance : DecidableEq (X q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (X q)
  body: inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext]

中文:
实例 :
  签名: AddCommGroup (X q)
  定义体: inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext]

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup (X q) := inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2)
  statement: x = y
  proof: by
  cases x; cases y; congr

中文:
定理 ext
  条件: {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2)
  结论: x = y
  证明: by
  cases x; cases y; congr
-/
theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; congr

/--
theorem `zero_fst` / 定理 `zero_fst`

English:
theorem zero_fst
  statement: (0 : X q).1 = 0
  proof: rfl

中文:
定理 zero_fst
  结论: (0 : X q).1 = 0
  证明: rfl
-/
@[simp] theorem zero_fst : (0 : X q).1 = 0 := rfl
/--
theorem `zero_snd` / 定理 `zero_snd`

English:
theorem zero_snd
  statement: (0 : X q).2 = 0
  proof: rfl

@[simp]

中文:
定理 zero_snd
  结论: (0 : X q).2 = 0
  证明: rfl

@[simp]
-/
@[simp] theorem zero_snd : (0 : X q).2 = 0 := rfl

@[simp]
/--
theorem `add_fst` / 定理 `add_fst`

English:
theorem add_fst
  given: (x y : X q)
  statement: (x + y).1 = x.1 + y.1
  proof: rfl

@[simp]

中文:
定理 add_fst
  条件: (x y : X q)
  结论: (x + y).1 = x.1 + y.1
  证明: rfl

@[simp]
-/
theorem add_fst (x y : X q) : (x + y).1 = x.1 + y.1 :=
  rfl

@[simp]
/--
theorem `add_snd` / 定理 `add_snd`

English:
theorem add_snd
  given: (x y : X q)
  statement: (x + y).2 = x.2 + y.2
  proof: rfl

@[simp]

中文:
定理 add_snd
  条件: (x y : X q)
  结论: (x + y).2 = x.2 + y.2
  证明: rfl

@[simp]
-/
theorem add_snd (x y : X q) : (x + y).2 = x.2 + y.2 :=
  rfl

@[simp]
/--
theorem `neg_fst` / 定理 `neg_fst`

English:
theorem neg_fst
  given: (x : X q)
  statement: (-x).1 = -x.1
  proof: rfl

@[simp]

中文:
定理 neg_fst
  条件: (x : X q)
  结论: (-x).1 = -x.1
  证明: rfl

@[simp]
-/
theorem neg_fst (x : X q) : (-x).1 = -x.1 :=
  rfl

@[simp]
/--
theorem `neg_snd` / 定理 `neg_snd`

English:
theorem neg_snd
  given: (x : X q)
  statement: (-x).2 = -x.2
  proof: rfl

中文:
定理 neg_snd
  条件: (x : X q)
  结论: (-x).2 = -x.2
  证明: rfl
-/
theorem neg_snd (x : X q) : (-x).2 = -x.2 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (X q)
  body: (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]

中文:
实例 :
  签名: Mul (X q)
  定义体: (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]
-/
instance : Mul (X q) where mul x y := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]
/--
theorem `mul_fst` / 定理 `mul_fst`

English:
theorem mul_fst
  given: (x y : X q)
  statement: (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2
  proof: rfl

@[simp]

中文:
定理 mul_fst
  条件: (x y : X q)
  结论: (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2
  证明: rfl

@[simp]
-/
theorem mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 :=
  rfl

@[simp]
/--
theorem `mul_snd` / 定理 `mul_snd`

English:
theorem mul_snd
  given: (x y : X q)
  statement: (x * y).2 = x.1 * y.2 + x.2 * y.1
  proof: rfl

中文:
定理 mul_snd
  条件: (x y : X q)
  结论: (x * y).2 = x.1 * y.2 + x.2 * y.1
  证明: rfl
-/
theorem mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (X q)
  body: ⟨1, 0⟩

@[simp]

中文:
实例 :
  签名: One (X q)
  定义体: ⟨1, 0⟩

@[simp]
-/
instance : One (X q) where one := ⟨1, 0⟩

@[simp]
/--
theorem `one_fst` / 定理 `one_fst`

English:
theorem one_fst
  statement: (1 : X q).1 = 1
  proof: rfl

@[simp]

中文:
定理 one_fst
  结论: (1 : X q).1 = 1
  证明: rfl

@[simp]
-/
theorem one_fst : (1 : X q).1 = 1 :=
  rfl

@[simp]
/--
theorem `one_snd` / 定理 `one_snd`

English:
theorem one_snd
  statement: (1 : X q).2 = 0
  proof: rfl

中文:
定理 one_snd
  结论: (1 : X q).2 = 0
  证明: rfl
-/
theorem one_snd : (1 : X q).2 = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (X q)
  body: { (inferInstance : Mul (X q)), (inferInstance : One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }

中文:
实例 :
  签名: Monoid (X q)
  定义体: { (inferInstance : Mul (X q)), (inferInstance : One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }

Depends on / 依赖: mul_assoc, mul_one, one_mul
-/
instance : Monoid (X q) :=
  { (inferInstance : Mul (X q)), (inferInstance : One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (X q)
  body: fun n => ⟨n, 0⟩

中文:
实例 :
  签名: 自然数Cast (X q)
  定义体: fun n => ⟨n, 0⟩
-/
instance : NatCast (X q) where
    natCast := fun n => ⟨n, 0⟩

/--
theorem `fst_natCast` / 定理 `fst_natCast`

English:
theorem fst_natCast
  given: (n : Nat)
  statement: (n : X q).fst = (n : ZMod q)
  proof: rfl

中文:
定理 fst_natCast
  条件: (n : 自然数)
  结论: (n : X q).fst = (n : ZMod q)
  证明: rfl
-/
@[simp] theorem fst_natCast (n : Nat) : (n : X q).fst = (n : ZMod q) := rfl

/--
theorem `snd_natCast` / 定理 `snd_natCast`

English:
theorem snd_natCast
  given: (n : Nat)
  statement: (n : X q).snd = (0 : ZMod q)
  proof: rfl

中文:
定理 snd_natCast
  条件: (n : 自然数)
  结论: (n : X q).snd = (0 : ZMod q)
  证明: rfl
-/
@[simp] theorem snd_natCast (n : Nat) : (n : X q).snd = (0 : ZMod q) := rfl

/--
theorem `ofNat_fst` / 定理 `ofNat_fst`

English:
theorem ofNat_fst
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 ofNat_fst
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[simp] theorem ofNat_fst (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : X q).fst = OfNat.ofNat n :=
  rfl

/--
theorem `ofNat_snd` / 定理 `ofNat_snd`

English:
theorem ofNat_snd
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 ofNat_snd
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[simp] theorem ofNat_snd (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : X q).snd = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroupWithOne (X q)
  body: { (inferInstance : Monoid (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : NatCast (X q)) with
    natCast_zero := by ext <;> simp
    natCast_succ := fun _ => by ext <;> simp
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun 

中文:
实例 :
  签名: AddGroupWithOne (X q)
  定义体: { (inferInstance : Monoid (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : NatCast (X q)) with
    natCast_zero := by ext <;> simp
    natCast_succ := fun _ => by ext <;> simp
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun 

Depends on / 依赖: AddCommGroup, Monoid, NatCast, intCast, intCast_negSucc, intCast_ofNat, natCast_succ, natCast_zero
-/
instance : AddGroupWithOne (X q) :=
  { (inferInstance : Monoid (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : NatCast (X q)) with
    natCast_zero := by ext <;> simp
    natCast_succ := fun _ => by ext <;> simp
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun n => by ext <;> simp }

/--
theorem `left_distrib` / 定理 `left_distrib`

English:
theorem left_distrib
  given: (x y z : X q)
  statement: x * (y + z) = x * y + x * z
  proof: by
  ext <;> dsimp <;> ring

中文:
定理 left_distrib
  条件: (x y z : X q)
  结论: x * (y + z) = x * y + x * z
  证明: by
  ext <;> dsimp <;> ring
-/
theorem left_distrib (x y z : X q) : x * (y + z) = x * y + x * z := by
  ext <;> dsimp <;> ring

/--
theorem `right_distrib` / 定理 `right_distrib`

English:
theorem right_distrib
  given: (x y z : X q)
  statement: (x + y) * z = x * z + y * z
  proof: by
  ext <;> dsimp <;> ring

中文:
定理 right_distrib
  条件: (x y z : X q)
  结论: (x + y) * z = x * z + y * z
  证明: by
  ext <;> dsimp <;> ring
-/
theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;> dsimp <;> ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring (X q)
  body: { (inferInstance : AddGroupWithOne (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ => by ext <;> simp
    zero_mul := fun _ => by ext <;> simp }

中文:
实例 :
  签名: Ring (X q)
  定义体: { (inferInstance : AddGroupWithOne (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ => by ext <;> simp
    zero_mul := fun _ => by ext <;> simp }

Depends on / 依赖: AddCommGroup, AddGroupWithOne, Monoid, left_distrib, mul_zero, right_distrib, zero_mul
-/
instance : Ring (X q) :=
  { (inferInstance : AddGroupWithOne (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ => by ext <;> simp
    zero_mul := fun _ => by ext <;> simp }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (X q)
  body: { (inferInstance : Ring (X q)) with
    mul_comm := fun _ _ => by ext <;> dsimp <;> ring }

中文:
实例 :
  签名: CommRing (X q)
  定义体: { (inferInstance : Ring (X q)) with
    mul_comm := fun _ _ => by ext <;> dsimp <;> ring }

Depends on / 依赖: mul_comm
-/
instance : CommRing (X q) :=
  { (inferInstance : Ring (X q)) with
    mul_comm := fun _ _ => by ext <;> dsimp <;> ring }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: (1 < (q : Nat))] : Nontrivial (X q)
  body: ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

@[simp]

中文:
实例 [Fact
  签名: (1 < (q : 自然数))] : Nontrivial (X q)
  定义体: ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

@[simp]

Depends on / 依赖: Prod.fst, ne_of_apply_ne, zero_ne_one
-/
instance [Fact (1 < (q : Nat))] : Nontrivial (X q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

@[simp]
/--
theorem `fst_intCast` / 定理 `fst_intCast`

English:
theorem fst_intCast
  given: (n : Int)
  statement: (n : X q).fst = (n : ZMod q)
  proof: rfl

@[simp]

中文:
定理 fst_intCast
  条件: (n : 整数)
  结论: (n : X q).fst = (n : ZMod q)
  证明: rfl

@[simp]
-/
theorem fst_intCast (n : Int) : (n : X q).fst = (n : ZMod q) :=
  rfl

@[simp]
/--
theorem `snd_intCast` / 定理 `snd_intCast`

English:
theorem snd_intCast
  given: (n : Int)
  statement: (n : X q).snd = (0 : ZMod q)
  proof: rfl

@[norm_cast]

中文:
定理 snd_intCast
  条件: (n : 整数)
  结论: (n : X q).snd = (0 : ZMod q)
  证明: rfl

@[norm_cast]
-/
theorem snd_intCast (n : Int) : (n : X q).snd = (0 : ZMod q) :=
  rfl

@[norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (n m : Int)
  statement: ((n * m : Int) : X q) = (n : X q) * (m : X q)
  proof: by ext <;> simp

@[norm_cast]

中文:
定理 coe_mul
  条件: (n m : 整数)
  结论: ((n * m : 整数) : X q) = (n : X q) * (m : X q)
  证明: by ext <;> simp

@[norm_cast]
-/
theorem coe_mul (n m : Int) : ((n * m : Int) : X q) = (n : X q) * (m : X q) := by ext <;> simp

@[norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : Int) : X q) = (n : X q)
  proof: by ext <;> simp

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : 整数) : X q) = (n : X q)
  证明: by ext <;> simp
-/
theorem coe_natCast (n : Nat) : ((n : Int) : X q) = (n : X q) := by ext <;> simp

/--
Definition of `ω` / `ω` 的定义

English:
definition ω
  signature: : X q
  body: (2, 1)

中文:
定义 ω
  签名: : X q
  定义体: (2, 1)
-/
def ω : X q := (2, 1)

/--
Definition of `ωb` / `ωb` 的定义

English:
definition ωb
  signature: : X q
  body: (2, -1)

中文:
定义 ωb
  签名: : X q
  定义体: (2, -1)
-/
def ωb : X q := (2, -1)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ω_mul_ωb` / 定理 `ω_mul_ωb`

English:
theorem ω_mul_ωb
  statement: (ω : X q) * ωb = 1
  proof: by
  dsimp [ω, ωb]
  ext <;> simp; ring

中文:
定理 ω_mul_ωb
  结论: (ω : X q) * ωb = 1
  证明: by
  dsimp [ω, ωb]
  ext <;> simp; ring
-/
theorem ω_mul_ωb : (ω : X q) * ωb = 1 := by
  dsimp [ω, ωb]
  ext <;> simp; ring

/--
theorem `ωb_mul_ω` / 定理 `ωb_mul_ω`

English:
theorem ωb_mul_ω
  statement: (ωb : X q) * ω = 1
  proof: by
  rw [mul_comm]; rw [ω_mul_ωb]

中文:
定理 ωb_mul_ω
  结论: (ωb : X q) * ω = 1
  证明: by
  rw [mul_comm]; rw [ω_mul_ωb]

Depends on / 依赖: mul_comm
-/
theorem ωb_mul_ω : (ωb : X q) * ω = 1 := by
  rw [mul_comm]; rw [ω_mul_ωb]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `closed_form` / 定理 `closed_form`

English:
theorem closed_form
  given: (i : Nat)
  statement: (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i
  proof: by
  induction i with
  | zero =>
    dsimp [s, ω, ωb]
    ext <;> norm_num
  | succ i ih =>
    calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : Int) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^

中文:
定理 closed_form
  条件: (i : 自然数)
  结论: (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i
  证明: by
  induction i with
  | zero =>
    dsimp [s, ω, ωb]
    ext <;> norm_num
  | succ i ih =>
    calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : Int) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^

Depends on / 依赖: add_sub_cancel_right, mul_one, mul_pow, one_pow
-/
theorem closed_form (i : Nat) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction i with
  | zero =>
    dsimp [s, ω, ωb]
    ext <;> norm_num
  | succ i ih =>
    calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : Int) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by ring
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_pow ωb ω]; rw [ωb_mul_ω]; rw [one_pow]; rw [mul_one]; rw [add_sub_cancel_right]
      _ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by rw [← pow_mul, ← pow_mul, _root_.pow_succ]

/--
Definition of `α` / `α` 的定义

English:
definition α
  signature: : X q
  body: (0, 1)

中文:
定义 α
  签名: : X q
  定义体: (0, 1)
-/
def α : X q := (0, 1)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `α_sq` / 引理 `α_sq`

English:
lemma α_sq
  statement: (α ^ 2 : X q) = 3
  proof: by
  ext <;> simp [α, sq]

中文:
引理 α_sq
  结论: (α ^ 2 : X q) = 3
  证明: by
  ext <;> simp [α, sq]
-/
@[simp] lemma α_sq : (α ^ 2 : X q) = 3 := by
  ext <;> simp [α, sq]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `one_add_α_sq` / 引理 `one_add_α_sq`

English:
lemma one_add_α_sq
  statement: ((1 + α) ^ 2 : X q) = 2 * ω
  proof: by
  ext <;> simp [α, ω, sq] <;> norm_num

中文:
引理 one_add_α_sq
  结论: ((1 + α) ^ 2 : X q) = 2 * ω
  证明: by
  ext <;> simp [α, ω, sq] <;> norm_num
-/
@[simp] lemma one_add_α_sq : ((1 + α) ^ 2 : X q) = 2 * ω := by
  ext <;> simp [α, ω, sq] <;> norm_num

/--
lemma `α_pow` / 引理 `α_pow`

English:
lemma α_pow
  given: (i : Nat)
  statement: (α : X q) ^ (2 * i + 1) = 3 ^ i * α
  proof: by
  rw [pow_succ]; rw [pow_mul]; rw [α_sq]

中文:
引理 α_pow
  条件: (i : 自然数)
  结论: (α : X q) ^ (2 * i + 1) = 3 ^ i * α
  证明: by
  rw [pow_succ]; rw [pow_mul]; rw [α_sq]

Depends on / 依赖: pow_mul, pow_succ
-/
lemma α_pow (i : Nat) : (α : X q) ^ (2 * i + 1) = 3 ^ i * α := by
  rw [pow_succ]; rw [pow_mul]; rw [α_sq]


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharP (X q) q
  body: by
    convert! ZMod.natCast_eq_zero_iff _ _
    exact ⟨congr_arg Prod.fst, fun hx => ext hx (by simp)⟩

中文:
实例 :
  签名: CharP (X q) q
  定义体: by
    convert! ZMod.natCast_eq_zero_iff _ _
    exact ⟨congr_arg Prod.fst, fun hx => ext hx (by simp)⟩

Depends on / 依赖: Prod.fst, ZMod.natCast_eq_zero_iff, congr_arg, convert, natCast_eq_zero_iff
-/
instance : CharP (X q) q where
  cast_eq_zero_iff x := by
    convert! ZMod.natCast_eq_zero_iff _ _
    exact ⟨congr_arg Prod.fst, fun hx => ext hx (by simp)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ZMod ↑q) (X q)
  body: ZMod.castHom dvd_rfl (X q)

中文:
实例 :
  签名: Coe (ZMod ↑q) (X q)
  定义体: ZMod.castHom dvd_rfl (X q)

Depends on / 依赖: ZMod.castHom, castHom, dvd_rfl
-/
instance : Coe (ZMod ↑q) (X q) where
  coe := ZMod.castHom dvd_rfl (X q)

/--
lemma `one_add_α_pow_q` / 引理 `one_add_α_pow_q`

English:
lemma one_add_α_pow_q
  given: [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1)
  proof: by
  obtain ⟨k, rfl⟩ := odd
  let q := 2 * k + 1
  have : (3 ^ k : ZMod q) = -1 := by
    simpa [leg3, mul_add_div, eq_comm] using legendreSym.eq_pow (2 * k + 1) 3
  rw [add_pow_expChar]; rw [α_pow]; rw [show (3 : X q) = (3 : ZMod q) by rw [map_ofNat], ← map_pow, this,
    map_neg]
  simp [sub_eq_ad

中文:
引理 one_add_α_pow_q
  条件: [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1)
  证明: by
  obtain ⟨k, rfl⟩ := odd
  let q := 2 * k + 1
  have : (3 ^ k : ZMod q) = -1 := by
    simpa [leg3, mul_add_div, eq_comm] using legendreSym.eq_pow (2 * k + 1) 3
  rw [add_pow_expChar]; rw [α_pow]; rw [show (3 : X q) = (3 : ZMod q) by rw [map_ofNat], ← map_pow, this,
    map_neg]
  simp [sub_eq_ad

Depends on / 依赖: add_pow_expChar, eq_comm, eq_pow, legendreSym, legendreSym.eq_pow, map_neg, map_ofNat, map_pow, mul_add_div, sub_eq_add_neg
-/
lemma one_add_α_pow_q [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (1 + α : X q) ^ q = 1 - α := by
  obtain ⟨k, rfl⟩ := odd
  let q := 2 * k + 1
  have : (3 ^ k : ZMod q) = -1 := by
    simpa [leg3, mul_add_div, eq_comm] using legendreSym.eq_pow (2 * k + 1) 3
  rw [add_pow_expChar]; rw [α_pow]; rw [show (3 : X q) = (3 : ZMod q) by rw [map_ofNat], ← map_pow, this,
    map_neg]
  simp [sub_eq_add_neg]

/--
lemma `one_add_α_pow_q_succ` / 引理 `one_add_α_pow_q_succ`

English:
lemma one_add_α_pow_q_succ
  given: [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1)
  proof: by
  rw [pow_succ]; rw [one_add_α_pow_q odd leg3]; rw [mul_comm]; rw [← _root_.sq_sub_sq]; rw [α_sq]
  norm_num

中文:
引理 one_add_α_pow_q_succ
  条件: [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1)
  证明: by
  rw [pow_succ]; rw [one_add_α_pow_q odd leg3]; rw [mul_comm]; rw [← _root_.sq_sub_sq]; rw [α_sq]
  norm_num

Depends on / 依赖: _root_, _root_.sq_sub_sq, mul_comm, pow_succ, sq_sub_sq
-/
lemma one_add_α_pow_q_succ [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (1 + α : X q) ^ (q + 1) = -2 := by
  rw [pow_succ]; rw [one_add_α_pow_q odd leg3]; rw [mul_comm]; rw [← _root_.sq_sub_sq]; rw [α_sq]
  norm_num

/--
lemma `two_mul_ω_pow` / 引理 `two_mul_ω_pow`

English:
lemma two_mul_ω_pow
  given: [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1)
  proof: by
  rw [← one_add_α_sq]; rw [← pow_mul]
  have : 2 * ((q + 1) / 2) = q + 1 := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    exact Odd.add_one odd
  rw [this]; rw [one_add_α_pow_q_succ odd leg3]

中文:
引理 two_mul_ω_pow
  条件: [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1)
  证明: by
  rw [← one_add_α_sq]; rw [← pow_mul]
  have : 2 * ((q + 1) / 2) = q + 1 := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    exact Odd.add_one odd
  rw [this]; rw [one_add_α_pow_q_succ odd leg3]

Depends on / 依赖: Nat.mul_div_cancel, Odd.add_one, add_one, even_iff_two_dvd, mul_div_cancel, pow_mul
-/
lemma two_mul_ω_pow [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (2 * ω : X q) ^ ((q + 1) / 2) = -2 := by
  rw [← one_add_α_sq]; rw [← pow_mul]
  have : 2 * ((q + 1) / 2) = q + 1 := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    exact Odd.add_one odd
  rw [this]; rw [one_add_α_pow_q_succ odd leg3]

/--
lemma `pow_ω` / 引理 `pow_ω`

English:
lemma pow_ω
  statement: [Fact q.Prime] (odd : Odd q)
  proof: by
  have pow2 : (2 : ZMod q) ^ ((q + 1) / 2) = 2 := by
    obtain ⟨_, _⟩ := odd
    rw [(by lia : (q + 1) / 2 = q / 2 + 1)]; rw [pow_succ]
    have leg := legendreSym.eq_pow q 2
    have : (2 : ZMod q) = ((2 : Int) : ZMod q) := by norm_cast
    rw [this]; rw [← leg]; rw [leg2]
    ring
  have := tw

中文:
引理 pow_ω
  结论: [Fact q.Prime] (odd : Odd q)
  证明: by
  have pow2 : (2 : ZMod q) ^ ((q + 1) / 2) = 2 := by
    obtain ⟨_, _⟩ := odd
    rw [(by lia : (q + 1) / 2 = q / 2 + 1)]; rw [pow_succ]
    have leg := legendreSym.eq_pow q 2
    have : (2 : ZMod q) = ((2 : Int) : ZMod q) := by norm_cast
    rw [this]; rw [← leg]; rw [leg2]
    ring
  have := tw

Depends on / 依赖: IsUnit, IsUnit.of_mul_eq_one, eq_pow, legendreSym, legendreSym.eq_pow, map_ofNat, map_pow, mul_pow, of_mul_eq_one, pow_succ
-/
lemma pow_ω [Fact q.Prime] (odd : Odd q)
    (leg3 : legendreSym q 3 = -1)
    (leg2 : legendreSym q 2 = 1) :
    (ω : X q) ^ ((q + 1) / 2) = -1 := by
  have pow2 : (2 : ZMod q) ^ ((q + 1) / 2) = 2 := by
    obtain ⟨_, _⟩ := odd
    rw [(by lia : (q + 1) / 2 = q / 2 + 1)]; rw [pow_succ]
    have leg := legendreSym.eq_pow q 2
    have : (2 : ZMod q) = ((2 : Int) : ZMod q) := by norm_cast
    rw [this]; rw [← leg]; rw [leg2]
    ring
  have := two_mul_ω_pow odd leg3
  rw [mul_pow] at this
  have coe : (2 : X q) = (2 : ZMod q) := by rw [map_ofNat]
  rw [coe]; rw [← map_pow]; rw [pow2]; rw [← coe]; rw [(by ring : (-2 : X q) = 2 * -1)] at this
  refine (IsUnit.of_mul_eq_one (M := X q) ↑((q + 1) / 2) ?_).mul_left_cancel this
  norm_cast
  simp [Nat.mul_div_cancel' odd.add_one.two_dvd]

/--
lemma `ω_pow_trace` / 引理 `ω_pow_trace`

English:
lemma ω_pow_trace
  statement: [Fact q.Prime] (odd : Odd q)
  proof: by
  have : (ω : X q) ^ ((q + 1) / 2) * ωb ^ ((q + 1) / 4) = -ωb ^ ((q + 1) / 4) := by
    rw [pow_ω odd leg3 leg2]
    ring
  have div4 : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by rcases hq4 with ⟨k, hk⟩; lia
  rw [div4]; rw [pow_add]; rw [mul_assoc]; rw [← mul_pow]; rw [ω_mul_ωb]; rw [one_pow]

中文:
引理 ω_pow_trace
  结论: [Fact q.Prime] (odd : Odd q)
  证明: by
  have : (ω : X q) ^ ((q + 1) / 2) * ωb ^ ((q + 1) / 4) = -ωb ^ ((q + 1) / 4) := by
    rw [pow_ω odd leg3 leg2]
    ring
  have div4 : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by rcases hq4 with ⟨k, hk⟩; lia
  rw [div4]; rw [pow_add]; rw [mul_assoc]; rw [← mul_pow]; rw [ω_mul_ωb]; rw [one_pow]

Depends on / 依赖: mul_assoc, mul_one, mul_pow, one_pow, pow_add
-/
lemma ω_pow_trace [Fact q.Prime] (odd : Odd q)
    (leg3 : legendreSym q 3 = -1)
    (leg2 : legendreSym q 2 = 1)
    (hq4 : 4 ∣ q + 1) :
    (ω : X q) ^ ((q + 1) / 4) + ωb ^ ((q + 1) / 4) = 0 := by
  have : (ω : X q) ^ ((q + 1) / 2) * ωb ^ ((q + 1) / 4) = -ωb ^ ((q + 1) / 4) := by
    rw [pow_ω odd leg3 leg2]
    ring
  have div4 : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by rcases hq4 with ⟨k, hk⟩; lia
  rw [div4]; rw [pow_add]; rw [mul_assoc]; rw [← mul_pow]; rw [ω_mul_ωb]; rw [one_pow]; rw [mul_one] at this
  rw [this]
  ring

variable [NeZero q]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (X q)
  body: inferInstanceAs Fintype (ZMod q × ZMod q)

中文:
实例 :
  签名: Fintype (X q)
  定义体: inferInstanceAs Fintype (ZMod q × ZMod q)

Depends on / 依赖: Fintype
-/
instance : Fintype (X q) := inferInstanceAs Fintype (ZMod q × ZMod q)

/--
theorem `card_eq` / 定理 `card_eq`

English:
theorem card_eq
  statement: Fintype.card (X q) = q ^ 2
  proof: by
  change Fintype.card (ZMod q × ZMod q) = q ^ 2
  rw [Fintype.card_prod]; rw [ZMod.card q]; rw [sq]

中文:
定理 card_eq
  结论: Fintype.card (X q) = q ^ 2
  证明: by
  change Fintype.card (ZMod q × ZMod q) = q ^ 2
  rw [Fintype.card_prod]; rw [ZMod.card q]; rw [sq]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_prod, ZMod.card, card_prod
-/
theorem card_eq : Fintype.card (X q) = q ^ 2 := by
  change Fintype.card (ZMod q × ZMod q) = q ^ 2
  rw [Fintype.card_prod]; rw [ZMod.card q]; rw [sq]

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
nonrec theorem card_units_lt (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : Nat)) := ⟨w⟩
  convert! card_units_lt (X q)
  rw [card_eq]

end X

open X

/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/

/--
theorem `two_lt_q` / 定理 `two_lt_q`

English:
theorem two_lt_q
  given: (p' : Nat)
  statement: 2 < q (p' + 2)
  proof: by
  refine (minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · exact le_add_left _ _
  · rw [Ne, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one Nat.one_le_two_pow

中文:
定理 two_lt_q
  条件: (p' : 自然数)
  结论: 2 < q (p' + 2)
  证明: by
  refine (minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · exact le_add_left _ _
  · rw [Ne, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one Nat.one_le_two_pow

Depends on / 依赖: Nat.one_le_two_pow, Nat.pow_succ, Nat.two_not_dvd_two_mul_sub_one, le_add_left, lt_of_ne, mersenne, minFac_eq_two_iff, minFac_prime, one_le_two_pow, one_lt_mersenne, pow_succ, two_le, two_le.lt_of_ne, two_not_dvd_two_mul_sub_one
-/
theorem two_lt_q (p' : Nat) : 2 < q (p' + 2) := by
  refine (minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · exact le_add_left _ _
  · rw [Ne, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one Nat.one_le_two_pow

/--
theorem `ω_pow_formula` / 定理 `ω_pow_formula`

English:
theorem ω_pow_formula
  given: (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0)
  proof: by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  replace h : 2 ^ (p' + 2) - 1 ∣ s p' := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  obtain ⟨k, h⟩ := h
  use k
  replace h := congr_arg (fun n : Int => (n : X (q (p' + 2)))) h
  rw [closed_form] at h
  replace h := congr_arg 

中文:
定理 ω_pow_formula
  条件: (p' : 自然数) (h : lucasLehmerResidue (p' + 2) = 0)
  证明: by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  replace h : 2 ^ (p' + 2) - 1 ∣ s p' := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  obtain ⟨k, h⟩ := h
  use k
  replace h := congr_arg (fun n : Int => (n : X (q (p' + 2)))) h
  rw [closed_form] at h
  replace h := congr_arg 

Depends on / 依赖: ZMod.intCast_zmod_eq_zero_iff_dvd, closed_form, coe_mul, congr_arg, intCast_zmod_eq_zero_iff_dvd, lucasLehmerResidue, mul_add, mul_comm, mul_pow, one_pow, pow_add, replace, sZMod_eq_s
-/
theorem ω_pow_formula (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0) :
    exists k : Int,
      (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) =
        k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  replace h : 2 ^ (p' + 2) - 1 ∣ s p' := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  obtain ⟨k, h⟩ := h
  use k
  replace h := congr_arg (fun n : Int => (n : X (q (p' + 2)))) h
  rw [closed_form] at h
  replace h := congr_arg (fun x => ω ^ 2 ^ p' * x) h
  have t : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  rw [mul_add]; rw [← pow_add ω]; rw [t]; rw [← mul_pow ω ωb (2 ^ p')]; rw [ω_mul_ωb]; rw [one_pow] at h
  rw [mul_comm]; rw [coe_mul] at h
  rw [mul_comm _ (k : X (q (p' + 2)))] at h
  replace h := eq_sub_of_add_eq h
  have : 1 <= 2 ^ (p' + 2) := Nat.one_le_pow _ _ (by decide)
  exact mod_cast h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mersenne_coe_X` / 定理 `mersenne_coe_X`

English:
theorem mersenne_coe_X
  given: (p : Nat)
  statement: (mersenne p : X (q p)) = 0
  proof: by
  ext <;> simp [mersenne, q, ZMod.natCast_eq_zero_iff, Nat.minFac_dvd, -pow_pos]

中文:
定理 mersenne_coe_X
  条件: (p : 自然数)
  结论: (mersenne p : X (q p)) = 0
  证明: by
  ext <;> simp [mersenne, q, ZMod.natCast_eq_zero_iff, Nat.minFac_dvd, -pow_pos]

Depends on / 依赖: Nat.minFac_dvd, ZMod.natCast_eq_zero_iff, mersenne, minFac_dvd, natCast_eq_zero_iff, pow_pos
-/
theorem mersenne_coe_X (p : Nat) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [mersenne, q, ZMod.natCast_eq_zero_iff, Nat.minFac_dvd, -pow_pos]

/--
theorem `ω_pow_eq_neg_one` / 定理 `ω_pow_eq_neg_one`

English:
theorem ω_pow_eq_neg_one
  given: (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0)
  proof: by
  obtain ⟨k, w⟩ := ω_pow_formula p' h
  rw [mersenne_coe_X] at w
  simpa using w

中文:
定理 ω_pow_eq_neg_one
  条件: (p' : 自然数) (h : lucasLehmerResidue (p' + 2) = 0)
  证明: by
  obtain ⟨k, w⟩ := ω_pow_formula p' h
  rw [mersenne_coe_X] at w
  simpa using w

Depends on / 依赖: mersenne_coe_X
-/
theorem ω_pow_eq_neg_one (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  obtain ⟨k, w⟩ := ω_pow_formula p' h
  rw [mersenne_coe_X] at w
  simpa using w

/--
theorem `ω_pow_eq_one` / 定理 `ω_pow_eq_one`

English:
theorem ω_pow_eq_one
  given: (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0)
  proof: calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul]; rw [← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp

中文:
定理 ω_pow_eq_one
  条件: (p' : 自然数) (h : lucasLehmerResidue (p' + 2) = 0)
  证明: calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul]; rw [← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp

Depends on / 依赖: Nat.pow_succ, pow_mul, pow_succ
-/
theorem ω_pow_eq_one (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul]; rw [← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp

/--
Definition of `ωUnit` / `ωUnit` 的定义

English:
definition ωUnit
  signature: (p : Nat)
  body: ω
  inv := ωb
  val_inv := ω_mul_ωb
  inv_val := ωb_mul_ω

@[simp]

中文:
定义 ωUnit
  签名: (p : 自然数)
  定义体: ω
  inv := ωb
  val_inv := ω_mul_ωb
  inv_val := ωb_mul_ω

@[simp]
-/
def ωUnit (p : Nat) : Units (X (q p)) where
  val := ω
  inv := ωb
  val_inv := ω_mul_ωb
  inv_val := ωb_mul_ω

@[simp]
/--
theorem `ωUnit_coe` / 定理 `ωUnit_coe`

English:
theorem ωUnit_coe
  given: (p : Nat)
  statement: (ωUnit p : X (q p)) = ω
  proof: rfl

中文:
定理 ωUnit_coe
  条件: (p : 自然数)
  结论: (ωUnit p : X (q p)) = ω
  证明: rfl
-/
theorem ωUnit_coe (p : Nat) : (ωUnit p : X (q p)) = ω :=
  rfl

/--
theorem `order_ω` / 定理 `order_ω`

English:
theorem order_ω
  given: (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0)
  proof: by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · exact Nat.prime_two
  · intro o
    have ω_pow :=
congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) -> X (q (p' + 2)))
        orderOf_dvd_iff_pow_eq_one.1 o
    have h : (1 : ZMod (q (p' + 2))) = 

中文:
定理 order_ω
  条件: (p' : 自然数) (h : lucasLehmerResidue (p' + 2) = 0)
  证明: by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · exact Nat.prime_two
  · intro o
    have ω_pow :=
congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) -> X (q (p' + 2)))
        orderOf_dvd_iff_pow_eq_one.1 o
    have h : (1 : ZMod (q (p' + 2))) = 

Depends on / 依赖: Nat.eq_prime_pow_of_dvd_least_prime_pow, eq_prime_pow_of_dvd_least_prime_pow
-/
theorem order_ω (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0) :
    orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · exact Nat.prime_two
  · intro o
    have ω_pow :=
congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) -> X (q (p' + 2)))
        orderOf_dvd_iff_pow_eq_one.1 o
    have h : (1 : ZMod (q (p' + 2))) = -1 :=
      congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    have : Fact (2 < (q (p' + 2) : Nat)) := ⟨two_lt_q _⟩
    apply ZMod.neg_one_ne_one h.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact ω_pow_eq_one p' h

/--
theorem `order_ineq` / 定理 `order_ineq`

English:
theorem order_ineq
  given: (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0)
  proof: calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ <= Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < q (p' + 2) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))

中文:
定理 order_ineq
  条件: (p' : 自然数) (h : lucasLehmerResidue (p' + 2) = 0)
  证明: calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ <= Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < q (p' + 2) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))

Depends on / 依赖: Fintype, Fintype.card, Nat.lt_of_succ_lt, card_units_lt, lt_of_succ_lt, orderOf, orderOf_le_card_univ, two_lt_q
-/
theorem order_ineq (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0) :
    2 ^ (p' + 2) < (q (p' + 2) : Nat) ^ 2 :=
  calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ <= Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < q (p' + 2) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))

end LucasLehmer

export LucasLehmer (LucasLehmerTest lucasLehmerResidue)

open LucasLehmer

/-- **Lucas–Lehmer primality test**: sufficiency direction. -/
@[wikidata Q1138992]
/--
theorem `lucas_lehmer_sufficiency` / 定理 `lucas_lehmer_sufficiency`

English:
theorem lucas_lehmer_sufficiency
  given: (p : Nat) (w : 1 < p)
  statement: LucasLehmerTest p -> (mersenne p).Prime
  proof: by
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  e

中文:
定理 lucas_lehmer_sufficiency
  条件: (p : 自然数) (w : 1 < p)
  结论: LucasLehmerTest p -> (mersenne p).Prime
  证明: by
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  e

Depends on / 依赖: Nat.lt_of_sub_eq_succ, Nat.lt_of_succ_lt, Nat.minFac_sq_le_self, Nat.sub_le, clear_value, contrapose, lt_of_lt_of_le, lt_of_sub_eq_succ, lt_of_succ_lt, mersenne_pos, minFac_sq_le_self, not_lt_of_ge, order_ineq, sub_le
-/
theorem lucas_lehmer_sufficiency (p : Nat) (w : 1 < p) : LucasLehmerTest p -> (mersenne p).Prime := by
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  exact not_lt_of_ge (Nat.sub_le _ _) h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lucas_lehmer_necessity` / 定理 `lucas_lehmer_necessity`

English:
theorem lucas_lehmer_necessity
  given: (p : Nat) (w : 3 <= p) (hp : (mersenne p).Prime)
  proof: by
  have : Fact (mersenne p).Prime := ⟨‹_›⟩
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  dsimp [LucasLehmerTest, lucasLehmerResidue]
  rw [sZMod_eq_s p']; rw [← X.fst_intCast]; rw [X.closed_form]; rw [add_tsub_cancel_right]
  have := X.ω_pow_trace (q := mersenne

中文:
定理 lucas_lehmer_necessity
  条件: (p : 自然数) (w : 3 <= p) (hp : (mersenne p).Prime)
  证明: by
  have : Fact (mersenne p).Prime := ⟨‹_›⟩
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  dsimp [LucasLehmerTest, lucasLehmerResidue]
  rw [sZMod_eq_s p']; rw [← X.fst_intCast]; rw [X.closed_form]; rw [add_tsub_cancel_right]
  have := X.ω_pow_trace (q := mersenne

Depends on / 依赖: LucasLehmerTest, X.closed_form, X.fst_intCast, add_tsub_cancel_right, clear_value, closed_form, fst_intCast, hp.of_mersenne.odd_of_ne_two, legendreSym_mersenne_three, legendreSym_mersenne_two, lucasLehmerResidue, mersenne, odd_of_ne_two, of_mersenne, pow_add, sZMod_eq_s, succ_mersenne
-/
theorem lucas_lehmer_necessity (p : Nat) (w : 3 <= p) (hp : (mersenne p).Prime) :
    LucasLehmerTest p := by
  have : Fact (mersenne p).Prime := ⟨‹_›⟩
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  dsimp [LucasLehmerTest, lucasLehmerResidue]
  rw [sZMod_eq_s p']; rw [← X.fst_intCast]; rw [X.closed_form]; rw [add_tsub_cancel_right]
  have := X.ω_pow_trace (q := mersenne (p' + 2)) (by simp)
    (legendreSym_mersenne_three w <| hp.of_mersenne.odd_of_ne_two (by lia))
    (legendreSym_mersenne_two w) (by simp [pow_add])
  rw [succ_mersenne]; rw [pow_add]; rw [show 2 ^ 2 = 4 by norm_num]; rw [mul_div_cancel_right₀ _ (by norm_num)]
    at this
  simp [this]

namespace LucasLehmer

/-!
### `norm_num` extension

Next we define a `norm_num` extension that calculates `LucasLehmerTest p` for `1 < p`.
It makes use of a version of `sMod` that is specifically written to be reducible by the
Lean 4 kernel, which has the capability of efficiently reducing natural number expressions.
With this reduction in hand, it's a simple matter of applying the lemma
`LucasLehmer.residue_eq_zero_iff_sMod_eq_zero`.

See `Archive/Examples/MersennePrimes.lean` for certifications of all Mersenne primes
up through `mersenne 4423`.
-/

namespace norm_num_ext
open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/--
Definition of `sModNat` / `sModNat` 的定义

English:
definition sModNat
  signature: (q : Nat)

中文:
定义 sModNat
  签名: (q : 自然数)
-/
def sModNat (q : Nat) : Nat -> Nat
  | 0 => 4 % q
  | i + 1 => (sModNat q i ^ 2 + (q - 2)) % q

/--
theorem `sModNat_eq_sMod` / 定理 `sModNat_eq_sMod`

English:
theorem sModNat_eq_sMod
  given: (p k : Nat) (hp : 2 <= p)
  statement: (sModNat (2 ^ p - 1) k : Int) = sMod p k
  proof: by
  induction k with
  | zero => grind [sModNat, sMod]
  | succ =>
    have : 2 ^ 2 <= 2 ^ p := Nat.pow_le_pow_right (by lia) hp
    grind [sModNat, sMod, Int.emod_eq_add_self_emod]

中文:
定理 sModNat_eq_sMod
  条件: (p k : 自然数) (hp : 2 <= p)
  结论: (sMod自然数 (2 ^ p - 1) k : 整数) = sMod p k
  证明: by
  induction k with
  | zero => grind [sModNat, sMod]
  | succ =>
    have : 2 ^ 2 <= 2 ^ p := Nat.pow_le_pow_right (by lia) hp
    grind [sModNat, sMod, Int.emod_eq_add_self_emod]

Depends on / 依赖: Int.emod_eq_add_self_emod, Nat.pow_le_pow_right, emod_eq_add_self_emod, pow_le_pow_right, sModNat
-/
theorem sModNat_eq_sMod (p k : Nat) (hp : 2 <= p) : (sModNat (2 ^ p - 1) k : Int) = sMod p k := by
  induction k with
  | zero => grind [sModNat, sMod]
  | succ =>
    have : 2 ^ 2 <= 2 ^ p := Nat.pow_le_pow_right (by lia) hp
    grind [sModNat, sMod, Int.emod_eq_add_self_emod]

/-- Tail-recursive version of `sModNat`. -/
meta def sModNatTR (q k : Nat) : Nat :=
  go k (4 % q)
where
  /-- Helper function for `sMod''`. -/
  go : Nat -> Nat -> Nat
  | 0, acc => acc
  | n + 1, acc => go n ((acc ^ 2 + (q - 2)) % q)
termination_by structural x => x

/--
Definition of `sModNatAux` / `sModNatAux` 的定义

English:
definition sModNatAux
  signature: (b q : Nat)

中文:
定义 sModNatAux
  签名: (b q : 自然数)
-/
def sModNatAux (b q : Nat) : Nat -> Nat
  | 0 => b
  | i + 1 => (sModNatAux b q i ^ 2 + (q - 2)) % q

/--
theorem `sModNatAux_eq` / 定理 `sModNatAux_eq`

English:
theorem sModNatAux_eq
  given: (q k : Nat)
  statement: sModNatAux (4 % q) q k = sModNat q k
  proof: by
  induction k with
  | zero => rfl
  | succ k ih => rw [sModNatAux, ih, sModNat, ← ih]

@[deprecated (since := "2026-06-06")] alias sModNat_aux := sModNatAux
@[deprecated (since := "2026-06-06")] alias sModNat_aux_eq := sModNatAux_eq

中文:
定理 sModNatAux_eq
  条件: (q k : 自然数)
  结论: sMod自然数Aux (4 % q) q k = sMod自然数 q k
  证明: by
  induction k with
  | zero => rfl
  | succ k ih => rw [sModNatAux, ih, sModNat, ← ih]

@[deprecated (since := "2026-06-06")] alias sModNat_aux := sModNatAux
@[deprecated (since := "2026-06-06")] alias sModNat_aux_eq := sModNatAux_eq

Depends on / 依赖: sModNat, sModNatAux
-/
theorem sModNatAux_eq (q k : Nat) : sModNatAux (4 % q) q k = sModNat q k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sModNatAux, ih, sModNat, ← ih]

@[deprecated (since := "2026-06-06")] alias sModNat_aux := sModNatAux
@[deprecated (since := "2026-06-06")] alias sModNat_aux_eq := sModNatAux_eq

/--
theorem `sModNatTR_eq_sModNat` / 定理 `sModNatTR_eq_sModNat`

English:
theorem sModNatTR_eq_sModNat
  given: (q i : Nat)
  statement: sModNatTR q i = sModNat q i
  proof: by
  rw [sModNatTR]; rw [helper]; rw [sModNatAux_eq]

中文:
定理 sModNatTR_eq_sModNat
  条件: (q i : 自然数)
  结论: sMod自然数TR q i = sMod自然数 q i
  证明: by
  rw [sModNatTR]; rw [helper]; rw [sModNatAux_eq]

Depends on / 依赖: helper, sModNatAux_eq, sModNatTR
-/
theorem sModNatTR_eq_sModNat (q i : Nat) : sModNatTR q i = sModNat q i := by
  rw [sModNatTR]; rw [helper]; rw [sModNatAux_eq]
where
  helper b q k : sModNatTR.go q k b = sModNatAux b q k := by
    induction k generalizing b with
    | zero => rfl
    | succ k ih =>
      rw [sModNatTR.go]; rw [ih]; rw [sModNatAux]
      clear ih
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [sModNatAux]; rw [ih]; rw [sModNatAux]

/--
lemma `testTrueHelper` / 引理 `testTrueHelper`

English:
lemma testTrueHelper
  given: (p : Nat) (hp : Nat.blt 1 p = true) (h : sModNatTR (2 ^ p - 1) (p - 2) = 0)
  proof: by
  rw [Nat.blt_eq] at hp
  rw [LucasLehmerTest]; rw [LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp]; rw [← sModNat_eq_sMod p _ hp]; rw [← sModNatTR_eq_sModNat]; rw [h]
  rfl

中文:
引理 testTrueHelper
  条件: (p : 自然数) (hp : 自然数.blt 1 p = true) (h : sMod自然数TR (2 ^ p - 1) (p - 2) = 0)
  证明: by
  rw [Nat.blt_eq] at hp
  rw [LucasLehmerTest]; rw [LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp]; rw [← sModNat_eq_sMod p _ hp]; rw [← sModNatTR_eq_sModNat]; rw [h]
  rfl

Depends on / 依赖: LucasLehmer, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero, LucasLehmerTest, Nat.blt_eq, blt_eq, residue_eq_zero_iff_sMod_eq_zero, sModNatTR_eq_sModNat, sModNat_eq_sMod
-/
lemma testTrueHelper (p : Nat) (hp : Nat.blt 1 p = true) (h : sModNatTR (2 ^ p - 1) (p - 2) = 0) :
    LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [LucasLehmerTest]; rw [LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp]; rw [← sModNat_eq_sMod p _ hp]; rw [← sModNatTR_eq_sModNat]; rw [h]
  rfl

/--
lemma `testFalseHelper` / 引理 `testFalseHelper`

English:
lemma testFalseHelper
  statement: (p : Nat) (hp : Nat.blt 1 p = true)
  proof: by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq]; rw [Nat.succ_le_iff]; rw [Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest]; rw [LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp]; rw [← sModNat_eq_sMod p _ hp]; rw [← sModNatTR_eq_sModNat]
  simpa using h

中文:
引理 testFalseHelper
  结论: (p : 自然数) (hp : 自然数.blt 1 p = true)
  证明: by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq]; rw [Nat.succ_le_iff]; rw [Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest]; rw [LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp]; rw [← sModNat_eq_sMod p _ hp]; rw [← sModNatTR_eq_sModNat]
  simpa using h

Depends on / 依赖: LucasLehmer, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero, LucasLehmerTest, Nat.ble_eq, Nat.blt_eq, Nat.pos_iff_ne_zero, Nat.succ_le_iff, ble_eq, blt_eq, pos_iff_ne_zero, residue_eq_zero_iff_sMod_eq_zero, sModNatTR_eq_sModNat, sModNat_eq_sMod, succ_le_iff
-/
lemma testFalseHelper (p : Nat) (hp : Nat.blt 1 p = true)
    (h : Nat.ble 1 (sModNatTR (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq]; rw [Nat.succ_le_iff]; rw [Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest]; rw [LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp]; rw [← sModNat_eq_sMod p _ hp]; rw [← sModNatTR_eq_sModNat]
  simpa using h

/--
theorem `isNat_lucasLehmerTest` / 定理 `isNat_lucasLehmerTest`

English:
theorem isNat_lucasLehmerTest
  statement: {p np : Nat} ->

中文:
定理 isNat_lucasLehmerTest
  结论: {p np : 自然数} ->
-/
theorem isNat_lucasLehmerTest : {p np : Nat} ->
    IsNat p np -> LucasLehmerTest np -> LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h

/--
theorem `isNat_not_lucasLehmerTest` / 定理 `isNat_not_lucasLehmerTest`

English:
theorem isNat_not_lucasLehmerTest
  statement: {p np : Nat} ->

中文:
定理 isNat_not_lucasLehmerTest
  结论: {p np : 自然数} ->
-/
theorem isNat_not_lucasLehmerTest : {p np : Nat} ->
    IsNat p np -> ¬ LucasLehmerTest np -> ¬ LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h

/-- Calculate `LucasLehmer.LucasLehmerTest p` for `2 ≤ p` by using kernel reduction for the
`sMod'` function. -/
@[norm_num LucasLehmer.LucasLehmerTest (_ : Nat)]
meta def evalLucasLehmerTest : NormNumExt where eval {_ _} e := do
  let .app _ (p : Q(Nat)) ← Meta.whnfR e | failure
  let ⟨ep, hp⟩ ← deriveNat p _
  let np := ep.natLit!
  unless 1 < np do
    failure
haveI' h1ltp : Nat.blt 1 ep =Q true := ⟨⟩
  if sModNatTR (2 ^ np - 1) (np - 2) = 0 then
    haveI' hs : sModNatTR (2 ^ $ep - 1) ($ep - 2) =Q 0 := ⟨⟩
    have pf : Q(LucasLehmerTest $ep) := q(testTrueHelper $ep $h1ltp $hs)
    have pf' : Q(LucasLehmerTest $p) := q(isNat_lucasLehmerTest $hp $pf)
    return .isTrue pf'
  else
    haveI' hs : Nat.ble 1 (sModNatTR (2 ^ $ep - 1) ($ep - 2)) =Q true := ⟨⟩
    have pf : Q(¬ LucasLehmerTest $ep) := q(testFalseHelper $ep $h1ltp $hs)
    have pf' : Q(¬ LucasLehmerTest $p) := q(isNat_not_lucasLehmerTest $hp $pf)
    return .isFalse pf'

end norm_num_ext

end LucasLehmer


/--
theorem `modEq_mersenne` / 定理 `modEq_mersenne`

English:
theorem modEq_mersenne
  given: (n k : Nat)
  statement: k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1]
  proof: -- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
  calc
    k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := (Nat.div_add_mod k (2 ^ n)).symm
    _ ≡ 1 * (k / 2 ^ n) + k % 2 ^ n [MOD 2 ^ n - 1] :=
      ((Nat.modEq_sub <| Nat.succ_le_of_

中文:
定理 modEq_mersenne
  条件: (n k : 自然数)
  结论: k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1]
  证明: -- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
  calc
    k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := (Nat.div_add_mod k (2 ^ n)).symm
    _ ≡ 1 * (k / 2 ^ n) + k % 2 ^ n [MOD 2 ^ n - 1] :=
      ((Nat.modEq_sub <| Nat.succ_le_of_
-/
theorem modEq_mersenne (n k : Nat) : k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1] :=
  -- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
  calc
    k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := (Nat.div_add_mod k (2 ^ n)).symm
    _ ≡ 1 * (k / 2 ^ n) + k % 2 ^ n [MOD 2 ^ n - 1] :=
      ((Nat.modEq_sub <| Nat.succ_le_of_lt <| pow_pos zero_lt_two _).mul_right _).add_right _
    _ = k / 2 ^ n + k % 2 ^ n := by rw [one_mul]

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
