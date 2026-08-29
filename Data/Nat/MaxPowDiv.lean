/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

public import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Notation

/-!
# The maximal power of one natural number dividing another

Here we introduce `p.maxPowDvd n` which returns the maximal `k : ℕ` for
which `p ^ k ∣ n` with the convention that `maxPowDvd 1 n = 0` for all `n`.

We prove enough about `maxPowDvd` in this file to show equality with `Nat.padicValNat` in
`padicValNat.padicValNat_eq_maxPowDvd`.

The implementation of `maxPowDvd` improves on the speed of `padicValNat`.
-/

@[expose] public section

namespace Nat

/--
Definition of `maxPowDvdDiv` / `maxPowDvdDiv` 的定义

English:
definition maxPowDvdDiv
  signature: (p n : Nat)
  body: if H : 1 < p ∧ n != 0 then
    go p H
  else
    (0, n)
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go (p : Nat) (hp : 1 < p ∧ n != 0) :=
    if hmod : n % p = 0 then
let (e, q) := go (p * p) by simp [Nat.one_lt_mul_iff, hp, Nat.lt_trans Nat.one_pos]
      if q % p = 0 then (2 * 

中文:
定义 maxPowDvdDiv
  签名: (p n : 自然数)
  定义体: if H : 1 < p ∧ n != 0 then
    go p H
  else
    (0, n)
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go (p : Nat) (hp : 1 < p ∧ n != 0) :=
    if hmod : n % p = 0 then
let (e, q) := go (p * p) by simp [Nat.one_lt_mul_iff, hp, Nat.lt_trans Nat.one_pos]
      if q % p = 0 then (2 * 
-/
def maxPowDvdDiv (p n : Nat) : Nat × Nat :=
  if H : 1 < p ∧ n != 0 then
    go p H
  else
    (0, n)
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go (p : Nat) (hp : 1 < p ∧ n != 0) :=
    if hmod : n % p = 0 then
let (e, q) := go (p * p) by simp [Nat.one_lt_mul_iff, hp, Nat.lt_trans Nat.one_pos]
      if q % p = 0 then (2 * e + 1, q / p) else (2 * e, q)
    else
      (0, n)
  termination_by n / p
  decreasing_by
    rw [← Nat.dvd_iff_mod_eq_zero] at hmod
    rcases hmod with ⟨m, rfl⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    rw [Nat.mul_div_mul_left _ _ hp₀]; rw [Nat.mul_div_cancel_left _ hp₀]
    exact Nat.div_lt_self (by grind) hp.1

/--
Definition of `_root_.padicValNat` / `_root_.padicValNat` 的定义

English:
definition _root_.padicValNat
  signature: (p n : Nat)
  body: (maxPowDvdDiv p n).fst

中文:
定义 _root_.padicVal自然数
  签名: (p n : 自然数)
  定义体: (maxPowDvdDiv p n).fst

Depends on / 依赖: maxPowDvdDiv
-/
def _root_.padicValNat (p n : Nat) : Nat := (maxPowDvdDiv p n).fst

/--
Definition of `divMaxPow` / `divMaxPow` 的定义

English:
definition divMaxPow
  signature: (n p : Nat)
  body: (maxPowDvdDiv p n).snd

中文:
定义 divMaxPow
  签名: (n p : 自然数)
  定义体: (maxPowDvdDiv p n).snd

Depends on / 依赖: maxPowDvdDiv
-/
def divMaxPow (n p : Nat) : Nat := (maxPowDvdDiv p n).snd

/--
theorem `maxPowDvdDiv.go_spec` / 定理 `maxPowDvdDiv.go_spec`

English:
theorem maxPowDvdDiv.go_spec
  given: {n p : Nat} (hnp)
  proof: by
  fun_induction go with
  | case1 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    simp_all [← Nat.dvd_iff_mod_eq_zero, Nat.pow_add', ← Nat.mul_assoc, Nat.div_mul_cancel,
      Nat.two_mul, Nat.mul_pow]
  | cas

中文:
定理 maxPowDvdDiv.go_spec
  条件: {n p : 自然数} (hnp)
  证明: by
  fun_induction go with
  | case1 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    simp_all [← Nat.dvd_iff_mod_eq_zero, Nat.pow_add', ← Nat.mul_assoc, Nat.div_mul_cancel,
      Nat.two_mul, Nat.mul_pow]
  | cas

Depends on / 依赖: Nat.div_mul_cancel, Nat.dvd_iff_mod_eq_zero, Nat.lt_trans, Nat.mul_assoc, Nat.mul_pow, Nat.one_pos, Nat.pow_add, Nat.two_mul, div_mul_cancel, dvd_iff_mod_eq_zero, fun_induction, lt_trans, mul_assoc, mul_pow, one_pos, pow_add, two_mul
-/
theorem maxPowDvdDiv.go_spec {n p : Nat} (hnp) :
    (go n p hnp).2 * p ^ (go n p hnp).1 = n ∧ ¬p ∣ (go n p hnp).2 := by
  fun_induction go with
  | case1 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    simp_all [← Nat.dvd_iff_mod_eq_zero, Nat.pow_add', ← Nat.mul_assoc, Nat.div_mul_cancel,
      Nat.two_mul, Nat.mul_pow]
  | case2 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    simp_all [Nat.dvd_iff_mod_eq_zero, Nat.two_mul, Nat.mul_pow, Nat.pow_add]
  | case3 =>
    simp_all [Nat.dvd_iff_mod_eq_zero]

/--
theorem `maxPowDvdDiv_of_base_le_one` / 定理 `maxPowDvdDiv_of_base_le_one`

English:
theorem maxPowDvdDiv_of_base_le_one
  given: {p : Nat} (hp : p <= 1) (n : Nat)
  statement: maxPowDvdDiv p n = (0, n)
  proof: by
  simp [maxPowDvdDiv, Nat.not_lt_of_ge hp]

@[simp]

中文:
定理 maxPowDvdDiv_of_base_le_one
  条件: {p : 自然数} (hp : p <= 1) (n : 自然数)
  结论: maxPowDvdDiv p n = (0, n)
  证明: by
  simp [maxPowDvdDiv, Nat.not_lt_of_ge hp]

@[simp]

Depends on / 依赖: Nat.not_lt_of_ge, maxPowDvdDiv, not_lt_of_ge
-/
theorem maxPowDvdDiv_of_base_le_one {p : Nat} (hp : p <= 1) (n : Nat) : maxPowDvdDiv p n = (0, n) := by
  simp [maxPowDvdDiv, Nat.not_lt_of_ge hp]

@[simp]
/--
theorem `maxPowDvdDiv_zero_left` / 定理 `maxPowDvdDiv_zero_left`

English:
theorem maxPowDvdDiv_zero_left
  given: (n : Nat)
  statement: maxPowDvdDiv 0 n = (0, n)
  proof: maxPowDvdDiv_of_base_le_one (Nat.zero_le _) _

@[simp]

中文:
定理 maxPowDvdDiv_zero_left
  条件: (n : 自然数)
  结论: maxPowDvdDiv 0 n = (0, n)
  证明: maxPowDvdDiv_of_base_le_one (Nat.zero_le _) _

@[simp]

Depends on / 依赖: Nat.zero_le, maxPowDvdDiv_of_base_le_one, zero_le
-/
theorem maxPowDvdDiv_zero_left (n : Nat) : maxPowDvdDiv 0 n = (0, n) :=
  maxPowDvdDiv_of_base_le_one (Nat.zero_le _) _

@[simp]
/--
theorem `_root_.padicValNat_zero_left` / 定理 `_root_.padicValNat_zero_left`

English:
theorem _root_.padicValNat_zero_left
  given: (n : Nat)
  statement: padicValNat 0 n = 0
  proof: by simp [padicValNat]

@[simp]

中文:
定理 _root_.padicVal自然数_zero_left
  条件: (n : 自然数)
  结论: padicVal自然数 0 n = 0
  证明: by simp [padicValNat]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_zero_left (n : Nat) : padicValNat 0 n = 0 := by simp [padicValNat]

@[simp]
/--
theorem `divMaxPow_zero_right` / 定理 `divMaxPow_zero_right`

English:
theorem divMaxPow_zero_right
  given: (n : Nat)
  statement: divMaxPow n 0 = n
  proof: by simp [divMaxPow]

@[simp]

中文:
定理 divMaxPow_zero_right
  条件: (n : 自然数)
  结论: divMaxPow n 0 = n
  证明: by simp [divMaxPow]

@[simp]

Depends on / 依赖: divMaxPow
-/
theorem divMaxPow_zero_right (n : Nat) : divMaxPow n 0 = n := by simp [divMaxPow]

@[simp]
/--
theorem `maxPowDvdDiv_one_left` / 定理 `maxPowDvdDiv_one_left`

English:
theorem maxPowDvdDiv_one_left
  given: (n : Nat)
  statement: maxPowDvdDiv 1 n = (0, n)
  proof: maxPowDvdDiv_of_base_le_one (Nat.le_refl _) _

@[simp]

中文:
定理 maxPowDvdDiv_one_left
  条件: (n : 自然数)
  结论: maxPowDvdDiv 1 n = (0, n)
  证明: maxPowDvdDiv_of_base_le_one (Nat.le_refl _) _

@[simp]

Depends on / 依赖: Nat.le_refl, le_refl, maxPowDvdDiv_of_base_le_one
-/
theorem maxPowDvdDiv_one_left (n : Nat) : maxPowDvdDiv 1 n = (0, n) :=
  maxPowDvdDiv_of_base_le_one (Nat.le_refl _) _

@[simp]
/--
theorem `_root_.padicValNat_one_left` / 定理 `_root_.padicValNat_one_left`

English:
theorem _root_.padicValNat_one_left
  given: (n : Nat)
  statement: padicValNat 1 n = 0
  proof: by simp [padicValNat]

@[simp]

中文:
定理 _root_.padicVal自然数_one_left
  条件: (n : 自然数)
  结论: padicVal自然数 1 n = 0
  证明: by simp [padicValNat]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_one_left (n : Nat) : padicValNat 1 n = 0 := by simp [padicValNat]

@[simp]
/--
theorem `divMaxPow_one_right` / 定理 `divMaxPow_one_right`

English:
theorem divMaxPow_one_right
  given: (n : Nat)
  statement: divMaxPow n 1 = n
  proof: by simp [divMaxPow]

@[simp]

中文:
定理 divMaxPow_one_right
  条件: (n : 自然数)
  结论: divMaxPow n 1 = n
  证明: by simp [divMaxPow]

@[simp]

Depends on / 依赖: divMaxPow
-/
theorem divMaxPow_one_right (n : Nat) : divMaxPow n 1 = n := by simp [divMaxPow]

@[simp]
/--
theorem `maxPowDvdDiv_zero_right` / 定理 `maxPowDvdDiv_zero_right`

English:
theorem maxPowDvdDiv_zero_right
  given: (p : Nat)
  statement: maxPowDvdDiv p 0 = (0, 0)
  proof: by simp [maxPowDvdDiv]

@[simp]

中文:
定理 maxPowDvdDiv_zero_right
  条件: (p : 自然数)
  结论: maxPowDvdDiv p 0 = (0, 0)
  证明: by simp [maxPowDvdDiv]

@[simp]

Depends on / 依赖: maxPowDvdDiv
-/
theorem maxPowDvdDiv_zero_right (p : Nat) : maxPowDvdDiv p 0 = (0, 0) := by simp [maxPowDvdDiv]

@[simp]
/--
theorem `_root_.padicValNat_zero_right` / 定理 `_root_.padicValNat_zero_right`

English:
theorem _root_.padicValNat_zero_right
  given: (p : Nat)
  statement: padicValNat p 0 = 0
  proof: by simp [padicValNat]

@[simp]

中文:
定理 _root_.padicVal自然数_zero_right
  条件: (p : 自然数)
  结论: padicVal自然数 p 0 = 0
  证明: by simp [padicValNat]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_zero_right (p : Nat) : padicValNat p 0 = 0 := by simp [padicValNat]

@[simp]
/--
theorem `divMaxPow_zero_left` / 定理 `divMaxPow_zero_left`

English:
theorem divMaxPow_zero_left
  given: (p : Nat)
  statement: divMaxPow 0 p = 0
  proof: by simp [divMaxPow]

中文:
定理 divMaxPow_zero_left
  条件: (p : 自然数)
  结论: divMaxPow 0 p = 0
  证明: by simp [divMaxPow]

Depends on / 依赖: divMaxPow
-/
theorem divMaxPow_zero_left (p : Nat) : divMaxPow 0 p = 0 := by simp [divMaxPow]

/--
theorem `maxPowDvdDiv_of_not_dvd` / 定理 `maxPowDvdDiv_of_not_dvd`

English:
theorem maxPowDvdDiv_of_not_dvd
  given: {p n : Nat} (h : ¬p ∣ n)
  statement: maxPowDvdDiv p n = (0, n)
  proof: by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]

中文:
定理 maxPowDvdDiv_of_not_dvd
  条件: {p n : 自然数} (h : ¬p ∣ n)
  结论: maxPowDvdDiv p n = (0, n)
  证明: by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero.not.mp, dvd_iff_mod_eq_zero, maxPowDvdDiv, maxPowDvdDiv.go
-/
theorem maxPowDvdDiv_of_not_dvd {p n : Nat} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, n) := by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]
/--
theorem `maxPowDvdDiv_one_right` / 定理 `maxPowDvdDiv_one_right`

English:
theorem maxPowDvdDiv_one_right
  given: (p : Nat)
  statement: maxPowDvdDiv p 1 = (0, 1)
  proof: by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [maxPowDvdDiv_of_not_dvd, *]

@[simp]

中文:
定理 maxPowDvdDiv_one_right
  条件: (p : 自然数)
  结论: maxPowDvdDiv p 1 = (0, 1)
  证明: by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [maxPowDvdDiv_of_not_dvd, *]

@[simp]

Depends on / 依赖: eq_or_ne, maxPowDvdDiv_of_not_dvd
-/
theorem maxPowDvdDiv_one_right (p : Nat) : maxPowDvdDiv p 1 = (0, 1) := by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [maxPowDvdDiv_of_not_dvd, *]

@[simp]
/--
theorem `_root_.padicValNat_one_right` / 定理 `_root_.padicValNat_one_right`

English:
theorem _root_.padicValNat_one_right
  given: (p : Nat)
  statement: padicValNat p 1 = 0
  proof: by simp [padicValNat]

@[simp]

中文:
定理 _root_.padicVal自然数_one_right
  条件: (p : 自然数)
  结论: padicVal自然数 p 1 = 0
  证明: by simp [padicValNat]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_one_right (p : Nat) : padicValNat p 1 = 0 := by simp [padicValNat]

@[simp]
/--
theorem `divMaxPow_one_left` / 定理 `divMaxPow_one_left`

English:
theorem divMaxPow_one_left
  given: (p : Nat)
  statement: divMaxPow 1 p = 1
  proof: by simp [divMaxPow]

中文:
定理 divMaxPow_one_left
  条件: (p : 自然数)
  结论: divMaxPow 1 p = 1
  证明: by simp [divMaxPow]

Depends on / 依赖: divMaxPow
-/
theorem divMaxPow_one_left (p : Nat) : divMaxPow 1 p = 1 := by simp [divMaxPow]

open maxPowDvdDiv in
@[simp]
/--
theorem `divMaxPow_mul_pow_padicValNat` / 定理 `divMaxPow_mul_pow_padicValNat`

English:
theorem divMaxPow_mul_pow_padicValNat
  given: (p n : Nat)
  statement: divMaxPow n p * p ^ padicValNat p n = n
  proof: by
  unfold divMaxPow padicValNat
  fun_cases maxPowDvdDiv with
.1 | case1 h => exact go_spec h
  | case2 h => simp

@[simp]

中文:
定理 divMaxPow_mul_pow_padicVal自然数
  条件: (p n : 自然数)
  结论: divMaxPow n p * p ^ padicVal自然数 p n = n
  证明: by
  unfold divMaxPow padicValNat
  fun_cases maxPowDvdDiv with
.1 | case1 h => exact go_spec h
  | case2 h => simp

@[simp]

Depends on / 依赖: divMaxPow, fun_cases, go_spec, maxPowDvdDiv, padicValNat
-/
theorem divMaxPow_mul_pow_padicValNat (p n : Nat) : divMaxPow n p * p ^ padicValNat p n = n := by
  unfold divMaxPow padicValNat
  fun_cases maxPowDvdDiv with
.1 | case1 h => exact go_spec h
  | case2 h => simp

@[simp]
/--
theorem `pow_padicValNat_mul_divMaxPow` / 定理 `pow_padicValNat_mul_divMaxPow`

English:
theorem pow_padicValNat_mul_divMaxPow
  given: (p n : Nat)
  statement: p ^ padicValNat p n * divMaxPow n p = n
  proof: by
  rw [Nat.mul_comm]; rw [divMaxPow_mul_pow_padicValNat]

中文:
定理 pow_padicVal自然数_mul_divMaxPow
  条件: (p n : 自然数)
  结论: p ^ padicVal自然数 p n * divMaxPow n p = n
  证明: by
  rw [Nat.mul_comm]; rw [divMaxPow_mul_pow_padicValNat]

Depends on / 依赖: Nat.mul_comm, divMaxPow_mul_pow_padicValNat, mul_comm
-/
theorem pow_padicValNat_mul_divMaxPow (p n : Nat) : p ^ padicValNat p n * divMaxPow n p = n := by
  rw [Nat.mul_comm]; rw [divMaxPow_mul_pow_padicValNat]

/--
theorem `_root_.pow_padicValNat_dvd` / 定理 `_root_.pow_padicValNat_dvd`

English:
theorem _root_.pow_padicValNat_dvd
  given: {p n : Nat}
  statement: p ^ padicValNat p n ∣ n
  proof: ⟨divMaxPow n p, by simp⟩

中文:
定理 _root_.pow_padicVal自然数_dvd
  条件: {p n : 自然数}
  结论: p ^ padicVal自然数 p n ∣ n
  证明: ⟨divMaxPow n p, by simp⟩

Depends on / 依赖: divMaxPow
-/
theorem _root_.pow_padicValNat_dvd {p n : Nat} : p ^ padicValNat p n ∣ n :=
  ⟨divMaxPow n p, by simp⟩

/--
theorem `padicValNat_lt_self` / 定理 `padicValNat_lt_self`

English:
theorem padicValNat_lt_self
  given: {p n : Nat} (hn : n != 0)
  statement: padicValNat p n < n
  proof: by
  match p with
  | 0 | 1 => simp [Nat.pos_of_ne_zero hn]
  | p + 2 =>
    apply (p + 2 |>.pow_lt_pow_iff_right <| by lia).mp
apply Nat.lt_of_le_of_lt ?_ Nat.lt_pow_self by lia
    exact le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

中文:
定理 padicVal自然数_lt_self
  条件: {p n : 自然数} (hn : n != 0)
  结论: padicVal自然数 p n < n
  证明: by
  match p with
  | 0 | 1 => simp [Nat.pos_of_ne_zero hn]
  | p + 2 =>
    apply (p + 2 |>.pow_lt_pow_iff_right <| by lia).mp
apply Nat.lt_of_le_of_lt ?_ Nat.lt_pow_self by lia
    exact le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

Depends on / 依赖: Nat.lt_of_le_of_lt, Nat.lt_pow_self, Nat.pos_of_ne_zero, le_of_dvd, lt_of_le_of_lt, lt_pow_self, pos_of_ne_zero, pow_lt_pow_iff_right, pow_padicValNat_dvd
-/
theorem padicValNat_lt_self {p n : Nat} (hn : n != 0) : padicValNat p n < n := by
  match p with
  | 0 | 1 => simp [Nat.pos_of_ne_zero hn]
  | p + 2 =>
    apply (p + 2 |>.pow_lt_pow_iff_right <| by lia).mp
apply Nat.lt_of_le_of_lt ?_ Nat.lt_pow_self by lia
    exact le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

/--
theorem `padicValNat_le_self` / 定理 `padicValNat_le_self`

English:
theorem padicValNat_le_self
  given: {p : Nat} (n : Nat)
  statement: padicValNat p n <= n
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
· exact Nat.le_of_lt padicValNat_lt_self hn

中文:
定理 padicVal自然数_le_self
  条件: {p : 自然数} (n : 自然数)
  结论: padicVal自然数 p n <= n
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
· exact Nat.le_of_lt padicValNat_lt_self hn

Depends on / 依赖: Nat.le_of_lt, eq_or_ne, le_of_lt, padicValNat_lt_self
-/
theorem padicValNat_le_self {p : Nat} (n : Nat) : padicValNat p n <= n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
· exact Nat.le_of_lt padicValNat_lt_self hn

/--
theorem `not_dvd_divMaxPow` / 定理 `not_dvd_divMaxPow`

English:
theorem not_dvd_divMaxPow
  given: {p n : Nat} (hp : 1 < p) (hn : n != 0)
  statement: ¬p ∣ divMaxPow n p
  proof: by
  simp [divMaxPow, maxPowDvdDiv, maxPowDvdDiv.go_spec, *]

中文:
定理 not_dvd_divMaxPow
  条件: {p n : 自然数} (hp : 1 < p) (hn : n != 0)
  结论: ¬p ∣ divMaxPow n p
  证明: by
  simp [divMaxPow, maxPowDvdDiv, maxPowDvdDiv.go_spec, *]

Depends on / 依赖: divMaxPow, go_spec, maxPowDvdDiv, maxPowDvdDiv.go_spec
-/
theorem not_dvd_divMaxPow {p n : Nat} (hp : 1 < p) (hn : n != 0) : ¬p ∣ divMaxPow n p := by
  simp [divMaxPow, maxPowDvdDiv, maxPowDvdDiv.go_spec, *]

/--
theorem `pow_dvd_iff_le_of_spec` / 定理 `pow_dvd_iff_le_of_spec`

English:
theorem pow_dvd_iff_le_of_spec
  statement: {p k n a b : Nat} (hp : 1 < p) (hn : n != 0)
  proof: by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd => ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc]; rw [Nat.pow_add]; rw [Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
exact hb

中文:
定理 pow_dvd_iff_le_of_spec
  结论: {p k n a b : 自然数} (hp : 1 < p) (hn : n != 0)
  证明: by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd => ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc]; rw [Nat.pow_add]; rw [Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
exact hb
-/
private theorem pow_dvd_iff_le_of_spec {p k n a b : Nat} (hp : 1 < p) (hn : n != 0)
    (hab : p ^ a * b = n) (hb : ¬p ∣ b) : p ^ k ∣ n ↔ k <= a := by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd => ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc]; rw [Nat.pow_add]; rw [Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
exact hb Nat.dvd_of_pow_dvd (Nat.le_add_left 1 l) hdvd
  | inr hle =>
    refine iff_of_true (Nat.dvd_mul_right_of_dvd ?_ _) hle
    exact Nat.pow_dvd_pow p hle

/--
theorem `pow_dvd_iff_le_padicValNat` / 定理 `pow_dvd_iff_le_padicValNat`

English:
theorem pow_dvd_iff_le_padicValNat
  given: {p k n : Nat} (hp : p != 1) (hn : n != 0)
  proof: by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_padicValNat_mul_divMaxPow p n)
      (not_dvd_divMaxPow hp₁ hn)

中文:
定理 pow_dvd_iff_le_padicVal自然数
  条件: {p k n : 自然数} (hp : p != 1) (hn : n != 0)
  证明: by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_padicValNat_mul_divMaxPow p n)
      (not_dvd_divMaxPow hp₁ hn)

Depends on / 依赖: Nat.ne_of_gt, eq_zero_or_pos, k.eq_zero_or_pos, ne_of_gt, not_dvd_divMaxPow, pow_dvd_iff_le_of_spec, pow_padicValNat_mul_divMaxPow
-/
theorem pow_dvd_iff_le_padicValNat {p k n : Nat} (hp : p != 1) (hn : n != 0) :
    p ^ k ∣ n ↔ k <= padicValNat p n := by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_padicValNat_mul_divMaxPow p n)
      (not_dvd_divMaxPow hp₁ hn)

/--
theorem `maxPowDvdDiv_of_pow_mul_eq` / 定理 `maxPowDvdDiv_of_pow_mul_eq`

English:
theorem maxPowDvdDiv_of_pow_mul_eq
  statement: {p n k l : Nat} (hn : n != 0) (h : p ^ k * l = n)
  proof: by
  obtain rfl | rfl | hp : p = 0 ∨ p = 1 ∨ 1 < p := by grind
  · cases k.eq_zero_or_pos <;> simp_all
  · simp_all
  · have hk : k = (p.maxPowDvdDiv n).1 := by
      · apply Nat.le_antisymm
        · rw [← padicValNat, ← pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn,
            pow_dvd_iff_le_of

中文:
定理 maxPowDvdDiv_of_pow_mul_eq
  结论: {p n k l : 自然数} (hn : n != 0) (h : p ^ k * l = n)
  证明: by
  obtain rfl | rfl | hp : p = 0 ∨ p = 1 ∨ 1 < p := by grind
  · cases k.eq_zero_or_pos <;> simp_all
  · simp_all
  · have hk : k = (p.maxPowDvdDiv n).1 := by
      · apply Nat.le_antisymm
        · rw [← padicValNat, ← pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn,
            pow_dvd_iff_le_of

Depends on / 依赖: Nat.le_antisymm, Nat.le_refl, Nat.mul_left_ca, Nat.ne_of_gt, eq_zero_or_pos, k.eq_zero_or_pos, le_antisymm, le_refl, maxPowDvdDiv, mul_left_ca, ne_of_gt, p.maxPowDvdDiv, padicValNat, pow_dvd_iff_le_of_spec, pow_dvd_iff_le_padicValNat, pow_padicValNat_mul_divMaxPow
-/
theorem maxPowDvdDiv_of_pow_mul_eq {p n k l : Nat} (hn : n != 0) (h : p ^ k * l = n)
    (hl : ¬p ∣ l) : maxPowDvdDiv p n = (k, l) := by
  obtain rfl | rfl | hp : p = 0 ∨ p = 1 ∨ 1 < p := by grind
  · cases k.eq_zero_or_pos <;> simp_all
  · simp_all
  · have hk : k = (p.maxPowDvdDiv n).1 := by
      · apply Nat.le_antisymm
        · rw [← padicValNat, ← pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn,
            pow_dvd_iff_le_of_spec hp hn h hl]
          apply Nat.le_refl
        · rw [← pow_dvd_iff_le_of_spec hp hn h hl, pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn]
          apply Nat.le_refl
    rw [← pow_padicValNat_mul_divMaxPow p n]; rw [hk]; rw [padicValNat]; rw [Nat.mul_left_cancel_iff] at h
    · exact Prod.ext hk.symm h.symm
· exact Nat.pow_pos Nat.zero_lt_of_lt hp

@[simp]
/--
theorem `maxPowDvdDiv_base_pow_mul` / 定理 `maxPowDvdDiv_base_pow_mul`

English:
theorem maxPowDvdDiv_base_pow_mul
  given: {p n : Nat} (hp : 1 < p) (hn : n != 0) (k : Nat)
  proof: by
  apply maxPowDvdDiv_of_pow_mul_eq
  · exact Nat.mul_ne_zero (Nat.ne_of_gt <| Nat.pow_pos <| Nat.zero_lt_of_lt hp) hn
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_padicValNat_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]

中文:
定理 maxPowDvdDiv_base_pow_mul
  条件: {p n : 自然数} (hp : 1 < p) (hn : n != 0) (k : 自然数)
  证明: by
  apply maxPowDvdDiv_of_pow_mul_eq
  · exact Nat.mul_ne_zero (Nat.ne_of_gt <| Nat.pow_pos <| Nat.zero_lt_of_lt hp) hn
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_padicValNat_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]

Depends on / 依赖: Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_ne_zero, Nat.ne_of_gt, Nat.pow_add, Nat.pow_pos, Nat.zero_lt_of_lt, maxPowDvdDiv_of_pow_mul_eq, mul_assoc, mul_left_comm, mul_ne_zero, ne_of_gt, not_dvd_divMaxPow, pow_add, pow_padicValNat_mul_divMaxPow, pow_pos, zero_lt_of_lt
-/
theorem maxPowDvdDiv_base_pow_mul {p n : Nat} (hp : 1 < p) (hn : n != 0) (k : Nat) :
    p.maxPowDvdDiv (p ^ k * n) = (padicValNat p n + k, divMaxPow n p) := by
  apply maxPowDvdDiv_of_pow_mul_eq
  · exact Nat.mul_ne_zero (Nat.ne_of_gt <| Nat.pow_pos <| Nat.zero_lt_of_lt hp) hn
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_padicValNat_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]
/--
theorem `_root_.padicValNat_base_pow_mul` / 定理 `_root_.padicValNat_base_pow_mul`

English:
theorem _root_.padicValNat_base_pow_mul
  given: {p n : Nat} (hp : 1 < p) (hn : n != 0) (k : Nat)
  proof: by
  simp [padicValNat, *]

@[simp]

中文:
定理 _root_.padicVal自然数_base_pow_mul
  条件: {p n : 自然数} (hp : 1 < p) (hn : n != 0) (k : 自然数)
  证明: by
  simp [padicValNat, *]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_base_pow_mul {p n : Nat} (hp : 1 < p) (hn : n != 0) (k : Nat) :
    padicValNat p (p ^ k * n) = padicValNat p n + k := by
  simp [padicValNat, *]

@[simp]
/--
theorem `divMaxPow_base_pow_mul` / 定理 `divMaxPow_base_pow_mul`

English:
theorem divMaxPow_base_pow_mul
  given: {p : Nat} (hp : p != 0) (n k : Nat)
  proof: by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [divMaxPow, *]

@[simp]

中文:
定理 divMaxPow_base_pow_mul
  条件: {p : 自然数} (hp : p != 0) (n k : 自然数)
  证明: by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [divMaxPow, *]

@[simp]

Depends on / 依赖: divMaxPow, eq_or_ne
-/
theorem divMaxPow_base_pow_mul {p : Nat} (hp : p != 0) (n k : Nat) :
    (p ^ k * n).divMaxPow p = n.divMaxPow p := by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [divMaxPow, *]

@[simp]
/--
theorem `maxPowDvdDiv_base_mul` / 定理 `maxPowDvdDiv_base_mul`

English:
theorem maxPowDvdDiv_base_mul
  given: {p n : Nat} (hp : 1 < p) (hn : n != 0)
  proof: by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1

@[simp]

中文:
定理 maxPowDvdDiv_base_mul
  条件: {p n : 自然数} (hp : 1 < p) (hn : n != 0)
  证明: by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1

@[simp]

Depends on / 依赖: maxPowDvdDiv_base_pow_mul
-/
theorem maxPowDvdDiv_base_mul {p n : Nat} (hp : 1 < p) (hn : n != 0) :
    p.maxPowDvdDiv (p * n) = (padicValNat p n + 1, divMaxPow n p) := by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1

@[simp]
/--
theorem `_root_.padicValNat_base_mul` / 定理 `_root_.padicValNat_base_mul`

English:
theorem _root_.padicValNat_base_mul
  given: {p n : Nat} (hp : 1 < p) (hn : n != 0)
  proof: by
  simp [padicValNat, *]

@[simp]

中文:
定理 _root_.padicVal自然数_base_mul
  条件: {p n : 自然数} (hp : 1 < p) (hn : n != 0)
  证明: by
  simp [padicValNat, *]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_base_mul {p n : Nat} (hp : 1 < p) (hn : n != 0) :
    padicValNat p (p * n) = padicValNat p n + 1 := by
  simp [padicValNat, *]

@[simp]
/--
theorem `divMaxPow_base_mul` / 定理 `divMaxPow_base_mul`

English:
theorem divMaxPow_base_mul
  given: {p : Nat} (hp : p != 0) (n : Nat)
  proof: by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]

中文:
定理 divMaxPow_base_mul
  条件: {p : 自然数} (hp : p != 0) (n : 自然数)
  证明: by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]

Depends on / 依赖: divMaxPow_base_pow_mul
-/
theorem divMaxPow_base_mul {p : Nat} (hp : p != 0) (n : Nat) :
    (p * n).divMaxPow p = n.divMaxPow p := by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]
/--
theorem `maxPowDvdDiv_base_pow` / 定理 `maxPowDvdDiv_base_pow`

English:
theorem maxPowDvdDiv_base_pow
  given: {p : Nat} (hp : 1 < p) (k : Nat)
  statement: p.maxPowDvdDiv (p ^ k) = (k, 1)
  proof: by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k

@[simp]

中文:
定理 maxPowDvdDiv_base_pow
  条件: {p : 自然数} (hp : 1 < p) (k : 自然数)
  结论: p.maxPowDvdDiv (p ^ k) = (k, 1)
  证明: by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k

@[simp]

Depends on / 依赖: Nat.one_ne_zero, maxPowDvdDiv_base_pow_mul, one_ne_zero
-/
theorem maxPowDvdDiv_base_pow {p : Nat} (hp : 1 < p) (k : Nat) : p.maxPowDvdDiv (p ^ k) = (k, 1) := by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k

@[simp]
/--
theorem `_root_.padicValNat_base_pow` / 定理 `_root_.padicValNat_base_pow`

English:
theorem _root_.padicValNat_base_pow
  given: {p : Nat} (hp : 1 < p) (k : Nat)
  statement: padicValNat p (p ^ k) = k
  proof: by
  simp [padicValNat, hp]

@[simp]

中文:
定理 _root_.padicVal自然数_base_pow
  条件: {p : 自然数} (hp : 1 < p) (k : 自然数)
  结论: padicVal自然数 p (p ^ k) = k
  证明: by
  simp [padicValNat, hp]

@[simp]

Depends on / 依赖: padicValNat
-/
theorem _root_.padicValNat_base_pow {p : Nat} (hp : 1 < p) (k : Nat) : padicValNat p (p ^ k) = k := by
  simp [padicValNat, hp]

@[simp]
/--
theorem `divMaxPow_base_pow` / 定理 `divMaxPow_base_pow`

English:
theorem divMaxPow_base_pow
  given: {p : Nat} (hp : p != 0) (k : Nat)
  statement: (p ^ k).divMaxPow p = 1
  proof: by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]

中文:
定理 divMaxPow_base_pow
  条件: {p : 自然数} (hp : p != 0) (k : 自然数)
  结论: (p ^ k).divMaxPow p = 1
  证明: by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]

Depends on / 依赖: divMaxPow_base_pow_mul
-/
theorem divMaxPow_base_pow {p : Nat} (hp : p != 0) (k : Nat) : (p ^ k).divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]
/--
theorem `maxPowDvdDiv_self` / 定理 `maxPowDvdDiv_self`

English:
theorem maxPowDvdDiv_self
  given: {p : Nat} (hp : 1 < p)
  statement: p.maxPowDvdDiv p = (1, 1)
  proof: by
  simpa using maxPowDvdDiv_base_pow hp 1

@[simp]

中文:
定理 maxPowDvdDiv_self
  条件: {p : 自然数} (hp : 1 < p)
  结论: p.maxPowDvdDiv p = (1, 1)
  证明: by
  simpa using maxPowDvdDiv_base_pow hp 1

@[simp]

Depends on / 依赖: maxPowDvdDiv_base_pow
-/
theorem maxPowDvdDiv_self {p : Nat} (hp : 1 < p) : p.maxPowDvdDiv p = (1, 1) := by
  simpa using maxPowDvdDiv_base_pow hp 1

@[simp]
/--
theorem `_root_.padicValNat_base` / 定理 `_root_.padicValNat_base`

English:
theorem _root_.padicValNat_base
  given: {p : Nat} (hp : 1 < p)
  statement: padicValNat p p = 1
  proof: by
  simpa using padicValNat_base_pow hp 1

@[simp]

中文:
定理 _root_.padicVal自然数_base
  条件: {p : 自然数} (hp : 1 < p)
  结论: padicVal自然数 p p = 1
  证明: by
  simpa using padicValNat_base_pow hp 1

@[simp]

Depends on / 依赖: padicValNat_base_pow
-/
theorem _root_.padicValNat_base {p : Nat} (hp : 1 < p) : padicValNat p p = 1 := by
  simpa using padicValNat_base_pow hp 1

@[simp]
/--
theorem `divMaxPow_self` / 定理 `divMaxPow_self`

English:
theorem divMaxPow_self
  given: {p : Nat} (hp : p != 0)
  statement: p.divMaxPow p = 1
  proof: by
  simpa using divMaxPow_base_pow hp 1

@[simp]

中文:
定理 divMaxPow_self
  条件: {p : 自然数} (hp : p != 0)
  结论: p.divMaxPow p = 1
  证明: by
  simpa using divMaxPow_base_pow hp 1

@[simp]

Depends on / 依赖: divMaxPow_base_pow
-/
theorem divMaxPow_self {p : Nat} (hp : p != 0) : p.divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow hp 1

@[simp]
/--
theorem `fst_maxPowDvdDiv` / 定理 `fst_maxPowDvdDiv`

English:
theorem fst_maxPowDvdDiv
  given: (p n : Nat)
  statement: (p.maxPowDvdDiv n).1 = padicValNat p n
  proof: rfl

@[simp]

中文:
定理 fst_maxPowDvdDiv
  条件: (p n : 自然数)
  结论: (p.maxPowDvdDiv n).1 = padicVal自然数 p n
  证明: rfl

@[simp]
-/
theorem fst_maxPowDvdDiv (p n : Nat) : (p.maxPowDvdDiv n).1 = padicValNat p n := rfl

@[simp]
/--
theorem `snd_maxPowDvdDiv` / 定理 `snd_maxPowDvdDiv`

English:
theorem snd_maxPowDvdDiv
  given: (p n : Nat)
  statement: (p.maxPowDvdDiv n).2 = n.divMaxPow p
  proof: rfl

@[deprecated (since := "2026-03-15")]
alias maxPowDiv := padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_mul_eq_succ := padicValNat_base_mul

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_pow_mul := padicValNat_base_pow_mul

@[deprecated (since := "2026-03-1

中文:
定理 snd_maxPowDvdDiv
  条件: (p n : 自然数)
  结论: (p.maxPowDvdDiv n).2 = n.divMaxPow p
  证明: rfl

@[deprecated (since := "2026-03-15")]
alias maxPowDiv := padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_mul_eq_succ := padicValNat_base_mul

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_pow_mul := padicValNat_base_pow_mul

@[deprecated (since := "2026-03-1
-/
theorem snd_maxPowDvdDiv (p n : Nat) : (p.maxPowDvdDiv n).2 = n.divMaxPow p := rfl

@[deprecated (since := "2026-03-15")]
alias maxPowDiv := padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_mul_eq_succ := padicValNat_base_mul

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_pow_mul := padicValNat_base_pow_mul

@[deprecated (since := "2026-03-15")]
alias ⟨_, maxPowDiv.le_of_dvd⟩ := pow_dvd_iff_le_padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.pow_dvd := pow_padicValNat_dvd

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero := padicValNat_zero_right

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero_base := padicValNat_zero_left

end Nat
