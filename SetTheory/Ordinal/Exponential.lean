/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Ordinal exponential

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `Ordinal.opow_le_iff_le_log : b ^ c ≤ x ↔ c ≤ log b x` for nontrivial inputs
`b`, `c`.
-/

public noncomputable section

open Function Set Equiv Order
open scoped Cardinal Ordinal

universe u v w

namespace Ordinal

/-- The ordinal exponential, defined by transfinite recursion.

We call this `opow` in theorems in order to disambiguate from other exponentials. -/
@[no_expose]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: : Pow Ordinal Ordinal
  body: ⟨fun a b => if a = 0 then 1 - b else
    limitRecOn b 1 (fun _ x => x * a) fun o _ f => ⨆ x : Iio o, f x.1 x.2⟩

中文:
实例 instPow
  签名: : Pow Ordinal Ordinal
  定义体: ⟨fun a b => if a = 0 then 1 - b else
    limitRecOn b 1 (fun _ x => x * a) fun o _ f => ⨆ x : Iio o, f x.1 x.2⟩

Depends on / 依赖: limitRecOn
-/
instance instPow : Pow Ordinal Ordinal :=
  ⟨fun a b => if a = 0 then 1 - b else
    limitRecOn b 1 (fun _ x => x * a) fun o _ f => ⨆ x : Iio o, f x.1 x.2⟩

/--
theorem `opow_of_ne_zero` / 定理 `opow_of_ne_zero`

English:
theorem opow_of_ne_zero
  given: {a b : Ordinal} (h : a != 0)
  statement: a ^ b =
  proof: if_neg h

中文:
定理 opow_of_ne_zero
  条件: {a b : Ordinal} (h : a != 0)
  结论: a ^ b =
  证明: if_neg h
-/
private theorem opow_of_ne_zero {a b : Ordinal} (h : a != 0) : a ^ b =
    limitRecOn b 1 (fun _ x => x * a) fun o _ f => ⨆ x : Iio o, f x.1 x.2 :=
  if_neg h

/--
theorem `zero_opow'` / 定理 `zero_opow'`

English:
theorem zero_opow'
  given: (a : Ordinal)
  statement: 0 ^ a = 1 - a
  proof: if_pos rfl

中文:
定理 zero_opow'
  条件: (a : Ordinal)
  结论: 0 ^ a = 1 - a
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem zero_opow' (a : Ordinal) : 0 ^ a = 1 - a :=
  if_pos rfl

/--
theorem `zero_opow_le` / 定理 `zero_opow_le`

English:
theorem zero_opow_le
  given: (a : Ordinal)
  statement: (0 : Ordinal) ^ a <= 1
  proof: by
  rw [zero_opow']
  exact sub_le_self 1 a

@[simp]

中文:
定理 zero_opow_le
  条件: (a : Ordinal)
  结论: (0 : Ordinal) ^ a <= 1
  证明: by
  rw [zero_opow']
  exact sub_le_self 1 a

@[simp]

Depends on / 依赖: sub_le_self, zero_opow
-/
theorem zero_opow_le (a : Ordinal) : (0 : Ordinal) ^ a <= 1 := by
  rw [zero_opow']
  exact sub_le_self 1 a

@[simp]
/--
theorem `zero_opow` / 定理 `zero_opow`

English:
theorem zero_opow
  given: {a : Ordinal} (a0 : a != 0)
  statement: (0 : Ordinal) ^ a = 0
  proof: by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]

中文:
定理 zero_opow
  条件: {a : Ordinal} (a0 : a != 0)
  结论: (0 : Ordinal) ^ a = 0
  证明: by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]

Depends on / 依赖: Ordinal, Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero, sub_eq_zero_iff_le, zero_opow
-/
theorem zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal) ^ a = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
/--
theorem `opow_zero` / 定理 `opow_zero`

English:
theorem opow_zero
  given: (a : Ordinal)
  statement: a ^ (0 : Ordinal) = 1
  proof: by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow', Ordinal.sub_zero]
  · rw [opow_of_ne_zero h, limitRecOn_zero]

@[simp]

中文:
定理 opow_zero
  条件: (a : Ordinal)
  结论: a ^ (0 : Ordinal) = 1
  证明: by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow', Ordinal.sub_zero]
  · rw [opow_of_ne_zero h, limitRecOn_zero]

@[simp]

Depends on / 依赖: Ordinal, Ordinal.sub_zero, eq_or_ne, limitRecOn_zero, opow_of_ne_zero, sub_zero, zero_opow
-/
theorem opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1 := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow', Ordinal.sub_zero]
  · rw [opow_of_ne_zero h, limitRecOn_zero]

@[simp]
/--
theorem `opow_add_one` / 定理 `opow_add_one`

English:
theorem opow_add_one
  given: (a b : Ordinal)
  statement: a ^ (b + 1) = a ^ b * a
  proof: by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow (add_pos_of_right zero_lt_one b).ne', mul_zero]
  · rw [opow_of_ne_zero h, opow_of_ne_zero h]
    exact limitRecOn_add_one ..

中文:
定理 opow_add_one
  条件: (a b : Ordinal)
  结论: a ^ (b + 1) = a ^ b * a
  证明: by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow (add_pos_of_right zero_lt_one b).ne', mul_zero]
  · rw [opow_of_ne_zero h, opow_of_ne_zero h]
    exact limitRecOn_add_one ..

Depends on / 依赖: add_pos_of_right, eq_or_ne, limitRecOn_add_one, mul_zero, opow_of_ne_zero, zero_lt_one, zero_opow
-/
theorem opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b * a := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow (add_pos_of_right zero_lt_one b).ne', mul_zero]
  · rw [opow_of_ne_zero h, opow_of_ne_zero h]
    exact limitRecOn_add_one ..

-- TODO: deprecate
/--
theorem `opow_succ` / 定理 `opow_succ`

English:
theorem opow_succ
  given: (a b : Ordinal)
  statement: a ^ succ b = a ^ b * a
  proof: opow_add_one a b

中文:
定理 opow_succ
  条件: (a b : Ordinal)
  结论: a ^ succ b = a ^ b * a
  证明: opow_add_one a b

Depends on / 依赖: opow_add_one
-/
theorem opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a :=
  opow_add_one a b

/--
theorem `opow_limit` / 定理 `opow_limit`

English:
theorem opow_limit
  given: {a b : Ordinal} (ha : a != 0) (hb : IsSuccLimit b)
  proof: by
  simp_rw [opow_of_ne_zero ha, limitRecOn_limit _ _ _ _ hb]

中文:
定理 opow_limit
  条件: {a b : Ordinal} (ha : a != 0) (hb : IsSuccLimit b)
  证明: by
  simp_rw [opow_of_ne_zero ha, limitRecOn_limit _ _ _ _ hb]

Depends on / 依赖: limitRecOn_limit, opow_of_ne_zero, simp_rw
-/
theorem opow_limit {a b : Ordinal} (ha : a != 0) (hb : IsSuccLimit b) :
    a ^ b = ⨆ x : Iio b, a ^ x.1 := by
  simp_rw [opow_of_ne_zero ha, limitRecOn_limit _ _ _ _ hb]

/--
theorem `opow_le_of_isSuccLimit` / 定理 `opow_le_of_isSuccLimit`

English:
theorem opow_le_of_isSuccLimit
  given: {a b c : Ordinal} (a0 : a != 0) (h : IsSuccLimit b)
  proof: by
  rw [opow_limit a0 h]; rw [Ordinal.iSup_le_iff]; rw [Subtype.forall]
  rfl

中文:
定理 opow_le_of_isSuccLimit
  条件: {a b c : Ordinal} (a0 : a != 0) (h : IsSuccLimit b)
  证明: by
  rw [opow_limit a0 h]; rw [Ordinal.iSup_le_iff]; rw [Subtype.forall]
  rfl

Depends on / 依赖: Ordinal, Ordinal.iSup_le_iff, Subtype, Subtype.forall, iSup_le_iff, opow_limit
-/
theorem opow_le_of_isSuccLimit {a b c : Ordinal} (a0 : a != 0) (h : IsSuccLimit b) :
    a ^ b <= c ↔ forall b' < b, a ^ b' <= c := by
  rw [opow_limit a0 h]; rw [Ordinal.iSup_le_iff]; rw [Subtype.forall]
  rfl

/--
theorem `lt_opow_of_isSuccLimit` / 定理 `lt_opow_of_isSuccLimit`

English:
theorem lt_opow_of_isSuccLimit
  given: {a b c : Ordinal} (b0 : b != 0) (h : IsSuccLimit c)
  proof: by
  simpa using (opow_le_of_isSuccLimit b0 h).not

@[simp]

中文:
定理 lt_opow_of_isSuccLimit
  条件: {a b c : Ordinal} (b0 : b != 0) (h : IsSuccLimit c)
  证明: by
  simpa using (opow_le_of_isSuccLimit b0 h).not

@[simp]

Depends on / 依赖: opow_le_of_isSuccLimit
-/
theorem lt_opow_of_isSuccLimit {a b c : Ordinal} (b0 : b != 0) (h : IsSuccLimit c) :
    a < b ^ c ↔ exists c' < c, a < b ^ c' := by
  simpa using (opow_le_of_isSuccLimit b0 h).not

@[simp]
/--
theorem `opow_one` / 定理 `opow_one`

English:
theorem opow_one
  given: (a : Ordinal)
  statement: a ^ (1 : Ordinal) = a
  proof: by
  simpa using opow_add_one a 0

@[simp]

中文:
定理 opow_one
  条件: (a : Ordinal)
  结论: a ^ (1 : Ordinal) = a
  证明: by
  simpa using opow_add_one a 0

@[simp]

Depends on / 依赖: opow_add_one
-/
theorem opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a := by
  simpa using opow_add_one a 0

@[simp]
/--
theorem `one_opow` / 定理 `one_opow`

English:
theorem one_opow
  given: (a : Ordinal)
  statement: (1 : Ordinal) ^ a = 1
  proof: by
  induction a using limitRecOn with
  | zero => simp
  | add_one _ IH => simp [IH, mul_one]
  | limit b l IH =>
    refine eq_of_forall_ge_iff fun c => ?_
    rw [opow_le_of_isSuccLimit one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.bot_lt, fun H b' h => by rwa [IH _ h]⟩

中文:
定理 one_opow
  条件: (a : Ordinal)
  结论: (1 : Ordinal) ^ a = 1
  证明: by
  induction a using limitRecOn with
  | zero => simp
  | add_one _ IH => simp [IH, mul_one]
  | limit b l IH =>
    refine eq_of_forall_ge_iff fun c => ?_
    rw [opow_le_of_isSuccLimit one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.bot_lt, fun H b' h => by rwa [IH _ h]⟩

Depends on / 依赖: add_one, bot_lt, eq_of_forall_ge_iff, l.bot_lt, limitRecOn, mul_one, one_ne_zero, opow_le_of_isSuccLimit, opow_zero
-/
theorem one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1 := by
  induction a using limitRecOn with
  | zero => simp
  | add_one _ IH => simp [IH, mul_one]
  | limit b l IH =>
    refine eq_of_forall_ge_iff fun c => ?_
    rw [opow_le_of_isSuccLimit one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.bot_lt, fun H b' h => by rwa [IH _ h]⟩

/--
theorem `opow_pos` / 定理 `opow_pos`

English:
theorem opow_pos
  given: {a : Ordinal} (b : Ordinal) (a0 : 0 < a)
  statement: 0 < a ^ b
  proof: by
  have h0 : 0 < a ^ (0 : Ordinal) := by simp
  induction b using limitRecOn with
  | zero => exact h0
  | add_one b IH => simpa using mul_pos IH a0
  | limit b l _ => exact (lt_opow_of_isSuccLimit (pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩

中文:
定理 opow_pos
  条件: {a : Ordinal} (b : Ordinal) (a0 : 0 < a)
  结论: 0 < a ^ b
  证明: by
  have h0 : 0 < a ^ (0 : Ordinal) := by simp
  induction b using limitRecOn with
  | zero => exact h0
  | add_one b IH => simpa using mul_pos IH a0
  | limit b l _ => exact (lt_opow_of_isSuccLimit (pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩

Depends on / 依赖: Ordinal, add_one, l.pos, limitRecOn, lt_opow_of_isSuccLimit, mul_pos, pos_iff_ne_zero
-/
theorem opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 < a ^ b := by
  have h0 : 0 < a ^ (0 : Ordinal) := by simp
  induction b using limitRecOn with
  | zero => exact h0
  | add_one b IH => simpa using mul_pos IH a0
  | limit b l _ => exact (lt_opow_of_isSuccLimit (pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩

/--
theorem `opow_ne_zero` / 定理 `opow_ne_zero`

English:
theorem opow_ne_zero
  given: {a : Ordinal} (b : Ordinal) (a0 : a != 0)
  statement: a ^ b != 0
  proof: pos_iff_ne_zero.1 opow_pos b pos_iff_ne_zero.2 a0

@[simp]

中文:
定理 opow_ne_zero
  条件: {a : Ordinal} (b : Ordinal) (a0 : a != 0)
  结论: a ^ b != 0
  证明: pos_iff_ne_zero.1 opow_pos b pos_iff_ne_zero.2 a0

@[simp]

Depends on / 依赖: opow_pos, pos_iff_ne_zero
-/
theorem opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a != 0) : a ^ b != 0 :=
pos_iff_ne_zero.1 opow_pos b pos_iff_ne_zero.2 a0

@[simp]
/--
theorem `opow_eq_zero` / 定理 `opow_eq_zero`

English:
theorem opow_eq_zero
  given: {a b : Ordinal}
  statement: a ^ b = 0 ↔ a = 0 ∧ b != 0
  proof: by
  by_cases a = 0 <;> by_cases b = 0 <;> simp_all [opow_ne_zero]

@[simp, norm_cast]

中文:
定理 opow_eq_zero
  条件: {a b : Ordinal}
  结论: a ^ b = 0 ↔ a = 0 ∧ b != 0
  证明: by
  by_cases a = 0 <;> by_cases b = 0 <;> simp_all [opow_ne_zero]

@[simp, norm_cast]

Depends on / 依赖: opow_ne_zero
-/
theorem opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧ b != 0 := by
  by_cases a = 0 <;> by_cases b = 0 <;> simp_all [opow_ne_zero]

@[simp, norm_cast]
/--
theorem `opow_natCast` / 定理 `opow_natCast`

English:
theorem opow_natCast
  given: (a : Ordinal) (n : Nat)
  statement: a ^ (n : Ordinal) = a ^ n
  proof: by
  induction n with
  | zero => rw [Nat.cast_zero, opow_zero, pow_zero]
  | succ n IH => rw [Nat.cast_succ, ← succ_eq_add_one, opow_succ, pow_succ, IH]

中文:
定理 opow_natCast
  条件: (a : Ordinal) (n : 自然数)
  结论: a ^ (n : Ordinal) = a ^ n
  证明: by
  induction n with
  | zero => rw [Nat.cast_zero, opow_zero, pow_zero]
  | succ n IH => rw [Nat.cast_succ, ← succ_eq_add_one, opow_succ, pow_succ, IH]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, cast_succ, cast_zero, opow_succ, opow_zero, pow_succ, pow_zero, succ_eq_add_one
-/
theorem opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Ordinal) = a ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, opow_zero, pow_zero]
  | succ n IH => rw [Nat.cast_succ, ← succ_eq_add_one, opow_succ, pow_succ, IH]

/--
theorem `isNormal_opow` / 定理 `isNormal_opow`

English:
theorem isNormal_opow
  given: {a : Ordinal} (h : 1 < a)
  statement: IsNormal (a ^ · : Ordinal -> Ordinal)
  proof: by
  have ha : 0 < a := zero_lt_one.trans h
  refine IsNormal.of_succ_lt ?_ fun hl => ?_
  · simpa only [mul_one, opow_succ] using fun b => mul_lt_mul_of_pos_left h (opow_pos b ha)
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, ← opow_le_of_isSuccLimit ha.ne' hl]

@[simp]

中文:
定理 isNormal_opow
  条件: {a : Ordinal} (h : 1 < a)
  结论: IsNormal (a ^ · : Ordinal -> Ordinal)
  证明: by
  have ha : 0 < a := zero_lt_one.trans h
  refine IsNormal.of_succ_lt ?_ fun hl => ?_
  · simpa only [mul_one, opow_succ] using fun b => mul_lt_mul_of_pos_left h (opow_pos b ha)
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, ← opow_le_of_isSuccLimit ha.ne' hl]

@[simp]

Depends on / 依赖: IsLeast, IsNormal, IsNormal.of_succ_lt, ha.ne, lowerBounds, mul_lt_mul_of_pos_left, mul_one, of_succ_lt, opow_le_of_isSuccLimit, opow_pos, opow_succ, upperBounds, zero_lt_one, zero_lt_one.trans
-/
theorem isNormal_opow {a : Ordinal} (h : 1 < a) : IsNormal (a ^ · : Ordinal -> Ordinal) := by
  have ha : 0 < a := zero_lt_one.trans h
  refine IsNormal.of_succ_lt ?_ fun hl => ?_
  · simpa only [mul_one, opow_succ] using fun b => mul_lt_mul_of_pos_left h (opow_pos b ha)
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, ← opow_le_of_isSuccLimit ha.ne' hl]

@[simp]
/--
theorem `opow_lt_opow_iff_right` / 定理 `opow_lt_opow_iff_right`

English:
theorem opow_lt_opow_iff_right
  given: {a b c : Ordinal} (a1 : 1 < a)
  statement: a ^ b < a ^ c ↔ b < c
  proof: (isNormal_opow a1).strictMono.lt_iff_lt

@[simp]

中文:
定理 opow_lt_opow_iff_right
  条件: {a b c : Ordinal} (a1 : 1 < a)
  结论: a ^ b < a ^ c ↔ b < c
  证明: (isNormal_opow a1).strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: isNormal_opow, lt_iff_lt, strictMono, strictMono.lt_iff_lt
-/
theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
  (isNormal_opow a1).strictMono.lt_iff_lt

@[simp]
/--
theorem `opow_le_opow_iff_right` / 定理 `opow_le_opow_iff_right`

English:
theorem opow_le_opow_iff_right
  given: {a b c : Ordinal} (a1 : 1 < a)
  statement: a ^ b <= a ^ c ↔ b <= c
  proof: (isNormal_opow a1).strictMono.le_iff_le

@[simp]

中文:
定理 opow_le_opow_iff_right
  条件: {a b c : Ordinal} (a1 : 1 < a)
  结论: a ^ b <= a ^ c ↔ b <= c
  证明: (isNormal_opow a1).strictMono.le_iff_le

@[simp]

Depends on / 依赖: isNormal_opow, le_iff_le, strictMono, strictMono.le_iff_le
-/
theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b <= a ^ c ↔ b <= c :=
  (isNormal_opow a1).strictMono.le_iff_le

@[simp]
/--
theorem `opow_right_inj` / 定理 `opow_right_inj`

English:
theorem opow_right_inj
  given: {a b c : Ordinal} (a1 : 1 < a)
  statement: a ^ b = a ^ c ↔ b = c
  proof: (isNormal_opow a1).strictMono.injective.eq_iff

@[simp]

中文:
定理 opow_right_inj
  条件: {a b c : Ordinal} (a1 : 1 < a)
  结论: a ^ b = a ^ c ↔ b = c
  证明: (isNormal_opow a1).strictMono.injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, injective, isNormal_opow, strictMono, strictMono.injective.eq_iff
-/
theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
  (isNormal_opow a1).strictMono.injective.eq_iff

@[simp]
/--
theorem `one_lt_opow` / 定理 `one_lt_opow`

English:
theorem one_lt_opow
  given: {a b : Ordinal}
  statement: 1 < a ^ b ↔ 1 < a ∧ b != 0
  proof: by
  refine ⟨?_, fun ⟨ha, hb⟩ => ?_⟩
  · contrapose! +distrib
    rw [le_one_iff]
    rintro ((rfl | rfl) | rfl)
    · exact zero_opow_le b
    · simp
    · simp
  · rwa [← opow_zero a, opow_lt_opow_iff_right ha, pos_iff_ne_zero]

@[simp]

中文:
定理 one_lt_opow
  条件: {a b : Ordinal}
  结论: 1 < a ^ b ↔ 1 < a ∧ b != 0
  证明: by
  refine ⟨?_, fun ⟨ha, hb⟩ => ?_⟩
  · contrapose! +distrib
    rw [le_one_iff]
    rintro ((rfl | rfl) | rfl)
    · exact zero_opow_le b
    · simp
    · simp
  · rwa [← opow_zero a, opow_lt_opow_iff_right ha, pos_iff_ne_zero]

@[simp]

Depends on / 依赖: contrapose, distrib, le_one_iff, opow_lt_opow_iff_right, opow_zero, pos_iff_ne_zero, zero_opow_le
-/
theorem one_lt_opow {a b : Ordinal} : 1 < a ^ b ↔ 1 < a ∧ b != 0 := by
  refine ⟨?_, fun ⟨ha, hb⟩ => ?_⟩
  · contrapose! +distrib
    rw [le_one_iff]
    rintro ((rfl | rfl) | rfl)
    · exact zero_opow_le b
    · simp
    · simp
  · rwa [← opow_zero a, opow_lt_opow_iff_right ha, pos_iff_ne_zero]

@[simp]
/--
theorem `one_lt_pow` / 定理 `one_lt_pow`

English:
theorem one_lt_pow
  given: {a : Ordinal} {n : Nat}
  statement: 1 < a ^ n ↔ 1 < a ∧ n != 0
  proof: mod_cast one_lt_opow (b := n)

@[simp]

中文:
定理 one_lt_pow
  条件: {a : Ordinal} {n : 自然数}
  结论: 1 < a ^ n ↔ 1 < a ∧ n != 0
  证明: mod_cast one_lt_opow (b := n)

@[simp]

Depends on / 依赖: mod_cast, one_lt_opow
-/
theorem one_lt_pow {a : Ordinal} {n : Nat} : 1 < a ^ n ↔ 1 < a ∧ n != 0 :=
  mod_cast one_lt_opow (b := n)

@[simp]
/--
theorem `opow_eq_one_iff` / 定理 `opow_eq_one_iff`

English:
theorem opow_eq_one_iff
  given: {a b : Ordinal}
  statement: a ^ b = 1 ↔ a = 1 ∨ b = 0
  proof: by
  refine ⟨fun h => ?_, by simp +contextual [or_imp]⟩
  contrapose! h
  obtain ha | ha := le_or_gt a 1
  · simp_all [le_one_iff]
  · simpa using ((opow_lt_opow_iff_right ha).2 h.2.pos).ne'

@[simp]

中文:
定理 opow_eq_one_iff
  条件: {a b : Ordinal}
  结论: a ^ b = 1 ↔ a = 1 ∨ b = 0
  证明: by
  refine ⟨fun h => ?_, by simp +contextual [or_imp]⟩
  contrapose! h
  obtain ha | ha := le_or_gt a 1
  · simp_all [le_one_iff]
  · simpa using ((opow_lt_opow_iff_right ha).2 h.2.pos).ne'

@[simp]

Depends on / 依赖: contextual, contrapose, le_one_iff, le_or_gt, opow_lt_opow_iff_right, or_imp
-/
theorem opow_eq_one_iff {a b : Ordinal} : a ^ b = 1 ↔ a = 1 ∨ b = 0 := by
  refine ⟨fun h => ?_, by simp +contextual [or_imp]⟩
  contrapose! h
  obtain ha | ha := le_or_gt a 1
  · simp_all [le_one_iff]
  · simpa using ((opow_lt_opow_iff_right ha).2 h.2.pos).ne'

@[simp]
/--
theorem `pow_eq_one_iff` / 定理 `pow_eq_one_iff`

English:
theorem pow_eq_one_iff
  given: {a : Ordinal} {n : Nat}
  statement: a ^ n = 1 ↔ a = 1 ∨ n = 0
  proof: mod_cast opow_eq_one_iff (b := n)

中文:
定理 pow_eq_one_iff
  条件: {a : Ordinal} {n : 自然数}
  结论: a ^ n = 1 ↔ a = 1 ∨ n = 0
  证明: mod_cast opow_eq_one_iff (b := n)

Depends on / 依赖: mod_cast, opow_eq_one_iff
-/
theorem pow_eq_one_iff {a : Ordinal} {n : Nat} : a ^ n = 1 ↔ a = 1 ∨ n = 0 :=
  mod_cast opow_eq_one_iff (b := n)

/--
theorem `isSuccLimit_opow` / 定理 `isSuccLimit_opow`

English:
theorem isSuccLimit_opow
  given: {a b : Ordinal} (a1 : 1 < a)
  statement: IsSuccLimit b -> IsSuccLimit (a ^ b)
  proof: (isNormal_opow a1).map_isSuccLimit

中文:
定理 isSuccLimit_opow
  条件: {a b : Ordinal} (a1 : 1 < a)
  结论: IsSuccLimit b -> IsSuccLimit (a ^ b)
  证明: (isNormal_opow a1).map_isSuccLimit

Depends on / 依赖: isNormal_opow, map_isSuccLimit
-/
theorem isSuccLimit_opow {a b : Ordinal} (a1 : 1 < a) : IsSuccLimit b -> IsSuccLimit (a ^ b) :=
  (isNormal_opow a1).map_isSuccLimit

/--
theorem `isSuccLimit_opow_left` / 定理 `isSuccLimit_opow_left`

English:
theorem isSuccLimit_opow_left
  given: {a b : Ordinal} (l : IsSuccLimit a) (hb : b != 0)
  proof: by
  rcases zero_or_succ_or_isSuccLimit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
  · rw [opow_succ]
    exact isSuccLimit_mul_right (opow_pos _ l.bot_lt) l
  · exact isSuccLimit_opow (one_lt_of_isSuccLimit l) l'

中文:
定理 isSuccLimit_opow_left
  条件: {a b : Ordinal} (l : IsSuccLimit a) (hb : b != 0)
  证明: by
  rcases zero_or_succ_or_isSuccLimit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
  · rw [opow_succ]
    exact isSuccLimit_mul_right (opow_pos _ l.bot_lt) l
  · exact isSuccLimit_opow (one_lt_of_isSuccLimit l) l'

Depends on / 依赖: absurd, bot_lt, isSuccLimit_mul_right, isSuccLimit_opow, l.bot_lt, one_lt_of_isSuccLimit, opow_pos, opow_succ, zero_or_succ_or_isSuccLimit
-/
theorem isSuccLimit_opow_left {a b : Ordinal} (l : IsSuccLimit a) (hb : b != 0) :
    IsSuccLimit (a ^ b) := by
  rcases zero_or_succ_or_isSuccLimit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
  · rw [opow_succ]
    exact isSuccLimit_mul_right (opow_pos _ l.bot_lt) l
  · exact isSuccLimit_opow (one_lt_of_isSuccLimit l) l'

/--
theorem `opow_le_opow_right` / 定理 `opow_le_opow_right`

English:
theorem opow_le_opow_right
  given: {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b <= c)
  statement: a ^ b <= a ^ c
  proof: by
  rcases (one_le_iff_pos.2 h₁).eq_or_lt' with h₁ | h₁
  · simp_all
  · exact (opow_le_opow_iff_right h₁).2 h₂

@[gcongr]

中文:
定理 opow_le_opow_right
  条件: {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b <= c)
  结论: a ^ b <= a ^ c
  证明: by
  rcases (one_le_iff_pos.2 h₁).eq_or_lt' with h₁ | h₁
  · simp_all
  · exact (opow_le_opow_iff_right h₁).2 h₂

@[gcongr]

Depends on / 依赖: eq_or_lt, one_le_iff_pos, opow_le_opow_iff_right
-/
theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b <= c) : a ^ b <= a ^ c := by
  rcases (one_le_iff_pos.2 h₁).eq_or_lt' with h₁ | h₁
  · simp_all
  · exact (opow_le_opow_iff_right h₁).2 h₂

@[gcongr]
/--
theorem `opow_le_opow_left` / 定理 `opow_le_opow_left`

English:
theorem opow_le_opow_left
  given: {a b : Ordinal} (c : Ordinal) (ab : a <= b)
  statement: a ^ c <= b ^ c
  proof: by
  by_cases ha : a = 0
  · by_cases c = 0 <;> simp_all
  · induction c using limitRecOn with
    | zero => simp
    | add_one c IH => simpa using mul_le_mul' IH ab
    | limit c l IH =>
      exact (opow_le_of_isSuccLimit ha l).2 fun b' h =>
        (IH _ h).trans (opow_le_opow_right ((pos_iff_ne_

中文:
定理 opow_le_opow_left
  条件: {a b : Ordinal} (c : Ordinal) (ab : a <= b)
  结论: a ^ c <= b ^ c
  证明: by
  by_cases ha : a = 0
  · by_cases c = 0 <;> simp_all
  · induction c using limitRecOn with
    | zero => simp
    | add_one c IH => simpa using mul_le_mul' IH ab
    | limit c l IH =>
      exact (opow_le_of_isSuccLimit ha l).2 fun b' h =>
        (IH _ h).trans (opow_le_opow_right ((pos_iff_ne_

Depends on / 依赖: add_one, h.le, limitRecOn, mul_le_mul, opow_le_of_isSuccLimit, opow_le_opow_right, pos_iff_ne_zero, trans_le
-/
theorem opow_le_opow_left {a b : Ordinal} (c : Ordinal) (ab : a <= b) : a ^ c <= b ^ c := by
  by_cases ha : a = 0
  · by_cases c = 0 <;> simp_all
  · induction c using limitRecOn with
    | zero => simp
    | add_one c IH => simpa using mul_le_mul' IH ab
    | limit c l IH =>
      exact (opow_le_of_isSuccLimit ha l).2 fun b' h =>
        (IH _ h).trans (opow_le_opow_right ((pos_iff_ne_zero.2 ha).trans_le ab) h.le)

@[gcongr]
/--
theorem `opow_le_opow` / 定理 `opow_le_opow`

English:
theorem opow_le_opow
  given: {a b c d : Ordinal} (hac : a <= c) (hbd : b <= d) (hc : 0 < c)
  statement: a ^ b <= c ^ d
  proof: (opow_le_opow_left b hac).trans (opow_le_opow_right hc hbd)

中文:
定理 opow_le_opow
  条件: {a b c d : Ordinal} (hac : a <= c) (hbd : b <= d) (hc : 0 < c)
  结论: a ^ b <= c ^ d
  证明: (opow_le_opow_left b hac).trans (opow_le_opow_right hc hbd)

Depends on / 依赖: opow_le_opow_left, opow_le_opow_right
-/
theorem opow_le_opow {a b c d : Ordinal} (hac : a <= c) (hbd : b <= d) (hc : 0 < c) : a ^ b <= c ^ d :=
  (opow_le_opow_left b hac).trans (opow_le_opow_right hc hbd)

/--
theorem `left_le_opow` / 定理 `left_le_opow`

English:
theorem left_le_opow
  given: (a : Ordinal) {b : Ordinal} (b1 : 0 < b)
  statement: a <= a ^ b
  proof: by
  nth_rw 1 [← opow_one a]
  rcases le_or_gt a 1 with a1 | a1
  · rcases lt_or_eq_of_le a1 with a0 | a1
    · rw [lt_one_iff] at a0
      rw [a0]; rw [zero_opow one_ne_zero]
      exact zero_le
    rw [a1]; rw [one_opow]; rw [one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]

中文:
定理 left_le_opow
  条件: (a : Ordinal) {b : Ordinal} (b1 : 0 < b)
  结论: a <= a ^ b
  证明: by
  nth_rw 1 [← opow_one a]
  rcases le_or_gt a 1 with a1 | a1
  · rcases lt_or_eq_of_le a1 with a0 | a1
    · rw [lt_one_iff] at a0
      rw [a0]; rw [zero_opow one_ne_zero]
      exact zero_le
    rw [a1]; rw [one_opow]; rw [one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]

Depends on / 依赖: le_or_gt, lt_one_iff, lt_or_eq_of_le, nth_rw, one_le_iff_pos, one_ne_zero, one_opow, opow_le_opow_iff_right, opow_one, zero_le, zero_opow
-/
theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a <= a ^ b := by
  nth_rw 1 [← opow_one a]
  rcases le_or_gt a 1 with a1 | a1
  · rcases lt_or_eq_of_le a1 with a0 | a1
    · rw [lt_one_iff] at a0
      rw [a0]; rw [zero_opow one_ne_zero]
      exact zero_le
    rw [a1]; rw [one_opow]; rw [one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]

/--
theorem `left_lt_opow` / 定理 `left_lt_opow`

English:
theorem left_lt_opow
  given: {a b : Ordinal} (ha : 1 < a) (hb : 1 < b)
  statement: a < a ^ b
  proof: by
  conv_lhs => rw [← opow_one a]
  rwa [opow_lt_opow_iff_right ha]

中文:
定理 left_lt_opow
  条件: {a b : Ordinal} (ha : 1 < a) (hb : 1 < b)
  结论: a < a ^ b
  证明: by
  conv_lhs => rw [← opow_one a]
  rwa [opow_lt_opow_iff_right ha]

Depends on / 依赖: conv_lhs, opow_lt_opow_iff_right, opow_one
-/
theorem left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 < b) : a < a ^ b := by
  conv_lhs => rw [← opow_one a]
  rwa [opow_lt_opow_iff_right ha]

/--
theorem `right_le_opow` / 定理 `right_le_opow`

English:
theorem right_le_opow
  given: {a : Ordinal} (b : Ordinal) (a1 : 1 < a)
  statement: b <= a ^ b
  proof: (isNormal_opow a1).strictMono.le_apply

中文:
定理 right_le_opow
  条件: {a : Ordinal} (b : Ordinal) (a1 : 1 < a)
  结论: b <= a ^ b
  证明: (isNormal_opow a1).strictMono.le_apply

Depends on / 依赖: isNormal_opow, le_apply, strictMono, strictMono.le_apply
-/
theorem right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1 < a) : b <= a ^ b :=
  (isNormal_opow a1).strictMono.le_apply

/--
theorem `opow_lt_opow_left_of_succ` / 定理 `opow_lt_opow_left_of_succ`

English:
theorem opow_lt_opow_left_of_succ
  given: {a b c : Ordinal} (ab : a < b)
  statement: a ^ succ c < b ^ succ c
  proof: by
  rw [opow_succ]; rw [opow_succ]
  exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (by gcongr) ab zero_le (opow_pos _ ab.bot_lt)

中文:
定理 opow_lt_opow_left_of_succ
  条件: {a b c : Ordinal} (ab : a < b)
  结论: a ^ succ c < b ^ succ c
  证明: by
  rw [opow_succ]; rw [opow_succ]
  exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (by gcongr) ab zero_le (opow_pos _ ab.bot_lt)

Depends on / 依赖: ab.bot_lt, bot_lt, mul_lt_mul_of_le_of_lt_of_nonneg_of_pos, opow_pos, opow_succ, zero_le
-/
theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : a ^ succ c < b ^ succ c := by
  rw [opow_succ]; rw [opow_succ]
  exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (by gcongr) ab zero_le (opow_pos _ ab.bot_lt)

/--
theorem `opow_add` / 定理 `opow_add`

English:
theorem opow_add
  given: (a b c : Ordinal)
  statement: a ^ (b + c) = a ^ b * a ^ c
  proof: by
  obtain rfl | ha := eq_zero_or_pos a
  · obtain rfl | hc := eq_zero_or_pos c; · simp
    have : b + c != 0 := (hc.trans_le le_add_self).ne'
    rw [zero_opow hc.ne']; rw [zero_opow]; rw [mul_zero]
    exact (hc.trans_le le_add_self).ne'
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha.ne').eq_or_l

中文:
定理 opow_add
  条件: (a b c : Ordinal)
  结论: a ^ (b + c) = a ^ b * a ^ c
  证明: by
  obtain rfl | ha := eq_zero_or_pos a
  · obtain rfl | hc := eq_zero_or_pos c; · simp
    have : b + c != 0 := (hc.trans_le le_add_self).ne'
    rw [zero_opow hc.ne']; rw [zero_opow]; rw [mul_zero]
    exact (hc.trans_le le_add_self).ne'
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha.ne').eq_or_l

Depends on / 依赖: add_assoc, add_one, eq_of_forall_ge_iff, eq_or_lt, eq_zero_or_pos, ha.ne, hc.ne, hc.trans_le, isNormal_opow, le_add_self, limitRecOn, mul_assoc, mul_zero, one_le_iff_ne_zero, opow_add_one, trans_le, zero_opow
-/
theorem opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^ c := by
  obtain rfl | ha := eq_zero_or_pos a
  · obtain rfl | hc := eq_zero_or_pos c; · simp
    have : b + c != 0 := (hc.trans_le le_add_self).ne'
    rw [zero_opow hc.ne']; rw [zero_opow]; rw [mul_zero]
    exact (hc.trans_le le_add_self).ne'
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha.ne').eq_or_lt; · simp
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [← add_assoc, opow_add_one, IH, opow_add_one, mul_assoc]
  | limit c l IH =>
    refine eq_of_forall_ge_iff fun d =>
      (((isNormal_opow ha').comp (isNormal_add_right b)).le_iff_forall_le l).trans ?_
    simpa +contextual [IH] using
      (((isNormal_mul_right <| opow_pos b (pos_iff_ne_zero.2 ha.ne')).comp
        (isNormal_opow ha')).le_iff_forall_le l).symm

/--
theorem `opow_one_add` / 定理 `opow_one_add`

English:
theorem opow_one_add
  given: (a b : Ordinal)
  statement: a ^ (1 + b) = a * a ^ b
  proof: by rw [opow_add, opow_one]

中文:
定理 opow_one_add
  条件: (a b : Ordinal)
  结论: a ^ (1 + b) = a * a ^ b
  证明: by rw [opow_add, opow_one]

Depends on / 依赖: opow_add, opow_one
-/
theorem opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a ^ b := by rw [opow_add, opow_one]

/--
theorem `opow_dvd_opow` / 定理 `opow_dvd_opow`

English:
theorem opow_dvd_opow
  given: (a : Ordinal) {b c : Ordinal} (h : b <= c)
  statement: a ^ b ∣ a ^ c
  proof: ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩

中文:
定理 opow_dvd_opow
  条件: (a : Ordinal) {b c : Ordinal} (h : b <= c)
  结论: a ^ b ∣ a ^ c
  证明: ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, opow_add
-/
theorem opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : b <= c) : a ^ b ∣ a ^ c :=
  ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩

/--
theorem `opow_dvd_opow_iff` / 定理 `opow_dvd_opow_iff`

English:
theorem opow_dvd_opow_iff
  given: {a b c : Ordinal} (a1 : 1 < a)
  statement: a ^ b ∣ a ^ c ↔ b <= c
  proof: ⟨fun h =>
    le_of_not_gt fun hn =>
not_le_of_gt ((opow_lt_opow_iff_right a1).2 hn)
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩

中文:
定理 opow_dvd_opow_iff
  条件: {a b c : Ordinal} (a1 : 1 < a)
  结论: a ^ b ∣ a ^ c ↔ b <= c
  证明: ⟨fun h =>
    le_of_not_gt fun hn =>
not_le_of_gt ((opow_lt_opow_iff_right a1).2 hn)
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩

Depends on / 依赖: a1.le, le_of_dvd, le_of_not_gt, not_le_of_gt, one_le_iff_ne_zero, opow_dvd_opow, opow_lt_opow_iff_right, opow_ne_zero
-/
theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b <= c :=
  ⟨fun h =>
    le_of_not_gt fun hn =>
not_le_of_gt ((opow_lt_opow_iff_right a1).2 hn)
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩

/--
theorem `opow_mul` / 定理 `opow_mul`

English:
theorem opow_mul
  given: (a b c : Ordinal)
  statement: a ^ (b * c) = (a ^ b) ^ c
  proof: by
  obtain rfl | hb := eq_zero_or_pos b; · simp
  obtain rfl | ha := eq_or_ne a 0
  · have := hb.ne'
    by_cases c = 0 <;> simp_all
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha).eq_or_lt; · simp
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, opow_add, I

中文:
定理 opow_mul
  条件: (a b c : Ordinal)
  结论: a ^ (b * c) = (a ^ b) ^ c
  证明: by
  obtain rfl | hb := eq_zero_or_pos b; · simp
  obtain rfl | ha := eq_or_ne a 0
  · have := hb.ne'
    by_cases c = 0 <;> simp_all
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha).eq_or_lt; · simp
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, opow_add, I

Depends on / 依赖: add_one, contextual, eq_of_forall_ge_iff, eq_or_lt, eq_or_ne, eq_zero_or_pos, hb.ne, isNormal_mul_right, isNormal_opow, le_iff_forall_le, limitRecOn, mul_add_one, one_le_iff_ne_zero, opow_add, opow_add_one, opow_le_of_isSuccLimit, opow_ne_zero
-/
theorem opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c := by
  obtain rfl | hb := eq_zero_or_pos b; · simp
  obtain rfl | ha := eq_or_ne a 0
  · have := hb.ne'
    by_cases c = 0 <;> simp_all
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha).eq_or_lt; · simp
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, opow_add, IH, opow_add_one]
  | limit c l IH =>
    refine eq_of_forall_ge_iff fun d =>
      (((isNormal_opow ha').comp (isNormal_mul_right hb)).le_iff_forall_le l).trans ?_
    simpa +contextual [IH] using (opow_le_of_isSuccLimit (opow_ne_zero _ ha) l).symm

/--
theorem `opow_mul_add_pos` / 定理 `opow_mul_add_pos`

English:
theorem opow_mul_add_pos
  given: {b v : Ordinal} (hb : b != 0) (u : Ordinal) (hv : v != 0) (w : Ordinal)
  proof: (opow_pos u <| pos_iff_ne_zero.2 hb).trans_le
    (le_mul_left _ <| pos_iff_ne_zero.2 hv).trans le_self_add

中文:
定理 opow_mul_add_pos
  条件: {b v : Ordinal} (hb : b != 0) (u : Ordinal) (hv : v != 0) (w : Ordinal)
  证明: (opow_pos u <| pos_iff_ne_zero.2 hb).trans_le
    (le_mul_left _ <| pos_iff_ne_zero.2 hv).trans le_self_add

Depends on / 依赖: le_mul_left, le_self_add, opow_pos, pos_iff_ne_zero, trans_le
-/
theorem opow_mul_add_pos {b v : Ordinal} (hb : b != 0) (u : Ordinal) (hv : v != 0) (w : Ordinal) :
    0 < b ^ u * v + w :=
(opow_pos u <| pos_iff_ne_zero.2 hb).trans_le
    (le_mul_left _ <| pos_iff_ne_zero.2 hv).trans le_self_add

/--
theorem `opow_mul_add_lt_opow_mul` / 定理 `opow_mul_add_lt_opow_mul`

English:
theorem opow_mul_add_lt_opow_mul
  given: {b u w x : Ordinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x)
  proof: by
  apply lt_of_lt_of_le (b := b ^ u * (v + 1))
  · rwa [mul_add_one, add_lt_add_iff_left]
  · grw [add_one_le_of_lt hv]

中文:
定理 opow_mul_add_lt_opow_mul
  条件: {b u w x : Ordinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x)
  证明: by
  apply lt_of_lt_of_le (b := b ^ u * (v + 1))
  · rwa [mul_add_one, add_lt_add_iff_left]
  · grw [add_one_le_of_lt hv]

Depends on / 依赖: add_lt_add_iff_left, add_one_le_of_lt, lt_of_lt_of_le, mul_add_one
-/
theorem opow_mul_add_lt_opow_mul {b u w x : Ordinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x) :
    b ^ u * v + w < b ^ u * x := by
  apply lt_of_lt_of_le (b := b ^ u * (v + 1))
  · rwa [mul_add_one, add_lt_add_iff_left]
  · grw [add_one_le_of_lt hv]

/--
theorem `opow_mul_add_lt_opow` / 定理 `opow_mul_add_lt_opow`

English:
theorem opow_mul_add_lt_opow
  given: {b u v w x : Ordinal} (hv : v < b) (hw : w < b ^ u) (hu : u < x)
  proof: by
  apply (opow_mul_add_lt_opow_mul hw hv).trans_le
  rw [← opow_succ]
  exact opow_le_opow_right hv.pos (succ_le_of_lt hu)

中文:
定理 opow_mul_add_lt_opow
  条件: {b u v w x : Ordinal} (hv : v < b) (hw : w < b ^ u) (hu : u < x)
  证明: by
  apply (opow_mul_add_lt_opow_mul hw hv).trans_le
  rw [← opow_succ]
  exact opow_le_opow_right hv.pos (succ_le_of_lt hu)

Depends on / 依赖: hv.pos, opow_le_opow_right, opow_mul_add_lt_opow_mul, opow_succ, succ_le_of_lt, trans_le
-/
theorem opow_mul_add_lt_opow {b u v w x : Ordinal} (hv : v < b) (hw : w < b ^ u) (hu : u < x) :
    b ^ u * v + w < b ^ x := by
  apply (opow_mul_add_lt_opow_mul hw hv).trans_le
  rw [← opow_succ]
  exact opow_le_opow_right hv.pos (succ_le_of_lt hu)

/--
theorem `opow_mul_lt_opow` / 定理 `opow_mul_lt_opow`

English:
theorem opow_mul_lt_opow
  given: {b u v x : Ordinal} (hv : v < b) (hu : u < x)
  statement: b ^ u * v < b ^ x
  proof: by
  simpa using opow_mul_add_lt_opow hv (opow_pos _ hv.pos) hu

中文:
定理 opow_mul_lt_opow
  条件: {b u v x : Ordinal} (hv : v < b) (hu : u < x)
  结论: b ^ u * v < b ^ x
  证明: by
  simpa using opow_mul_add_lt_opow hv (opow_pos _ hv.pos) hu

Depends on / 依赖: hv.pos, opow_mul_add_lt_opow, opow_pos
-/
theorem opow_mul_lt_opow {b u v x : Ordinal} (hv : v < b) (hu : u < x) : b ^ u * v < b ^ x := by
  simpa using opow_mul_add_lt_opow hv (opow_pos _ hv.pos) hu

/-! ### Ordinal logarithm -/

/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
`w < b ^ u`.

We special case `log 0 x = log 1 x = 0`, as well as `log b 0 = 0`. -/
@[pp_nodot]
/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (b x : Ordinal)
  body: sSup ((b ^ ·) ⁻¹' Iic x)

@[simp]

中文:
定义 log
  签名: (b x : Ordinal)
  定义体: sSup ((b ^ ·) ⁻¹' Iic x)

@[simp]
-/
def log (b x : Ordinal) : Ordinal :=
  sSup ((b ^ ·) ⁻¹' Iic x)

@[simp]
/--
theorem `log_of_left_le_one` / 定理 `log_of_left_le_one`

English:
theorem log_of_left_le_one
  given: {b : Ordinal} (h : b <= 1) (x : Ordinal)
  statement: log b x = 0
  proof: by
  obtain rfl | rfl := le_one_iff.1 h
  · apply (csSup_of_not_bddAbove _).trans csSup_empty
    by_contra! hb
    refine not_bddAbove_Ici 1 (hb.mono fun a => ?_)
    simp +contextual [one_le_iff_ne_zero]
  · simp_rw [log, one_opow, preimage_const]
    split_ifs <;> simp

中文:
定理 log_of_left_le_one
  条件: {b : Ordinal} (h : b <= 1) (x : Ordinal)
  结论: log b x = 0
  证明: by
  obtain rfl | rfl := le_one_iff.1 h
  · apply (csSup_of_not_bddAbove _).trans csSup_empty
    by_contra! hb
    refine not_bddAbove_Ici 1 (hb.mono fun a => ?_)
    simp +contextual [one_le_iff_ne_zero]
  · simp_rw [log, one_opow, preimage_const]
    split_ifs <;> simp

Depends on / 依赖: contextual, csSup_empty, csSup_of_not_bddAbove, hb.mono, le_one_iff, not_bddAbove_Ici, one_le_iff_ne_zero, one_opow, preimage_const, simp_rw, split_ifs
-/
theorem log_of_left_le_one {b : Ordinal} (h : b <= 1) (x : Ordinal) : log b x = 0 := by
  obtain rfl | rfl := le_one_iff.1 h
  · apply (csSup_of_not_bddAbove _).trans csSup_empty
    by_contra! hb
    refine not_bddAbove_Ici 1 (hb.mono fun a => ?_)
    simp +contextual [one_le_iff_ne_zero]
  · simp_rw [log, one_opow, preimage_const]
    split_ifs <;> simp

/--
theorem `log_zero_left` / 定理 `log_zero_left`

English:
theorem log_zero_left
  given: (x : Ordinal)
  statement: log 0 x = 0
  proof: by simp

中文:
定理 log_zero_left
  条件: (x : Ordinal)
  结论: log 0 x = 0
  证明: by simp
-/
theorem log_zero_left (x : Ordinal) : log 0 x = 0 := by simp
/--
theorem `log_one_left` / 定理 `log_one_left`

English:
theorem log_one_left
  given: (x : Ordinal)
  statement: log 1 x = 0
  proof: by simp

@[simp]

中文:
定理 log_one_left
  条件: (x : Ordinal)
  结论: log 1 x = 0
  证明: by simp

@[simp]
-/
theorem log_one_left (x : Ordinal) : log 1 x = 0 := by simp

@[simp]
/--
theorem `log_zero_right` / 定理 `log_zero_right`

English:
theorem log_zero_right
  given: (b : Ordinal)
  statement: log b 0 = 0
  proof: by
  obtain rfl | hb := eq_or_ne b 0
  · exact log_zero_left 0
  · rw [log]
    convert! csSup_empty
    aesop

中文:
定理 log_zero_right
  条件: (b : Ordinal)
  结论: log b 0 = 0
  证明: by
  obtain rfl | hb := eq_or_ne b 0
  · exact log_zero_left 0
  · rw [log]
    convert! csSup_empty
    aesop

Depends on / 依赖: convert, csSup_empty, eq_or_ne, log_zero_left
-/
theorem log_zero_right (b : Ordinal) : log b 0 = 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · exact log_zero_left 0
  · rw [log]
    convert! csSup_empty
    aesop

/--
theorem `opow_le_iff_le_log` / 定理 `opow_le_iff_le_log`

English:
theorem opow_le_iff_le_log
  given: {b x c : Ordinal} (hb : 1 < b) (hx : x != 0)
  proof: (isNormal_opow hb).le_iff_le_sSup' ⟨0, by simpa [one_le_iff_ne_zero]⟩

中文:
定理 opow_le_iff_le_log
  条件: {b x c : Ordinal} (hb : 1 < b) (hx : x != 0)
  证明: (isNormal_opow hb).le_iff_le_sSup' ⟨0, by simpa [one_le_iff_ne_zero]⟩

Depends on / 依赖: isNormal_opow, le_iff_le_sSup, one_le_iff_ne_zero
-/
theorem opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x != 0) :
    b ^ c <= x ↔ c <= log b x :=
  (isNormal_opow hb).le_iff_le_sSup' ⟨0, by simpa [one_le_iff_ne_zero]⟩

/--
theorem `opow_le_iff_le_log'` / 定理 `opow_le_iff_le_log'`

English:
theorem opow_le_iff_le_log'
  given: {b x c : Ordinal} (hb : 1 < b) (hc : c != 0)
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simpa [hc] using hb.ne_bot
  · exact opow_le_iff_le_log hb hx

中文:
定理 opow_le_iff_le_log'
  条件: {b x c : Ordinal} (hb : 1 < b) (hc : c != 0)
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simpa [hc] using hb.ne_bot
  · exact opow_le_iff_le_log hb hx

Depends on / 依赖: eq_or_ne, hb.ne_bot, ne_bot, opow_le_iff_le_log
-/
theorem opow_le_iff_le_log' {b x c : Ordinal} (hb : 1 < b) (hc : c != 0) :
    b ^ c <= x ↔ c <= log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa [hc] using hb.ne_bot
  · exact opow_le_iff_le_log hb hx

/--
theorem `le_log_of_opow_le` / 定理 `le_log_of_opow_le`

English:
theorem le_log_of_opow_le
  given: {b x c : Ordinal} (hb : 1 < b) (h : b ^ c <= x)
  statement: c <= log b x
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · rw [nonpos_iff_eq_zero, opow_eq_zero] at h
    exact (zero_lt_one.asymm <| h.1 ▸ hb).elim
  · exact (opow_le_iff_le_log hb hx).1 h

中文:
定理 le_log_of_opow_le
  条件: {b x c : Ordinal} (hb : 1 < b) (h : b ^ c <= x)
  结论: c <= log b x
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · rw [nonpos_iff_eq_zero, opow_eq_zero] at h
    exact (zero_lt_one.asymm <| h.1 ▸ hb).elim
  · exact (opow_le_iff_le_log hb hx).1 h

Depends on / 依赖: eq_or_ne, nonpos_iff_eq_zero, opow_eq_zero, opow_le_iff_le_log, zero_lt_one, zero_lt_one.asymm
-/
theorem le_log_of_opow_le {b x c : Ordinal} (hb : 1 < b) (h : b ^ c <= x) : c <= log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [nonpos_iff_eq_zero, opow_eq_zero] at h
    exact (zero_lt_one.asymm <| h.1 ▸ hb).elim
  · exact (opow_le_iff_le_log hb hx).1 h

/--
theorem `opow_le_of_le_log` / 定理 `opow_le_of_le_log`

English:
theorem opow_le_of_le_log
  given: {b x c : Ordinal} (hc : c != 0) (h : c <= log b x)
  statement: b ^ c <= x
  proof: by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb] at h
    exact (h.not_gt (pos_iff_ne_zero.2 hc)).elim
  · rwa [opow_le_iff_le_log' hb hc]

中文:
定理 opow_le_of_le_log
  条件: {b x c : Ordinal} (hc : c != 0) (h : c <= log b x)
  结论: b ^ c <= x
  证明: by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb] at h
    exact (h.not_gt (pos_iff_ne_zero.2 hc)).elim
  · rwa [opow_le_iff_le_log' hb hc]

Depends on / 依赖: h.not_gt, le_or_gt, log_of_left_le_one, not_gt, opow_le_iff_le_log, pos_iff_ne_zero
-/
theorem opow_le_of_le_log {b x c : Ordinal} (hc : c != 0) (h : c <= log b x) : b ^ c <= x := by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb] at h
    exact (h.not_gt (pos_iff_ne_zero.2 hc)).elim
  · rwa [opow_le_iff_le_log' hb hc]

/--
theorem `lt_opow_iff_log_lt` / 定理 `lt_opow_iff_log_lt`

English:
theorem lt_opow_iff_log_lt
  given: {b x c : Ordinal} (hb : 1 < b) (hx : x != 0)
  statement: x < b ^ c ↔ log b x < c
  proof: lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)

中文:
定理 lt_opow_iff_log_lt
  条件: {b x c : Ordinal} (hb : 1 < b) (hx : x != 0)
  结论: x < b ^ c ↔ log b x < c
  证明: lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)

Depends on / 依赖: lt_iff_lt_of_le_iff_le, opow_le_iff_le_log
-/
theorem lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x != 0) : x < b ^ c ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)

/--
theorem `lt_opow_iff_log_lt'` / 定理 `lt_opow_iff_log_lt'`

English:
theorem lt_opow_iff_log_lt'
  given: {b x c : Ordinal} (hb : 1 < b) (hc : c != 0)
  statement: x < b ^ c ↔ log b x < c
  proof: lt_iff_lt_of_le_iff_le (opow_le_iff_le_log' hb hc)

中文:
定理 lt_opow_iff_log_lt'
  条件: {b x c : Ordinal} (hb : 1 < b) (hc : c != 0)
  结论: x < b ^ c ↔ log b x < c
  证明: lt_iff_lt_of_le_iff_le (opow_le_iff_le_log' hb hc)

Depends on / 依赖: lt_iff_lt_of_le_iff_le, opow_le_iff_le_log
-/
theorem lt_opow_iff_log_lt' {b x c : Ordinal} (hb : 1 < b) (hc : c != 0) : x < b ^ c ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log' hb hc)

/--
theorem `lt_opow_of_log_lt` / 定理 `lt_opow_of_log_lt`

English:
theorem lt_opow_of_log_lt
  given: {b x c : Ordinal} (hb : 1 < b)
  statement: log b x < c -> x < b ^ c
  proof: lt_imp_lt_of_le_imp_le le_log_of_opow_le hb

中文:
定理 lt_opow_of_log_lt
  条件: {b x c : Ordinal} (hb : 1 < b)
  结论: log b x < c -> x < b ^ c
  证明: lt_imp_lt_of_le_imp_le le_log_of_opow_le hb

Depends on / 依赖: le_log_of_opow_le, lt_imp_lt_of_le_imp_le
-/
theorem lt_opow_of_log_lt {b x c : Ordinal} (hb : 1 < b) : log b x < c -> x < b ^ c :=
lt_imp_lt_of_le_imp_le le_log_of_opow_le hb

/--
theorem `lt_log_of_lt_opow` / 定理 `lt_log_of_lt_opow`

English:
theorem lt_log_of_lt_opow
  given: {b x c : Ordinal} (hc : c != 0)
  statement: x < b ^ c -> log b x < c
  proof: lt_imp_lt_of_le_imp_le opow_le_of_le_log hc

中文:
定理 lt_log_of_lt_opow
  条件: {b x c : Ordinal} (hc : c != 0)
  结论: x < b ^ c -> log b x < c
  证明: lt_imp_lt_of_le_imp_le opow_le_of_le_log hc

Depends on / 依赖: lt_imp_lt_of_le_imp_le, opow_le_of_le_log
-/
theorem lt_log_of_lt_opow {b x c : Ordinal} (hc : c != 0) : x < b ^ c -> log b x < c :=
lt_imp_lt_of_le_imp_le opow_le_of_le_log hc

/--
theorem `lt_opow_succ_log_self` / 定理 `lt_opow_succ_log_self`

English:
theorem lt_opow_succ_log_self
  given: {b : Ordinal} (hb : 1 < b) (x : Ordinal)
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using hb.pos
  · rw [lt_opow_iff_log_lt hb hx, lt_succ_iff]

中文:
定理 lt_opow_succ_log_self
  条件: {b : Ordinal} (hb : 1 < b) (x : Ordinal)
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using hb.pos
  · rw [lt_opow_iff_log_lt hb hx, lt_succ_iff]

Depends on / 依赖: eq_or_ne, hb.pos, lt_opow_iff_log_lt, lt_succ_iff
-/
theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) :
    x < b ^ succ (log b x) := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using hb.pos
  · rw [lt_opow_iff_log_lt hb hx, lt_succ_iff]

/--
theorem `opow_log_le_self` / 定理 `opow_log_le_self`

English:
theorem opow_log_le_self
  given: (b : Ordinal) {x : Ordinal} (hx : x != 0)
  statement: b ^ log b x <= x
  proof: by
  obtain hb | hb := le_or_gt b 1
  · rw [← one_le_iff_ne_zero] at hx
    obtain rfl | rfl := le_one_iff.1 hb <;> simpa
  · rw [opow_le_iff_le_log hb hx]

中文:
定理 opow_log_le_self
  条件: (b : Ordinal) {x : Ordinal} (hx : x != 0)
  结论: b ^ log b x <= x
  证明: by
  obtain hb | hb := le_or_gt b 1
  · rw [← one_le_iff_ne_zero] at hx
    obtain rfl | rfl := le_one_iff.1 hb <;> simpa
  · rw [opow_le_iff_le_log hb hx]

Depends on / 依赖: le_one_iff, le_or_gt, one_le_iff_ne_zero, opow_le_iff_le_log
-/
theorem opow_log_le_self (b : Ordinal) {x : Ordinal} (hx : x != 0) : b ^ log b x <= x := by
  obtain hb | hb := le_or_gt b 1
  · rw [← one_le_iff_ne_zero] at hx
    obtain rfl | rfl := le_one_iff.1 hb <;> simpa
  · rw [opow_le_iff_le_log hb hx]

/--
theorem `log_pos` / 定理 `log_pos`

English:
theorem log_pos
  given: {b o : Ordinal} (hb : 1 < b) (ho : o != 0) (hbo : b <= o)
  statement: 0 < log b o
  proof: by
  rwa [← add_one_le_iff, zero_add, ← opow_le_iff_le_log hb ho, opow_one]

中文:
定理 log_pos
  条件: {b o : Ordinal} (hb : 1 < b) (ho : o != 0) (hbo : b <= o)
  结论: 0 < log b o
  证明: by
  rwa [← add_one_le_iff, zero_add, ← opow_le_iff_le_log hb ho, opow_one]

Depends on / 依赖: add_one_le_iff, opow_le_iff_le_log, opow_one, zero_add
-/
theorem log_pos {b o : Ordinal} (hb : 1 < b) (ho : o != 0) (hbo : b <= o) : 0 < log b o := by
  rwa [← add_one_le_iff, zero_add, ← opow_le_iff_le_log hb ho, opow_one]

/--
theorem `log_eq_zero` / 定理 `log_eq_zero`

English:
theorem log_eq_zero
  given: {b o : Ordinal} (hbo : o < b)
  statement: log b o = 0
  proof: by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  rcases le_or_gt b 1 with hb | hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← nonpos_iff_eq_zero, ← lt_add_one_iff, zero_add, ← lt_opow_iff_log_lt hb ho, opow_one]



中文:
定理 log_eq_zero
  条件: {b o : Ordinal} (hbo : o < b)
  结论: log b o = 0
  证明: by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  rcases le_or_gt b 1 with hb | hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← nonpos_iff_eq_zero, ← lt_add_one_iff, zero_add, ← lt_opow_iff_log_lt hb ho, opow_one]



Depends on / 依赖: eq_or_ne, le_one_iff, le_or_gt, log_one_left, log_zero_left, log_zero_right, lt_add_one_iff, lt_opow_iff_log_lt, nonpos_iff_eq_zero, opow_one, zero_add
-/
theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  rcases le_or_gt b 1 with hb | hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← nonpos_iff_eq_zero, ← lt_add_one_iff, zero_add, ← lt_opow_iff_log_lt hb ho, opow_one]

@[gcongr, mono]
/--
theorem `log_mono_right` / 定理 `log_mono_right`

English:
theorem log_mono_right
  given: (b : Ordinal) {x y : Ordinal} (xy : x <= y)
  statement: log b x <= log b y
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [log_zero_right, zero_le]
  · obtain hb | hb := lt_or_ge 1 b
· exact (opow_le_iff_le_log hb (hx.bot_lt.trans_le xy).ne').1
        (opow_log_le_self _ hx).trans xy
    · rw [log_of_left_le_one hb, log_of_left_le_one hb]

中文:
定理 log_mono_right
  条件: (b : Ordinal) {x y : Ordinal} (xy : x <= y)
  结论: log b x <= log b y
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [log_zero_right, zero_le]
  · obtain hb | hb := lt_or_ge 1 b
· exact (opow_le_iff_le_log hb (hx.bot_lt.trans_le xy).ne').1
        (opow_log_le_self _ hx).trans xy
    · rw [log_of_left_le_one hb, log_of_left_le_one hb]

Depends on / 依赖: bot_lt, eq_or_ne, hx.bot_lt.trans_le, log_of_left_le_one, log_zero_right, lt_or_ge, opow_le_iff_le_log, opow_log_le_self, simp_rw, trans_le, zero_le
-/
theorem log_mono_right (b : Ordinal) {x y : Ordinal} (xy : x <= y) : log b x <= log b y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [log_zero_right, zero_le]
  · obtain hb | hb := lt_or_ge 1 b
· exact (opow_le_iff_le_log hb (hx.bot_lt.trans_le xy).ne').1
        (opow_log_le_self _ hx).trans xy
    · rw [log_of_left_le_one hb, log_of_left_le_one hb]

/--
theorem `log_le_self` / 定理 `log_le_self`

English:
theorem log_le_self
  given: (b x : Ordinal)
  statement: log b x <= x
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero_right]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (right_le_opow _ hb).trans (opow_log_le_self b hx)
    · simp_rw [log_of_left_le_one hb, zero_le]

@[simp]

中文:
定理 log_le_self
  条件: (b x : Ordinal)
  结论: log b x <= x
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero_right]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (right_le_opow _ hb).trans (opow_log_le_self b hx)
    · simp_rw [log_of_left_le_one hb, zero_le]

@[simp]

Depends on / 依赖: eq_or_ne, log_of_left_le_one, log_zero_right, lt_or_ge, opow_log_le_self, right_le_opow, simp_rw, zero_le
-/
theorem log_le_self (b x : Ordinal) : log b x <= x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero_right]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (right_le_opow _ hb).trans (opow_log_le_self b hx)
    · simp_rw [log_of_left_le_one hb, zero_le]

@[simp]
/--
theorem `log_one_right` / 定理 `log_one_right`

English:
theorem log_one_right
  given: (b : Ordinal)
  statement: log b 1 = 0
  proof: by
  obtain hb | hb := lt_or_ge 1 b
  · exact log_eq_zero hb
  · exact log_of_left_le_one hb 1

中文:
定理 log_one_right
  条件: (b : Ordinal)
  结论: log b 1 = 0
  证明: by
  obtain hb | hb := lt_or_ge 1 b
  · exact log_eq_zero hb
  · exact log_of_left_le_one hb 1

Depends on / 依赖: log_eq_zero, log_of_left_le_one, lt_or_ge
-/
theorem log_one_right (b : Ordinal) : log b 1 = 0 := by
  obtain hb | hb := lt_or_ge 1 b
  · exact log_eq_zero hb
  · exact log_of_left_le_one hb 1

/--
theorem `mod_opow_log_lt_self` / 定理 `mod_opow_log_lt_self`

English:
theorem mod_opow_log_lt_self
  given: (b : Ordinal) {o : Ordinal} (ho : o != 0)
  statement: o % (b ^ log b o) < o
  proof: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)

中文:
定理 mod_opow_log_lt_self
  条件: (b : Ordinal) {o : Ordinal} (ho : o != 0)
  结论: o % (b ^ log b o) < o
  证明: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)

Depends on / 依赖: eq_or_ne, mod_lt, opow_log_le_self, opow_ne_zero, pos_iff_ne_zero, trans_le
-/
theorem mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o != 0) : o % (b ^ log b o) < o := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)

/--
theorem `log_mod_opow_log_lt_log_self` / 定理 `log_mod_opow_log_lt_log_self`

English:
theorem log_mod_opow_log_lt_log_self
  given: {b o : Ordinal} (hb : 1 < b) (hbo : b <= o)
  proof: by
  rcases eq_or_ne (o % (b ^ log b o)) 0 with h | h
  · rw [h, log_zero_right]
    exact log_pos hb (one_le_iff_ne_zero.1 (hb.le.trans hbo)) hbo
  · rw [← lt_opow_iff_log_lt hb h]
    exact mod_lt _ (opow_pos _ hb.pos).ne'

中文:
定理 log_mod_opow_log_lt_log_self
  条件: {b o : Ordinal} (hb : 1 < b) (hbo : b <= o)
  证明: by
  rcases eq_or_ne (o % (b ^ log b o)) 0 with h | h
  · rw [h, log_zero_right]
    exact log_pos hb (one_le_iff_ne_zero.1 (hb.le.trans hbo)) hbo
  · rw [← lt_opow_iff_log_lt hb h]
    exact mod_lt _ (opow_pos _ hb.pos).ne'

Depends on / 依赖: eq_or_ne, hb.le.trans, hb.pos, log_pos, log_zero_right, lt_opow_iff_log_lt, mod_lt, one_le_iff_ne_zero, opow_pos
-/
theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (hbo : b <= o) :
    log b (o % (b ^ log b o)) < log b o := by
  rcases eq_or_ne (o % (b ^ log b o)) 0 with h | h
  · rw [h, log_zero_right]
    exact log_pos hb (one_le_iff_ne_zero.1 (hb.le.trans hbo)) hbo
  · rw [← lt_opow_iff_log_lt hb h]
    exact mod_lt _ (opow_pos _ hb.pos).ne'

/--
theorem `log_eq_iff` / 定理 `log_eq_iff`

English:
theorem log_eq_iff
  given: {b x : Ordinal} (hb : 1 < b) (hx : x != 0) (y : Ordinal)
  proof: by
  constructor
  · rintro rfl
    use opow_log_le_self b hx, lt_opow_succ_log_self hb x
  · rintro ⟨hx₁, hx₂⟩
    apply le_antisymm
    · rwa [← lt_add_one_iff, ← lt_opow_iff_log_lt hb hx]
    · rwa [← opow_le_iff_le_log hb hx]

中文:
定理 log_eq_iff
  条件: {b x : Ordinal} (hb : 1 < b) (hx : x != 0) (y : Ordinal)
  证明: by
  constructor
  · rintro rfl
    use opow_log_le_self b hx, lt_opow_succ_log_self hb x
  · rintro ⟨hx₁, hx₂⟩
    apply le_antisymm
    · rwa [← lt_add_one_iff, ← lt_opow_iff_log_lt hb hx]
    · rwa [← opow_le_iff_le_log hb hx]

Depends on / 依赖: le_antisymm, lt_add_one_iff, lt_opow_iff_log_lt, lt_opow_succ_log_self, opow_le_iff_le_log, opow_log_le_self
-/
theorem log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x != 0) (y : Ordinal) :
    log b x = y ↔ b ^ y <= x ∧ x < b ^ (y + 1) := by
  constructor
  · rintro rfl
    use opow_log_le_self b hx, lt_opow_succ_log_self hb x
  · rintro ⟨hx₁, hx₂⟩
    apply le_antisymm
    · rwa [← lt_add_one_iff, ← lt_opow_iff_log_lt hb hx]
    · rwa [← opow_le_iff_le_log hb hx]

/--
theorem `log_opow_mul_add` / 定理 `log_opow_mul_add`

English:
theorem log_opow_mul_add
  given: {b u v w : Ordinal} (hb : 1 < b) (hv : v != 0) (hw : w < b ^ u)
  proof: by
  rw [log_eq_iff hb]
  · constructor
    · grw [opow_add, opow_log_le_self b hv, ← le_self_add]
    · grw [hw, ← mul_add_one, add_assoc, opow_add]
      gcongr
      rw [add_one_le_iff]
      exact lt_opow_succ_log_self hb _
· exact fun h => mul_ne_zero (opow_ne_zero u (bot_lt_of_lt hb).ne') hv
 

中文:
定理 log_opow_mul_add
  条件: {b u v w : Ordinal} (hb : 1 < b) (hv : v != 0) (hw : w < b ^ u)
  证明: by
  rw [log_eq_iff hb]
  · constructor
    · grw [opow_add, opow_log_le_self b hv, ← le_self_add]
    · grw [hw, ← mul_add_one, add_assoc, opow_add]
      gcongr
      rw [add_one_le_iff]
      exact lt_opow_succ_log_self hb _
· exact fun h => mul_ne_zero (opow_ne_zero u (bot_lt_of_lt hb).ne') hv
 

Depends on / 依赖: add_assoc, add_one_le_iff, bot_lt_of_lt, le_self_add, left_eq_zero_of_add_eq_zero, log_eq_iff, lt_opow_succ_log_self, mul_add_one, mul_ne_zero, opow_add, opow_log_le_self, opow_ne_zero
-/
theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v != 0) (hw : w < b ^ u) :
    log b (b ^ u * v + w) = u + log b v := by
  rw [log_eq_iff hb]
  · constructor
    · grw [opow_add, opow_log_le_self b hv, ← le_self_add]
    · grw [hw, ← mul_add_one, add_assoc, opow_add]
      gcongr
      rw [add_one_le_iff]
      exact lt_opow_succ_log_self hb _
· exact fun h => mul_ne_zero (opow_ne_zero u (bot_lt_of_lt hb).ne') hv
      left_eq_zero_of_add_eq_zero h

/--
theorem `log_opow_mul` / 定理 `log_opow_mul`

English:
theorem log_opow_mul
  given: {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v != 0)
  proof: by
  simpa using log_opow_mul_add hb hv (opow_pos u (bot_lt_of_lt hb))

中文:
定理 log_opow_mul
  条件: {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v != 0)
  证明: by
  simpa using log_opow_mul_add hb hv (opow_pos u (bot_lt_of_lt hb))

Depends on / 依赖: bot_lt_of_lt, log_opow_mul_add, opow_pos
-/
theorem log_opow_mul {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v != 0) :
    log b (b ^ u * v) = u + log b v := by
  simpa using log_opow_mul_add hb hv (opow_pos u (bot_lt_of_lt hb))

/--
theorem `log_opow` / 定理 `log_opow`

English:
theorem log_opow
  given: {b : Ordinal} (hb : 1 < b) (x : Ordinal)
  statement: log b (b ^ x) = x
  proof: by
  convert! log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]

中文:
定理 log_opow
  条件: {b : Ordinal} (hb : 1 < b) (x : Ordinal)
  结论: log b (b ^ x) = x
  证明: by
  convert! log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]

Depends on / 依赖: add_zero, convert, log_one_right, log_opow_mul, mul_one, zero_ne_one, zero_ne_one.symm
-/
theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b ^ x) = x := by
  convert! log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]

/--
theorem `div_opow_log_pos` / 定理 `div_opow_log_pos`

English:
theorem div_opow_log_pos
  given: (b : Ordinal) {o : Ordinal} (ho : o != 0)
  statement: 0 < o / b ^ log b o
  proof: by
  rcases eq_zero_or_pos b with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · rw [div_pos (opow_ne_zero _ hb.ne')]
    exact opow_log_le_self b ho

中文:
定理 div_opow_log_pos
  条件: (b : Ordinal) {o : Ordinal} (ho : o != 0)
  结论: 0 < o / b ^ log b o
  证明: by
  rcases eq_zero_or_pos b with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · rw [div_pos (opow_ne_zero _ hb.ne')]
    exact opow_log_le_self b ho

Depends on / 依赖: div_pos, eq_zero_or_pos, hb.ne, opow_log_le_self, opow_ne_zero, pos_iff_ne_zero
-/
theorem div_opow_log_pos (b : Ordinal) {o : Ordinal} (ho : o != 0) : 0 < o / b ^ log b o := by
  rcases eq_zero_or_pos b with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · rw [div_pos (opow_ne_zero _ hb.ne')]
    exact opow_log_le_self b ho

/--
theorem `div_opow_log_lt` / 定理 `div_opow_log_lt`

English:
theorem div_opow_log_lt
  given: {b : Ordinal} (o : Ordinal) (hb : 1 < b)
  statement: o / b ^ log b o < b
  proof: by
  rw [← lt_mul_iff_div_lt (opow_pos _ (zero_lt_one.trans hb)).ne']; rw [← opow_succ]
  exact lt_opow_succ_log_self hb o

中文:
定理 div_opow_log_lt
  条件: {b : Ordinal} (o : Ordinal) (hb : 1 < b)
  结论: o / b ^ log b o < b
  证明: by
  rw [← lt_mul_iff_div_lt (opow_pos _ (zero_lt_one.trans hb)).ne']; rw [← opow_succ]
  exact lt_opow_succ_log_self hb o

Depends on / 依赖: lt_mul_iff_div_lt, lt_opow_succ_log_self, opow_pos, opow_succ, zero_lt_one, zero_lt_one.trans
-/
theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / b ^ log b o < b := by
  rw [← lt_mul_iff_div_lt (opow_pos _ (zero_lt_one.trans hb)).ne']; rw [← opow_succ]
  exact lt_opow_succ_log_self hb o

/--
theorem `div_two_opow_log` / 定理 `div_two_opow_log`

English:
theorem div_two_opow_log
  given: {o : Ordinal} (ho : o != 0)
  statement: o / 2 ^ log 2 o = 1
  proof: by
  apply le_antisymm
  · simpa [← one_add_one_eq_two] using div_opow_log_lt o one_lt_two
  · simpa [one_le_iff_ne_zero, pos_iff_ne_zero] using div_opow_log_pos 2 ho

中文:
定理 div_two_opow_log
  条件: {o : Ordinal} (ho : o != 0)
  结论: o / 2 ^ log 2 o = 1
  证明: by
  apply le_antisymm
  · simpa [← one_add_one_eq_two] using div_opow_log_lt o one_lt_two
  · simpa [one_le_iff_ne_zero, pos_iff_ne_zero] using div_opow_log_pos 2 ho

Depends on / 依赖: div_opow_log_lt, div_opow_log_pos, le_antisymm, one_add_one_eq_two, one_le_iff_ne_zero, one_lt_two, pos_iff_ne_zero
-/
theorem div_two_opow_log {o : Ordinal} (ho : o != 0) : o / 2 ^ log 2 o = 1 := by
  apply le_antisymm
  · simpa [← one_add_one_eq_two] using div_opow_log_lt o one_lt_two
  · simpa [one_le_iff_ne_zero, pos_iff_ne_zero] using div_opow_log_pos 2 ho

/--
theorem `two_opow_log_add` / 定理 `two_opow_log_add`

English:
theorem two_opow_log_add
  given: {o : Ordinal} (ho : o != 0)
  statement: 2 ^ log 2 o + o % 2 ^ log 2 o = o
  proof: by
  convert! div_add_mod .. using 2
  rw [div_two_opow_log ho]; rw [mul_one]

中文:
定理 two_opow_log_add
  条件: {o : Ordinal} (ho : o != 0)
  结论: 2 ^ log 2 o + o % 2 ^ log 2 o = o
  证明: by
  convert! div_add_mod .. using 2
  rw [div_two_opow_log ho]; rw [mul_one]

Depends on / 依赖: convert, div_add_mod, div_two_opow_log, mul_one
-/
theorem two_opow_log_add {o : Ordinal} (ho : o != 0) : 2 ^ log 2 o + o % 2 ^ log 2 o = o := by
  convert! div_add_mod .. using 2
  rw [div_two_opow_log ho]; rw [mul_one]

/--
theorem `add_log_le_log_mul` / 定理 `add_log_le_log_mul`

English:
theorem add_log_le_log_mul
  given: {x y : Ordinal} (b : Ordinal) (hx : x != 0) (hy : y != 0)
  proof: by
  obtain hb | hb := lt_or_ge 1 b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  · simpa only [log_of_left_le_one hb, zero_add] using le_rfl

@[deprecated opow_mul_lt_opow (since := "2026-06-01")]

中文:
定理 add_log_le_log_mul
  条件: {x y : Ordinal} (b : Ordinal) (hx : x != 0) (hy : y != 0)
  证明: by
  obtain hb | hb := lt_or_ge 1 b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  · simpa only [log_of_left_le_one hb, zero_add] using le_rfl

@[deprecated opow_mul_lt_opow (since := "2026-06-01")]

Depends on / 依赖: le_rfl, log_of_left_le_one, lt_or_ge, mul_le_mul, mul_ne_zero, opow_add, opow_le_iff_le_log, opow_log_le_self, zero_add
-/
theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x != 0) (hy : y != 0) :
    log b x + log b y <= log b (x * y) := by
  obtain hb | hb := lt_or_ge 1 b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  · simpa only [log_of_left_le_one hb, zero_add] using le_rfl

@[deprecated opow_mul_lt_opow (since := "2026-06-01")]
/--
theorem `omega0_opow_mul_nat_lt` / 定理 `omega0_opow_mul_nat_lt`

English:
theorem omega0_opow_mul_nat_lt
  given: {a b : Ordinal} (h : a < b) (n : Nat)
  statement: ω ^ a * n < ω ^ b
  proof: opow_mul_lt_opow (natCast_lt_omega0 n) h

中文:
定理 omega0_opow_mul_nat_lt
  条件: {a b : Ordinal} (h : a < b) (n : 自然数)
  结论: ω ^ a * n < ω ^ b
  证明: opow_mul_lt_opow (natCast_lt_omega0 n) h

Depends on / 依赖: natCast_lt_omega0, opow_mul_lt_opow
-/
theorem omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : Nat) : ω ^ a * n < ω ^ b :=
  opow_mul_lt_opow (natCast_lt_omega0 n) h

/--
theorem `sub_omega0_opow_log_lt` / 定理 `sub_omega0_opow_log_lt`

English:
theorem sub_omega0_opow_log_lt
  given: {a : Ordinal} (ha : a != 0)
  statement: a - ω ^ log ω a < a
  proof: by
obtain ⟨n, hn⟩ := lt_omega0.1 div_opow_log_lt a one_lt_omega0
  conv_lhs => left; rw [← div_add_mod a (ω ^ log ω a), hn]
  cases n with
  | zero =>
    simpa using ((div_pos (opow_ne_zero _ omega0_ne_zero)).2 (opow_log_le_self _ ha)).trans_eq hn
  | succ n =>
    rw [add_comm]; rw [Nat.cast_add];

中文:
定理 sub_omega0_opow_log_lt
  条件: {a : Ordinal} (ha : a != 0)
  结论: a - ω ^ log ω a < a
  证明: by
obtain ⟨n, hn⟩ := lt_omega0.1 div_opow_log_lt a one_lt_omega0
  conv_lhs => left; rw [← div_add_mod a (ω ^ log ω a), hn]
  cases n with
  | zero =>
    simpa using ((div_pos (opow_ne_zero _ omega0_ne_zero)).2 (opow_log_le_self _ ha)).trans_eq hn
  | succ n =>
    rw [add_comm]; rw [Nat.cast_add];

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Ordinal, Ordinal.add_sub_cancel, Ordinal.mul_le_iff_le_div, add_assoc, add_comm, add_sub_cancel, cast_add, cast_one, conv_lhs, div_add_mod, div_opow_log_lt, div_pos, lt_add_one, lt_omega0, mod_lt, mul_le_iff_le_div, mul_one_add, omega0_ne_zero
-/
theorem sub_omega0_opow_log_lt {a : Ordinal} (ha : a != 0) : a - ω ^ log ω a < a := by
obtain ⟨n, hn⟩ := lt_omega0.1 div_opow_log_lt a one_lt_omega0
  conv_lhs => left; rw [← div_add_mod a (ω ^ log ω a), hn]
  cases n with
  | zero =>
    simpa using ((div_pos (opow_ne_zero _ omega0_ne_zero)).2 (opow_log_le_self _ ha)).trans_eq hn
  | succ n =>
    rw [add_comm]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [mul_one_add]; rw [add_assoc]; rw [Ordinal.add_sub_cancel]
    apply (opow_mul_add_lt_opow_mul _ (lt_add_one _)).trans_le
    · rw [Ordinal.mul_le_iff_le_div, hn] <;> simp
    · exact mod_lt _ (opow_ne_zero _ omega0_ne_zero)

/--
theorem `lt_omega0_opow` / 定理 `lt_omega0_opow`

English:
theorem lt_omega0_opow
  given: {a b : Ordinal} (hb : b != 0)
  proof: by
  refine ⟨fun ha => ⟨_, lt_log_of_lt_opow hb ha, ?_⟩,
    fun ⟨c, hc, n, hn⟩ => hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) hc)⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  use n + 1
  rw [Nat.cast_add_one]; rw [← hn]
  exact lt_mul_succ_div a (opow_ne_zero _ omega0_n

中文:
定理 lt_omega0_opow
  条件: {a b : Ordinal} (hb : b != 0)
  证明: by
  refine ⟨fun ha => ⟨_, lt_log_of_lt_opow hb ha, ?_⟩,
    fun ⟨c, hc, n, hn⟩ => hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) hc)⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  use n + 1
  rw [Nat.cast_add_one]; rw [← hn]
  exact lt_mul_succ_div a (opow_ne_zero _ omega0_n

Depends on / 依赖: Nat.cast_add_one, cast_add_one, div_opow_log_lt, hn.trans, lt_log_of_lt_opow, lt_mul_succ_div, lt_omega0, natCast_lt_omega0, omega0_ne_zero, one_lt_omega0, opow_mul_lt_opow, opow_ne_zero
-/
theorem lt_omega0_opow {a b : Ordinal} (hb : b != 0) :
    a < ω ^ b ↔ exists c < b, exists n : Nat, a < ω ^ c * n := by
  refine ⟨fun ha => ⟨_, lt_log_of_lt_opow hb ha, ?_⟩,
    fun ⟨c, hc, n, hn⟩ => hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) hc)⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  use n + 1
  rw [Nat.cast_add_one]; rw [← hn]
  exact lt_mul_succ_div a (opow_ne_zero _ omega0_ne_zero)

/--
theorem `lt_omega0_opow_succ` / 定理 `lt_omega0_opow_succ`

English:
theorem lt_omega0_opow_succ
  given: {a b : Ordinal}
  statement: a < ω ^ succ b ↔ exists n : Nat, a < ω ^ b * n
  proof: by
  refine ⟨fun ha => ?_, fun ⟨n, hn⟩ => hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) (lt_succ b))⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (add_pos_of_right zero_lt_one b).ne').1 ha
  refine ⟨n, hn.trans_le ?_⟩
  grw [lt_succ_iff.1 hc]
  exact omega0_pos

中文:
定理 lt_omega0_opow_succ
  条件: {a b : Ordinal}
  结论: a < ω ^ succ b ↔ 存在 n : 自然数, a < ω ^ b * n
  证明: by
  refine ⟨fun ha => ?_, fun ⟨n, hn⟩ => hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) (lt_succ b))⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (add_pos_of_right zero_lt_one b).ne').1 ha
  refine ⟨n, hn.trans_le ?_⟩
  grw [lt_succ_iff.1 hc]
  exact omega0_pos

Depends on / 依赖: add_pos_of_right, hn.trans, hn.trans_le, lt_omega0_opow, lt_succ, lt_succ_iff, natCast_lt_omega0, omega0_pos, opow_mul_lt_opow, trans_le, zero_lt_one
-/
theorem lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ exists n : Nat, a < ω ^ b * n := by
  refine ⟨fun ha => ?_, fun ⟨n, hn⟩ => hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) (lt_succ b))⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (add_pos_of_right zero_lt_one b).ne').1 ha
  refine ⟨n, hn.trans_le ?_⟩
  grw [lt_succ_iff.1 hc]
  exact omega0_pos

/--
theorem `lt_omega0_omega0_opow` / 定理 `lt_omega0_omega0_opow`

English:
theorem lt_omega0_omega0_opow
  given: {a b : Ordinal} (hb : b != 0)
  proof: by
  simp_rw [lt_omega0_opow (opow_ne_zero _ omega0_ne_zero), lt_omega0_opow hb]
  constructor
  · intro ⟨a, ⟨b, hb, ⟨m, hm⟩⟩, ⟨n, hn⟩⟩
exact ⟨_, hb, _, hn.trans opow_mul_lt_opow (natCast_lt_omega0 _)
      hm.trans_le (mul_le_mul_right (Nat.cast_le.2 m.le_succ) _)⟩
  · intro ⟨a, ha, ⟨n, hn⟩⟩
    re

中文:
定理 lt_omega0_omega0_opow
  条件: {a b : Ordinal} (hb : b != 0)
  证明: by
  simp_rw [lt_omega0_opow (opow_ne_zero _ omega0_ne_zero), lt_omega0_opow hb]
  constructor
  · intro ⟨a, ⟨b, hb, ⟨m, hm⟩⟩, ⟨n, hn⟩⟩
exact ⟨_, hb, _, hn.trans opow_mul_lt_opow (natCast_lt_omega0 _)
      hm.trans_le (mul_le_mul_right (Nat.cast_le.2 m.le_succ) _)⟩
  · intro ⟨a, ha, ⟨n, hn⟩⟩
    re

Depends on / 依赖: Nat.cast_le, cast_le, hm.trans_le, hn.trans, le_succ, lt_omega0_opow, m.le_succ, mul_le_mul_right, natCast_lt_omega0, omega0_ne_zero, opow_mul_lt_opow, opow_ne_zero, opow_pos, simp_rw, trans_le
-/
theorem lt_omega0_omega0_opow {a b : Ordinal} (hb : b != 0) :
    a < ω ^ ω ^ b ↔ exists c < b, exists n : Nat, a < ω ^ (ω ^ c * n) := by
  simp_rw [lt_omega0_opow (opow_ne_zero _ omega0_ne_zero), lt_omega0_opow hb]
  constructor
  · intro ⟨a, ⟨b, hb, ⟨m, hm⟩⟩, ⟨n, hn⟩⟩
exact ⟨_, hb, _, hn.trans opow_mul_lt_opow (natCast_lt_omega0 _)
      hm.trans_le (mul_le_mul_right (Nat.cast_le.2 m.le_succ) _)⟩
  · intro ⟨a, ha, ⟨n, hn⟩⟩
    refine ⟨ω ^ a * n, ⟨a, ha, n + 1, ?_⟩, 1, ?_⟩
    · simp [mul_lt_mul_iff_right₀, opow_pos]
    · simpa

/-! ### Interaction with `Nat.cast` -/

@[simp, norm_cast]
/--
theorem `natCast_pow` / 定理 `natCast_pow`

English:
theorem natCast_pow
  given: (m : Nat)
  statement: forall n : Nat, ↑(m ^ n : Nat) = (m : Ordinal) ^ n

中文:
定理 natCast_pow
  条件: (m : 自然数)
  结论: 对任意 n : 自然数, ↑(m ^ n : 自然数) = (m : Ordinal) ^ n
-/
theorem natCast_pow (m : Nat) : forall n : Nat, ↑(m ^ n : Nat) = (m : Ordinal) ^ n
  | 0 => by simp
  | n + 1 => by simp [pow_succ, natCast_pow m n]

@[deprecated natCast_pow (since := "2026-01-31")]
/--
theorem `natCast_opow` / 定理 `natCast_opow`

English:
theorem natCast_opow
  given: (m : Nat)
  statement: forall n : Nat, ↑(m ^ n : Nat) = (m : Ordinal) ^ (n : Ordinal)
  proof: by
  simp

中文:
定理 natCast_opow
  条件: (m : 自然数)
  结论: 对任意 n : 自然数, ↑(m ^ n : 自然数) = (m : Ordinal) ^ (n : Ordinal)
  证明: by
  simp
-/
theorem natCast_opow (m : Nat) : forall n : Nat, ↑(m ^ n : Nat) = (m : Ordinal) ^ (n : Ordinal) := by
  simp

/--
theorem `iSup_pow_natCast` / 定理 `iSup_pow_natCast`

English:
theorem iSup_pow_natCast
  given: {o : Ordinal} (ho : 0 < o)
  statement: ⨆ n : Nat, o ^ n = o ^ ω
  proof: by
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · simpa using apply_omega0_of_isNormal (isNormal_opow ho₁)
  · simp

@[simp, norm_cast]

中文:
定理 iSup_pow_natCast
  条件: {o : Ordinal} (ho : 0 < o)
  结论: ⨆ n : 自然数, o ^ n = o ^ ω
  证明: by
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · simpa using apply_omega0_of_isNormal (isNormal_opow ho₁)
  · simp

@[simp, norm_cast]

Depends on / 依赖: apply_omega0_of_isNormal, isNormal_opow, lt_or_eq, one_le_iff_pos
-/
theorem iSup_pow_natCast {o : Ordinal} (ho : 0 < o) : ⨆ n : Nat, o ^ n = o ^ ω := by
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · simpa using apply_omega0_of_isNormal (isNormal_opow ho₁)
  · simp

@[simp, norm_cast]
/--
lemma `natCast_log` / 引理 `natCast_log`

English:
lemma natCast_log
  given: (m n : Nat)
  statement: ↑(Nat.log m n) = Ordinal.log ↑m ↑n
  proof: by
  obtain hm | hm := le_or_gt m 1
  case inl => rw_mod_cast [Nat.log_of_left_le_one hm, log_of_left_le_one (mod_cast hm)]
  obtain rfl | hn := eq_or_ne n 0
  case inl => simp
  rw_mod_cast [eq_comm, log_eq_iff (mod_cast hm) (mod_cast hn), ← Nat.log_eq_iff (.inr ⟨hm, hn⟩)]

中文:
引理 natCast_log
  条件: (m n : 自然数)
  结论: ↑(自然数.log m n) = Ordinal.log ↑m ↑n
  证明: by
  obtain hm | hm := le_or_gt m 1
  case inl => rw_mod_cast [Nat.log_of_left_le_one hm, log_of_left_le_one (mod_cast hm)]
  obtain rfl | hn := eq_or_ne n 0
  case inl => simp
  rw_mod_cast [eq_comm, log_eq_iff (mod_cast hm) (mod_cast hn), ← Nat.log_eq_iff (.inr ⟨hm, hn⟩)]

Depends on / 依赖: Nat.log_eq_iff, Nat.log_of_left_le_one, eq_comm, eq_or_ne, le_or_gt, log_eq_iff, log_of_left_le_one, mod_cast, rw_mod_cast
-/
lemma natCast_log (m n : Nat) : ↑(Nat.log m n) = Ordinal.log ↑m ↑n := by
  obtain hm | hm := le_or_gt m 1
  case inl => rw_mod_cast [Nat.log_of_left_le_one hm, log_of_left_le_one (mod_cast hm)]
  obtain rfl | hn := eq_or_ne n 0
  case inl => simp
  rw_mod_cast [eq_comm, log_eq_iff (mod_cast hm) (mod_cast hn), ← Nat.log_eq_iff (.inr ⟨hm, hn⟩)]

end Ordinal

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Port this meta code.

-- namespace Tactic

-- open Ordinal Mathlib.Meta.Positivity

-- /-- Extension for the `positivity` tactic: `ordinal.opow` takes positive values on positive
-- inputs. -/
-- @[positivity]
-- unsafe def positivity_opow : expr → tactic strictness
-- | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
-- let strictness_a ← core a
-- match strictness_a with
-- | positive p => positive <$> mk_app `` opow_pos [b, p]
-- | _ => failed
-- |-- We already know that `0 ≤ x` for all `x : Ordinal`
-- _ =>
-- failed

-- end Tactic
