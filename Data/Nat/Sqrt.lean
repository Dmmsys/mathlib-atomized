/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Properties of the natural number square root function.
-/

public section

namespace Nat

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

variable {m n a : Nat}


/--
lemma `sqrt_le'` / 引理 `sqrt_le'`

English:
lemma sqrt_le'
  given: (n : Nat)
  statement: sqrt n ^ 2 <= n
  proof: by simpa [Nat.pow_two] using sqrt_le n

中文:
引理 sqrt_le'
  条件: (n : 自然数)
  结论: sqrt n ^ 2 <= n
  证明: by simpa [Nat.pow_two] using sqrt_le n

Depends on / 依赖: Nat.pow_two, pow_two, sqrt_le
-/
lemma sqrt_le' (n : Nat) : sqrt n ^ 2 <= n := by simpa [Nat.pow_two] using sqrt_le n

/--
lemma `lt_succ_sqrt'` / 引理 `lt_succ_sqrt'`

English:
lemma lt_succ_sqrt'
  given: (n : Nat)
  statement: n < succ (sqrt n) ^ 2
  proof: by simpa [Nat.pow_two] using lt_succ_sqrt n

中文:
引理 lt_succ_sqrt'
  条件: (n : 自然数)
  结论: n < succ (sqrt n) ^ 2
  证明: by simpa [Nat.pow_two] using lt_succ_sqrt n

Depends on / 依赖: Nat.pow_two, lt_succ_sqrt, pow_two
-/
lemma lt_succ_sqrt' (n : Nat) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n

/--
lemma `sqrt_le_add` / 引理 `sqrt_le_add`

English:
lemma sqrt_le_add
  given: (n : Nat)
  statement: n <= sqrt n * sqrt n + sqrt n + sqrt n
  proof: by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

中文:
引理 sqrt_le_add
  条件: (n : 自然数)
  结论: n <= sqrt n * sqrt n + sqrt n + sqrt n
  证明: by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

Depends on / 依赖: le_of_lt_succ, lt_succ_sqrt, succ_mul
-/
lemma sqrt_le_add (n : Nat) : n <= sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

/--
lemma `le_sqrt` / 引理 `le_sqrt`

English:
lemma le_sqrt
  statement: m <= sqrt n ↔ m * m <= n
  proof: ⟨fun h => le_trans (mul_self_le_mul_self h) (sqrt_le n),
fun h => le_of_lt_succ Nat.mul_self_lt_mul_self_iff.1 lt_of_le_of_lt h (lt_succ_sqrt n)⟩

中文:
引理 le_sqrt
  结论: m <= sqrt n ↔ m * m <= n
  证明: ⟨fun h => le_trans (mul_self_le_mul_self h) (sqrt_le n),
fun h => le_of_lt_succ Nat.mul_self_lt_mul_self_iff.1 lt_of_le_of_lt h (lt_succ_sqrt n)⟩

Depends on / 依赖: Nat.mul_self_lt_mul_self_iff, le_of_lt_succ, le_trans, lt_of_le_of_lt, lt_succ_sqrt, mul_self_le_mul_self, mul_self_lt_mul_self_iff, sqrt_le
-/
lemma le_sqrt : m <= sqrt n ↔ m * m <= n :=
  ⟨fun h => le_trans (mul_self_le_mul_self h) (sqrt_le n),
fun h => le_of_lt_succ Nat.mul_self_lt_mul_self_iff.1 lt_of_le_of_lt h (lt_succ_sqrt n)⟩

/--
lemma `le_sqrt'` / 引理 `le_sqrt'`

English:
lemma le_sqrt'
  statement: m <= sqrt n ↔ m ^ 2 <= n
  proof: by simpa only [Nat.pow_two] using le_sqrt

中文:
引理 le_sqrt'
  结论: m <= sqrt n ↔ m ^ 2 <= n
  证明: by simpa only [Nat.pow_two] using le_sqrt

Depends on / 依赖: Nat.pow_two, le_sqrt, pow_two
-/
lemma le_sqrt' : m <= sqrt n ↔ m ^ 2 <= n := by simpa only [Nat.pow_two] using le_sqrt

/--
lemma `sqrt_lt` / 引理 `sqrt_lt`

English:
lemma sqrt_lt
  statement: sqrt m < n ↔ m < n * n
  proof: by simp only [← not_le, le_sqrt]

中文:
引理 sqrt_lt
  结论: sqrt m < n ↔ m < n * n
  证明: by simp only [← not_le, le_sqrt]

Depends on / 依赖: le_sqrt, not_le
-/
lemma sqrt_lt : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt]

/--
lemma `sqrt_lt'` / 引理 `sqrt_lt'`

English:
lemma sqrt_lt'
  statement: sqrt m < n ↔ m < n ^ 2
  proof: by simp only [← not_le, le_sqrt']

中文:
引理 sqrt_lt'
  结论: sqrt m < n ↔ m < n ^ 2
  证明: by simp only [← not_le, le_sqrt']

Depends on / 依赖: le_sqrt, not_le
-/
lemma sqrt_lt' : sqrt m < n ↔ m < n ^ 2 := by simp only [← not_le, le_sqrt']

/--
lemma `sqrt_le_self` / 引理 `sqrt_le_self`

English:
lemma sqrt_le_self
  given: (n : Nat)
  statement: sqrt n <= n
  proof: le_trans (le_mul_self _) (sqrt_le n)

@[gcongr]

中文:
引理 sqrt_le_self
  条件: (n : 自然数)
  结论: sqrt n <= n
  证明: le_trans (le_mul_self _) (sqrt_le n)

@[gcongr]

Depends on / 依赖: le_mul_self, le_trans, sqrt_le
-/
lemma sqrt_le_self (n : Nat) : sqrt n <= n := le_trans (le_mul_self _) (sqrt_le n)

@[gcongr]
/--
lemma `sqrt_le_sqrt` / 引理 `sqrt_le_sqrt`

English:
lemma sqrt_le_sqrt
  given: (h : m <= n)
  statement: sqrt m <= sqrt n
  proof: le_sqrt.2 (le_trans (sqrt_le _) h)

中文:
引理 sqrt_le_sqrt
  条件: (h : m <= n)
  结论: sqrt m <= sqrt n
  证明: le_sqrt.2 (le_trans (sqrt_le _) h)

Depends on / 依赖: le_sqrt, le_trans, sqrt_le
-/
lemma sqrt_le_sqrt (h : m <= n) : sqrt m <= sqrt n := le_sqrt.2 (le_trans (sqrt_le _) h)

/--
lemma `eq_sqrt` / 引理 `eq_sqrt`

English:
lemma eq_sqrt
  statement: a = sqrt n ↔ a * a <= n ∧ n < (a + 1) * (a + 1)
  proof: ⟨fun e => e.symm ▸ ⟨sqrt_le n, lt_succ_sqrt n⟩,
   fun ⟨h₁, h₂⟩ => le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩

中文:
引理 eq_sqrt
  结论: a = sqrt n ↔ a * a <= n ∧ n < (a + 1) * (a + 1)
  证明: ⟨fun e => e.symm ▸ ⟨sqrt_le n, lt_succ_sqrt n⟩,
   fun ⟨h₁, h₂⟩ => le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩

Depends on / 依赖: e.symm, le_antisymm, le_of_lt_succ, le_sqrt, lt_succ_sqrt, sqrt_le, sqrt_lt
-/
lemma eq_sqrt : a = sqrt n ↔ a * a <= n ∧ n < (a + 1) * (a + 1) :=
  ⟨fun e => e.symm ▸ ⟨sqrt_le n, lt_succ_sqrt n⟩,
   fun ⟨h₁, h₂⟩ => le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩

/--
lemma `eq_sqrt'` / 引理 `eq_sqrt'`

English:
lemma eq_sqrt'
  statement: a = sqrt n ↔ a ^ 2 <= n ∧ n < (a + 1) ^ 2
  proof: by
  simpa only [Nat.pow_two] using eq_sqrt

中文:
引理 eq_sqrt'
  结论: a = sqrt n ↔ a ^ 2 <= n ∧ n < (a + 1) ^ 2
  证明: by
  simpa only [Nat.pow_two] using eq_sqrt

Depends on / 依赖: Nat.pow_two, eq_sqrt, pow_two
-/
lemma eq_sqrt' : a = sqrt n ↔ a ^ 2 <= n ∧ n < (a + 1) ^ 2 := by
  simpa only [Nat.pow_two] using eq_sqrt

/--
lemma `le_three_of_sqrt_eq_one` / 引理 `le_three_of_sqrt_eq_one`

English:
lemma le_three_of_sqrt_eq_one
  given: (h : sqrt n = 1)
  statement: n <= 3
  proof: le_of_lt_succ (@sqrt_lt n 2).1 by grind

中文:
引理 le_three_of_sqrt_eq_one
  条件: (h : sqrt n = 1)
  结论: n <= 3
  证明: le_of_lt_succ (@sqrt_lt n 2).1 by grind

Depends on / 依赖: le_of_lt_succ, sqrt_lt
-/
lemma le_three_of_sqrt_eq_one (h : sqrt n = 1) : n <= 3 :=
le_of_lt_succ (@sqrt_lt n 2).1 by grind

/--
lemma `sqrt_lt_self` / 引理 `sqrt_lt_self`

English:
lemma sqrt_lt_self
  given: (h : 1 < n)
  statement: sqrt n < n
  proof: sqrt_lt.2 by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); grind

@[grind =]

中文:
引理 sqrt_lt_self
  条件: (h : 1 < n)
  结论: sqrt n < n
  证明: sqrt_lt.2 by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); grind

@[grind =]

Depends on / 依赖: Nat.mul_lt_mul_of_pos_left, lt_of_succ_lt, mul_lt_mul_of_pos_left, sqrt_lt
-/
lemma sqrt_lt_self (h : 1 < n) : sqrt n < n :=
sqrt_lt.2 by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); grind

@[grind =]
/--
lemma `sqrt_pos` / 引理 `sqrt_pos`

English:
lemma sqrt_pos
  statement: 0 < sqrt n ↔ 0 < n
  proof: le_sqrt

中文:
引理 sqrt_pos
  结论: 0 < sqrt n ↔ 0 < n
  证明: le_sqrt

Depends on / 依赖: le_sqrt
-/
lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
  le_sqrt

/--
lemma `sqrt_add_eq` / 引理 `sqrt_add_eq`

English:
lemma sqrt_add_eq
  given: (n : Nat) (h : a <= n + n)
  statement: sqrt (n * n + a) = n
  proof: le_antisymm
    (le_of_lt_succ <| sqrt_lt.2 <| by grind)
    (le_sqrt.2 <| by grind)

中文:
引理 sqrt_add_eq
  条件: (n : 自然数) (h : a <= n + n)
  结论: sqrt (n * n + a) = n
  证明: le_antisymm
    (le_of_lt_succ <| sqrt_lt.2 <| by grind)
    (le_sqrt.2 <| by grind)

Depends on / 依赖: le_antisymm, le_of_lt_succ, le_sqrt, sqrt_lt
-/
lemma sqrt_add_eq (n : Nat) (h : a <= n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <| sqrt_lt.2 <| by grind)
    (le_sqrt.2 <| by grind)

/--
lemma `sqrt_add_eq'` / 引理 `sqrt_add_eq'`

English:
lemma sqrt_add_eq'
  given: (n : Nat) (h : a <= n + n)
  statement: sqrt (n ^ 2 + a) = n
  proof: by
  simpa [Nat.pow_two] using sqrt_add_eq n h

@[simp]

中文:
引理 sqrt_add_eq'
  条件: (n : 自然数) (h : a <= n + n)
  结论: sqrt (n ^ 2 + a) = n
  证明: by
  simpa [Nat.pow_two] using sqrt_add_eq n h

@[simp]

Depends on / 依赖: Nat.pow_two, pow_two, sqrt_add_eq
-/
lemma sqrt_add_eq' (n : Nat) (h : a <= n + n) : sqrt (n ^ 2 + a) = n := by
  simpa [Nat.pow_two] using sqrt_add_eq n h

@[simp]
/--
lemma `sqrt_eq` / 引理 `sqrt_eq`

English:
lemma sqrt_eq
  given: (n : Nat)
  statement: sqrt (n * n) = n
  proof: sqrt_add_eq n (zero_le _)

@[simp]

中文:
引理 sqrt_eq
  条件: (n : 自然数)
  结论: sqrt (n * n) = n
  证明: sqrt_add_eq n (zero_le _)

@[simp]

Depends on / 依赖: sqrt_add_eq, zero_le
-/
lemma sqrt_eq (n : Nat) : sqrt (n * n) = n := sqrt_add_eq n (zero_le _)

@[simp]
/--
lemma `sqrt_eq'` / 引理 `sqrt_eq'`

English:
lemma sqrt_eq'
  given: (n : Nat)
  statement: sqrt (n ^ 2) = n
  proof: sqrt_add_eq' n (zero_le _)

中文:
引理 sqrt_eq'
  条件: (n : 自然数)
  结论: sqrt (n ^ 2) = n
  证明: sqrt_add_eq' n (zero_le _)

Depends on / 依赖: sqrt_add_eq, zero_le
-/
lemma sqrt_eq' (n : Nat) : sqrt (n ^ 2) = n := sqrt_add_eq' n (zero_le _)

/--
lemma `sqrt_succ_le_succ_sqrt` / 引理 `sqrt_succ_le_succ_sqrt`

English:
lemma sqrt_succ_le_succ_sqrt
  given: (n : Nat)
  statement: sqrt n.succ <= n.sqrt.succ
  proof: le_of_lt_succ sqrt_lt.2 (have := sqrt_le_add n; by grind)

@[simp]

中文:
引理 sqrt_succ_le_succ_sqrt
  条件: (n : 自然数)
  结论: sqrt n.succ <= n.sqrt.succ
  证明: le_of_lt_succ sqrt_lt.2 (have := sqrt_le_add n; by grind)

@[simp]

Depends on / 依赖: le_of_lt_succ, sqrt_le_add, sqrt_lt
-/
lemma sqrt_succ_le_succ_sqrt (n : Nat) : sqrt n.succ <= n.sqrt.succ :=
le_of_lt_succ sqrt_lt.2 (have := sqrt_le_add n; by grind)

@[simp]
/--
lemma `log2_two` / 引理 `log2_two`

English:
lemma log2_two
  statement: (2 : Nat).log2 = 1
  proof: by simp [log2_def]

中文:
引理 log2_two
  结论: (2 : 自然数).log2 = 1
  证明: by simp [log2_def]

Depends on / 依赖: log2_def
-/
lemma log2_two : (2 : Nat).log2 = 1 := by simp [log2_def]

/--
lemma `sqrt_zero` / 引理 `sqrt_zero`

English:
lemma sqrt_zero
  statement: sqrt 0 = 0
  proof: eq_comm.1 (by simp [eq_sqrt])

中文:
引理 sqrt_zero
  结论: sqrt 0 = 0
  证明: eq_comm.1 (by simp [eq_sqrt])
-/
@[simp, grind =] lemma sqrt_zero : sqrt 0 = 0 :=
  eq_comm.1 (by simp [eq_sqrt])

/--
lemma `sqrt_one` / 引理 `sqrt_one`

English:
lemma sqrt_one
  statement: sqrt 1 = 1
  proof: eq_comm.1 (by simp [eq_sqrt])

中文:
引理 sqrt_one
  结论: sqrt 1 = 1
  证明: eq_comm.1 (by simp [eq_sqrt])
-/
@[simp, grind =] lemma sqrt_one : sqrt 1 = 1 :=
  eq_comm.1 (by simp [eq_sqrt])

/--
lemma `sqrt_eq_zero` / 引理 `sqrt_eq_zero`

English:
lemma sqrt_eq_zero
  statement: sqrt n = 0 ↔ n = 0
  proof: ⟨fun h => have := @sqrt_lt n 1; by grind, by grind⟩

@[simp]

中文:
引理 sqrt_eq_zero
  结论: sqrt n = 0 ↔ n = 0
  证明: ⟨fun h => have := @sqrt_lt n 1; by grind, by grind⟩

@[simp]

Depends on / 依赖: sqrt_lt
-/
lemma sqrt_eq_zero : sqrt n = 0 ↔ n = 0 :=
  ⟨fun h => have := @sqrt_lt n 1; by grind, by grind⟩

@[simp]
/--
lemma `sqrt_two` / 引理 `sqrt_two`

English:
lemma sqrt_two
  statement: sqrt 2 = 1
  proof: eq_comm.1 (by simp [eq_sqrt])

中文:
引理 sqrt_two
  结论: sqrt 2 = 1
  证明: eq_comm.1 (by simp [eq_sqrt])

Depends on / 依赖: eq_comm, eq_sqrt
-/
lemma sqrt_two : sqrt 2 = 1 :=
  eq_comm.1 (by simp [eq_sqrt])

/--
lemma `add_one_sqrt_le_of_ne_zero` / 引理 `add_one_sqrt_le_of_ne_zero`

English:
lemma add_one_sqrt_le_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  statement: (n + 1).sqrt <= n
  proof: le_induction (by simp) (fun n _ ih => le_trans n.succ.sqrt_succ_le_succ_sqrt (succ_le_succ ih)) n
    (Nat.pos_of_ne_zero hn)

中文:
引理 add_one_sqrt_le_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  结论: (n + 1).sqrt <= n
  证明: le_induction (by simp) (fun n _ ih => le_trans n.succ.sqrt_succ_le_succ_sqrt (succ_le_succ ih)) n
    (Nat.pos_of_ne_zero hn)

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, AdjoinRoot.mk_surjective, Derivation, Derivation.liftOfSurjective, Nat.pos_of_ne_zero, le_induction, le_trans, liftOfSurjective, mk_surjective, n.succ.sqrt_succ_le_succ_sqrt, pos_of_ne_zero, sqrt_succ_le_succ_sqrt, succ_le_succ, toIntAlgHom
-/
lemma add_one_sqrt_le_of_ne_zero {n : Nat} (hn : n != 0) : (n + 1).sqrt <= n :=
  le_induction (by simp) (fun n _ ih => le_trans n.succ.sqrt_succ_le_succ_sqrt (succ_le_succ ih)) n
    (Nat.pos_of_ne_zero hn)

/--
lemma `exists_mul_self` / 引理 `exists_mul_self`

English:
lemma exists_mul_self
  given: (x : Nat)
  statement: (exists n, n * n = x) ↔ sqrt x * sqrt x = x
  proof: ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq], fun h => ⟨sqrt x, h⟩⟩

中文:
引理 exists_mul_self
  条件: (x : 自然数)
  结论: (存在 n, n * n = x) ↔ sqrt x * sqrt x = x
  证明: ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq], fun h => ⟨sqrt x, h⟩⟩

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, Derivation, Derivation.liftOfSurjective, Derivation.liftOfSurjective_apply, implicitDeriv_C, liftOfSurjective, liftOfSurjective_apply, sqrt_eq, toIntAlgHom
-/
lemma exists_mul_self (x : Nat) : (exists n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq], fun h => ⟨sqrt x, h⟩⟩

/--
lemma `exists_mul_self'` / 引理 `exists_mul_self'`

English:
lemma exists_mul_self'
  given: (x : Nat)
  statement: (exists n, n ^ 2 = x) ↔ sqrt x ^ 2 = x
  proof: by
  simpa only [Nat.pow_two] using exists_mul_self x

中文:
引理 exists_mul_self'
  条件: (x : 自然数)
  结论: (存在 n, n ^ 2 = x) ↔ sqrt x ^ 2 = x
  证明: by
  simpa only [Nat.pow_two] using exists_mul_self x

Depends on / 依赖: Nat.pow_two, exists_mul_self, pow_two
-/
lemma exists_mul_self' (x : Nat) : (exists n, n ^ 2 = x) ↔ sqrt x ^ 2 = x := by
  simpa only [Nat.pow_two] using exists_mul_self x

/--
lemma `sqrt_mul_sqrt_lt_succ` / 引理 `sqrt_mul_sqrt_lt_succ`

English:
lemma sqrt_mul_sqrt_lt_succ
  given: (n : Nat)
  statement: sqrt n * sqrt n < n + 1
  proof: Nat.lt_succ_iff.mpr (sqrt_le _)

中文:
引理 sqrt_mul_sqrt_lt_succ
  条件: (n : 自然数)
  结论: sqrt n * sqrt n < n + 1
  证明: Nat.lt_succ_iff.mpr (sqrt_le _)

Depends on / 依赖: Nat.lt_succ_iff.mpr, lt_succ_iff, sqrt_le
-/
lemma sqrt_mul_sqrt_lt_succ (n : Nat) : sqrt n * sqrt n < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le _)

/--
lemma `sqrt_mul_sqrt_lt_succ'` / 引理 `sqrt_mul_sqrt_lt_succ'`

English:
lemma sqrt_mul_sqrt_lt_succ'
  given: (n : Nat)
  statement: sqrt n ^ 2 < n + 1
  proof: Nat.lt_succ_iff.mpr (sqrt_le' _)

中文:
引理 sqrt_mul_sqrt_lt_succ'
  条件: (n : 自然数)
  结论: sqrt n ^ 2 < n + 1
  证明: Nat.lt_succ_iff.mpr (sqrt_le' _)

Depends on / 依赖: Nat.lt_succ_iff.mpr, lt_succ_iff, sqrt_le
-/
lemma sqrt_mul_sqrt_lt_succ' (n : Nat) : sqrt n ^ 2 < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le' _)

/--
lemma `succ_le_succ_sqrt` / 引理 `succ_le_succ_sqrt`

English:
lemma succ_le_succ_sqrt
  given: (n : Nat)
  statement: n + 1 <= (sqrt n + 1) * (sqrt n + 1)
  proof: le_of_pred_lt (lt_succ_sqrt _)

中文:
引理 succ_le_succ_sqrt
  条件: (n : 自然数)
  结论: n + 1 <= (sqrt n + 1) * (sqrt n + 1)
  证明: le_of_pred_lt (lt_succ_sqrt _)

Depends on / 依赖: differentialFiniteDimensional, le_of_pred_lt, lt_succ_sqrt
-/
lemma succ_le_succ_sqrt (n : Nat) : n + 1 <= (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt _)

/--
lemma `succ_le_succ_sqrt'` / 引理 `succ_le_succ_sqrt'`

English:
lemma succ_le_succ_sqrt'
  given: (n : Nat)
  statement: n + 1 <= (sqrt n + 1) ^ 2
  proof: le_of_pred_lt (lt_succ_sqrt' _)

中文:
引理 succ_le_succ_sqrt'
  条件: (n : 自然数)
  结论: n + 1 <= (sqrt n + 1) ^ 2
  证明: le_of_pred_lt (lt_succ_sqrt' _)

Depends on / 依赖: differentialAlgebraFiniteDimensional, le_of_pred_lt, lt_succ_sqrt
-/
lemma succ_le_succ_sqrt' (n : Nat) : n + 1 <= (sqrt n + 1) ^ 2 :=
  le_of_pred_lt (lt_succ_sqrt' _)

/--
lemma `not_exists_sq` / 引理 `not_exists_sq`

English:
lemma not_exists_sq
  given: (hl : m * m < n) (hr : n < (m + 1) * (m + 1))
  statement: ¬exists t, t * t = n
  proof: by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.1 hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.1 hr
  grind

中文:
引理 not_exists_sq
  条件: (hl : m * m < n) (hr : n < (m + 1) * (m + 1))
  结论: ¬存在 t, t * t = n
  证明: by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.1 hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.1 hr
  grind

Depends on / 依赖: Nat.mul_self_lt_mul_self_iff, mul_self_lt_mul_self_iff
-/
lemma not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬exists t, t * t = n := by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.1 hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.1 hr
  grind

/--
lemma `not_exists_sq'` / 引理 `not_exists_sq'`

English:
lemma not_exists_sq'
  statement: m ^ 2 < n -> n < (m + 1) ^ 2 -> ¬exists t, t ^ 2 = n
  proof: by
  simpa only [Nat.pow_two] using not_exists_sq

中文:
引理 not_exists_sq'
  结论: m ^ 2 < n -> n < (m + 1) ^ 2 -> ¬存在 t, t ^ 2 = n
  证明: by
  simpa only [Nat.pow_two] using not_exists_sq

Depends on / 依赖: Nat.pow_two, not_exists_sq, pow_two
-/
lemma not_exists_sq' : m ^ 2 < n -> n < (m + 1) ^ 2 -> ¬exists t, t ^ 2 = n := by
  simpa only [Nat.pow_two] using not_exists_sq

/--
lemma `le_sqrt_of_eq_mul` / 引理 `le_sqrt_of_eq_mul`

English:
lemma le_sqrt_of_eq_mul
  given: {a b c : Nat} (h : a = b * c)
  statement: b <= a.sqrt ∨ c <= a.sqrt
  proof: by
  rcases le_total b c with bc | cb
· exact Or.inl le_sqrt.mpr h ▸ mul_le_mul_left b bc
· exact Or.inr le_sqrt.mpr h ▸ mul_le_mul_right c cb

中文:
引理 le_sqrt_of_eq_mul
  条件: {a b c : 自然数} (h : a = b * c)
  结论: b <= a.sqrt ∨ c <= a.sqrt
  证明: by
  rcases le_total b c with bc | cb
· exact Or.inl le_sqrt.mpr h ▸ mul_le_mul_left b bc
· exact Or.inr le_sqrt.mpr h ▸ mul_le_mul_right c cb

Depends on / 依赖: Or.inl, Or.inr, le_sqrt, le_sqrt.mpr, le_total, mul_le_mul_left, mul_le_mul_right
-/
lemma le_sqrt_of_eq_mul {a b c : Nat} (h : a = b * c) : b <= a.sqrt ∨ c <= a.sqrt := by
  rcases le_total b c with bc | cb
· exact Or.inl le_sqrt.mpr h ▸ mul_le_mul_left b bc
· exact Or.inr le_sqrt.mpr h ▸ mul_le_mul_right c cb

end Nat
