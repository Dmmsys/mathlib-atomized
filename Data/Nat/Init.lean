/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.Nat.Lemmas
public import Batteries.Util.LibraryNote
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

See note [foundational algebra order theory].
-/

@[expose] public section

library_note «foundational algebra order theory» /--
Batteries has a home-baked development of the algebraic and order-theoretic theory of `ℕ` and `ℤ`
which, in particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness
libraries in mathlib (naturals and integers show up as indices/offsets in lists, cardinality in
finsets, powers in groups, ...).

Less basic uses of `ℕ` and `ℤ` should however use the typeclass-mediated development.

The relevant files are:
* `Mathlib/Data/Nat/Basic.lean` for the continuation of the home-baked development on `ℕ`
* `Mathlib/Data/Int/Init.lean` for the continuation of the home-baked development on `ℤ`
* `Mathlib/Algebra/Group/Nat/Defs.lean` for the monoid instances on `ℕ`
* `Mathlib/Algebra/Group/Int/Defs.lean` for the group instance on `ℤ`
* `Mathlib/Algebra/Ring/Nat.lean` for the semiring instance on `ℕ`
* `Mathlib/Algebra/Ring/Int/Defs.lean` for the ring instance on `ℤ`
* `Mathlib/Algebra/Order/Group/Nat.lean` for the ordered monoid instance on `ℕ`
* `Mathlib/Algebra/Order/Group/Int.lean` for the ordered group instance on `ℤ`
* `Mathlib/Algebra/Order/Ring/Nat.lean` for the ordered semiring instance on `ℕ`
* `Mathlib/Algebra/Order/Ring/Int.lean` for the ordered ring instance on `ℤ`
-/

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d e m n k : Nat} {p : Nat -> Prop}


/--
lemma `succ_pos'` / 引理 `succ_pos'`

English:
lemma succ_pos'
  statement: 0 < succ n
  proof: succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff

中文:
引理 succ_pos'
  结论: 0 < succ n
  证明: succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff

Depends on / 依赖: succ_pos
-/
lemma succ_pos' : 0 < succ n := succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff

/--
lemma `two_lt_of_ne` / 引理 `two_lt_of_ne`

English:
lemma two_lt_of_ne
  statement: forall {n}, n != 0 -> n != 1 -> n != 2 -> 2 < n

中文:
引理 two_lt_of_ne
  结论: 对任意 {n}, n != 0 -> n != 1 -> n != 2 -> 2 < n
-/
lemma two_lt_of_ne : forall {n}, n != 0 -> n != 1 -> n != 2 -> 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  | n + 3, _, _, _ => le_add_left 3 n

/--
lemma `two_le_iff` / 引理 `two_le_iff`

English:
lemma two_le_iff
  statement: forall n, 2 <= n ↔ n != 0 ∧ n != 1

中文:
引理 two_le_iff
  结论: 对任意 n, 2 <= n ↔ n != 0 ∧ n != 1
-/
lemma two_le_iff : forall n, 2 <= n ↔ n != 0 ∧ n != 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp

/-! ### `add` -/

/-! ### `sub` -/


/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  statement: Nat.mul m n = m * n
  proof: mul_eq

中文:
引理 mul_def
  结论: 自然数.mul m n = m * n
  证明: mul_eq

Depends on / 依赖: mul_eq
-/
lemma mul_def : Nat.mul m n = m * n := mul_eq

/--
lemma `two_mul_ne_two_mul_add_one` / 引理 `two_mul_ne_two_mul_add_one`

English:
lemma two_mul_ne_two_mul_add_one
  statement: 2 * n != 2 * m + 1
  proof: mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

中文:
引理 two_mul_ne_two_mul_add_one
  结论: 2 * n != 2 * m + 1
  证明: mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

Depends on / 依赖: Nat.add_comm, add_comm, add_mul_mod_self_left, mod_eq_of_lt, mul_mod_right
-/
lemma two_mul_ne_two_mul_add_one : 2 * n != 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)


/--
lemma `le_div_two_iff_mul_two_le` / 引理 `le_div_two_iff_mul_two_le`

English:
lemma le_div_two_iff_mul_two_le
  given: {n m : Nat}
  statement: m <= n / 2 ↔ (m : Int) * 2 <= n
  proof: by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two]; rw [← Int.ofNat_le]; rw [Int.natCast_mul]; rw [Int.ofNat_two]

中文:
引理 le_div_two_iff_mul_two_le
  条件: {n m : 自然数}
  结论: m <= n / 2 ↔ (m : 整数) * 2 <= n
  证明: by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two]; rw [← Int.ofNat_le]; rw [Int.natCast_mul]; rw [Int.ofNat_two]

Depends on / 依赖: Int.natCast_mul, Int.ofNat_le, Int.ofNat_two, Nat.le_div_iff_mul_le, Nat.zero_lt_two, le_div_iff_mul_le, natCast_mul, ofNat_le, ofNat_two, zero_lt_two
-/
lemma le_div_two_iff_mul_two_le {n m : Nat} : m <= n / 2 ↔ (m : Int) * 2 <= n := by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two]; rw [← Int.ofNat_le]; rw [Int.natCast_mul]; rw [Int.ofNat_two]

/--
lemma `div_lt_self'` / 引理 `div_lt_self'`

English:
lemma div_lt_self'
  given: (a b : Nat)
  statement: (a + 1) / (b + 2) < a + 1
  proof: Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

中文:
引理 div_lt_self'
  条件: (a b : 自然数)
  结论: (a + 1) / (b + 2) < a + 1
  证明: Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

Depends on / 依赖: Nat.div_lt_self, Nat.succ_lt_succ, Nat.succ_pos, div_lt_self, succ_lt_succ, succ_pos
-/
lemma div_lt_self' (a b : Nat) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

/--
lemma `two_mul_odd_div_two` / 引理 `two_mul_odd_div_two`

English:
lemma two_mul_odd_div_two
  given: (hn : n % 2 = 1)
  statement: 2 * (n / 2) = n - 1
  proof: by
  lia

中文:
引理 two_mul_odd_div_two
  条件: (hn : n % 2 = 1)
  结论: 2 * (n / 2) = n - 1
  证明: by
  lia
-/
lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  lia


/--
lemma `one_le_pow'` / 引理 `one_le_pow'`

English:
lemma one_le_pow'
  given: (n m : Nat)
  statement: 1 <= (m + 1) ^ n
  proof: one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

中文:
引理 one_le_pow'
  条件: (n m : 自然数)
  结论: 1 <= (m + 1) ^ n
  证明: one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

Depends on / 依赖: one_le_pow, succ_pos
-/
lemma one_le_pow' (n m : Nat) : 1 <= (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp]
/--
lemma `rec_zero` / 引理 `rec_zero`

English:
lemma rec_zero
  given: {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1))
  statement: Nat.rec h0 h 0 = h0
  proof: rfl

中文:
引理 rec_zero
  条件: {C : 自然数 -> 类型层*} (h0 : C 0) (h : 对任意 n, C n -> C (n + 1))
  结论: 自然数.rec h0 h 0 = h0
  证明: rfl
-/
lemma rec_zero {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1)) : Nat.rec h0 h 0 = h0 := rfl

-- Not `@[simp]` since `simp` can reduce the whole term.
/--
lemma `rec_add_one` / 引理 `rec_add_one`

English:
lemma rec_add_one
  given: {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1)) (n : Nat)
  proof: rfl

中文:
引理 rec_add_one
  条件: {C : 自然数 -> 类型层*} (h0 : C 0) (h : 对任意 n, C n -> C (n + 1)) (n : 自然数)
  证明: rfl
-/
lemma rec_add_one {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1)) (n : Nat) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl

/--
lemma `rec_one` / 引理 `rec_one`

English:
lemma rec_one
  given: {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1))
  proof: rfl

中文:
引理 rec_one
  条件: {C : 自然数 -> 类型层*} (h0 : C 0) (h : 对任意 n, C n -> C (n + 1))
  证明: rfl
-/
@[simp] lemma rec_one {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1)) :
    Nat.rec (motive := C) h0 h 1 = h 0 h0 := rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`.

This is a version of `Nat.le.rec` that works for `Sort u`.
Similarly to `Nat.le.rec`, it can be used as
```
induction hle using Nat.leRec with
| refl => sorry
| le_succ_of_le hle ih => sorry
```
-/
@[elab_as_elim]
/--
Definition of `leRec` / `leRec` 的定义

English:
definition leRec
  signature: {n} {motive : (m : Nat) -> n <= m -> Sort*}

中文:
定义 leRec
  签名: {n} {motive : (m : 自然数) -> n <= m -> 类型层*}
-/
def leRec {n} {motive : (m : Nat) -> n <= m -> Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motive k h -> motive (k + 1) (le_succ_of_le h)) :
    forall {m} (h : n <= m), motive m h
  | 0, H => Nat.eq_zero_of_le_zero H ▸ refl
  | m + 1, H =>
    (le_succ_iff.1 H).by_cases
      (fun h : n <= m => le_succ_of_le h <| leRec refl le_succ_of_le h)
      (fun h : n = m + 1 => h ▸ refl)

-- This verifies the signatures of the recursor matches the builtin one, as promised in the
-- above.
/--
theorem `leRec_eq_leRec` / 定理 `leRec_eq_leRec`

English:
theorem leRec_eq_leRec
  statement: @Nat.leRec.{0} = @Nat.le.rec
  proof: rfl

@[simp]

中文:
定理 leRec_eq_leRec
  结论: @自然数.leRec.{0} = @自然数.le.rec
  证明: rfl

@[simp]
-/
theorem leRec_eq_leRec : @Nat.leRec.{0} = @Nat.le.rec := rfl

@[simp]
/--
lemma `leRec_self` / 引理 `leRec_self`

English:
lemma leRec_self
  statement: {n} {motive : (m : Nat) -> n <= m -> Sort*}
  proof: by
  cases n <;> simp [leRec, Or.by_cases, dif_neg]

@[simp]

中文:
引理 leRec_self
  结论: {n} {motive : (m : 自然数) -> n <= m -> 类型层*}
  证明: by
  cases n <;> simp [leRec, Or.by_cases, dif_neg]

@[simp]

Depends on / 依赖: Nat.le_refl, le_refl, le_succ_of_le, motive
-/
lemma leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motive k h -> motive (k + 1) (le_succ_of_le h)) :
    (leRec (motive := motive) refl le_succ_of_le (Nat.le_refl _) :
    motive n (Nat.le_refl _)) = refl := by
  cases n <;> simp [leRec, Or.by_cases, dif_neg]

@[simp]
/--
lemma `leRec_succ` / 引理 `leRec_succ`

English:
lemma leRec_succ
  statement: {n} {motive : (m : Nat) -> n <= m -> Sort*}
  proof: by
  conv =>
    lhs
    rw [leRec]; rw [Or.by_cases]; rw [dif_pos h1]

中文:
引理 leRec_succ
  结论: {n} {motive : (m : 自然数) -> n <= m -> 类型层*}
  证明: by
  conv =>
    lhs
    rw [leRec]; rw [Or.by_cases]; rw [dif_pos h1]

Depends on / 依赖: le_succ_of_le, motive
-/
lemma leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motive k h -> motive (k + 1) (le_succ_of_le h))
    (h1 : n <= m) {h2 : n <= m + 1} :
    (leRec (motive := motive) refl le_succ_of_le h2) =
      le_succ_of_le h1 (leRec (motive := motive) refl le_succ_of_le h1) := by
  conv =>
    lhs
    rw [leRec]; rw [Or.by_cases]; rw [dif_pos h1]

/--
lemma `leRec_succ'` / 引理 `leRec_succ'`

English:
lemma leRec_succ'
  given: {n} {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_of_le)
  proof: by
  rw [leRec_succ]; rw [leRec_self]

中文:
引理 leRec_succ'
  条件: {n} {motive : (m : 自然数) -> n <= m -> 类型层*} (refl le_succ_of_le)
  证明: by
  rw [leRec_succ]; rw [leRec_self]

Depends on / 依赖: leRec_self, leRec_succ, le_succ, le_succ_of_le, motive
-/
lemma leRec_succ' {n} {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_of_le) :
    (leRec (motive := motive) refl le_succ_of_le (le_succ _)) = le_succ_of_le _ refl := by
  rw [leRec_succ]; rw [leRec_self]

/--
lemma `leRec_trans` / 引理 `leRec_trans`

English:
lemma leRec_trans
  statement: {n m k} {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_of_le)
  proof: by
  induction hmk with
  | refl => rw [leRec_self]
  | step hmk ih => rw [leRec_succ _ _ (Nat.le_trans hnm hmk), ih, leRec_succ]

中文:
引理 leRec_trans
  结论: {n m k} {motive : (m : 自然数) -> n <= m -> 类型层*} (refl le_succ_of_le)
  证明: by
  induction hmk with
  | refl => rw [leRec_self]
  | step hmk ih => rw [leRec_succ _ _ (Nat.le_trans hnm hmk), ih, leRec_succ]

Depends on / 依赖: Nat.le_trans, le_succ_of_le, le_trans, motive
-/
lemma leRec_trans {n m k} {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_of_le)
    (hnm : n <= m) (hmk : m <= k) :
    leRec (motive := motive) refl le_succ_of_le (Nat.le_trans hnm hmk) =
      leRec
        (leRec refl (fun _ h => le_succ_of_le h) hnm)
        (fun _ h => le_succ_of_le <| Nat.le_trans hnm h) hmk := by
  induction hmk with
  | refl => rw [leRec_self]
  | step hmk ih => rw [leRec_succ _ _ (Nat.le_trans hnm hmk), ih, leRec_succ]

/--
lemma `leRec_succ_left` / 引理 `leRec_succ_left`

English:
lemma leRec_succ_left
  statement: {motive : (m : Nat) -> n <= m -> Sort*}
  proof: by
  rw [leRec_trans _ _ (le_succ n) h2]; rw [leRec_succ']

中文:
引理 leRec_succ_left
  结论: {motive : (m : 自然数) -> n <= m -> 类型层*}
  证明: by
  rw [leRec_trans _ _ (le_succ n) h2]; rw [leRec_succ']

Depends on / 依赖: leRec_succ, leRec_trans, le_succ, le_succ_of_le, motive
-/
lemma leRec_succ_left {motive : (m : Nat) -> n <= m -> Sort*}
    (refl le_succ_of_le) {m} (h1 : n <= m) (h2 : n + 1 <= m) :
    -- the `@` is needed for this to elaborate, even though we only provide explicit arguments!
    @leRec _ _ (le_succ_of_le (Nat.le_refl _) refl)
        (fun _ h ih => le_succ_of_le (le_of_succ_le h) ih) _ h2 =
      leRec (motive := motive) refl le_succ_of_le h1 := by
  rw [leRec_trans _ _ (le_succ n) h2]; rw [leRec_succ']

/-- Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `Nat.leRec`. -/
@[elab_as_elim]
/--
Definition of `leRecOn` / `leRecOn` 的定义

English:
definition leRecOn
  signature: {C : Nat -> Sort*} {n : Nat}
  body: fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h

中文:
定义 leRecOn
  签名: {C : 自然数 -> 类型层*} {n : 自然数}
  定义体: fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h

Depends on / 依赖: Nat.leRec, of_succ
-/
def leRecOn {C : Nat -> Sort*} {n : Nat} : forall {m}, n <= m -> (forall {k}, C k -> C (k + 1)) -> C n -> C m :=
  fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h

/--
lemma `leRecOn_self` / 引理 `leRecOn_self`

English:
lemma leRecOn_self
  given: {C : Nat -> Sort*} {n} {next : forall {k}, C k -> C (k + 1)} (x : C n)
  proof: leRec_self _ _

中文:
引理 leRecOn_self
  条件: {C : 自然数 -> 类型层*} {n} {next : 对任意 {k}, C k -> C (k + 1)} (x : C n)
  证明: leRec_self _ _

Depends on / 依赖: leRec_self
-/
lemma leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}, C k -> C (k + 1)} (x : C n) :
    (leRecOn n.le_refl next x : C n) = x :=
  leRec_self _ _

/--
lemma `leRecOn_succ` / 引理 `leRecOn_succ`

English:
lemma leRecOn_succ
  given: {C : Nat -> Sort*} {n m} (h1 : n <= m) {h2 : n <= m + 1} {next} (x : C n)
  proof: leRec_succ _ _ _

中文:
引理 leRecOn_succ
  条件: {C : 自然数 -> 类型层*} {n m} (h1 : n <= m) {h2 : n <= m + 1} {next} (x : C n)
  证明: leRec_succ _ _ _

Depends on / 依赖: leRec_succ
-/
lemma leRecOn_succ {C : Nat -> Sort*} {n m} (h1 : n <= m) {h2 : n <= m + 1} {next} (x : C n) :
    (leRecOn h2 next x : C (m + 1)) = next (leRecOn h1 next x : C m) :=
  leRec_succ _ _ _

/--
lemma `leRecOn_succ'` / 引理 `leRecOn_succ'`

English:
lemma leRecOn_succ'
  given: {C : Nat -> Sort*} {n} {h : n <= n + 1} {next : forall {k}, C k -> C (k + 1)} (x : C n)
  proof: leRec_succ' _ _

中文:
引理 leRecOn_succ'
  条件: {C : 自然数 -> 类型层*} {n} {h : n <= n + 1} {next : 对任意 {k}, C k -> C (k + 1)} (x : C n)
  证明: leRec_succ' _ _

Depends on / 依赖: leRec_succ
-/
lemma leRecOn_succ' {C : Nat -> Sort*} {n} {h : n <= n + 1} {next : forall {k}, C k -> C (k + 1)} (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x :=
  leRec_succ' _ _

/--
lemma `leRecOn_trans` / 引理 `leRecOn_trans`

English:
lemma leRecOn_trans
  given: {C : Nat -> Sort*} {n m k} (hnm : n <= m) (hmk : m <= k) {next} (x : C n)
  proof: leRec_trans _ _ _ _

中文:
引理 leRecOn_trans
  条件: {C : 自然数 -> 类型层*} {n m k} (hnm : n <= m) (hmk : m <= k) {next} (x : C n)
  证明: leRec_trans _ _ _ _

Depends on / 依赖: leRec_trans
-/
lemma leRecOn_trans {C : Nat -> Sort*} {n m k} (hnm : n <= m) (hmk : m <= k) {next} (x : C n) :
    (leRecOn (Nat.le_trans hnm hmk) (@next) x : C k) =
      leRecOn hmk (@next) (leRecOn hnm (@next) x) :=
  leRec_trans _ _ _ _

/--
lemma `leRecOn_succ_left` / 引理 `leRecOn_succ_left`

English:
lemma leRecOn_succ_left
  statement: {C : Nat -> Sort*} {n m}
  proof: leRec_succ_left (motive := fun n _ => C n) _ (fun _ _ => @next _) _ _

@[deprecated (since := "2026-03-05")] alias strongRec' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRec'_spec := Nat.strongRec_eq
@[deprecated (since := "2026-03-05")] alias strongRecOn' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRecOn'_beta := Nat.strongRec_eq

中文:
引理 leRecOn_succ_left
  结论: {C : 自然数 -> 类型层*} {n m}
  证明: leRec_succ_left (motive := fun n _ => C n) _ (fun _ _ => @next _) _ _

@[deprecated (since := "2026-03-05")] alias strongRec' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRec'_spec := Nat.strongRec_eq
@[deprecated (since := "2026-03-05")] alias strongRecOn' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRecOn'_beta := Nat.strongRec_eq

Depends on / 依赖: leRec_succ_left, motive
-/
lemma leRecOn_succ_left {C : Nat -> Sort*} {n m}
    {next : forall {k}, C k -> C (k + 1)} (x : C n) (h1 : n <= m) (h2 : n + 1 <= m) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) :=
  leRec_succ_left (motive := fun n _ => C n) _ (fun _ _ => @next _) _ _

@[deprecated (since := "2026-03-05")] alias strongRec' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRec'_spec := Nat.strongRec_eq
@[deprecated (since := "2026-03-05")] alias strongRecOn' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRecOn'_beta := Nat.strongRec_eq

/-- Induction principle starting at a non-zero number.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`).

This is an alias of `Nat.leRec`, specialized to `Prop`. -/
@[elab_as_elim]
/--
lemma `le_induction` / 引理 `le_induction`

English:
lemma le_induction
  statement: {m : Nat} {P : forall n, m <= n -> Prop} (base : P m m.le_refl)
  proof: @Nat.leRec (motive := P) _ base succ

中文:
引理 le_induction
  结论: {m : 自然数} {P : 对任意 n, m <= n -> 命题} (base : P m m.le_refl)
  证明: @Nat.leRec (motive := P) _ base succ

Depends on / 依赖: Nat.leRec, motive
-/
lemma le_induction {m : Nat} {P : forall n, m <= n -> Prop} (base : P m m.le_refl)
    (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le hmn)) : forall n hmn, P n hmn :=
  @Nat.leRec (motive := P) _ base succ

/-- Induction principle deriving the next case from the two previous ones. -/
@[elab_as_elim]
/--
Definition of `twoStepInduction` / `twoStepInduction` 的定义

English:
definition twoStepInduction
  signature: {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1)

中文:
定义 twoStepInduction
  签名: {motive : 自然数 -> 类型层*} (zero : motive 0) (one : motive 1)
-/
def twoStepInduction {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1)
    (more : forall n, motive n -> motive (n + 1) -> motive (n + 2)) : forall a, motive a
  | 0 => zero
  | 1 => one
  | _ + 2 => more _ (twoStepInduction zero one more _) (twoStepInduction zero one more _)

/-- Induction principle deriving the next case from the `k` previous ones. Use as
```
induction n using stepInduction 3 with
| base n hn => ...
| step n ih => ...
``` -/
@[elab_as_elim]
/--
Definition of `stepInduction` / `stepInduction` 的定义

English:
definition stepInduction
  signature: {motive : Nat -> Sort*} (k : Nat) (base : forall i < k, motive i)
  body: if h : a < k then base _ h else
  (show a - k + k = a by lia) ▸ step (a - k) fun _ _ => stepInduction k base step _

@[elab_as_elim]

中文:
定义 stepInduction
  签名: {motive : 自然数 -> 类型层*} (k : 自然数) (base : 对任意 i < k, motive i)
  定义体: if h : a < k then base _ h else
  (show a - k + k = a by lia) ▸ step (a - k) fun _ _ => stepInduction k base step _

@[elab_as_elim]

Depends on / 依赖: stepInduction
-/
def stepInduction {motive : Nat -> Sort*} (k : Nat) (base : forall i < k, motive i)
    (step : forall n, (forall i < k, motive (n + i)) -> motive (n + k)) (a : Nat) : motive a :=
  if h : a < k then base _ h else
  (show a - k + k = a by lia) ▸ step (a - k) fun _ _ => stepInduction k base step _

@[elab_as_elim]
/--
theorem `strong_induction_on` / 定理 `strong_induction_on`

English:
theorem strong_induction_on
  statement: {p : Nat -> Prop} (n : Nat)
  proof: Nat.strongRecOn n h

中文:
定理 strong_induction_on
  结论: {p : 自然数 -> 命题} (n : 自然数)
  证明: Nat.strongRecOn n h
-/
protected theorem strong_induction_on {p : Nat -> Prop} (n : Nat)
    (h : forall n, (forall m < n, p m) -> p n) : p n :=
  Nat.strongRecOn n h

/--
theorem `case_strong_induction_on` / 定理 `case_strong_induction_on`

English:
theorem case_strong_induction_on
  statement: {p : Nat -> Prop} (a : Nat) (hz : p 0)
  proof: Nat.caseStrongRecOn a hz hi

中文:
定理 case_strong_induction_on
  结论: {p : 自然数 -> 命题} (a : 自然数) (hz : p 0)
  证明: Nat.caseStrongRecOn a hz hi
-/
protected theorem case_strong_induction_on {p : Nat -> Prop} (a : Nat) (hz : p 0)
    (hi : forall n, (forall m <= n, p m) -> p (n + 1)) : p a :=
  Nat.caseStrongRecOn a hz hi

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `k < n`, then `P n` implies `P m` for
all `m ≤ n`.
Also works for functions to `Sort*`.

For a version also assuming `m ≤ k`, see `Nat.decreasingInduction'`. -/
@[elab_as_elim]
/--
Definition of `decreasingInduction` / `decreasingInduction` 的定义

English:
definition decreasingInduction
  signature: {n} {motive : (m : Nat) -> m <= n -> Sort*}
  body: by
  induction mn using leRec with
  | refl => exact self
  | @le_succ_of_le k _ ih =>
    apply ih (fun i hi => of_succ i (le_succ_of_le hi)) (of_succ k (lt_succ_self _) self)

@[simp]

中文:
定义 decreasingInduction
  签名: {n} {motive : (m : 自然数) -> m <= n -> 类型层*}
  定义体: by
  induction mn using leRec with
  | refl => exact self
  | @le_succ_of_le k _ ih =>
    apply ih (fun i hi => of_succ i (le_succ_of_le hi)) (of_succ k (lt_succ_self _) self)

@[simp]

Depends on / 依赖: le_succ_of_le, lt_succ_self, of_succ
-/
def decreasingInduction {n} {motive : (m : Nat) -> m <= n -> Sort*}
    (of_succ : forall k (h : k < n), motive (k + 1) h -> motive k (le_of_succ_le h))
    (self : motive n (Nat.le_refl _)) {m} (mn : m <= n) : motive m mn := by
  induction mn using leRec with
  | refl => exact self
  | @le_succ_of_le k _ ih =>
    apply ih (fun i hi => of_succ i (le_succ_of_le hi)) (of_succ k (lt_succ_self _) self)

@[simp]
/--
lemma `decreasingInduction_self` / 引理 `decreasingInduction_self`

English:
lemma decreasingInduction_self
  given: {n} {motive : (m : Nat) -> m <= n -> Sort*} (of_succ self)
  proof: by
  dsimp only [decreasingInduction]
  rw [leRec_self]

中文:
引理 decreasingInduction_self
  条件: {n} {motive : (m : 自然数) -> m <= n -> 类型层*} (of_succ self)
  证明: by
  dsimp only [decreasingInduction]
  rw [leRec_self]

Depends on / 依赖: Nat.le_refl, decreasingInduction, leRec_self, le_refl, motive, of_succ
-/
lemma decreasingInduction_self {n} {motive : (m : Nat) -> m <= n -> Sort*} (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_refl _)) = self := by
  dsimp only [decreasingInduction]
  rw [leRec_self]

/--
lemma `decreasingInduction_succ` / 引理 `decreasingInduction_succ`

English:
lemma decreasingInduction_succ
  statement: {n} {motive : (m : Nat) -> m <= n + 1 -> Sort*} (of_succ self)
  proof: by
  dsimp only [decreasingInduction]; rw [leRec_succ]

@[simp]

中文:
引理 decreasingInduction_succ
  结论: {n} {motive : (m : 自然数) -> m <= n + 1 -> 类型层*} (of_succ self)
  证明: by
  dsimp only [decreasingInduction]; rw [leRec_succ]

@[simp]

Depends on / 依赖: motive, of_succ
-/
lemma decreasingInduction_succ {n} {motive : (m : Nat) -> m <= n + 1 -> Sort*} (of_succ self)
    (mn : m <= n) (msn : m <= n + 1) :
    (decreasingInduction (motive := motive) of_succ self msn : motive m msn) =
      decreasingInduction (motive := fun m h => motive m (le_succ_of_le h))
        (fun _ _ => of_succ _ _) (of_succ _ _ self) mn := by
  dsimp only [decreasingInduction]; rw [leRec_succ]

@[simp]
/--
lemma `decreasingInduction_succ'` / 引理 `decreasingInduction_succ'`

English:
lemma decreasingInduction_succ'
  given: {n} {motive : (m : Nat) -> m <= n + 1 -> Sort*} (of_succ self)
  proof: by
  dsimp only [decreasingInduction]; rw [leRec_succ']

中文:
引理 decreasingInduction_succ'
  条件: {n} {motive : (m : 自然数) -> m <= n + 1 -> 类型层*} (of_succ self)
  证明: by
  dsimp only [decreasingInduction]; rw [leRec_succ']

Depends on / 依赖: decreasingInduction, leRec_succ, le_succ, motive, n.le_succ, of_succ
-/
lemma decreasingInduction_succ' {n} {motive : (m : Nat) -> m <= n + 1 -> Sort*} (of_succ self) :
    decreasingInduction (motive := motive) of_succ self n.le_succ = of_succ _ _ self := by
  dsimp only [decreasingInduction]; rw [leRec_succ']

/--
lemma `decreasingInduction_trans` / 引理 `decreasingInduction_trans`

English:
lemma decreasingInduction_trans
  statement: {motive : (m : Nat) -> m <= k -> Sort*} (hmn : m <= n) (hnk : n <= k)
  proof: by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ _ _ (Nat.le_trans hmn hnk)]; rw [ih]; rw [decreasingInduction_succ]

中文:
引理 decreasingInduction_trans
  结论: {motive : (m : 自然数) -> m <= k -> 类型层*} (hmn : m <= n) (hnk : n <= k)
  证明: by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ _ _ (Nat.le_trans hmn hnk)]; rw [ih]; rw [decreasingInduction_succ]

Depends on / 依赖: Nat.le_trans, le_trans, motive, of_succ
-/
lemma decreasingInduction_trans {motive : (m : Nat) -> m <= k -> Sort*} (hmn : m <= n) (hnk : n <= k)
    (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_trans hmn hnk) : motive m _) =
    decreasingInduction (fun _ _ => of_succ _ _) (decreasingInduction of_succ self hnk) hmn := by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ _ _ (Nat.le_trans hmn hnk)]; rw [ih]; rw [decreasingInduction_succ]

/--
lemma `decreasingInduction_succ_left` / 引理 `decreasingInduction_succ_left`

English:
lemma decreasingInduction_succ_left
  statement: {motive : (m : Nat) -> m <= n -> Sort*} (of_succ self)
  proof: by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn)]; rw [decreasingInduction_trans (n := m + 1) (Nat.le_succ m)]; rw [decreasingInduction_succ']

中文:
引理 decreasingInduction_succ_left
  结论: {motive : (m : 自然数) -> m <= n -> 类型层*} (of_succ self)
  证明: by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn)]; rw [decreasingInduction_trans (n := m + 1) (Nat.le_succ m)]; rw [decreasingInduction_succ']

Depends on / 依赖: motive, of_succ
-/
lemma decreasingInduction_succ_left {motive : (m : Nat) -> m <= n -> Sort*} (of_succ self)
    (smn : m + 1 <= n) (mn : m <= n) :
    decreasingInduction (motive := motive) of_succ self mn =
      of_succ m smn (decreasingInduction of_succ self smn) := by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn)]; rw [decreasingInduction_trans (n := m + 1) (Nat.le_succ m)]; rw [decreasingInduction_succ']

/-- Given `P : ℕ → ℕ → Sort*`, if for all `m n : ℕ` we can extend `P` from the rectangle
strictly below `(m, n)` to `P m n`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
/--
Definition of `strongSubRecursion` / `strongSubRecursion` 的定义

English:
definition strongSubRecursion
  signature: {P : Nat -> Nat -> Sort*} (H : forall m n, (forall x y, x < m -> y < n -> P x y) -> P m n)

中文:
定义 strongSubRecursion
  签名: {P : 自然数 -> 自然数 -> 类型层*} (H : 对任意 m n, (对任意 x y, x < m -> y < n -> P x y) -> P m n)
-/
def strongSubRecursion {P : Nat -> Nat -> Sort*} (H : forall m n, (forall x y, x < m -> y < n -> P x y) -> P m n) :
    forall n m : Nat, P n m
  | n, m => H n m fun x y _ _ => strongSubRecursion H x y

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P m 0` and `P 0 n` for all `m n : ℕ`, and for any
`m n : ℕ` we can extend `P` from `(m, n + 1)` and `(m + 1, n)` to `(m + 1, n + 1)` then we have
`P m n` for all `m n : ℕ`.

Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
/--
Definition of `pincerRecursion` / `pincerRecursion` 的定义

English:
definition pincerRecursion
  signature: {P : Nat -> Nat -> Sort*} (Ha0 : forall m : Nat, P m 0) (H0b : forall n : Nat, P 0 n)

中文:
定义 pincerRecursion
  签名: {P : 自然数 -> 自然数 -> 类型层*} (Ha0 : 对任意 m : 自然数, P m 0) (H0b : 对任意 n : 自然数, P 0 n)
-/
def pincerRecursion {P : Nat -> Nat -> Sort*} (Ha0 : forall m : Nat, P m 0) (H0b : forall n : Nat, P 0 n)
    (H : forall x y : Nat, P x y.succ -> P x.succ y -> P x.succ y.succ) : forall n m : Nat, P n m
  | m, 0 => Ha0 m
  | 0, n => H0b n
  | Nat.succ _, Nat.succ _ => H _ _ (pincerRecursion Ha0 H0b H _ _) (pincerRecursion Ha0 H0b H _ _)

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`.

Weakens the assumptions of `Nat.decreasingInduction`. -/
@[elab_as_elim]
/--
Definition of `decreasingInduction'` / `decreasingInduction'` 的定义

English:
definition decreasingInduction'
  signature: {P : Nat -> Sort*} (h : forall k < n, m <= k -> P (k + 1) -> P k)
  body: by
  induction mn using decreasingInduction with
  | self => exact hP
  | of_succ k hk ih =>
    exact h _ (lt_of_succ_le hk) (Nat.le_refl _)
      (ih fun k' hk' h'' => h k' hk' <| le_of_succ_le h'')

中文:
定义 decreasingInduction'
  签名: {P : 自然数 -> 类型层*} (h : 对任意 k < n, m <= k -> P (k + 1) -> P k)
  定义体: by
  induction mn using decreasingInduction with
  | self => exact hP
  | of_succ k hk ih =>
    exact h _ (lt_of_succ_le hk) (Nat.le_refl _)
      (ih fun k' hk' h'' => h k' hk' <| le_of_succ_le h'')

Depends on / 依赖: Nat.le_refl, decreasingInduction, le_of_succ_le, le_refl, lt_of_succ_le, of_succ
-/
def decreasingInduction' {P : Nat -> Sort*} (h : forall k < n, m <= k -> P (k + 1) -> P k)
    (mn : m <= n) (hP : P n) : P m := by
  induction mn using decreasingInduction with
  | self => exact hP
  | of_succ k hk ih =>
    exact h _ (lt_of_succ_le hk) (Nat.le_refl _)
      (ih fun k' hk' h'' => h k' hk' <| le_of_succ_le h'')

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_elim]
/--
theorem `diag_induction` / 定理 `diag_induction`

English:
theorem diag_induction
  statement: (P : Nat -> Nat -> Prop) (ha : forall a, P (a + 1) (a + 1)) (hb : forall b, P 0 (b + 1))
  proof: by lia
      rcases this with (rfl | h)
      · exact ha _
      apply diag_induction P ha hb hd (a + 1) b h
    apply diag_induction P ha hb hd a (b + 1)
    apply Nat.lt_of_le_of_lt (Nat.le_succ _) h

中文:
定理 diag_induction
  结论: (P : 自然数 -> 自然数 -> 命题) (ha : 对任意 a, P (a + 1) (a + 1)) (hb : 对任意 b, P 0 (b + 1))
  证明: by lia
      rcases this with (rfl | h)
      · exact ha _
      apply diag_induction P ha hb hd (a + 1) b h
    apply diag_induction P ha hb hd a (b + 1)
    apply Nat.lt_of_le_of_lt (Nat.le_succ _) h

Depends on / 依赖: Nat.le_succ, Nat.lt_of_le_of_lt, diag_induction, le_succ, lt_of_le_of_lt
-/
theorem diag_induction (P : Nat -> Nat -> Prop) (ha : forall a, P (a + 1) (a + 1)) (hb : forall b, P 0 (b + 1))
    (hd : forall a b, a < b -> P (a + 1) b -> P a (b + 1) -> P (a + 1) (b + 1)) : forall a b, a < b -> P a b
  | 0, _ + 1, _ => hb _
  | a + 1, b + 1, h => by
    apply hd _ _ (Nat.add_lt_add_iff_right.1 h)
    · have : a + 1 = b ∨ a + 1 < b := by lia
      rcases this with (rfl | h)
      · exact ha _
      apply diag_induction P ha hb hd (a + 1) b h
    apply diag_induction P ha hb hd a (b + 1)
    apply Nat.lt_of_le_of_lt (Nat.le_succ _) h


/--
lemma `not_pos_pow_dvd` / 引理 `not_pos_pow_dvd`

English:
lemma not_pos_pow_dvd
  given: {a n : Nat} (ha : 1 < a) (hn : 1 < n)
  statement: ¬ a ^ n ∣ a
  proof: not_dvd_of_pos_of_lt (Nat.lt_trans Nat.zero_lt_one ha)
    (lt_of_eq_of_lt (Nat.pow_one a).symm ((Nat.pow_lt_pow_iff_right ha).2 hn))

@[simp]

中文:
引理 not_pos_pow_dvd
  条件: {a n : 自然数} (ha : 1 < a) (hn : 1 < n)
  结论: ¬ a ^ n ∣ a
  证明: not_dvd_of_pos_of_lt (Nat.lt_trans Nat.zero_lt_one ha)
    (lt_of_eq_of_lt (Nat.pow_one a).symm ((Nat.pow_lt_pow_iff_right ha).2 hn))

@[simp]

Depends on / 依赖: Nat.lt_trans, Nat.pow_lt_pow_iff_right, Nat.pow_one, Nat.zero_lt_one, lt_of_eq_of_lt, lt_trans, not_dvd_of_pos_of_lt, pow_lt_pow_iff_right, pow_one, zero_lt_one
-/
lemma not_pos_pow_dvd {a n : Nat} (ha : 1 < a) (hn : 1 < n) : ¬ a ^ n ∣ a :=
  not_dvd_of_pos_of_lt (Nat.lt_trans Nat.zero_lt_one ha)
    (lt_of_eq_of_lt (Nat.pow_one a).symm ((Nat.pow_lt_pow_iff_right ha).2 hn))

@[simp]
/--
theorem `not_two_dvd_bit1` / 定理 `not_two_dvd_bit1`

English:
theorem not_two_dvd_bit1
  given: (n : Nat)
  statement: ¬2 ∣ 2 * n + 1
  proof: by
  lia

中文:
定理 not_two_dvd_bit1
  条件: (n : 自然数)
  结论: ¬2 ∣ 2 * n + 1
  证明: by
  lia
-/
protected theorem not_two_dvd_bit1 (n : Nat) : ¬2 ∣ 2 * n + 1 := by
  lia

/--
lemma `dvd_add_self_left` / 引理 `dvd_add_self_left`

English:
lemma dvd_add_self_left
  statement: m ∣ m + n ↔ m ∣ n
  proof: Nat.dvd_add_right (Nat.dvd_refl m)

中文:
引理 dvd_add_self_left
  结论: m ∣ m + n ↔ m ∣ n
  证明: Nat.dvd_add_right (Nat.dvd_refl m)
-/
@[simp] protected lemma dvd_add_self_left : m ∣ m + n ↔ m ∣ n := Nat.dvd_add_right (Nat.dvd_refl m)

/--
lemma `dvd_add_self_right` / 引理 `dvd_add_self_right`

English:
lemma dvd_add_self_right
  statement: m ∣ n + m ↔ m ∣ n
  proof: Nat.dvd_add_left (Nat.dvd_refl m)

中文:
引理 dvd_add_self_right
  结论: m ∣ n + m ↔ m ∣ n
  证明: Nat.dvd_add_left (Nat.dvd_refl m)
-/
@[simp] protected lemma dvd_add_self_right : m ∣ n + m ↔ m ∣ n := Nat.dvd_add_left (Nat.dvd_refl m)

/--
lemma `dvd_right_iff_eq` / 引理 `dvd_right_iff_eq`

English:
lemma dvd_right_iff_eq
  statement: (forall a : Nat, m ∣ a ↔ n ∣ a) ↔ m = n
  proof: ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

中文:
引理 dvd_right_iff_eq
  结论: (对任意 a : 自然数, m ∣ a ↔ n ∣ a) ↔ m = n
  证明: ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

Depends on / 依赖: Nat.dvd_antisymm, Nat.dvd_refl, dvd_antisymm, dvd_refl
-/
lemma dvd_right_iff_eq : (forall a : Nat, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/--
lemma `dvd_left_iff_eq` / 引理 `dvd_left_iff_eq`

English:
lemma dvd_left_iff_eq
  statement: (forall a : Nat, a ∣ m ↔ a ∣ n) ↔ m = n
  proof: ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

中文:
引理 dvd_left_iff_eq
  结论: (对任意 a : 自然数, a ∣ m ↔ a ∣ n) ↔ m = n
  证明: ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

Depends on / 依赖: Nat.dvd_antisymm, Nat.dvd_refl, dvd_antisymm, dvd_refl
-/
lemma dvd_left_iff_eq : (forall a : Nat, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩


/--
Instance `decidableLoHi` / 实例 `decidableLoHi`

English:
instance decidableLoHi
  signature: (lo hi : Nat) (P : Nat -> Prop) [DecidablePred P]
  body: decidable_of_iff (forall x < hi - lo, P (lo + x)) by
    refine ⟨fun al x hl hh => ?_,
      fun al x h => al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this

中文:
实例 decidableLoHi
  签名: (lo hi : 自然数) (P : 自然数 -> 命题) [DecidablePred P]
  定义体: decidable_of_iff (forall x < hi - lo, P (lo + x)) by
    refine ⟨fun al x hl hh => ?_,
      fun al x h => al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this

Depends on / 依赖: Nat.add_sub_cancel, Nat.le_add_right, Nat.lt_sub_iff_add_lt, Nat.sub_lt_sub_iff_right, add_sub_cancel, decidable_of_iff, le_add_right, lt_sub_iff_add_lt, sub_lt_sub_iff_right
-/
instance decidableLoHi (lo hi : Nat) (P : Nat -> Prop) [DecidablePred P] :
    Decidable (forall x, lo <= x -> x < hi -> P x) :=
decidable_of_iff (forall x < hi - lo, P (lo + x)) by
    refine ⟨fun al x hl hh => ?_,
      fun al x h => al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this

/--
Instance `decidableLoHiLe` / 实例 `decidableLoHiLe`

English:
instance decidableLoHiLe
  signature: (lo hi : Nat) (P : Nat -> Prop) [DecidablePred P]
  body: decidable_of_iff (forall x, lo <= x -> x < hi + 1 -> P x)
    forall₂_congr fun _ _ => imp_congr Nat.lt_succ_iff Iff.rfl

中文:
实例 decidableLoHiLe
  签名: (lo hi : 自然数) (P : 自然数 -> 命题) [DecidablePred P]
  定义体: decidable_of_iff (forall x, lo <= x -> x < hi + 1 -> P x)
    forall₂_congr fun _ _ => imp_congr Nat.lt_succ_iff Iff.rfl

Depends on / 依赖: Iff.rfl, Nat.lt_succ_iff, decidable_of_iff, imp_congr, lt_succ_iff
-/
instance decidableLoHiLe (lo hi : Nat) (P : Nat -> Prop) [DecidablePred P] :
    Decidable (forall x, lo <= x -> x <= hi -> P x) :=
decidable_of_iff (forall x, lo <= x -> x < hi + 1 -> P x)
    forall₂_congr fun _ _ => imp_congr Nat.lt_succ_iff Iff.rfl

instance (n : Int) [NeZero n] : NeZero n.natAbs where
  out := n.natAbs_ne_zero.mpr (NeZero.ne n)

/-! ### `Nat.AtLeastTwo` -/

/--
Definition of `AtLeastTwo` / `AtLeastTwo` 的定义

English:
class AtLeastTwo
  parameters: (n : Nat)
  axioms and operations (1):
    - prop : 2 <= n

中文:
类 AtLeastTwo
  参数: (n : 自然数)
  公理与运算 (1 个):
    - prop : 2 <= n
-/
class AtLeastTwo (n : Nat) : Prop where
  prop : 2 <= n

-- Note: the following should stay axiom-free, since it is used whenever one writes the symbol
-- `2` in an abstract additive monoid...
instance (n : Nat) [NeZero n] : (n + 1).AtLeastTwo :=
  ⟨add_le_add (one_le_iff_ne_zero.mpr (NeZero.ne n)) (Nat.le_refl 1)⟩

namespace AtLeastTwo

variable {n : Nat} [n.AtLeastTwo]

/--
lemma `one_lt` / 引理 `one_lt`

English:
lemma one_lt
  statement: 1 < n
  proof: prop

中文:
引理 one_lt
  结论: 1 < n
  证明: prop
-/
lemma one_lt : 1 < n := prop
/--
lemma `ne_one` / 引理 `ne_one`

English:
lemma ne_one
  statement: n != 1
  proof: Nat.ne_of_gt one_lt

中文:
引理 ne_one
  结论: n != 1
  证明: Nat.ne_of_gt one_lt

Depends on / 依赖: Nat.ne_of_gt, ne_of_gt, one_lt
-/
lemma ne_one : n != 1 := Nat.ne_of_gt one_lt

instance (priority := 100) toNeZero (n : Nat) [n.AtLeastTwo] : NeZero n :=
  ⟨Nat.ne_of_gt (Nat.le_of_lt one_lt)⟩

variable (n) in
/--
lemma `neZero_sub_one` / 引理 `neZero_sub_one`

English:
lemma neZero_sub_one
  statement: NeZero (n - 1)
  proof: ⟨by have := prop (n := n); lia⟩

中文:
引理 neZero_sub_one
  结论: NeZero (n - 1)
  证明: ⟨by have := prop (n := n); lia⟩
-/
lemma neZero_sub_one : NeZero (n - 1) := ⟨by have := prop (n := n); lia⟩

end AtLeastTwo

end Nat
