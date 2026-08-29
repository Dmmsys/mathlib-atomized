/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
module

public import Mathlib.Data.Int.DivMod
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Common
public import Batteries.Data.Fin.Basic

/-!
# The finite type with `n` elements

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `finZeroElim` : Elimination principle for the empty set `Fin 0`, generalizes `Fin.elim0`.
  Further definitions and eliminators can be found in `Init.Data.Fin.Lemmas`
* `Fin.equivSubtype` : Equivalence between `Fin n` and `{ i // i < n }`.

-/

@[expose] public section


assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

/--
theorem `Nat.forall_lt_iff_fin` / 定理 `Nat.forall_lt_iff_fin`

English:
theorem Nat.forall_lt_iff_fin
  given: {n : Nat} {p : forall k, k < n -> Prop}
  proof: .symm Fin.forall_iff

中文:
定理 Nat.forall_lt_iff_fin
  条件: {n : 自然数} {p : 对任意 k, k < n -> 命题}
  证明: .symm Fin.forall_iff

Depends on / 依赖: Fin.forall_iff, forall_iff
-/
theorem Nat.forall_lt_iff_fin {n : Nat} {p : forall k, k < n -> Prop} :
    (forall k hk, p k hk) ↔ forall k : Fin n, p k k.is_lt :=
.symm Fin.forall_iff

/--
theorem `Nat.exists_lt_iff_fin` / 定理 `Nat.exists_lt_iff_fin`

English:
theorem Nat.exists_lt_iff_fin
  given: {n : Nat} {p : forall k, k < n -> Prop}
  proof: .symm Fin.exists_iff

中文:
定理 Nat.exists_lt_iff_fin
  条件: {n : 自然数} {p : 对任意 k, k < n -> 命题}
  证明: .symm Fin.exists_iff

Depends on / 依赖: Fin.exists_iff, exists_iff
-/
theorem Nat.exists_lt_iff_fin {n : Nat} {p : forall k, k < n -> Prop} :
    (exists k hk, p k hk) ↔ exists k : Fin n, p k k.is_lt :=
.symm Fin.exists_iff

/--
Definition of `finZeroElim` / `finZeroElim` 的定义

English:
definition finZeroElim
  signature: {α : Fin 0 -> Sort*} (x : Fin 0)
  body: x.elim0

中文:
定义 finZeroElim
  签名: {α : Fin 0 -> Sort*} (x : Fin 0)
  定义体: x.elim0

Depends on / 依赖: x.elim0
-/
def finZeroElim {α : Fin 0 -> Sort*} (x : Fin 0) : α x :=
  x.elim0

namespace Fin

/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: {n a : Nat} {ha : a < n + 2}
  proof: mk.inj_iff

中文:
定理 mk_eq_one
  条件: {n a : 自然数} {ha : a < n + 2}
  证明: mk.inj_iff
-/
@[simp] theorem mk_eq_one {n a : Nat} {ha : a < n + 2} :
    (⟨a, ha⟩ : Fin (n + 2)) = 1 ↔ a = 1 :=
  mk.inj_iff

/--
theorem `one_eq_mk` / 定理 `one_eq_mk`

English:
theorem one_eq_mk
  given: {n a : Nat} {ha : a < n + 2}
  proof: by
  simp [eq_comm]

中文:
定理 one_eq_mk
  条件: {n a : 自然数} {ha : a < n + 2}
  证明: by
  simp [eq_comm]
-/
@[simp] theorem one_eq_mk {n a : Nat} {ha : a < n + 2} :
    1 = (⟨a, ha⟩ : Fin (n + 2)) ↔ a = 1 := by
  simp [eq_comm]

instance {n : Nat} : CanLift Nat (Fin n) Fin.val (· < n) where
  prf k hk := ⟨⟨k, hk⟩, rfl⟩

/--
Definition of `rec0` / `rec0` 的定义

English:
definition rec0
  signature: {α : Fin 0 -> Sort*} (i : Fin 0)
  body: absurd i.2 (Nat.not_lt_zero _)

中文:
定义 rec0
  签名: {α : Fin 0 -> Sort*} (i : Fin 0)
  定义体: absurd i.2 (Nat.not_lt_zero _)

Depends on / 依赖: Nat.not_lt_zero, absurd, not_lt_zero
-/
def rec0 {α : Fin 0 -> Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)

variable {n m : Nat}

/--
theorem `val_injective` / 定理 `val_injective`

English:
theorem val_injective
  statement: Function.Injective (@Fin.val n)
  proof: @Fin.eq_of_val_eq n

中文:
定理 val_injective
  结论: Function.Injective (@Fin.val n)
  证明: @Fin.eq_of_val_eq n

Depends on / 依赖: Fin.eq_of_val_eq, eq_of_val_eq
-/
theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_val_eq n

/--
lemma `size_positive` / 引理 `size_positive`

English:
lemma size_positive
  statement: Fin n -> 0 < n
  proof: Fin.pos

中文:
引理 size_positive
  结论: Fin n -> 0 < n
  证明: Fin.pos

Depends on / 依赖: Fin.pos
-/
lemma size_positive : Fin n -> 0 < n := Fin.pos

/--
lemma `size_positive'` / 引理 `size_positive'`

English:
lemma size_positive'
  given: [Nonempty (Fin n)]
  statement: 0 < n
  proof: ‹Nonempty (Fin n)›.elim Fin.pos

中文:
引理 size_positive'
  条件: [Nonempty (Fin n)]
  结论: 0 < n
  证明: ‹Nonempty (Fin n)›.elim Fin.pos

Depends on / 依赖: Fin.pos, Nonempty
-/
lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim Fin.pos

/--
theorem `prop` / 定理 `prop`

English:
theorem prop
  given: (a : Fin n)
  statement: a.val < n
  proof: a.2

中文:
定理 prop
  条件: (a : Fin n)
  结论: a.val < n
  证明: a.2
-/
protected theorem prop (a : Fin n) : a.val < n :=
  a.2

/--
lemma `lt_last_iff_ne_last` / 引理 `lt_last_iff_ne_last`

English:
lemma lt_last_iff_ne_last
  given: {a : Fin (n + 1)}
  statement: a < last n ↔ a != last n
  proof: by
  simp [Fin.lt_iff_le_and_ne, le_last]

中文:
引理 lt_last_iff_ne_last
  条件: {a : Fin (n + 1)}
  结论: a < last n ↔ a != last n
  证明: by
  simp [Fin.lt_iff_le_and_ne, le_last]

Depends on / 依赖: Fin.lt_iff_le_and_ne, le_last, lt_iff_le_and_ne
-/
lemma lt_last_iff_ne_last {a : Fin (n + 1)} : a < last n ↔ a != last n := by
  simp [Fin.lt_iff_le_and_ne, le_last]

/--
lemma `ne_zero_of_lt` / 引理 `ne_zero_of_lt`

English:
lemma ne_zero_of_lt
  given: {a b : Fin (n + 1)} (hab : a < b)
  statement: b != 0
  proof: Fin.ne_of_gt Fin.lt_of_le_of_lt a.zero_le hab

中文:
引理 ne_zero_of_lt
  条件: {a b : Fin (n + 1)} (hab : a < b)
  结论: b != 0
  证明: Fin.ne_of_gt Fin.lt_of_le_of_lt a.zero_le hab

Depends on / 依赖: Fin.lt_of_le_of_lt, Fin.ne_of_gt, a.zero_le, lt_of_le_of_lt, ne_of_gt, zero_le
-/
lemma ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b != 0 :=
Fin.ne_of_gt Fin.lt_of_le_of_lt a.zero_le hab

/--
lemma `ne_last_of_lt` / 引理 `ne_last_of_lt`

English:
lemma ne_last_of_lt
  given: {a b : Fin (n + 1)} (hab : a < b)
  statement: a != last n
  proof: Fin.ne_of_lt Fin.lt_of_lt_of_le hab b.le_last

中文:
引理 ne_last_of_lt
  条件: {a b : Fin (n + 1)} (hab : a < b)
  结论: a != last n
  证明: Fin.ne_of_lt Fin.lt_of_lt_of_le hab b.le_last

Depends on / 依赖: Fin.lt_of_lt_of_le, Fin.ne_of_lt, b.le_last, le_last, lt_of_lt_of_le, ne_of_lt
-/
lemma ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a != last n :=
Fin.ne_of_lt Fin.lt_of_lt_of_le hab b.le_last

/--
lemma `ne_last_of_ne_last_of_le` / 引理 `ne_last_of_ne_last_of_le`

English:
lemma ne_last_of_ne_last_of_le
  given: {a b : Fin (n + 1)} (hb : b != last n) (hab : a <= b)
  proof: by
  intro rfl
  exact Nat.not_lt_of_le hab (lt_last_iff_ne_last.mpr hb)

中文:
引理 ne_last_of_ne_last_of_le
  条件: {a b : Fin (n + 1)} (hb : b != last n) (hab : a <= b)
  证明: by
  intro rfl
  exact Nat.not_lt_of_le hab (lt_last_iff_ne_last.mpr hb)

Depends on / 依赖: Nat.not_lt_of_le, lt_last_iff_ne_last, lt_last_iff_ne_last.mpr, not_lt_of_le
-/
lemma ne_last_of_ne_last_of_le {a b : Fin (n + 1)} (hb : b != last n) (hab : a <= b) :
    a != last n := by
  intro rfl
  exact Nat.not_lt_of_le hab (lt_last_iff_ne_last.mpr hb)

/--
lemma `val_sub_lt_of_lt_of_le` / 引理 `val_sub_lt_of_lt_of_le`

English:
lemma val_sub_lt_of_lt_of_le
  given: {a b : Fin n} (ha : a.val < m) (hab : b <= a)
  proof: by
  rw [Fin.sub_val_of_le hab]
  exact sub_lt_of_lt ha

中文:
引理 val_sub_lt_of_lt_of_le
  条件: {a b : Fin n} (ha : a.val < m) (hab : b <= a)
  证明: by
  rw [Fin.sub_val_of_le hab]
  exact sub_lt_of_lt ha

Depends on / 依赖: Fin.sub_val_of_le, sub_lt_of_lt, sub_val_of_le
-/
lemma val_sub_lt_of_lt_of_le {a b : Fin n} (ha : a.val < m) (hab : b <= a) :
    (a - b).val < m := by
  rw [Fin.sub_val_of_le hab]
  exact sub_lt_of_lt ha

/--
lemma `sub_ne_last_of_ne_last_of_le` / 引理 `sub_ne_last_of_ne_last_of_le`

English:
lemma sub_ne_last_of_ne_last_of_le
  given: {a b : Fin (n + 1)} (ha : a != last n) (hab : b <= a)
  proof: by
  rw [← lt_last_iff_ne_last]; rw [lt_def]
  exact val_sub_lt_of_lt_of_le (val_lt_last ha) hab

中文:
引理 sub_ne_last_of_ne_last_of_le
  条件: {a b : Fin (n + 1)} (ha : a != last n) (hab : b <= a)
  证明: by
  rw [← lt_last_iff_ne_last]; rw [lt_def]
  exact val_sub_lt_of_lt_of_le (val_lt_last ha) hab

Depends on / 依赖: lt_def, lt_last_iff_ne_last, val_lt_last, val_sub_lt_of_lt_of_le
-/
lemma sub_ne_last_of_ne_last_of_le {a b : Fin (n + 1)} (ha : a != last n) (hab : b <= a) :
    a - b != last n := by
  rw [← lt_last_iff_ne_last]; rw [lt_def]
  exact val_sub_lt_of_lt_of_le (val_lt_last ha) hab

/-- Equivalence between `Fin n` and `{ i // i < n }`. -/
@[simps apply symm_apply]
/--
Definition of `equivSubtype` / `equivSubtype` 的定义

English:
definition equivSubtype
  signature: : Fin n ≃ { i // i < n } where
  body: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

中文:
定义 equivSubtype
  签名: : Fin n ≃ { i // i < n } where
  定义体: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
-/
def equivSubtype : Fin n ≃ { i // i < n } where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/--
lemma `neZero` / 引理 `neZero`

English:
lemma neZero
  given: {n : Nat} (i : Fin n)
  statement: NeZero n
  proof: ⟨Nat.ne_zero_of_lt i.isLt⟩

中文:
引理 neZero
  条件: {n : 自然数} (i : Fin n)
  结论: NeZero n
  证明: ⟨Nat.ne_zero_of_lt i.isLt⟩

Depends on / 依赖: Nat.ne_zero_of_lt, i.isLt, ne_zero_of_lt
-/
lemma neZero {n : Nat} (i : Fin n) : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩

section coe


/--
theorem `val_eq_val` / 定理 `val_eq_val`

English:
theorem val_eq_val
  given: (a b : Fin n)
  statement: (a : Nat) = b ↔ a = b
  proof: Fin.ext_iff.symm

中文:
定理 val_eq_val
  条件: (a b : Fin n)
  结论: (a : 自然数) = b ↔ a = b
  证明: Fin.ext_iff.symm

Depends on / 依赖: Fin.ext_iff.symm, ext_iff
-/
theorem val_eq_val (a b : Fin n) : (a : Nat) = b ↔ a = b :=
  Fin.ext_iff.symm

/--
theorem `ne_iff_vne` / 定理 `ne_iff_vne`

English:
theorem ne_iff_vne
  given: (a b : Fin n)
  statement: a != b ↔ a.1 != b.1
  proof: Fin.ext_iff.not

中文:
定理 ne_iff_vne
  条件: (a b : Fin n)
  结论: a != b ↔ a.1 != b.1
  证明: Fin.ext_iff.not

Depends on / 依赖: Fin.ext_iff.not, ext_iff
-/
theorem ne_iff_vne (a b : Fin n) : a != b ↔ a.1 != b.1 :=
  Fin.ext_iff.not

/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {a h a' h'}
  statement: @mk n a h = @mk n a' h' ↔ a = a'
  proof: Fin.ext_iff

中文:
定理 mk_eq_mk
  条件: {a h a' h'}
  结论: @mk n a h = @mk n a' h' ↔ a = a'
  证明: Fin.ext_iff

Depends on / 依赖: Fin.ext_iff, ext_iff
-/
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  Fin.ext_iff

/--
theorem `heq_fun_iff` / 定理 `heq_fun_iff`

English:
theorem heq_fun_iff
  given: {α : Sort*} {k l : Nat} (h : k = l) {f : Fin k -> α} {g : Fin l -> α}
  proof: by
  subst h
  simp [funext_iff]

中文:
定理 heq_fun_iff
  条件: {α : Sort*} {k l : 自然数} (h : k = l) {f : Fin k -> α} {g : Fin l -> α}
  证明: by
  subst h
  simp [funext_iff]
-/
protected theorem heq_fun_iff {α : Sort*} {k l : Nat} (h : k = l) {f : Fin k -> α} {g : Fin l -> α} :
    f ≍ g ↔ forall i : Fin k, f i = g ⟨(i : Nat), h ▸ i.2⟩ := by
  subst h
  simp [funext_iff]

/--
theorem `heq_fun₂_iff` / 定理 `heq_fun₂_iff`

English:
theorem heq_fun₂_iff
  statement: {α : Sort*} {k l k' l' : Nat} (h : k = l) (h' : k' = l')
  proof: by
  subst h
  subst h'
  simp [funext_iff]

中文:
定理 heq_fun₂_iff
  结论: {α : Sort*} {k l k' l' : 自然数} (h : k = l) (h' : k' = l')
  证明: by
  subst h
  subst h'
  simp [funext_iff]
-/
protected theorem heq_fun₂_iff {α : Sort*} {k l k' l' : Nat} (h : k = l) (h' : k' = l')
    {f : Fin k -> Fin k' -> α} {g : Fin l -> Fin l' -> α} :
    f ≍ g ↔ forall (i : Fin k) (j : Fin k'), f i j = g ⟨(i : Nat), h ▸ i.2⟩ ⟨(j : Nat), h' ▸ j.2⟩ := by
  subst h
  subst h'
  simp [funext_iff]

/--
theorem `heq_ext_iff` / 定理 `heq_ext_iff`

English:
theorem heq_ext_iff
  given: {k l : Nat} (h : k = l) {i : Fin k} {j : Fin l}
  proof: by
  subst h
  simp [val_eq_val]

中文:
定理 heq_ext_iff
  条件: {k l : 自然数} (h : k = l) {i : Fin k} {j : Fin l}
  证明: by
  subst h
  simp [val_eq_val]
-/
protected theorem heq_ext_iff {k l : Nat} (h : k = l) {i : Fin k} {j : Fin l} :
    i ≍ j ↔ (i : Nat) = (j : Nat) := by
  subst h
  simp [val_eq_val]

end coe


section Order

/-!
### order
-/

/-- `Fin.lt_or_ge` is an alias of `Fin.lt_or_le`.
It is preferred since it follows the mathlib naming convention. -/
protected alias lt_or_ge := Fin.lt_or_le
/-- `Fin.le_or_gt` is an alias of `Fin.le_or_lt`.
It is preferred since it follows the mathlib naming convention. -/
protected alias le_or_gt := Fin.le_or_lt

/--
theorem `le_iff_val_le_val` / 定理 `le_iff_val_le_val`

English:
theorem le_iff_val_le_val
  given: {a b : Fin n}
  statement: a <= b ↔ (a : Nat) <= b
  proof: Iff.rfl

中文:
定理 le_iff_val_le_val
  条件: {a b : Fin n}
  结论: a <= b ↔ (a : 自然数) <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : Nat) <= b :=
  Iff.rfl

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
@[norm_cast, simp]
/--
theorem `val_fin_lt` / 定理 `val_fin_lt`

English:
theorem val_fin_lt
  given: {n : Nat} {a b : Fin n}
  statement: (a : Nat) < (b : Nat) ↔ a < b
  proof: Iff.rfl

中文:
定理 val_fin_lt
  条件: {n : 自然数} {a b : Fin n}
  结论: (a : 自然数) < (b : 自然数) ↔ a < b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem val_fin_lt {n : Nat} {a b : Fin n} : (a : Nat) < (b : Nat) ↔ a < b :=
  Iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `Fin n`. -/
@[norm_cast, simp]
/--
theorem `val_fin_le` / 定理 `val_fin_le`

English:
theorem val_fin_le
  given: {n : Nat} {a b : Fin n}
  statement: (a : Nat) <= (b : Nat) ↔ a <= b
  proof: Iff.rfl

中文:
定理 val_fin_le
  条件: {n : 自然数} {a b : Fin n}
  结论: (a : 自然数) <= (b : 自然数) ↔ a <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem val_fin_le {n : Nat} {a b : Fin n} : (a : Nat) <= (b : Nat) ↔ a <= b :=
  Iff.rfl

/--
theorem `min_val` / 定理 `min_val`

English:
theorem min_val
  given: {a : Fin n}
  statement: min (a : Nat) n = a
  proof: by simp

中文:
定理 min_val
  条件: {a : Fin n}
  结论: min (a : 自然数) n = a
  证明: by simp
-/
theorem min_val {a : Fin n} : min (a : Nat) n = a := by simp

/--
theorem `max_val` / 定理 `max_val`

English:
theorem max_val
  given: {a : Fin n}
  statement: max (a : Nat) n = n
  proof: by simp

中文:
定理 max_val
  条件: {a : Fin n}
  结论: max (a : 自然数) n = n
  证明: by simp
-/
theorem max_val {a : Fin n} : max (a : Nat) n = n := by simp

/-- Use the ordering on `Fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `WellFoundedRelation` instance:
```lean
def factorial {n : ℕ} : Fin n → ℕ
  | ⟨0, _⟩ := 1
  | ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : Nat} : WellFoundedRelation (Fin n) :=
  measure (val : Fin n -> Nat)

/-- `Fin.mk_zero` in `Lean` only applies in `Fin (n + 1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
/--
theorem `mk_zero'` / 定理 `mk_zero'`

English:
theorem mk_zero'
  given: (n : Nat) [NeZero n]
  statement: (⟨0, pos_of_neZero n⟩ : Fin n) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_zero'
  条件: (n : 自然数) [NeZero n]
  结论: (⟨0, pos_of_neZero n⟩ : Fin n) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_zero' (n : Nat) [NeZero n] : (⟨0, pos_of_neZero n⟩ : Fin n) = 0 := rfl

@[simp, norm_cast]
/--
theorem `val_pos_iff` / 定理 `val_pos_iff`

English:
theorem val_pos_iff
  given: [NeZero n] {a : Fin n}
  statement: 0 < a.val ↔ 0 < a
  proof: by
  rw [← val_fin_lt]; rw [val_zero]

中文:
定理 val_pos_iff
  条件: [NeZero n] {a : Fin n}
  结论: 0 < a.val ↔ 0 < a
  证明: by
  rw [← val_fin_lt]; rw [val_zero]

Depends on / 依赖: val_fin_lt, val_zero
-/
theorem val_pos_iff [NeZero n] {a : Fin n} : 0 < a.val ↔ 0 < a := by
  rw [← val_fin_lt]; rw [val_zero]

/--
theorem `pos_iff_ne_zero'` / 定理 `pos_iff_ne_zero'`

English:
theorem pos_iff_ne_zero'
  given: [NeZero n] (a : Fin n)
  statement: 0 < a ↔ a != 0
  proof: by
  rw [← val_pos_iff]; rw [Nat.pos_iff_ne_zero]; rw [val_ne_zero_iff]

中文:
定理 pos_iff_ne_zero'
  条件: [NeZero n] (a : Fin n)
  结论: 0 < a ↔ a != 0
  证明: by
  rw [← val_pos_iff]; rw [Nat.pos_iff_ne_zero]; rw [val_ne_zero_iff]

Depends on / 依赖: Nat.pos_iff_ne_zero, pos_iff_ne_zero, val_ne_zero_iff, val_pos_iff
-/
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a != 0 := by
  rw [← val_pos_iff]; rw [Nat.pos_iff_ne_zero]; rw [val_ne_zero_iff]

/--
lemma `cast_eq_self` / 引理 `cast_eq_self`

English:
lemma cast_eq_self
  given: (a : Fin n)
  statement: a.cast rfl = a
  proof: rfl

中文:
引理 cast_eq_self
  条件: (a : Fin n)
  结论: a.cast rfl = a
  证明: rfl
-/
@[simp] lemma cast_eq_self (a : Fin n) : a.cast rfl = a := rfl

/--
theorem `cast_eq_zero` / 定理 `cast_eq_zero`

English:
theorem cast_eq_zero
  statement: {k l : Nat} [NeZero k] [NeZero l]
  proof: by
  simp [← val_eq_zero_iff]

中文:
定理 cast_eq_zero
  结论: {k l : 自然数} [NeZero k] [NeZero l]
  证明: by
  simp [← val_eq_zero_iff]
-/
@[simp] theorem cast_eq_zero {k l : Nat} [NeZero k] [NeZero l]
    (h : k = l) (x : Fin k) : Fin.cast h x = 0 ↔ x = 0 := by
  simp [← val_eq_zero_iff]

/--
lemma `cast_injective` / 引理 `cast_injective`

English:
lemma cast_injective
  given: {k l : Nat} (h : k = l)
  statement: Injective (Fin.cast h)
  proof: fun a b hab => by simpa [← val_eq_val] using hab

中文:
引理 cast_injective
  条件: {k l : 自然数} (h : k = l)
  结论: Injective (Fin.cast h)
  证明: fun a b hab => by simpa [← val_eq_val] using hab

Depends on / 依赖: val_eq_val
-/
lemma cast_injective {k l : Nat} (h : k = l) : Injective (Fin.cast h) :=
  fun a b hab => by simpa [← val_eq_val] using hab

/--
theorem `last_pos'` / 定理 `last_pos'`

English:
theorem last_pos'
  given: [NeZero n]
  statement: 0 < last n
  proof: n.pos_of_neZero

中文:
定理 last_pos'
  条件: [NeZero n]
  结论: 0 < last n
  证明: n.pos_of_neZero

Depends on / 依赖: n.pos_of_neZero, pos_of_neZero
-/
theorem last_pos' [NeZero n] : 0 < last n := n.pos_of_neZero

/--
theorem `one_lt_last` / 定理 `one_lt_last`

English:
theorem one_lt_last
  given: [NeZero n]
  statement: 1 < last (n + 1)
  proof: by
  rw [lt_def]; rw [val_one]; rw [val_last]; rw [Nat.lt_add_left_iff_pos]; rw [Nat.pos_iff_ne_zero]
  exact NeZero.ne n

中文:
定理 one_lt_last
  条件: [NeZero n]
  结论: 1 < last (n + 1)
  证明: by
  rw [lt_def]; rw [val_one]; rw [val_last]; rw [Nat.lt_add_left_iff_pos]; rw [Nat.pos_iff_ne_zero]
  exact NeZero.ne n

Depends on / 依赖: Nat.lt_add_left_iff_pos, Nat.pos_iff_ne_zero, NeZero, NeZero.ne, lt_add_left_iff_pos, lt_def, pos_iff_ne_zero, val_last, val_one
-/
theorem one_lt_last [NeZero n] : 1 < last (n + 1) := by
  rw [lt_def]; rw [val_one]; rw [val_last]; rw [Nat.lt_add_left_iff_pos]; rw [Nat.pos_iff_ne_zero]
  exact NeZero.ne n

end Order

/-! ### Coercions to `ℤ` and the `fin_omega` tactic. -/

open Int

/--
theorem `coe_int_sub_eq_ite` / 定理 `coe_int_sub_eq_ite`

English:
theorem coe_int_sub_eq_ite
  given: {n : Nat} (u v : Fin n)
  proof: by
  rw [Fin.sub_def]
  split
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> omega
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> omega

中文:
定理 coe_int_sub_eq_ite
  条件: {n : 自然数} (u v : Fin n)
  证明: by
  rw [Fin.sub_def]
  split
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> omega
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> omega

Depends on / 依赖: Fin.sub_def, Int.emod_eq_of_lt, Int.emod_eq_sub_self_emod, emod_eq_of_lt, emod_eq_sub_self_emod, natCast_emod, sub_def
-/
theorem coe_int_sub_eq_ite {n : Nat} (u v : Fin n) :
    ((u - v : Fin n) : Int) = if v <= u then (u - v : Int) else (u - v : Int) + n := by
  rw [Fin.sub_def]
  split
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> omega
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> omega

/--
theorem `coe_int_sub_eq_mod` / 定理 `coe_int_sub_eq_mod`

English:
theorem coe_int_sub_eq_mod
  given: {n : Nat} (u v : Fin n)
  proof: by
  rw [coe_int_sub_eq_ite]
  split
  · rw [Int.emod_eq_of_lt] <;> omega
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega

中文:
定理 coe_int_sub_eq_mod
  条件: {n : 自然数} (u v : Fin n)
  证明: by
  rw [coe_int_sub_eq_ite]
  split
  · rw [Int.emod_eq_of_lt] <;> omega
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega

Depends on / 依赖: Int.emod_eq_add_self_emod, Int.emod_eq_of_lt, coe_int_sub_eq_ite, emod_eq_add_self_emod, emod_eq_of_lt
-/
theorem coe_int_sub_eq_mod {n : Nat} (u v : Fin n) :
    ((u - v : Fin n) : Int) = ((u : Int) - (v : Int)) % n := by
  rw [coe_int_sub_eq_ite]
  split
  · rw [Int.emod_eq_of_lt] <;> omega
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega

/--
theorem `coe_int_add_eq_ite` / 定理 `coe_int_add_eq_ite`

English:
theorem coe_int_add_eq_ite
  given: {n : Nat} (u v : Fin n)
  proof: by
  rw [Fin.add_def]
  split
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> lia
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> lia

中文:
定理 coe_int_add_eq_ite
  条件: {n : 自然数} (u v : Fin n)
  证明: by
  rw [Fin.add_def]
  split
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> lia
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> lia

Depends on / 依赖: Fin.add_def, Int.emod_eq_of_lt, Int.emod_eq_sub_self_emod, add_def, emod_eq_of_lt, emod_eq_sub_self_emod, natCast_emod
-/
theorem coe_int_add_eq_ite {n : Nat} (u v : Fin n) :
    ((u + v : Fin n) : Int) = if (u + v : Nat) < n then (u + v : Int) else (u + v : Int) - n := by
  rw [Fin.add_def]
  split
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> lia
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> lia

/--
theorem `coe_int_add_eq_mod` / 定理 `coe_int_add_eq_mod`

English:
theorem coe_int_add_eq_mod
  given: {n : Nat} (u v : Fin n)
  proof: by
  omega

中文:
定理 coe_int_add_eq_mod
  条件: {n : 自然数} (u v : Fin n)
  证明: by
  omega
-/
theorem coe_int_add_eq_mod {n : Nat} (u v : Fin n) :
    ((u + v : Fin n) : Int) = ((u : Int) + (v : Int)) % n := by
  omega

-- Write `a + b` as `if (a + b : ℕ) < n then (a + b : ℤ) else (a + b : ℤ) - n` and
-- similarly `a - b` as `if (b : ℕ) ≤ a then (a - b : ℤ) else (a - b : ℤ) + n`.
attribute [fin_omega] coe_int_sub_eq_ite coe_int_add_eq_ite

-- Rewrite inequalities in `Fin` to inequalities in `ℕ`
attribute [fin_omega] Fin.lt_iff_val_lt_val Fin.le_iff_val_le_val

-- Rewrite `1 : Fin (n + 2)` to `1 : ℤ`
attribute [fin_omega] val_one

/--
`fin_omega` is a preprocessor for `omega` to handle inequalities in `Fin`.
It rewrites all hypotheses and the goal, turning statements about addition, subtraction and
inequalities in `Fin n` into statements that `omega` can use/solve.
Note that this involves a lot of case splitting, so may be slow.
-/
-- Further adjustment to the simp set can probably make this more powerful.
-- Please experiment and PR updates!
macro "fin_omega" : tactic => `(tactic|
  { try simp only [fin_omega, ← Int.ofNat_lt, ← Int.ofNat_le] at *
    omega })

section Add


/--
theorem `val_one'` / 定理 `val_one'`

English:
theorem val_one'
  given: (n : Nat) [NeZero n]
  statement: ((1 : Fin n) : Nat) = 1 % n
  proof: rfl

中文:
定理 val_one'
  条件: (n : 自然数) [NeZero n]
  结论: ((1 : Fin n) : 自然数) = 1 % n
  证明: rfl
-/
theorem val_one' (n : Nat) [NeZero n] : ((1 : Fin n) : Nat) = 1 % n :=
  rfl

/--
theorem `nontrivial_iff_two_le` / 定理 `nontrivial_iff_two_le`

English:
theorem nontrivial_iff_two_le
  statement: Nontrivial (Fin n) ↔ 2 <= n
  proof: by
  simp [← not_subsingleton_iff_nontrivial, subsingleton_iff_le_one]; lia

中文:
定理 nontrivial_iff_two_le
  结论: Nontrivial (Fin n) ↔ 2 <= n
  证明: by
  simp [← not_subsingleton_iff_nontrivial, subsingleton_iff_le_one]; lia

Depends on / 依赖: not_subsingleton_iff_nontrivial, subsingleton_iff_le_one
-/
theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 <= n := by
  simp [← not_subsingleton_iff_nontrivial, subsingleton_iff_le_one]; lia

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [n.AtLeastTwo]
  body: nontrivial_iff_two_le.2 Nat.AtLeastTwo.one_lt

中文:
实例 instNontrivial
  签名: [n.AtLeastTwo]
  定义体: nontrivial_iff_two_le.2 Nat.AtLeastTwo.one_lt

Depends on / 依赖: AtLeastTwo, Nat.AtLeastTwo.one_lt, nontrivial_iff_two_le, one_lt
-/
instance instNontrivial [n.AtLeastTwo] : Nontrivial (Fin n) :=
  nontrivial_iff_two_le.2 Nat.AtLeastTwo.one_lt

/--
theorem `exists_ne_and_ne_of_two_lt` / 定理 `exists_ne_and_ne_of_two_lt`

English:
theorem exists_ne_and_ne_of_two_lt
  given: (i j : Fin n) (h : 2 < n)
  statement: exists k, k != i ∧ k != j
  proof: by
  have : NeZero n := ⟨by lia⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp_rw [← Fin.val_ne_iff]
  by_cases h0 : 0 != i ∧ 0 != j
  · exact ⟨0, h0⟩
  · by_cases h1 : 1 != i ∧ 1 != j
    · exact ⟨⟨1, by lia⟩, h1⟩
    · refine ⟨⟨2, by lia⟩, ?_⟩
      dsimp only
      lia

中文:
定理 exists_ne_and_ne_of_two_lt
  条件: (i j : Fin n) (h : 2 < n)
  结论: 存在 k, k != i ∧ k != j
  证明: by
  have : NeZero n := ⟨by lia⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp_rw [← Fin.val_ne_iff]
  by_cases h0 : 0 != i ∧ 0 != j
  · exact ⟨0, h0⟩
  · by_cases h1 : 1 != i ∧ 1 != j
    · exact ⟨⟨1, by lia⟩, h1⟩
    · refine ⟨⟨2, by lia⟩, ?_⟩
      dsimp only
      lia

Depends on / 依赖: Fin.val_ne_iff, NeZero, simp_rw, val_ne_iff
-/
theorem exists_ne_and_ne_of_two_lt (i j : Fin n) (h : 2 < n) : exists k, k != i ∧ k != j := by
  have : NeZero n := ⟨by lia⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp_rw [← Fin.val_ne_iff]
  by_cases h0 : 0 != i ∧ 0 != j
  · exact ⟨0, h0⟩
  · by_cases h1 : 1 != i ∧ 1 != j
    · exact ⟨⟨1, by lia⟩, h1⟩
    · refine ⟨⟨2, by lia⟩, ?_⟩
      dsimp only
      lia

section Monoid

/--
Instance `inhabitedFinOneAdd` / 实例 `inhabitedFinOneAdd`

English:
instance inhabitedFinOneAdd
  signature: (n : Nat)
  body: haveI : NeZero (1 + n) := by rw [Nat.add_comm]; infer_instance
  inferInstance

@[simp]

中文:
实例 inhabitedFinOneAdd
  签名: (n : 自然数)
  定义体: haveI : NeZero (1 + n) := by rw [Nat.add_comm]; infer_instance
  inferInstance

@[simp]

Depends on / 依赖: Nat.add_comm, NeZero, add_comm, infer_instance
-/
instance inhabitedFinOneAdd (n : Nat) : Inhabited (Fin (1 + n)) :=
  haveI : NeZero (1 + n) := by rw [Nat.add_comm]; infer_instance
  inferInstance

@[simp]
/--
theorem `default_eq_zero` / 定理 `default_eq_zero`

English:
theorem default_eq_zero
  given: (n : Nat) [NeZero n]
  statement: (default : Fin n) = 0
  proof: rfl

中文:
定理 default_eq_zero
  条件: (n : 自然数) [NeZero n]
  结论: (default : Fin n) = 0
  证明: rfl
-/
theorem default_eq_zero (n : Nat) [NeZero n] : (default : Fin n) = 0 :=
  rfl

end Monoid

/--
theorem `val_add_eq_ite` / 定理 `val_add_eq_ite`

English:
theorem val_add_eq_ite
  given: {n : Nat} (a b : Fin n)
  proof: by
  rw [Fin.val_add]; rw [Nat.add_mod_eq_ite]; rw [Nat.mod_eq_of_lt (show ↑a < n from a.2)]; rw [Nat.mod_eq_of_lt (show ↑b < n from b.2)]

中文:
定理 val_add_eq_ite
  条件: {n : 自然数} (a b : Fin n)
  证明: by
  rw [Fin.val_add]; rw [Nat.add_mod_eq_ite]; rw [Nat.mod_eq_of_lt (show ↑a < n from a.2)]; rw [Nat.mod_eq_of_lt (show ↑b < n from b.2)]

Depends on / 依赖: Fin.val_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt, add_mod_eq_ite, mod_eq_of_lt, val_add
-/
theorem val_add_eq_ite {n : Nat} (a b : Fin n) :
    (↑(a + b) : Nat) = if n <= a + b then a + b - n else a + b := by
  rw [Fin.val_add]; rw [Nat.add_mod_eq_ite]; rw [Nat.mod_eq_of_lt (show ↑a < n from a.2)]; rw [Nat.mod_eq_of_lt (show ↑b < n from b.2)]

/--
theorem `val_add_eq_of_add_lt` / 定理 `val_add_eq_of_add_lt`

English:
theorem val_add_eq_of_add_lt
  given: {n : Nat} {a b : Fin n} (huv : a.val + b.val < n)
  proof: by
  rw [val_add]
  simp [Nat.mod_eq_of_lt huv]

中文:
定理 val_add_eq_of_add_lt
  条件: {n : 自然数} {a b : Fin n} (huv : a.val + b.val < n)
  证明: by
  rw [val_add]
  simp [Nat.mod_eq_of_lt huv]

Depends on / 依赖: Nat.mod_eq_of_lt, mod_eq_of_lt, val_add
-/
theorem val_add_eq_of_add_lt {n : Nat} {a b : Fin n} (huv : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  rw [val_add]
  simp [Nat.mod_eq_of_lt huv]

/--
lemma `intCast_val_sub_eq_sub_add_ite` / 引理 `intCast_val_sub_eq_sub_add_ite`

English:
lemma intCast_val_sub_eq_sub_add_ite
  given: {n : Nat} (a b : Fin n)
  proof: by
  split <;> fin_omega

中文:
引理 intCast_val_sub_eq_sub_add_ite
  条件: {n : 自然数} (a b : Fin n)
  证明: by
  split <;> fin_omega

Depends on / 依赖: fin_omega
-/
lemma intCast_val_sub_eq_sub_add_ite {n : Nat} (a b : Fin n) :
    ((a - b).val : Int) = a.val - b.val + if b <= a then 0 else n := by
  split <;> fin_omega

/--
lemma `sub_val_lt_sub` / 引理 `sub_val_lt_sub`

English:
lemma sub_val_lt_sub
  given: {n : Nat} {i j : Fin n} (hij : i <= j)
  statement: (j - i).val < n - i.val
  proof: by
  simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]

中文:
引理 sub_val_lt_sub
  条件: {n : 自然数} {i j : Fin n} (hij : i <= j)
  结论: (j - i).val < n - i.val
  证明: by
  simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]

Depends on / 依赖: Nat.sub_lt_sub_right, j.isLt, sub_lt_sub_right, sub_val_of_le
-/
lemma sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j) : (j - i).val < n - i.val := by
  simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]

/--
lemma `castLT_sub_nezero` / 引理 `castLT_sub_nezero`

English:
lemma castLT_sub_nezero
  given: {n : Nat} {i j : Fin n} (hij : i < j)
  proof: neZero_iff.mpr (by lia)
    (j - i).castLT (sub_val_lt_sub (Fin.le_of_lt hij)) != 0 := by
  refine Ne.symm (ne_of_val_ne ?_)
  simp [coe_sub_iff_le.mpr (Fin.le_of_lt hij)]
  lia

中文:
引理 castLT_sub_nezero
  条件: {n : 自然数} {i j : Fin n} (hij : i < j)
  证明: neZero_iff.mpr (by lia)
    (j - i).castLT (sub_val_lt_sub (Fin.le_of_lt hij)) != 0 := by
  refine Ne.symm (ne_of_val_ne ?_)
  simp [coe_sub_iff_le.mpr (Fin.le_of_lt hij)]
  lia

Depends on / 依赖: neZero_iff, neZero_iff.mpr
-/
lemma castLT_sub_nezero {n : Nat} {i j : Fin n} (hij : i < j) :
    haveI : NeZero (n - i.1) := neZero_iff.mpr (by lia)
    (j - i).castLT (sub_val_lt_sub (Fin.le_of_lt hij)) != 0 := by
  refine Ne.symm (ne_of_val_ne ?_)
  simp [coe_sub_iff_le.mpr (Fin.le_of_lt hij)]
  lia

/--
lemma `one_le_of_ne_zero` / 引理 `one_le_of_ne_zero`

English:
lemma one_le_of_ne_zero
  given: {n : Nat} {k : Fin n}
  proof: k.neZero
    (hk : k != 0) -> 1 <= k := by
  have : NeZero n := k.neZero
  intro hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  cases n with
  | zero => simp only [Fin.isValue, Fin.zero_le]
  | succ n => rwa [Fin.le_iff_val_le_val, Fin.val_one, Nat.one_le_iff_ne_zero, val_ne_z

中文:
引理 one_le_of_ne_zero
  条件: {n : 自然数} {k : Fin n}
  证明: k.neZero
    (hk : k != 0) -> 1 <= k := by
  have : NeZero n := k.neZero
  intro hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  cases n with
  | zero => simp only [Fin.isValue, Fin.zero_le]
  | succ n => rwa [Fin.le_iff_val_le_val, Fin.val_one, Nat.one_le_iff_ne_zero, val_ne_z

Depends on / 依赖: k.neZero, neZero
-/
lemma one_le_of_ne_zero {n : Nat} {k : Fin n} :
    haveI := k.neZero
    (hk : k != 0) -> 1 <= k := by
  have : NeZero n := k.neZero
  intro hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  cases n with
  | zero => simp only [Fin.isValue, Fin.zero_le]
  | succ n => rwa [Fin.le_iff_val_le_val, Fin.val_one, Nat.one_le_iff_ne_zero, val_ne_zero_iff]

/--
lemma `val_sub_one_of_ne_zero` / 引理 `val_sub_one_of_ne_zero`

English:
lemma val_sub_one_of_ne_zero
  given: {i : Fin n}
  proof: i.neZero
    (hi : i != 0) -> (i - 1).val = i - 1 := by
  have := i.neZero
  intro hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.sub_val_of_le (one_le_of_ne_zero hi)]; rw [Fin.val_one']; rw [Nat.mod_eq_of_lt
    (Nat.succ_le_iff.mpr (nontrivial_iff_two_le.mp <| nontri

中文:
引理 val_sub_one_of_ne_zero
  条件: {i : Fin n}
  证明: i.neZero
    (hi : i != 0) -> (i - 1).val = i - 1 := by
  have := i.neZero
  intro hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.sub_val_of_le (one_le_of_ne_zero hi)]; rw [Fin.val_one']; rw [Nat.mod_eq_of_lt
    (Nat.succ_le_iff.mpr (nontrivial_iff_two_le.mp <| nontri

Depends on / 依赖: i.neZero, neZero
-/
lemma val_sub_one_of_ne_zero {i : Fin n} :
    haveI := i.neZero
    (hi : i != 0) -> (i - 1).val = i - 1 := by
  have := i.neZero
  intro hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.sub_val_of_le (one_le_of_ne_zero hi)]; rw [Fin.val_one']; rw [Nat.mod_eq_of_lt
    (Nat.succ_le_iff.mpr (nontrivial_iff_two_le.mp <| nontrivial_of_ne i 0 hi))]

section OfNatCoe

-- We allow the coercion from `Nat` to `Fin` in this section.
open Fin.NatCast

@[simp]
/--
theorem `ofNat_eq_cast` / 定理 `ofNat_eq_cast`

English:
theorem ofNat_eq_cast
  given: (n : Nat) [NeZero n] (a : Nat)
  statement: Fin.ofNat n a = (a : Fin n)
  proof: rfl

中文:
定理 ofNat_eq_cast
  条件: (n : 自然数) [NeZero n] (a : 自然数)
  结论: Fin.of自然数 n a = (a : Fin n)
  证明: rfl
-/
theorem ofNat_eq_cast (n : Nat) [NeZero n] (a : Nat) : Fin.ofNat n a = (a : Fin n) :=
  rfl

/--
lemma `val_natCast` / 引理 `val_natCast`

English:
lemma val_natCast
  given: (a n : Nat) [NeZero n]
  statement: (a : Fin n).val = a % n
  proof: rfl

中文:
引理 val_natCast
  条件: (a n : 自然数) [NeZero n]
  结论: (a : Fin n).val = a % n
  证明: rfl
-/
@[simp] lemma val_natCast (a n : Nat) [NeZero n] : (a : Fin n).val = a % n := rfl

/--
theorem `val_cast_of_lt` / 定理 `val_cast_of_lt`

English:
theorem val_cast_of_lt
  given: {n : Nat} [NeZero n] {a : Nat} (h : a < n)
  statement: (a : Fin n).val = a
  proof: Nat.mod_eq_of_lt h

中文:
定理 val_cast_of_lt
  条件: {n : 自然数} [NeZero n] {a : 自然数} (h : a < n)
  结论: (a : Fin n).val = a
  证明: Nat.mod_eq_of_lt h

Depends on / 依赖: Nat.mod_eq_of_lt, mod_eq_of_lt
-/
theorem val_cast_of_lt {n : Nat} [NeZero n] {a : Nat} (h : a < n) : (a : Fin n).val = a :=
  Nat.mod_eq_of_lt h

/--
theorem `cast_val_eq_self` / 定理 `cast_val_eq_self`

English:
theorem cast_val_eq_self
  given: {n : Nat} (a : Fin n)
  proof: a.neZero
    (a.val : Fin n) = a :=
  have := a.neZero
Fin.ext val_cast_of_lt a.isLt

中文:
定理 cast_val_eq_self
  条件: {n : 自然数} (a : Fin n)
  证明: a.neZero
    (a.val : Fin n) = a :=
  have := a.neZero
Fin.ext val_cast_of_lt a.isLt
-/
@[simp, norm_cast] theorem cast_val_eq_self {n : Nat} (a : Fin n) :
    haveI := a.neZero
    (a.val : Fin n) = a :=
  have := a.neZero
Fin.ext val_cast_of_lt a.isLt

-- This is a special case of `CharP.cast_eq_zero` that doesn't require typeclass search
/--
lemma `natCast_self` / 引理 `natCast_self`

English:
lemma natCast_self
  given: (n : Nat) [NeZero n]
  statement: (n : Fin n) = 0
  proof: by ext; simp

中文:
引理 natCast_self
  条件: (n : 自然数) [NeZero n]
  结论: (n : Fin n) = 0
  证明: by ext; simp
-/
@[simp high] lemma natCast_self (n : Nat) [NeZero n] : (n : Fin n) = 0 := by ext; simp

/--
lemma `natCast_eq_zero` / 引理 `natCast_eq_zero`

English:
lemma natCast_eq_zero
  given: {a n : Nat} [NeZero n]
  statement: (a : Fin n) = 0 ↔ n ∣ a
  proof: by
  simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]

中文:
引理 natCast_eq_zero
  条件: {a n : 自然数} [NeZero n]
  结论: (a : Fin n) = 0 ↔ n ∣ a
  证明: by
  simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]
-/
@[simp] lemma natCast_eq_zero {a n : Nat} [NeZero n] : (a : Fin n) = 0 ↔ n ∣ a := by
  simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]

/--
lemma `natCast_zero` / 引理 `natCast_zero`

English:
lemma natCast_zero
  given: {n : Nat} [NeZero n]
  statement: ((0 : Nat) : Fin n) = 0
  proof: by
  simp

@[simp]

中文:
引理 natCast_zero
  条件: {n : 自然数} [NeZero n]
  结论: ((0 : 自然数) : Fin n) = 0
  证明: by
  simp

@[simp]
-/
@[simp] lemma natCast_zero {n : Nat} [NeZero n] : ((0 : Nat) : Fin n) = 0 := by
  simp

@[simp]
/--
theorem `natCast_eq_last` / 定理 `natCast_eq_last`

English:
theorem natCast_eq_last
  given: (n)
  statement: (n : Fin (n + 1)) = Fin.last n
  proof: by ext; simp

中文:
定理 natCast_eq_last
  条件: (n)
  结论: (n : Fin (n + 1)) = Fin.last n
  证明: by ext; simp
-/
theorem natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by ext; simp

/--
theorem `natCast_eq_mk` / 定理 `natCast_eq_mk`

English:
theorem natCast_eq_mk
  given: {m n : Nat} (h : m < n)
  statement: have : NeZero n
  proof: ⟨Nat.ne_zero_of_lt h⟩
    (m : Fin n) = Fin.mk m h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

中文:
定理 natCast_eq_mk
  条件: {m n : 自然数} (h : m < n)
  结论: have : NeZero n
  证明: ⟨Nat.ne_zero_of_lt h⟩
    (m : Fin n) = Fin.mk m h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

Depends on / 依赖: Nat.ne_zero_of_lt, ne_zero_of_lt
-/
theorem natCast_eq_mk {m n : Nat} (h : m < n) : have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    (m : Fin n) = Fin.mk m h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

/--
theorem `one_eq_mk_of_lt` / 定理 `one_eq_mk_of_lt`

English:
theorem one_eq_mk_of_lt
  given: {n : Nat} (h : 1 < n)
  statement: have : NeZero n
  proof: ⟨Nat.ne_zero_of_lt h⟩
    1 = Fin.mk 1 h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

中文:
定理 one_eq_mk_of_lt
  条件: {n : 自然数} (h : 1 < n)
  结论: have : NeZero n
  证明: ⟨Nat.ne_zero_of_lt h⟩
    1 = Fin.mk 1 h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

Depends on / 依赖: Nat.ne_zero_of_lt, ne_zero_of_lt
-/
theorem one_eq_mk_of_lt {n : Nat} (h : 1 < n) : have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    1 = Fin.mk 1 h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

/--
theorem `le_val_last` / 定理 `le_val_last`

English:
theorem le_val_last
  given: (i : Fin (n + 1))
  statement: i <= n
  proof: by
  rw [Fin.natCast_eq_last]
  exact Fin.le_last i

中文:
定理 le_val_last
  条件: (i : Fin (n + 1))
  结论: i <= n
  证明: by
  rw [Fin.natCast_eq_last]
  exact Fin.le_last i

Depends on / 依赖: Fin.le_last, Fin.natCast_eq_last, le_last, natCast_eq_last
-/
theorem le_val_last (i : Fin (n + 1)) : i <= n := by
  rw [Fin.natCast_eq_last]
  exact Fin.le_last i

variable {a b : Nat}

/--
lemma `natCast_le_natCast` / 引理 `natCast_le_natCast`

English:
lemma natCast_le_natCast
  given: (han : a <= n) (hbn : b <= n)
  statement: (a : Fin (n + 1)) <= b ↔ a <= b
  proof: by
  rw [← Nat.lt_succ_iff] at han hbn
  simp [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, han, hbn]

中文:
引理 natCast_le_natCast
  条件: (han : a <= n) (hbn : b <= n)
  结论: (a : Fin (n + 1)) <= b ↔ a <= b
  证明: by
  rw [← Nat.lt_succ_iff] at han hbn
  simp [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, han, hbn]

Depends on / 依赖: Nat.lt_succ_iff, Nat.mod_eq_of_lt, le_iff_val_le_val, lt_succ_iff, mod_eq_of_lt, val_fin_le
-/
lemma natCast_le_natCast (han : a <= n) (hbn : b <= n) : (a : Fin (n + 1)) <= b ↔ a <= b := by
  rw [← Nat.lt_succ_iff] at han hbn
  simp [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, han, hbn]

/--
lemma `natCast_lt_natCast` / 引理 `natCast_lt_natCast`

English:
lemma natCast_lt_natCast
  given: (han : a <= n) (hbn : b <= n)
  statement: (a : Fin (n + 1)) < b ↔ a < b
  proof: by
  rw [← Nat.lt_succ_iff] at han hbn; simp [lt_def, Nat.mod_eq_of_lt, han, hbn]

中文:
引理 natCast_lt_natCast
  条件: (han : a <= n) (hbn : b <= n)
  结论: (a : Fin (n + 1)) < b ↔ a < b
  证明: by
  rw [← Nat.lt_succ_iff] at han hbn; simp [lt_def, Nat.mod_eq_of_lt, han, hbn]

Depends on / 依赖: Nat.lt_succ_iff, Nat.mod_eq_of_lt, lt_def, lt_succ_iff, mod_eq_of_lt
-/
lemma natCast_lt_natCast (han : a <= n) (hbn : b <= n) : (a : Fin (n + 1)) < b ↔ a < b := by
  rw [← Nat.lt_succ_iff] at han hbn; simp [lt_def, Nat.mod_eq_of_lt, han, hbn]

/--
lemma `natCast_mono` / 引理 `natCast_mono`

English:
lemma natCast_mono
  given: (hbn : b <= n) (hab : a <= b)
  statement: (a : Fin (n + 1)) <= b
  proof: (natCast_le_natCast (hab.trans hbn) hbn).2 hab

中文:
引理 natCast_mono
  条件: (hbn : b <= n) (hab : a <= b)
  结论: (a : Fin (n + 1)) <= b
  证明: (natCast_le_natCast (hab.trans hbn) hbn).2 hab

Depends on / 依赖: hab.trans, natCast_le_natCast
-/
lemma natCast_mono (hbn : b <= n) (hab : a <= b) : (a : Fin (n + 1)) <= b :=
  (natCast_le_natCast (hab.trans hbn) hbn).2 hab

/--
lemma `natCast_strictMono` / 引理 `natCast_strictMono`

English:
lemma natCast_strictMono
  given: (hbn : b <= n) (hab : a < b)
  statement: (a : Fin (n + 1)) < b
  proof: (natCast_lt_natCast (hab.le.trans hbn) hbn).2 hab

@[simp]

中文:
引理 natCast_strictMono
  条件: (hbn : b <= n) (hab : a < b)
  结论: (a : Fin (n + 1)) < b
  证明: (natCast_lt_natCast (hab.le.trans hbn) hbn).2 hab

@[simp]

Depends on / 依赖: hab.le.trans, natCast_lt_natCast
-/
lemma natCast_strictMono (hbn : b <= n) (hab : a < b) : (a : Fin (n + 1)) < b :=
  (natCast_lt_natCast (hab.le.trans hbn) hbn).2 hab

@[simp]
/--
lemma `castLE_natCast` / 引理 `castLE_natCast`

English:
lemma castLE_natCast
  given: {m n : Nat} [NeZero m] (h : m <= n) (a : Nat)
  proof: ⟨Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le m.pos_of_neZero h)⟩
    Fin.castLE h (a.cast : Fin m) = (a % m : Nat) := by
  ext
  simp only [val_castLE, val_natCast]
  rw [Nat.mod_eq_of_lt (a := a % m) (lt_of_lt_of_le (Nat.mod_lt _ m.pos_of_neZero) h)]

中文:
引理 castLE_natCast
  条件: {m n : 自然数} [NeZero m] (h : m <= n) (a : 自然数)
  证明: ⟨Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le m.pos_of_neZero h)⟩
    Fin.castLE h (a.cast : Fin m) = (a % m : Nat) := by
  ext
  simp only [val_castLE, val_natCast]
  rw [Nat.mod_eq_of_lt (a := a % m) (lt_of_lt_of_le (Nat.mod_lt _ m.pos_of_neZero) h)]

Depends on / 依赖: Nat.pos_iff_ne_zero.mp, lt_of_lt_of_le, m.pos_of_neZero, pos_iff_ne_zero, pos_of_neZero
-/
lemma castLE_natCast {m n : Nat} [NeZero m] (h : m <= n) (a : Nat) :
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le m.pos_of_neZero h)⟩
    Fin.castLE h (a.cast : Fin m) = (a % m : Nat) := by
  ext
  simp only [val_castLE, val_natCast]
  rw [Nat.mod_eq_of_lt (a := a % m) (lt_of_lt_of_le (Nat.mod_lt _ m.pos_of_neZero) h)]

end OfNatCoe

end Add

section DivMod

/--
theorem `modNat_rev` / 定理 `modNat_rev`

English:
theorem modNat_rev
  given: (i : Fin (m * n))
  statement: i.rev.modNat = i.modNat.rev
  proof: by
  ext
  have H₁ : i % n + 1 <= n := i.modNat.is_lt
  have H₂ : i / n < m := i.divNat.is_lt
  simp only [val_rev]
  calc
    (m * n - (i + 1)) % n = (m * n - ((i / n) * n + i % n + 1)) % n := by rw [Nat.div_add_mod']
    _ = ((m - i / n - 1) * n + (n - (i % n + 1))) % n := by
      rw [Nat.mul_sub

中文:
定理 modNat_rev
  条件: (i : Fin (m * n))
  结论: i.rev.mod自然数 = i.mod自然数.rev
  证明: by
  ext
  have H₁ : i % n + 1 <= n := i.modNat.is_lt
  have H₂ : i / n < m := i.divNat.is_lt
  simp only [val_rev]
  calc
    (m * n - (i + 1)) % n = (m * n - ((i / n) * n + i % n + 1)) % n := by rw [Nat.div_add_mod']
    _ = ((m - i / n - 1) * n + (n - (i % n + 1))) % n := by
      rw [Nat.mul_sub

Depends on / 依赖: Nat.add_assoc, Nat.div_add_mod, Nat.le_mul_of_pos_left, Nat.le_sub_of_add_le, Nat.mul_sub_right_distrib, Nat.one_mul, Nat.sub_add_sub_cancel, Nat.sub_sub, add_assoc, divNat, div_add_mod, i.divNat.is_lt, i.modNat.is_lt, is_lt, le_mul_of_pos_left, le_sub_of_add_le, modNat, mul_sub_right_distrib, one_mul, sub_add_sub_cancel
-/
theorem modNat_rev (i : Fin (m * n)) : i.rev.modNat = i.modNat.rev := by
  ext
  have H₁ : i % n + 1 <= n := i.modNat.is_lt
  have H₂ : i / n < m := i.divNat.is_lt
  simp only [val_rev]
  calc
    (m * n - (i + 1)) % n = (m * n - ((i / n) * n + i % n + 1)) % n := by rw [Nat.div_add_mod']
    _ = ((m - i / n - 1) * n + (n - (i % n + 1))) % n := by
      rw [Nat.mul_sub_right_distrib]; rw [Nat.one_mul]; rw [Nat.sub_add_sub_cancel _ H₁]; rw [Nat.mul_sub_right_distrib]; rw [Nat.sub_sub]; rw [Nat.add_assoc]
exact Nat.le_mul_of_pos_left _ Nat.le_sub_of_add_le' H₂
    _ = n - (i % n + 1) := by
      rw [Nat.mul_comm]; rw [Nat.mul_add_mod]; rw [Nat.mod_eq_of_lt]; exact i.modNat.rev.is_lt

end DivMod

section Rec

/-!
### recursion and induction principles
-/

@[elab_as_elim]
/--
lemma `strong_induction_on` / 引理 `strong_induction_on`

English:
lemma strong_induction_on
  statement: {n : Nat} {motive : Fin n -> Prop}
  proof: by
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | h j hj => exact h _ (fun ⟨k, hk₁⟩ hk₂ => hj _ hk₂ hk₁)

中文:
引理 strong_induction_on
  结论: {n : 自然数} {motive : Fin n -> 命题}
  证明: by
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | h j hj => exact h _ (fun ⟨k, hk₁⟩ hk₂ => hj _ hk₂ hk₁)

Depends on / 依赖: Nat.strong_induction_on, strong_induction_on
-/
lemma strong_induction_on {n : Nat} {motive : Fin n -> Prop}
    (h : forall (j : Fin n) (_ : forall (k : Fin n), k < j -> motive k), motive j) (i : Fin n) :
    motive i := by
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | h j hj => exact h _ (fun ⟨k, hk₁⟩ hk₂ => hj _ hk₂ hk₁)

end Rec

open scoped Relator in
/--
theorem `liftFun_iff_succ` / 定理 `liftFun_iff_succ`

English:
theorem liftFun_iff_succ
  given: {α : Type*} (r : α -> α -> Prop) [IsTrans α r] {f : Fin (n + 1) -> α}
  proof: by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine fun H i => Fin.induction (fun h => ?_) ?_
    · simp at h
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      obtain hij | hij := (le_def.1 hij).eq_or_lt
      · obtain rfl := Fin.ext hij
        exact H _
      · e

中文:
定理 liftFun_iff_succ
  条件: {α : 类型} (r : α -> α -> 命题) [IsTrans α r] {f : Fin (n + 1) -> α}
  证明: by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine fun H i => Fin.induction (fun h => ?_) ?_
    · simp at h
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      obtain hij | hij := (le_def.1 hij).eq_or_lt
      · obtain rfl := Fin.ext hij
        exact H _
      · e

Depends on / 依赖: Fin.ext, Fin.induction, _root_, _root_.trans, castSucc_lt_succ, eq_or_lt, i.castSucc_lt_succ, le_castSucc_iff, le_def
-/
theorem liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) [IsTrans α r] {f : Fin (n + 1) -> α} :
    ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (f (castSucc i)) (f i.succ) := by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine fun H i => Fin.induction (fun h => ?_) ?_
    · simp at h
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      obtain hij | hij := (le_def.1 hij).eq_or_lt
      · obtain rfl := Fin.ext hij
        exact H _
      · exact _root_.trans (ihj hij) (H j)

section AddGroup

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: (n : Fin 1)
  statement: n = 0
  proof: Subsingleton.elim _ _

中文:
定理 eq_zero
  条件: (n : Fin 1)
  结论: n = 0
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem eq_zero (n : Fin 1) : n = 0 := Subsingleton.elim _ _

/--
lemma `eq_one_of_ne_zero` / 引理 `eq_one_of_ne_zero`

English:
lemma eq_one_of_ne_zero
  given: (i : Fin 2) (hi : i != 0)
  statement: i = 1
  proof: by lia

@[simp]

中文:
引理 eq_one_of_ne_zero
  条件: (i : Fin 2) (hi : i != 0)
  结论: i = 1
  证明: by lia

@[simp]
-/
lemma eq_one_of_ne_zero (i : Fin 2) (hi : i != 0) : i = 1 := by lia

@[simp]
/--
theorem `coe_neg_one` / 定理 `coe_neg_one`

English:
theorem coe_neg_one
  statement: ↑(-1 : Fin (n + 1)) = n
  proof: by
  cases n
  · simp
  rw [Fin.val_neg']; rw [Fin.val_one]; rw [Nat.add_one_sub_one]; rw [Nat.mod_eq_of_lt]
  constructor

中文:
定理 coe_neg_one
  结论: ↑(-1 : Fin (n + 1)) = n
  证明: by
  cases n
  · simp
  rw [Fin.val_neg']; rw [Fin.val_one]; rw [Nat.add_one_sub_one]; rw [Nat.mod_eq_of_lt]
  constructor

Depends on / 依赖: Fin.val_neg, Fin.val_one, Nat.add_one_sub_one, Nat.mod_eq_of_lt, add_one_sub_one, mod_eq_of_lt, val_neg, val_one
-/
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.val_neg']; rw [Fin.val_one]; rw [Nat.add_one_sub_one]; rw [Nat.mod_eq_of_lt]
  constructor

/--
theorem `last_sub` / 定理 `last_sub`

English:
theorem last_sub
  given: (i : Fin (n + 1))
  statement: last n - i = Fin.rev i
  proof: Fin.ext by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]

中文:
定理 last_sub
  条件: (i : Fin (n + 1))
  结论: last n - i = Fin.rev i
  证明: Fin.ext by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]

Depends on / 依赖: Fin.ext, Nat.succ_sub_succ_eq_sub, coe_sub_iff_le, i.le_last, le_last, succ_sub_succ_eq_sub, val_last, val_rev
-/
theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
Fin.ext by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]

/--
theorem `add_one_le_of_lt` / 定理 `add_one_le_of_lt`

English:
theorem add_one_le_of_lt
  given: {n : Nat} {a b : Fin (n + 1)} (h : a < b)
  statement: a + 1 <= b
  proof: by
  cases n <;> fin_omega

中文:
定理 add_one_le_of_lt
  条件: {n : 自然数} {a b : Fin (n + 1)} (h : a < b)
  结论: a + 1 <= b
  证明: by
  cases n <;> fin_omega

Depends on / 依赖: fin_omega
-/
theorem add_one_le_of_lt {n : Nat} {a b : Fin (n + 1)} (h : a < b) : a + 1 <= b := by
  cases n <;> fin_omega

/--
theorem `exists_eq_add_of_le` / 定理 `exists_eq_add_of_le`

English:
theorem exists_eq_add_of_le
  given: {n : Nat} {a b : Fin n} (h : a <= b)
  statement: exists k <= b, b = a + k
  proof: by
  obtain ⟨k, hk⟩ : exists k : Nat, (b : Nat) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k <= b := by lia
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

中文:
定理 exists_eq_add_of_le
  条件: {n : 自然数} {a b : Fin n} (h : a <= b)
  结论: 存在 k <= b, b = a + k
  证明: by
  obtain ⟨k, hk⟩ : exists k : Nat, (b : Nat) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k <= b := by lia
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

Depends on / 依赖: Fin.ext_iff, Fin.val_add, Nat.exists_eq_add_of_le, Nat.mod_eq_of_lt, b.is_lt, exists_eq_add_of_le, ext_iff, hkb.trans_lt, is_lt, mod_eq_of_lt, trans_lt, val_add
-/
theorem exists_eq_add_of_le {n : Nat} {a b : Fin n} (h : a <= b) : exists k <= b, b = a + k := by
  obtain ⟨k, hk⟩ : exists k : Nat, (b : Nat) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k <= b := by lia
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

/--
theorem `exists_eq_add_of_lt` / 定理 `exists_eq_add_of_lt`

English:
theorem exists_eq_add_of_lt
  given: {n : Nat} {a b : Fin (n + 1)} (h : a < b)
  proof: by
  cases n
  · lia
  obtain ⟨k, hk⟩ : exists k : Nat, (b : Nat) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by lia
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, by fin_omega, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

中文:
定理 exists_eq_add_of_lt
  条件: {n : 自然数} {a b : Fin (n + 1)} (h : a < b)
  证明: by
  cases n
  · lia
  obtain ⟨k, hk⟩ : exists k : Nat, (b : Nat) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by lia
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, by fin_omega, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

Depends on / 依赖: Fin.ext_iff, Fin.val_add, Nat.exists_eq_add_of_lt, Nat.mod_eq_of_lt, b.is_lt, exists_eq_add_of_lt, ext_iff, fin_omega, hkb.trans, is_lt, mod_eq_of_lt, val_add
-/
theorem exists_eq_add_of_lt {n : Nat} {a b : Fin (n + 1)} (h : a < b) :
    exists k < b, k + 1 <= b ∧ b = a + k + 1 := by
  cases n
  · lia
  obtain ⟨k, hk⟩ : exists k : Nat, (b : Nat) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by lia
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, by fin_omega, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

/--
lemma `pos_of_ne_zero` / 引理 `pos_of_ne_zero`

English:
lemma pos_of_ne_zero
  given: {n : Nat} {a : Fin (n + 1)} (h : a != 0)
  statement: 0 < a
  proof: Nat.pos_of_ne_zero (val_ne_of_ne h)

中文:
引理 pos_of_ne_zero
  条件: {n : 自然数} {a : Fin (n + 1)} (h : a != 0)
  结论: 0 < a
  证明: Nat.pos_of_ne_zero (val_ne_of_ne h)

Depends on / 依赖: Nat.pos_of_ne_zero, pos_of_ne_zero, val_ne_of_ne
-/
lemma pos_of_ne_zero {n : Nat} {a : Fin (n + 1)} (h : a != 0) : 0 < a :=
  Nat.pos_of_ne_zero (val_ne_of_ne h)

/--
lemma `sub_succ_le_sub_of_le` / 引理 `sub_succ_le_sub_of_le`

English:
lemma sub_succ_le_sub_of_le
  given: {n : Nat} {u v : Fin (n + 2)} (h : u < v)
  statement: v - (u + 1) < v - u
  proof: by
  fin_omega

中文:
引理 sub_succ_le_sub_of_le
  条件: {n : 自然数} {u v : Fin (n + 2)} (h : u < v)
  结论: v - (u + 1) < v - u
  证明: by
  fin_omega

Depends on / 依赖: fin_omega
-/
lemma sub_succ_le_sub_of_le {n : Nat} {u v : Fin (n + 2)} (h : u < v) : v - (u + 1) < v - u := by
  fin_omega

end AddGroup

open Fin.NatCast in
@[simp]
/--
theorem `coe_natCast_eq_mod` / 定理 `coe_natCast_eq_mod`

English:
theorem coe_natCast_eq_mod
  given: (m n : Nat) [NeZero m]
  proof: rfl

@[simp]

中文:
定理 coe_natCast_eq_mod
  条件: (m n : 自然数) [NeZero m]
  证明: rfl

@[simp]
-/
theorem coe_natCast_eq_mod (m n : Nat) [NeZero m] :
    ((n : Fin m) : Nat) = n % m :=
  rfl

@[simp]
/--
theorem `coe_ofNat_eq_mod` / 定理 `coe_ofNat_eq_mod`

English:
theorem coe_ofNat_eq_mod
  given: (m n : Nat) [NeZero m]
  proof: rfl

中文:
定理 coe_ofNat_eq_mod
  条件: (m n : 自然数) [NeZero m]
  证明: rfl
-/
theorem coe_ofNat_eq_mod (m n : Nat) [NeZero m] :
    ((ofNat(n) : Fin m) : Nat) = ofNat(n) % m :=
  rfl

/--
theorem `val_add_one_of_lt'` / 定理 `val_add_one_of_lt'`

English:
theorem val_add_one_of_lt'
  given: {n : Nat} {i : Fin n} (h : i + 1 < n)
  proof: i.neZero
    (i + 1).val = i.val + 1 := by
  simpa [add_def] using Nat.mod_eq_of_lt (by lia)

中文:
定理 val_add_one_of_lt'
  条件: {n : 自然数} {i : Fin n} (h : i + 1 < n)
  证明: i.neZero
    (i + 1).val = i.val + 1 := by
  simpa [add_def] using Nat.mod_eq_of_lt (by lia)

Depends on / 依赖: i.neZero, neZero
-/
theorem val_add_one_of_lt' {n : Nat} {i : Fin n} (h : i + 1 < n) :
    haveI := i.neZero
    (i + 1).val = i.val + 1 := by
  simpa [add_def] using Nat.mod_eq_of_lt (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: n] [NeZero ofNat(m)] : NeZero (ofNat(m)
  body: by
  suffices m % (n + m) = m by simpa [neZero_iff, Fin.ext_iff, OfNat.ofNat, this] using! NeZero.ne m
  apply Nat.mod_eq_of_lt
  simpa using! zero_lt_of_ne_zero (NeZero.ne n)

中文:
实例 [NeZero
  签名: n] [NeZero of自然数(m)] : NeZero (of自然数(m)
  定义体: by
  suffices m % (n + m) = m by simpa [neZero_iff, Fin.ext_iff, OfNat.ofNat, this] using! NeZero.ne m
  apply Nat.mod_eq_of_lt
  simpa using! zero_lt_of_ne_zero (NeZero.ne n)

Depends on / 依赖: Fin.ext_iff, Nat.mod_eq_of_lt, NeZero, NeZero.ne, OfNat.ofNat, ext_iff, mod_eq_of_lt, neZero_iff, zero_lt_of_ne_zero
-/
instance [NeZero n] [NeZero ofNat(m)] : NeZero (ofNat(m) : Fin (n + ofNat(m))) := by
  suffices m % (n + m) = m by simpa [neZero_iff, Fin.ext_iff, OfNat.ofNat, this] using! NeZero.ne m
  apply Nat.mod_eq_of_lt
  simpa using! zero_lt_of_ne_zero (NeZero.ne n)

section Mul

/-!
### mul
-/

end Mul

end Fin
