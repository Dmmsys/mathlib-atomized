/-
Copyright (c) 2022 Siddhartha Prasad, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Kleene algebras

This file defines idempotent semirings and Kleene algebras, which are used extensively in the theory
of computation.

An idempotent semiring is a semiring whose addition is idempotent. An idempotent semiring is
naturally a semilattice by setting `a ≤ b` if `a + b = b`.

A Kleene algebra is an idempotent semiring equipped with an additional unary operator `∗`, the
Kleene star, such that (informally) `a∗ = 1 + a + a * a + a * a * a + ...`

## Main declarations

* `IdemSemiring`: Idempotent semiring
* `IdemCommSemiring`: Idempotent commutative semiring
* `KleeneAlgebra`: Kleene algebra

## Notation

`a∗` is notation for `kstar a` in scope `Computability`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
  [kozen1994]
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleene_algebra

## TODO

Instances for `AddOpposite`, `MulOpposite`, `ULift`, `Subsemiring`, `Subring`, `Subalgebra`.

## Tags

kleene algebra, idempotent semiring
-/

@[expose] public section

open Function

variable {α β ι : Type*} {π : ι -> Type*}

/--
Definition of `IdemSemiring` / `IdemSemiring` 的定义

English:
class IdemSemiring
  parameters: (α : Type*)
  extends: Semiring α, SemilatticeSup α, OrderBot α
  axioms and operations (1):
    - add_eq_sup((a b : α)) : a + b = a ⊔ b  [default: by intros; rfl]

中文:
类 IdemSemiring
  参数: (α : 类型)
  继承: 半环 α, SemilatticeSup α, 有底序 α
  公理与运算 (1 个):
    - add_eq_sup((a b : α)) : a + b = a ⊔ b  [默认: by intros; rfl]

Depends on / 依赖: intros
-/
class IdemSemiring (α : Type*) extends Semiring α, SemilatticeSup α, OrderBot α where
  protected add_eq_sup (a b : α) : a + b = a ⊔ b := by intros; rfl

/--
Definition of `IdemCommSemiring` / `IdemCommSemiring` 的定义

English:
class IdemCommSemiring
  parameters: (α : Type*)
  extends: CommSemiring α, IdemSemiring α
  (no additional axioms)

中文:
类 IdemCommSemiring
  参数: (α : 类型)
  继承: 交换半环 α, IdemSemiring α
  (无附加公理)
-/
class IdemCommSemiring (α : Type*) extends CommSemiring α, IdemSemiring α

/--
Definition of `KStar` / `KStar` 的定义

English:
class KStar
  parameters: (α : Type*)
  axioms and operations (1):
    - kstar : α -> α

中文:
类 KStar
  参数: (α : 类型)
  公理与运算 (1 个):
    - kstar : α -> α
-/
class KStar (α : Type*) where
  /-- The Kleene star operator on a Kleene algebra -/
  protected kstar : α -> α

@[inherit_doc] scoped[Computability] postfix:1024 "∗" => KStar.kstar

open Computability

/--
Definition of `KleeneAlgebra` / `KleeneAlgebra` 的定义

English:
class KleeneAlgebra
  parameters: (α : Type*)
  extends: IdemSemiring α, KStar α
  axioms and operations (5):
    - one_le_kstar((a : α)) : 1 <= a∗
    - mul_kstar_le_kstar((a : α)) : a * a∗ <= a∗
    - kstar_mul_le_kstar((a : α)) : a∗ * a <= a∗
    - mul_kstar_le_self((a b : α)) : b * a <= b -> b * a∗ <= b
    - kstar_mul_le_self((a b : α)) : a * b <= b -> a∗ * b <= b

中文:
类 Kleene代数
  参数: (α : 类型)
  继承: IdemSemiring α, KStar α
  公理与运算 (5 个):
    - one_le_kstar((a : α)) : 1 <= a∗
    - mul_kstar_le_kstar((a : α)) : a * a∗ <= a∗
    - kstar_mul_le_kstar((a : α)) : a∗ * a <= a∗
    - mul_kstar_le_self((a b : α)) : b * a <= b -> b * a∗ <= b
    - kstar_mul_le_self((a b : α)) : a * b <= b -> a∗ * b <= b
-/
class KleeneAlgebra (α : Type*) extends IdemSemiring α, KStar α where
  protected one_le_kstar (a : α) : 1 <= a∗
  protected mul_kstar_le_kstar (a : α) : a * a∗ <= a∗
  protected kstar_mul_le_kstar (a : α) : a∗ * a <= a∗
  protected mul_kstar_le_self (a b : α) : b * a <= b -> b * a∗ <= b
  protected kstar_mul_le_self (a b : α) : a * b <= b -> a∗ * b <= b

-- See note [reducible non-instances]
/--
Definition of `IdemSemiring.ofSemiring` / `IdemSemiring.ofSemiring` 的定义

English:
abbreviation IdemSemiring.ofSemiring
  signature: [Semiring α] (h : forall a : α, a + a = a)
  body: a + b = b
  le_refl := h
  le_trans a b c hab hbc := by rw [← hbc, ← add_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, add_comm]
  sup := (· + ·)
  le_sup_left a b := by rw [← add_assoc, h]
  le_sup_right a b := by rw [add_comm, add_assoc, h]
  sup_le a b c hab hbc := by rwa [add_assoc, hb

中文:
缩写 IdemSemiring.ofSemiring
  签名: [半环 α] (h : 对任意 a : α, a + a = a)
  定义体: a + b = b
  le_refl := h
  le_trans a b c hab hbc := by rw [← hbc, ← add_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, add_comm]
  sup := (· + ·)
  le_sup_left a b := by rw [← add_assoc, h]
  le_sup_right a b := by rw [add_comm, add_assoc, h]
  sup_le a b c hab hbc := by rwa [add_assoc, hb
-/
abbrev IdemSemiring.ofSemiring [Semiring α] (h : forall a : α, a + a = a) : IdemSemiring α where
  le a b := a + b = b
  le_refl := h
  le_trans a b c hab hbc := by rw [← hbc, ← add_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, add_comm]
  sup := (· + ·)
  le_sup_left a b := by rw [← add_assoc, h]
  le_sup_right a b := by rw [add_comm, add_assoc, h]
  sup_le a b c hab hbc := by rwa [add_assoc, hbc]
  bot := 0
  bot_le := zero_add

section IdemSemiring

variable [IdemSemiring α] {a b c : α}

/--
theorem `add_eq_sup` / 定理 `add_eq_sup`

English:
theorem add_eq_sup
  given: (a b : α)
  statement: a + b = a ⊔ b
  proof: IdemSemiring.add_eq_sup _ _

scoped[Computability] attribute [simp] add_eq_sup

中文:
定理 add_eq_sup
  条件: (a b : α)
  结论: a + b = a ⊔ b
  证明: IdemSemiring.add_eq_sup _ _

scoped[Computability] attribute [simp] add_eq_sup

Depends on / 依赖: IdemSemiring, IdemSemiring.add_eq_sup, add_eq_sup
-/
theorem add_eq_sup (a b : α) : a + b = a ⊔ b :=
  IdemSemiring.add_eq_sup _ _

scoped[Computability] attribute [simp] add_eq_sup

/--
theorem `add_idem` / 定理 `add_idem`

English:
theorem add_idem
  given: (a : α)
  statement: a + a = a
  proof: by simp

中文:
定理 add_idem
  条件: (a : α)
  结论: a + a = a
  证明: by simp
-/
theorem add_idem (a : α) : a + a = a := by simp

/--
lemma `natCast_eq_one` / 引理 `natCast_eq_one`

English:
lemma natCast_eq_one
  given: {n : Nat} (nezero : n != 0)
  statement: (n : α) = 1
  proof: by
  rw [← Nat.one_le_iff_ne_zero] at nezero
  induction n, nezero using Nat.le_induction with
  | base => exact Nat.cast_one
  | succ x _ hx => rw [Nat.cast_add, hx, Nat.cast_one, add_idem 1]

中文:
引理 natCast_eq_one
  条件: {n : 自然数} (nezero : n != 0)
  结论: (n : α) = 1
  证明: by
  rw [← Nat.one_le_iff_ne_zero] at nezero
  induction n, nezero using Nat.le_induction with
  | base => exact Nat.cast_one
  | succ x _ hx => rw [Nat.cast_add, hx, Nat.cast_one, add_idem 1]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Nat.le_induction, Nat.one_le_iff_ne_zero, add_idem, cast_add, cast_one, le_induction, nezero, one_le_iff_ne_zero
-/
lemma natCast_eq_one {n : Nat} (nezero : n != 0) : (n : α) = 1 := by
  rw [← Nat.one_le_iff_ne_zero] at nezero
  induction n, nezero using Nat.le_induction with
  | base => exact Nat.cast_one
  | succ x _ hx => rw [Nat.cast_add, hx, Nat.cast_one, add_idem 1]

/--
lemma `ofNat_eq_one` / 引理 `ofNat_eq_one`

English:
lemma ofNat_eq_one
  given: {n : Nat} [n.AtLeastTwo]
  statement: (ofNat(n) : α) = 1
  proof: natCast_eq_one Nat.ne_zero_of_lt Nat.AtLeastTwo.prop

中文:
引理 of自然数_eq_one
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: (of自然数(n) : α) = 1
  证明: natCast_eq_one Nat.ne_zero_of_lt Nat.AtLeastTwo.prop

Depends on / 依赖: AtLeastTwo, Nat.AtLeastTwo.prop, Nat.ne_zero_of_lt, natCast_eq_one, ne_zero_of_lt
-/
lemma ofNat_eq_one {n : Nat} [n.AtLeastTwo] : (ofNat(n) : α) = 1 :=
natCast_eq_one Nat.ne_zero_of_lt Nat.AtLeastTwo.prop

/--
theorem `nsmul_eq_self` / 定理 `nsmul_eq_self`

English:
theorem nsmul_eq_self
  statement: forall {n : Nat} (_ : n != 0) (a : α), n • a = a

中文:
定理 nsmul_eq_self
  结论: 对任意 {n : 自然数} (_ : n != 0) (a : α), n • a = a
-/
theorem nsmul_eq_self : forall {n : Nat} (_ : n != 0) (a : α), n • a = a
  | 0, h => (h rfl).elim
  | 1, _ => one_nsmul
  | n + 2, _ => fun a => by rw [succ_nsmul, nsmul_eq_self n.succ_ne_zero, add_idem]

/--
theorem `add_eq_left_iff_le` / 定理 `add_eq_left_iff_le`

English:
theorem add_eq_left_iff_le
  statement: a + b = a ↔ b <= a
  proof: by simp

中文:
定理 add_eq_left_iff_le
  结论: a + b = a ↔ b <= a
  证明: by simp
-/
theorem add_eq_left_iff_le : a + b = a ↔ b <= a := by simp

/--
theorem `add_eq_right_iff_le` / 定理 `add_eq_right_iff_le`

English:
theorem add_eq_right_iff_le
  statement: a + b = b ↔ a <= b
  proof: by simp

alias ⟨_, LE.le.add_eq_left⟩ := add_eq_left_iff_le

alias ⟨_, LE.le.add_eq_right⟩ := add_eq_right_iff_le

中文:
定理 add_eq_right_iff_le
  结论: a + b = b ↔ a <= b
  证明: by simp

alias ⟨_, LE.le.add_eq_left⟩ := add_eq_left_iff_le

alias ⟨_, LE.le.add_eq_right⟩ := add_eq_right_iff_le
-/
theorem add_eq_right_iff_le : a + b = b ↔ a <= b := by simp

alias ⟨_, LE.le.add_eq_left⟩ := add_eq_left_iff_le

alias ⟨_, LE.le.add_eq_right⟩ := add_eq_right_iff_le

/--
theorem `add_le_iff` / 定理 `add_le_iff`

English:
theorem add_le_iff
  statement: a + b <= c ↔ a <= c ∧ b <= c
  proof: by simp

中文:
定理 add_le_iff
  结论: a + b <= c ↔ a <= c ∧ b <= c
  证明: by simp
-/
theorem add_le_iff : a + b <= c ↔ a <= c ∧ b <= c := by simp

/--
theorem `add_le` / 定理 `add_le`

English:
theorem add_le
  given: (ha : a <= c) (hb : b <= c)
  statement: a + b <= c
  proof: add_le_iff.2 ⟨ha, hb⟩

中文:
定理 add_le
  条件: (ha : a <= c) (hb : b <= c)
  结论: a + b <= c
  证明: add_le_iff.2 ⟨ha, hb⟩

Depends on / 依赖: add_le_iff
-/
theorem add_le (ha : a <= c) (hb : b <= c) : a + b <= c :=
  add_le_iff.2 ⟨ha, hb⟩

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toIsOrderedAddMonoid : IsOrderedAddMonoid α where
  add_le_add_left a b hbc c := by
    simp_rw [add_eq_sup]
    grw [hbc]

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toCanonicallyOrderedAdd : CanonicallyOrderedAdd α where
  exists_add_of_le h := ⟨_, h.add_eq_right.symm⟩
le_add_self a b := add_eq_left_iff_le.1 by rw [add_assoc, add_idem]
le_self_add a b := add_eq_right_iff_le.1 by rw [← add_assoc, add_idem]

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toMulLeftMono : MulLeftMono α where
elim a b c hbc := add_eq_left_iff_le.1 by rw [← mul_add, hbc.add_eq_left]

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toMulRightMono : MulRightMono α where
elim a b c hbc := add_eq_left_iff_le.1 by rw [← add_mul, hbc.add_eq_left]

end IdemSemiring

section KleeneAlgebra

variable [KleeneAlgebra α] {a b c : α}

@[simp]
/--
theorem `one_le_kstar` / 定理 `one_le_kstar`

English:
theorem one_le_kstar
  statement: 1 <= a∗
  proof: KleeneAlgebra.one_le_kstar _

中文:
定理 one_le_kstar
  结论: 1 <= a∗
  证明: KleeneAlgebra.one_le_kstar _

Depends on / 依赖: KleeneAlgebra, KleeneAlgebra.one_le_kstar, one_le_kstar
-/
theorem one_le_kstar : 1 <= a∗ :=
  KleeneAlgebra.one_le_kstar _

/--
theorem `mul_kstar_le_kstar` / 定理 `mul_kstar_le_kstar`

English:
theorem mul_kstar_le_kstar
  statement: a * a∗ <= a∗
  proof: KleeneAlgebra.mul_kstar_le_kstar _

中文:
定理 mul_kstar_le_kstar
  结论: a * a∗ <= a∗
  证明: KleeneAlgebra.mul_kstar_le_kstar _

Depends on / 依赖: KleeneAlgebra, KleeneAlgebra.mul_kstar_le_kstar, mul_kstar_le_kstar
-/
theorem mul_kstar_le_kstar : a * a∗ <= a∗ :=
  KleeneAlgebra.mul_kstar_le_kstar _

/--
theorem `kstar_mul_le_kstar` / 定理 `kstar_mul_le_kstar`

English:
theorem kstar_mul_le_kstar
  statement: a∗ * a <= a∗
  proof: KleeneAlgebra.kstar_mul_le_kstar _

中文:
定理 kstar_mul_le_kstar
  结论: a∗ * a <= a∗
  证明: KleeneAlgebra.kstar_mul_le_kstar _

Depends on / 依赖: KleeneAlgebra, KleeneAlgebra.kstar_mul_le_kstar, kstar_mul_le_kstar
-/
theorem kstar_mul_le_kstar : a∗ * a <= a∗ :=
  KleeneAlgebra.kstar_mul_le_kstar _

/--
theorem `mul_kstar_le_self` / 定理 `mul_kstar_le_self`

English:
theorem mul_kstar_le_self
  statement: b * a <= b -> b * a∗ <= b
  proof: KleeneAlgebra.mul_kstar_le_self _ _

中文:
定理 mul_kstar_le_self
  结论: b * a <= b -> b * a∗ <= b
  证明: KleeneAlgebra.mul_kstar_le_self _ _

Depends on / 依赖: KleeneAlgebra, KleeneAlgebra.mul_kstar_le_self, mul_kstar_le_self
-/
theorem mul_kstar_le_self : b * a <= b -> b * a∗ <= b :=
  KleeneAlgebra.mul_kstar_le_self _ _

/--
theorem `kstar_mul_le_self` / 定理 `kstar_mul_le_self`

English:
theorem kstar_mul_le_self
  statement: a * b <= b -> a∗ * b <= b
  proof: KleeneAlgebra.kstar_mul_le_self _ _

中文:
定理 kstar_mul_le_self
  结论: a * b <= b -> a∗ * b <= b
  证明: KleeneAlgebra.kstar_mul_le_self _ _

Depends on / 依赖: KleeneAlgebra, KleeneAlgebra.kstar_mul_le_self, kstar_mul_le_self
-/
theorem kstar_mul_le_self : a * b <= b -> a∗ * b <= b :=
  KleeneAlgebra.kstar_mul_le_self _ _

/--
theorem `mul_kstar_le` / 定理 `mul_kstar_le`

English:
theorem mul_kstar_le
  given: (hb : b <= c) (ha : c * a <= c)
  statement: b * a∗ <= c
  proof: by grw [hb, mul_kstar_le_self ha]

中文:
定理 mul_kstar_le
  条件: (hb : b <= c) (ha : c * a <= c)
  结论: b * a∗ <= c
  证明: by grw [hb, mul_kstar_le_self ha]

Depends on / 依赖: mul_kstar_le_self
-/
theorem mul_kstar_le (hb : b <= c) (ha : c * a <= c) : b * a∗ <= c := by grw [hb, mul_kstar_le_self ha]

/--
theorem `kstar_mul_le` / 定理 `kstar_mul_le`

English:
theorem kstar_mul_le
  given: (hb : b <= c) (ha : a * c <= c)
  statement: a∗ * b <= c
  proof: by grw [hb, kstar_mul_le_self ha]

中文:
定理 kstar_mul_le
  条件: (hb : b <= c) (ha : a * c <= c)
  结论: a∗ * b <= c
  证明: by grw [hb, kstar_mul_le_self ha]

Depends on / 依赖: kstar_mul_le_self
-/
theorem kstar_mul_le (hb : b <= c) (ha : a * c <= c) : a∗ * b <= c := by grw [hb, kstar_mul_le_self ha]

/--
theorem `kstar_le_of_mul_le_left` / 定理 `kstar_le_of_mul_le_left`

English:
theorem kstar_le_of_mul_le_left
  given: (hb : 1 <= b)
  statement: b * a <= b -> a∗ <= b
  proof: by
  simpa using mul_kstar_le hb

中文:
定理 kstar_le_of_mul_le_left
  条件: (hb : 1 <= b)
  结论: b * a <= b -> a∗ <= b
  证明: by
  simpa using mul_kstar_le hb

Depends on / 依赖: mul_kstar_le
-/
theorem kstar_le_of_mul_le_left (hb : 1 <= b) : b * a <= b -> a∗ <= b := by
  simpa using mul_kstar_le hb

/--
theorem `kstar_le_of_mul_le_right` / 定理 `kstar_le_of_mul_le_right`

English:
theorem kstar_le_of_mul_le_right
  given: (hb : 1 <= b)
  statement: a * b <= b -> a∗ <= b
  proof: by
  simpa using kstar_mul_le hb

@[simp]

中文:
定理 kstar_le_of_mul_le_right
  条件: (hb : 1 <= b)
  结论: a * b <= b -> a∗ <= b
  证明: by
  simpa using kstar_mul_le hb

@[simp]

Depends on / 依赖: kstar_mul_le
-/
theorem kstar_le_of_mul_le_right (hb : 1 <= b) : a * b <= b -> a∗ <= b := by
  simpa using kstar_mul_le hb

@[simp]
/--
theorem `le_kstar` / 定理 `le_kstar`

English:
theorem le_kstar
  statement: a <= a∗
  proof: le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar

@[gcongr, mono]

中文:
定理 le_kstar
  结论: a <= a∗
  证明: le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar

@[gcongr, mono]

Depends on / 依赖: kstar_mul_le_kstar, le_mul_of_one_le_left, le_trans, one_le_kstar
-/
theorem le_kstar : a <= a∗ :=
  le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar

@[gcongr, mono]
/--
theorem `kstar_mono` / 定理 `kstar_mono`

English:
theorem kstar_mono
  statement: Monotone (KStar.kstar : α -> α)
  proof: fun _ _ h =>
kstar_le_of_mul_le_left one_le_kstar kstar_mul_le (h.trans le_kstar) mul_kstar_le_kstar

@[simp]

中文:
定理 kstar_mono
  结论: 递增 (KStar.kstar : α -> α)
  证明: fun _ _ h =>
kstar_le_of_mul_le_left one_le_kstar kstar_mul_le (h.trans le_kstar) mul_kstar_le_kstar

@[simp]

Depends on / 依赖: h.trans, kstar_le_of_mul_le_left, kstar_mul_le, le_kstar, mul_kstar_le_kstar, one_le_kstar
-/
theorem kstar_mono : Monotone (KStar.kstar : α -> α) :=
  fun _ _ h =>
kstar_le_of_mul_le_left one_le_kstar kstar_mul_le (h.trans le_kstar) mul_kstar_le_kstar

@[simp]
/--
theorem `kstar_eq_one` / 定理 `kstar_eq_one`

English:
theorem kstar_eq_one
  statement: a∗ = 1 ↔ a <= 1
  proof: ⟨le_kstar.trans_eq,
fun h => one_le_kstar.antisymm' kstar_le_of_mul_le_left le_rfl by rwa [one_mul]⟩

中文:
定理 kstar_eq_one
  结论: a∗ = 1 ↔ a <= 1
  证明: ⟨le_kstar.trans_eq,
fun h => one_le_kstar.antisymm' kstar_le_of_mul_le_left le_rfl by rwa [one_mul]⟩

Depends on / 依赖: antisymm, kstar_le_of_mul_le_left, le_kstar, le_kstar.trans_eq, le_rfl, one_le_kstar, one_le_kstar.antisymm, one_mul, trans_eq
-/
theorem kstar_eq_one : a∗ = 1 ↔ a <= 1 :=
  ⟨le_kstar.trans_eq,
fun h => one_le_kstar.antisymm' kstar_le_of_mul_le_left le_rfl by rwa [one_mul]⟩

/--
lemma `kstar_zero` / 引理 `kstar_zero`

English:
lemma kstar_zero
  statement: (0 : α)∗ = 1
  proof: kstar_eq_one.2 zero_le

@[simp]

中文:
引理 kstar_zero
  结论: (0 : α)∗ = 1
  证明: kstar_eq_one.2 zero_le

@[simp]
-/
@[simp] lemma kstar_zero : (0 : α)∗ = 1 := kstar_eq_one.2 zero_le

@[simp]
/--
theorem `kstar_one` / 定理 `kstar_one`

English:
theorem kstar_one
  statement: (1 : α)∗ = 1
  proof: kstar_eq_one.2 le_rfl

@[simp]

中文:
定理 kstar_one
  结论: (1 : α)∗ = 1
  证明: kstar_eq_one.2 le_rfl

@[simp]

Depends on / 依赖: kstar_eq_one, le_rfl
-/
theorem kstar_one : (1 : α)∗ = 1 :=
  kstar_eq_one.2 le_rfl

@[simp]
/--
theorem `kstar_mul_kstar` / 定理 `kstar_mul_kstar`

English:
theorem kstar_mul_kstar
  given: (a : α)
  statement: a∗ * a∗ = a∗
  proof: (mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm le_mul_of_one_le_left' one_le_kstar

@[simp]

中文:
定理 kstar_mul_kstar
  条件: (a : α)
  结论: a∗ * a∗ = a∗
  证明: (mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm le_mul_of_one_le_left' one_le_kstar

@[simp]

Depends on / 依赖: antisymm, kstar_mul_le_kstar, le_mul_of_one_le_left, le_rfl, mul_kstar_le, one_le_kstar
-/
theorem kstar_mul_kstar (a : α) : a∗ * a∗ = a∗ :=
(mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm le_mul_of_one_le_left' one_le_kstar

@[simp]
/--
theorem `kstar_eq_self` / 定理 `kstar_eq_self`

English:
theorem kstar_eq_self
  statement: a∗ = a ↔ a * a = a ∧ 1 <= a
  proof: ⟨fun h => ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩,
    fun h => (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

@[simp]

中文:
定理 kstar_eq_self
  结论: a∗ = a ↔ a * a = a ∧ 1 <= a
  证明: ⟨fun h => ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩,
    fun h => (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

@[simp]

Depends on / 依赖: antisymm, kstar_le_of_mul_le_left, kstar_mul_kstar, le_kstar, one_le_kstar, one_le_kstar.trans_eq, trans_eq
-/
theorem kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 <= a :=
  ⟨fun h => ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩,
    fun h => (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

@[simp]
/--
theorem `kstar_idem` / 定理 `kstar_idem`

English:
theorem kstar_idem
  given: (a : α)
  statement: a∗∗ = a∗
  proof: kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

@[simp]

中文:
定理 kstar_idem
  条件: (a : α)
  结论: a∗∗ = a∗
  证明: kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

@[simp]

Depends on / 依赖: kstar_eq_self, kstar_mul_kstar, one_le_kstar
-/
theorem kstar_idem (a : α) : a∗∗ = a∗ :=
  kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

@[simp]
/--
theorem `pow_le_kstar` / 定理 `pow_le_kstar`

English:
theorem pow_le_kstar
  statement: forall {n : Nat}, a ^ n <= a∗

中文:
定理 pow_le_kstar
  结论: 对任意 {n : 自然数}, a ^ n <= a∗
-/
theorem pow_le_kstar : forall {n : Nat}, a ^ n <= a∗
  | 0 => (pow_zero _).trans_le one_le_kstar
  | n + 1 => by grw [pow_succ', pow_le_kstar, mul_kstar_le_kstar]

/--
theorem `one_add_mul_kstar` / 定理 `one_add_mul_kstar`

English:
theorem one_add_mul_kstar
  statement: 1 + a * a∗ = a∗
  proof: by
  have h : 1 + a * a∗ <= a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, mul_kstar_le_kstar⟩
  apply le_antisymm h
  suffices 1 + a * (1 + a * a∗) <= 1 + a * a∗ by
    rw [add_le_iff] at this
    nth_rw 1 [← mul_one a∗]
    exact (mul_right_mono this.1).trans (kstar_mul_le_self this.2)
  ap

中文:
定理 one_add_mul_kstar
  结论: 1 + a * a∗ = a∗
  证明: by
  have h : 1 + a * a∗ <= a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, mul_kstar_le_kstar⟩
  apply le_antisymm h
  suffices 1 + a * (1 + a * a∗) <= 1 + a * a∗ by
    rw [add_le_iff] at this
    nth_rw 1 [← mul_one a∗]
    exact (mul_right_mono this.1).trans (kstar_mul_le_self this.2)
  ap

Depends on / 依赖: add_le_add_right, add_le_iff, kstar_mul_le_self, le_antisymm, mul_kstar_le_kstar, mul_one, mul_right_mono, nth_rw, one_le_kstar
-/
theorem one_add_mul_kstar : 1 + a * a∗ = a∗ := by
  have h : 1 + a * a∗ <= a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, mul_kstar_le_kstar⟩
  apply le_antisymm h
  suffices 1 + a * (1 + a * a∗) <= 1 + a * a∗ by
    rw [add_le_iff] at this
    nth_rw 1 [← mul_one a∗]
    exact (mul_right_mono this.1).trans (kstar_mul_le_self this.2)
  apply add_le_add_right (mul_right_mono h)

/--
theorem `one_add_kstar_mul` / 定理 `one_add_kstar_mul`

English:
theorem one_add_kstar_mul
  statement: 1 + a∗ * a = a∗
  proof: by
  have h : 1 + a∗ * a <= a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, kstar_mul_le_kstar⟩
  apply le_antisymm h
  suffices 1 + (1 + a∗ * a) * a <= 1 + a∗ * a by
    rw [add_le_iff] at this
    nth_rw 1 [← one_mul a∗]
    exact (mul_left_mono this.1).trans (mul_kstar_le_self this.2)
  app

中文:
定理 one_add_kstar_mul
  结论: 1 + a∗ * a = a∗
  证明: by
  have h : 1 + a∗ * a <= a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, kstar_mul_le_kstar⟩
  apply le_antisymm h
  suffices 1 + (1 + a∗ * a) * a <= 1 + a∗ * a by
    rw [add_le_iff] at this
    nth_rw 1 [← one_mul a∗]
    exact (mul_left_mono this.1).trans (mul_kstar_le_self this.2)
  app

Depends on / 依赖: add_le_add_right, add_le_iff, kstar_mul_le_kstar, le_antisymm, mul_kstar_le_self, mul_left_mono, nth_rw, one_le_kstar, one_mul
-/
theorem one_add_kstar_mul : 1 + a∗ * a = a∗ := by
  have h : 1 + a∗ * a <= a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, kstar_mul_le_kstar⟩
  apply le_antisymm h
  suffices 1 + (1 + a∗ * a) * a <= 1 + a∗ * a by
    rw [add_le_iff] at this
    nth_rw 1 [← one_mul a∗]
    exact (mul_left_mono this.1).trans (mul_kstar_le_self this.2)
  apply add_le_add_right (mul_left_mono h)

end KleeneAlgebra

namespace Prod

/--
Instance `instIdemSemiring` / 实例 `instIdemSemiring`

English:
instance instIdemSemiring
  signature: [IdemSemiring α] [IdemSemiring β]
  body: Prod.ext (add_eq_sup _ _) (add_eq_sup _ _)

中文:
实例 instIdemSemiring
  签名: [IdemSemiring α] [IdemSemiring β]
  定义体: Prod.ext (add_eq_sup _ _) (add_eq_sup _ _)

Depends on / 依赖: Prod.ext, add_eq_sup
-/
instance instIdemSemiring [IdemSemiring α] [IdemSemiring β] : IdemSemiring (α × β) where
  add_eq_sup _ _ := Prod.ext (add_eq_sup _ _) (add_eq_sup _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IdemCommSemiring
  signature: α] [IdemCommSemiring β] : IdemCommSemiring (α × β) where
  body: Prod.instCommSemiring
  __ := Prod.instIdemSemiring

中文:
实例 [IdemCommSemiring
  签名: α] [IdemCommSemiring β] : IdemCommSemiring (α × β) where
  定义体: Prod.instCommSemiring
  __ := Prod.instIdemSemiring

Depends on / 依赖: Prod.instCommSemiring, instCommSemiring
-/
instance [IdemCommSemiring α] [IdemCommSemiring β] : IdemCommSemiring (α × β) where
  __ := Prod.instCommSemiring
  __ := Prod.instIdemSemiring

variable [KleeneAlgebra α] [KleeneAlgebra β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: KleeneAlgebra (α × β)
  body: (a.1∗, a.2∗)
  one_le_kstar _ := ⟨one_le_kstar, one_le_kstar⟩
  mul_kstar_le_kstar _ := ⟨mul_kstar_le_kstar, mul_kstar_le_kstar⟩
  kstar_mul_le_kstar _ := ⟨kstar_mul_le_kstar, kstar_mul_le_kstar⟩
  mul_kstar_le_self _ _ := And.imp mul_kstar_le_self mul_kstar_le_self
  kstar_mul_le_self _ _ := And.im

中文:
实例 :
  签名: Kleene代数 (α × β)
  定义体: (a.1∗, a.2∗)
  one_le_kstar _ := ⟨one_le_kstar, one_le_kstar⟩
  mul_kstar_le_kstar _ := ⟨mul_kstar_le_kstar, mul_kstar_le_kstar⟩
  kstar_mul_le_kstar _ := ⟨kstar_mul_le_kstar, kstar_mul_le_kstar⟩
  mul_kstar_le_self _ _ := And.imp mul_kstar_le_self mul_kstar_le_self
  kstar_mul_le_self _ _ := And.im
-/
instance : KleeneAlgebra (α × β) where
  kstar a := (a.1∗, a.2∗)
  one_le_kstar _ := ⟨one_le_kstar, one_le_kstar⟩
  mul_kstar_le_kstar _ := ⟨mul_kstar_le_kstar, mul_kstar_le_kstar⟩
  kstar_mul_le_kstar _ := ⟨kstar_mul_le_kstar, kstar_mul_le_kstar⟩
  mul_kstar_le_self _ _ := And.imp mul_kstar_le_self mul_kstar_le_self
  kstar_mul_le_self _ _ := And.imp kstar_mul_le_self kstar_mul_le_self

/--
theorem `kstar_def` / 定理 `kstar_def`

English:
theorem kstar_def
  given: (a : α × β)
  statement: a∗ = (a.1∗, a.2∗)
  proof: rfl

@[simp]

中文:
定理 kstar_def
  条件: (a : α × β)
  结论: a∗ = (a.1∗, a.2∗)
  证明: rfl

@[simp]
-/
theorem kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗) :=
  rfl

@[simp]
/--
theorem `fst_kstar` / 定理 `fst_kstar`

English:
theorem fst_kstar
  given: (a : α × β)
  statement: a∗.1 = a.1∗
  proof: rfl

@[simp]

中文:
定理 fst_kstar
  条件: (a : α × β)
  结论: a∗.1 = a.1∗
  证明: rfl

@[simp]
-/
theorem fst_kstar (a : α × β) : a∗.1 = a.1∗ :=
  rfl

@[simp]
/--
theorem `snd_kstar` / 定理 `snd_kstar`

English:
theorem snd_kstar
  given: (a : α × β)
  statement: a∗.2 = a.2∗
  proof: rfl

中文:
定理 snd_kstar
  条件: (a : α × β)
  结论: a∗.2 = a.2∗
  证明: rfl
-/
theorem snd_kstar (a : α × β) : a∗.2 = a.2∗ :=
  rfl

end Prod

namespace Pi

/--
Instance `instIdemSemiring` / 实例 `instIdemSemiring`

English:
instance instIdemSemiring
  signature: [forall i, IdemSemiring (π i)]
  body: funext fun _ => add_eq_sup _ _

中文:
实例 instIdemSemiring
  签名: [对任意 i, IdemSemiring (π i)]
  定义体: funext fun _ => add_eq_sup _ _

Depends on / 依赖: add_eq_sup
-/
instance instIdemSemiring [forall i, IdemSemiring (π i)] : IdemSemiring (forall i, π i) where
  add_eq_sup _ _ := funext fun _ => add_eq_sup _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IdemCommSemiring (π i)] : IdemCommSemiring (forall i, π i) where
  body: Pi.commSemiring
  __ := Pi.instIdemSemiring

中文:
实例 [对任意
  签名: i, IdemCommSemiring (π i)] : IdemCommSemiring (对任意 i, π i) where
  定义体: Pi.commSemiring
  __ := Pi.instIdemSemiring

Depends on / 依赖: Pi.commSemiring, commSemiring
-/
instance [forall i, IdemCommSemiring (π i)] : IdemCommSemiring (forall i, π i) where
  __ := Pi.commSemiring
  __ := Pi.instIdemSemiring

variable [forall i, KleeneAlgebra (π i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: KleeneAlgebra (forall i, π i)
  body: (a i)∗
  one_le_kstar _ _ := one_le_kstar
  mul_kstar_le_kstar _ _ := mul_kstar_le_kstar
  kstar_mul_le_kstar _ _ := kstar_mul_le_kstar
  mul_kstar_le_self _ _ h _ := mul_kstar_le_self (h _)
  kstar_mul_le_self _ _ h _ := kstar_mul_le_self (h _)

@[push ←]

中文:
实例 :
  签名: Kleene代数 (对任意 i, π i)
  定义体: (a i)∗
  one_le_kstar _ _ := one_le_kstar
  mul_kstar_le_kstar _ _ := mul_kstar_le_kstar
  kstar_mul_le_kstar _ _ := kstar_mul_le_kstar
  mul_kstar_le_self _ _ h _ := mul_kstar_le_self (h _)
  kstar_mul_le_self _ _ h _ := kstar_mul_le_self (h _)

@[push ←]
-/
instance : KleeneAlgebra (forall i, π i) where
  kstar a i := (a i)∗
  one_le_kstar _ _ := one_le_kstar
  mul_kstar_le_kstar _ _ := mul_kstar_le_kstar
  kstar_mul_le_kstar _ _ := kstar_mul_le_kstar
  mul_kstar_le_self _ _ h _ := mul_kstar_le_self (h _)
  kstar_mul_le_self _ _ h _ := kstar_mul_le_self (h _)

@[push ←]
/--
theorem `kstar_def` / 定理 `kstar_def`

English:
theorem kstar_def
  given: (a : forall i, π i)
  statement: a∗ = fun i => (a i)∗
  proof: rfl

@[simp]

中文:
定理 kstar_def
  条件: (a : 对任意 i, π i)
  结论: a∗ = fun i => (a i)∗
  证明: rfl

@[simp]
-/
theorem kstar_def (a : forall i, π i) : a∗ = fun i => (a i)∗ :=
  rfl

@[simp]
/--
theorem `kstar_apply` / 定理 `kstar_apply`

English:
theorem kstar_apply
  given: (a : forall i, π i) (i : ι)
  statement: a∗ i = (a i)∗
  proof: rfl

中文:
定理 kstar_apply
  条件: (a : 对任意 i, π i) (i : ι)
  结论: a∗ i = (a i)∗
  证明: rfl
-/
theorem kstar_apply (a : forall i, π i) (i : ι) : a∗ i = (a i)∗ :=
  rfl

end Pi

namespace Function.Injective

-- See note [reducible non-instances]
/--
Definition of `idemSemiring` / `idemSemiring` 的定义

English:
abbreviation idemSemiring
  signature: [IdemSemiring α] [LE β] [LT β] [Zero β] [One β]
  body: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.semilatticeSup f le lt sup
add_eq_sup a b := hf by rw [sup, add, add_eq_sup]
bot_le a := le.1 bot.trans_le bot_le

中文:
缩写 idemSemiring
  签名: [IdemSemiring α] [LE β] [LT β] [零 β] [幺 β]
  定义体: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.semilatticeSup f le lt sup
add_eq_sup a b := hf by rw [sup, add, add_eq_sup]
bot_le a := le.1 bot.trans_le bot_le
-/
protected abbrev idemSemiring [IdemSemiring α] [LE β] [LT β] [Zero β] [One β]
    [Add β] [Mul β] [Pow β Nat] [SMul Nat β] [NatCast β] [Max β] [Bot β] (f : β -> α)
    (hf : Injective f) (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemSemiring β where
  __ := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.semilatticeSup f le lt sup
add_eq_sup a b := hf by rw [sup, add, add_eq_sup]
bot_le a := le.1 bot.trans_le bot_le

-- See note [reducible non-instances]
/--
Definition of `idemCommSemiring` / `idemCommSemiring` 的定义

English:
abbreviation idemCommSemiring
  signature: [IdemCommSemiring α] [LE β] [LT β] [Zero β] [One β]
  body: hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot

中文:
缩写 idemCommSemiring
  签名: [IdemCommSemiring α] [LE β] [LT β] [零 β] [幺 β]
  定义体: hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot
-/
protected abbrev idemCommSemiring [IdemCommSemiring α] [LE β] [LT β] [Zero β] [One β]
    [Add β] [Mul β] [Pow β Nat] [SMul Nat β] [NatCast β] [Max β] [Bot β] (f : β -> α)
    (hf : Injective f) (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemCommSemiring β where
  __ := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot

-- See note [reducible non-instances]
/--
Definition of `kleeneAlgebra` / `kleeneAlgebra` 的定义

English:
abbreviation kleeneAlgebra
  signature: [KleeneAlgebra α] [LE β] [LT β] [Zero β] [One β]
  body: hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot
  one_le_kstar a := by
    rw [← le]; rw [one]; rw [kstar]
    exact one_le_kstar
  mul_kstar_le_kstar a := by
    rw [← le]; rw [mul]; rw [kstar]
    exact mul_kstar_le_kstar
  kstar_mul_le_kstar a := by
    rw [← le]; rw [mul]; rw

中文:
缩写 kleeneAlgebra
  签名: [Kleene代数 α] [LE β] [LT β] [零 β] [幺 β]
  定义体: hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot
  one_le_kstar a := by
    rw [← le]; rw [one]; rw [kstar]
    exact one_le_kstar
  mul_kstar_le_kstar a := by
    rw [← le]; rw [mul]; rw [kstar]
    exact mul_kstar_le_kstar
  kstar_mul_le_kstar a := by
    rw [← le]; rw [mul]; rw
-/
protected abbrev kleeneAlgebra [KleeneAlgebra α] [LE β] [LT β] [Zero β] [One β]
    [Add β] [Mul β] [Pow β Nat] [SMul Nat β] [NatCast β] [Max β] [Bot β] [KStar β] (f : β -> α)
    (hf : Injective f) (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥)
    (kstar : forall a, f a∗ = (f a)∗) : KleeneAlgebra β where
  __ := hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot
  one_le_kstar a := by
    rw [← le]; rw [one]; rw [kstar]
    exact one_le_kstar
  mul_kstar_le_kstar a := by
    rw [← le]; rw [mul]; rw [kstar]
    exact mul_kstar_le_kstar
  kstar_mul_le_kstar a := by
    rw [← le]; rw [mul]; rw [kstar]
    exact kstar_mul_le_kstar
  mul_kstar_le_self a b h := by
    rw [← le]; rw [mul]; rw [kstar]
    rw [← le]; rw [mul] at h
    exact mul_kstar_le_self h
  kstar_mul_le_self a b h := by
    rw [← le]; rw [mul]; rw [kstar]
    rw [← le]; rw [mul] at h
    exact kstar_mul_le_self h

end Function.Injective
