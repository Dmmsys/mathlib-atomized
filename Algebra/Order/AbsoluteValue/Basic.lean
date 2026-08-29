/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Positivity.Core

/-!
# Absolute values

This file defines a bundled type of absolute values `AbsoluteValue R S`.

## Main definitions

* `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`.
* `AbsoluteValue.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
* `AbsoluteValue.toMonoidWithZeroHom`: absolute values mapping to a
  linear ordered field preserve `0`, `*` and `1`
* `IsAbsoluteValue`: a type class stating that `f : β → α` satisfies the axioms of an absolute
  value
-/

@[expose] public section

variable {ι α R S : Type*}

/--
Definition of `AbsoluteValue` / `AbsoluteValue` 的定义

English:
structure AbsoluteValue
  parameters: (R S : Type*) [Semiring R] [Semiring S] [PartialOrder S]
  extends: R ->ₙ* S
  axioms and operations (3):
    - nonneg' : forall x, 0 <= toFun x
    - eq_zero' : forall x, toFun x = 0 ↔ x = 0
    - add_le' : forall x y, toFun (x + y) <= toFun x + toFun y

中文:
结构 绝对值
  参数: (R S : 类型) [半环 R] [半环 S] [偏序 S]
  继承: R ->ₙ* S
  公理与运算 (3 个):
    - nonneg' : 对任意 x, 0 <= toFun x
    - eq_zero' : 对任意 x, toFun x = 0 ↔ x = 0
    - add_le' : 对任意 x y, toFun (x + y) <= toFun x + toFun y
-/
structure AbsoluteValue (R S : Type*) [Semiring R] [Semiring S] [PartialOrder S]
    extends R ->ₙ* S where
  /-- The absolute value is nonnegative -/
  nonneg' : forall x, 0 <= toFun x
  /-- The absolute value is positive definitive -/
  eq_zero' : forall x, toFun x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  add_le' : forall x y, toFun (x + y) <= toFun x + toFun y

namespace AbsoluteValue

attribute [nolint docBlame] AbsoluteValue.toMulHom

section OrderedSemiring

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (AbsoluteValue R S) R S where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

中文:
实例 funLike
  签名: : 函数状 (绝对值 R S) R S where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (AbsoluteValue R S) R S where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

/--
Instance `zeroHomClass` / 实例 `zeroHomClass`

English:
instance zeroHomClass
  signature: : ZeroHomClass (AbsoluteValue R S) R S where
  body: (f.eq_zero' _).2 rfl

中文:
实例 zeroHomClass
  签名: : 保零态射类 (绝对值 R S) R S where
  定义体: (f.eq_zero' _).2 rfl

Depends on / 依赖: eq_zero, f.eq_zero
-/
instance zeroHomClass : ZeroHomClass (AbsoluteValue R S) R S where
  map_zero f := (f.eq_zero' _).2 rfl

/--
Instance `mulHomClass` / 实例 `mulHomClass`

English:
instance mulHomClass
  signature: : MulHomClass (AbsoluteValue R S) R S
  body: { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_mul := fun f => f.map_mul' }

中文:
实例 mulHomClass
  签名: : 乘法态射类 (绝对值 R S) R S
  定义体: { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_mul := fun f => f.map_mul' }

Depends on / 依赖: AbsoluteValue, AbsoluteValue.zeroHomClass, f.map_mul, map_mul, zeroHomClass
-/
instance mulHomClass : MulHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_mul := fun f => f.map_mul' }

/--
Instance `nonnegHomClass` / 实例 `nonnegHomClass`

English:
instance nonnegHomClass
  signature: : NonnegHomClass (AbsoluteValue R S) R S
  body: { AbsoluteValue.zeroHomClass (R := R) (S := S) with apply_nonneg := fun f => f.nonneg' }

中文:
实例 nonnegHomClass
  签名: : Nonneg态射类 (绝对值 R S) R S
  定义体: { AbsoluteValue.zeroHomClass (R := R) (S := S) with apply_nonneg := fun f => f.nonneg' }

Depends on / 依赖: AbsoluteValue, AbsoluteValue.zeroHomClass, apply_nonneg, f.nonneg, nonneg, zeroHomClass
-/
instance nonnegHomClass : NonnegHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with apply_nonneg := fun f => f.nonneg' }

/--
Instance `subadditiveHomClass` / 实例 `subadditiveHomClass`

English:
instance subadditiveHomClass
  signature: : SubadditiveHomClass (AbsoluteValue R S) R S
  body: { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_add_le_add := fun f => f.add_le' }

@[simp]

中文:
实例 subadditiveHomClass
  签名: : Subadditive态射类 (绝对值 R S) R S
  定义体: { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_add_le_add := fun f => f.add_le' }

@[simp]

Depends on / 依赖: AbsoluteValue, AbsoluteValue.zeroHomClass, add_le, f.add_le, map_add_le_add, zeroHomClass
-/
instance subadditiveHomClass : SubadditiveHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_add_le_add := fun f => f.add_le' }

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : R ->ₙ* S) {h₁ h₂ h₃}
  statement: (AbsoluteValue.mk f h₁ h₂ h₃ : R -> S) = f
  proof: rfl

@[ext]

中文:
定理 coe_mk
  条件: (f : R ->ₙ* S) {h₁ h₂ h₃}
  结论: (绝对值.mk f h₁ h₂ h₃ : R -> S) = f
  证明: rfl

@[ext]
-/
theorem coe_mk (f : R ->ₙ* S) {h₁ h₂ h₃} : (AbsoluteValue.mk f h₁ h₂ h₃ : R -> S) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: AbsoluteValue R S⦄ : (forall x, f x = g x) -> f = g
  proof: DFunLike.ext _ _

中文:
定理 ext
  条件: ⦃f g
  结论: 绝对值 R S⦄ : (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext _ _

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x) -> f = g :=
  DFunLike.ext _ _

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : AbsoluteValue R S)
  body: f

initialize_simps_projections AbsoluteValue (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: (f : 绝对值 R S)
  定义体: f

initialize_simps_projections AbsoluteValue (toFun -> apply)

@[simp]
-/
def Simps.apply (f : AbsoluteValue R S) : R -> S :=
  f

initialize_simps_projections AbsoluteValue (toFun -> apply)

@[simp]
/--
theorem `coe_toMulHom` / 定理 `coe_toMulHom`

English:
theorem coe_toMulHom
  statement: ⇑abv.toMulHom = abv
  proof: rfl

@[bound]

中文:
定理 coe_toMulHom
  结论: ⇑abv.toMulHom = abv
  证明: rfl

@[bound]
-/
theorem coe_toMulHom : ⇑abv.toMulHom = abv :=
  rfl

@[bound]
/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (x : R)
  statement: 0 <= abv x
  proof: abv.nonneg' x

@[simp]

中文:
定理 nonneg
  条件: (x : R)
  结论: 0 <= abv x
  证明: abv.nonneg' x

@[simp]
-/
protected theorem nonneg (x : R) : 0 <= abv x :=
  abv.nonneg' x

@[simp]
/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: {x : R}
  statement: abv x = 0 ↔ x = 0
  proof: abv.eq_zero' x

@[bound]

中文:
定理 eq_zero
  条件: {x : R}
  结论: abv x = 0 ↔ x = 0
  证明: abv.eq_zero' x

@[bound]
-/
protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 :=
  abv.eq_zero' x

@[bound]
/--
theorem `add_le` / 定理 `add_le`

English:
theorem add_le
  given: (x y : R)
  statement: abv (x + y) <= abv x + abv y
  proof: abv.add_le' x y

中文:
定理 add_le
  条件: (x y : R)
  结论: abv (x + y) <= abv x + abv y
  证明: abv.add_le' x y
-/
protected theorem add_le (x y : R) : abv (x + y) <= abv x + abv y :=
  abv.add_le' x y

/--
lemma `listSum_le` / 引理 `listSum_le`

English:
lemma listSum_le
  given: [AddLeftMono S] (l : List R)
  statement: abv l.sum <= (l.map abv).sum
  proof: by
  induction l with
  | nil => simp
| cons head tail ih => exact (abv.add_le ..).trans add_le_add_right ih (abv head)

@[simp]

中文:
引理 listSum_le
  条件: [AddLeftMono S] (l : 列表 R)
  结论: abv l.求和 <= (l.map abv).求和
  证明: by
  induction l with
  | nil => simp
| cons head tail ih => exact (abv.add_le ..).trans add_le_add_right ih (abv head)

@[simp]

Depends on / 依赖: abv.add_le, add_le, add_le_add_right
-/
lemma listSum_le [AddLeftMono S] (l : List R) : abv l.sum <= (l.map abv).sum := by
  induction l with
  | nil => simp
| cons head tail ih => exact (abv.add_le ..).trans add_le_add_right ih (abv head)

@[simp]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (x y : R)
  statement: abv (x * y) = abv x * abv y
  proof: abv.map_mul' x y

中文:
定理 map_mul
  条件: (x y : R)
  结论: abv (x * y) = abv x * abv y
  证明: abv.map_mul' x y
-/
protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y :=
  abv.map_mul' x y

/--
theorem `ne_zero_iff` / 定理 `ne_zero_iff`

English:
theorem ne_zero_iff
  given: {x : R}
  statement: abv x != 0 ↔ x != 0
  proof: abv.eq_zero.not
protected alias ⟨_, ne_zero⟩ := AbsoluteValue.ne_zero_iff

@[simp]

中文:
定理 ne_zero_iff
  条件: {x : R}
  结论: abv x != 0 ↔ x != 0
  证明: abv.eq_zero.not
protected alias ⟨_, ne_zero⟩ := AbsoluteValue.ne_zero_iff

@[simp]
-/
protected theorem ne_zero_iff {x : R} : abv x != 0 ↔ x != 0 :=
  abv.eq_zero.not
protected alias ⟨_, ne_zero⟩ := AbsoluteValue.ne_zero_iff

@[simp]
/--
theorem `pos_iff` / 定理 `pos_iff`

English:
theorem pos_iff
  given: {x : R}
  statement: 0 < abv x ↔ x != 0
  proof: (abv.nonneg x).lt_iff_ne'.trans abv.ne_zero_iff
protected alias ⟨_, pos⟩ := AbsoluteValue.pos_iff

@[simp]

中文:
定理 pos_iff
  条件: {x : R}
  结论: 0 < abv x ↔ x != 0
  证明: (abv.nonneg x).lt_iff_ne'.trans abv.ne_zero_iff
protected alias ⟨_, pos⟩ := AbsoluteValue.pos_iff

@[simp]
-/
protected theorem pos_iff {x : R} : 0 < abv x ↔ x != 0 :=
  (abv.nonneg x).lt_iff_ne'.trans abv.ne_zero_iff
protected alias ⟨_, pos⟩ := AbsoluteValue.pos_iff

@[simp]
/--
theorem `nonpos_iff` / 定理 `nonpos_iff`

English:
theorem nonpos_iff
  given: {x : R}
  statement: abv x <= 0 ↔ x = 0
  proof: by
  simp only [← abv.eq_zero, le_antisymm_iff, abv.nonneg, and_true]

中文:
定理 nonpos_iff
  条件: {x : R}
  结论: abv x <= 0 ↔ x = 0
  证明: by
  simp only [← abv.eq_zero, le_antisymm_iff, abv.nonneg, and_true]
-/
protected theorem nonpos_iff {x : R} : abv x <= 0 ↔ x = 0 := by
  simp only [← abv.eq_zero, le_antisymm_iff, abv.nonneg, and_true]

/--
theorem `map_one_of_isLeftRegular` / 定理 `map_one_of_isLeftRegular`

English:
theorem map_one_of_isLeftRegular
  given: (h : IsLeftRegular (abv 1))
  statement: abv 1 = 1
  proof: h by simp [← abv.map_mul]

@[simp]

中文:
定理 map_one_of_isLeftRegular
  条件: (h : IsLeftRegular (abv 1))
  结论: abv 1 = 1
  证明: h by simp [← abv.map_mul]

@[simp]

Depends on / 依赖: abv.map_mul, map_mul
-/
theorem map_one_of_isLeftRegular (h : IsLeftRegular (abv 1)) : abv 1 = 1 :=
h by simp [← abv.map_mul]

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: abv 0 = 0
  proof: abv.eq_zero.2 rfl

中文:
定理 map_zero
  结论: abv 0 = 0
  证明: abv.eq_zero.2 rfl
-/
protected theorem map_zero : abv 0 = 0 :=
  abv.eq_zero.2 rfl

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

/--
theorem `sub_le` / 定理 `sub_le`

English:
theorem sub_le
  given: (a b c : R)
  statement: abv (a - c) <= abv (a - b) + abv (b - c)
  proof: by
  simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

@[simp high] -- added `high` to apply it before `AbsoluteValue.eq_zero`

中文:
定理 sub_le
  条件: (a b c : R)
  结论: abv (a - c) <= abv (a - b) + abv (b - c)
  证明: by
  simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

@[simp high] -- added `high` to apply it before `AbsoluteValue.eq_zero`
-/
protected theorem sub_le (a b c : R) : abv (a - c) <= abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

@[simp high] -- added `high` to apply it before `AbsoluteValue.eq_zero`
/--
theorem `map_sub_eq_zero_iff` / 定理 `map_sub_eq_zero_iff`

English:
theorem map_sub_eq_zero_iff
  given: (a b : R)
  statement: abv (a - b) = 0 ↔ a = b
  proof: abv.eq_zero.trans sub_eq_zero

中文:
定理 map_sub_eq_zero_iff
  条件: (a b : R)
  结论: abv (a - b) = 0 ↔ a = b
  证明: abv.eq_zero.trans sub_eq_zero

Depends on / 依赖: abv.eq_zero.trans, eq_zero, sub_eq_zero
-/
theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
  abv.eq_zero.trans sub_eq_zero

end Ring

section Semiring

section IsDomain

-- all of these are true for `NoZeroDivisors S`; but it doesn't work smoothly with the
-- `IsDomain`/`IsCancelMulZero` API
variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)
variable [IsDomain S] [Nontrivial R]

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: abv 1 = 1
  proof: abv.map_one_of_isLeftRegular (IsRegular.of_ne_zero <| abv.ne_zero one_ne_zero).left

中文:
定理 map_one
  结论: abv 1 = 1
  证明: abv.map_one_of_isLeftRegular (IsRegular.of_ne_zero <| abv.ne_zero one_ne_zero).left
-/
protected theorem map_one : abv 1 = 1 :=
  abv.map_one_of_isLeftRegular (IsRegular.of_ne_zero <| abv.ne_zero one_ne_zero).left

/--
Instance `monoidWithZeroHomClass` / 实例 `monoidWithZeroHomClass`

English:
instance monoidWithZeroHomClass
  signature: : MonoidWithZeroHomClass (AbsoluteValue R S) R S
  body: { AbsoluteValue.mulHomClass with
    map_zero := fun f => f.map_zero
    map_one := fun f => f.map_one }

中文:
实例 monoidWithZeroHomClass
  签名: : 带零幺半群态射类 (绝对值 R S) R S
  定义体: { AbsoluteValue.mulHomClass with
    map_zero := fun f => f.map_zero
    map_one := fun f => f.map_one }

Depends on / 依赖: AbsoluteValue, AbsoluteValue.mulHomClass, f.map_one, f.map_zero, map_one, map_zero, mulHomClass
-/
instance monoidWithZeroHomClass : MonoidWithZeroHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.mulHomClass with
    map_zero := fun f => f.map_zero
    map_one := fun f => f.map_one }

/--
Definition of `toMonoidWithZeroHom` / `toMonoidWithZeroHom` 的定义

English:
definition toMonoidWithZeroHom
  signature: : R ->*₀ S
  body: .ofClass abv

@[simp]

中文:
定义 toMonoidWithZeroHom
  签名: : R ->*₀ S
  定义体: .ofClass abv

@[simp]

Depends on / 依赖: ofClass
-/
def toMonoidWithZeroHom : R ->*₀ S :=
  .ofClass abv

@[simp]
/--
theorem `coe_toMonoidWithZeroHom` / 定理 `coe_toMonoidWithZeroHom`

English:
theorem coe_toMonoidWithZeroHom
  statement: ⇑abv.toMonoidWithZeroHom = abv
  proof: rfl

中文:
定理 coe_toMonoidWithZeroHom
  结论: ⇑abv.toMonoidWithZeroHom = abv
  证明: rfl
-/
theorem coe_toMonoidWithZeroHom : ⇑abv.toMonoidWithZeroHom = abv :=
  rfl

/--
Definition of `toMonoidHom` / `toMonoidHom` 的定义

English:
definition toMonoidHom
  signature: : R ->* S
  body: abv

@[simp]

中文:
定义 toMonoidHom
  签名: : R ->* S
  定义体: abv

@[simp]
-/
def toMonoidHom : R ->* S :=
  abv

@[simp]
/--
theorem `coe_toMonoidHom` / 定理 `coe_toMonoidHom`

English:
theorem coe_toMonoidHom
  statement: ⇑abv.toMonoidHom = abv
  proof: rfl

@[simp]

中文:
定理 coe_toMonoidHom
  结论: ⇑abv.toMonoidHom = abv
  证明: rfl

@[simp]
-/
theorem coe_toMonoidHom : ⇑abv.toMonoidHom = abv :=
  rfl

@[simp]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (a : R) (n : Nat)
  statement: abv (a ^ n) = abv a ^ n
  proof: abv.toMonoidHom.map_pow a n

omit [Nontrivial R] in

中文:
定理 map_pow
  条件: (a : R) (n : 自然数)
  结论: abv (a ^ n) = abv a ^ n
  证明: abv.toMonoidHom.map_pow a n

omit [Nontrivial R] in
-/
protected theorem map_pow (a : R) (n : Nat) : abv (a ^ n) = abv a ^ n :=
  abv.toMonoidHom.map_pow a n

omit [Nontrivial R] in
/--
lemma `apply_nat_le_self` / 引理 `apply_nat_le_self`

English:
lemma apply_nat_le_self
  given: [IsOrderedRing S] (n : Nat)
  statement: abv n <= n
  proof: by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.eq_zero (α := R)]
  induction n with
  | zero => simp
  | succ n ih =>
  · grw [Nat.cast_succ, Nat.cast_succ, abv.add_le, abv.map_one, ih]

中文:
引理 apply_nat_le_self
  条件: [是Ordered环 S] (n : 自然数)
  结论: abv n <= n
  证明: by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.eq_zero (α := R)]
  induction n with
  | zero => simp
  | succ n ih =>
  · grw [Nat.cast_succ, Nat.cast_succ, abv.add_le, abv.map_one, ih]

Depends on / 依赖: Nat.cast_succ, Subsingleton, Subsingleton.eq_zero, abv.add_le, abv.map_one, add_le, cast_succ, eq_zero, map_one, subsingleton_or_nontrivial
-/
lemma apply_nat_le_self [IsOrderedRing S] (n : Nat) : abv n <= n := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.eq_zero (α := R)]
  induction n with
  | zero => simp
  | succ n ih =>
  · grw [Nat.cast_succ, Nat.cast_succ, abv.add_le, abv.map_one, ih]

end IsDomain

end Semiring

end OrderedSemiring

section OrderedRing

section Ring

variable {R S : Type*} [Ring R] [Ring S] [PartialOrder S] [IsOrderedRing S]
  (abv : AbsoluteValue R S)

@[bound]
/--
theorem `le_sub` / 定理 `le_sub`

English:
theorem le_sub
  given: (a b : R)
  statement: abv a - abv b <= abv (a - b)
  proof: sub_le_iff_le_add.2 by simpa using abv.add_le (a - b) b

中文:
定理 le_sub
  条件: (a b : R)
  结论: abv a - abv b <= abv (a - b)
  证明: sub_le_iff_le_add.2 by simpa using abv.add_le (a - b) b
-/
protected theorem le_sub (a b : R) : abv a - abv b <= abv (a - b) :=
sub_le_iff_le_add.2 by simpa using abv.add_le (a - b) b

end Ring

end OrderedRing

section OrderedCommRing

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (a : R)
  statement: abv (-a) = abv a
  proof: by
  by_cases ha : a = 0; · simp [ha]
  refine
    (mul_self_eq_mul_self_iff.mp (by rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right ?_
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'

中文:
定理 map_neg
  条件: (a : R)
  结论: abv (-a) = abv a
  证明: by
  by_cases ha : a = 0; · simp [ha]
  refine
    (mul_self_eq_mul_self_iff.mp (by rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right ?_
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'
-/
protected theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases ha : a = 0; · simp [ha]
  refine
    (mul_self_eq_mul_self_iff.mp (by rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right ?_
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (a b : R)
  statement: abv (a - b) = abv (b - a)
  proof: by rw [← neg_sub, abv.map_neg]

中文:
定理 map_sub
  条件: (a b : R)
  结论: abv (a - b) = abv (b - a)
  证明: by rw [← neg_sub, abv.map_neg]
-/
protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by rw [← neg_sub, abv.map_neg]

/-- Bound `abv (a + b)` from below -/
@[bound]
/--
theorem `le_add` / 定理 `le_add`

English:
theorem le_add
  given: (a b : R)
  statement: abv a - abv b <= abv (a + b)
  proof: by
  simpa only [tsub_le_iff_right, add_neg_cancel_right, abv.map_neg] using abv.add_le (a + b) (-b)

中文:
定理 le_add
  条件: (a b : R)
  结论: abv a - abv b <= abv (a + b)
  证明: by
  simpa only [tsub_le_iff_right, add_neg_cancel_right, abv.map_neg] using abv.add_le (a + b) (-b)
-/
protected theorem le_add (a b : R) : abv a - abv b <= abv (a + b) := by
  simpa only [tsub_le_iff_right, add_neg_cancel_right, abv.map_neg] using abv.add_le (a + b) (-b)

/-- Bound `abv (a - b)` from above -/
@[bound]
/--
lemma `sub_le_add` / 引理 `sub_le_add`

English:
lemma sub_le_add
  given: (a b : R)
  statement: abv (a - b) <= abv a + abv b
  proof: by
  simpa only [← sub_eq_add_neg, AbsoluteValue.map_neg] using abv.add_le a (-b)

中文:
引理 sub_le_add
  条件: (a b : R)
  结论: abv (a - b) <= abv a + abv b
  证明: by
  simpa only [← sub_eq_add_neg, AbsoluteValue.map_neg] using abv.add_le a (-b)

Depends on / 依赖: AbsoluteValue, AbsoluteValue.map_neg, abv.add_le, add_le, map_neg, sub_eq_add_neg
-/
lemma sub_le_add (a b : R) : abv (a - b) <= abv a + abv b := by
  simpa only [← sub_eq_add_neg, AbsoluteValue.map_neg] using abv.add_le a (-b)

/--
Instance `addGroupSeminormClass` / 实例 `addGroupSeminormClass`

English:
instance addGroupSeminormClass
  signature: : AddGroupSeminormClass (AbsoluteValue R S) R S where
  body: AbsoluteValue.subadditiveHomClass
  map_zero := AbsoluteValue.map_zero
  map_neg_eq_map f a := AbsoluteValue.map_neg f a

中文:
实例 addGroupSeminormClass
  签名: : 加法群半范数类 (绝对值 R S) R S where
  定义体: AbsoluteValue.subadditiveHomClass
  map_zero := AbsoluteValue.map_zero
  map_neg_eq_map f a := AbsoluteValue.map_neg f a

Depends on / 依赖: AbsoluteValue, AbsoluteValue.subadditiveHomClass, subadditiveHomClass
-/
instance addGroupSeminormClass : AddGroupSeminormClass (AbsoluteValue R S) R S where
  toSubadditiveHomClass := AbsoluteValue.subadditiveHomClass
  map_zero := AbsoluteValue.map_zero
  map_neg_eq_map f a := AbsoluteValue.map_neg f a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] [IsDomain S] : MulRingNormClass (AbsoluteValue R S) R S
  body: { AbsoluteValue.subadditiveHomClass,
    AbsoluteValue.monoidWithZeroHomClass with
    map_neg_eq_map := fun f => f.map_neg
    eq_zero_of_map_eq_zero := fun f _ => f.eq_zero.1 }

中文:
实例 [非平凡
  签名: R] [是整环 S] : 乘法环范数类 (绝对值 R S) R S
  定义体: { AbsoluteValue.subadditiveHomClass,
    AbsoluteValue.monoidWithZeroHomClass with
    map_neg_eq_map := fun f => f.map_neg
    eq_zero_of_map_eq_zero := fun f _ => f.eq_zero.1 }

Depends on / 依赖: AbsoluteValue, AbsoluteValue.monoidWithZeroHomClass, AbsoluteValue.subadditiveHomClass, eq_zero, eq_zero_of_map_eq_zero, f.eq_zero, f.map_neg, map_neg, map_neg_eq_map, monoidWithZeroHomClass, subadditiveHomClass
-/
instance [Nontrivial R] [IsDomain S] : MulRingNormClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.subadditiveHomClass,
    AbsoluteValue.monoidWithZeroHomClass with
    map_neg_eq_map := fun f => f.map_neg
    eq_zero_of_map_eq_zero := fun f _ => f.eq_zero.1 }

open Int in
/--
lemma `apply_natAbs_eq` / 引理 `apply_natAbs_eq`

English:
lemma apply_natAbs_eq
  given: (x : Int)
  statement: abv (natAbs x) = abv x
  proof: by
  obtain ⟨_, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

中文:
引理 apply_natAbs_eq
  条件: (x : 整数)
  结论: abv (natAbs x) = abv x
  证明: by
  obtain ⟨_, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

Depends on / 依赖: Int.eq_nat_or_neg, eq_nat_or_neg
-/
lemma apply_natAbs_eq (x : Int) : abv (natAbs x) = abv x := by
  obtain ⟨_, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

open Int in
/--
lemma `eq_on_nat_iff_eq_on_int` / 引理 `eq_on_nat_iff_eq_on_int`

English:
lemma eq_on_nat_iff_eq_on_int
  given: {f g : AbsoluteValue R S}
  proof: by
  refine ⟨fun h z => ?_, fun a n => mod_cast a n⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp [h n]

中文:
引理 eq_on_nat_iff_eq_on_int
  条件: {f g : 绝对值 R S}
  证明: by
  refine ⟨fun h z => ?_, fun a n => mod_cast a n⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp [h n]

Depends on / 依赖: Int.eq_nat_or_neg, eq_nat_or_neg, mod_cast
-/
lemma eq_on_nat_iff_eq_on_int {f g : AbsoluteValue R S} :
    (forall n : Nat, f n = g n) ↔ forall n : Int, f n = g n := by
  refine ⟨fun h z => ?_, fun a n => mod_cast a n⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp [h n]

end OrderedCommRing

section LinearOrderedRing

variable {R S : Type*} [Semiring R] [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

/-- `AbsoluteValue.abs` is `abs` as a bundled `AbsoluteValue`. -/
@[simps]
/--
Definition of `abs` / `abs` 的定义

English:
definition abs
  signature: : AbsoluteValue S S where
  body: abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add_le
  map_mul' := abs_mul

中文:
定义 abs
  签名: : 绝对值 S S where
  定义体: abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add_le
  map_mul' := abs_mul
-/
protected def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add_le
  map_mul' := abs_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AbsoluteValue S S)
  body: ⟨AbsoluteValue.abs⟩

中文:
实例 :
  签名: 可居 (绝对值 S S)
  定义体: ⟨AbsoluteValue.abs⟩

Depends on / 依赖: AbsoluteValue, AbsoluteValue.abs
-/
instance : Inhabited (AbsoluteValue S S) :=
  ⟨AbsoluteValue.abs⟩

end LinearOrderedRing

section LinearOrderedCommRing

variable {R S : Type*} [Ring R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

@[bound]
/--
theorem `abs_abv_sub_le_abv_sub` / 定理 `abs_abv_sub_le_abv_sub`

English:
theorem abs_abv_sub_le_abv_sub
  given: (a b : R)
  statement: abs (abv a - abv b) <= abv (a - b)
  proof: abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw [abv.map_sub]; apply abv.le_sub⟩

中文:
定理 abs_abv_sub_le_abv_sub
  条件: (a b : R)
  结论: abs (abv a - abv b) <= abv (a - b)
  证明: abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw [abv.map_sub]; apply abv.le_sub⟩

Depends on / 依赖: abs_sub_le_iff, abv.le_sub, abv.map_sub, le_sub, map_sub
-/
theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) <= abv (a - b) :=
  abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw [abv.map_sub]; apply abv.le_sub⟩

end LinearOrderedCommRing

section trivial

variable {R : Type*} [Semiring R] [DecidablePred fun x : R => x = 0] [NoZeroDivisors R]
variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [Nontrivial S]

/-- The *trivial* absolute value takes the value `1` on all nonzero elements. -/
protected
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : AbsoluteValue R S where
  body: if x = 0 then 0 else 1
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp [hx, hy]
  nonneg' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  eq_zero' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  add_le'

中文:
定义 trivial
  签名: : 绝对值 R S where
  定义体: if x = 0 then 0 else 1
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp [hx, hy]
  nonneg' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  eq_zero' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  add_le'
-/
def trivial : AbsoluteValue R S where
  toFun x := if x = 0 then 0 else 1
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp [hx, hy]
  nonneg' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  eq_zero' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  add_le' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp only [hx, ↓reduceIte, hy, one_add_one_eq_two]
    rcases eq_or_ne (x + y) 0 with hxy | hxy <;> simp [hxy, one_le_two]

@[simp]
/--
lemma `trivial_apply` / 引理 `trivial_apply`

English:
lemma trivial_apply
  given: {x : R} (hx : x != 0)
  statement: AbsoluteValue.trivial (S := S) x = 1
  proof: if_neg hx

中文:
引理 trivial_apply
  条件: {x : R} (hx : x != 0)
  结论: 绝对值.trivial (S := S) x = 1
  证明: if_neg hx
-/
lemma trivial_apply {x : R} (hx : x != 0) : AbsoluteValue.trivial (S := S) x = 1 :=
  if_neg hx

end trivial

section nontrivial

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

/--
Definition of `IsNontrivial` / `IsNontrivial` 的定义

English:
definition IsNontrivial
  signature: (v : AbsoluteValue R S)
  body: exists x != 0, v x != 1

中文:
定义 是非平凡
  签名: (v : 绝对值 R S)
  定义体: exists x != 0, v x != 1
-/
def IsNontrivial (v : AbsoluteValue R S) : Prop :=
  exists x != 0, v x != 1

/--
lemma `isNontrivial_iff_ne_trivial` / 引理 `isNontrivial_iff_ne_trivial`

English:
lemma isNontrivial_iff_ne_trivial
  statement: [DecidablePred fun x : R => x = 0] [NoZeroDivisors R]
  proof: by
refine ⟨fun ⟨x, hx₀, hx₁⟩ h => hx₁ h.symm ▸ trivial_apply hx₀, fun H => ?_⟩
  simp only [IsNontrivial]
  contrapose! H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

omit [IsOrderedRing S] in

中文:
引理 isNontrivial_iff_ne_trivial
  结论: [DecidablePred fun x : R => x = 0] [无零因子 R]
  证明: by
refine ⟨fun ⟨x, hx₀, hx₁⟩ h => hx₁ h.symm ▸ trivial_apply hx₀, fun H => ?_⟩
  simp only [IsNontrivial]
  contrapose! H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

omit [IsOrderedRing S] in

Depends on / 依赖: IsNontrivial, contrapose, eq_or_ne, h.symm, trivial_apply
-/
lemma isNontrivial_iff_ne_trivial [DecidablePred fun x : R => x = 0] [NoZeroDivisors R]
    [Nontrivial S] (v : AbsoluteValue R S) :
    v.IsNontrivial ↔ v != .trivial := by
refine ⟨fun ⟨x, hx₀, hx₁⟩ h => hx₁ h.symm ▸ trivial_apply hx₀, fun H => ?_⟩
  simp only [IsNontrivial]
  contrapose! H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

omit [IsOrderedRing S] in
/--
lemma `not_isNontrivial_iff` / 引理 `not_isNontrivial_iff`

English:
lemma not_isNontrivial_iff
  given: (v : AbsoluteValue R S)
  proof: by
  simp only [IsNontrivial]
  push Not
  rfl

omit [IsOrderedRing S] in
@[simp]

中文:
引理 not_isNontrivial_iff
  条件: (v : 绝对值 R S)
  证明: by
  simp only [IsNontrivial]
  push Not
  rfl

omit [IsOrderedRing S] in
@[simp]

Depends on / 依赖: IsNontrivial
-/
lemma not_isNontrivial_iff (v : AbsoluteValue R S) :
    ¬ v.IsNontrivial ↔ forall x != 0, v x = 1 := by
  simp only [IsNontrivial]
  push Not
  rfl

omit [IsOrderedRing S] in
@[simp]
/--
lemma `not_isNontrivial_apply` / 引理 `not_isNontrivial_apply`

English:
lemma not_isNontrivial_apply
  given: {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x : R} (hx : x != 0)
  proof: v.not_isNontrivial_iff.mp hv _ hx

中文:
引理 not_isNontrivial_apply
  条件: {v : 绝对值 R S} (hv : ¬ v.是非平凡) {x : R} (hx : x != 0)
  证明: v.not_isNontrivial_iff.mp hv _ hx

Depends on / 依赖: not_isNontrivial_iff, v.not_isNontrivial_iff.mp
-/
lemma not_isNontrivial_apply {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x : R} (hx : x != 0) :
    v x = 1 :=
  v.not_isNontrivial_iff.mp hv _ hx

end OrderedSemiring

section LinearOrderedSemifield

variable [Field R] [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] [ExistsAddOfLE S]
  {v : AbsoluteValue R S}

/--
lemma `IsNontrivial.exists_abv_gt_one` / 引理 `IsNontrivial.exists_abv_gt_one`

English:
lemma IsNontrivial.exists_abv_gt_one
  given: (h : v.IsNontrivial)
  statement: exists x, 1 < v x
  proof: by
  obtain ⟨x, hx₀, hx₁⟩ := h
  rcases hx₁.lt_or_gt with h | h
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ <| v.pos hx₀).mpr h
  · exact ⟨x, h⟩

中文:
引理 是非平凡.存在_abv_gt_one
  条件: (h : v.是非平凡)
  结论: 存在 x, 1 < v x
  证明: by
  obtain ⟨x, hx₀, hx₁⟩ := h
  rcases hx₁.lt_or_gt with h | h
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ <| v.pos hx₀).mpr h
  · exact ⟨x, h⟩

Depends on / 依赖: lt_or_gt, v.pos
-/
lemma IsNontrivial.exists_abv_gt_one (h : v.IsNontrivial) : exists x, 1 < v x := by
  obtain ⟨x, hx₀, hx₁⟩ := h
  rcases hx₁.lt_or_gt with h | h
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ <| v.pos hx₀).mpr h
  · exact ⟨x, h⟩

/--
lemma `IsNontrivial.exists_abv_lt_one` / 引理 `IsNontrivial.exists_abv_lt_one`

English:
lemma IsNontrivial.exists_abv_lt_one
  given: (h : v.IsNontrivial)
  statement: exists x != 0, v x < 1
  proof: by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
have hy₀ := v.ne_zero_iff.mp (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

中文:
引理 是非平凡.存在_abv_lt_one
  条件: (h : v.是非平凡)
  结论: 存在 x != 0, v x < 1
  证明: by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
have hy₀ := v.ne_zero_iff.mp (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

Depends on / 依赖: exists_abv_gt_one, h.exists_abv_gt_one, inv_ne_zero, ne_zero_iff, v.ne_zero_iff.mp, v.pos, zero_lt_one, zero_lt_one.trans
-/
lemma IsNontrivial.exists_abv_lt_one (h : v.IsNontrivial) : exists x != 0, v x < 1 := by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
have hy₀ := v.ne_zero_iff.mp (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

end LinearOrderedSemifield

end nontrivial

end AbsoluteValue

/--
Definition of `IsAbsoluteValue` / `IsAbsoluteValue` 的定义

English:
class IsAbsoluteValue
  parameters: {S} [Semiring S] [PartialOrder S] {R} [Semiring R] (f : R -> S)
  axioms and operations (4):
    - abv_nonneg' : forall x, 0 <= f x
    - abv_eq_zero' : forall {x}, f x = 0 ↔ x = 0
    - abv_add' : forall x y, f (x + y) <= f x + f y
    - abv_mul' : forall x y, f (x * y) = f x * f y

中文:
类 是绝对值
  参数: {S} [半环 S] [偏序 S] {R} [半环 R] (f : R -> S)
  公理与运算 (4 个):
    - abv_nonneg' : 对任意 x, 0 <= f x
    - abv_eq_zero' : 对任意 {x}, f x = 0 ↔ x = 0
    - abv_add' : 对任意 x y, f (x + y) <= f x + f y
    - abv_mul' : 对任意 x y, f (x * y) = f x * f y
-/
class IsAbsoluteValue {S} [Semiring S] [PartialOrder S] {R} [Semiring R] (f : R -> S) : Prop where
  /-- The absolute value is nonnegative -/
  abv_nonneg' : forall x, 0 <= f x
  /-- The absolute value is positive definitive -/
  abv_eq_zero' : forall {x}, f x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  abv_add' : forall x y, f (x + y) <= f x + f y
  /-- The absolute value is multiplicative -/
  abv_mul' : forall x y, f (x * y) = f x * f y

namespace IsAbsoluteValue

section OrderedSemiring

variable {S : Type*} [Semiring S] [PartialOrder S]
variable {R : Type*} [Semiring R] (abv : R -> S) [IsAbsoluteValue abv]

/--
lemma `abv_nonneg` / 引理 `abv_nonneg`

English:
lemma abv_nonneg
  given: (x)
  statement: 0 <= abv x
  proof: abv_nonneg' x

中文:
引理 abv_nonneg
  条件: (x)
  结论: 0 <= abv x
  证明: abv_nonneg' x

Depends on / 依赖: abv_nonneg
-/
lemma abv_nonneg (x) : 0 <= abv x := abv_nonneg' x

open Lean Meta Mathlib Meta Positivity Qq in
/-- The `positivity` extension which identifies expressions of the form `abv a`.
For performance reasons, we only attempt to apply this when `abv` is a variable.
If it is an explicit function, e.g. `|_|` or `‖_‖`, another extension should apply. -/
@[positivity _]
meta def Mathlib.Meta.Positivity.evalAbv : PositivityExt where eval {_ _α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let (.app f a) ← whnfR e | throwError "not abv ·"
  if !f.getAppFn.isFVar then
    throwError "abv: function is not a variable"
  let pa' ← mkAppM ``abv_nonneg #[f, a]
  pure (.nonnegative pa')

/--
lemma `abv_eq_zero` / 引理 `abv_eq_zero`

English:
lemma abv_eq_zero
  given: {x}
  statement: abv x = 0 ↔ x = 0
  proof: abv_eq_zero'

中文:
引理 abv_eq_zero
  条件: {x}
  结论: abv x = 0 ↔ x = 0
  证明: abv_eq_zero'

Depends on / 依赖: abv_eq_zero
-/
lemma abv_eq_zero {x} : abv x = 0 ↔ x = 0 := abv_eq_zero'

/--
lemma `abv_add` / 引理 `abv_add`

English:
lemma abv_add
  given: (x y)
  statement: abv (x + y) <= abv x + abv y
  proof: abv_add' x y

中文:
引理 abv_add
  条件: (x y)
  结论: abv (x + y) <= abv x + abv y
  证明: abv_add' x y

Depends on / 依赖: abv_add
-/
lemma abv_add (x y) : abv (x + y) <= abv x + abv y := abv_add' x y

/--
lemma `abv_mul` / 引理 `abv_mul`

English:
lemma abv_mul
  given: (x y)
  statement: abv (x * y) = abv x * abv y
  proof: abv_mul' x y

中文:
引理 abv_mul
  条件: (x y)
  结论: abv (x * y) = abv x * abv y
  证明: abv_mul' x y

Depends on / 依赖: abv_mul
-/
lemma abv_mul (x y) : abv (x * y) = abv x * abv y := abv_mul' x y

/--
Instance `_root_.AbsoluteValue.isAbsoluteValue` / 实例 `_root_.AbsoluteValue.isAbsoluteValue`

English:
instance _root_.AbsoluteValue.isAbsoluteValue
  signature: (abv : AbsoluteValue R S)
  body: abv.nonneg
  abv_eq_zero' := abv.eq_zero
  abv_add' := abv.add_le
  abv_mul' := abv.map_mul

中文:
实例 _root_.绝对值.isAbsoluteValue
  签名: (abv : 绝对值 R S)
  定义体: abv.nonneg
  abv_eq_zero' := abv.eq_zero
  abv_add' := abv.add_le
  abv_mul' := abv.map_mul

Depends on / 依赖: abv.nonneg, nonneg
-/
instance _root_.AbsoluteValue.isAbsoluteValue (abv : AbsoluteValue R S) : IsAbsoluteValue abv where
  abv_nonneg' := abv.nonneg
  abv_eq_zero' := abv.eq_zero
  abv_add' := abv.add_le
  abv_mul' := abv.map_mul

/-- Convert an unbundled `IsAbsoluteValue` to a bundled `AbsoluteValue`. -/
@[simps]
/--
Definition of `toAbsoluteValue` / `toAbsoluteValue` 的定义

English:
definition toAbsoluteValue
  signature: : AbsoluteValue R S where
  body: abv
  add_le' := abv_add'
  eq_zero' _ := abv_eq_zero'
  nonneg' := abv_nonneg'
  map_mul' := abv_mul'

中文:
定义 toAbsoluteValue
  签名: : 绝对值 R S where
  定义体: abv
  add_le' := abv_add'
  eq_zero' _ := abv_eq_zero'
  nonneg' := abv_nonneg'
  map_mul' := abv_mul'
-/
def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add'
  eq_zero' _ := abv_eq_zero'
  nonneg' := abv_nonneg'
  map_mul' := abv_mul'

/--
theorem `abv_zero` / 定理 `abv_zero`

English:
theorem abv_zero
  statement: abv 0 = 0
  proof: (toAbsoluteValue abv).map_zero

中文:
定理 abv_zero
  结论: abv 0 = 0
  证明: (toAbsoluteValue abv).map_zero

Depends on / 依赖: map_zero, toAbsoluteValue
-/
theorem abv_zero : abv 0 = 0 :=
  (toAbsoluteValue abv).map_zero

/--
theorem `abv_pos` / 定理 `abv_pos`

English:
theorem abv_pos
  given: {a : R}
  statement: 0 < abv a ↔ a != 0
  proof: (toAbsoluteValue abv).pos_iff

中文:
定理 abv_pos
  条件: {a : R}
  结论: 0 < abv a ↔ a != 0
  证明: (toAbsoluteValue abv).pos_iff

Depends on / 依赖: pos_iff, toAbsoluteValue
-/
theorem abv_pos {a : R} : 0 < abv a ↔ a != 0 :=
  (toAbsoluteValue abv).pos_iff

end OrderedSemiring

section LinearOrderedRing

variable {S : Type*} [Ring S] [LinearOrder S] [IsStrictOrderedRing S]

/--
Instance `abs_isAbsoluteValue` / 实例 `abs_isAbsoluteValue`

English:
instance abs_isAbsoluteValue
  signature: : IsAbsoluteValue (abs : S -> S)
  body: AbsoluteValue.abs.isAbsoluteValue

中文:
实例 abs_isAbsoluteValue
  签名: : 是绝对值 (abs : S -> S)
  定义体: AbsoluteValue.abs.isAbsoluteValue

Depends on / 依赖: AbsoluteValue, AbsoluteValue.abs.isAbsoluteValue, isAbsoluteValue
-/
instance abs_isAbsoluteValue : IsAbsoluteValue (abs : S -> S) :=
  AbsoluteValue.abs.isAbsoluteValue

end LinearOrderedRing

section OrderedRing

variable {S : Type*} [Ring S] [PartialOrder S]

section Semiring

variable {R : Type*} [Semiring R] (abv : R -> S) [IsAbsoluteValue abv]
variable [IsDomain S]

/--
theorem `abv_one` / 定理 `abv_one`

English:
theorem abv_one
  given: [Nontrivial R]
  statement: abv 1 = 1
  proof: (toAbsoluteValue abv).map_one

中文:
定理 abv_one
  条件: [非平凡 R]
  结论: abv 1 = 1
  证明: (toAbsoluteValue abv).map_one

Depends on / 依赖: map_one, toAbsoluteValue
-/
theorem abv_one [Nontrivial R] : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one

/--
Definition of `abvHom` / `abvHom` 的定义

English:
definition abvHom
  signature: [Nontrivial R]
  body: (toAbsoluteValue abv).toMonoidWithZeroHom

中文:
定义 abvHom
  签名: [非平凡 R]
  定义体: (toAbsoluteValue abv).toMonoidWithZeroHom

Depends on / 依赖: toAbsoluteValue, toMonoidWithZeroHom
-/
def abvHom [Nontrivial R] : R ->*₀ S :=
  (toAbsoluteValue abv).toMonoidWithZeroHom

/--
theorem `abv_pow` / 定理 `abv_pow`

English:
theorem abv_pow
  given: [Nontrivial R] (abv : R -> S) [IsAbsoluteValue abv] (a : R) (n : Nat)
  proof: (toAbsoluteValue abv).map_pow a n

中文:
定理 abv_pow
  条件: [非平凡 R] (abv : R -> S) [是绝对值 abv] (a : R) (n : 自然数)
  证明: (toAbsoluteValue abv).map_pow a n

Depends on / 依赖: map_pow, toAbsoluteValue
-/
theorem abv_pow [Nontrivial R] (abv : R -> S) [IsAbsoluteValue abv] (a : R) (n : Nat) :
    abv (a ^ n) = abv a ^ n :=
  (toAbsoluteValue abv).map_pow a n

end Semiring

section Ring

variable {R : Type*} [Ring R] (abv : R -> S) [IsAbsoluteValue abv]

/--
theorem `abv_sub_le` / 定理 `abv_sub_le`

English:
theorem abv_sub_le
  given: (a b c : R)
  statement: abv (a - c) <= abv (a - b) + abv (b - c)
  proof: by
  simpa [sub_eq_add_neg, add_assoc] using abv_add abv (a - b) (b - c)

中文:
定理 abv_sub_le
  条件: (a b c : R)
  结论: abv (a - c) <= abv (a - b) + abv (b - c)
  证明: by
  simpa [sub_eq_add_neg, add_assoc] using abv_add abv (a - b) (b - c)

Depends on / 依赖: abv_add, add_assoc, sub_eq_add_neg
-/
theorem abv_sub_le (a b c : R) : abv (a - c) <= abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv_add abv (a - b) (b - c)

/--
theorem `sub_abv_le_abv_sub` / 定理 `sub_abv_le_abv_sub`

English:
theorem sub_abv_le_abv_sub
  given: [IsOrderedRing S] (a b : R)
  statement: abv a - abv b <= abv (a - b)
  proof: (toAbsoluteValue abv).le_sub a b

中文:
定理 sub_abv_le_abv_sub
  条件: [是Ordered环 S] (a b : R)
  结论: abv a - abv b <= abv (a - b)
  证明: (toAbsoluteValue abv).le_sub a b

Depends on / 依赖: le_sub, toAbsoluteValue
-/
theorem sub_abv_le_abv_sub [IsOrderedRing S] (a b : R) : abv a - abv b <= abv (a - b) :=
  (toAbsoluteValue abv).le_sub a b

end Ring

end OrderedRing

section OrderedCommRing
variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [NoZeroDivisors S] [Ring R]
  (abv : R -> S) [IsAbsoluteValue abv]

/--
theorem `abv_neg` / 定理 `abv_neg`

English:
theorem abv_neg
  given: (a : R)
  statement: abv (-a) = abv a
  proof: (toAbsoluteValue abv).map_neg a

中文:
定理 abv_neg
  条件: (a : R)
  结论: abv (-a) = abv a
  证明: (toAbsoluteValue abv).map_neg a

Depends on / 依赖: map_neg, toAbsoluteValue
-/
theorem abv_neg (a : R) : abv (-a) = abv a :=
  (toAbsoluteValue abv).map_neg a

/--
theorem `abv_sub` / 定理 `abv_sub`

English:
theorem abv_sub
  given: (a b : R)
  statement: abv (a - b) = abv (b - a)
  proof: (toAbsoluteValue abv).map_sub a b

中文:
定理 abv_sub
  条件: (a b : R)
  结论: abv (a - b) = abv (b - a)
  证明: (toAbsoluteValue abv).map_sub a b

Depends on / 依赖: map_sub, toAbsoluteValue
-/
theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) :=
  (toAbsoluteValue abv).map_sub a b

end OrderedCommRing

section LinearOrderedCommRing

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

section Ring

variable {R : Type*} [Ring R] (abv : R -> S) [IsAbsoluteValue abv]

/--
theorem `abs_abv_sub_le_abv_sub` / 定理 `abs_abv_sub_le_abv_sub`

English:
theorem abs_abv_sub_le_abv_sub
  given: (a b : R)
  statement: abs (abv a - abv b) <= abv (a - b)
  proof: (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b

中文:
定理 abs_abv_sub_le_abv_sub
  条件: (a b : R)
  结论: abs (abv a - abv b) <= abv (a - b)
  证明: (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b

Depends on / 依赖: abs_abv_sub_le_abv_sub, toAbsoluteValue
-/
theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) <= abv (a - b) :=
  (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b

end Ring

end LinearOrderedCommRing

section IsCancelMulZero

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [IsCancelMulZero S]

section Semiring

variable {R : Type*} [Semiring R] [Nontrivial R] (abv : R -> S) [IsAbsoluteValue abv]

omit [IsOrderedRing S] in
/--
theorem `abv_one'` / 定理 `abv_one'`

English:
theorem abv_one'
  statement: abv 1 = 1
  proof: (toAbsoluteValue abv).map_one_of_isLeftRegular
    (IsRegular.of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left

中文:
定理 abv_one'
  结论: abv 1 = 1
  证明: (toAbsoluteValue abv).map_one_of_isLeftRegular
    (IsRegular.of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, map_one_of_isLeftRegular, ne_zero, of_ne_zero, one_ne_zero, toAbsoluteValue
-/
theorem abv_one' : abv 1 = 1 :=
(toAbsoluteValue abv).map_one_of_isLeftRegular
    (IsRegular.of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left

/--
Definition of `abvHom'` / `abvHom'` 的定义

English:
definition abvHom'
  signature: : R ->*₀ S where
  body: abv; map_zero' := abv_zero abv; map_one' := abv_one' abv; map_mul' := abv_mul abv

中文:
定义 abvHom'
  签名: : R ->*₀ S where
  定义体: abv; map_zero' := abv_zero abv; map_one' := abv_one' abv; map_mul' := abv_mul abv

Depends on / 依赖: abv_mul, abv_one, abv_zero, map_mul, map_one, map_zero
-/
def abvHom' : R ->*₀ S where
  toFun := abv; map_zero' := abv_zero abv; map_one' := abv_one' abv; map_mul' := abv_mul abv

end Semiring

end IsCancelMulZero

section LinearOrderedSemifield

variable {S : Type*} [Semifield S] [LinearOrder S]

section DivisionSemiring

variable {R : Type*} [DivisionSemiring R] (abv : R -> S) [IsAbsoluteValue abv]

/--
theorem `abv_inv` / 定理 `abv_inv`

English:
theorem abv_inv
  given: (a : R)
  statement: abv a⁻¹ = (abv a)⁻¹
  proof: map_inv₀ (abvHom' abv) a

中文:
定理 abv_inv
  条件: (a : R)
  结论: abv a⁻¹ = (abv a)⁻¹
  证明: map_inv₀ (abvHom' abv) a

Depends on / 依赖: abvHom
-/
theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  map_inv₀ (abvHom' abv) a

/--
theorem `abv_div` / 定理 `abv_div`

English:
theorem abv_div
  given: (a b : R)
  statement: abv (a / b) = abv a / abv b
  proof: map_div₀ (abvHom' abv) a b

中文:
定理 abv_div
  条件: (a b : R)
  结论: abv (a / b) = abv a / abv b
  证明: map_div₀ (abvHom' abv) a b

Depends on / 依赖: abvHom
-/
theorem abv_div (a b : R) : abv (a / b) = abv a / abv b :=
  map_div₀ (abvHom' abv) a b

end DivisionSemiring

end LinearOrderedSemifield

end IsAbsoluteValue
