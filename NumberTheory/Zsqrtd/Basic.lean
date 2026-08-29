/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Associated
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.EuclideanDomain.Int

/-! # ℤ[√d]

The ring of integers adjoined with a square root of `d : ℤ`.

After defining the norm, we show that it is a linearly ordered commutative ring,
as well as an integral domain.

We provide the universal property, that ring homomorphisms `ℤ√d →+* R` correspond
to choices of square roots of `d` in `R`.

-/

@[expose] public section


/-- The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case. -/
@[ext]
/--
Definition of `Zsqrtd` / `Zsqrtd` 的定义

English:
structure Zsqrtd
  parameters: (d : Int)
  axioms and operations (2):
    - re : Int
    - im : Int

中文:
结构 Zsqrtd
  参数: (d : 整数)
  公理与运算 (2 个):
    - re : 整数
    - im : 整数
-/
structure Zsqrtd (d : Int) where
  /-- Component of the integer not multiplied by `√d` -/
  re : Int
  /-- Component of the integer multiplied by `√d` -/
  im : Int
  deriving DecidableEq

@[inherit_doc] prefix:100 "Int√" => Zsqrtd

namespace Zsqrtd

section

variable {d : Int}

/--
Definition of `ofInt` / `ofInt` 的定义

English:
definition ofInt
  signature: (n : Int)
  body: ⟨n, 0⟩

中文:
定义 of整数
  签名: (n : 整数)
  定义体: ⟨n, 0⟩
-/
def ofInt (n : Int) : Int√d :=
  ⟨n, 0⟩

/--
theorem `re_ofInt` / 定理 `re_ofInt`

English:
theorem re_ofInt
  given: (n : Int)
  statement: (ofInt n : Int√d).re = n
  proof: rfl

中文:
定理 re_of整数
  条件: (n : 整数)
  结论: (of整数 n : 整数√d).re = n
  证明: rfl
-/
theorem re_ofInt (n : Int) : (ofInt n : Int√d).re = n :=
  rfl

/--
theorem `im_ofInt` / 定理 `im_ofInt`

English:
theorem im_ofInt
  given: (n : Int)
  statement: (ofInt n : Int√d).im = 0
  proof: rfl

中文:
定理 im_of整数
  条件: (n : 整数)
  结论: (of整数 n : 整数√d).im = 0
  证明: rfl
-/
theorem im_ofInt (n : Int) : (ofInt n : Int√d).im = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Int√d)
  body: ⟨ofInt 0⟩

@[simp]

中文:
实例 :
  签名: 零 (整数√d)
  定义体: ⟨ofInt 0⟩

@[simp]
-/
instance : Zero (Int√d) :=
  ⟨ofInt 0⟩

@[simp]
/--
theorem `re_zero` / 定理 `re_zero`

English:
theorem re_zero
  statement: (0 : Int√d).re = 0
  proof: rfl

@[simp]

中文:
定理 re_zero
  结论: (0 : 整数√d).re = 0
  证明: rfl

@[simp]
-/
theorem re_zero : (0 : Int√d).re = 0 :=
  rfl

@[simp]
/--
theorem `im_zero` / 定理 `im_zero`

English:
theorem im_zero
  statement: (0 : Int√d).im = 0
  proof: rfl

中文:
定理 im_zero
  结论: (0 : 整数√d).im = 0
  证明: rfl
-/
theorem im_zero : (0 : Int√d).im = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Int√d)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (整数√d)
  定义体: ⟨0⟩
-/
instance : Inhabited (Int√d) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Int√d)
  body: ⟨ofInt 1⟩

@[simp]

中文:
实例 :
  签名: 幺 (整数√d)
  定义体: ⟨ofInt 1⟩

@[simp]
-/
instance : One (Int√d) :=
  ⟨ofInt 1⟩

@[simp]
/--
theorem `re_one` / 定理 `re_one`

English:
theorem re_one
  statement: (1 : Int√d).re = 1
  proof: rfl

@[simp]

中文:
定理 re_one
  结论: (1 : 整数√d).re = 1
  证明: rfl

@[simp]
-/
theorem re_one : (1 : Int√d).re = 1 :=
  rfl

@[simp]
/--
theorem `im_one` / 定理 `im_one`

English:
theorem im_one
  statement: (1 : Int√d).im = 0
  proof: rfl

中文:
定理 im_one
  结论: (1 : 整数√d).im = 0
  证明: rfl
-/
theorem im_one : (1 : Int√d).im = 0 :=
  rfl

/--
Definition of `sqrtd` / `sqrtd` 的定义

English:
definition sqrtd
  signature: : Int√d
  body: ⟨0, 1⟩

@[simp]

中文:
定义 sqrtd
  签名: : 整数√d
  定义体: ⟨0, 1⟩

@[simp]
-/
def sqrtd : Int√d :=
  ⟨0, 1⟩

@[simp]
/--
theorem `re_sqrtd` / 定理 `re_sqrtd`

English:
theorem re_sqrtd
  statement: (sqrtd : Int√d).re = 0
  proof: rfl

@[simp]

中文:
定理 re_sqrtd
  结论: (sqrtd : 整数√d).re = 0
  证明: rfl

@[simp]
-/
theorem re_sqrtd : (sqrtd : Int√d).re = 0 :=
  rfl

@[simp]
/--
theorem `im_sqrtd` / 定理 `im_sqrtd`

English:
theorem im_sqrtd
  statement: (sqrtd : Int√d).im = 1
  proof: rfl

中文:
定理 im_sqrtd
  结论: (sqrtd : 整数√d).im = 1
  证明: rfl
-/
theorem im_sqrtd : (sqrtd : Int√d).im = 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Int√d)
  body: ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]

中文:
实例 :
  签名: 加法 (整数√d)
  定义体: ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
-/
instance : Add (Int√d) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
/--
theorem `add_def` / 定理 `add_def`

English:
theorem add_def
  given: (x y x' y' : Int)
  statement: (⟨x, y⟩ + ⟨x', y'⟩ : Int√d) = ⟨x + x', y + y'⟩
  proof: rfl

@[simp]

中文:
定理 add_def
  条件: (x y x' y' : 整数)
  结论: (⟨x, y⟩ + ⟨x', y'⟩ : 整数√d) = ⟨x + x', y + y'⟩
  证明: rfl

@[simp]
-/
theorem add_def (x y x' y' : Int) : (⟨x, y⟩ + ⟨x', y'⟩ : Int√d) = ⟨x + x', y + y'⟩ :=
  rfl

@[simp]
/--
theorem `re_add` / 定理 `re_add`

English:
theorem re_add
  given: (z w : Int√d)
  statement: (z + w).re = z.re + w.re
  proof: rfl

@[simp]

中文:
定理 re_add
  条件: (z w : 整数√d)
  结论: (z + w).re = z.re + w.re
  证明: rfl

@[simp]
-/
theorem re_add (z w : Int√d) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
/--
theorem `im_add` / 定理 `im_add`

English:
theorem im_add
  given: (z w : Int√d)
  statement: (z + w).im = z.im + w.im
  proof: rfl

中文:
定理 im_add
  条件: (z w : 整数√d)
  结论: (z + w).im = z.im + w.im
  证明: rfl
-/
theorem im_add (z w : Int√d) : (z + w).im = z.im + w.im :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (Int√d)
  body: ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]

中文:
实例 :
  签名: 取负 (整数√d)
  定义体: ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]
-/
instance : Neg (Int√d) :=
  ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]
/--
theorem `re_neg` / 定理 `re_neg`

English:
theorem re_neg
  given: (z : Int√d)
  statement: (-z).re = -z.re
  proof: rfl

@[simp]

中文:
定理 re_neg
  条件: (z : 整数√d)
  结论: (-z).re = -z.re
  证明: rfl

@[simp]
-/
theorem re_neg (z : Int√d) : (-z).re = -z.re :=
  rfl

@[simp]
/--
theorem `im_neg` / 定理 `im_neg`

English:
theorem im_neg
  given: (z : Int√d)
  statement: (-z).im = -z.im
  proof: rfl

中文:
定理 im_neg
  条件: (z : 整数√d)
  结论: (-z).im = -z.im
  证明: rfl
-/
theorem im_neg (z : Int√d) : (-z).im = -z.im :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Int√d)
  body: ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]

中文:
实例 :
  签名: 乘法 (整数√d)
  定义体: ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]
-/
instance : Mul (Int√d) :=
  ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]
/--
theorem `re_mul` / 定理 `re_mul`

English:
theorem re_mul
  given: (z w : Int√d)
  statement: (z * w).re = z.re * w.re + d * z.im * w.im
  proof: rfl

@[simp]

中文:
定理 re_mul
  条件: (z w : 整数√d)
  结论: (z * w).re = z.re * w.re + d * z.im * w.im
  证明: rfl

@[simp]
-/
theorem re_mul (z w : Int√d) : (z * w).re = z.re * w.re + d * z.im * w.im :=
  rfl

@[simp]
/--
theorem `im_mul` / 定理 `im_mul`

English:
theorem im_mul
  given: (z w : Int√d)
  statement: (z * w).im = z.re * w.im + z.im * w.re
  proof: rfl

中文:
定理 im_mul
  条件: (z w : 整数√d)
  结论: (z * w).im = z.re * w.im + z.im * w.re
  证明: rfl
-/
theorem im_mul (z w : Int√d) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup (Int√d)
  body: by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]

中文:
实例 addCommGroup
  签名: : 加法交换群 (整数√d)
  定义体: by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]

Depends on / 依赖: Neg.neg, add_assoc, add_comm, add_left_comm, add_zero, intros, neg_add_cancel, nsmulRec, zero_add, zsmulRec
-/
instance addCommGroup : AddCommGroup (Int√d) := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (Int√d) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]
/--
theorem `re_sub` / 定理 `re_sub`

English:
theorem re_sub
  given: (z w : Int√d)
  statement: (z - w).re = z.re - w.re
  proof: rfl

@[simp]

中文:
定理 re_sub
  条件: (z w : 整数√d)
  结论: (z - w).re = z.re - w.re
  证明: rfl

@[simp]
-/
theorem re_sub (z w : Int√d) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
/--
theorem `im_sub` / 定理 `im_sub`

English:
theorem im_sub
  given: (z w : Int√d)
  statement: (z - w).im = z.im - w.im
  proof: rfl

中文:
定理 im_sub
  条件: (z w : 整数√d)
  结论: (z - w).im = z.im - w.im
  证明: rfl
-/
theorem im_sub (z w : Int√d) : (z - w).im = z.im - w.im :=
  rfl

/--
Instance `addGroupWithOne` / 实例 `addGroupWithOne`

English:
instance addGroupWithOne
  signature: : AddGroupWithOne (Int√d)
  body: { Zsqrtd.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

中文:
实例 addGroupWithOne
  签名: : 加法带幺群 (整数√d)
  定义体: { Zsqrtd.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

Depends on / 依赖: Zsqrtd, Zsqrtd.addCommGroup, addCommGroup, intCast, natCast
-/
instance addGroupWithOne : AddGroupWithOne (Int√d) :=
  { Zsqrtd.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing (Int√d)
  body: by
  refine
  { Zsqrtd.addGroupWithOne with
    npow := @npowRec (Int√d) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

中文:
实例 commRing
  签名: : 交换环 (整数√d)
  定义体: by
  refine
  { Zsqrtd.addGroupWithOne with
    npow := @npowRec (Int√d) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

Depends on / 依赖: Zsqrtd, Zsqrtd.addGroupWithOne, addGroupWithOne, add_comm, intros, left_distrib, mul_assoc, mul_comm, mul_one, mul_zero, npowRec, one_mul, right_distrib, zero_mul
-/
instance commRing : CommRing (Int√d) := by
  refine
  { Zsqrtd.addGroupWithOne with
    npow := @npowRec (Int√d) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 加法幺半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddMonoid (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 幺半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Monoid (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 交换幺半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommMonoid (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemigroup (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 交换半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommSemigroup (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semigroup (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Semigroup (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommSemigroup (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 加法交换半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddCommSemigroup (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSemigroup (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 加法半群 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddSemigroup (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 交换半环 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommSemiring (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 半环 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Semiring (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: 环 (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Ring (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Distrib (Int√d)
  body: by infer_instance

中文:
实例 :
  签名: Distrib (整数√d)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Distrib (Int√d) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (Int√d)
  body: ⟨z.1, -z.2⟩

@[simp]

中文:
实例 :
  签名: 对合 (整数√d)
  定义体: ⟨z.1, -z.2⟩

@[simp]
-/
instance : Star (Int√d) where
  star z := ⟨z.1, -z.2⟩

@[simp]
/--
theorem `star_mk` / 定理 `star_mk`

English:
theorem star_mk
  given: (x y : Int)
  statement: star (⟨x, y⟩ : Int√d) = ⟨x, -y⟩
  proof: rfl

@[simp]

中文:
定理 star_mk
  条件: (x y : 整数)
  结论: star (⟨x, y⟩ : 整数√d) = ⟨x, -y⟩
  证明: rfl

@[simp]
-/
theorem star_mk (x y : Int) : star (⟨x, y⟩ : Int√d) = ⟨x, -y⟩ :=
  rfl

@[simp]
/--
theorem `re_star` / 定理 `re_star`

English:
theorem re_star
  given: (z : Int√d)
  statement: (star z).re = z.re
  proof: rfl

@[simp]

中文:
定理 re_star
  条件: (z : 整数√d)
  结论: (star z).re = z.re
  证明: rfl

@[simp]
-/
theorem re_star (z : Int√d) : (star z).re = z.re :=
  rfl

@[simp]
/--
theorem `im_star` / 定理 `im_star`

English:
theorem im_star
  given: (z : Int√d)
  statement: (star z).im = -z.im
  proof: rfl

中文:
定理 im_star
  条件: (z : 整数√d)
  结论: (star z).im = -z.im
  证明: rfl
-/
theorem im_star (z : Int√d) : (star z).im = -z.im :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (Int√d)
  body: Zsqrtd.ext rfl (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add _ _ := Zsqrtd.ext rfl (neg_add _ _)

中文:
实例 :
  签名: 对合环 (整数√d)
  定义体: Zsqrtd.ext rfl (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add _ _ := Zsqrtd.ext rfl (neg_add _ _)

Depends on / 依赖: Zsqrtd, Zsqrtd.ext, neg_neg
-/
instance : StarRing (Int√d) where
  star_involutive _ := Zsqrtd.ext rfl (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add _ _ := Zsqrtd.ext rfl (neg_add _ _)

-- Porting note: proof was `by decide`
/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: : Nontrivial (Int√d)
  body: ⟨⟨0, 1, Zsqrtd.ext_iff.not.mpr (by simp)⟩⟩

@[simp]

中文:
实例 nontrivial
  签名: : 非平凡 (整数√d)
  定义体: ⟨⟨0, 1, Zsqrtd.ext_iff.not.mpr (by simp)⟩⟩

@[simp]

Depends on / 依赖: Zsqrtd, Zsqrtd.ext_iff.not.mpr, ext_iff
-/
instance nontrivial : Nontrivial (Int√d) :=
  ⟨⟨0, 1, Zsqrtd.ext_iff.not.mpr (by simp)⟩⟩

@[simp]
/--
theorem `re_natCast` / 定理 `re_natCast`

English:
theorem re_natCast
  given: (n : Nat)
  statement: (n : Int√d).re = n
  proof: rfl

@[simp]

中文:
定理 re_natCast
  条件: (n : 自然数)
  结论: (n : 整数√d).re = n
  证明: rfl

@[simp]
-/
theorem re_natCast (n : Nat) : (n : Int√d).re = n :=
  rfl

@[simp]
/--
theorem `re_ofNat` / 定理 `re_ofNat`

English:
theorem re_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : Int√d).re = n
  proof: rfl

@[simp]

中文:
定理 re_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : 整数√d).re = n
  证明: rfl

@[simp]
-/
theorem re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Int√d).re = n :=
  rfl

@[simp]
/--
theorem `im_natCast` / 定理 `im_natCast`

English:
theorem im_natCast
  given: (n : Nat)
  statement: (n : Int√d).im = 0
  proof: rfl

@[simp]

中文:
定理 im_natCast
  条件: (n : 自然数)
  结论: (n : 整数√d).im = 0
  证明: rfl

@[simp]
-/
theorem im_natCast (n : Nat) : (n : Int√d).im = 0 :=
  rfl

@[simp]
/--
theorem `im_ofNat` / 定理 `im_ofNat`

English:
theorem im_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : Int√d).im = 0
  proof: rfl

中文:
定理 im_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : 整数√d).im = 0
  证明: rfl
-/
theorem im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Int√d).im = 0 :=
  rfl

/--
theorem `natCast_val` / 定理 `natCast_val`

English:
theorem natCast_val
  given: (n : Nat)
  statement: (n : Int√d) = ⟨n, 0⟩
  proof: rfl

@[simp]

中文:
定理 natCast_val
  条件: (n : 自然数)
  结论: (n : 整数√d) = ⟨n, 0⟩
  证明: rfl

@[simp]
-/
theorem natCast_val (n : Nat) : (n : Int√d) = ⟨n, 0⟩ :=
  rfl

@[simp]
/--
theorem `re_intCast` / 定理 `re_intCast`

English:
theorem re_intCast
  given: (n : Int)
  statement: (n : Int√d).re = n
  proof: by cases n <;> rfl

@[simp]

中文:
定理 re_intCast
  条件: (n : 整数)
  结论: (n : 整数√d).re = n
  证明: by cases n <;> rfl

@[simp]
-/
theorem re_intCast (n : Int) : (n : Int√d).re = n := by cases n <;> rfl

@[simp]
/--
theorem `im_intCast` / 定理 `im_intCast`

English:
theorem im_intCast
  given: (n : Int)
  statement: (n : Int√d).im = 0
  proof: by cases n <;> rfl

中文:
定理 im_intCast
  条件: (n : 整数)
  结论: (n : 整数√d).im = 0
  证明: by cases n <;> rfl
-/
theorem im_intCast (n : Int) : (n : Int√d).im = 0 := by cases n <;> rfl

/--
theorem `intCast_val` / 定理 `intCast_val`

English:
theorem intCast_val
  given: (n : Int)
  statement: (n : Int√d) = ⟨n, 0⟩
  proof: by ext <;> simp

中文:
定理 intCast_val
  条件: (n : 整数)
  结论: (n : 整数√d) = ⟨n, 0⟩
  证明: by ext <;> simp
-/
theorem intCast_val (n : Int) : (n : Int√d) = ⟨n, 0⟩ := by ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharZero (Int√d)
  body: by simp [Zsqrtd.ext_iff]

@[simp]

中文:
实例 :
  签名: 特征零 (整数√d)
  定义体: by simp [Zsqrtd.ext_iff]

@[simp]

Depends on / 依赖: Zsqrtd, Zsqrtd.ext_iff, ext_iff
-/
instance : CharZero (Int√d) where cast_injective m n := by simp [Zsqrtd.ext_iff]

@[simp]
/--
theorem `ofInt_eq_intCast` / 定理 `ofInt_eq_intCast`

English:
theorem ofInt_eq_intCast
  given: (n : Int)
  statement: (ofInt n : Int√d) = n
  proof: by ext <;> simp [re_ofInt, im_ofInt]

@[simp]

中文:
定理 of整数_eq_intCast
  条件: (n : 整数)
  结论: (of整数 n : 整数√d) = n
  证明: by ext <;> simp [re_ofInt, im_ofInt]

@[simp]

Depends on / 依赖: im_ofInt, re_ofInt
-/
theorem ofInt_eq_intCast (n : Int) : (ofInt n : Int√d) = n := by ext <;> simp [re_ofInt, im_ofInt]

@[simp]
/--
theorem `nsmul_val` / 定理 `nsmul_val`

English:
theorem nsmul_val
  given: (n : Nat) (x y : Int)
  statement: (n : Int√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
  proof: by ext <;> simp

@[simp]

中文:
定理 nsmul_val
  条件: (n : 自然数) (x y : 整数)
  结论: (n : 整数√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
  证明: by ext <;> simp

@[simp]
-/
theorem nsmul_val (n : Nat) (x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by ext <;> simp

@[simp]
/--
theorem `smul_val` / 定理 `smul_val`

English:
theorem smul_val
  given: (n x y : Int)
  statement: (n : Int√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
  proof: by ext <;> simp

中文:
定理 smul_val
  条件: (n x y : 整数)
  结论: (n : 整数√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
  证明: by ext <;> simp
-/
theorem smul_val (n x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by ext <;> simp

/--
theorem `re_smul` / 定理 `re_smul`

English:
theorem re_smul
  given: (a : Int) (b : Int√d)
  statement: (↑a * b).re = a * b.re
  proof: by simp

中文:
定理 re_smul
  条件: (a : 整数) (b : 整数√d)
  结论: (↑a * b).re = a * b.re
  证明: by simp
-/
theorem re_smul (a : Int) (b : Int√d) : (↑a * b).re = a * b.re := by simp

/--
theorem `im_smul` / 定理 `im_smul`

English:
theorem im_smul
  given: (a : Int) (b : Int√d)
  statement: (↑a * b).im = a * b.im
  proof: by simp

@[simp]

中文:
定理 im_smul
  条件: (a : 整数) (b : 整数√d)
  结论: (↑a * b).im = a * b.im
  证明: by simp

@[simp]
-/
theorem im_smul (a : Int) (b : Int√d) : (↑a * b).im = a * b.im := by simp

@[simp]
/--
theorem `muld_val` / 定理 `muld_val`

English:
theorem muld_val
  given: (x y : Int)
  statement: sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩
  proof: by ext <;> simp

@[simp]

中文:
定理 muld_val
  条件: (x y : 整数)
  结论: sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩
  证明: by ext <;> simp

@[simp]
-/
theorem muld_val (x y : Int) : sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩ := by ext <;> simp

@[simp]
/--
theorem `dmuld` / 定理 `dmuld`

English:
theorem dmuld
  statement: sqrtd (d := d) * sqrtd (d := d) = d
  proof: by ext <;> simp

@[simp]

中文:
定理 dmuld
  结论: sqrtd (d := d) * sqrtd (d := d) = d
  证明: by ext <;> simp

@[simp]
-/
theorem dmuld : sqrtd (d := d) * sqrtd (d := d) = d := by ext <;> simp

@[simp]
/--
theorem `smuld_val` / 定理 `smuld_val`

English:
theorem smuld_val
  given: (n x y : Int)
  statement: sqrtd * (n : Int√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩
  proof: by ext <;> simp

中文:
定理 smuld_val
  条件: (n x y : 整数)
  结论: sqrtd * (n : 整数√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩
  证明: by ext <;> simp
-/
theorem smuld_val (n x y : Int) : sqrtd * (n : Int√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ := by ext <;> simp

/--
theorem `decompose` / 定理 `decompose`

English:
theorem decompose
  given: {x y : Int}
  statement: (⟨x, y⟩ : Int√d) = x + sqrtd (d := d) * y
  proof: by ext <;> simp

中文:
定理 decompose
  条件: {x y : 整数}
  结论: (⟨x, y⟩ : 整数√d) = x + sqrtd (d := d) * y
  证明: by ext <;> simp
-/
theorem decompose {x y : Int} : (⟨x, y⟩ : Int√d) = x + sqrtd (d := d) * y := by ext <;> simp

/--
theorem `mul_star` / 定理 `mul_star`

English:
theorem mul_star
  given: {x y : Int}
  statement: (⟨x, y⟩ * star ⟨x, y⟩ : Int√d) = x * x - d * y * y
  proof: by
  ext <;> simp [sub_eq_add_neg, mul_comm]

中文:
定理 mul_star
  条件: {x y : 整数}
  结论: (⟨x, y⟩ * star ⟨x, y⟩ : 整数√d) = x * x - d * y * y
  证明: by
  ext <;> simp [sub_eq_add_neg, mul_comm]

Depends on / 依赖: mul_comm, sub_eq_add_neg
-/
theorem mul_star {x y : Int} : (⟨x, y⟩ * star ⟨x, y⟩ : Int√d) = x * x - d * y * y := by
  ext <;> simp [sub_eq_add_neg, mul_comm]

/--
theorem `intCast_dvd` / 定理 `intCast_dvd`

English:
theorem intCast_dvd
  given: (z : Int) (a : Int√d)
  statement: ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im
  proof: by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val]; rw [Zsqrtd.ext_iff]
    exact ⟨hr, hi⟩

@[simp, norm_cast]

中文:
定理 intCast_dvd
  条件: (z : 整数) (a : 整数√d)
  结论: ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im
  证明: by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val]; rw [Zsqrtd.ext_iff]
    exact ⟨hr, hi⟩

@[simp, norm_cast]

Depends on / 依赖: Zsqrtd, Zsqrtd.ext_iff, ext_iff, smul_val
-/
theorem intCast_dvd (z : Int) (a : Int√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val]; rw [Zsqrtd.ext_iff]
    exact ⟨hr, hi⟩

@[simp, norm_cast]
/--
theorem `intCast_dvd_intCast` / 定理 `intCast_dvd_intCast`

English:
theorem intCast_dvd_intCast
  given: (a b : Int)
  statement: (a : Int√d) ∣ b ↔ a ∣ b
  proof: by
  rw [intCast_dvd]
  simp

中文:
定理 intCast_dvd_intCast
  条件: (a b : 整数)
  结论: (a : 整数√d) ∣ b ↔ a ∣ b
  证明: by
  rw [intCast_dvd]
  simp

Depends on / 依赖: intCast_dvd
-/
theorem intCast_dvd_intCast (a b : Int) : (a : Int√d) ∣ b ↔ a ∣ b := by
  rw [intCast_dvd]
  simp

/--
theorem `eq_of_smul_eq_smul_left` / 定理 `eq_of_smul_eq_smul_left`

English:
theorem eq_of_smul_eq_smul_left
  given: {a : Int} {b c : Int√d} (ha : a != 0) (h : ↑a * b = a * c)
  proof: by
  rw [Zsqrtd.ext_iff] at h ⊢
  apply And.imp _ _ h <;> simpa only [re_smul, im_smul] using mul_left_cancel₀ ha

中文:
定理 eq_of_smul_eq_smul_left
  条件: {a : 整数} {b c : 整数√d} (ha : a != 0) (h : ↑a * b = a * c)
  证明: by
  rw [Zsqrtd.ext_iff] at h ⊢
  apply And.imp _ _ h <;> simpa only [re_smul, im_smul] using mul_left_cancel₀ ha
-/
protected theorem eq_of_smul_eq_smul_left {a : Int} {b c : Int√d} (ha : a != 0) (h : ↑a * b = a * c) :
    b = c := by
  rw [Zsqrtd.ext_iff] at h ⊢
  apply And.imp _ _ h <;> simpa only [re_smul, im_smul] using mul_left_cancel₀ ha

section Gcd

/--
theorem `gcd_eq_zero_iff` / 定理 `gcd_eq_zero_iff`

English:
theorem gcd_eq_zero_iff
  given: (a : Int√d)
  statement: Int.gcd a.re a.im = 0 ↔ a = 0
  proof: by
  simp only [Int.gcd_eq_zero_iff, Zsqrtd.ext_iff, im_zero, re_zero]

中文:
定理 gcd_eq_zero_iff
  条件: (a : 整数√d)
  结论: 整数.最大公约数 a.re a.im = 0 ↔ a = 0
  证明: by
  simp only [Int.gcd_eq_zero_iff, Zsqrtd.ext_iff, im_zero, re_zero]

Depends on / 依赖: Int.gcd_eq_zero_iff, Zsqrtd, Zsqrtd.ext_iff, ext_iff, gcd_eq_zero_iff, im_zero, re_zero
-/
theorem gcd_eq_zero_iff (a : Int√d) : Int.gcd a.re a.im = 0 ↔ a = 0 := by
  simp only [Int.gcd_eq_zero_iff, Zsqrtd.ext_iff, im_zero, re_zero]

/--
theorem `gcd_pos_iff` / 定理 `gcd_pos_iff`

English:
theorem gcd_pos_iff
  given: (a : Int√d)
  statement: 0 < Int.gcd a.re a.im ↔ a != 0
  proof: pos_iff_ne_zero.trans not_congr a.gcd_eq_zero_iff

中文:
定理 gcd_pos_iff
  条件: (a : 整数√d)
  结论: 0 < 整数.最大公约数 a.re a.im ↔ a != 0
  证明: pos_iff_ne_zero.trans not_congr a.gcd_eq_zero_iff

Depends on / 依赖: a.gcd_eq_zero_iff, gcd_eq_zero_iff, not_congr, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
theorem gcd_pos_iff (a : Int√d) : 0 < Int.gcd a.re a.im ↔ a != 0 :=
pos_iff_ne_zero.trans not_congr a.gcd_eq_zero_iff

/--
theorem `isCoprime_of_dvd_isCoprime` / 定理 `isCoprime_of_dvd_isCoprime`

English:
theorem isCoprime_of_dvd_isCoprime
  given: {a b : Int√d} (hcoprime : IsCoprime a.re a.im) (hdvd : b ∣ a)
  proof: by
  apply isCoprime_of_dvd
  · rintro ⟨hre, him⟩
    obtain rfl : b = 0 := Zsqrtd.ext hre him
    rw [zero_dvd_iff] at hdvd
    simp [hdvd, im_zero, re_zero, not_isCoprime_zero_zero] at hcoprime
  · rintro z hz - hzdvdu hzdvdv
    apply hz
    obtain ⟨ha, hb⟩ : z ∣ a.re ∧ z ∣ a.im := by
      rw [← intCast_dvd]
      apply dvd_trans _ hdvd
      rw [intCast_dvd]
      exact ⟨hzdvdu, hzdvdv⟩
    exact hcoprime.isUnit_of_dvd' ha hb

中文:
定理 isCoprime_of_dvd_isCoprime
  条件: {a b : 整数√d} (hcoprime : IsCoprime a.re a.im) (hdvd : b ∣ a)
  证明: by
  apply isCoprime_of_dvd
  · rintro ⟨hre, him⟩
    obtain rfl : b = 0 := Zsqrtd.ext hre him
    rw [zero_dvd_iff] at hdvd
    simp [hdvd, im_zero, re_zero, not_isCoprime_zero_zero] at hcoprime
  · rintro z hz - hzdvdu hzdvdv
    apply hz
    obtain ⟨ha, hb⟩ : z ∣ a.re ∧ z ∣ a.im := by
      rw [← intCast_dvd]
      apply dvd_trans _ hdvd
      rw [intCast_dvd]
      exact ⟨hzdvdu, hzdvdv⟩
    exact hcoprime.isUnit_of_dvd' ha hb

Depends on / 依赖: Zsqrtd, Zsqrtd.ext, a.im, a.re, dvd_trans, hcoprime, hcoprime.isUnit_of_dvd, hzdvdu, hzdvdv, im_zero, intCast_dvd, isCoprime_of_dvd, isUnit_of_dvd, not_isCoprime_zero_zero, re_zero, zero_dvd_iff
-/
theorem isCoprime_of_dvd_isCoprime {a b : Int√d} (hcoprime : IsCoprime a.re a.im) (hdvd : b ∣ a) :
    IsCoprime b.re b.im := by
  apply isCoprime_of_dvd
  · rintro ⟨hre, him⟩
    obtain rfl : b = 0 := Zsqrtd.ext hre him
    rw [zero_dvd_iff] at hdvd
    simp [hdvd, im_zero, re_zero, not_isCoprime_zero_zero] at hcoprime
  · rintro z hz - hzdvdu hzdvdv
    apply hz
    obtain ⟨ha, hb⟩ : z ∣ a.re ∧ z ∣ a.im := by
      rw [← intCast_dvd]
      apply dvd_trans _ hdvd
      rw [intCast_dvd]
      exact ⟨hzdvdu, hzdvdv⟩
    exact hcoprime.isUnit_of_dvd' ha hb

/--
theorem `exists_coprime_of_gcd_pos` / 定理 `exists_coprime_of_gcd_pos`

English:
theorem exists_coprime_of_gcd_pos
  given: {a : Int√d} (hgcd : 0 < Int.gcd a.re a.im)
  proof: by
  obtain ⟨re, im, H1, Hre, Him⟩ := Int.exists_gcd_one hgcd
  rw [mul_comm] at Hre Him
  refine ⟨⟨re, im⟩, ?_, ?_⟩
  · rw [smul_val, ← Hre, ← Him]
  · rw [Int.isCoprime_iff_gcd_eq_one, H1]

中文:
定理 存在_coprime_of_gcd_pos
  条件: {a : 整数√d} (hgcd : 0 < 整数.最大公约数 a.re a.im)
  证明: by
  obtain ⟨re, im, H1, Hre, Him⟩ := Int.exists_gcd_one hgcd
  rw [mul_comm] at Hre Him
  refine ⟨⟨re, im⟩, ?_, ?_⟩
  · rw [smul_val, ← Hre, ← Him]
  · rw [Int.isCoprime_iff_gcd_eq_one, H1]

Depends on / 依赖: Int.exists_gcd_one, Int.isCoprime_iff_gcd_eq_one, exists_gcd_one, isCoprime_iff_gcd_eq_one, mul_comm, smul_val
-/
theorem exists_coprime_of_gcd_pos {a : Int√d} (hgcd : 0 < Int.gcd a.re a.im) :
    exists b : Int√d, a = ((Int.gcd a.re a.im : Int) : Int√d) * b ∧ IsCoprime b.re b.im := by
  obtain ⟨re, im, H1, Hre, Him⟩ := Int.exists_gcd_one hgcd
  rw [mul_comm] at Hre Him
  refine ⟨⟨re, im⟩, ?_, ?_⟩
  · rw [smul_val, ← Hre, ← Him]
  · rw [Int.isCoprime_iff_gcd_eq_one, H1]

end Gcd

/--
Definition of `SqLe` / `SqLe` 的定义

English:
definition SqLe
  signature: (a c b d : Nat)
  body: c * a * a <= d * b * b

中文:
定义 SqLe
  签名: (a c b d : 自然数)
  定义体: c * a * a <= d * b * b
-/
def SqLe (a c b d : Nat) : Prop :=
  c * a * a <= d * b * b

/--
theorem `sqLe_of_le` / 定理 `sqLe_of_le`

English:
theorem sqLe_of_le
  given: {c d x y z w : Nat} (xz : z <= x) (yw : y <= w) (xy : SqLe x c y d)
  proof: calc
  c * z * z <= c * x * x := by gcongr
  _ <= d * y * y := xy
  _ <= d * w * w := by gcongr

中文:
定理 sqLe_of_le
  条件: {c d x y z w : 自然数} (xz : z <= x) (yw : y <= w) (xy : SqLe x c y d)
  证明: calc
  c * z * z <= c * x * x := by gcongr
  _ <= d * y * y := xy
  _ <= d * w * w := by gcongr
-/
theorem sqLe_of_le {c d x y z w : Nat} (xz : z <= x) (yw : y <= w) (xy : SqLe x c y d) :
    SqLe z c w d := calc
  c * z * z <= c * x * x := by gcongr
  _ <= d * y * y := xy
  _ <= d * w * w := by gcongr

/--
theorem `sqLe_add_mixed` / 定理 `sqLe_add_mixed`

English:
theorem sqLe_add_mixed
  given: {c d x y z w : Nat} (xy : SqLe x c y d) (zw : SqLe z c w d)
  proof: Nat.mul_self_le_mul_self_iff.1 by
    simpa [mul_comm, mul_left_comm] using Nat.mul_le_mul xy zw

中文:
定理 sqLe_add_mixed
  条件: {c d x y z w : 自然数} (xy : SqLe x c y d) (zw : SqLe z c w d)
  证明: Nat.mul_self_le_mul_self_iff.1 by
    simpa [mul_comm, mul_left_comm] using Nat.mul_le_mul xy zw

Depends on / 依赖: Nat.mul_le_mul, Nat.mul_self_le_mul_self_iff, mul_comm, mul_le_mul, mul_left_comm, mul_self_le_mul_self_iff
-/
theorem sqLe_add_mixed {c d x y z w : Nat} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    c * (x * z) <= d * (y * w) :=
Nat.mul_self_le_mul_self_iff.1 by
    simpa [mul_comm, mul_left_comm] using Nat.mul_le_mul xy zw

/--
theorem `sqLe_add` / 定理 `sqLe_add`

English:
theorem sqLe_add
  given: {c d x y z w : Nat} (xy : SqLe x c y d) (zw : SqLe z c w d)
  proof: by
  have xz := sqLe_add_mixed xy zw
  simp only [SqLe, mul_assoc] at xy zw
  simp [SqLe, mul_add, mul_comm, mul_left_comm, add_le_add, *]

中文:
定理 sqLe_add
  条件: {c d x y z w : 自然数} (xy : SqLe x c y d) (zw : SqLe z c w d)
  证明: by
  have xz := sqLe_add_mixed xy zw
  simp only [SqLe, mul_assoc] at xy zw
  simp [SqLe, mul_add, mul_comm, mul_left_comm, add_le_add, *]

Depends on / 依赖: add_le_add, mul_add, mul_assoc, mul_comm, mul_left_comm, sqLe_add_mixed
-/
theorem sqLe_add {c d x y z w : Nat} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    SqLe (x + z) c (y + w) d := by
  have xz := sqLe_add_mixed xy zw
  simp only [SqLe, mul_assoc] at xy zw
  simp [SqLe, mul_add, mul_comm, mul_left_comm, add_le_add, *]

/--
theorem `sqLe_cancel` / 定理 `sqLe_cancel`

English:
theorem sqLe_cancel
  given: {c d x y z w : Nat} (zw : SqLe y d x c) (h : SqLe (x + z) c (y + w) d)
  proof: by
  apply le_of_not_gt
  intro l
  refine not_le_of_gt ?_ h
  simp only [mul_add, mul_comm, mul_left_comm, add_assoc]
  have hm := sqLe_add_mixed zw (le_of_lt l)
  simp only [SqLe, mul_assoc] at l zw
  grw [zw, hm]
  gcongr

中文:
定理 sqLe_cancel
  条件: {c d x y z w : 自然数} (zw : SqLe y d x c) (h : SqLe (x + z) c (y + w) d)
  证明: by
  apply le_of_not_gt
  intro l
  refine not_le_of_gt ?_ h
  simp only [mul_add, mul_comm, mul_left_comm, add_assoc]
  have hm := sqLe_add_mixed zw (le_of_lt l)
  simp only [SqLe, mul_assoc] at l zw
  grw [zw, hm]
  gcongr

Depends on / 依赖: add_assoc, le_of_lt, le_of_not_gt, mul_add, mul_assoc, mul_comm, mul_left_comm, not_le_of_gt, sqLe_add_mixed
-/
theorem sqLe_cancel {c d x y z w : Nat} (zw : SqLe y d x c) (h : SqLe (x + z) c (y + w) d) :
    SqLe z c w d := by
  apply le_of_not_gt
  intro l
  refine not_le_of_gt ?_ h
  simp only [mul_add, mul_comm, mul_left_comm, add_assoc]
  have hm := sqLe_add_mixed zw (le_of_lt l)
  simp only [SqLe, mul_assoc] at l zw
  grw [zw, hm]
  gcongr

/--
theorem `sqLe_smul` / 定理 `sqLe_smul`

English:
theorem sqLe_smul
  given: {c d x y : Nat} (n : Nat) (xy : SqLe x c y d)
  statement: SqLe (n * x) c (n * y) d
  proof: by
  simpa [SqLe, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left (n * n) xy

中文:
定理 sqLe_smul
  条件: {c d x y : 自然数} (n : 自然数) (xy : SqLe x c y d)
  结论: SqLe (n * x) c (n * y) d
  证明: by
  simpa [SqLe, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left (n * n) xy

Depends on / 依赖: Nat.mul_le_mul_left, mul_assoc, mul_le_mul_left, mul_left_comm
-/
theorem sqLe_smul {c d x y : Nat} (n : Nat) (xy : SqLe x c y d) : SqLe (n * x) c (n * y) d := by
  simpa [SqLe, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left (n * n) xy

/--
theorem `sqLe_mul` / 定理 `sqLe_mul`

English:
theorem sqLe_mul
  given: {d x y z w : Nat}
  proof: by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro xy zw
      have :=
        Int.mul_nonneg (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le xy))
          (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le zw))
      refine Int.le_of_ofNat_le_ofNat (le_of_sub_nonneg ?_)
      convert! this using 1
      simp only [one_mul, Int.natCast_add, Int.natCast_mul]
      ring

中文:
定理 sqLe_mul
  条件: {d x y z w : 自然数}
  证明: by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro xy zw
      have :=
        Int.mul_nonneg (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le xy))
          (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le zw))
      refine Int.le_of_ofNat_le_ofNat (le_of_sub_nonneg ?_)
      convert! this using 1
      simp only [one_mul, Int.natCast_add, Int.natCast_mul]
      ring

Depends on / 依赖: Int.le_of_ofNat_le_ofNat, Int.mul_nonneg, Int.natCast_add, Int.natCast_mul, Int.ofNat_le_ofNat_of_le, convert, le_of_ofNat_le_ofNat, le_of_sub_nonneg, mul_nonneg, natCast_add, natCast_mul, ofNat_le_ofNat_of_le, one_mul, sub_nonneg_of_le
-/
theorem sqLe_mul {d x y z w : Nat} :
    (SqLe x 1 y d -> SqLe z 1 w d -> SqLe (x * w + y * z) d (x * z + d * y * w) 1) ∧
      (SqLe x 1 y d -> SqLe w d z 1 -> SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
        (SqLe y d x 1 -> SqLe z 1 w d -> SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
          (SqLe y d x 1 -> SqLe w d z 1 -> SqLe (x * w + y * z) d (x * z + d * y * w) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro xy zw
      have :=
        Int.mul_nonneg (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le xy))
          (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le zw))
      refine Int.le_of_ofNat_le_ofNat (le_of_sub_nonneg ?_)
      convert! this using 1
      simp only [one_mul, Int.natCast_add, Int.natCast_mul]
      ring

open Int in
/--
Definition of `Nonnegg` / `Nonnegg` 的定义

English:
definition Nonnegg
  signature: (c d : Nat)

中文:
定义 Nonnegg
  签名: (c d : 自然数)
-/
def Nonnegg (c d : Nat) : Int -> Int -> Prop
  | (a : Nat), (b : Nat) => True
  | (a : Nat), -[b+1] => SqLe (b + 1) c a d
  | -[a+1], (b : Nat) => SqLe (a + 1) d b c
  | -[_+1], -[_+1] => False

/--
theorem `nonnegg_comm` / 定理 `nonnegg_comm`

English:
theorem nonnegg_comm
  given: {c d : Nat} {x y : Int}
  statement: Nonnegg c d x y = Nonnegg d c y x
  proof: by
  cases x <;> cases y <;> rfl

中文:
定理 nonnegg_comm
  条件: {c d : 自然数} {x y : 整数}
  结论: Nonnegg c d x y = Nonnegg d c y x
  证明: by
  cases x <;> cases y <;> rfl
-/
theorem nonnegg_comm {c d : Nat} {x y : Int} : Nonnegg c d x y = Nonnegg d c y x := by
  cases x <;> cases y <;> rfl

/--
theorem `nonnegg_neg_pos` / 定理 `nonnegg_neg_pos`

English:
theorem nonnegg_neg_pos
  given: {c d}
  statement: forall {a b : Nat}, Nonnegg c d (-a) b ↔ SqLe a d b c

中文:
定理 nonnegg_neg_pos
  条件: {c d}
  结论: 对任意 {a b : 自然数}, Nonnegg c d (-a) b ↔ SqLe a d b c
-/
theorem nonnegg_neg_pos {c d} : forall {a b : Nat}, Nonnegg c d (-a) b ↔ SqLe a d b c
  | 0, b => ⟨by simp [SqLe], fun _ => trivial⟩
  | a + 1, b => by rfl

/--
theorem `nonnegg_pos_neg` / 定理 `nonnegg_pos_neg`

English:
theorem nonnegg_pos_neg
  given: {c d} {a b : Nat}
  statement: Nonnegg c d a (-b) ↔ SqLe b c a d
  proof: by
  rw [nonnegg_comm]; exact nonnegg_neg_pos

中文:
定理 nonnegg_pos_neg
  条件: {c d} {a b : 自然数}
  结论: Nonnegg c d a (-b) ↔ SqLe b c a d
  证明: by
  rw [nonnegg_comm]; exact nonnegg_neg_pos

Depends on / 依赖: nonnegg_comm, nonnegg_neg_pos
-/
theorem nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d a (-b) ↔ SqLe b c a d := by
  rw [nonnegg_comm]; exact nonnegg_neg_pos

open Int in
/--
theorem `nonnegg_cases_right` / 定理 `nonnegg_cases_right`

English:
theorem nonnegg_cases_right
  given: {c d} {a : Nat}

中文:
定理 nonnegg_cases_right
  条件: {c d} {a : 自然数}
-/
theorem nonnegg_cases_right {c d} {a : Nat} :
    forall {b : Int}, (forall x : Nat, b = -x -> SqLe x c a d) -> Nonnegg c d a b
  | (b : Nat), _ => trivial
  | -[b+1], h => h (b + 1) rfl

/--
theorem `nonnegg_cases_left` / 定理 `nonnegg_cases_left`

English:
theorem nonnegg_cases_left
  given: {c d} {b : Nat} {a : Int} (h : forall x : Nat, a = -x -> SqLe x d b c)
  proof: cast nonnegg_comm (nonnegg_cases_right h)

中文:
定理 nonnegg_cases_left
  条件: {c d} {b : 自然数} {a : 整数} (h : 对任意 x : 自然数, a = -x -> SqLe x d b c)
  证明: cast nonnegg_comm (nonnegg_cases_right h)

Depends on / 依赖: nonnegg_cases_right, nonnegg_comm
-/
theorem nonnegg_cases_left {c d} {b : Nat} {a : Int} (h : forall x : Nat, a = -x -> SqLe x d b c) :
    Nonnegg c d a b :=
  cast nonnegg_comm (nonnegg_cases_right h)

section Norm

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: (n : Int√d)
  body: n.re * n.re - d * n.im * n.im

中文:
定义 norm
  签名: (n : 整数√d)
  定义体: n.re * n.re - d * n.im * n.im

Depends on / 依赖: n.im, n.re
-/
def norm (n : Int√d) : Int :=
  n.re * n.re - d * n.im * n.im

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (n : Int√d)
  statement: n.norm = n.re * n.re - d * n.im * n.im
  proof: rfl

@[simp]

中文:
定理 norm_def
  条件: (n : 整数√d)
  结论: n.norm = n.re * n.re - d * n.im * n.im
  证明: rfl

@[simp]
-/
theorem norm_def (n : Int√d) : n.norm = n.re * n.re - d * n.im * n.im :=
  rfl

@[simp]
/--
theorem `norm_zero` / 定理 `norm_zero`

English:
theorem norm_zero
  statement: norm (0 : Int√d) = 0
  proof: by simp [norm]

@[simp]

中文:
定理 norm_zero
  结论: norm (0 : 整数√d) = 0
  证明: by simp [norm]

@[simp]
-/
theorem norm_zero : norm (0 : Int√d) = 0 := by simp [norm]

@[simp]
/--
theorem `norm_one` / 定理 `norm_one`

English:
theorem norm_one
  statement: norm (1 : Int√d) = 1
  proof: by simp [norm]

@[simp]

中文:
定理 norm_one
  结论: norm (1 : 整数√d) = 1
  证明: by simp [norm]

@[simp]
-/
theorem norm_one : norm (1 : Int√d) = 1 := by simp [norm]

@[simp]
/--
theorem `norm_intCast` / 定理 `norm_intCast`

English:
theorem norm_intCast
  given: (n : Int)
  statement: norm (n : Int√d) = n * n
  proof: by simp [norm]

@[simp]

中文:
定理 norm_intCast
  条件: (n : 整数)
  结论: norm (n : 整数√d) = n * n
  证明: by simp [norm]

@[simp]
-/
theorem norm_intCast (n : Int) : norm (n : Int√d) = n * n := by simp [norm]

@[simp]
/--
theorem `norm_natCast` / 定理 `norm_natCast`

English:
theorem norm_natCast
  given: (n : Nat)
  statement: norm (n : Int√d) = n * n
  proof: norm_intCast n

@[simp]

中文:
定理 norm_natCast
  条件: (n : 自然数)
  结论: norm (n : 整数√d) = n * n
  证明: norm_intCast n

@[simp]

Depends on / 依赖: norm_intCast
-/
theorem norm_natCast (n : Nat) : norm (n : Int√d) = n * n :=
  norm_intCast n

@[simp]
/--
theorem `norm_mul` / 定理 `norm_mul`

English:
theorem norm_mul
  given: (n m : Int√d)
  statement: norm (n * m) = norm n * norm m
  proof: by
  simp only [norm, im_mul, re_mul]
  ring

中文:
定理 norm_mul
  条件: (n m : 整数√d)
  结论: norm (n * m) = norm n * norm m
  证明: by
  simp only [norm, im_mul, re_mul]
  ring

Depends on / 依赖: im_mul, re_mul
-/
theorem norm_mul (n m : Int√d) : norm (n * m) = norm n * norm m := by
  simp only [norm, im_mul, re_mul]
  ring

/--
Definition of `normMonoidHom` / `normMonoidHom` 的定义

English:
definition normMonoidHom
  signature: : Int√d ->* Int where
  body: norm
  map_mul' := norm_mul
  map_one' := norm_one

中文:
定义 normMonoidHom
  签名: : 整数√d ->* 整数 where
  定义体: norm
  map_mul' := norm_mul
  map_one' := norm_one
-/
def normMonoidHom : Int√d ->* Int where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one

/--
theorem `norm_eq_mul_conj` / 定理 `norm_eq_mul_conj`

English:
theorem norm_eq_mul_conj
  given: (n : Int√d)
  statement: (norm n : Int√d) = n * star n
  proof: by
  ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]

@[simp]

中文:
定理 norm_eq_mul_conj
  条件: (n : 整数√d)
  结论: (norm n : 整数√d) = n * star n
  证明: by
  ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]

@[simp]

Depends on / 依赖: mul_comm, sub_eq_add_neg
-/
theorem norm_eq_mul_conj (n : Int√d) : (norm n : Int√d) = n * star n := by
  ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]

@[simp]
/--
theorem `norm_neg` / 定理 `norm_neg`

English:
theorem norm_neg
  given: (x : Int√d)
  statement: (-x).norm = x.norm
  proof: (Int.cast_inj (α := Int√d)).1 by simp [norm_eq_mul_conj]

@[simp]

中文:
定理 norm_neg
  条件: (x : 整数√d)
  结论: (-x).norm = x.norm
  证明: (Int.cast_inj (α := Int√d)).1 by simp [norm_eq_mul_conj]

@[simp]

Depends on / 依赖: Int.cast_inj, cast_inj, norm_eq_mul_conj
-/
theorem norm_neg (x : Int√d) : (-x).norm = x.norm :=
(Int.cast_inj (α := Int√d)).1 by simp [norm_eq_mul_conj]

@[simp]
/--
theorem `norm_conj` / 定理 `norm_conj`

English:
theorem norm_conj
  given: (x : Int√d)
  statement: (star x).norm = x.norm
  proof: (Int.cast_inj (α := Int√d)).1 by simp [norm_eq_mul_conj, mul_comm]

中文:
定理 norm_conj
  条件: (x : 整数√d)
  结论: (star x).norm = x.norm
  证明: (Int.cast_inj (α := Int√d)).1 by simp [norm_eq_mul_conj, mul_comm]

Depends on / 依赖: Int.cast_inj, cast_inj, mul_comm, norm_eq_mul_conj
-/
theorem norm_conj (x : Int√d) : (star x).norm = x.norm :=
(Int.cast_inj (α := Int√d)).1 by simp [norm_eq_mul_conj, mul_comm]

/--
theorem `norm_nonneg` / 定理 `norm_nonneg`

English:
theorem norm_nonneg
  given: (hd : d <= 0) (n : Int√d)
  statement: 0 <= n.norm
  proof: add_nonneg (mul_self_nonneg _)
    (by
      rw [mul_assoc]; rw [neg_mul_eq_neg_mul]
      exact mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _))

@[simp]

中文:
定理 norm_nonneg
  条件: (hd : d <= 0) (n : 整数√d)
  结论: 0 <= n.norm
  证明: add_nonneg (mul_self_nonneg _)
    (by
      rw [mul_assoc]; rw [neg_mul_eq_neg_mul]
      exact mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _))

@[simp]

Depends on / 依赖: add_nonneg, mul_assoc, mul_nonneg, mul_self_nonneg, neg_mul_eq_neg_mul, neg_nonneg
-/
theorem norm_nonneg (hd : d <= 0) (n : Int√d) : 0 <= n.norm :=
  add_nonneg (mul_self_nonneg _)
    (by
      rw [mul_assoc]; rw [neg_mul_eq_neg_mul]
      exact mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _))

@[simp]
/--
theorem `abs_norm` / 定理 `abs_norm`

English:
theorem abs_norm
  given: (hd : d <= 0) (n : Int√d)
  statement: |n.norm| = n.norm
  proof: abs_of_nonneg norm_nonneg hd n

中文:
定理 abs_norm
  条件: (hd : d <= 0) (n : 整数√d)
  结论: |n.norm| = n.norm
  证明: abs_of_nonneg norm_nonneg hd n

Depends on / 依赖: abs_of_nonneg, norm_nonneg
-/
theorem abs_norm (hd : d <= 0) (n : Int√d) : |n.norm| = n.norm :=
abs_of_nonneg norm_nonneg hd n

/--
theorem `norm_eq_one_iff` / 定理 `norm_eq_one_iff`

English:
theorem norm_eq_one_iff
  given: {x : Int√d}
  statement: x.norm.natAbs = 1 ↔ IsUnit x
  proof: ⟨fun h =>
isUnit_iff_dvd_one.2
      (le_total 0 (norm x)).casesOn
        (fun hx =>
          ⟨star x, by
            rwa [← Int.natCast_inj, Int.natAbs_of_nonneg hx, ← @Int.cast_inj (Int√d) _ _,
              norm_eq_mul_conj, eq_comm] at h⟩)
        fun hx =>
          ⟨-star x, by
            rwa [← Int.natCast_inj, Int.ofNat_natAbs_of_nonpos hx, ← @Int.cast_inj (Int√d) _ _,
              Int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg, eq_comm] at h⟩,
    fun h => by
    let ⟨y, hy⟩ := isUnit_iff_dvd_one.1 h
    have := congr_arg (Int.natAbs ∘ norm) hy
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [norm_mul]; rw [Int.natAbs_mul]; rw [norm_one]; rw [Int.natAbs_one]; rw [eq_comm]; rw [mul_eq_one] at this
    exact this.1⟩

中文:
定理 norm_eq_one_iff
  条件: {x : 整数√d}
  结论: x.norm.natAbs = 1 ↔ 是单位 x
  证明: ⟨fun h =>
isUnit_iff_dvd_one.2
      (le_total 0 (norm x)).casesOn
        (fun hx =>
          ⟨star x, by
            rwa [← Int.natCast_inj, Int.natAbs_of_nonneg hx, ← @Int.cast_inj (Int√d) _ _,
              norm_eq_mul_conj, eq_comm] at h⟩)
        fun hx =>
          ⟨-star x, by
            rwa [← Int.natCast_inj, Int.ofNat_natAbs_of_nonpos hx, ← @Int.cast_inj (Int√d) _ _,
              Int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg, eq_comm] at h⟩,
    fun h => by
    let ⟨y, hy⟩ := isUnit_iff_dvd_one.1 h
    have := congr_arg (Int.natAbs ∘ norm) hy
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [norm_mul]; rw [Int.natAbs_mul]; rw [norm_one]; rw [Int.natAbs_one]; rw [eq_comm]; rw [mul_eq_one] at this
    exact this.1⟩

Depends on / 依赖: Function, Function.comp_apply, Int.cast_inj, Int.cast_neg, Int.natAbs, Int.natAbs_of_nonneg, Int.natCast_inj, Int.ofNat_natAbs_of_nonpos, casesOn, cast_inj, cast_neg, comp_apply, congr_arg, eq_comm, isUnit_iff_dvd_one, le_total, natAbs, natAbs_of_nonneg, natCast_inj, neg_mul_eq_mul_neg
-/
theorem norm_eq_one_iff {x : Int√d} : x.norm.natAbs = 1 ↔ IsUnit x :=
  ⟨fun h =>
isUnit_iff_dvd_one.2
      (le_total 0 (norm x)).casesOn
        (fun hx =>
          ⟨star x, by
            rwa [← Int.natCast_inj, Int.natAbs_of_nonneg hx, ← @Int.cast_inj (Int√d) _ _,
              norm_eq_mul_conj, eq_comm] at h⟩)
        fun hx =>
          ⟨-star x, by
            rwa [← Int.natCast_inj, Int.ofNat_natAbs_of_nonpos hx, ← @Int.cast_inj (Int√d) _ _,
              Int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg, eq_comm] at h⟩,
    fun h => by
    let ⟨y, hy⟩ := isUnit_iff_dvd_one.1 h
    have := congr_arg (Int.natAbs ∘ norm) hy
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [norm_mul]; rw [Int.natAbs_mul]; rw [norm_one]; rw [Int.natAbs_one]; rw [eq_comm]; rw [mul_eq_one] at this
    exact this.1⟩

/--
theorem `isUnit_iff_norm_isUnit` / 定理 `isUnit_iff_norm_isUnit`

English:
theorem isUnit_iff_norm_isUnit
  given: {d : Int} (z : Int√d)
  statement: IsUnit z ↔ IsUnit z.norm
  proof: by
  rw [Int.isUnit_iff_natAbs_eq]; rw [norm_eq_one_iff]

中文:
定理 isUnit_iff_norm_isUnit
  条件: {d : 整数} (z : 整数√d)
  结论: 是单位 z ↔ 是单位 z.norm
  证明: by
  rw [Int.isUnit_iff_natAbs_eq]; rw [norm_eq_one_iff]

Depends on / 依赖: Int.isUnit_iff_natAbs_eq, isUnit_iff_natAbs_eq, norm_eq_one_iff
-/
theorem isUnit_iff_norm_isUnit {d : Int} (z : Int√d) : IsUnit z ↔ IsUnit z.norm := by
  rw [Int.isUnit_iff_natAbs_eq]; rw [norm_eq_one_iff]

/--
theorem `norm_eq_one_iff'` / 定理 `norm_eq_one_iff'`

English:
theorem norm_eq_one_iff'
  given: {d : Int} (hd : d <= 0) (z : Int√d)
  statement: z.norm = 1 ↔ IsUnit z
  proof: by
  rw [← norm_eq_one_iff]; rw [← Int.natCast_inj]; rw [Int.natAbs_of_nonneg (norm_nonneg hd z)]; rw [Int.ofNat_one]

中文:
定理 norm_eq_one_iff'
  条件: {d : 整数} (hd : d <= 0) (z : 整数√d)
  结论: z.norm = 1 ↔ 是单位 z
  证明: by
  rw [← norm_eq_one_iff]; rw [← Int.natCast_inj]; rw [Int.natAbs_of_nonneg (norm_nonneg hd z)]; rw [Int.ofNat_one]

Depends on / 依赖: Int.natAbs_of_nonneg, Int.natCast_inj, Int.ofNat_one, natAbs_of_nonneg, natCast_inj, norm_eq_one_iff, norm_nonneg, ofNat_one
-/
theorem norm_eq_one_iff' {d : Int} (hd : d <= 0) (z : Int√d) : z.norm = 1 ↔ IsUnit z := by
  rw [← norm_eq_one_iff]; rw [← Int.natCast_inj]; rw [Int.natAbs_of_nonneg (norm_nonneg hd z)]; rw [Int.ofNat_one]

/--
theorem `norm_eq_zero_iff` / 定理 `norm_eq_zero_iff`

English:
theorem norm_eq_zero_iff
  given: {d : Int} (hd : d < 0) (z : Int√d)
  statement: z.norm = 0 ↔ z = 0
  proof: by
  constructor
  · intro h
    rw [norm_def]; rw [sub_eq_add_neg]; rw [mul_assoc] at h
    have left := mul_self_nonneg z.re
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im))
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg left right).mp h
    ext <;> apply eq_zero_of_mul_self_eq_zero
    · exact ha
    · rw [neg_eq_zero, mul_eq_zero] at hb
      exact hb.resolve_left hd.ne
  · rintro rfl
    exact norm_zero

中文:
定理 norm_eq_zero_iff
  条件: {d : 整数} (hd : d < 0) (z : 整数√d)
  结论: z.norm = 0 ↔ z = 0
  证明: by
  constructor
  · intro h
    rw [norm_def]; rw [sub_eq_add_neg]; rw [mul_assoc] at h
    have left := mul_self_nonneg z.re
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im))
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg left right).mp h
    ext <;> apply eq_zero_of_mul_self_eq_zero
    · exact ha
    · rw [neg_eq_zero, mul_eq_zero] at hb
      exact hb.resolve_left hd.ne
  · rintro rfl
    exact norm_zero

Depends on / 依赖: add_eq_zero_iff_of_nonneg, eq_zero_of_mul_self_eq_zero, hb.resolve_left, hd.le, hd.ne, mul_assoc, mul_eq_zero, mul_nonpos_of_nonpos_of_nonneg, mul_self_nonneg, neg_eq_zero, neg_nonneg, neg_nonneg.mpr, norm_def, norm_zero, resolve_left, sub_eq_add_neg, z.im, z.re
-/
theorem norm_eq_zero_iff {d : Int} (hd : d < 0) (z : Int√d) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [norm_def]; rw [sub_eq_add_neg]; rw [mul_assoc] at h
    have left := mul_self_nonneg z.re
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im))
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg left right).mp h
    ext <;> apply eq_zero_of_mul_self_eq_zero
    · exact ha
    · rw [neg_eq_zero, mul_eq_zero] at hb
      exact hb.resolve_left hd.ne
  · rintro rfl
    exact norm_zero

/--
theorem `norm_eq_of_associated` / 定理 `norm_eq_of_associated`

English:
theorem norm_eq_of_associated
  given: {d : Int} (hd : d <= 0) {x y : Int√d} (h : Associated x y)
  proof: by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul]; rw [(norm_eq_one_iff' hd _).mpr u.isUnit]; rw [mul_one]

中文:
定理 norm_eq_of_associated
  条件: {d : 整数} (hd : d <= 0) {x y : 整数√d} (h : Associated x y)
  证明: by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul]; rw [(norm_eq_one_iff' hd _).mpr u.isUnit]; rw [mul_one]

Depends on / 依赖: isUnit, mul_one, norm_eq_one_iff, norm_mul, u.isUnit
-/
theorem norm_eq_of_associated {d : Int} (hd : d <= 0) {x y : Int√d} (h : Associated x y) :
    x.norm = y.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul]; rw [(norm_eq_one_iff' hd _).mpr u.isUnit]; rw [mul_one]

end Norm

end

section

variable {d : Nat}

/--
Definition of `Nonneg` / `Nonneg` 的定义

English:
definition Nonneg
  signature: : Int√d -> Prop

中文:
定义 Nonneg
  签名: : 整数√d -> 命题
-/
def Nonneg : Int√d -> Prop
  | ⟨a, b⟩ => Nonnegg d 1 a b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Int√d)
  body: ⟨fun a b => Nonneg (b - a)⟩

中文:
实例 :
  签名: LE (整数√d)
  定义体: ⟨fun a b => Nonneg (b - a)⟩

Depends on / 依赖: Nonneg
-/
instance : LE (Int√d) :=
  ⟨fun a b => Nonneg (b - a)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (Int√d)
  body: ⟨fun a b => ¬b <= a⟩

中文:
实例 :
  签名: LT (整数√d)
  定义体: ⟨fun a b => ¬b <= a⟩
-/
instance : LT (Int√d) :=
  ⟨fun a b => ¬b <= a⟩

/--
Instance `decidableNonnegg` / 实例 `decidableNonnegg`

English:
instance decidableNonnegg
  signature: (c d)

中文:
实例 decidableNonnegg
  签名: (c d)
-/
instance decidableNonnegg (c d) : DecidableRel (Nonnegg c d)
| .ofNat _, .ofNat _ => inferInstanceAs Decidable True
| .ofNat _, .negSucc _ => inferInstanceAs Decidable (_ <= _)
| .negSucc _, .ofNat _ => inferInstanceAs Decidable (_ <= _)
| .negSucc _, .negSucc _ => inferInstanceAs Decidable False

/--
Instance `decidableNonneg` / 实例 `decidableNonneg`

English:
instance decidableNonneg
  signature: : forall a : Int√d, Decidable (Nonneg a)

中文:
实例 decidableNonneg
  签名: : 对任意 a : 整数√d, 可判定 (Nonneg a)
-/
instance decidableNonneg : forall a : Int√d, Decidable (Nonneg a)
  | ⟨_, _⟩ => Zsqrtd.decidableNonnegg _ _ _ _

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: : DecidableLE (Int√d)
  body: fun _ _ => decidableNonneg _

中文:
实例 decidableLE
  签名: : DecidableLE (整数√d)
  定义体: fun _ _ => decidableNonneg _

Depends on / 依赖: decidableNonneg
-/
instance decidableLE : DecidableLE (Int√d) := fun _ _ => decidableNonneg _

open Int in
/--
theorem `nonneg_cases` / 定理 `nonneg_cases`

English:
theorem nonneg_cases
  statement: forall {a : Int√d}, Nonneg a -> exists x y : Nat, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩

中文:
定理 nonneg_cases
  结论: 对任意 {a : 整数√d}, Nonneg a -> 存在 x y : 自然数, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
-/
theorem nonneg_cases : forall {a : Int√d}, Nonneg a -> exists x y : Nat, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
  | ⟨(x : Nat), (y : Nat)⟩, _ => ⟨x, y, Or.inl rfl⟩
| ⟨(x : Nat), -[y+1]⟩, _ => ⟨x, y + 1, Or.inr Or.inl rfl⟩
| ⟨-[x+1], (y : Nat)⟩, _ => ⟨x + 1, y, Or.inr Or.inr rfl⟩
  | ⟨-[_+1], -[_+1]⟩, h => False.elim h

open Int in
/--
theorem `nonneg_add_lem` / 定理 `nonneg_add_lem`

English:
theorem nonneg_add_lem
  given: {x y z w : Nat} (xy : Nonneg (⟨x, -y⟩ : Int√d)) (zw : Nonneg (⟨-z, w⟩ : Int√d))
  proof: by
  have : Nonneg ⟨Int.subNatNat x z, Int.subNatNat w y⟩ :=
    Int.subNatNat_elim x z
      (fun m n i => SqLe y d m 1 -> SqLe n 1 w d -> Nonneg ⟨i, Int.subNatNat w y⟩)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d (k + j) 1 -> SqLe k 1 m d -> Nonneg ⟨Int.ofNat j, i⟩)
          (fun _ _ _ _ => trivial) fun m n xy zw => sqLe_cancel zw xy)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d k 1 -> SqLe (k + j + 1) 1 m d -> Nonneg ⟨-[j+1], i⟩)
          (fun m n xy zw => sqLe_cancel xy zw) fun m n xy zw =>
          let t := Nat.le_trans zw (sqLe_of_le (Nat.le_add_right n (m + 1)) le_rfl xy)
          have : k + j + 1 <= k :=
            Nat.mul_self_le_mul_self_iff.1 (by simpa [one_mul] using t)
          absurd this (not_le_of_gt <| Nat.succ_le_succ <| Nat.le_add_right _ _))
      (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw)
  rw [add_def]; rw [neg_add_eq_sub]
  rwa [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at this

中文:
定理 nonneg_add_lem
  条件: {x y z w : 自然数} (xy : Nonneg (⟨x, -y⟩ : 整数√d)) (zw : Nonneg (⟨-z, w⟩ : 整数√d))
  证明: by
  have : Nonneg ⟨Int.subNatNat x z, Int.subNatNat w y⟩ :=
    Int.subNatNat_elim x z
      (fun m n i => SqLe y d m 1 -> SqLe n 1 w d -> Nonneg ⟨i, Int.subNatNat w y⟩)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d (k + j) 1 -> SqLe k 1 m d -> Nonneg ⟨Int.ofNat j, i⟩)
          (fun _ _ _ _ => trivial) fun m n xy zw => sqLe_cancel zw xy)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d k 1 -> SqLe (k + j + 1) 1 m d -> Nonneg ⟨-[j+1], i⟩)
          (fun m n xy zw => sqLe_cancel xy zw) fun m n xy zw =>
          let t := Nat.le_trans zw (sqLe_of_le (Nat.le_add_right n (m + 1)) le_rfl xy)
          have : k + j + 1 <= k :=
            Nat.mul_self_le_mul_self_iff.1 (by simpa [one_mul] using t)
          absurd this (not_le_of_gt <| Nat.succ_le_succ <| Nat.le_add_right _ _))
      (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw)
  rw [add_def]; rw [neg_add_eq_sub]
  rwa [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at this

Depends on / 依赖: Int.ofNat, Int.subNatNat, Int.subNatNat_elim, Nonneg, sqLe_cancel, subNatNat, subNatNat_elim
-/
theorem nonneg_add_lem {x y z w : Nat} (xy : Nonneg (⟨x, -y⟩ : Int√d)) (zw : Nonneg (⟨-z, w⟩ : Int√d)) :
    Nonneg (⟨x, -y⟩ + ⟨-z, w⟩ : Int√d) := by
  have : Nonneg ⟨Int.subNatNat x z, Int.subNatNat w y⟩ :=
    Int.subNatNat_elim x z
      (fun m n i => SqLe y d m 1 -> SqLe n 1 w d -> Nonneg ⟨i, Int.subNatNat w y⟩)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d (k + j) 1 -> SqLe k 1 m d -> Nonneg ⟨Int.ofNat j, i⟩)
          (fun _ _ _ _ => trivial) fun m n xy zw => sqLe_cancel zw xy)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d k 1 -> SqLe (k + j + 1) 1 m d -> Nonneg ⟨-[j+1], i⟩)
          (fun m n xy zw => sqLe_cancel xy zw) fun m n xy zw =>
          let t := Nat.le_trans zw (sqLe_of_le (Nat.le_add_right n (m + 1)) le_rfl xy)
          have : k + j + 1 <= k :=
            Nat.mul_self_le_mul_self_iff.1 (by simpa [one_mul] using t)
          absurd this (not_le_of_gt <| Nat.succ_le_succ <| Nat.le_add_right _ _))
      (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw)
  rw [add_def]; rw [neg_add_eq_sub]
  rwa [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at this

/--
theorem `Nonneg.add` / 定理 `Nonneg.add`

English:
theorem Nonneg.add
  given: {a b : Int√d} (ha : Nonneg a) (hb : Nonneg b)
  statement: Nonneg (a + b)
  proof: by
  rcases nonneg_cases ha with ⟨x, y, rfl | rfl | rfl⟩ <;>
    rcases nonneg_cases hb with ⟨z, w, rfl | rfl | rfl⟩
  · trivial
  · refine nonnegg_cases_right fun i h => sqLe_of_le ?_ ?_ (nonnegg_pos_neg.1 hb)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro y (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 hb)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro x (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine nonnegg_cases_right fun i h => sqLe_of_le ?_ ?_ (nonnegg_pos_neg.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro w (by simp [*])))
    · apply Nat.le_add_right
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_pos_neg.2 (sqLe_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
    rw [Nat.cast_add]; rw [Nat.cast_add]; rw [neg_add] at this
    rwa [add_def]
  · exact nonneg_add_lem ha hb
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro _ h))
    · apply Nat.le_add_right
  · dsimp
    rw [add_comm]; rw [add_comm (y : Int)]
    exact nonneg_add_lem hb ha
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_neg_pos.2 (sqLe_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
    rw [Nat.cast_add]; rw [Nat.cast_add]; rw [neg_add] at this
    rwa [add_def]

中文:
定理 Nonneg.add
  条件: {a b : 整数√d} (ha : Nonneg a) (hb : Nonneg b)
  结论: Nonneg (a + b)
  证明: by
  rcases nonneg_cases ha with ⟨x, y, rfl | rfl | rfl⟩ <;>
    rcases nonneg_cases hb with ⟨z, w, rfl | rfl | rfl⟩
  · trivial
  · refine nonnegg_cases_right fun i h => sqLe_of_le ?_ ?_ (nonnegg_pos_neg.1 hb)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro y (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 hb)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro x (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine nonnegg_cases_right fun i h => sqLe_of_le ?_ ?_ (nonnegg_pos_neg.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro w (by simp [*])))
    · apply Nat.le_add_right
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_pos_neg.2 (sqLe_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
    rw [Nat.cast_add]; rw [Nat.cast_add]; rw [neg_add] at this
    rwa [add_def]
  · exact nonneg_add_lem ha hb
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro _ h))
    · apply Nat.le_add_right
  · dsimp
    rw [add_comm]; rw [add_comm (y : Int)]
    exact nonneg_add_lem hb ha
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_neg_pos.2 (sqLe_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
    rw [Nat.cast_add]; rw [Nat.cast_add]; rw [neg_add] at this
    rwa [add_def]
-/
theorem Nonneg.add {a b : Int√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a + b) := by
  rcases nonneg_cases ha with ⟨x, y, rfl | rfl | rfl⟩ <;>
    rcases nonneg_cases hb with ⟨z, w, rfl | rfl | rfl⟩
  · trivial
  · refine nonnegg_cases_right fun i h => sqLe_of_le ?_ ?_ (nonnegg_pos_neg.1 hb)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro y (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 hb)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro x (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine nonnegg_cases_right fun i h => sqLe_of_le ?_ ?_ (nonnegg_pos_neg.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro w (by simp [*])))
    · apply Nat.le_add_right
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_pos_neg.2 (sqLe_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
    rw [Nat.cast_add]; rw [Nat.cast_add]; rw [neg_add] at this
    rwa [add_def]
  · exact nonneg_add_lem ha hb
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro _ h))
    · apply Nat.le_add_right
  · dsimp
    rw [add_comm]; rw [add_comm (y : Int)]
    exact nonneg_add_lem hb ha
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_neg_pos.2 (sqLe_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
    rw [Nat.cast_add]; rw [Nat.cast_add]; rw [neg_add] at this
    rwa [add_def]

/--
theorem `nonneg_iff_zero_le` / 定理 `nonneg_iff_zero_le`

English:
theorem nonneg_iff_zero_le
  given: {a : Int√d}
  statement: Nonneg a ↔ 0 <= a
  proof: show _ ↔ Nonneg _ by simp

中文:
定理 nonneg_iff_zero_le
  条件: {a : 整数√d}
  结论: Nonneg a ↔ 0 <= a
  证明: show _ ↔ Nonneg _ by simp

Depends on / 依赖: Nonneg
-/
theorem nonneg_iff_zero_le {a : Int√d} : Nonneg a ↔ 0 <= a :=
  show _ ↔ Nonneg _ by simp

/--
theorem `le_of_le_le` / 定理 `le_of_le_le`

English:
theorem le_of_le_le
  given: {x y z w : Int} (xz : x <= z) (yw : y <= w)
  statement: (⟨x, y⟩ : Int√d) <= ⟨z, w⟩
  proof: show Nonneg ⟨z - x, w - y⟩ from
    match z - x, w - y, Int.le.dest_sub xz, Int.le.dest_sub yw with
    | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => trivial

中文:
定理 le_of_le_le
  条件: {x y z w : 整数} (xz : x <= z) (yw : y <= w)
  结论: (⟨x, y⟩ : 整数√d) <= ⟨z, w⟩
  证明: show Nonneg ⟨z - x, w - y⟩ from
    match z - x, w - y, Int.le.dest_sub xz, Int.le.dest_sub yw with
    | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => trivial

Depends on / 依赖: Int.le.dest_sub, Nonneg, dest_sub
-/
theorem le_of_le_le {x y z w : Int} (xz : x <= z) (yw : y <= w) : (⟨x, y⟩ : Int√d) <= ⟨z, w⟩ :=
  show Nonneg ⟨z - x, w - y⟩ from
    match z - x, w - y, Int.le.dest_sub xz, Int.le.dest_sub yw with
    | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => trivial

open Int in
/--
theorem `nonneg_total` / 定理 `nonneg_total`

English:
theorem nonneg_total
  statement: forall a : Int√d, Nonneg a ∨ Nonneg (-a)

中文:
定理 nonneg_total
  结论: 对任意 a : 整数√d, Nonneg a ∨ Nonneg (-a)
-/
protected theorem nonneg_total : forall a : Int√d, Nonneg a ∨ Nonneg (-a)
  | ⟨(x : Nat), (y : Nat)⟩ => Or.inl trivial
  | ⟨-[_+1], -[_+1]⟩ => Or.inr trivial
  | ⟨0, -[_+1]⟩ => Or.inr trivial
  | ⟨-[_+1], 0⟩ => Or.inr trivial
  | ⟨(_ + 1 : Nat), -[_+1]⟩ => Nat.le_total _ _
  | ⟨-[_+1], (_ + 1 : Nat)⟩ => Nat.le_total _ _

@[deprecated _root_.le_total (since := "2026-02-19")]
/--
theorem `le_total` / 定理 `le_total`

English:
theorem le_total
  given: (a b : Int√d)
  statement: a <= b ∨ b <= a
  proof: by
  have t := (b - a).nonneg_total
  rwa [neg_sub] at t

中文:
定理 le_total
  条件: (a b : 整数√d)
  结论: a <= b ∨ b <= a
  证明: by
  have t := (b - a).nonneg_total
  rwa [neg_sub] at t
-/
protected theorem le_total (a b : Int√d) : a <= b ∨ b <= a := by
  have t := (b - a).nonneg_total
  rwa [neg_sub] at t

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: : Preorder (Int√d) where
  body: show Nonneg (a - a) by simp only [sub_self]; trivial
  le_trans a b c hab hbc := by simpa [sub_add_sub_cancel'] using! hab.add hbc
  lt_iff_le_not_ge a b := by
    have ht : b <= a ∨ a <= b := by
      have t := (a - b).nonneg_total
      rwa [neg_sub] at t
    exact (and_iff_right_of_imp ht.resolve_left).symm

中文:
实例 preorder
  签名: : 预序 (整数√d) where
  定义体: show Nonneg (a - a) by simp only [sub_self]; trivial
  le_trans a b c hab hbc := by simpa [sub_add_sub_cancel'] using! hab.add hbc
  lt_iff_le_not_ge a b := by
    have ht : b <= a ∨ a <= b := by
      have t := (a - b).nonneg_total
      rwa [neg_sub] at t
    exact (and_iff_right_of_imp ht.resolve_left).symm

Depends on / 依赖: Nonneg, sub_self
-/
instance preorder : Preorder (Int√d) where
  le_refl a := show Nonneg (a - a) by simp only [sub_self]; trivial
  le_trans a b c hab hbc := by simpa [sub_add_sub_cancel'] using! hab.add hbc
  lt_iff_le_not_ge a b := by
    have ht : b <= a ∨ a <= b := by
      have t := (a - b).nonneg_total
      rwa [neg_sub] at t
    exact (and_iff_right_of_imp ht.resolve_left).symm

open Int in
-- TODO add an `Archimedean (ℤ√d)` instance and drop this lemma
/--
theorem `le_arch` / 定理 `le_arch`

English:
theorem le_arch
  given: (a : Int√d)
  statement: exists n : Nat, a <= n
  proof: by
  obtain ⟨x, y, (h : a <= ⟨x, y⟩)⟩ : exists x y : Nat, Nonneg (⟨x, y⟩ + -a) :=
    match -a with
    | ⟨Int.ofNat x, Int.ofNat y⟩ => ⟨0, 0, by trivial⟩
    | ⟨Int.ofNat x, -[y+1]⟩ => ⟨0, y + 1, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
    | ⟨-[x+1], Int.ofNat y⟩ => ⟨x + 1, 0, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
    | ⟨-[x+1], -[y+1]⟩ => ⟨x + 1, y + 1, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
  refine ⟨x + d * y, h.trans ?_⟩
  change Nonneg ⟨↑x + d * y - ↑x, 0 - ↑y⟩
  rcases y with - | y
  · simp only [Nat.cast_zero, mul_zero, add_zero, sub_self]
    trivial
  have h : forall y, SqLe y d (d * y) 1 := fun y => by
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (y * y) (Nat.le_mul_self d)
  rw [show (x : Int) + d * Nat.succ y - x = d * Nat.succ y by simp]
  exact h (y + 1)

@[deprecated _root_.add_le_add_left (since := "2026-02-19")]

中文:
定理 le_arch
  条件: (a : 整数√d)
  结论: 存在 n : 自然数, a <= n
  证明: by
  obtain ⟨x, y, (h : a <= ⟨x, y⟩)⟩ : exists x y : Nat, Nonneg (⟨x, y⟩ + -a) :=
    match -a with
    | ⟨Int.ofNat x, Int.ofNat y⟩ => ⟨0, 0, by trivial⟩
    | ⟨Int.ofNat x, -[y+1]⟩ => ⟨0, y + 1, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
    | ⟨-[x+1], Int.ofNat y⟩ => ⟨x + 1, 0, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
    | ⟨-[x+1], -[y+1]⟩ => ⟨x + 1, y + 1, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
  refine ⟨x + d * y, h.trans ?_⟩
  change Nonneg ⟨↑x + d * y - ↑x, 0 - ↑y⟩
  rcases y with - | y
  · simp only [Nat.cast_zero, mul_zero, add_zero, sub_self]
    trivial
  have h : forall y, SqLe y d (d * y) 1 := fun y => by
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (y * y) (Nat.le_mul_self d)
  rw [show (x : Int) + d * Nat.succ y - x = d * Nat.succ y by simp]
  exact h (y + 1)

@[deprecated _root_.add_le_add_left (since := "2026-02-19")]

Depends on / 依赖: Int.negSucc_eq, Int.ofNat, Nonneg, Nonnegg, add_assoc, h.trans, negSucc_eq
-/
theorem le_arch (a : Int√d) : exists n : Nat, a <= n := by
  obtain ⟨x, y, (h : a <= ⟨x, y⟩)⟩ : exists x y : Nat, Nonneg (⟨x, y⟩ + -a) :=
    match -a with
    | ⟨Int.ofNat x, Int.ofNat y⟩ => ⟨0, 0, by trivial⟩
    | ⟨Int.ofNat x, -[y+1]⟩ => ⟨0, y + 1, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
    | ⟨-[x+1], Int.ofNat y⟩ => ⟨x + 1, 0, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
    | ⟨-[x+1], -[y+1]⟩ => ⟨x + 1, y + 1, by simp [Int.negSucc_eq, add_assoc, Nonneg, Nonnegg]⟩
  refine ⟨x + d * y, h.trans ?_⟩
  change Nonneg ⟨↑x + d * y - ↑x, 0 - ↑y⟩
  rcases y with - | y
  · simp only [Nat.cast_zero, mul_zero, add_zero, sub_self]
    trivial
  have h : forall y, SqLe y d (d * y) 1 := fun y => by
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (y * y) (Nat.le_mul_self d)
  rw [show (x : Int) + d * Nat.succ y - x = d * Nat.succ y by simp]
  exact h (y + 1)

@[deprecated _root_.add_le_add_left (since := "2026-02-19")]
/--
theorem `add_le_add_left` / 定理 `add_le_add_left`

English:
theorem add_le_add_left
  given: (a b : Int√d) (ab : a <= b) (c : Int√d)
  statement: a + c <= b + c
  proof: show Nonneg _ by rwa [add_sub_add_right_eq_sub]

中文:
定理 add_le_add_left
  条件: (a b : 整数√d) (ab : a <= b) (c : 整数√d)
  结论: a + c <= b + c
  证明: show Nonneg _ by rwa [add_sub_add_right_eq_sub]
-/
protected theorem add_le_add_left (a b : Int√d) (ab : a <= b) (c : Int√d) : a + c <= b + c :=
  show Nonneg _ by rwa [add_sub_add_right_eq_sub]



/--
theorem `nonneg_smul` / 定理 `nonneg_smul`

English:
theorem nonneg_smul
  given: {a : Int√d} {n : Nat} (ha : Nonneg a)
  statement: Nonneg ((n : Int√d) * a)
  proof: by
  rw [← Int.cast_natCast n]
  exact
    match a, nonneg_cases ha, ha with
    | _, ⟨x, y, Or.inl rfl⟩, _ => by rw [smul_val]; trivial
| _, ⟨x, y, Or.inr Or.inl rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_pos_neg.2 (sqLe_smul n <| nonnegg_pos_neg.1 ha)
| _, ⟨x, y, Or.inr Or.inr rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_neg_pos.2 (sqLe_smul n <| nonnegg_neg_pos.1 ha)

中文:
定理 nonneg_smul
  条件: {a : 整数√d} {n : 自然数} (ha : Nonneg a)
  结论: Nonneg ((n : 整数√d) * a)
  证明: by
  rw [← Int.cast_natCast n]
  exact
    match a, nonneg_cases ha, ha with
    | _, ⟨x, y, Or.inl rfl⟩, _ => by rw [smul_val]; trivial
| _, ⟨x, y, Or.inr Or.inl rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_pos_neg.2 (sqLe_smul n <| nonnegg_pos_neg.1 ha)
| _, ⟨x, y, Or.inr Or.inr rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_neg_pos.2 (sqLe_smul n <| nonnegg_neg_pos.1 ha)

Depends on / 依赖: Int.cast_natCast, Or.inl, Or.inr, cast_natCast, nonneg_cases, nonnegg_neg_pos, nonnegg_pos_neg, smul_val, sqLe_smul
-/
theorem nonneg_smul {a : Int√d} {n : Nat} (ha : Nonneg a) : Nonneg ((n : Int√d) * a) := by
  rw [← Int.cast_natCast n]
  exact
    match a, nonneg_cases ha, ha with
    | _, ⟨x, y, Or.inl rfl⟩, _ => by rw [smul_val]; trivial
| _, ⟨x, y, Or.inr Or.inl rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_pos_neg.2 (sqLe_smul n <| nonnegg_pos_neg.1 ha)
| _, ⟨x, y, Or.inr Or.inr rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_neg_pos.2 (sqLe_smul n <| nonnegg_neg_pos.1 ha)

/--
theorem `nonneg_muld` / 定理 `nonneg_muld`

English:
theorem nonneg_muld
  given: {a : Int√d} (ha : Nonneg a)
  statement: Nonneg (sqrtd * a)
  proof: match a, nonneg_cases ha, ha with
  | _, ⟨_, _, Or.inl rfl⟩, _ => trivial
| _, ⟨x, y, Or.inr Or.inl rfl⟩, ha => by
    simp only [muld_val, mul_neg]
    apply nonnegg_neg_pos.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
| _, ⟨x, y, Or.inr Or.inr rfl⟩, ha => by
    simp only [muld_val]
    apply nonnegg_pos_neg.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)

中文:
定理 nonneg_muld
  条件: {a : 整数√d} (ha : Nonneg a)
  结论: Nonneg (sqrtd * a)
  证明: match a, nonneg_cases ha, ha with
  | _, ⟨_, _, Or.inl rfl⟩, _ => trivial
| _, ⟨x, y, Or.inr Or.inl rfl⟩, ha => by
    simp only [muld_val, mul_neg]
    apply nonnegg_neg_pos.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
| _, ⟨x, y, Or.inr Or.inr rfl⟩, ha => by
    simp only [muld_val]
    apply nonnegg_pos_neg.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)

Depends on / 依赖: Nat.mul_le_mul_left, Or.inl, Or.inr, mul_comm, mul_le_mul_left, mul_left_comm, mul_neg, muld_val, nonneg_cases, nonnegg_neg_pos, nonnegg_pos_neg
-/
theorem nonneg_muld {a : Int√d} (ha : Nonneg a) : Nonneg (sqrtd * a) :=
  match a, nonneg_cases ha, ha with
  | _, ⟨_, _, Or.inl rfl⟩, _ => trivial
| _, ⟨x, y, Or.inr Or.inl rfl⟩, ha => by
    simp only [muld_val, mul_neg]
    apply nonnegg_neg_pos.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
| _, ⟨x, y, Or.inr Or.inr rfl⟩, ha => by
    simp only [muld_val]
    apply nonnegg_pos_neg.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)

/--
theorem `nonneg_mul_lem` / 定理 `nonneg_mul_lem`

English:
theorem nonneg_mul_lem
  given: {x y : Nat} {a : Int√d} (ha : Nonneg a)
  statement: Nonneg (⟨x, y⟩ * a)
  proof: by
  have : (⟨x, y⟩ * a : Int√d) = (x : Int√d) * a + sqrtd * ((y : Int√d) * a) := by
    rw [decompose]; rw [right_distrib]; rw [mul_assoc]; rw [Int.cast_natCast]; rw [Int.cast_natCast]
  rw [this]
  exact (nonneg_smul ha).add (nonneg_muld <| nonneg_smul ha)

中文:
定理 nonneg_mul_lem
  条件: {x y : 自然数} {a : 整数√d} (ha : Nonneg a)
  结论: Nonneg (⟨x, y⟩ * a)
  证明: by
  have : (⟨x, y⟩ * a : Int√d) = (x : Int√d) * a + sqrtd * ((y : Int√d) * a) := by
    rw [decompose]; rw [right_distrib]; rw [mul_assoc]; rw [Int.cast_natCast]; rw [Int.cast_natCast]
  rw [this]
  exact (nonneg_smul ha).add (nonneg_muld <| nonneg_smul ha)

Depends on / 依赖: Int.cast_natCast, cast_natCast, decompose, mul_assoc, nonneg_muld, nonneg_smul, right_distrib
-/
theorem nonneg_mul_lem {x y : Nat} {a : Int√d} (ha : Nonneg a) : Nonneg (⟨x, y⟩ * a) := by
  have : (⟨x, y⟩ * a : Int√d) = (x : Int√d) * a + sqrtd * ((y : Int√d) * a) := by
    rw [decompose]; rw [right_distrib]; rw [mul_assoc]; rw [Int.cast_natCast]; rw [Int.cast_natCast]
  rw [this]
  exact (nonneg_smul ha).add (nonneg_muld <| nonneg_smul ha)

/--
theorem `nonneg_mul` / 定理 `nonneg_mul`

English:
theorem nonneg_mul
  given: {a b : Int√d} (ha : Nonneg a) (hb : Nonneg b)
  statement: Nonneg (a * b)
  proof: match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | _, _, ⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inl rfl⟩, _, _ => trivial
| _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, _, hb => nonneg_mul_lem hb
| _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, _, hb => nonneg_mul_lem hb
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨-x]; rw [y⟩ * ⟨-z]; rw [w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨x * z + d * y * w]; rw [-(x * w + y * z)⟩ := by simp [add_comm]]
    exact nonnegg_pos_neg.2 (sqLe_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨-x]; rw [y⟩ * ⟨z]; rw [-w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨-(x * z + d * y * w)]; rw [x * w + y * z⟩ := by simp [add_comm]]
    exact nonnegg_neg_pos.2 (sqLe_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨x]; rw [-y⟩ * ⟨-z]; rw [w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨-(x * z + d * y * w)]; rw [x * w + y * z⟩ := by simp [add_comm]]
    exact
        nonnegg_neg_pos.2 (sqLe_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨x]; rw [-y⟩ * ⟨z]; rw [-w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨x * z + d * y * w]; rw [-(x * w + y * z)⟩ := by simp [add_comm]]
    exact
        nonnegg_pos_neg.2
          (sqLe_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))

中文:
定理 nonneg_mul
  条件: {a b : 整数√d} (ha : Nonneg a) (hb : Nonneg b)
  结论: Nonneg (a * b)
  证明: match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | _, _, ⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inl rfl⟩, _, _ => trivial
| _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, _, hb => nonneg_mul_lem hb
| _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, _, hb => nonneg_mul_lem hb
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨-x]; rw [y⟩ * ⟨-z]; rw [w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨x * z + d * y * w]; rw [-(x * w + y * z)⟩ := by simp [add_comm]]
    exact nonnegg_pos_neg.2 (sqLe_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨-x]; rw [y⟩ * ⟨z]; rw [-w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨-(x * z + d * y * w)]; rw [x * w + y * z⟩ := by simp [add_comm]]
    exact nonnegg_neg_pos.2 (sqLe_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨x]; rw [-y⟩ * ⟨-z]; rw [w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨-(x * z + d * y * w)]; rw [x * w + y * z⟩ := by simp [add_comm]]
    exact
        nonnegg_neg_pos.2 (sqLe_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨x]; rw [-y⟩ * ⟨z]; rw [-w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨x * z + d * y * w]; rw [-(x * w + y * z)⟩ := by simp [add_comm]]
    exact
        nonnegg_pos_neg.2
          (sqLe_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))

Depends on / 依赖: Or.inl, Or.inr, mul_comm, nonneg_cases, nonneg_mul_lem
-/
theorem nonneg_mul {a b : Int√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a * b) :=
  match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | _, _, ⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inl rfl⟩, _, _ => trivial
| _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, _, hb => nonneg_mul_lem hb
| _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, _, hb => nonneg_mul_lem hb
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨-x]; rw [y⟩ * ⟨-z]; rw [w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨x * z + d * y * w]; rw [-(x * w + y * z)⟩ := by simp [add_comm]]
    exact nonnegg_pos_neg.2 (sqLe_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
| _, _, ⟨x, y, Or.inr Or.inr rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨-x]; rw [y⟩ * ⟨z]; rw [-w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨-(x * z + d * y * w)]; rw [x * w + y * z⟩ := by simp [add_comm]]
    exact nonnegg_neg_pos.2 (sqLe_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inr Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨x]; rw [-y⟩ * ⟨-z]; rw [w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨-(x * z + d * y * w)]; rw [x * w + y * z⟩ := by simp [add_comm]]
    exact
        nonnegg_neg_pos.2 (sqLe_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
| _, _, ⟨x, y, Or.inr Or.inl rfl⟩, ⟨z, w, Or.inr Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨x]; rw [-y⟩ * ⟨z]; rw [-w⟩ : Int√d) = ⟨_]; rw [_⟩ := rfl
          _ = ⟨x * z + d * y * w]; rw [-(x * w + y * z)⟩ := by simp [add_comm]]
    exact
        nonnegg_pos_neg.2
          (sqLe_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))

/--
theorem `mul_nonneg` / 定理 `mul_nonneg`

English:
theorem mul_nonneg
  given: (a b : Int√d)
  statement: 0 <= a -> 0 <= b -> 0 <= a * b
  proof: by
  simp_rw [← nonneg_iff_zero_le]
  exact nonneg_mul

中文:
定理 mul_nonneg
  条件: (a b : 整数√d)
  结论: 0 <= a -> 0 <= b -> 0 <= a * b
  证明: by
  simp_rw [← nonneg_iff_zero_le]
  exact nonneg_mul
-/
protected theorem mul_nonneg (a b : Int√d) : 0 <= a -> 0 <= b -> 0 <= a * b := by
  simp_rw [← nonneg_iff_zero_le]
  exact nonneg_mul

/--
theorem `not_sqLe_succ` / 定理 `not_sqLe_succ`

English:
theorem not_sqLe_succ
  given: (c d y) (h : 0 < c)
  statement: ¬SqLe (y + 1) c 0 d
  proof: not_le_of_gt mul_pos (mul_pos h <| Nat.succ_pos _) Nat.succ_pos _

中文:
定理 not_sqLe_succ
  条件: (c d y) (h : 0 < c)
  结论: ¬SqLe (y + 1) c 0 d
  证明: not_le_of_gt mul_pos (mul_pos h <| Nat.succ_pos _) Nat.succ_pos _

Depends on / 依赖: Nat.succ_pos, mul_pos, not_le_of_gt, succ_pos
-/
theorem not_sqLe_succ (c d y) (h : 0 < c) : ¬SqLe (y + 1) c 0 d :=
not_le_of_gt mul_pos (mul_pos h <| Nat.succ_pos _) Nat.succ_pos _

/--
Definition of `Nonsquare` / `Nonsquare` 的定义

English:
class Nonsquare
  parameters: (x : Nat)
  axioms and operations (1):
    - ns((x)) : forall n : Nat, x != n * n

中文:
类 Nonsquare
  参数: (x : 自然数)
  公理与运算 (1 个):
    - ns((x)) : 对任意 n : 自然数, x != n * n
-/
class Nonsquare (x : Nat) : Prop where
  ns (x) : forall n : Nat, x != n * n

variable [dnsq : Nonsquare d]

/--
theorem `d_pos` / 定理 `d_pos`

English:
theorem d_pos
  statement: 0 < d
  proof: lt_of_le_of_ne (Nat.zero_le _) Ne.symm Nonsquare.ns d 0

中文:
定理 d_pos
  结论: 0 < d
  证明: lt_of_le_of_ne (Nat.zero_le _) Ne.symm Nonsquare.ns d 0

Depends on / 依赖: Nat.zero_le, Ne.symm, Nonsquare, Nonsquare.ns, lt_of_le_of_ne, zero_le
-/
theorem d_pos : 0 < d :=
lt_of_le_of_ne (Nat.zero_le _) Ne.symm Nonsquare.ns d 0

/--
theorem `divides_sq_eq_zero` / 定理 `divides_sq_eq_zero`

English:
theorem divides_sq_eq_zero
  given: {x y} (h : x * x = d * y * y)
  statement: x = 0 ∧ y = 0
  proof: let g := x.gcd y
  Or.elim g.eq_zero_or_pos
    (fun H => ⟨Nat.eq_zero_of_gcd_eq_zero_left H, Nat.eq_zero_of_gcd_eq_zero_right H⟩) fun gpos =>
False.elim by
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime _ _
      rw [hx]; rw [hy] at h
      have : m * m = d * (n * n) := by
        refine mul_left_cancel₀ (mul_pos gpos gpos).ne' ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have co2 :=
        let co1 := co.mul_right co
        co1.mul_left co1
      exact
        Nonsquare.ns d m
          (Nat.dvd_antisymm (by rw [this]; apply dvd_mul_right) <|
co2.dvd_of_dvd_mul_right by simp [this])

中文:
定理 divides_sq_eq_zero
  条件: {x y} (h : x * x = d * y * y)
  结论: x = 0 ∧ y = 0
  证明: let g := x.gcd y
  Or.elim g.eq_zero_or_pos
    (fun H => ⟨Nat.eq_zero_of_gcd_eq_zero_left H, Nat.eq_zero_of_gcd_eq_zero_right H⟩) fun gpos =>
False.elim by
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime _ _
      rw [hx]; rw [hy] at h
      have : m * m = d * (n * n) := by
        refine mul_left_cancel₀ (mul_pos gpos gpos).ne' ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have co2 :=
        let co1 := co.mul_right co
        co1.mul_left co1
      exact
        Nonsquare.ns d m
          (Nat.dvd_antisymm (by rw [this]; apply dvd_mul_right) <|
co2.dvd_of_dvd_mul_right by simp [this])

Depends on / 依赖: False.elim, Nat.dvd_antisymm, Nat.eq_zero_of_gcd_eq_zero_left, Nat.eq_zero_of_gcd_eq_zero_right, Nat.exists_coprime, Nonsquare, Nonsquare.ns, Or.elim, co.mul_right, co1.mul_left, dvd_antisymm, eq_zero_of_gcd_eq_zero_left, eq_zero_of_gcd_eq_zero_right, eq_zero_or_pos, exists_coprime, g.eq_zero_or_pos, mul_assoc, mul_comm, mul_left, mul_left_comm
-/
theorem divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
  let g := x.gcd y
  Or.elim g.eq_zero_or_pos
    (fun H => ⟨Nat.eq_zero_of_gcd_eq_zero_left H, Nat.eq_zero_of_gcd_eq_zero_right H⟩) fun gpos =>
False.elim by
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime _ _
      rw [hx]; rw [hy] at h
      have : m * m = d * (n * n) := by
        refine mul_left_cancel₀ (mul_pos gpos gpos).ne' ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have co2 :=
        let co1 := co.mul_right co
        co1.mul_left co1
      exact
        Nonsquare.ns d m
          (Nat.dvd_antisymm (by rw [this]; apply dvd_mul_right) <|
co2.dvd_of_dvd_mul_right by simp [this])

/--
theorem `divides_sq_eq_zero_z` / 定理 `divides_sq_eq_zero_z`

English:
theorem divides_sq_eq_zero_z
  given: {x y : Int} (h : x * x = d * y * y)
  statement: x = 0 ∧ y = 0
  proof: by
  rw [mul_assoc]; rw [← Int.natAbs_mul_self]; rw [← Int.natAbs_mul_self]; rw [← Int.natCast_mul]; rw [← mul_assoc] at h
  exact
    let ⟨h1, h2⟩ := divides_sq_eq_zero (Int.ofNat.inj h)
    ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2⟩

中文:
定理 divides_sq_eq_zero_z
  条件: {x y : 整数} (h : x * x = d * y * y)
  结论: x = 0 ∧ y = 0
  证明: by
  rw [mul_assoc]; rw [← Int.natAbs_mul_self]; rw [← Int.natAbs_mul_self]; rw [← Int.natCast_mul]; rw [← mul_assoc] at h
  exact
    let ⟨h1, h2⟩ := divides_sq_eq_zero (Int.ofNat.inj h)
    ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2⟩

Depends on / 依赖: Int.natAbs_eq_zero.mp, Int.natAbs_mul_self, Int.natCast_mul, Int.ofNat.inj, divides_sq_eq_zero, mul_assoc, natAbs_eq_zero, natAbs_mul_self, natCast_mul
-/
theorem divides_sq_eq_zero_z {x y : Int} (h : x * x = d * y * y) : x = 0 ∧ y = 0 := by
  rw [mul_assoc]; rw [← Int.natAbs_mul_self]; rw [← Int.natAbs_mul_self]; rw [← Int.natCast_mul]; rw [← mul_assoc] at h
  exact
    let ⟨h1, h2⟩ := divides_sq_eq_zero (Int.ofNat.inj h)
    ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2⟩

/--
theorem `not_divides_sq` / 定理 `not_divides_sq`

English:
theorem not_divides_sq
  given: (x y)
  statement: (x + 1) * (x + 1) != d * (y + 1) * (y + 1)
  proof: fun e => by
  have t := (divides_sq_eq_zero e).left
  contradiction

中文:
定理 not_divides_sq
  条件: (x y)
  结论: (x + 1) * (x + 1) != d * (y + 1) * (y + 1)
  证明: fun e => by
  have t := (divides_sq_eq_zero e).left
  contradiction

Depends on / 依赖: divides_sq_eq_zero
-/
theorem not_divides_sq (x y) : (x + 1) * (x + 1) != d * (y + 1) * (y + 1) := fun e => by
  have t := (divides_sq_eq_zero e).left
  contradiction

open Int in
/--
theorem `nonneg_antisymm` / 定理 `nonneg_antisymm`

English:
theorem nonneg_antisymm
  statement: forall {a : Int√d}, Nonneg a -> Nonneg (-a) -> a = 0
  proof: le_antisymm yx xy
    rw [one_mul] at t
    exact absurd t (not_divides_sq _ _)
  | ⟨-[x+1], (y + 1 : Nat)⟩, (xy : SqLe _ _ _ _), (yx : SqLe _ _ _ _) => by
    let t := le_antisymm xy yx
    rw [one_mul] at t
    exact absurd t (not_divides_sq _ _)

@[deprecated _root_.le_antisymm (since := "2026-02-19")]

中文:
定理 nonneg_antisymm
  结论: 对任意 {a : 整数√d}, Nonneg a -> Nonneg (-a) -> a = 0
  证明: le_antisymm yx xy
    rw [one_mul] at t
    exact absurd t (not_divides_sq _ _)
  | ⟨-[x+1], (y + 1 : Nat)⟩, (xy : SqLe _ _ _ _), (yx : SqLe _ _ _ _) => by
    let t := le_antisymm xy yx
    rw [one_mul] at t
    exact absurd t (not_divides_sq _ _)

@[deprecated _root_.le_antisymm (since := "2026-02-19")]

Depends on / 依赖: le_antisymm
-/
theorem nonneg_antisymm : forall {a : Int√d}, Nonneg a -> Nonneg (-a) -> a = 0
  | ⟨0, 0⟩, _, _ => rfl
  | ⟨-[_+1], -[_+1]⟩, xy, _ => False.elim xy
  | ⟨(_ + 1 : Nat), (_ + 1 : Nat)⟩, _, yx => False.elim yx
  | ⟨-[_+1], 0⟩, xy, _ => absurd xy (not_sqLe_succ _ _ _ (by decide))
  | ⟨(_ + 1 : Nat), 0⟩, _, yx => absurd yx (not_sqLe_succ _ _ _ (by decide))
  | ⟨0, -[_+1]⟩, xy, _ => absurd xy (not_sqLe_succ _ _ _ d_pos)
  | ⟨0, (_ + 1 : Nat)⟩, _, yx => absurd yx (not_sqLe_succ _ _ _ d_pos)
  | ⟨(x + 1 : Nat), -[y+1]⟩, (xy : SqLe _ _ _ _), (yx : SqLe _ _ _ _) => by
    let t := le_antisymm yx xy
    rw [one_mul] at t
    exact absurd t (not_divides_sq _ _)
  | ⟨-[x+1], (y + 1 : Nat)⟩, (xy : SqLe _ _ _ _), (yx : SqLe _ _ _ _) => by
    let t := le_antisymm xy yx
    rw [one_mul] at t
    exact absurd t (not_divides_sq _ _)

@[deprecated _root_.le_antisymm (since := "2026-02-19")]
/--
theorem `le_antisymm` / 定理 `le_antisymm`

English:
theorem le_antisymm
  given: {a b : Int√d} (ab : a <= b) (ba : b <= a)
  statement: a = b
  proof: eq_of_sub_eq_zero nonneg_antisymm ba (by rwa [neg_sub])

中文:
定理 le_antisymm
  条件: {a b : 整数√d} (ab : a <= b) (ba : b <= a)
  结论: a = b
  证明: eq_of_sub_eq_zero nonneg_antisymm ba (by rwa [neg_sub])

Depends on / 依赖: eq_of_sub_eq_zero, neg_sub, nonneg_antisymm
-/
theorem le_antisymm {a b : Int√d} (ab : a <= b) (ba : b <= a) : a = b :=
eq_of_sub_eq_zero nonneg_antisymm ba (by rwa [neg_sub])

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder (Int√d)
  body: { Zsqrtd.preorder with
le_antisymm := fun _ _ ab ba => eq_of_sub_eq_zero nonneg_antisymm ba (by rwa [neg_sub])
    le_total := fun a b => by
      have t := (b - a).nonneg_total
      rwa [neg_sub] at t
    toDecidableLE := Zsqrtd.decidableLE
    toDecidableEq := inferInstance }

中文:
实例 linearOrder
  签名: : 线性序 (整数√d)
  定义体: { Zsqrtd.preorder with
le_antisymm := fun _ _ ab ba => eq_of_sub_eq_zero nonneg_antisymm ba (by rwa [neg_sub])
    le_total := fun a b => by
      have t := (b - a).nonneg_total
      rwa [neg_sub] at t
    toDecidableLE := Zsqrtd.decidableLE
    toDecidableEq := inferInstance }

Depends on / 依赖: Zsqrtd, Zsqrtd.decidableLE, Zsqrtd.preorder, decidableLE, eq_of_sub_eq_zero, le_antisymm, le_total, neg_sub, nonneg_antisymm, nonneg_total, preorder, toDecidableEq, toDecidableLE
-/
instance linearOrder : LinearOrder (Int√d) :=
  { Zsqrtd.preorder with
le_antisymm := fun _ _ ab ba => eq_of_sub_eq_zero nonneg_antisymm ba (by rwa [neg_sub])
    le_total := fun a b => by
      have t := (b - a).nonneg_total
      rwa [neg_sub] at t
    toDecidableLE := Zsqrtd.decidableLE
    toDecidableEq := inferInstance }

/--
theorem `eq_zero_or_eq_zero_of_mul_eq_zero` / 定理 `eq_zero_or_eq_zero_of_mul_eq_zero`

English:
theorem eq_zero_or_eq_zero_of_mul_eq_zero
  statement: forall {a b : Int√d}, a * b = 0 -> a = 0 ∨ b = 0
  proof: eq_neg_of_add_eq_zero_left h1
    have h2 : x * w = -(y * z) := eq_neg_of_add_eq_zero_left h2
    have fin : x * x = d * y * y -> (⟨x, y⟩ : Int√d) = 0 := fun e =>
      match x, y, divides_sq_eq_zero_z e with
      | _, _, ⟨rfl, rfl⟩ => rfl
    exact
      if z0 : z = 0 then
        if w0 : w = 0 then
          Or.inr
            (match z, w, z0, w0 with
            | _, _, rfl, rfl => rfl)
        else
Or.inl
fin
mul_right_cancel₀ w0
                calc
                  x * x * w = -y * (x * z) := by simp [h2, mul_assoc, mul_left_comm]
                  _ = d * y * y * w := by simp [h1, mul_assoc, mul_left_comm]
      else
Or.inl
fin
mul_right_cancel₀ z0
              calc
                x * x * z = d * -y * (x * w) := by simp [h1, mul_assoc, mul_left_comm]
                _ = d * y * y * z := by simp [h2, mul_assoc, mul_left_comm]

中文:
定理 eq_zero_or_eq_zero_of_mul_eq_zero
  结论: 对任意 {a b : 整数√d}, a * b = 0 -> a = 0 ∨ b = 0
  证明: eq_neg_of_add_eq_zero_left h1
    have h2 : x * w = -(y * z) := eq_neg_of_add_eq_zero_left h2
    have fin : x * x = d * y * y -> (⟨x, y⟩ : Int√d) = 0 := fun e =>
      match x, y, divides_sq_eq_zero_z e with
      | _, _, ⟨rfl, rfl⟩ => rfl
    exact
      if z0 : z = 0 then
        if w0 : w = 0 then
          Or.inr
            (match z, w, z0, w0 with
            | _, _, rfl, rfl => rfl)
        else
Or.inl
fin
mul_right_cancel₀ w0
                calc
                  x * x * w = -y * (x * z) := by simp [h2, mul_assoc, mul_left_comm]
                  _ = d * y * y * w := by simp [h1, mul_assoc, mul_left_comm]
      else
Or.inl
fin
mul_right_cancel₀ z0
              calc
                x * x * z = d * -y * (x * w) := by simp [h1, mul_assoc, mul_left_comm]
                _ = d * y * y * z := by simp [h2, mul_assoc, mul_left_comm]
-/
protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : forall {a b : Int√d}, a * b = 0 -> a = 0 ∨ b = 0
  | ⟨x, y⟩, ⟨z, w⟩, h => by
    injection h with h1 h2
    have h1 : x * z = -(d * y * w) := eq_neg_of_add_eq_zero_left h1
    have h2 : x * w = -(y * z) := eq_neg_of_add_eq_zero_left h2
    have fin : x * x = d * y * y -> (⟨x, y⟩ : Int√d) = 0 := fun e =>
      match x, y, divides_sq_eq_zero_z e with
      | _, _, ⟨rfl, rfl⟩ => rfl
    exact
      if z0 : z = 0 then
        if w0 : w = 0 then
          Or.inr
            (match z, w, z0, w0 with
            | _, _, rfl, rfl => rfl)
        else
Or.inl
fin
mul_right_cancel₀ w0
                calc
                  x * x * w = -y * (x * z) := by simp [h2, mul_assoc, mul_left_comm]
                  _ = d * y * y * w := by simp [h1, mul_assoc, mul_left_comm]
      else
Or.inl
fin
mul_right_cancel₀ z0
              calc
                x * x * z = d * -y * (x * w) := by simp [h1, mul_assoc, mul_left_comm]
                _ = d * y * y * z := by simp [h2, mul_assoc, mul_left_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors (Int√d)
  body: Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

中文:
实例 :
  签名: 无零因子 (整数√d)
  定义体: Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

Depends on / 依赖: Zsqrtd, Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero, eq_zero_or_eq_zero_of_mul_eq_zero
-/
instance : NoZeroDivisors (Int√d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain (Int√d)
  body: NoZeroDivisors.to_isDomain _

中文:
实例 :
  签名: 是整环 (整数√d)
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance : IsDomain (Int√d) :=
  NoZeroDivisors.to_isDomain _

/--
theorem `mul_pos` / 定理 `mul_pos`

English:
theorem mul_pos
  given: (a b : Int√d) (a0 : 0 < a) (b0 : 0 < b)
  statement: 0 < a * b
  proof: fun ab =>
  Or.elim
    (eq_zero_or_eq_zero_of_mul_eq_zero
      (_root_.le_antisymm ab (Zsqrtd.mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (fun e => ne_of_gt a0 e) fun e => ne_of_gt b0 e

中文:
定理 mul_pos
  条件: (a b : 整数√d) (a0 : 0 < a) (b0 : 0 < b)
  结论: 0 < a * b
  证明: fun ab =>
  Or.elim
    (eq_zero_or_eq_zero_of_mul_eq_zero
      (_root_.le_antisymm ab (Zsqrtd.mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (fun e => ne_of_gt a0 e) fun e => ne_of_gt b0 e
-/
protected theorem mul_pos (a b : Int√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := fun ab =>
  Or.elim
    (eq_zero_or_eq_zero_of_mul_eq_zero
      (_root_.le_antisymm ab (Zsqrtd.mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (fun e => ne_of_gt a0 e) fun e => ne_of_gt b0 e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ZeroLEOneClass (Int√d)
  body: { zero_le_one := by trivial }

中文:
实例 :
  签名: ZeroLEOne类 (整数√d)
  定义体: { zero_le_one := by trivial }

Depends on / 依赖: zero_le_one
-/
instance : ZeroLEOneClass (Int√d) :=
  { zero_le_one := by trivial }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (Int√d)
  body: { add_le_add_left := fun a b ab c => show Nonneg _ by rwa [add_sub_add_right_eq_sub] }

@[deprecated _root_.le_of_add_le_add_left (since := "2026-02-19")]

中文:
实例 :
  签名: 是OrderedAdd幺半群 (整数√d)
  定义体: { add_le_add_left := fun a b ab c => show Nonneg _ by rwa [add_sub_add_right_eq_sub] }

@[deprecated _root_.le_of_add_le_add_left (since := "2026-02-19")]

Depends on / 依赖: Nonneg, add_le_add_left, add_sub_add_right_eq_sub
-/
instance : IsOrderedAddMonoid (Int√d) :=
  { add_le_add_left := fun a b ab c => show Nonneg _ by rwa [add_sub_add_right_eq_sub] }

@[deprecated _root_.le_of_add_le_add_left (since := "2026-02-19")]
/--
theorem `le_of_add_le_add_left` / 定理 `le_of_add_le_add_left`

English:
theorem le_of_add_le_add_left
  given: (a b c : Int√d) (h : c + a <= c + b)
  statement: a <= b
  proof: by
  exact _root_.le_of_add_le_add_left h

@[deprecated _root_.add_lt_add_left (since := "2026-02-19")]

中文:
定理 le_of_add_le_add_left
  条件: (a b c : 整数√d) (h : c + a <= c + b)
  结论: a <= b
  证明: by
  exact _root_.le_of_add_le_add_left h

@[deprecated _root_.add_lt_add_left (since := "2026-02-19")]
-/
protected theorem le_of_add_le_add_left (a b c : Int√d) (h : c + a <= c + b) : a <= b := by
  exact _root_.le_of_add_le_add_left h

@[deprecated _root_.add_lt_add_left (since := "2026-02-19")]
/--
theorem `add_lt_add_left` / 定理 `add_lt_add_left`

English:
theorem add_lt_add_left
  given: (a b : Int√d) (h : a < b) (c)
  statement: c + a < c + b
  proof: fun h' =>
  h (_root_.le_of_add_le_add_left h')

中文:
定理 add_lt_add_left
  条件: (a b : 整数√d) (h : a < b) (c)
  结论: c + a < c + b
  证明: fun h' =>
  h (_root_.le_of_add_le_add_left h')

Depends on / 依赖: Kernel, isFiniteKernel_of_isFiniteKernel_fst
-/
protected theorem add_lt_add_left (a b : Int√d) (h : a < b) (c) : c + a < c + b := fun h' =>
  h (_root_.le_of_add_le_add_left h')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictOrderedRing (Int√d)
  body: .of_mul_pos Zsqrtd.mul_pos

中文:
实例 :
  签名: 是StrictOrdered环 (整数√d)
  定义体: .of_mul_pos Zsqrtd.mul_pos

Depends on / 依赖: Zsqrtd, Zsqrtd.mul_pos, mul_pos, of_mul_pos
-/
instance : IsStrictOrderedRing (Int√d) :=
  .of_mul_pos Zsqrtd.mul_pos

end

/--
theorem `norm_eq_zero` / 定理 `norm_eq_zero`

English:
theorem norm_eq_zero
  given: {d : Int} (h_nonsquare : forall n : Int, d != n * n) (a : Int√d)
  statement: norm a = 0 ↔ a = 0
  proof: by
  refine ⟨fun ha => Zsqrtd.ext_iff.mpr ?_, fun h => by rw [h, norm_zero]⟩
  dsimp only [norm] at ha
  rw [sub_eq_zero] at ha
  by_cases! h : 0 <= d
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le h
have : Nonsquare d' := ⟨fun n h => h_nonsquare n mod_cast h⟩
    exact divides_sq_eq_zero_z ha
  · suffices a.re * a.re = 0 by
      rw [eq_zero_of_mul_self_eq_zero this] at ha ⊢
      simpa only [true_and, or_self_right, re_zero, im_zero, eq_self_iff_true, zero_eq_mul,
        mul_zero, mul_eq_zero, h.ne, false_or, or_self_iff] using ha
    apply _root_.le_antisymm _ (mul_self_nonneg _)
    rw [ha]; rw [mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _)

中文:
定理 norm_eq_zero
  条件: {d : 整数} (h_nonsquare : 对任意 n : 整数, d != n * n) (a : 整数√d)
  结论: norm a = 0 ↔ a = 0
  证明: by
  refine ⟨fun ha => Zsqrtd.ext_iff.mpr ?_, fun h => by rw [h, norm_zero]⟩
  dsimp only [norm] at ha
  rw [sub_eq_zero] at ha
  by_cases! h : 0 <= d
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le h
have : Nonsquare d' := ⟨fun n h => h_nonsquare n mod_cast h⟩
    exact divides_sq_eq_zero_z ha
  · suffices a.re * a.re = 0 by
      rw [eq_zero_of_mul_self_eq_zero this] at ha ⊢
      simpa only [true_and, or_self_right, re_zero, im_zero, eq_self_iff_true, zero_eq_mul,
        mul_zero, mul_eq_zero, h.ne, false_or, or_self_iff] using ha
    apply _root_.le_antisymm _ (mul_self_nonneg _)
    rw [ha]; rw [mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _)

Depends on / 依赖: Int.eq_ofNat_of_zero_le, Nonsquare, Zsqrtd, Zsqrtd.ext_iff.mpr, a.re, divides_sq_eq_zero_z, eq_ofNat_of_zero_le, eq_self_iff_true, eq_zero_of_mul_self_eq_zero, ext_iff, false_or, h.ne, h_nonsquare, im_zero, mod_cast, mul_eq_zero, mul_zero, norm_zero, or_self_iff, or_self_right
-/
theorem norm_eq_zero {d : Int} (h_nonsquare : forall n : Int, d != n * n) (a : Int√d) : norm a = 0 ↔ a = 0 := by
  refine ⟨fun ha => Zsqrtd.ext_iff.mpr ?_, fun h => by rw [h, norm_zero]⟩
  dsimp only [norm] at ha
  rw [sub_eq_zero] at ha
  by_cases! h : 0 <= d
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le h
have : Nonsquare d' := ⟨fun n h => h_nonsquare n mod_cast h⟩
    exact divides_sq_eq_zero_z ha
  · suffices a.re * a.re = 0 by
      rw [eq_zero_of_mul_self_eq_zero this] at ha ⊢
      simpa only [true_and, or_self_right, re_zero, im_zero, eq_self_iff_true, zero_eq_mul,
        mul_zero, mul_eq_zero, h.ne, false_or, or_self_iff] using ha
    apply _root_.le_antisymm _ (mul_self_nonneg _)
    rw [ha]; rw [mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _)

variable {R : Type*}

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: [NonAssocRing R] {d : Int} (f g : Int√d ->+* R) (h : f sqrtd = g sqrtd)
  statement: f = g
  proof: by
  ext ⟨re_x, im_x⟩
  simp [decompose, h]

中文:
定理 hom_ext
  条件: [非结合环 R] {d : 整数} (f g : 整数√d ->+* R) (h : f sqrtd = g sqrtd)
  结论: f = g
  证明: by
  ext ⟨re_x, im_x⟩
  simp [decompose, h]

Depends on / 依赖: decompose, im_x, re_x
-/
theorem hom_ext [NonAssocRing R] {d : Int} (f g : Int√d ->+* R) (h : f sqrtd = g sqrtd) : f = g := by
  ext ⟨re_x, im_x⟩
  simp [decompose, h]

variable [CommRing R]

/-- The unique `RingHom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` with the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` in `R`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {d : Int}
  body: { toFun := fun a => a.1 + a.2 * (r : R)
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [re_add, Int.cast_add, im_add]
        ring
      map_one' := by simp
      map_mul' := fun a b => by
        have :
          (a.re + a.im * r : R) * (b.re + b.im * r) =
            a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) := by
          ring
        simp only [re_mul, Int.cast_add, Int.cast_mul, im_mul, this, r.prop]
        ring }
  invFun f := ⟨f sqrtd, by rw [← f.map_mul, dmuld, map_intCast]⟩
  left_inv r := by simp
  right_inv f := by
    ext
    simp

中文:
定义 lift
  签名: {d : 整数}
  定义体: { toFun := fun a => a.1 + a.2 * (r : R)
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [re_add, Int.cast_add, im_add]
        ring
      map_one' := by simp
      map_mul' := fun a b => by
        have :
          (a.re + a.im * r : R) * (b.re + b.im * r) =
            a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) := by
          ring
        simp only [re_mul, Int.cast_add, Int.cast_mul, im_mul, this, r.prop]
        ring }
  invFun f := ⟨f sqrtd, by rw [← f.map_mul, dmuld, map_intCast]⟩
  left_inv r := by simp
  right_inv f := by
    ext
    simp

Depends on / 依赖: Int.cast_add, Int.cast_mul, a.im, a.re, b.im, b.re, cast_add, cast_mul, f.map_mul, im_add, im_mul, invFun, left_inv, map_add, map_intCast, map_mul, map_one, map_zero, r.prop, re_add
-/
def lift {d : Int} : { r : R // r * r = ↑d } ≃ (Int√d ->+* R) where
  toFun r :=
    { toFun := fun a => a.1 + a.2 * (r : R)
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [re_add, Int.cast_add, im_add]
        ring
      map_one' := by simp
      map_mul' := fun a b => by
        have :
          (a.re + a.im * r : R) * (b.re + b.im * r) =
            a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) := by
          ring
        simp only [re_mul, Int.cast_add, Int.cast_mul, im_mul, this, r.prop]
        ring }
  invFun f := ⟨f sqrtd, by rw [← f.map_mul, dmuld, map_intCast]⟩
  left_inv r := by simp
  right_inv f := by
    ext
    simp

/--
theorem `lift_injective` / 定理 `lift_injective`

English:
theorem lift_injective
  statement: [CharZero R] {d : Int} (r : { r : R // r * r = ↑d })
  proof: (injective_iff_map_eq_zero (lift r)).mpr fun a ha => by
    have h_inj : Function.Injective ((↑) : Int -> R) := Int.cast_injective
    suffices lift r a.norm = 0 by
      simp only [re_intCast, add_zero, lift_apply_apply, im_intCast, Int.cast_zero,
        zero_mul] at this
      rwa [← Int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this
    rw [norm_eq_mul_conj]; rw [map_mul]; rw [ha]; rw [zero_mul]

中文:
定理 lift_injective
  结论: [特征零 R] {d : 整数} (r : { r : R // r * r = ↑d })
  证明: (injective_iff_map_eq_zero (lift r)).mpr fun a ha => by
    have h_inj : Function.Injective ((↑) : Int -> R) := Int.cast_injective
    suffices lift r a.norm = 0 by
      simp only [re_intCast, add_zero, lift_apply_apply, im_intCast, Int.cast_zero,
        zero_mul] at this
      rwa [← Int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this
    rw [norm_eq_mul_conj]; rw [map_mul]; rw [ha]; rw [zero_mul]

Depends on / 依赖: Function, Function.Injective, Injective, Int.cast_injective, Int.cast_zero, a.norm, add_zero, cast_injective, cast_zero, eq_iff, h_inj, h_inj.eq_iff, im_intCast, injective_iff_map_eq_zero, lift_apply_apply, map_mul, norm_eq_mul_conj, norm_eq_zero, re_intCast, zero_mul
-/
theorem lift_injective [CharZero R] {d : Int} (r : { r : R // r * r = ↑d })
    (hd : forall n : Int, d != n * n) : Function.Injective (lift r) :=
  (injective_iff_map_eq_zero (lift r)).mpr fun a ha => by
    have h_inj : Function.Injective ((↑) : Int -> R) := Int.cast_injective
    suffices lift r a.norm = 0 by
      simp only [re_intCast, add_zero, lift_apply_apply, im_intCast, Int.cast_zero,
        zero_mul] at this
      rwa [← Int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this
    rw [norm_eq_mul_conj]; rw [map_mul]; rw [ha]; rw [zero_mul]

/--
theorem `norm_eq_one_iff_mem_unitary` / 定理 `norm_eq_one_iff_mem_unitary`

English:
theorem norm_eq_one_iff_mem_unitary
  given: {d : Int} {a : Int√d}
  statement: a.norm = 1 ↔ a in unitary (Int√d)
  proof: by
  rw [Unitary.mem_iff_self_mul_star]; rw [← norm_eq_mul_conj]
  norm_cast

中文:
定理 norm_eq_one_iff_mem_unitary
  条件: {d : 整数} {a : 整数√d}
  结论: a.norm = 1 ↔ a in unitary (整数√d)
  证明: by
  rw [Unitary.mem_iff_self_mul_star]; rw [← norm_eq_mul_conj]
  norm_cast

Depends on / 依赖: Unitary, Unitary.mem_iff_self_mul_star, mem_iff_self_mul_star, norm_eq_mul_conj
-/
theorem norm_eq_one_iff_mem_unitary {d : Int} {a : Int√d} : a.norm = 1 ↔ a in unitary (Int√d) := by
  rw [Unitary.mem_iff_self_mul_star]; rw [← norm_eq_mul_conj]
  norm_cast

/--
theorem `mker_norm_eq_unitary` / 定理 `mker_norm_eq_unitary`

English:
theorem mker_norm_eq_unitary
  given: {d : Int}
  statement: MonoidHom.mker (@normMonoidHom d) = unitary (Int√d)
  proof: Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

中文:
定理 mker_norm_eq_unitary
  条件: {d : 整数}
  结论: 幺半群态射.mker (@normMonoidHom d) = unitary (整数√d)
  证明: Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

Depends on / 依赖: Submonoid, Submonoid.ext, norm_eq_one_iff_mem_unitary
-/
theorem mker_norm_eq_unitary {d : Int} : MonoidHom.mker (@normMonoidHom d) = unitary (Int√d) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

end Zsqrtd
