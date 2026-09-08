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
/-
**Zsqrtd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℤ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case.
-/
structure Zsqrtd (d : ℤ) where
  /-- Component of the integer not multiplied by `√d` -/
  re : ℤ
  /-- Component of the integer multiplied by `√d` -/
  im : ℤ
  deriving DecidableEq

@[inherit_doc] prefix:100 "ℤ√" => Zsqrtd

namespace Zsqrtd

section

variable {d : ℤ}

/-- Convert an integer to a `ℤ√d` -/
/-
**Zsqrtd.ofInt** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：ofInt (n : Int) : Int√d
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert an integer to a `ℤ√d`
-/
def ofInt (n : ℤ) : ℤ√d :=
  ⟨n, 0⟩
/-
**Zsqrtd.re_ofInt** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_ofInt (n : Int) : (ofInt n : Int√d).re = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_ofInt (n : ℤ) : (ofInt n : ℤ√d).re = n :=
  rfl
/-
**Zsqrtd.im_ofInt** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_ofInt (n : Int) : (ofInt n : Int√d).im = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_ofInt (n : ℤ) : (ofInt n : ℤ√d).im = 0 :=
  rfl

/-- The zero of the ring -/
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero of the ring
-/
instance : Zero (ℤ√d) :=
  ⟨ofInt 0⟩

@[simp]
/-
**Zsqrtd.re_zero** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_zero : (0 : Int√d).re = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_zero : (0 : ℤ√d).re = 0 :=
  rfl

@[simp]
/-
**Zsqrtd.im_zero** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_zero : (0 : Int√d).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_zero : (0 : ℤ√d).im = 0 :=
  rfl
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ℤ√d) :=
  ⟨0⟩

/-- The one of the ring -/
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one of the ring
-/
instance : One (ℤ√d) :=
  ⟨ofInt 1⟩

@[simp]
/-
**Zsqrtd.re_one** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_one : (1 : Int√d).re = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_one : (1 : ℤ√d).re = 1 :=
  rfl

@[simp]
/-
**Zsqrtd.im_one** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_one : (1 : Int√d).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_one : (1 : ℤ√d).im = 0 :=
  rfl

/-- The representative of `√d` in the ring -/
/-
**Zsqrtd.sqrtd** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：sqrtd : Int√d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representative of `√d` in the ring
-/
def sqrtd : ℤ√d :=
  ⟨0, 1⟩

@[simp]
/-
**Zsqrtd.re_sqrtd** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_sqrtd : (sqrtd : Int√d).re = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_sqrtd : (sqrtd : ℤ√d).re = 0 :=
  rfl

@[simp]
/-
**Zsqrtd.im_sqrtd** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_sqrtd : (sqrtd : Int√d).im = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_sqrtd : (sqrtd : ℤ√d).im = 1 :=
  rfl

/-- Addition of elements of `ℤ√d` -/
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of elements of `ℤ√d`
-/
instance : Add (ℤ√d) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
/-
**Zsqrtd.add_def** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：add_def (x y x' y' : Int) : (⟨x, y⟩ + ⟨x', y'⟩ : Int√d) = ⟨x + x', y + y'⟩
参数：x y x' y' : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_def (x y x' y' : ℤ) : (⟨x, y⟩ + ⟨x', y'⟩ : ℤ√d) = ⟨x + x', y + y'⟩ :=
  rfl

@[simp]
/-
**Zsqrtd.re_add** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_add (z w : Int√d) : (z + w).re = z.re + w.re
参数：z w : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_add (z w : ℤ√d) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
/-
**Zsqrtd.im_add** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_add (z w : Int√d) : (z + w).im = z.im + w.im
参数：z w : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_add (z w : ℤ√d) : (z + w).im = z.im + w.im :=
  rfl

/-- Negation in `ℤ√d` -/
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negation in `ℤ√d`
-/
instance : Neg (ℤ√d) :=
  ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]
/-
**Zsqrtd.re_neg** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_neg (z : Int√d) : (-z).re = -z.re
参数：z : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_neg (z : ℤ√d) : (-z).re = -z.re :=
  rfl

@[simp]
/-
**Zsqrtd.im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_neg (z : Int√d) : (-z).im = -z.im
参数：z : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_neg (z : ℤ√d) : (-z).im = -z.im :=
  rfl

/-- Multiplication in `ℤ√d` -/
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication in `ℤ√d`
-/
instance : Mul (ℤ√d) :=
  ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]
/-
**Zsqrtd.re_mul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_mul (z w : Int√d) : (z * w).re = z.re * w.re + d * z.im * w.im
参数：z w : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_mul (z w : ℤ√d) : (z * w).re = z.re * w.re + d * z.im * w.im :=
  rfl

@[simp]
/-
**Zsqrtd.im_mul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_mul (z w : Int√d) : (z * w).im = z.re * w.im + z.im * w.re
参数：z w : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_mul (z w : ℤ√d) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
/-
**Zsqrtd.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：addCommGroup : AddCommGroup (Int√d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup (ℤ√d) := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]
/-
**Zsqrtd.re_sub** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_sub (z w : Int√d) : (z - w).re = z.re - w.re
参数：z w : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_sub (z w : ℤ√d) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
/-
**Zsqrtd.im_sub** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_sub (z w : Int√d) : (z - w).im = z.im - w.im
参数：z w : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_sub (z w : ℤ√d) : (z - w).im = z.im - w.im :=
  rfl
/-
**Zsqrtd.addGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：addGroupWithOne : AddGroupWithOne (Int√d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroupWithOne : AddGroupWithOne (ℤ√d) :=
  { Zsqrtd.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }
/-
**Zsqrtd.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：commRing : CommRing (Int√d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing : CommRing (ℤ√d) := by
  refine
  { Zsqrtd.addGroupWithOne with
    npow := @npowRec (ℤ√d) ⟨1⟩ ⟨(· * ·)⟩,
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
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemigroup (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semigroup (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommSemigroup (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSemigroup (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring (ℤ√d) := by infer_instance
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Distrib (ℤ√d) := by infer_instance

/-- Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`. -/
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`.
-/
instance : Star (ℤ√d) where
  star z := ⟨z.1, -z.2⟩

@[simp]
/-
**Zsqrtd.star_mk** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：star_mk (x y : Int) : star (⟨x, y⟩ : Int√d) = ⟨x, -y⟩
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_mk (x y : ℤ) : star (⟨x, y⟩ : ℤ√d) = ⟨x, -y⟩ :=
  rfl

@[simp]
/-
**Zsqrtd.re_star** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_star (z : Int√d) : (star z).re = z.re
参数：z : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_star (z : ℤ√d) : (star z).re = z.re :=
  rfl

@[simp]
/-
**Zsqrtd.im_star** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_star (z : Int√d) : (star z).im = -z.im
参数：z : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_star (z : ℤ√d) : (star z).im = -z.im :=
  rfl
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRing (ℤ√d) where
  star_involutive _ := Zsqrtd.ext rfl (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add _ _ := Zsqrtd.ext rfl (neg_add _ _)

-- Porting note: proof was `by decide`
/-
**Zsqrtd.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：nontrivial : Nontrivial (Int√d)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Zsqrtd.ext_iff`：∀ {d : ℤ} {x y : ℤ√d}, x = y ↔ x.re = y.re ∧ x.im = y.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance nontrivial : Nontrivial (ℤ√d) :=
  ⟨⟨0, 1, Zsqrtd.ext_iff.not.mpr (by simp)⟩⟩

@[simp]
/-
**Zsqrtd.re_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_natCast (n : Nat) : (n : Int√d).re = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_natCast (n : ℕ) : (n : ℤ√d).re = n :=
  rfl

@[simp]
/-
**Zsqrtd.re_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Int√d).re = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℤ√d).re = n :=
  rfl

@[simp]
/-
**Zsqrtd.im_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_natCast (n : Nat) : (n : Int√d).im = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_natCast (n : ℕ) : (n : ℤ√d).im = 0 :=
  rfl

@[simp]
/-
**Zsqrtd.im_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Int√d).im = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℤ√d).im = 0 :=
  rfl
/-
**Zsqrtd.natCast_val** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：natCast_val (n : Nat) : (n : Int√d) = ⟨n, 0⟩
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_val (n : ℕ) : (n : ℤ√d) = ⟨n, 0⟩ :=
  rfl

@[simp]
/-
**Zsqrtd.re_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_intCast (n : Int) : (n : Int√d).re = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem re_intCast (n : ℤ) : (n : ℤ√d).re = n := by cases n <;> rfl

@[simp]
/-
**Zsqrtd.im_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_intCast (n : Int) : (n : Int√d).im = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem im_intCast (n : ℤ) : (n : ℤ√d).im = 0 := by cases n <;> rfl
/-
**Zsqrtd.intCast_val** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：intCast_val (n : Int) : (n : Int√d) = ⟨n, 0⟩
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
-/
theorem intCast_val (n : ℤ) : (n : ℤ√d) = ⟨n, 0⟩ := by ext <;> simp
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharZero (ℤ√d) where cast_injective m n := by simp [Zsqrtd.ext_iff]

@[simp]
/-
**Zsqrtd.ofInt_eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：ofInt_eq_intCast (n : Int) : (ofInt n : Int√d) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
-/
theorem ofInt_eq_intCast (n : ℤ) : (ofInt n : ℤ√d) = n := by ext <;> simp [re_ofInt, im_ofInt]

@[simp]
/-
**Zsqrtd.nsmul_val** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nsmul_val (n : Nat) (x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
参数：n : Nat；x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nsmul_val (n : ℕ) (x y : ℤ) : (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by ext <;> simp

@[simp]
/-
**Zsqrtd.smul_val** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：smul_val (n x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
参数：n x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_val (n x y : ℤ) : (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by ext <;> simp
/-
**Zsqrtd.re_smul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：re_smul (a : Int) (b : Int√d) : (↑a * b).re = a * b.re
参数：a : Int；b : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_smul (a : ℤ) (b : ℤ√d) : (↑a * b).re = a * b.re := by simp
/-
**Zsqrtd.im_smul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：im_smul (a : Int) (b : Int√d) : (↑a * b).im = a * b.im
参数：a : Int；b : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_smul (a : ℤ) (b : ℤ√d) : (↑a * b).im = a * b.im := by simp

@[simp]
/-
**Zsqrtd.muld_val** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：muld_val (x y : Int) : sqrtd (d
参数：x y : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem muld_val (x y : ℤ) : sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩ := by ext <;> simp

@[simp]
/-
**Zsqrtd.dmuld** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：dmuld : sqrtd (d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
-/
theorem dmuld : sqrtd (d := d) * sqrtd (d := d) = d := by ext <;> simp

@[simp]
/-
**Zsqrtd.smuld_val** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：smuld_val (n x y : Int) : sqrtd * (n : Int√d) * ⟨x, y⟩ = ⟨d * n * y, n * x
⟩
参数：n x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smuld_val (n x y : ℤ) : sqrtd * (n : ℤ√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ := by ext <;> simp
/-
**Zsqrtd.decompose** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：decompose {x y : Int} : (⟨x, y⟩ : Int√d) = x + sqrtd (d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ√d) = x + sqrtd (d := d) * y := by ext <;> simp
/-
**Zsqrtd.mul_star** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：mul_star {x y : Int} : (⟨x, y⟩ * star ⟨x, y⟩ : Int√d) = x * x - d * y * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem mul_star {x y : ℤ} : (⟨x, y⟩ * star ⟨x, y⟩ : ℤ√d) = x * x - d * y * y := by
  ext <;> simp [sub_eq_add_neg, mul_comm]
/-
**Zsqrtd.intCast_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：intCast_dvd (z : Int) (a : Int√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im
参数：z : Int；a : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zsqrtd.smul_val`：smul_val (n x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x,
 n * y⟩
· 使用定理 `Zsqrtd.ext_iff`：∀ {d : ℤ} {x y : ℤ√d}, x = y ↔ x.re = y.re ∧ x.im = y.im
-/
theorem intCast_dvd (z : ℤ) (a : ℤ√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val, Zsqrtd.ext_iff]
    exact ⟨hr, hi⟩

@[simp, norm_cast]
/-
**Zsqrtd.intCast_dvd_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：intCast_dvd_intCast (a b : Int) : (a : Int√d) ∣ b ↔ a ∣ b
参数：a b : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.intCast_dvd`：intCast_dvd (z : Int) (a : Int√d) : ↑z ∣ a ↔ z ∣ a.r
e ∧ z ∣ a.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intCast_dvd_intCast (a b : ℤ) : (a : ℤ√d) ∣ b ↔ a ∣ b := by
  rw [intCast_dvd]
  simp
/-
**Zsqrtd.eq_of_smul_eq_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d a : ℤ} {b c : ℤ√d}, a ≠ 0 → ↑a * b = ↑a * c → b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.ext_iff`：∀ {d : ℤ} {x y : ℤ√d}, x = y ↔ x.re = y.re ∧ x.im = y.im
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_smul`：re_smul (a : Int) (b : Int√d) : (↑a * b).re = a * b.re
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Zsqrtd.im_smul`：im_smul (a : Int) (b : Int√d) : (↑a * b).im = a * b.im
-/
protected theorem eq_of_smul_eq_smul_left {a : ℤ} {b c : ℤ√d} (ha : a ≠ 0) (h : ↑a * b = a * c) :
    b = c := by
  rw [Zsqrtd.ext_iff] at h ⊢
  apply And.imp _ _ h <;> simpa only [re_smul, im_smul] using mul_left_cancel₀ ha

section Gcd

/-
**Zsqrtd.gcd_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：gcd_eq_zero_iff (a : Int√d) : Int.gcd a.re a.im = 0 ↔ a = 0
参数：a : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gcd_eq_zero_iff (a : ℤ√d) : Int.gcd a.re a.im = 0 ↔ a = 0 := by
  simp only [Int.gcd_eq_zero_iff, Zsqrtd.ext_iff, im_zero, re_zero]
/-
**Zsqrtd.gcd_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：gcd_pos_iff (a : Int√d) : 0 < Int.gcd a.re a.im ↔ a != 0
参数：a : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Zsqrtd.gcd_eq_zero_iff`：gcd_eq_zero_iff (a : Int√d) : Int.gcd a.re a.im 
= 0 ↔ a = 0
-/
theorem gcd_pos_iff (a : ℤ√d) : 0 < Int.gcd a.re a.im ↔ a ≠ 0 :=
  pos_iff_ne_zero.trans <| not_congr a.gcd_eq_zero_iff
/-
**Zsqrtd.isCoprime_of_dvd_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：isCoprime_of_dvd_isCoprime {a b : Int√d} (hcoprime : IsCoprime a.re a.im) 
(hdvd : b ∣ a) : IsCoprime b.re b.im
参数：hcoprime : IsCoprime a.re a.im；hdvd : b ∣ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_of_dvd`：isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0)
) (H : forall z in nonunits R, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `Zsqrtd.intCast_dvd`：intCast_dvd (z : Int) (a : Int√d) : ↑z ∣ a ↔ z ∣ a.r
e ∧ z ∣ a.im
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `IsCoprime.isUnit_of_dvd'`：IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCo
prime a b) (ha : x ∣ a) (hb : x ∣ b) : IsUnit x
-/
theorem isCoprime_of_dvd_isCoprime {a b : ℤ√d} (hcoprime : IsCoprime a.re a.im) (hdvd : b ∣ a) :
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
/-
**Zsqrtd.exists_coprime_of_gcd_pos** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：exists_coprime_of_gcd_pos {a : Int√d} (hgcd : 0 < Int.gcd a.re a.im) : exi
sts b : Int√d, a = ((Int.gcd a.re a.im : Int) : Int√d) * b ∧ IsCoprime b.re b.im
参数：hgcd : 0 < Int.gcd a.re a.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.exists_gcd_one`：exists_gcd_one {m n : Int} (H : 0 < gcd m n) : exist
s m' n' : Int, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.smul_val`：smul_val (n x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x,
 n * y⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
-/
theorem exists_coprime_of_gcd_pos {a : ℤ√d} (hgcd : 0 < Int.gcd a.re a.im) :
    ∃ b : ℤ√d, a = ((Int.gcd a.re a.im : ℤ) : ℤ√d) * b ∧ IsCoprime b.re b.im := by
  obtain ⟨re, im, H1, Hre, Him⟩ := Int.exists_gcd_one hgcd
  rw [mul_comm] at Hre Him
  refine ⟨⟨re, im⟩, ?_, ?_⟩
  · rw [smul_val, ← Hre, ← Him]
  · rw [Int.isCoprime_iff_gcd_eq_one, H1]

end Gcd

/-- Read `SqLe a c b d` as `a √c ≤ b √d` -/
/-
**Zsqrtd.SqLe** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：SqLe (a c b d : Nat) : Prop
参数：a c b d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Read `SqLe a c b d` as `a √c ≤ b √d`
-/
def SqLe (a c b d : ℕ) : Prop :=
  c * a * a ≤ d * b * b
/-
**Zsqrtd.sqLe_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：sqLe_of_le {c d x y z w : Nat} (xz : z <= x) (yw : y <= w) (xy : SqLe x c 
y d) : SqLe z c w d
参数：xz : z <= x；yw : y <= w；xy : SqLe x c y d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem sqLe_of_le {c d x y z w : ℕ} (xz : z ≤ x) (yw : y ≤ w) (xy : SqLe x c y d) :
    SqLe z c w d := calc
  c * z * z ≤ c * x * x := by gcongr
  _ ≤ d * y * y := xy
  _ ≤ d * w * w := by gcongr
/-
**Zsqrtd.sqLe_add_mixed** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：sqLe_add_mixed {c d x y z w : Nat} (xy : SqLe x c y d) (zw : SqLe z c w d)
 : c * (x * z) <= d * (y * w)
参数：xy : SqLe x c y d；zw : SqLe z c w d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_self_le_mul_self_iff`：∀ {m n : ℕ}, m * m ≤ n * n ↔ m ≤ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
-/
theorem sqLe_add_mixed {c d x y z w : ℕ} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    c * (x * z) ≤ d * (y * w) :=
  Nat.mul_self_le_mul_self_iff.1 <| by
    simpa [mul_comm, mul_left_comm] using Nat.mul_le_mul xy zw
/-
**Zsqrtd.sqLe_add** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：sqLe_add {c d x y z w : Nat} (xy : SqLe x c y d) (zw : SqLe z c w d) : SqL
e (x + z) c (y + w) d
参数：xy : SqLe x c y d；zw : SqLe z c w d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.sqLe_add_mixed`：sqLe_add_mixed {c d x y z w : Nat} (xy : SqLe x c
 y d) (zw : SqLe z c w d) : c * (x * z) <= d * (y * w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem sqLe_add {c d x y z w : ℕ} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    SqLe (x + z) c (y + w) d := by
  have xz := sqLe_add_mixed xy zw
  simp only [SqLe, mul_assoc] at xy zw
  simp [SqLe, mul_add, mul_comm, mul_left_comm, add_le_add, *]
/-
**Zsqrtd.sqLe_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：sqLe_cancel {c d x y z w : Nat} (zw : SqLe y d x c) (h : SqLe (x + z) c (y
 + w) d) : SqLe z c w d
参数：zw : SqLe y d x c；h : SqLe (x + z) c (y + w) d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Zsqrtd.sqLe_add_mixed`：sqLe_add_mixed {c d x y z w : Nat} (xy : SqLe x c
 y d) (zw : SqLe z c w d) : c * (x * z) <= d * (y * w)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem sqLe_cancel {c d x y z w : ℕ} (zw : SqLe y d x c) (h : SqLe (x + z) c (y + w) d) :
    SqLe z c w d := by
  apply le_of_not_gt
  intro l
  refine not_le_of_gt ?_ h
  simp only [mul_add, mul_comm, mul_left_comm, add_assoc]
  have hm := sqLe_add_mixed zw (le_of_lt l)
  simp only [SqLe, mul_assoc] at l zw
  grw [zw, hm]
  gcongr
/-
**Zsqrtd.sqLe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：sqLe_smul {c d x y : Nat} (n : Nat) (xy : SqLe x c y d) : SqLe (n * x) c (
n * y) d
参数：n : Nat；xy : SqLe x c y d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
-/
theorem sqLe_smul {c d x y : ℕ} (n : ℕ) (xy : SqLe x c y d) : SqLe (n * x) c (n * y) d := by
  simpa [SqLe, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left (n * n) xy
/-
**Zsqrtd.sqLe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：sqLe_mul {d x y z w : Nat} : (SqLe x 1 y d -> SqLe z 1 w d -> SqLe (x * w 
+ y * z) d (x * z + d * y * w) 1) ∧ (SqLe x 1 y d -> SqLe w d z 1 -> SqLe (x * z
 + d * y * w) 1 (x * w + y * z) d) ∧ (SqLe y d x 1 -> SqLe z 1 w d -> SqLe (x * 
z + d * y * w) 1 (x * w + y * z) d) ∧ (SqLe y d x 1 -> SqLe w d z 1 -> SqLe (x *
 w + y * z) d (x * z + d * y * w) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.mul_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_le_ofNat_of_le`：∀ {m n : ℕ}, m ≤ n → ↑m ≤ ↑n
· 使用定理 `Int.le_of_ofNat_le_ofNat`：∀ {m n : ℕ}, ↑m ≤ ↑n → m ≤ n
· 使用定理 `le_of_sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, 0 ≤ a - b → b ≤ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
（共 47 条，此处仅展示前 30 条）
-/
theorem sqLe_mul {d x y z w : ℕ} :
    (SqLe x 1 y d → SqLe z 1 w d → SqLe (x * w + y * z) d (x * z + d * y * w) 1) ∧
      (SqLe x 1 y d → SqLe w d z 1 → SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
        (SqLe y d x 1 → SqLe z 1 w d → SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
          (SqLe y d x 1 → SqLe w d z 1 → SqLe (x * w + y * z) d (x * z + d * y * w) 1) := by
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
/-- "Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
  we are interested in the case `c = 1` but this is more symmetric -/
/-
**Zsqrtd.Nonnegg** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：ℕ → ℕ → ℤ → ℤ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
  we are interested in the case `c = 1` but this is more symmetric
-/
def Nonnegg (c d : ℕ) : ℤ → ℤ → Prop
  | (a : ℕ), (b : ℕ) => True
  | (a : ℕ), -[b+1] => SqLe (b + 1) c a d
  | -[a+1], (b : ℕ) => SqLe (a + 1) d b c
  | -[_+1], -[_+1] => False
/-
**Zsqrtd.nonnegg_comm** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonnegg_comm {c d : Nat} {x y : Int} : Nonnegg c d x y = Nonnegg d c y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonnegg_comm {c d : ℕ} {x y : ℤ} : Nonnegg c d x y = Nonnegg d c y x := by
  cases x <;> cases y <;> rfl
/-
**Zsqrtd.nonnegg_neg_pos** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Zsqrtd.SqLe a d b c
参数：-↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `trivial`：True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonnegg_neg_pos {c d} : ∀ {a b : ℕ}, Nonnegg c d (-a) b ↔ SqLe a d b c
  | 0, b => ⟨by simp [SqLe], fun _ => trivial⟩
  | a + 1, b => by rfl
/-
**Zsqrtd.nonnegg_pos_neg** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d a (-b) ↔ SqLe b c a d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.nonnegg_comm`：nonnegg_comm {c d : Nat} {x y : Int} : Nonnegg c d 
x y = Nonnegg d c y x
· 使用定理 `Zsqrtd.nonnegg_neg_pos`：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Z
sqrtd.SqLe a d b c
-/
theorem nonnegg_pos_neg {c d} {a b : ℕ} : Nonnegg c d a (-b) ↔ SqLe b c a d := by
  rw [nonnegg_comm]; exact nonnegg_neg_pos

open Int in
/-
**Zsqrtd.nonnegg_cases_right** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {c d a : ℕ} {b : ℤ}, (∀ (x : ℕ), b = -↑x → Zsqrtd.SqLe x c a d) → Zsqrtd
.Nonnegg c d (↑a) b
参数：∀ (x : ℕ), b = -↑x → Zsqrtd.SqLe x c a d；↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem nonnegg_cases_right {c d} {a : ℕ} :
    ∀ {b : ℤ}, (∀ x : ℕ, b = -x → SqLe x c a d) → Nonnegg c d a b
  | (b : Nat), _ => trivial
  | -[b+1], h => h (b + 1) rfl
/-
**Zsqrtd.nonnegg_cases_left** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonnegg_cases_left {c d} {b : Nat} {a : Int} (h : forall x : Nat, a = -x -
> SqLe x d b c) : Nonnegg c d a b
参数：h : forall x : Nat, a = -x -> SqLe x d b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.nonnegg_comm`：nonnegg_comm {c d : Nat} {x y : Int} : Nonnegg c d 
x y = Nonnegg d c y x
· 使用定理 `Zsqrtd.nonnegg_cases_right`：∀ {c d a : ℕ} {b : ℤ}, (∀ (x : ℕ), b = -↑x →
 Zsqrtd.SqLe x c a d) → Zsqrtd.Nonnegg c d (↑a) b
-/
theorem nonnegg_cases_left {c d} {b : ℕ} {a : ℤ} (h : ∀ x : ℕ, a = -x → SqLe x d b c) :
    Nonnegg c d a b :=
  cast nonnegg_comm (nonnegg_cases_right h)

section Norm

/-- The norm of an element of `ℤ[√d]`. -/
/-
**Zsqrtd.norm** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：norm (n : Int√d) : Int
参数：n : Int√d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of an element of `ℤ[√d]`.
-/
def norm (n : ℤ√d) : ℤ :=
  n.re * n.re - d * n.im * n.im
/-
**Zsqrtd.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_def (n : Int√d) : n.norm = n.re * n.re - d * n.im * n.im
参数：n : Int√d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (n : ℤ√d) : n.norm = n.re * n.re - d * n.im * n.im :=
  rfl

@[simp]
/-
**Zsqrtd.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_zero : norm (0 : Int√d) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_zero : norm (0 : ℤ√d) = 0 := by simp [norm]

@[simp]
/-
**Zsqrtd.norm_one** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_one : norm (1 : Int√d) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_one : norm (1 : ℤ√d) = 1 := by simp [norm]

@[simp]
/-
**Zsqrtd.norm_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_intCast (n : Int) : norm (n : Int√d) = n * n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_intCast (n : ℤ) : norm (n : ℤ√d) = n * n := by simp [norm]

@[simp]
/-
**Zsqrtd.norm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_natCast (n : Nat) : norm (n : Int√d) = n * n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.norm_intCast`：norm_intCast (n : Int) : norm (n : Int√d) = n * n
-/
theorem norm_natCast (n : ℕ) : norm (n : ℤ√d) = n * n :=
  norm_intCast n

@[simp]
/-
**Zsqrtd.norm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_mul (n m : Int√d) : norm (n * m) = norm n * norm m
参数：n m : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 37 条，此处仅展示前 30 条）
-/
theorem norm_mul (n m : ℤ√d) : norm (n * m) = norm n * norm m := by
  simp only [norm, im_mul, re_mul]
  ring

/-- `norm` as a `MonoidHom`. -/
/-
**Zsqrtd.normMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：normMonoidHom : Int√d ->* Int where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.norm_one`：norm_one : norm (1 : Int√d) = 1
· 使用定理 `Zsqrtd.norm_mul`：norm_mul (n m : Int√d) : norm (n * m) = norm n * norm m

--- 原说明 ---
`norm` as a `MonoidHom`.
-/
def normMonoidHom : ℤ√d →* ℤ where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one
/-
**Zsqrtd.norm_eq_mul_conj** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_mul_conj (n : Int√d) : (norm n : Int√d) = n * star n
参数：n : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
theorem norm_eq_mul_conj (n : ℤ√d) : (norm n : ℤ√d) = n * star n := by
  ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]

@[simp]
/-
**Zsqrtd.norm_neg** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_neg (x : Int√d) : (-x).norm = x.norm
参数：x : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `Zsqrtd.instCharZero`：∀ {d : ℤ}, CharZero (ℤ√d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm_eq_mul_conj`：norm_eq_mul_conj (n : Int√d) : (norm n : Int√d)
 = n * star n
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_neg (x : ℤ√d) : (-x).norm = x.norm :=
  (Int.cast_inj (α := ℤ√d)).1 <| by simp [norm_eq_mul_conj]

@[simp]
/-
**Zsqrtd.norm_conj** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_conj (x : Int√d) : (star x).norm = x.norm
参数：x : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `Zsqrtd.instCharZero`：∀ {d : ℤ}, CharZero (ℤ√d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm_eq_mul_conj`：norm_eq_mul_conj (n : Int√d) : (norm n : Int√d)
 = n * star n
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_conj (x : ℤ√d) : (star x).norm = x.norm :=
  (Int.cast_inj (α := ℤ√d)).1 <| by simp [norm_eq_mul_conj, mul_comm]
/-
**Zsqrtd.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_nonneg (hd : d <= 0) (n : Int√d) : 0 <= n.norm
参数：hd : d <= 0；n : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
-/
theorem norm_nonneg (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ n.norm :=
  add_nonneg (mul_self_nonneg _)
    (by
      rw [mul_assoc, neg_mul_eq_neg_mul]
      exact mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _))

@[simp]
/-
**Zsqrtd.abs_norm** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：abs_norm (hd : d <= 0) (n : Int√d) : |n.norm| = n.norm
参数：hd : d <= 0；n : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Zsqrtd.norm_nonneg`：norm_nonneg (hd : d <= 0) (n : Int√d) : 0 <= n.norm
-/
theorem abs_norm (hd : d ≤ 0) (n : ℤ√d) : |n.norm| = n.norm :=
  abs_of_nonneg <| norm_nonneg hd n
/-
**Zsqrtd.norm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_one_iff {x : Int√d} : x.norm.natAbs = 1 ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Zsqrtd.norm_eq_mul_conj`：norm_eq_mul_conj (n : Int√d) : (norm n : Int√d)
 = n * star n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `Zsqrtd.instCharZero`：∀ {d : ℤ}, CharZero (ℤ√d)
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.ofNat_natAbs_of_nonpos`：∀ {a : ℤ}, a ≤ 0 → ↑a.natAbs = -a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_eq_one`：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Int.natAbs_one`：Int.natAbs 1 = 1
· 使用定理 `Zsqrtd.norm_one`：norm_one : norm (1 : Int√d) = 1
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Zsqrtd.norm_mul`：norm_mul (n m : Int√d) : norm (n * m) = norm n * norm m
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem norm_eq_one_iff {x : ℤ√d} : x.norm.natAbs = 1 ↔ IsUnit x :=
  ⟨fun h =>
    isUnit_iff_dvd_one.2 <|
      (le_total 0 (norm x)).casesOn
        (fun hx =>
          ⟨star x, by
            rwa [← Int.natCast_inj, Int.natAbs_of_nonneg hx, ← @Int.cast_inj (ℤ√d) _ _,
              norm_eq_mul_conj, eq_comm] at h⟩)
        fun hx =>
          ⟨-star x, by
            rwa [← Int.natCast_inj, Int.ofNat_natAbs_of_nonpos hx, ← @Int.cast_inj (ℤ√d) _ _,
              Int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg, eq_comm] at h⟩,
    fun h => by
    let ⟨y, hy⟩ := isUnit_iff_dvd_one.1 h
    have := congr_arg (Int.natAbs ∘ norm) hy
    rw [Function.comp_apply, Function.comp_apply, norm_mul, Int.natAbs_mul, norm_one,
      Int.natAbs_one, eq_comm, mul_eq_one] at this
    exact this.1⟩
/-
**Zsqrtd.isUnit_iff_norm_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：isUnit_iff_norm_isUnit {d : Int} (z : Int√d) : IsUnit z ↔ IsUnit z.norm
参数：z : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.isUnit_iff_natAbs_eq`：isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1
· 使用定理 `Zsqrtd.norm_eq_one_iff`：norm_eq_one_iff {x : Int√d} : x.norm.natAbs = 1 
↔ IsUnit x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_norm_isUnit {d : ℤ} (z : ℤ√d) : IsUnit z ↔ IsUnit z.norm := by
  rw [Int.isUnit_iff_natAbs_eq, norm_eq_one_iff]
/-
**Zsqrtd.norm_eq_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_one_iff' {d : Int} (hd : d <= 0) (z : Int√d) : z.norm = 1 ↔ IsUnit
 z
参数：hd : d <= 0；z : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zsqrtd.norm_eq_one_iff`：norm_eq_one_iff {x : Int√d} : x.norm.natAbs = 1 
↔ IsUnit x
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `Zsqrtd.norm_nonneg`：norm_nonneg (hd : d <= 0) (n : Int√d) : 0 <= n.norm
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_eq_one_iff' {d : ℤ} (hd : d ≤ 0) (z : ℤ√d) : z.norm = 1 ↔ IsUnit z := by
  rw [← norm_eq_one_iff, ← Int.natCast_inj, Int.natAbs_of_nonneg (norm_nonneg hd z), Int.ofNat_one]
/-
**Zsqrtd.norm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_zero_iff {d : Int} (hd : d < 0) (z : Int√d) : z.norm = 0 ↔ z = 0
参数：hd : d < 0；z : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero_iff_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [ins
t_1 : PartialOrder α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ 
b → (a + b = 0 …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Zsqrtd.norm_def`：norm_def (n : Int√d) : n.norm = n.re * n.re - d * n.im 
* n.im
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `eq_zero_of_mul_self_eq_zero`：eq_zero_of_mul_self_eq_zero (h : a * a = 0)
 : a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Zsqrtd.norm_zero`：norm_zero : norm (0 : Int√d) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem norm_eq_zero_iff {d : ℤ} (hd : d < 0) (z : ℤ√d) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [norm_def, sub_eq_add_neg, mul_assoc] at h
    have left := mul_self_nonneg z.re
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im))
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg left right).mp h
    ext <;> apply eq_zero_of_mul_self_eq_zero
    · exact ha
    · rw [neg_eq_zero, mul_eq_zero] at hb
      exact hb.resolve_left hd.ne
  · rintro rfl
    exact norm_zero
/-
**Zsqrtd.norm_eq_of_associated** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_of_associated {d : Int} (hd : d <= 0) {x y : Int√d} (h : Associate
d x y) : x.norm = y.norm
参数：hd : d <= 0；h : Associated x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm_mul`：norm_mul (n m : Int√d) : norm (n * m) = norm n * norm m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.norm_eq_one_iff'`：norm_eq_one_iff' {d : Int} (hd : d <= 0) (z : I
nt√d) : z.norm = 1 ↔ IsUnit z
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem norm_eq_of_associated {d : ℤ} (hd : d ≤ 0) {x y : ℤ√d} (h : Associated x y) :
    x.norm = y.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, (norm_eq_one_iff' hd _).mpr u.isUnit, mul_one]

end Norm

end

section

variable {d : ℕ}

/-- Nonnegativity of an element of `ℤ√d`. -/
/-
**Zsqrtd.Nonneg** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：{d : ℕ} → ℤ√↑d → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nonnegativity of an element of `ℤ√d`.
-/
def Nonneg : ℤ√d → Prop
  | ⟨a, b⟩ => Nonnegg d 1 a b
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (ℤ√d) :=
  ⟨fun a b => Nonneg (b - a)⟩
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT (ℤ√d) :=
  ⟨fun a b => ¬b ≤ a⟩
/-
**Zsqrtd.decidableNonnegg** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：(c d : ℕ) → DecidableRel (Zsqrtd.Nonnegg c d)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableNonnegg (c d) : DecidableRel (Nonnegg c d)
  | .ofNat _, .ofNat _ => inferInstanceAs <| Decidable True
  | .ofNat _, .negSucc _ => inferInstanceAs <| Decidable (_ ≤ _)
  | .negSucc _, .ofNat _ => inferInstanceAs <| Decidable (_ ≤ _)
  | .negSucc _, .negSucc _ => inferInstanceAs <| Decidable False
/-
**Zsqrtd.decidableNonneg** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：{d : ℕ} → (a : ℤ√↑d) → Decidable a.Nonneg
参数：a : ℤ√↑d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableNonneg : ∀ a : ℤ√d, Decidable (Nonneg a)
  | ⟨_, _⟩ => Zsqrtd.decidableNonnegg _ _ _ _
/-
**Zsqrtd.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：decidableLE : DecidableLE (Int√d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE : DecidableLE (ℤ√d) := fun _ _ => decidableNonneg _

open Int in
/-
**Zsqrtd.nonneg_cases** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} {a : ℤ√↑d},   a.Nonneg → ∃ x y, a = { re := ↑x, im := ↑y } ∨ a =
 { re := ↑x, im := -↑y } ∨ a = { re := -↑x, im := ↑y }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonneg_cases : ∀ {a : ℤ√d}, Nonneg a → ∃ x y : ℕ, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
  | ⟨(x : ℕ), (y : ℕ)⟩, _ => ⟨x, y, Or.inl rfl⟩
  | ⟨(x : ℕ), -[y+1]⟩, _ => ⟨x, y + 1, Or.inr <| Or.inl rfl⟩
  | ⟨-[x+1], (y : ℕ)⟩, _ => ⟨x + 1, y, Or.inr <| Or.inr rfl⟩
  | ⟨-[_+1], -[_+1]⟩, h => False.elim h

open Int in
/-
**Zsqrtd.nonneg_add_lem** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_add_lem {x y z w : Nat} (xy : Nonneg (⟨x, -y⟩ : Int√d)) (zw : Nonne
g (⟨-z, w⟩ : Int√d)) : Nonneg (⟨x, -y⟩ + ⟨-z, w⟩ : Int√d)
参数：xy : Nonneg (⟨x, -y⟩ : Int√d)；zw : Nonneg (⟨-z, w⟩ : Int√d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.subNatNat_elim`：∀ (m n : ℕ) (motive : ℕ → ℕ → ℤ → Prop),   (∀ (i n :
 ℕ), motive (n + i) n ↑i) →     (∀ (i m : ℕ), motive m (m + i + 1) (Int.negSucc 
i)) → mo…
· 使用定理 `trivial`：True
· 使用定理 `Zsqrtd.sqLe_cancel`：sqLe_cancel {c d x y z w : Nat} (zw : SqLe y d x c) 
(h : SqLe (x + z) c (y + w) d) : SqLe z c w d
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Zsqrtd.sqLe_of_le`：sqLe_of_le {c d x y z w : Nat} (xz : z <= x) (yw : y 
<= w) (xy : SqLe x c y d) : SqLe z c w d
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_self_le_mul_self_iff`：∀ {m n : ℕ}, m * m ≤ n * n ↔ m ≤ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Zsqrtd.nonnegg_pos_neg`：nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d 
a (-b) ↔ SqLe b c a d
· 使用定理 `Zsqrtd.nonnegg_neg_pos`：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Z
sqrtd.SqLe a d b c
· 使用定理 `Zsqrtd.add_def`：add_def (x y x' y' : Int) : (⟨x, y⟩ + ⟨x', y'⟩ : Int√d) 
= ⟨x + x', y + y'⟩
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Int.subNatNat_eq_coe`：∀ {m n : ℕ}, Int.subNatNat m n = ↑m - ↑n
-/
theorem nonneg_add_lem {x y z w : ℕ} (xy : Nonneg (⟨x, -y⟩ : ℤ√d)) (zw : Nonneg (⟨-z, w⟩ : ℤ√d)) :
    Nonneg (⟨x, -y⟩ + ⟨-z, w⟩ : ℤ√d) := by
  have : Nonneg ⟨Int.subNatNat x z, Int.subNatNat w y⟩ :=
    Int.subNatNat_elim x z
      (fun m n i => SqLe y d m 1 → SqLe n 1 w d → Nonneg ⟨i, Int.subNatNat w y⟩)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d (k + j) 1 → SqLe k 1 m d → Nonneg ⟨Int.ofNat j, i⟩)
          (fun _ _ _ _ => trivial) fun m n xy zw => sqLe_cancel zw xy)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d k 1 → SqLe (k + j + 1) 1 m d → Nonneg ⟨-[j+1], i⟩)
          (fun m n xy zw => sqLe_cancel xy zw) fun m n xy zw =>
          let t := Nat.le_trans zw (sqLe_of_le (Nat.le_add_right n (m + 1)) le_rfl xy)
          have : k + j + 1 ≤ k :=
            Nat.mul_self_le_mul_self_iff.1 (by simpa [one_mul] using t)
          absurd this (not_le_of_gt <| Nat.succ_le_succ <| Nat.le_add_right _ _))
      (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw)
  rw [add_def, neg_add_eq_sub]
  rwa [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at this
/-
**Zsqrtd.Nonneg.add** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd.Nonneg`。
形式化陈述：∀ {d : ℕ} {a b : ℤ√↑d}, a.Nonneg → b.Nonneg → (a + b).Nonneg
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.nonneg_cases`：∀ {d : ℕ} {a : ℤ√↑d},   a.Nonneg → ∃ x y, a = { re 
:= ↑x, im := ↑y } ∨ a = { re := ↑x, im := -↑y } ∨ a = { re := -↑x, im := ↑y }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zsqrtd.nonnegg_cases_right`：∀ {c d a : ℕ} {b : ℤ}, (∀ (x : ℕ), b = -↑x →
 Zsqrtd.SqLe x c a d) → Zsqrtd.Nonnegg c d (↑a) b
· 使用定理 `Zsqrtd.sqLe_of_le`：sqLe_of_le {c d x y z w : Nat} (xz : z <= x) (yw : y 
<= w) (xy : SqLe x c y d) : SqLe z c w d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `le_of_neg_le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dLeftMono α] {a b : α} [AddRightMono α], -a ≤ -b → b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.le.intro`：∀ {a b : ℤ} (n : ℕ), a + ↑n = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Zsqrtd.nonnegg_pos_neg`：nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d 
a (-b) ↔ SqLe b c a d
· 使用定理 `Zsqrtd.nonnegg_cases_left`：nonnegg_cases_left {c d} {b : Nat} {a : Int} 
(h : forall x : Nat, a = -x -> SqLe x d b c) : Nonnegg c d a b
· 使用定理 `Zsqrtd.nonnegg_neg_pos`：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Z
sqrtd.SqLe a d b c
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.sqLe_add`：sqLe_add {c d x y z w : Nat} (xy : SqLe x c y d) (zw : 
SqLe z c w d) : SqLe (x + z) c (y + w) d
· 使用定理 `Zsqrtd.add_def`：add_def (x y x' y' : Int) : (⟨x, y⟩ + ⟨x', y'⟩ : Int√d) 
= ⟨x + x', y + y'⟩
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Zsqrtd.nonneg_add_lem`：nonneg_add_lem {x y z w : Nat} (xy : Nonneg (⟨x, 
-y⟩ : Int√d)) (zw : Nonneg (⟨-z, w⟩ : Int√d)) : Nonneg (⟨x, -y⟩ + ⟨-z, w⟩ : Int√
d)
-/
theorem Nonneg.add {a b : ℤ√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a + b) := by
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
    rw [Nat.cast_add, Nat.cast_add, neg_add] at this
    rwa [add_def]
  · exact nonneg_add_lem ha hb
  · refine nonnegg_cases_left fun i h => sqLe_of_le ?_ ?_ (nonnegg_neg_pos.1 ha)
    · dsimp only at h
      exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro _ h))
    · apply Nat.le_add_right
  · dsimp
    rw [add_comm, add_comm (y : ℤ)]
    exact nonneg_add_lem hb ha
  · have : Nonneg ⟨_, _⟩ :=
      nonnegg_neg_pos.2 (sqLe_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
    rw [Nat.cast_add, Nat.cast_add, neg_add] at this
    rwa [add_def]
/-
**Zsqrtd.nonneg_iff_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_iff_zero_le {a : Int√d} : Nonneg a ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonneg_iff_zero_le {a : ℤ√d} : Nonneg a ↔ 0 ≤ a :=
  show _ ↔ Nonneg _ by simp
/-
**Zsqrtd.le_of_le_le** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：le_of_le_le {x y z w : Int} (xz : x <= z) (yw : y <= w) : (⟨x, y⟩ : Int√d)
 <= ⟨z, w⟩
参数：xz : x <= z；yw : y <= w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le.dest_sub`：∀ {a b : ℤ}, a ≤ b → ∃ n, b - a = ↑n
· 使用定理 `trivial`：True
-/
theorem le_of_le_le {x y z w : ℤ} (xz : x ≤ z) (yw : y ≤ w) : (⟨x, y⟩ : ℤ√d) ≤ ⟨z, w⟩ :=
  show Nonneg ⟨z - x, w - y⟩ from
    match z - x, w - y, Int.le.dest_sub xz, Int.le.dest_sub yw with
    | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => trivial

open Int in
/-
**Zsqrtd.nonneg_total** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} (a : ℤ√↑d), a.Nonneg ∨ (-a).Nonneg
参数：a : ℤ√↑d；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Nat.le_total`：∀ (m n : ℕ), m ≤ n ∨ n ≤ m
-/
protected theorem nonneg_total : ∀ a : ℤ√d, Nonneg a ∨ Nonneg (-a)
  | ⟨(x : ℕ), (y : ℕ)⟩ => Or.inl trivial
  | ⟨-[_+1], -[_+1]⟩ => Or.inr trivial
  | ⟨0, -[_+1]⟩ => Or.inr trivial
  | ⟨-[_+1], 0⟩ => Or.inr trivial
  | ⟨(_ + 1 : ℕ), -[_+1]⟩ => Nat.le_total _ _
  | ⟨-[_+1], (_ + 1 : ℕ)⟩ => Nat.le_total _ _

@[deprecated _root_.le_total (since := "2026-02-19")]
/-
**Zsqrtd.le_total** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} (a b : ℤ√↑d), a ≤ b ∨ b ≤ a
参数：a b : ℤ√↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.nonneg_total`：∀ {d : ℕ} (a : ℤ√↑d), a.Nonneg ∨ (-a).Nonneg
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
protected theorem le_total (a b : ℤ√d) : a ≤ b ∨ b ≤ a := by
  have t := (b - a).nonneg_total
  rwa [neg_sub] at t
/-
**Zsqrtd.preorder** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：preorder : Preorder (Int√d) where le_refl a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preorder : Preorder (ℤ√d) where
  le_refl a := show Nonneg (a - a) by simp only [sub_self]; trivial
  le_trans a b c hab hbc := by simpa [sub_add_sub_cancel'] using! hab.add hbc
  lt_iff_le_not_ge a b := by
    have ht : b ≤ a ∨ a ≤ b := by
      have t := (a - b).nonneg_total
      rwa [neg_sub] at t
    exact (and_iff_right_of_imp ht.resolve_left).symm

open Int in
-- TODO add an `Archimedean (ℤ√d)` instance and drop this lemma
/-
**Zsqrtd.le_arch** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：le_arch (a : Int√d) : exists n : Nat, a <= n
参数：a : Int√d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_neg_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a +
 (-a + b) = b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_arch (a : ℤ√d) : ∃ n : ℕ, a ≤ n := by
  obtain ⟨x, y, (h : a ≤ ⟨x, y⟩)⟩ : ∃ x y : ℕ, Nonneg (⟨x, y⟩ + -a) :=
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
  have h : ∀ y, SqLe y d (d * y) 1 := fun y => by
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (y * y) (Nat.le_mul_self d)
  rw [show (x : ℤ) + d * Nat.succ y - x = d * Nat.succ y by simp]
  exact h (y + 1)

@[deprecated _root_.add_le_add_left (since := "2026-02-19")]
/-
**Zsqrtd.add_le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} (a b : ℤ√↑d), a ≤ b → ∀ (c : ℤ√↑d), a + c ≤ b + c
参数：a b : ℤ√↑d；c : ℤ√↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
-/
protected theorem add_le_add_left (a b : ℤ√d) (ab : a ≤ b) (c : ℤ√d) : a + c ≤ b + c :=
  show Nonneg _ by rwa [add_sub_add_right_eq_sub]
/-
**Zsqrtd.nonneg_smul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_smul {a : Int√d} {n : Nat} (ha : Nonneg a) : Nonneg ((n : Int√d) * 
a)
参数：ha : Nonneg a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Zsqrtd.nonneg_cases`：∀ {d : ℕ} {a : ℤ√↑d},   a.Nonneg → ∃ x y, a = { re 
:= ↑x, im := ↑y } ∨ a = { re := ↑x, im := -↑y } ∨ a = { re := -↑x, im := ↑y }
· 使用定理 `Zsqrtd.smul_val`：smul_val (n x y : Int) : (n : Int√d) * ⟨x, y⟩ = ⟨n * x,
 n * y⟩
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.nonnegg_pos_neg`：nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d 
a (-b) ↔ SqLe b c a d
· 使用定理 `Zsqrtd.sqLe_smul`：sqLe_smul {c d x y : Nat} (n : Nat) (xy : SqLe x c y d
) : SqLe (n * x) c (n * y) d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Zsqrtd.nonnegg_neg_pos`：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Z
sqrtd.SqLe a d b c
-/
theorem nonneg_smul {a : ℤ√d} {n : ℕ} (ha : Nonneg a) : Nonneg ((n : ℤ√d) * a) := by
  rw [← Int.cast_natCast n]
  exact
    match a, nonneg_cases ha, ha with
    | _, ⟨x, y, Or.inl rfl⟩, _ => by rw [smul_val]; trivial
    | _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_pos_neg.2 (sqLe_smul n <| nonnegg_pos_neg.1 ha)
    | _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ha => by
      rw [smul_val]; simpa using! nonnegg_neg_pos.2 (sqLe_smul n <| nonnegg_neg_pos.1 ha)
/-
**Zsqrtd.nonneg_muld** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_muld {a : Int√d} (ha : Nonneg a) : Nonneg (sqrtd * a)
参数：ha : Nonneg a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.nonneg_cases`：∀ {d : ℕ} {a : ℤ√↑d},   a.Nonneg → ∃ x y, a = { re 
:= ↑x, im := ↑y } ∨ a = { re := ↑x, im := -↑y } ∨ a = { re := -↑x, im := ↑y }
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zsqrtd.muld_val`：muld_val (x y : Int) : sqrtd (d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.nonnegg_neg_pos`：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Z
sqrtd.SqLe a d b c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Zsqrtd.nonnegg_pos_neg`：nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d 
a (-b) ↔ SqLe b c a d
-/
theorem nonneg_muld {a : ℤ√d} (ha : Nonneg a) : Nonneg (sqrtd * a) :=
  match a, nonneg_cases ha, ha with
  | _, ⟨_, _, Or.inl rfl⟩, _ => trivial
  | _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ha => by
    simp only [muld_val, mul_neg]
    apply nonnegg_neg_pos.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
  | _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ha => by
    simp only [muld_val]
    apply nonnegg_pos_neg.2
    simpa [SqLe, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)
/-
**Zsqrtd.nonneg_mul_lem** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_mul_lem {x y : Nat} {a : Int√d} (ha : Nonneg a) : Nonneg (⟨x, y⟩ * 
a)
参数：ha : Nonneg a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.decompose`：decompose {x y : Int} : (⟨x, y⟩ : Int√d) = x + sqrtd (
d
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Zsqrtd.Nonneg.add`：∀ {d : ℕ} {a b : ℤ√↑d}, a.Nonneg → b.Nonneg → (a + b)
.Nonneg
· 使用定理 `Zsqrtd.nonneg_smul`：nonneg_smul {a : Int√d} {n : Nat} (ha : Nonneg a) : 
Nonneg ((n : Int√d) * a)
· 使用定理 `Zsqrtd.nonneg_muld`：nonneg_muld {a : Int√d} (ha : Nonneg a) : Nonneg (sq
rtd * a)
-/
theorem nonneg_mul_lem {x y : ℕ} {a : ℤ√d} (ha : Nonneg a) : Nonneg (⟨x, y⟩ * a) := by
  have : (⟨x, y⟩ * a : ℤ√d) = (x : ℤ√d) * a + sqrtd * ((y : ℤ√d) * a) := by
    rw [decompose, right_distrib, mul_assoc, Int.cast_natCast, Int.cast_natCast]
  rw [this]
  exact (nonneg_smul ha).add (nonneg_muld <| nonneg_smul ha)
/-
**Zsqrtd.nonneg_mul** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_mul {a b : Int√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a * b)
参数：ha : Nonneg a；hb : Nonneg b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.nonneg_cases`：∀ {d : ℕ} {a : ℤ√↑d},   a.Nonneg → ∃ x y, a = { re 
:= ↑x, im := ↑y } ∨ a = { re := ↑x, im := -↑y } ∨ a = { re := -↑x, im := ↑y }
· 使用定理 `trivial`：True
· 使用定理 `Zsqrtd.nonneg_mul_lem`：nonneg_mul_lem {x y : Nat} {a : Int√d} (ha : Nonn
eg a) : Nonneg (⟨x, y⟩ * a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.nonnegg_pos_neg`：nonnegg_pos_neg {c d} {a b : Nat} : Nonnegg c d 
a (-b) ↔ SqLe b c a d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Zsqrtd.sqLe_mul`：sqLe_mul {d x y z w : Nat} : (SqLe x 1 y d -> SqLe z 1 
w d -> SqLe (x * w + y * z) d (x * z + d * y * w) 1) ∧ (SqLe x 1 y d -> SqLe w d
 z 1 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Zsqrtd.nonnegg_neg_pos`：∀ {c d a b : ℕ}, Zsqrtd.Nonnegg c d (-↑a) ↑b ↔ Z
sqrtd.SqLe a d b c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem nonneg_mul {a b : ℤ√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a * b) :=
  match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | _, _, ⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inl rfl⟩, _, _ => trivial
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, _, hb => nonneg_mul_lem hb
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, _, hb => nonneg_mul_lem hb
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, _ => by
    rw [mul_comm]; exact nonneg_mul_lem ha
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨-x, y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨x * z + d * y * w, -(x * w + y * z)⟩ := by simp [add_comm]]
    exact nonnegg_pos_neg.2 (sqLe_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨-x, y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨-(x * z + d * y * w), x * w + y * z⟩ := by simp [add_comm]]
    exact nonnegg_neg_pos.2 (sqLe_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨x, -y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨-(x * z + d * y * w), x * w + y * z⟩ := by simp [add_comm]]
    exact
        nonnegg_neg_pos.2 (sqLe_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨x, -y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨x * z + d * y * w, -(x * w + y * z)⟩ := by simp [add_comm]]
    exact
        nonnegg_pos_neg.2
          (sqLe_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
/-
**Zsqrtd.mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} (a b : ℤ√↑d), 0 ≤ a → 0 ≤ b → 0 ≤ a * b
参数：a b : ℤ√↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Zsqrtd.nonneg_mul`：nonneg_mul {a b : Int√d} (ha : Nonneg a) (hb : Nonneg
 b) : Nonneg (a * b)
-/
protected theorem mul_nonneg (a b : ℤ√d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
  simp_rw [← nonneg_iff_zero_le]
  exact nonneg_mul
/-
**Zsqrtd.not_sqLe_succ** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：not_sqLe_succ (c d y) (h : 0 < c) : ¬SqLe (y + 1) c 0 d
参数：c d y；h : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem not_sqLe_succ (c d y) (h : 0 < c) : ¬SqLe (y + 1) c 0 d :=
  not_le_of_gt <| mul_pos (mul_pos h <| Nat.succ_pos _) <| Nat.succ_pos _

/-- A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory. -/
/-
**Zsqrtd.Nonsquare** 是 Mathlib 中的一个归纳类型，位于命名空间 `Zsqrtd`。
形式化陈述：ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory.
-/
class Nonsquare (x : ℕ) : Prop where
  ns (x) : ∀ n : ℕ, x ≠ n * n

variable [dnsq : Nonsquare d]
/-
**Zsqrtd.d_pos** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：d_pos : 0 < d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Zsqrtd.Nonsquare.ns`：∀ (x : ℕ) [self : Zsqrtd.Nonsquare x] (n : ℕ), x ≠ 
n * n
-/
theorem d_pos : 0 < d :=
  lt_of_le_of_ne (Nat.zero_le _) <| Ne.symm <| Nonsquare.ns d 0
/-
**Zsqrtd.divides_sq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0
参数：h : x * x = d * y * y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Nat.eq_zero_of_gcd_eq_zero_left`：∀ {m n : ℕ}, m.gcd n = 0 → m = 0
· 使用定理 `Nat.eq_zero_of_gcd_eq_zero_right`：∀ {m n : ℕ}, m.gcd n = 0 → n = 0
· 使用定理 `Nat.exists_coprime`：∀ (m n : ℕ), ∃ m' n', m'.Coprime n' ∧ m = m' * m.gcd
 n ∧ n = n' * m.gcd n
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `Nat.Coprime.mul_left`：∀ {m k n : ℕ}, m.Coprime k → n.Coprime k → (m * n)
.Coprime k
· 使用定理 `Zsqrtd.Nonsquare.ns`：∀ (x : ℕ) [self : Zsqrtd.Nonsquare x] (n : ℕ), x ≠ 
n * n
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
  let g := x.gcd y
  Or.elim g.eq_zero_or_pos
    (fun H => ⟨Nat.eq_zero_of_gcd_eq_zero_left H, Nat.eq_zero_of_gcd_eq_zero_right H⟩) fun gpos =>
    False.elim <| by
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime _ _
      rw [hx, hy] at h
      have : m * m = d * (n * n) := by
        refine mul_left_cancel₀ (mul_pos gpos gpos).ne' ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have co2 :=
        let co1 := co.mul_right co
        co1.mul_left co1
      exact
        Nonsquare.ns d m
          (Nat.dvd_antisymm (by rw [this]; apply dvd_mul_right) <|
            co2.dvd_of_dvd_mul_right <| by simp [this])
/-
**Zsqrtd.divides_sq_eq_zero_z** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：divides_sq_eq_zero_z {x y : Int} (h : x * x = d * y * y) : x = 0 ∧ y = 0
参数：h : x * x = d * y * y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.divides_sq_eq_zero`：divides_sq_eq_zero {x y} (h : x * x = d * y *
 y) : x = 0 ∧ y = 0
· 使用定理 `Int.ofNat.inj`：∀ {a a_1 : ℕ}, Int.ofNat a = Int.ofNat a_1 → a = a_1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Int.natAbs_mul_self`：∀ {a : ℤ}, ↑(a.natAbs * a.natAbs) = a * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natAbs_eq_zero`：∀ {a : ℤ}, a.natAbs = 0 ↔ a = 0
-/
theorem divides_sq_eq_zero_z {x y : ℤ} (h : x * x = d * y * y) : x = 0 ∧ y = 0 := by
  rw [mul_assoc, ← Int.natAbs_mul_self, ← Int.natAbs_mul_self, ← Int.natCast_mul, ← mul_assoc] at h
  exact
    let ⟨h1, h2⟩ := divides_sq_eq_zero (Int.ofNat.inj h)
    ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2⟩
/-
**Zsqrtd.not_divides_sq** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：not_divides_sq (x y) : (x + 1) * (x + 1) != d * (y + 1) * (y + 1)
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Zsqrtd.divides_sq_eq_zero`：divides_sq_eq_zero {x y} (h : x * x = d * y *
 y) : x = 0 ∧ y = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem not_divides_sq (x y) : (x + 1) * (x + 1) ≠ d * (y + 1) * (y + 1) := fun e => by
  have t := (divides_sq_eq_zero e).left
  contradiction

open Int in
/-
**Zsqrtd.nonneg_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：nonneg_antisymm : forall {a : Int√d}, Nonneg a -> Nonneg (-a) -> a = 0 | ⟨
0, 0⟩, _, _ => rfl | ⟨-[_+1], -[_+1]⟩, xy, _ => False.elim xy | ⟨(_ + 1 : Nat), 
(_ + 1 : Nat)⟩, _, yx => False.elim yx | ⟨-[_+1], 0⟩, xy, _ => absurd xy (not_sq
Le_succ _ _ _ (by decide)) | ⟨(_ + 1 : Nat), 0⟩, _, yx => absurd yx (not_sqLe_su
cc _ _ _ (by decide)) | ⟨0, -[_+1]⟩, xy, _ => absurd xy (not_sqLe_succ _ _ _ d_p
os) | ⟨0, (_ + 1 : Nat)⟩, _, yx => absurd yx (not_sqLe_succ _ _ _ d_pos) | ⟨(x +
 1 : Nat), -[y+1]⟩, (xy : 
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.not_sqLe_succ`：not_sqLe_succ (c d y) (h : 0 < c) : ¬SqLe (y + 1) 
c 0 d
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Zsqrtd.d_pos`：d_pos : 0 < d
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Zsqrtd.not_divides_sq`：not_divides_sq (x y) : (x + 1) * (x + 1) != d * (
y + 1) * (y + 1)
-/
theorem nonneg_antisymm : ∀ {a : ℤ√d}, Nonneg a → Nonneg (-a) → a = 0
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
/-
**Zsqrtd.le_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：le_antisymm {a b : Int√d} (ab : a <= b) (ba : b <= a) : a = b
参数：ab : a <= b；ba : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `Zsqrtd.nonneg_antisymm`：nonneg_antisymm : forall {a : Int√d}, Nonneg a -
> Nonneg (-a) -> a = 0 | ⟨0, 0⟩, _, _ => rfl | ⟨-[_+1], -[_+1]⟩, xy, _ => False.
elim xy | ⟨(…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem le_antisymm {a b : ℤ√d} (ab : a ≤ b) (ba : b ≤ a) : a = b :=
  eq_of_sub_eq_zero <| nonneg_antisymm ba (by rwa [neg_sub])
/-
**Zsqrtd.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
形式化陈述：linearOrder : LinearOrder (Int√d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder : LinearOrder (ℤ√d) :=
  { Zsqrtd.preorder with
    le_antisymm := fun _ _ ab ba => eq_of_sub_eq_zero <| nonneg_antisymm ba (by rwa [neg_sub])
    le_total := fun a b => by
      have t := (b - a).nonneg_total
      rwa [neg_sub] at t
    toDecidableLE := Zsqrtd.decidableLE
    toDecidableEq := inferInstance }
/-
**Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} [dnsq : Zsqrtd.Nonsquare d] {a b : ℤ√↑d}, a * b = 0 → a = 0 ∨ b 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `Zsqrtd.divides_sq_eq_zero_z`：divides_sq_eq_zero_z {x y : Int} (h : x * x
 = d * y * y) : x = 0 ∧ y = 0
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : ℤ√d}, a * b = 0 → a = 0 ∨ b = 0
  | ⟨x, y⟩, ⟨z, w⟩, h => by
    injection h with h1 h2
    have h1 : x * z = -(d * y * w) := eq_neg_of_add_eq_zero_left h1
    have h2 : x * w = -(y * z) := eq_neg_of_add_eq_zero_left h2
    have fin : x * x = d * y * y → (⟨x, y⟩ : ℤ√d) = 0 := fun e =>
      match x, y, divides_sq_eq_zero_z e with
      | _, _, ⟨rfl, rfl⟩ => rfl
    exact
      if z0 : z = 0 then
        if w0 : w = 0 then
          Or.inr
            (match z, w, z0, w0 with
            | _, _, rfl, rfl => rfl)
        else
          Or.inl <|
            fin <|
              mul_right_cancel₀ w0 <|
                calc
                  x * x * w = -y * (x * z) := by simp [h2, mul_assoc, mul_left_comm]
                  _ = d * y * y * w := by simp [h1, mul_assoc, mul_left_comm]
      else
        Or.inl <|
          fin <|
            mul_right_cancel₀ z0 <|
              calc
                x * x * z = d * -y * (x * w) := by simp [h1, mul_assoc, mul_left_comm]
                _ = d * y * y * z := by simp [h2, mul_assoc, mul_left_comm]
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors (ℤ√d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain (ℤ√d) :=
  NoZeroDivisors.to_isDomain _
/-
**Zsqrtd.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} [dnsq : Zsqrtd.Nonsquare d] (a b : ℤ√↑d), 0 < a → 0 < b → 0 < a 
* b
参数：a b : ℤ√↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Zsqrtd.instNoZeroDivisorsCastInt`：∀ {d : ℕ} [dnsq : Zsqrtd.Nonsquare d],
 NoZeroDivisors (ℤ√↑d)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Zsqrtd.mul_nonneg`：∀ {d : ℕ} (a b : ℤ√↑d), 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
protected theorem mul_pos (a b : ℤ√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := fun ab =>
  Or.elim
    (eq_zero_or_eq_zero_of_mul_eq_zero
      (_root_.le_antisymm ab (Zsqrtd.mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (fun e => ne_of_gt a0 e) fun e => ne_of_gt b0 e
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ZeroLEOneClass (ℤ√d) :=
  { zero_le_one := by trivial }
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid (ℤ√d) :=
  { add_le_add_left := fun a b ab c => show Nonneg _ by rwa [add_sub_add_right_eq_sub] }

@[deprecated _root_.le_of_add_le_add_left (since := "2026-02-19")]
/-
**Zsqrtd.le_of_add_le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} [dnsq : Zsqrtd.Nonsquare d] (a b c : ℤ√↑d), c + a ≤ c + b → a ≤ 
b
参数：a b c : ℤ√↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Zsqrtd.instIsOrderedAddMonoidCastInt`：∀ {d : ℕ}, IsOrderedAddMonoid (ℤ√↑
d)
-/
protected theorem le_of_add_le_add_left (a b c : ℤ√d) (h : c + a ≤ c + b) : a ≤ b := by
  exact _root_.le_of_add_le_add_left h

@[deprecated _root_.add_lt_add_left (since := "2026-02-19")]
/-
**Zsqrtd.add_lt_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：∀ {d : ℕ} [dnsq : Zsqrtd.Nonsquare d] (a b : ℤ√↑d), a < b → ∀ (c : ℤ√↑d), 
c + a < c + b
参数：a b : ℤ√↑d；c : ℤ√↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Zsqrtd.instIsOrderedAddMonoidCastInt`：∀ {d : ℕ}, IsOrderedAddMonoid (ℤ√↑
d)
-/
protected theorem add_lt_add_left (a b : ℤ√d) (h : a < b) (c) : c + a < c + b := fun h' =>
  h (_root_.le_of_add_le_add_left h')
/-
**Zsqrtd.** 是 Mathlib 中的一个实例，位于命名空间 `Zsqrtd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictOrderedRing (ℤ√d) :=
  .of_mul_pos Zsqrtd.mul_pos

end

/-
**Zsqrtd.norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_zero {d : Int} (h_nonsquare : forall n : Int, d != n * n) (a : Int
√d) : norm a = 0 ↔ a = 0
参数：h_nonsquare : forall n : Int, d != n * n；a : Int√d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.ext_iff`：∀ {d : ℤ} {x y : ℤ√d}, x = y ↔ x.re = y.re ∧ x.im = y.im
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.divides_sq_eq_zero_z`：divides_sq_eq_zero_z {x y : Int} (h : x * x
 = d * y * y) : x = 0 ∧ y = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_zero_of_mul_self_eq_zero`：eq_zero_of_mul_self_eq_zero (h : a * a = 0)
 : a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Zsqrtd.norm_zero`：norm_zero : norm (0 : Int√d) = 0
-/
theorem norm_eq_zero {d : ℤ} (h_nonsquare : ∀ n : ℤ, d ≠ n * n) (a : ℤ√d) : norm a = 0 ↔ a = 0 := by
  refine ⟨fun ha => Zsqrtd.ext_iff.mpr ?_, fun h => by rw [h, norm_zero]⟩
  dsimp only [norm] at ha
  rw [sub_eq_zero] at ha
  by_cases! h : 0 ≤ d
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le h
    have : Nonsquare d' := ⟨fun n h => h_nonsquare n <| mod_cast h⟩
    exact divides_sq_eq_zero_z ha
  · suffices a.re * a.re = 0 by
      rw [eq_zero_of_mul_self_eq_zero this] at ha ⊢
      simpa only [true_and, or_self_right, re_zero, im_zero, eq_self_iff_true, zero_eq_mul,
        mul_zero, mul_eq_zero, h.ne, false_or, or_self_iff] using ha
    apply _root_.le_antisymm _ (mul_self_nonneg _)
    rw [ha, mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _)

variable {R : Type*}

@[ext]
/-
**Zsqrtd.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：hom_ext [NonAssocRing R] {d : Int} (f g : Int√d ->+* R) (h : f sqrtd = g s
qrtd) : f = g
参数：f g : Int√d ->+* R；h : f sqrtd = g sqrtd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.decompose`：decompose {x y : Int} : (⟨x, y⟩ : Int√d) = x + sqrtd (
d
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_ext [NonAssocRing R] {d : ℤ} (f g : ℤ√d →+* R) (h : f sqrtd = g sqrtd) : f = g := by
  ext ⟨re_x, im_x⟩
  simp [decompose, h]

variable [CommRing R]

/-- The unique `RingHom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` with the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` in `R`. -/
@[simps]
/-
**Zsqrtd.lift** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：lift {d : Int} : { r : R // r * r = ↑d } ≃ (Int√d ->+* R) where toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique `RingHom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` wit
h the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` i
n `R`.
-/
def lift {d : ℤ} : { r : R // r * r = ↑d } ≃ (ℤ√d →+* R) where
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

/-- `lift r` is injective if `d` is non-square, and R has characteristic zero (that is, the map from
`ℤ` into `R` is injective). -/
/-
**Zsqrtd.lift_injective** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：lift_injective [CharZero R] {d : Int} (r : { r : R // r * r = ↑d }) (hd : 
forall n : Int, d != n * n) : Function.Injective (lift r)
参数：r : { r : R // r * r = ↑d }；hd : forall n : Int, d != n * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm_eq_mul_conj`：norm_eq_mul_conj (n : Int√d) : (norm n : Int√d)
 = n * star n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Zsqrtd.norm_eq_zero`：norm_eq_zero {d : Int} (h_nonsquare : forall n : In
t, d != n * n) (a : Int√d) : norm a = 0 ↔ a = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zsqrtd.lift_apply_apply`：∀ {R : Type u_1} [inst : CommRing R] {d : ℤ} (r
 : { r // r * r = ↑d }) (a : ℤ√d), (Zsqrtd.lift r) a = ↑a.re + ↑a.im * ↑r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Zsqrtd.re_intCast`：re_intCast (n : Int) : (n : Int√d).re = n
· 使用定理 `Zsqrtd.im_intCast`：im_intCast (n : Int) : (n : Int√d).im = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
`lift r` is injective if `d` is non-square, and R has characteristic zero (that 
is, the map from
`ℤ` into `R` is injective).
-/
theorem lift_injective [CharZero R] {d : ℤ} (r : { r : R // r * r = ↑d })
    (hd : ∀ n : ℤ, d ≠ n * n) : Function.Injective (lift r) :=
  (injective_iff_map_eq_zero (lift r)).mpr fun a ha => by
    have h_inj : Function.Injective ((↑) : ℤ → R) := Int.cast_injective
    suffices lift r a.norm = 0 by
      simp only [re_intCast, add_zero, lift_apply_apply, im_intCast, Int.cast_zero,
        zero_mul] at this
      rwa [← Int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this
    rw [norm_eq_mul_conj, map_mul, ha, zero_mul]

/-- An element of `ℤ√d` has norm equal to `1` if and only if it is contained in the submonoid
of unitary elements. -/
/-
**Zsqrtd.norm_eq_one_iff_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：norm_eq_one_iff_mem_unitary {d : Int} {a : Int√d} : a.norm = 1 ↔ a in unit
ary (Int√d)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.mem_iff_self_mul_star`：mem_iff_self_mul_star {U : R} : U in unit
ary R ↔ U * star U = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zsqrtd.norm_eq_mul_conj`：norm_eq_mul_conj (n : Int√d) : (norm n : Int√d)
 = n * star n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Zsqrtd.instCharZero`：∀ {d : ℤ}, CharZero (ℤ√d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element of `ℤ√d` has norm equal to `1` if and only if it is contained in the 
submonoid
of unitary elements.
-/
theorem norm_eq_one_iff_mem_unitary {d : ℤ} {a : ℤ√d} : a.norm = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [Unitary.mem_iff_self_mul_star, ← norm_eq_mul_conj]
  norm_cast

/-- The kernel of the norm map on `ℤ√d` equals the submonoid of unitary elements. -/
/-
**Zsqrtd.mker_norm_eq_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：mker_norm_eq_unitary {d : Int} : MonoidHom.mker (@normMonoidHom d) = unita
ry (Int√d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `Zsqrtd.norm_eq_one_iff_mem_unitary`：norm_eq_one_iff_mem_unitary {d : Int
} {a : Int√d} : a.norm = 1 ↔ a in unitary (Int√d)

--- 原说明 ---
The kernel of the norm map on `ℤ√d` equals the submonoid of unitary elements.
-/
theorem mker_norm_eq_unitary {d : ℤ} : MonoidHom.mker (@normMonoidHom d) = unitary (ℤ√d) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

end Zsqrtd

