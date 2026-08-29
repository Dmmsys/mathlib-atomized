/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Tactic.Abel

/-!
# Associator in a ring

If `R` is a non-associative ring, then `(x * y) * z - x * (y * z)` is called the `associator` of
ring elements `x y z : R`.

The associator vanishes exactly when `R` is associative.

We prove variants of this statement also for the `AddMonoidHom` bundled version of the associator,
as well as the bundled version of `mulLeft₃` and `mulRight₃`, the multiplications `(x * y) * z` and
`x * (y * z)`.
-/

@[expose] public section

variable {R : Type*}

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R]

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (x y z : R)
  body: (x * y) * z - x * (y * z)

中文:
定义 associator
  签名: (x y z : R)
  定义体: (x * y) * z - x * (y * z)
-/
def associator (x y z : R) : R := (x * y) * z - x * (y * z)

/--
theorem `associator_apply` / 定理 `associator_apply`

English:
theorem associator_apply
  given: (x y z : R)
  statement: associator x y z = (x * y) * z - x * (y * z)
  proof: rfl

中文:
定理 associator_apply
  条件: (x y z : R)
  结论: associator x y z = (x * y) * z - x * (y * z)
  证明: rfl
-/
theorem associator_apply (x y z : R) : associator x y z = (x * y) * z - x * (y * z) := rfl

/--
theorem `associator_eq_zero_iff_associative` / 定理 `associator_eq_zero_iff_associative`

English:
theorem associator_eq_zero_iff_associative
  proof: ⟨fun x y z => sub_eq_zero.mp congr_fun₃ h x y z⟩
  mpr h := by ext x y z; simp [associator, Std.Associative.assoc]

中文:
定理 associator_eq_zero_iff_associative
  证明: ⟨fun x y z => sub_eq_zero.mp congr_fun₃ h x y z⟩
  mpr h := by ext x y z; simp [associator, Std.Associative.assoc]

Depends on / 依赖: Associative, Std.Associative
-/
theorem associator_eq_zero_iff_associative :
    associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) => x * y) where
mp h := ⟨fun x y z => sub_eq_zero.mp congr_fun₃ h x y z⟩
  mpr h := by ext x y z; simp [associator, Std.Associative.assoc]

/--
theorem `associator_cocycle` / 定理 `associator_cocycle`

English:
theorem associator_cocycle
  given: (a b c d : R)
  proof: by
  simp only [associator, mul_sub, sub_mul]
  abel1

中文:
定理 associator_cocycle
  条件: (a b c d : R)
  证明: by
  simp only [associator, mul_sub, sub_mul]
  abel1

Depends on / 依赖: associator, mul_sub, sub_mul
-/
theorem associator_cocycle (a b c d : R) :
    a * associator b c d - associator (a * b) c d + associator a (b * c) d - associator a b (c * d)
    + (associator a b c) * d = 0 := by
  simp only [associator, mul_sub, sub_mul]
  abel1

open MulOpposite in
@[simp]
/--
lemma `associator_op` / 引理 `associator_op`

English:
lemma associator_op
  given: (x y z : Rᵐᵒᵖ)
  proof: by
  simp only [associator_apply, ← unop_mul, ← unop_sub, op_unop, neg_sub]

中文:
引理 associator_op
  条件: (x y z : Rᵐᵒᵖ)
  证明: by
  simp only [associator_apply, ← unop_mul, ← unop_sub, op_unop, neg_sub]

Depends on / 依赖: associator_apply, neg_sub, op_unop, unop_mul, unop_sub
-/
lemma associator_op (x y z : Rᵐᵒᵖ) :
    associator x y z = -op (associator (unop z) (unop y) (unop x)) := by
  simp only [associator_apply, ← unop_mul, ← unop_sub, op_unop, neg_sub]

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

@[simp]
/--
theorem `associator_eq_zero` / 定理 `associator_eq_zero`

English:
theorem associator_eq_zero
  statement: associator (R := R) = 0
  proof: associator_eq_zero_iff_associative.mpr inferInstance

中文:
定理 associator_eq_zero
  结论: associator (R := R) = 0
  证明: associator_eq_zero_iff_associative.mpr inferInstance
-/
theorem associator_eq_zero : associator (R := R) = 0 :=
  associator_eq_zero_iff_associative.mpr inferInstance

end NonUnitalRing

namespace AddMonoidHom

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/--
Definition of `mulLeft₃` / `mulLeft₃` 的定义

English:
definition mulLeft₃
  signature: : R ->+ R ->+ R ->+ R where
  body: comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]

中文:
定义 mulLeft₃
  签名: : R ->+ R ->+ R ->+ R where
  定义体: comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]

Depends on / 依赖: mulLeft
-/
def mulLeft₃ : R ->+ R ->+ R ->+ R where
  toFun x := comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]
/--
theorem `mulLeft₃_apply` / 定理 `mulLeft₃_apply`

English:
theorem mulLeft₃_apply
  given: (x y z : R)
  statement: mulLeft₃ x y z = (x * y) * z
  proof: rfl

中文:
定理 mulLeft₃_apply
  条件: (x y z : R)
  结论: mulLeft₃ x y z = (x * y) * z
  证明: rfl
-/
theorem mulLeft₃_apply (x y z : R) : mulLeft₃ x y z = (x * y) * z := rfl

/--
Definition of `mulRight₃` / `mulRight₃` 的定义

English:
definition mulRight₃
  signature: : R ->+ R ->+ R ->+ R where
  body: compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]

中文:
定义 mulRight₃
  签名: : R ->+ R ->+ R ->+ R where
  定义体: compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]

Depends on / 依赖: mulLeft
-/
def mulRight₃ : R ->+ R ->+ R ->+ R where
  toFun x := compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]
/--
theorem `mulRight₃_apply` / 定理 `mulRight₃_apply`

English:
theorem mulRight₃_apply
  given: (x y z : R)
  statement: mulRight₃ x y z = x * (y * z)
  proof: rfl

中文:
定理 mulRight₃_apply
  条件: (x y z : R)
  结论: mulRight₃ x y z = x * (y * z)
  证明: rfl
-/
theorem mulRight₃_apply (x y z : R) : mulRight₃ x y z = x * (y * z) := rfl

/--
theorem `mulLeft₃_eq_mulRight₃_iff_associative` / 定理 `mulLeft₃_eq_mulRight₃_iff_associative`

English:
theorem mulLeft₃_eq_mulRight₃_iff_associative
  proof: ⟨fun x y z => by rw [← mulLeft₃_apply, ← mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]

中文:
定理 mulLeft₃_eq_mulRight₃_iff_associative
  证明: ⟨fun x y z => by rw [← mulLeft₃_apply, ← mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]

Depends on / 依赖: Associative, Std.Associative
-/
theorem mulLeft₃_eq_mulRight₃_iff_associative :
    mulLeft₃ (R := R) = mulRight₃ ↔ Std.Associative (fun (x y : R) => x * y) where
  mp h := ⟨fun x y z => by rw [← mulLeft₃_apply, ← mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R]

/--
theorem `mulLeft₃_eq_mulRight₃` / 定理 `mulLeft₃_eq_mulRight₃`

English:
theorem mulLeft₃_eq_mulRight₃
  statement: mulLeft₃ (R := R) = mulRight₃
  proof: mulLeft₃_eq_mulRight₃_iff_associative.2 inferInstance

中文:
定理 mulLeft₃_eq_mulRight₃
  结论: mulLeft₃ (R := R) = mulRight₃
  证明: mulLeft₃_eq_mulRight₃_iff_associative.2 inferInstance
-/
theorem mulLeft₃_eq_mulRight₃ : mulLeft₃ (R := R) = mulRight₃ :=
  mulLeft₃_eq_mulRight₃_iff_associative.2 inferInstance

end NonUnitalSemiring

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] (a b c : R)

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: : R ->+ R ->+ R ->+ R
  body: mulLeft₃ - mulRight₃

@[simp]

中文:
定义 associator
  签名: : R ->+ R ->+ R ->+ R
  定义体: mulLeft₃ - mulRight₃

@[simp]
-/
def associator : R ->+ R ->+ R ->+ R := mulLeft₃ - mulRight₃

@[simp]
/--
theorem `associator_apply` / 定理 `associator_apply`

English:
theorem associator_apply
  statement: associator a b c = _root_.associator a b c
  proof: rfl

中文:
定理 associator_apply
  结论: associator a b c = _root_.associator a b c
  证明: rfl
-/
theorem associator_apply : associator a b c = _root_.associator a b c := rfl

/--
theorem `associator_eq_zero_iff_associative` / 定理 `associator_eq_zero_iff_associative`

English:
theorem associator_eq_zero_iff_associative
  proof: by
  simp [mulLeft₃_eq_mulRight₃_iff_associative, associator, sub_eq_zero]

中文:
定理 associator_eq_zero_iff_associative
  证明: by
  simp [mulLeft₃_eq_mulRight₃_iff_associative, associator, sub_eq_zero]

Depends on / 依赖: Associative, Std.Associative, associator, sub_eq_zero
-/
theorem associator_eq_zero_iff_associative :
    associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) => x * y) := by
  simp [mulLeft₃_eq_mulRight₃_iff_associative, associator, sub_eq_zero]

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

@[simp]
/--
theorem `associator_eq_zero` / 定理 `associator_eq_zero`

English:
theorem associator_eq_zero
  statement: associator (R := R) = 0
  proof: associator_eq_zero_iff_associative.mpr inferInstance

中文:
定理 associator_eq_zero
  结论: associator (R := R) = 0
  证明: associator_eq_zero_iff_associative.mpr inferInstance
-/
theorem associator_eq_zero : associator (R := R) = 0 :=
  associator_eq_zero_iff_associative.mpr inferInstance

end NonUnitalRing
end AddMonoidHom
