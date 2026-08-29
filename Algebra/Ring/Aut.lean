/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Equiv

/-!
# Ring automorphisms

This file defines the automorphism group structure on `RingAut R := RingEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

ring aut
-/

@[expose] public section

variable (R : Type*) [Mul R] [Add R]

/--
Definition of `RingAut` / `RingAut` 的定义

English:
abbreviation RingAut
  body: RingEquiv R R

中文:
缩写 RingAut
  定义体: RingEquiv R R

Depends on / 依赖: RingEquiv
-/
abbrev RingAut := RingEquiv R R

namespace RingAut

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (RingAut R)
  body: RingEquiv.trans h g
  one := RingEquiv.refl R
  inv := RingEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := RingEquiv.self_trans_symm

中文:
实例 :
  签名: 群 (RingAut R)
  定义体: RingEquiv.trans h g
  one := RingEquiv.refl R
  inv := RingEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := RingEquiv.self_trans_symm

Depends on / 依赖: RingEquiv, RingEquiv.trans
-/
instance : Group (RingAut R) where
  mul g h := RingEquiv.trans h g
  one := RingEquiv.refl R
  inv := RingEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := RingEquiv.self_trans_symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RingAut R)
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 (RingAut R)
  定义体: ⟨1⟩
-/
instance : Inhabited (RingAut R) :=
  ⟨1⟩

/--
Definition of `toAddAut` / `toAddAut` 的定义

English:
definition toAddAut
  signature: : RingAut R ->* Multiplicative (AddAut R) where
  body: RingEquiv.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toAddAut
  签名: : RingAut R ->* Multiplicative (AddAut R) where
  定义体: RingEquiv.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: RingEquiv, RingEquiv.toAddEquiv, toAddEquiv
-/
def toAddAut : RingAut R ->* Multiplicative (AddAut R) where
  toFun := RingEquiv.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Definition of `toMulAut` / `toMulAut` 的定义

English:
definition toMulAut
  signature: : RingAut R ->* MulAut R where
  body: RingEquiv.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toMulAut
  签名: : RingAut R ->* MulAut R where
  定义体: RingEquiv.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: RingEquiv, RingEquiv.toMulEquiv, toMulEquiv
-/
def toMulAut : RingAut R ->* MulAut R where
  toFun := RingEquiv.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: : RingAut R ->* Equiv.Perm R where
  body: RingEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toPerm
  签名: : RingAut R ->* 等价.置换 R where
  定义体: RingEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: RingEquiv, RingEquiv.toEquiv, toEquiv
-/
def toPerm : RingAut R ->* Equiv.Perm R where
  toFun := RingEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

variable {R}

/--
theorem `one_eq_refl` / 定理 `one_eq_refl`

English:
theorem one_eq_refl
  statement: (1 : R ≃+* R) = RingEquiv.refl R
  proof: rfl

@[simp]

中文:
定理 one_eq_refl
  结论: (1 : R ≃+* R) = 环等价.refl R
  证明: rfl

@[simp]
-/
theorem one_eq_refl : (1 : R ≃+* R) = RingEquiv.refl R := rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : R)
  statement: (1 : R ≃+* R) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : R)
  结论: (1 : R ≃+* R) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : R) : (1 : R ≃+* R) x = x := rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : R ≃+* R) = id
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ⇑(1 : R ≃+* R) = id
  证明: rfl

@[simp]
-/
theorem coe_one : ⇑(1 : R ≃+* R) = id := rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : R ≃+* R) (x : R)
  statement: (f * g) x = f (g x)
  proof: rfl

@[simp]

中文:
定理 mul_apply
  条件: (f g : R ≃+* R) (x : R)
  结论: (f * g) x = f (g x)
  证明: rfl

@[simp]
-/
theorem mul_apply (f g : R ≃+* R) (x : R) : (f * g) x = f (g x) := rfl

@[simp]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: (f : R ≃+* R) (x : R)
  statement: f⁻¹ x = f.symm x
  proof: rfl

@[simp]

中文:
定理 inv_apply
  条件: (f : R ≃+* R) (x : R)
  结论: f⁻¹ x = f.symm x
  证明: rfl

@[simp]
-/
theorem inv_apply (f : R ≃+* R) (x : R) : f⁻¹ x = f.symm x := rfl

@[simp]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : R ≃+* R) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ext
    simp [pow_succ, ih]

中文:
定理 coe_pow
  条件: (f : R ≃+* R) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ext
    simp [pow_succ, ih]

Depends on / 依赖: pow_succ
-/
theorem coe_pow (f : R ≃+* R) (n : Nat) : ⇑(f ^ n) = f^[n] := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ext
    simp [pow_succ, ih]

end RingAut
