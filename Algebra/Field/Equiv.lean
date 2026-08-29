/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Equiv

/-!
# If a semiring is a field, any isomorphic semiring is also a field.

This is in a separate file to avoid needing to import `Field` in `Mathlib/Algebra/Ring/Equiv.lean`
-/

public section

variable {A B F : Type*} [Semiring A] [Semiring B]

/--
theorem `IsLocalHom.isField` / 定理 `IsLocalHom.isField`

English:
theorem IsLocalHom.isField
  statement: [FunLike F A B] [MonoidWithZeroHomClass F A B] {f : F}
  proof: have : Nontrivial B := ⟨hB.1⟩; (domain_nontrivial f (map_zero f) (map_one f)).1
mul_comm x y := inj by rw [map_mul, map_mul, hB.mul_comm]
  mul_inv_cancel h :=
    have ⟨a', he⟩ := hB.mul_inv_cancel ((inj.ne h).trans_eq <| map_zero f)
    let _ := hB.toSemifield
    (IsUnit.of_mul_eq_one _ he).of_ma

中文:
定理 是Local态射.isField
  结论: [函数状 F A B] [带零幺半群态射类 F A B] {f : F}
  证明: have : Nontrivial B := ⟨hB.1⟩; (domain_nontrivial f (map_zero f) (map_one f)).1
mul_comm x y := inj by rw [map_mul, map_mul, hB.mul_comm]
  mul_inv_cancel h :=
    have ⟨a', he⟩ := hB.mul_inv_cancel ((inj.ne h).trans_eq <| map_zero f)
    let _ := hB.toSemifield
    (IsUnit.of_mul_eq_one _ he).of_ma
-/
protected theorem IsLocalHom.isField [FunLike F A B] [MonoidWithZeroHomClass F A B] {f : F}
    [IsLocalHom f] (inj : Function.Injective f) (hB : IsField B) : IsField A where
  exists_pair_ne := have : Nontrivial B := ⟨hB.1⟩; (domain_nontrivial f (map_zero f) (map_one f)).1
mul_comm x y := inj by rw [map_mul, map_mul, hB.mul_comm]
  mul_inv_cancel h :=
    have ⟨a', he⟩ := hB.mul_inv_cancel ((inj.ne h).trans_eq <| map_zero f)
    let _ := hB.toSemifield
    (IsUnit.of_mul_eq_one _ he).of_map.exists_right_inv

/--
theorem `MulEquiv.isField` / 定理 `MulEquiv.isField`

English:
theorem MulEquiv.isField
  given: (hB : IsField B) (e : A ≃* B)
  statement: IsField A
  proof: IsLocalHom.isField e.injective hB

中文:
定理 乘法等价.isField
  条件: (hB : 是域 B) (e : A ≃* B)
  结论: 是域 A
  证明: IsLocalHom.isField e.injective hB
-/
protected theorem MulEquiv.isField (hB : IsField B) (e : A ≃* B) : IsField A :=
  IsLocalHom.isField e.injective hB

/--
theorem `MulEquiv.isField_congr` / 定理 `MulEquiv.isField_congr`

English:
theorem MulEquiv.isField_congr
  given: (e : A ≃* B)
  statement: IsField A ↔ IsField B
  proof: ⟨e.symm.isField, e.isField⟩

中文:
定理 乘法等价.isField_congr
  条件: (e : A ≃* B)
  结论: 是域 A ↔ 是域 B
  证明: ⟨e.symm.isField, e.isField⟩
-/
protected theorem MulEquiv.isField_congr (e : A ≃* B) : IsField A ↔ IsField B :=
  ⟨e.symm.isField, e.isField⟩
