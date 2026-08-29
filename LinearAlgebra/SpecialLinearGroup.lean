/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# The special linear group of a module

If `R` is a commutative ring and `V` is an `R`-module,
we define `SpecialLinearGroup R V` as the subtype of
linear equivalences `V ≃ₗ[R] V` with determinant 1.
When `V` doesn't have a finite basis, the determinant is defined to be 1
and the definition gives `V ≃ₗ[R] V`.
The interest of this definition is that `SpecialLinearGroup R V`
has a group structure. (Starting from linear maps wouldn't have worked.)

The file is constructed parallel to the one defining `Matrix.SpecialLinearGroup`.

We provide `SpecialLinearGroup.toLinearEquiv`: the canonical map
from `SpecialLinearGroup R V` to `V ≃ₗ[R] V`, as a monoid hom.

When `V` is free and finite over `R`, we define
* `SpecialLinearGroup.dualMap`
* `SpecialLinearGroup.baseChange`

We define `Matrix.SpecialLinearGroup.toLin'_equiv`: the multiplicative equivalence
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R (n → R)`
and its variant
`Matrix.SpecialLinearGroup.toLin_equiv`,
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R V`,
associated with a finite basis of `V`.

-/

@[expose] public section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

variable (R V) in
/--
Definition of `SpecialLinearGroup` / `SpecialLinearGroup` 的定义

English:
abbreviation SpecialLinearGroup
  body: { u : V ≃ₗ[R] V // u.det = 1 }

中文:
缩写 SpecialLinearGroup
  定义体: { u : V ≃ₗ[R] V // u.det = 1 }

Depends on / 依赖: u.det
-/
abbrev SpecialLinearGroup := { u : V ≃ₗ[R] V // u.det = 1 }

namespace SpecialLinearGroup

/--
theorem `det_eq_one` / 定理 `det_eq_one`

English:
theorem det_eq_one
  given: (u : SpecialLinearGroup R V)
  proof: by
  simp [← LinearEquiv.coe_det, u.prop]

中文:
定理 det_eq_one
  条件: (u : SpecialLinearGroup R V)
  证明: by
  simp [← LinearEquiv.coe_det, u.prop]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_det, coe_det, u.prop
-/
theorem det_eq_one (u : SpecialLinearGroup R V) :
    LinearMap.det (u : V ->ₗ[R] V) = 1 := by
  simp [← LinearEquiv.coe_det, u.prop]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (SpecialLinearGroup R V) (fun _ => V -> V)
  body: u.val x

中文:
实例 :
  签名: CoeFun (SpecialLinearGroup R V) (fun _ => V -> V)
  定义体: u.val x

Depends on / 依赖: u.val
-/
instance : CoeFun (SpecialLinearGroup R V) (fun _ => V -> V) where
  coe u x := u.val x

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (u v : SpecialLinearGroup R V)
  statement: u = v ↔ forall x : V, u x = v x
  proof: by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]

中文:
定理 ext_iff
  条件: (u v : SpecialLinearGroup R V)
  结论: u = v ↔ 对任意 x : V, u x = v x
  证明: by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]

Depends on / 依赖: LinearEquiv, LinearEquiv.ext_iff, Subtype, Subtype.coe_inj, coe_inj, ext_iff
-/
theorem ext_iff (u v : SpecialLinearGroup R V) : u = v ↔ forall x : V, u x = v x := by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (u v : SpecialLinearGroup R V)
  statement: (forall x, u x = v x) -> u = v
  proof: (SpecialLinearGroup.ext_iff u v).mpr

中文:
定理 ext
  条件: (u v : SpecialLinearGroup R V)
  结论: (对任意 x, u x = v x) -> u = v
  证明: (SpecialLinearGroup.ext_iff u v).mpr

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.ext_iff, ext_iff
-/
theorem ext (u v : SpecialLinearGroup R V) : (forall x, u x = v x) -> u = v :=
  (SpecialLinearGroup.ext_iff u v).mpr

section rankOne

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `subsingleton_of_finrank_eq_one` / 定理 `subsingleton_of_finrank_eq_one`

English:
theorem subsingleton_of_finrank_eq_one
  given: [Module.Free R V] (d1 : Module.finrank R V = 1)
  proof: by
    nontriviality R
    ext x
    by_cases hx : x = 0
    · simp [hx]
    suffices forall (u : SpecialLinearGroup R V), (u : V ->ₗ[R] V) = LinearMap.id by
      simp only [LinearMap.ext_iff, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
      simp [this u, this v]
    intro u
    ext x
    set c := (LinearEquiv.smul_id_of_finrank_eq_one d1).symm u with hc
    rw [LinearEquiv.eq_symm_apply] at hc
    suffices c = 1 by
      simp [← hc, LinearEquiv.smul_id_of_finrank_eq_one, this]
    have hu := u.prop
    simpa [← Units.val_inj, LinearEquiv.coe_det, ← hc,
      LinearEquiv.smul_id_of_finrank_eq_one, d1] using hu

中文:
定理 subsingleton_of_finrank_eq_one
  条件: [模.自由 R V] (d1 : 模.finrank R V = 1)
  证明: by
    nontriviality R
    ext x
    by_cases hx : x = 0
    · simp [hx]
    suffices forall (u : SpecialLinearGroup R V), (u : V ->ₗ[R] V) = LinearMap.id by
      simp only [LinearMap.ext_iff, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
      simp [this u, this v]
    intro u
    ext x
    set c := (LinearEquiv.smul_id_of_finrank_eq_one d1).symm u with hc
    rw [LinearEquiv.eq_symm_apply] at hc
    suffices c = 1 by
      simp [← hc, LinearEquiv.smul_id_of_finrank_eq_one, this]
    have hu := u.prop
    simpa [← Units.val_inj, LinearEquiv.coe_det, ← hc,
      LinearEquiv.smul_id_of_finrank_eq_one, d1] using hu

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_det, LinearEquiv.eq_symm_apply, LinearEquiv.smul_id_of_finrank_eq_one, LinearMap, LinearMap.ext_iff, LinearMap.id, LinearMap.id_coe, SpecialLinearGroup, Units.val_inj, coe_coe, coe_det, eq_symm_apply, ext_iff, id_coe, id_eq, nontriviality, smul_id_of_finrank_eq_one, u.prop
-/
theorem subsingleton_of_finrank_eq_one [Module.Free R V] (d1 : Module.finrank R V = 1) :
    Subsingleton (SpecialLinearGroup R V) where
  allEq u v := by
    nontriviality R
    ext x
    by_cases hx : x = 0
    · simp [hx]
    suffices forall (u : SpecialLinearGroup R V), (u : V ->ₗ[R] V) = LinearMap.id by
      simp only [LinearMap.ext_iff, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
      simp [this u, this v]
    intro u
    ext x
    set c := (LinearEquiv.smul_id_of_finrank_eq_one d1).symm u with hc
    rw [LinearEquiv.eq_symm_apply] at hc
    suffices c = 1 by
      simp [← hc, LinearEquiv.smul_id_of_finrank_eq_one, this]
    have hu := u.prop
    simpa [← Units.val_inj, LinearEquiv.coe_det, ← hc,
      LinearEquiv.smul_id_of_finrank_eq_one, d1] using hu

end rankOne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (SpecialLinearGroup R V)
  body: ⟨fun A => ⟨A⁻¹, by simp [A.prop]⟩⟩

中文:
实例 :
  签名: 取逆 (SpecialLinearGroup R V)
  定义体: ⟨fun A => ⟨A⁻¹, by simp [A.prop]⟩⟩

Depends on / 依赖: A.prop
-/
instance : Inv (SpecialLinearGroup R V) :=
  ⟨fun A => ⟨A⁻¹, by simp [A.prop]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (SpecialLinearGroup R V)
  body: ⟨fun A B => ⟨A * B, by simp [A.prop, B.prop]⟩⟩

中文:
实例 :
  签名: 乘法 (SpecialLinearGroup R V)
  定义体: ⟨fun A B => ⟨A * B, by simp [A.prop, B.prop]⟩⟩

Depends on / 依赖: A.prop, B.prop
-/
instance : Mul (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A * B, by simp [A.prop, B.prop]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (SpecialLinearGroup R V)
  body: ⟨fun A B => ⟨A / B, by simp [A.prop, B.prop]⟩⟩

中文:
实例 :
  签名: 除法 (SpecialLinearGroup R V)
  定义体: ⟨fun A B => ⟨A / B, by simp [A.prop, B.prop]⟩⟩

Depends on / 依赖: A.prop, B.prop
-/
instance : Div (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A / B, by simp [A.prop, B.prop]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (SpecialLinearGroup R V)
  body: ⟨⟨1, by simp⟩⟩

中文:
实例 :
  签名: 幺 (SpecialLinearGroup R V)
  定义体: ⟨⟨1, by simp⟩⟩
-/
instance : One (SpecialLinearGroup R V) :=
  ⟨⟨1, by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (SpecialLinearGroup R V) Nat
  body: ⟨x ^ n, by simp [x.prop]⟩

中文:
实例 :
  签名: 幂 (SpecialLinearGroup R V) 自然数
  定义体: ⟨x ^ n, by simp [x.prop]⟩

Depends on / 依赖: x.prop
-/
instance : Pow (SpecialLinearGroup R V) Nat where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (SpecialLinearGroup R V) Int
  body: ⟨x ^ n, by simp [x.prop]⟩

中文:
实例 :
  签名: 幂 (SpecialLinearGroup R V) 整数
  定义体: ⟨x ^ n, by simp [x.prop]⟩

Depends on / 依赖: x.prop
-/
instance : Pow (SpecialLinearGroup R V) Int where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SpecialLinearGroup R V)
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 (SpecialLinearGroup R V)
  定义体: ⟨1⟩
-/
instance : Inhabited (SpecialLinearGroup R V) :=
  ⟨1⟩

/--
Definition of `dualMap` / `dualMap` 的定义

English:
definition dualMap
  body: ⟨LinearEquiv.dualMap (A : V ≃ₗ[R] V), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
      LinearEquiv.dualMap, LinearMap.det_dualMap]
    simp [← LinearEquiv.coe_det, A.prop]⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.dualMap

中文:
定义 dualMap
  定义体: ⟨LinearEquiv.dualMap (A : V ≃ₗ[R] V), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
      LinearEquiv.dualMap, LinearMap.det_dualMap]
    simp [← LinearEquiv.coe_det, A.prop]⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.dualMap

Depends on / 依赖: A.prop, LinearEquiv, LinearEquiv.coe_det, LinearEquiv.dualMap, LinearMap, LinearMap.det_dualMap, Units.val_inj, Units.val_one, coe_det, det_dualMap, dualMap, val_inj, val_one
-/
def dualMap
    [Module.Free R V] [Module.Finite R V] (A : SpecialLinearGroup R V) :
    SpecialLinearGroup R (Module.Dual R V) :=
  ⟨LinearEquiv.dualMap (A : V ≃ₗ[R] V), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
      LinearEquiv.dualMap, LinearMap.det_dualMap]
    simp [← LinearEquiv.coe_det, A.prop]⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.dualMap

section CoeLemmas

variable (A B : SpecialLinearGroup R V)

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (A : V ≃ₗ[R] V) (h : A.det = 1)
  statement: ↑(⟨A, h⟩ : SpecialLinearGroup R V) = A
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (A : V ≃ₗ[R] V) (h : A.det = 1)
  结论: ↑(⟨A, h⟩ : SpecialLinearGroup R V) = A
  证明: rfl

@[simp]
-/
theorem coe_mk (A : V ≃ₗ[R] V) (h : A.det = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup R V) = A :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: (A * B : SpecialLinearGroup R V) = (A * B : V ≃ₗ[R] V)
  proof: rfl

@[simp]

中文:
定理 coe_mul
  结论: (A * B : SpecialLinearGroup R V) = (A * B : V ≃ₗ[R] V)
  证明: rfl

@[simp]
-/
theorem coe_mul : (A * B : SpecialLinearGroup R V) = (A * B : V ≃ₗ[R] V) :=
  rfl

@[simp]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  statement: (A / B : SpecialLinearGroup R V) = (A / B : V ≃ₗ[R] V)
  proof: rfl

@[simp]

中文:
定理 coe_div
  结论: (A / B : SpecialLinearGroup R V) = (A / B : V ≃ₗ[R] V)
  证明: rfl

@[simp]
-/
theorem coe_div : (A / B : SpecialLinearGroup R V) = (A / B : V ≃ₗ[R] V) :=
  rfl

@[simp]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  statement: (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V)
  proof: rfl

@[simp]

中文:
定理 coe_inv
  结论: (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V)
  证明: rfl

@[simp]
-/
theorem coe_inv : (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V) :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V)
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V)
  证明: rfl

@[simp]
-/
theorem coe_one : (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V) :=
  rfl

@[simp]
/--
theorem `det_coe` / 定理 `det_coe`

English:
theorem det_coe
  statement: LinearEquiv.det (A : V ≃ₗ[R] V) = 1
  proof: A.prop

@[simp]

中文:
定理 det_coe
  结论: 线性等价.det (A : V ≃ₗ[R] V) = 1
  证明: A.prop

@[simp]

Depends on / 依赖: A.prop
-/
theorem det_coe : LinearEquiv.det (A : V ≃ₗ[R] V) = 1 :=
  A.prop

@[simp]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (m : Nat)
  statement: (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m
  proof: rfl

@[simp]

中文:
定理 coe_pow
  条件: (m : 自然数)
  结论: (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m
  证明: rfl

@[simp]
-/
theorem coe_pow (m : Nat) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (m : Int)
  statement: (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m
  proof: rfl

@[simp]

中文:
定理 coe_zpow
  条件: (m : 整数)
  结论: (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m
  证明: rfl

@[simp]
-/
theorem coe_zpow (m : Int) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
/--
theorem `coe_dualMap` / 定理 `coe_dualMap`

English:
theorem coe_dualMap
  proof: rfl

中文:
定理 coe_dualMap
  证明: rfl
-/
theorem coe_dualMap
    [Module.Free R V] [Module.Finite R V] :
    Aᵀ = (A : V ≃ₗ[R] V).dualMap :=
  rfl

end CoeLemmas

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (SpecialLinearGroup R V)
  body: fast_instance%
  Function.Injective.group _ Subtype.coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

中文:
实例 :
  签名: 群 (SpecialLinearGroup R V)
  定义体: fast_instance%
  Function.Injective.group _ Subtype.coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

Depends on / 依赖: fast_instance
-/
instance : Group (SpecialLinearGroup R V) := fast_instance%
  Function.Injective.group _ Subtype.coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: : SpecialLinearGroup R V ->* V ≃ₗ[R] V where
  body: A.val
  map_one' := coe_one
  map_mul' := coe_mul

中文:
定义 toLinearEquiv
  签名: : SpecialLinearGroup R V ->* V ≃ₗ[R] V where
  定义体: A.val
  map_one' := coe_one
  map_mul' := coe_mul

Depends on / 依赖: A.val
-/
def toLinearEquiv : SpecialLinearGroup R V ->* V ≃ₗ[R] V where
  toFun A := A.val
  map_one' := coe_one
  map_mul' := coe_mul

/--
lemma `toLinearEquiv_apply` / 引理 `toLinearEquiv_apply`

English:
lemma toLinearEquiv_apply
  given: (A : SpecialLinearGroup R V) (v : V)
  proof: rfl

@[simp]

中文:
引理 toLinearEquiv_apply
  条件: (A : SpecialLinearGroup R V) (v : V)
  证明: rfl

@[simp]
-/
@[simp] lemma toLinearEquiv_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv v = A v :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_to_linearMap` / 定理 `toLinearEquiv_to_linearMap`

English:
theorem toLinearEquiv_to_linearMap
  given: (A : SpecialLinearGroup R V)
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_to_linearMap
  条件: (A : SpecialLinearGroup R V)
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_to_linearMap (A : SpecialLinearGroup R V) :
    (SpecialLinearGroup.toLinearEquiv A) = (A : V ->ₗ[R] V) :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_symm_apply` / 定理 `toLinearEquiv_symm_apply`

English:
theorem toLinearEquiv_symm_apply
  given: (A : SpecialLinearGroup R V) (v : V)
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_symm_apply
  条件: (A : SpecialLinearGroup R V) (v : V)
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_symm_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv.symm v = A⁻¹ v :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_symm_to_linearMap` / 定理 `toLinearEquiv_symm_to_linearMap`

English:
theorem toLinearEquiv_symm_to_linearMap
  given: (A : SpecialLinearGroup R V)
  proof: rfl

中文:
定理 toLinearEquiv_symm_to_linearMap
  条件: (A : SpecialLinearGroup R V)
  证明: rfl
-/
theorem toLinearEquiv_symm_to_linearMap (A : SpecialLinearGroup R V) :
    A.toLinearEquiv.symm = ((A⁻¹ : SpecialLinearGroup R V) : V ->ₗ[R] V) :=
  rfl

/--
theorem `toLinearEquiv_injective` / 定理 `toLinearEquiv_injective`

English:
theorem toLinearEquiv_injective
  proof: Subtype.val_injective

中文:
定理 toLinearEquiv_injective
  证明: Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : SpecialLinearGroup R V ->* V ≃ₗ[R] V) :=
  Subtype.val_injective

/--
Definition of `toGeneralLinearGroup` / `toGeneralLinearGroup` 的定义

English:
definition toGeneralLinearGroup
  signature: : SpecialLinearGroup R V ->* LinearMap.GeneralLinearGroup R V
  body: (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.toMonoidHom.comp toLinearEquiv

中文:
定义 toGeneralLinearGroup
  签名: : SpecialLinearGroup R V ->* 线性映射.GeneralLinearGroup R V
  定义体: (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.toMonoidHom.comp toLinearEquiv

Depends on / 依赖: GeneralLinearGroup, LinearMap, LinearMap.GeneralLinearGroup.generalLinearEquiv, generalLinearEquiv, symm.toMonoidHom.comp, toLinearEquiv, toMonoidHom
-/
def toGeneralLinearGroup : SpecialLinearGroup R V ->* LinearMap.GeneralLinearGroup R V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.toMonoidHom.comp toLinearEquiv

/--
lemma `toGeneralLinearGroup_toLinearEquiv_apply` / 引理 `toGeneralLinearGroup_toLinearEquiv_apply`

English:
lemma toGeneralLinearGroup_toLinearEquiv_apply
  given: (u : SpecialLinearGroup R V)
  proof: rfl

中文:
引理 toGeneralLinearGroup_toLinearEquiv_apply
  条件: (u : SpecialLinearGroup R V)
  证明: rfl
-/
lemma toGeneralLinearGroup_toLinearEquiv_apply (u : SpecialLinearGroup R V) :
    u.toGeneralLinearGroup.toLinearEquiv = u.toLinearEquiv := rfl

/--
lemma `coe_toGeneralLinearGroup_apply` / 引理 `coe_toGeneralLinearGroup_apply`

English:
lemma coe_toGeneralLinearGroup_apply
  given: (u : SpecialLinearGroup R V)
  proof: rfl

中文:
引理 coe_toGeneralLinearGroup_apply
  条件: (u : SpecialLinearGroup R V)
  证明: rfl
-/
lemma coe_toGeneralLinearGroup_apply (u : SpecialLinearGroup R V) :
    u.toGeneralLinearGroup.val = u.toLinearEquiv := rfl

/--
lemma `toGeneralLinearGroup_injective` / 引理 `toGeneralLinearGroup_injective`

English:
lemma toGeneralLinearGroup_injective
  proof: by
  simp [toGeneralLinearGroup, toLinearEquiv_injective]

中文:
引理 toGeneralLinearGroup_injective
  证明: by
  simp [toGeneralLinearGroup, toLinearEquiv_injective]

Depends on / 依赖: Integrable, MeasurableSet, MeasureTheory, MeasureTheory.Integrable.restrict, VectorMeasure, VectorMeasure.Integrable, restrict, restrict_not_measurable, toGeneralLinearGroup, toLinearEquiv_injective, transpose_restrict, variation_restrict
-/
lemma toGeneralLinearGroup_injective :
    Function.Injective ⇑(toGeneralLinearGroup (R := R) (V := V)) := by
  simp [toGeneralLinearGroup, toLinearEquiv_injective]

/--
lemma `mem_range_toGeneralLinearGroup_iff` / 引理 `mem_range_toGeneralLinearGroup_iff`

English:
lemma mem_range_toGeneralLinearGroup_iff
  given: {u : LinearMap.GeneralLinearGroup R V}
  proof: by
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]; rw [toGeneralLinearGroup_toLinearEquiv_apply]
    exact v.prop
  · intro hu
    refine ⟨⟨u.toLinearEquiv, hu⟩, rfl⟩

中文:
引理 mem_range_toGeneralLinearGroup_iff
  条件: {u : 线性映射.GeneralLinearGroup R V}
  证明: by
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]; rw [toGeneralLinearGroup_toLinearEquiv_apply]
    exact v.prop
  · intro hu
    refine ⟨⟨u.toLinearEquiv, hu⟩, rfl⟩
-/
lemma mem_range_toGeneralLinearGroup_iff {u : LinearMap.GeneralLinearGroup R V} :
    u in Set.range ⇑(toGeneralLinearGroup (R := R) (V := V)) ↔
      u.toLinearEquiv.det = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]; rw [toGeneralLinearGroup_toLinearEquiv_apply]
    exact v.prop
  · intro hu
    refine ⟨⟨u.toLinearEquiv, hu⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction (SpecialLinearGroup R V) V
  body: DistribMulAction.compHom _ (SpecialLinearGroup.toLinearEquiv)

中文:
实例 :
  签名: 分配乘法作用 (SpecialLinearGroup R V) V
  定义体: DistribMulAction.compHom _ (SpecialLinearGroup.toLinearEquiv)

Depends on / 依赖: DistribMulAction, DistribMulAction.compHom, SpecialLinearGroup, SpecialLinearGroup.toLinearEquiv, compHom, toLinearEquiv
-/
instance : DistribMulAction (SpecialLinearGroup R V) V :=
  DistribMulAction.compHom _ (SpecialLinearGroup.toLinearEquiv)

/--
theorem `_root_.SpecialLinearGroup.smul_def` / 定理 `_root_.SpecialLinearGroup.smul_def`

English:
theorem _root_.SpecialLinearGroup.smul_def
  given: (g : SpecialLinearGroup R V) (v : V)
  proof: rfl

中文:
定理 _root_.SpecialLinearGroup.smul_def
  条件: (g : SpecialLinearGroup R V) (v : V)
  证明: rfl
-/
theorem _root_.SpecialLinearGroup.smul_def (g : SpecialLinearGroup R V) (v : V) :
    g • v = g.toLinearEquiv • v := rfl

/--
theorem `_root_.SpecialLinearGroup.toLinearEquiv_eq_coe` / 定理 `_root_.SpecialLinearGroup.toLinearEquiv_eq_coe`

English:
theorem _root_.SpecialLinearGroup.toLinearEquiv_eq_coe
  given: (g : SpecialLinearGroup R V)
  proof: rfl

中文:
定理 _root_.SpecialLinearGroup.toLinearEquiv_eq_coe
  条件: (g : SpecialLinearGroup R V)
  证明: rfl
-/
theorem _root_.SpecialLinearGroup.toLinearEquiv_eq_coe (g : SpecialLinearGroup R V) :
    g.toLinearEquiv = (g : V ≃ₗ[R] V) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass (SpecialLinearGroup R V) R V
  body: by
    simp [SpecialLinearGroup.smul_def]

中文:
实例 :
  签名: 标量交换类 (SpecialLinearGroup R V) R V
  定义体: by
    simp [SpecialLinearGroup.smul_def]

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.smul_def, smul_def
-/
instance : SMulCommClass (SpecialLinearGroup R V) R V where
  smul_comm g a v := by
    simp [SpecialLinearGroup.smul_def]

section baseChange

open TensorProduct

variable {S : Type*} [CommRing S] [Algebra R S]
  [Module.Free R V] [Module.Finite R V]

/-- By base change, an `R`-algebra `S` induces a group homomorphism from
`SpecialLinearGroup R V` to `SpecialLinearGroup S (S ⊗[R] V)`. -/
@[simps]
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: : SpecialLinearGroup R V ->* SpecialLinearGroup S (S otimes[R] V) where
  body: ⟨LinearEquiv.baseChange R S V V g, by
      rw [LinearEquiv.det_baseChange]; rw [g.prop]; rw [map_one]⟩
map_one' := Subtype.ext by simp
map_mul' x y := Subtype.ext by simp [LinearEquiv.baseChange_mul]

中文:
定义 baseChange
  签名: : SpecialLinearGroup R V ->* SpecialLinearGroup S (S otimes[R] V) where
  定义体: ⟨LinearEquiv.baseChange R S V V g, by
      rw [LinearEquiv.det_baseChange]; rw [g.prop]; rw [map_one]⟩
map_one' := Subtype.ext by simp
map_mul' x y := Subtype.ext by simp [LinearEquiv.baseChange_mul]

Depends on / 依赖: LinearEquiv, LinearEquiv.baseChange, LinearEquiv.baseChange_mul, LinearEquiv.det_baseChange, Subtype, Subtype.ext, baseChange, baseChange_mul, det_baseChange, g.prop, map_mul, map_one
-/
def baseChange : SpecialLinearGroup R V ->* SpecialLinearGroup S (S otimes[R] V) where
  toFun g := ⟨LinearEquiv.baseChange R S V V g, by
      rw [LinearEquiv.det_baseChange]; rw [g.prop]; rw [map_one]⟩
map_one' := Subtype.ext by simp
map_mul' x y := Subtype.ext by simp [LinearEquiv.baseChange_mul]

end baseChange

variable {W X : Type*} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]

/--
Definition of `congr_linearEquiv` / `congr_linearEquiv` 的定义

English:
definition congr_linearEquiv
  signature: (e : V ≃ₗ[R] W)
  body: ⟨e.symm ≪≫ₗ f ≪≫ₗ e, by simp [f.prop]⟩
  invFun g := ⟨e ≪≫ₗ g ≪≫ₗ e.symm, by
    nth_rewrite 1 [← LinearEquiv.symm_symm e]
    rw [LinearEquiv.det_conj g e.symm]; rw [g.prop]⟩
left_inv f := Subtype.coe_injective by aesop
right_inv g := Subtype.coe_injective by aesop
map_mul' f g := Subtype.coe_injective by aesop

@[simp]

中文:
定义 congr_linearEquiv
  签名: (e : V ≃ₗ[R] W)
  定义体: ⟨e.symm ≪≫ₗ f ≪≫ₗ e, by simp [f.prop]⟩
  invFun g := ⟨e ≪≫ₗ g ≪≫ₗ e.symm, by
    nth_rewrite 1 [← LinearEquiv.symm_symm e]
    rw [LinearEquiv.det_conj g e.symm]; rw [g.prop]⟩
left_inv f := Subtype.coe_injective by aesop
right_inv g := Subtype.coe_injective by aesop
map_mul' f g := Subtype.coe_injective by aesop

@[simp]

Depends on / 依赖: e.symm, f.prop
-/
def congr_linearEquiv (e : V ≃ₗ[R] W) :
    SpecialLinearGroup R V ≃* SpecialLinearGroup R W where
  toFun f := ⟨e.symm ≪≫ₗ f ≪≫ₗ e, by simp [f.prop]⟩
  invFun g := ⟨e ≪≫ₗ g ≪≫ₗ e.symm, by
    nth_rewrite 1 [← LinearEquiv.symm_symm e]
    rw [LinearEquiv.det_conj g e.symm]; rw [g.prop]⟩
left_inv f := Subtype.coe_injective by aesop
right_inv g := Subtype.coe_injective by aesop
map_mul' f g := Subtype.coe_injective by aesop

@[simp]
/--
theorem `congr_linearEquiv_coe_apply` / 定理 `congr_linearEquiv_coe_apply`

English:
theorem congr_linearEquiv_coe_apply
  given: (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V)
  proof: rfl

@[simp]

中文:
定理 congr_linearEquiv_coe_apply
  条件: (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V)
  证明: rfl

@[simp]
-/
theorem congr_linearEquiv_coe_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) :
    (congr_linearEquiv e f : W ≃ₗ[R] W) = e.symm ≪≫ₗ f ≪≫ₗ e :=
  rfl

@[simp]
/--
theorem `congr_linearEquiv_apply_apply` / 定理 `congr_linearEquiv_apply_apply`

English:
theorem congr_linearEquiv_apply_apply
  given: (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) (x : W)
  proof: rfl

中文:
定理 congr_linearEquiv_apply_apply
  条件: (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) (x : W)
  证明: rfl
-/
theorem congr_linearEquiv_apply_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) (x : W) :
    congr_linearEquiv e f x = e (f (e.symm x)) :=
  rfl

/--
theorem `congr_linearEquiv_symm` / 定理 `congr_linearEquiv_symm`

English:
theorem congr_linearEquiv_symm
  given: (e : V ≃ₗ[R] W)
  proof: rfl

中文:
定理 congr_linearEquiv_symm
  条件: (e : V ≃ₗ[R] W)
  证明: rfl
-/
theorem congr_linearEquiv_symm (e : V ≃ₗ[R] W) :
    (congr_linearEquiv e).symm = congr_linearEquiv e.symm :=
  rfl

/--
theorem `congr_linearEquiv_trans` / 定理 `congr_linearEquiv_trans`

English:
theorem congr_linearEquiv_trans
  given: (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X)
  proof: by
  rfl

中文:
定理 congr_linearEquiv_trans
  条件: (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X)
  证明: by
  rfl
-/
theorem congr_linearEquiv_trans (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X) :
    (congr_linearEquiv e).trans (congr_linearEquiv f) = congr_linearEquiv (e.trans f) := by
  rfl

/--
theorem `congr_linearEquiv_refl` / 定理 `congr_linearEquiv_refl`

English:
theorem congr_linearEquiv_refl
  proof: by
  rfl

中文:
定理 congr_linearEquiv_refl
  证明: by
  rfl
-/
theorem congr_linearEquiv_refl :
    congr_linearEquiv (LinearEquiv.refl R V) = MulEquiv.refl _ := by
  rfl

end SpecialLinearGroup

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n R V)

/--
Definition of `toLin'_equiv` / `toLin'_equiv` 的定义

English:
definition toLin'_equiv
  signature: : SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R (n -> R) where
  body: ⟨Matrix.SpecialLinearGroup.toLin' A,
    by
      simp [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
        Matrix.SpecialLinearGroup.toLin'_to_linearMap]⟩
  invFun u := ⟨LinearMap.toMatrix' u,
      by simp [← LinearEquiv.coe_det, u.prop]⟩
left_inv A := Subtype.coe_injective by
    rw [← LinearEquiv.eq_symm_apply]; rw [LinearMap.toMatrix'_symm]; rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]
right_inv u := Subtype.coe_injective by
    simp [← LinearEquiv.toLinearMap_inj, Matrix.SpecialLinearGroup.toLin']
  map_mul' A B := Subtype.coe_injective (by simp)

中文:
定义 toLin'_equiv
  签名: : SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R (n -> R) where
  定义体: ⟨Matrix.SpecialLinearGroup.toLin' A,
    by
      simp [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
        Matrix.SpecialLinearGroup.toLin'_to_linearMap]⟩
  invFun u := ⟨LinearMap.toMatrix' u,
      by simp [← LinearEquiv.coe_det, u.prop]⟩
left_inv A := Subtype.coe_injective by
    rw [← LinearEquiv.eq_symm_apply]; rw [LinearMap.toMatrix'_symm]; rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]
right_inv u := Subtype.coe_injective by
    simp [← LinearEquiv.toLinearMap_inj, Matrix.SpecialLinearGroup.toLin']
  map_mul' A B := Subtype.coe_injective (by simp)

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.toLin, SpecialLinearGroup
-/
def toLin'_equiv : SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R (n -> R) where
  toFun A := ⟨Matrix.SpecialLinearGroup.toLin' A,
    by
      simp [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
        Matrix.SpecialLinearGroup.toLin'_to_linearMap]⟩
  invFun u := ⟨LinearMap.toMatrix' u,
      by simp [← LinearEquiv.coe_det, u.prop]⟩
left_inv A := Subtype.coe_injective by
    rw [← LinearEquiv.eq_symm_apply]; rw [LinearMap.toMatrix'_symm]; rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]
right_inv u := Subtype.coe_injective by
    simp [← LinearEquiv.toLinearMap_inj, Matrix.SpecialLinearGroup.toLin']
  map_mul' A B := Subtype.coe_injective (by simp)

/--
Definition of `toLin_equiv` / `toLin_equiv` 的定义

English:
definition toLin_equiv
  signature: (b : Module.Basis n R V)
  body: SpecialLinearGroup.toLin'_equiv.trans
    (SpecialLinearGroup.congr_linearEquiv b.equivFun.symm)

中文:
定义 toLin_equiv
  签名: (b : 模.基 n R V)
  定义体: SpecialLinearGroup.toLin'_equiv.trans
    (SpecialLinearGroup.congr_linearEquiv b.equivFun.symm)

Depends on / 依赖: Not.imp_symm, SpecialLinearGroup, SpecialLinearGroup.congr_linearEquiv, SpecialLinearGroup.toLin, _equiv, _equiv.trans, b.equivFun.symm, congr_linearEquiv, equivFun, imp_symm, integral_undef
-/
noncomputable def toLin_equiv (b : Module.Basis n R V) :
    SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R V :=
  SpecialLinearGroup.toLin'_equiv.trans
    (SpecialLinearGroup.congr_linearEquiv b.equivFun.symm)

/--
theorem `toLin_equiv.toLinearMap_eq` / 定理 `toLin_equiv.toLinearMap_eq`

English:
theorem toLin_equiv.toLinearMap_eq
  proof: rfl

中文:
定理 toLin_equiv.toLinearMap_eq
  证明: rfl
-/
theorem toLin_equiv.toLinearMap_eq
    (b : Module.Basis n R V) (g : Matrix.SpecialLinearGroup n R) :
    (toLin_equiv b g : V ->ₗ[R] V) = (Matrix.toLin b b g) :=
  rfl

/--
theorem `toLin_equiv.symm_toLinearMap_eq` / 定理 `toLin_equiv.symm_toLinearMap_eq`

English:
theorem toLin_equiv.symm_toLinearMap_eq
  proof: rfl

中文:
定理 toLin_equiv.symm_toLinearMap_eq
  证明: rfl
-/
theorem toLin_equiv.symm_toLinearMap_eq
    (b : Module.Basis n R V) (g : _root_.SpecialLinearGroup R V) :
    ((toLin_equiv b).symm g : Matrix n n R) = LinearMap.toMatrix b b g :=
  rfl

end Matrix.SpecialLinearGroup

namespace SpecialLinearGroup

section center

variable [Module.Free R V] [Module.Finite R V]

/--
theorem `center_eq_bot_of_finrank_le_one` / 定理 `center_eq_bot_of_finrank_le_one`

English:
theorem center_eq_bot_of_finrank_le_one
  given: (h : Module.finrank R V <= 1)
  proof: by
  nontriviality R
  let b := Module.Free.chooseBasis R V
  have : Subsingleton (Module.Free.ChooseBasisIndex R V) := by
    rwa [← Finite.card_le_one_iff_subsingleton,
      Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b]
  have : Subsingleton (Subgroup.center
    (Matrix.SpecialLinearGroup (Module.Free.ChooseBasisIndex R V) R)) := by
    infer_instance
  rw [Equiv.subsingleton_congr
    (Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).toEquiv] at this
  exact Subgroup.eq_bot_of_subsingleton _

中文:
定理 center_eq_bot_of_finrank_le_one
  条件: (h : 模.finrank R V <= 1)
  证明: by
  nontriviality R
  let b := Module.Free.chooseBasis R V
  have : Subsingleton (Module.Free.ChooseBasisIndex R V) := by
    rwa [← Finite.card_le_one_iff_subsingleton,
      Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b]
  have : Subsingleton (Subgroup.center
    (Matrix.SpecialLinearGroup (Module.Free.ChooseBasisIndex R V) R)) := by
    infer_instance
  rw [Equiv.subsingleton_congr
    (Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).toEquiv] at this
  exact Subgroup.eq_bot_of_subsingleton _

Depends on / 依赖: ChooseBasisIndex, Equiv.subsingleton_congr, Finite, Finite.card_le_one_iff_subsingleton, Matrix, Matrix.SpecialLinearGroup, Matrix.SpecialLinearGroup.toLin_equiv, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Module.finrank_eq_card_basis, Nat.card_eq_fintype_card, SpecialLinearGroup, Subgroup, Subgroup.center, Subgroup.centerCongr, Subgroup.eq_bot_of_subsingleton, Subsingleton, card_eq_fintype_card, card_le_one_iff_subsingleton
-/
theorem center_eq_bot_of_finrank_le_one (h : Module.finrank R V <= 1) :
    Subgroup.center (SpecialLinearGroup R V) = ⊥ := by
  nontriviality R
  let b := Module.Free.chooseBasis R V
  have : Subsingleton (Module.Free.ChooseBasisIndex R V) := by
    rwa [← Finite.card_le_one_iff_subsingleton,
      Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b]
  have : Subsingleton (Subgroup.center
    (Matrix.SpecialLinearGroup (Module.Free.ChooseBasisIndex R V) R)) := by
    infer_instance
  rw [Equiv.subsingleton_congr
    (Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).toEquiv] at this
  exact Subgroup.eq_bot_of_subsingleton _

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {g : SpecialLinearGroup R V}
  proof: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (SpecialLinearGroup R V) := inferInstance
    simp [Subsingleton.eq_one g]
  let b := Module.Free.chooseBasis R V
  let := Module.Free.ChooseBasisIndex.fintype R V
  rw [Module.finrank_eq_card_basis b]
  let e := (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  rw [← show e g in Subgroup.center _ ↔ g in Subgroup.center _ from
    MulEquivClass.apply_mem_center_iff e]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  apply exists_congr
  simp only [Matrix.scalar_apply, and_congr_right_iff, e]
  intro r hr
  suffices ((Matrix.SpecialLinearGroup.toLin_equiv b).symm g) =
    Matrix.of fun i j => (b.repr (g (b j))) i by
    simp only [this]
    rw [← (LinearMap.toMatrix b b).injective.eq_iff]
    simp only [← Matrix.ext_iff, Matrix.of_apply]
    apply forall₂_congr
    intro i j
    simp [Matrix.diagonal, LinearMap.toMatrix_apply,
      Finsupp.single, Pi.single_apply, Iff.symm eq_comm]
  ext
  simp [Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq, LinearMap.toMatrix_apply]

中文:
定理 mem_center_iff
  条件: {g : SpecialLinearGroup R V}
  证明: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (SpecialLinearGroup R V) := inferInstance
    simp [Subsingleton.eq_one g]
  let b := Module.Free.chooseBasis R V
  let := Module.Free.ChooseBasisIndex.fintype R V
  rw [Module.finrank_eq_card_basis b]
  let e := (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  rw [← show e g in Subgroup.center _ ↔ g in Subgroup.center _ from
    MulEquivClass.apply_mem_center_iff e]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  apply exists_congr
  simp only [Matrix.scalar_apply, and_congr_right_iff, e]
  intro r hr
  suffices ((Matrix.SpecialLinearGroup.toLin_equiv b).symm g) =
    Matrix.of fun i j => (b.repr (g (b j))) i by
    simp only [this]
    rw [← (LinearMap.toMatrix b b).injective.eq_iff]
    simp only [← Matrix.ext_iff, Matrix.of_apply]
    apply forall₂_congr
    intro i j
    simp [Matrix.diagonal, LinearMap.toMatrix_apply,
      Finsupp.single, Pi.single_apply, Iff.symm eq_comm]
  ext
  simp [Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq, LinearMap.toMatrix_apply]

Depends on / 依赖: ChooseBasisIndex, Matrix, Matrix.SpecialLinearGroup.mem_center_iff, Matrix.SpecialLinearGroup.toLin_equiv, Module, Module.Free.ChooseBasisIndex.fintype, Module.Free.chooseBasis, Module.finrank_eq_card_basis, MulEquivClass, MulEquivClass.apply_mem_center_iff, SpecialLinearGroup, Subgroup, Subgroup.center, Subsingleton, Subsingleton.eq_one, apply_mem_center_iff, center, chooseBasis, eq_one, exists_congr
-/
theorem mem_center_iff {g : SpecialLinearGroup R V} :
    g in Subgroup.center (SpecialLinearGroup R V) ↔
      exists (r : R), r ^ (Module.finrank R V) = 1 ∧
        (g : V ->ₗ[R] V) = r • LinearMap.id := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (SpecialLinearGroup R V) := inferInstance
    simp [Subsingleton.eq_one g]
  let b := Module.Free.chooseBasis R V
  let := Module.Free.ChooseBasisIndex.fintype R V
  rw [Module.finrank_eq_card_basis b]
  let e := (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  rw [← show e g in Subgroup.center _ ↔ g in Subgroup.center _ from
    MulEquivClass.apply_mem_center_iff e]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  apply exists_congr
  simp only [Matrix.scalar_apply, and_congr_right_iff, e]
  intro r hr
  suffices ((Matrix.SpecialLinearGroup.toLin_equiv b).symm g) =
    Matrix.of fun i j => (b.repr (g (b j))) i by
    simp only [this]
    rw [← (LinearMap.toMatrix b b).injective.eq_iff]
    simp only [← Matrix.ext_iff, Matrix.of_apply]
    apply forall₂_congr
    intro i j
    simp [Matrix.diagonal, LinearMap.toMatrix_apply,
      Finsupp.single, Pi.single_apply, Iff.symm eq_comm]
  ext
  simp [Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq, LinearMap.toMatrix_apply]

/--
theorem `mem_center_iff_spec` / 定理 `mem_center_iff_spec`

English:
theorem mem_center_iff_spec
  statement: {g : SpecialLinearGroup R V}
  proof: by
  let H := (mem_center_iff.mp hg).choose_spec.2
  rw [LinearMap.ext_iff] at H
  simp [H]

中文:
定理 mem_center_iff_spec
  结论: {g : SpecialLinearGroup R V}
  证明: by
  let H := (mem_center_iff.mp hg).choose_spec.2
  rw [LinearMap.ext_iff] at H
  simp [H]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, choose_spec, ext_iff, mem_center_iff, mem_center_iff.mp
-/
theorem mem_center_iff_spec {g : SpecialLinearGroup R V}
    (hg : g in Subgroup.center (SpecialLinearGroup R V)) (x : V) :
    (g : V ->ₗ[R] V) x = (mem_center_iff.mp hg).choose • x := by
  let H := (mem_center_iff.mp hg).choose_spec.2
  rw [LinearMap.ext_iff] at H
  simp [H]

/- TODO : delete this auxiliary definition
and put it in the definition of `centerEquivRootsOfUnity.
How can one access to the definition of one already defined term in a structure
while one is still defining it? -/
/--
Definition of `centerEquivRootsOfUnity_invFun` / `centerEquivRootsOfUnity_invFun` 的定义

English:
definition centerEquivRootsOfUnity_invFun
  body: ⟨⟨LinearMap.equivOfIsUnitDet (M := V) (R := R) (f := ((r : Rˣ) : R) • LinearMap.id) (by
    simp [LinearMap.det_smul, IsUnit.pow]), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, LinearMap.coe_equivOfIsUnitDet,
      LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_one]
    have := (mem_rootsOfUnity' _ _).mp r.prop
    rcases max_cases (Module.finrank R V) 1 with ⟨h, h'⟩ | ⟨h, h'⟩
    · simp_rw [h] at this
      exact this
    · simp_rw [h, pow_one] at this
      simp [this]⟩, by
    simp only [mem_center_iff, LinearMap.coe_equivOfIsUnitDet]
    use r.val
    simp only [and_true]
    let ⟨r, hr⟩ := r
    by_cases hV : Module.finrank R V = 0
    · simp [hV]
    · rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at hV
      rw [mem_rootsOfUnity']; rw [max_eq_left hV] at hr
      simpa [← Subtype.val_inj, ← Units.val_inj]⟩

中文:
定义 centerEquivRootsOfUnity_invFun
  定义体: ⟨⟨LinearMap.equivOfIsUnitDet (M := V) (R := R) (f := ((r : Rˣ) : R) • LinearMap.id) (by
    simp [LinearMap.det_smul, IsUnit.pow]), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, LinearMap.coe_equivOfIsUnitDet,
      LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_one]
    have := (mem_rootsOfUnity' _ _).mp r.prop
    rcases max_cases (Module.finrank R V) 1 with ⟨h, h'⟩ | ⟨h, h'⟩
    · simp_rw [h] at this
      exact this
    · simp_rw [h, pow_one] at this
      simp [this]⟩, by
    simp only [mem_center_iff, LinearMap.coe_equivOfIsUnitDet]
    use r.val
    simp only [and_true]
    let ⟨r, hr⟩ := r
    by_cases hV : Module.finrank R V = 0
    · simp [hV]
    · rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at hV
      rw [mem_rootsOfUnity']; rw [max_eq_left hV] at hr
      simpa [← Subtype.val_inj, ← Units.val_inj]⟩

Depends on / 依赖: IsUnit, IsUnit.pow, LinearEquiv, LinearEquiv.coe_det, LinearMap, LinearMap.coe, LinearMap.coe_equivOfIsUnitDet, LinearMap.det_id, LinearMap.det_smul, LinearMap.equivOfIsUnitDet, LinearMap.id, Module, Module.finrank, Units.val_inj, Units.val_one, coe_det, coe_equivOfIsUnitDet, det_id, det_smul, equivOfIsUnitDet
-/
noncomputable def centerEquivRootsOfUnity_invFun
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    Subgroup.center (SpecialLinearGroup R V) :=
  ⟨⟨LinearMap.equivOfIsUnitDet (M := V) (R := R) (f := ((r : Rˣ) : R) • LinearMap.id) (by
    simp [LinearMap.det_smul, IsUnit.pow]), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, LinearMap.coe_equivOfIsUnitDet,
      LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_one]
    have := (mem_rootsOfUnity' _ _).mp r.prop
    rcases max_cases (Module.finrank R V) 1 with ⟨h, h'⟩ | ⟨h, h'⟩
    · simp_rw [h] at this
      exact this
    · simp_rw [h, pow_one] at this
      simp [this]⟩, by
    simp only [mem_center_iff, LinearMap.coe_equivOfIsUnitDet]
    use r.val
    simp only [and_true]
    let ⟨r, hr⟩ := r
    by_cases hV : Module.finrank R V = 0
    · simp [hV]
    · rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at hV
      rw [mem_rootsOfUnity']; rw [max_eq_left hV] at hr
      simpa [← Subtype.val_inj, ← Units.val_inj]⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Definition of `centerEquivRootsOfUnity` / `centerEquivRootsOfUnity` 的定义

English:
definition centerEquivRootsOfUnity
  signature: :
  body: (subsingleton_or_nontrivial R).by_cases
    (fun _ => 1)
    (fun hR => (subsingleton_or_nontrivial V).by_cases
      (fun _ => 1)
      (fun hV => by
        rw [← Module.finrank_pos_iff_of_free (R := R)] at hV
        replace hV : 1 <= Module.finrank R V := hV
        have hr := (mem_center_iff.mp g.prop).choose_spec.1
        set r := (mem_center_iff.mp g.prop).choose
        rw [← Nat.max_eq_left hV] at hr
        have : IsUnit r := by
          rw [← isUnit_pow_iff _]; rw [hr]
          · exact isUnit_one
          rw [Nat.max_eq_left hV]
          exact Nat.ne_zero_of_lt hV
        exact ⟨this.unit, by simp [mem_rootsOfUnity, ← Units.val_inj, hr]⟩))
  invFun := centerEquivRootsOfUnity_invFun
  left_inv g := by
    simp only [centerEquivRootsOfUnity_invFun, ← Subtype.val_inj,
      ← LinearEquiv.toLinearMap_inj, LinearMap.coe_equivOfIsUnitDet]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one g]
    · simp [Subsingleton.eq_one g]
    · simp only [IsUnit.unit_spec, ← (mem_center_iff.mp g.prop).choose_spec.2]
  right_inv r := by
    rw [← Subtype.val_inj]; rw [SetLike.coe_eq_coe]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one r]
    · replace hR := not_subsingleton_iff_nontrivial.mp hR
      symm
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simpa [hV] using (mem_rootsOfUnity _ _).mp r.prop
    · rw [not_subsingleton_iff_nontrivial] at hV
      have := Module.Free.instFaithfulSMulOfNontrivial R V
      simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec]
      have H := mem_center_iff.mp (Subtype.prop (centerEquivRootsOfUnity_invFun r))
      suffices (H.choose • LinearMap.id : V ->ₗ[R] V) = (r.val : R) • LinearMap.id by
        apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
        intro x
        rw [LinearMap.ext_iff] at this
        simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at this
        rw [this x]
      rw [← H.choose_spec.2]
      simp [centerEquivRootsOfUnity_invFun]
  map_mul' g h := by
    simp only [Or.by_cases, Subgroup.coe_mul, coe_mul, LinearEquiv.coe_toLinearMap_mul,
      mul_dite, mul_one, dite_mul, one_mul, MulMemClass.mk_mul_mk]
    split_ifs with hR hV
    · rfl
    · rfl
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    set Hg := (mem_center_iff.mp g.prop)
    set Hh := (mem_center_iff.mp h.prop)
    set Hgh := (mem_center_iff.mp (g * h).prop)
    simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec, Units.val_mul]
    change Hgh.choose = Hg.choose * Hh.choose
    suffices (Hgh.choose • LinearMap.id : V ->ₗ[R] V)
      = (Hg.choose • LinearMap.id) * (Hh.choose • LinearMap.id) by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp [mul_smul,
        ← mem_center_iff_spec (g * h).prop, ← mem_center_iff_spec h.prop,
        ← mem_center_iff_spec g.prop]
    simp [← Hgh.choose_spec.2, ← Hh.choose_spec.2, ← Hg.choose_spec.2]

中文:
定义 centerEquivRootsOfUnity
  签名: :
  定义体: (subsingleton_or_nontrivial R).by_cases
    (fun _ => 1)
    (fun hR => (subsingleton_or_nontrivial V).by_cases
      (fun _ => 1)
      (fun hV => by
        rw [← Module.finrank_pos_iff_of_free (R := R)] at hV
        replace hV : 1 <= Module.finrank R V := hV
        have hr := (mem_center_iff.mp g.prop).choose_spec.1
        set r := (mem_center_iff.mp g.prop).choose
        rw [← Nat.max_eq_left hV] at hr
        have : IsUnit r := by
          rw [← isUnit_pow_iff _]; rw [hr]
          · exact isUnit_one
          rw [Nat.max_eq_left hV]
          exact Nat.ne_zero_of_lt hV
        exact ⟨this.unit, by simp [mem_rootsOfUnity, ← Units.val_inj, hr]⟩))
  invFun := centerEquivRootsOfUnity_invFun
  left_inv g := by
    simp only [centerEquivRootsOfUnity_invFun, ← Subtype.val_inj,
      ← LinearEquiv.toLinearMap_inj, LinearMap.coe_equivOfIsUnitDet]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one g]
    · simp [Subsingleton.eq_one g]
    · simp only [IsUnit.unit_spec, ← (mem_center_iff.mp g.prop).choose_spec.2]
  right_inv r := by
    rw [← Subtype.val_inj]; rw [SetLike.coe_eq_coe]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one r]
    · replace hR := not_subsingleton_iff_nontrivial.mp hR
      symm
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simpa [hV] using (mem_rootsOfUnity _ _).mp r.prop
    · rw [not_subsingleton_iff_nontrivial] at hV
      have := Module.Free.instFaithfulSMulOfNontrivial R V
      simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec]
      have H := mem_center_iff.mp (Subtype.prop (centerEquivRootsOfUnity_invFun r))
      suffices (H.choose • LinearMap.id : V ->ₗ[R] V) = (r.val : R) • LinearMap.id by
        apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
        intro x
        rw [LinearMap.ext_iff] at this
        simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at this
        rw [this x]
      rw [← H.choose_spec.2]
      simp [centerEquivRootsOfUnity_invFun]
  map_mul' g h := by
    simp only [Or.by_cases, Subgroup.coe_mul, coe_mul, LinearEquiv.coe_toLinearMap_mul,
      mul_dite, mul_one, dite_mul, one_mul, MulMemClass.mk_mul_mk]
    split_ifs with hR hV
    · rfl
    · rfl
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    set Hg := (mem_center_iff.mp g.prop)
    set Hh := (mem_center_iff.mp h.prop)
    set Hgh := (mem_center_iff.mp (g * h).prop)
    simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec, Units.val_mul]
    change Hgh.choose = Hg.choose * Hh.choose
    suffices (Hgh.choose • LinearMap.id : V ->ₗ[R] V)
      = (Hg.choose • LinearMap.id) * (Hh.choose • LinearMap.id) by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp [mul_smul,
        ← mem_center_iff_spec (g * h).prop, ← mem_center_iff_spec h.prop,
        ← mem_center_iff_spec g.prop]
    simp [← Hgh.choose_spec.2, ← Hh.choose_spec.2, ← Hg.choose_spec.2]

Depends on / 依赖: subsingleton_or_nontrivial
-/
noncomputable def centerEquivRootsOfUnity :
    (Subgroup.center (SpecialLinearGroup R V)) ≃*
      ↥(rootsOfUnity (max (Module.finrank R V) 1) R) where
  toFun g := (subsingleton_or_nontrivial R).by_cases
    (fun _ => 1)
    (fun hR => (subsingleton_or_nontrivial V).by_cases
      (fun _ => 1)
      (fun hV => by
        rw [← Module.finrank_pos_iff_of_free (R := R)] at hV
        replace hV : 1 <= Module.finrank R V := hV
        have hr := (mem_center_iff.mp g.prop).choose_spec.1
        set r := (mem_center_iff.mp g.prop).choose
        rw [← Nat.max_eq_left hV] at hr
        have : IsUnit r := by
          rw [← isUnit_pow_iff _]; rw [hr]
          · exact isUnit_one
          rw [Nat.max_eq_left hV]
          exact Nat.ne_zero_of_lt hV
        exact ⟨this.unit, by simp [mem_rootsOfUnity, ← Units.val_inj, hr]⟩))
  invFun := centerEquivRootsOfUnity_invFun
  left_inv g := by
    simp only [centerEquivRootsOfUnity_invFun, ← Subtype.val_inj,
      ← LinearEquiv.toLinearMap_inj, LinearMap.coe_equivOfIsUnitDet]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one g]
    · simp [Subsingleton.eq_one g]
    · simp only [IsUnit.unit_spec, ← (mem_center_iff.mp g.prop).choose_spec.2]
  right_inv r := by
    rw [← Subtype.val_inj]; rw [SetLike.coe_eq_coe]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one r]
    · replace hR := not_subsingleton_iff_nontrivial.mp hR
      symm
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simpa [hV] using (mem_rootsOfUnity _ _).mp r.prop
    · rw [not_subsingleton_iff_nontrivial] at hV
      have := Module.Free.instFaithfulSMulOfNontrivial R V
      simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec]
      have H := mem_center_iff.mp (Subtype.prop (centerEquivRootsOfUnity_invFun r))
      suffices (H.choose • LinearMap.id : V ->ₗ[R] V) = (r.val : R) • LinearMap.id by
        apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
        intro x
        rw [LinearMap.ext_iff] at this
        simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at this
        rw [this x]
      rw [← H.choose_spec.2]
      simp [centerEquivRootsOfUnity_invFun]
  map_mul' g h := by
    simp only [Or.by_cases, Subgroup.coe_mul, coe_mul, LinearEquiv.coe_toLinearMap_mul,
      mul_dite, mul_one, dite_mul, one_mul, MulMemClass.mk_mul_mk]
    split_ifs with hR hV
    · rfl
    · rfl
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    set Hg := (mem_center_iff.mp g.prop)
    set Hh := (mem_center_iff.mp h.prop)
    set Hgh := (mem_center_iff.mp (g * h).prop)
    simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec, Units.val_mul]
    change Hgh.choose = Hg.choose * Hh.choose
    suffices (Hgh.choose • LinearMap.id : V ->ₗ[R] V)
      = (Hg.choose • LinearMap.id) * (Hh.choose • LinearMap.id) by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp [mul_smul,
        ← mem_center_iff_spec (g * h).prop, ← mem_center_iff_spec h.prop,
        ← mem_center_iff_spec g.prop]
    simp [← Hgh.choose_spec.2, ← Hh.choose_spec.2, ← Hg.choose_spec.2]

/--
theorem `centerEquivRootsOfUnity_apply` / 定理 `centerEquivRootsOfUnity_apply`

English:
theorem centerEquivRootsOfUnity_apply
  proof: by
  simp only [centerEquivRootsOfUnity, Or.by_cases, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    dite_smul, one_smul, Subgroup.mk_smul, Units.smul_isUnit, dite_eq_ite]
  split_ifs with hR hV
  · have : Subsingleton V := Module.subsingleton R V
    apply Subsingleton.eq_one
  · apply Subsingleton.eq_one
  · rw [not_subsingleton_iff_nontrivial] at hV
    rw [← (mem_center_iff.mp g.prop).choose_spec.2]

中文:
定理 centerEquivRootsOfUnity_apply
  证明: by
  simp only [centerEquivRootsOfUnity, Or.by_cases, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    dite_smul, one_smul, Subgroup.mk_smul, Units.smul_isUnit, dite_eq_ite]
  split_ifs with hR hV
  · have : Subsingleton V := Module.subsingleton R V
    apply Subsingleton.eq_one
  · apply Subsingleton.eq_one
  · rw [not_subsingleton_iff_nontrivial] at hV
    rw [← (mem_center_iff.mp g.prop).choose_spec.2]

Depends on / 依赖: Equiv.coe_fn_mk, Module, Module.subsingleton, MulEquiv, MulEquiv.coe_mk, Or.by_cases, Subgroup, Subgroup.mk_smul, Subsingleton, Subsingleton.eq_one, Units.smul_isUnit, centerEquivRootsOfUnity, choose_spec, coe_fn_mk, coe_mk, dite_eq_ite, dite_smul, eq_one, g.prop, mem_center_iff
-/
theorem centerEquivRootsOfUnity_apply
    (g : Subgroup.center (SpecialLinearGroup R V)) :
    (g : V ->ₗ[R] V) = (centerEquivRootsOfUnity g) • LinearMap.id := by
  simp only [centerEquivRootsOfUnity, Or.by_cases, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    dite_smul, one_smul, Subgroup.mk_smul, Units.smul_isUnit, dite_eq_ite]
  split_ifs with hR hV
  · have : Subsingleton V := Module.subsingleton R V
    apply Subsingleton.eq_one
  · apply Subsingleton.eq_one
  · rw [not_subsingleton_iff_nontrivial] at hV
    rw [← (mem_center_iff.mp g.prop).choose_spec.2]

/--
theorem `centerEquivRootsOfUnity_apply_apply` / 定理 `centerEquivRootsOfUnity_apply_apply`

English:
theorem centerEquivRootsOfUnity_apply_apply
  proof: by
  simp only
  rw [← LinearEquiv.coe_toLinearMap]; rw [centerEquivRootsOfUnity_apply]
  simp

中文:
定理 centerEquivRootsOfUnity_apply_apply
  证明: by
  simp only
  rw [← LinearEquiv.coe_toLinearMap]; rw [centerEquivRootsOfUnity_apply]
  simp

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, centerEquivRootsOfUnity_apply, coe_toLinearMap
-/
theorem centerEquivRootsOfUnity_apply_apply
    (g : Subgroup.center (SpecialLinearGroup R V)) (x : V) :
    (centerEquivRootsOfUnity g) • x = (g : SpecialLinearGroup R V) x := by
  simp only
  rw [← LinearEquiv.coe_toLinearMap]; rw [centerEquivRootsOfUnity_apply]
  simp

/--
theorem `_root_.rootsOfUnity.eq_one` / 定理 `_root_.rootsOfUnity.eq_one`

English:
theorem _root_.rootsOfUnity.eq_one
  statement: {n : Nat} {r : rootsOfUnity n R}
  proof: by
  have h := r.prop
  simpa only [mem_rootsOfUnity, hn, pow_one] using h

中文:
定理 _root_.rootsOfUnity.eq_one
  结论: {n : 自然数} {r : rootsOfUnity n R}
  证明: by
  have h := r.prop
  simpa only [mem_rootsOfUnity, hn, pow_one] using h

Depends on / 依赖: mem_rootsOfUnity, pow_one, r.prop
-/
theorem _root_.rootsOfUnity.eq_one {n : Nat} {r : rootsOfUnity n R}
    (hn : n = 1) : r.val = 1 := by
  have h := r.prop
  simpa only [mem_rootsOfUnity, hn, pow_one] using h

/--
theorem `centerEquivRootsOfUnity_apply_of_finrank_le_one` / 定理 `centerEquivRootsOfUnity_apply_of_finrank_le_one`

English:
theorem centerEquivRootsOfUnity_apply_of_finrank_le_one
  proof: by
  rw [← Subtype.coe_inj]; rw [OneMemClass.coe_one]
  apply rootsOfUnity.eq_one
  rw [Nat.max_eq_right d1]

中文:
定理 centerEquivRootsOfUnity_apply_of_finrank_le_one
  证明: by
  rw [← Subtype.coe_inj]; rw [OneMemClass.coe_one]
  apply rootsOfUnity.eq_one
  rw [Nat.max_eq_right d1]

Depends on / 依赖: Nat.max_eq_right, OneMemClass, OneMemClass.coe_one, Subtype, Subtype.coe_inj, coe_inj, coe_one, eq_one, max_eq_right, rootsOfUnity, rootsOfUnity.eq_one
-/
theorem centerEquivRootsOfUnity_apply_of_finrank_le_one
    (d1 : Module.finrank R V <= 1) (g : Subgroup.center (SpecialLinearGroup R V)) :
    centerEquivRootsOfUnity g = 1 := by
  rw [← Subtype.coe_inj]; rw [OneMemClass.coe_one]
  apply rootsOfUnity.eq_one
  rw [Nat.max_eq_right d1]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `centerEquivRootsOfUnity_symm_apply` / 定理 `centerEquivRootsOfUnity_symm_apply`

English:
theorem centerEquivRootsOfUnity_symm_apply
  proof: by
  simp only [centerEquivRootsOfUnity, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    centerEquivRootsOfUnity_invFun, LinearMap.coe_equivOfIsUnitDet]
  congr

中文:
定理 centerEquivRootsOfUnity_symm_apply
  证明: by
  simp only [centerEquivRootsOfUnity, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    centerEquivRootsOfUnity_invFun, LinearMap.coe_equivOfIsUnitDet]
  congr

Depends on / 依赖: Equiv.coe_fn_symm_mk, LinearMap, LinearMap.coe_equivOfIsUnitDet, MulEquiv, MulEquiv.coe_mk, MulEquiv.symm_mk, centerEquivRootsOfUnity, centerEquivRootsOfUnity_invFun, coe_equivOfIsUnitDet, coe_fn_symm_mk, coe_mk, symm_mk
-/
theorem centerEquivRootsOfUnity_symm_apply
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    (centerEquivRootsOfUnity.symm r : V ->ₗ[R] V) = r • LinearMap.id := by
  simp only [centerEquivRootsOfUnity, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    centerEquivRootsOfUnity_invFun, LinearMap.coe_equivOfIsUnitDet]
  congr

section

open Subgroup Matrix Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)

-- compare with `Matrix.SpecialLinearGroup.centerEquivRootsOfUnity`
-- TODO : golf!
/--
theorem `centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq` / 定理 `centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq`

English:
theorem centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq
  given: (g)
  proof: by
  nontriviality R
  by_cases hV : Subsingleton V
  · convert! Eq.refl (1 : Rˣ) <;>
    · apply rootsOfUnity.eq_one
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simp only [hV, sup_eq_right, zero_le_one, ← Module.finrank_eq_card_basis b]
  · have hι : ¬ IsEmpty ι := fun hι => hV (by
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)]; rw [Module.finrank_eq_card_basis b]; rw [Fintype.card_of_isEmpty])
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    suffices (((((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).trans
      centerEquivRootsOfUnity g).val : R) • LinearMap.id) : V ->ₗ[R] V) =
        ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g).val : R) • LinearMap.id by
      rw [← Units.val_inj]
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp only [MulEquiv.trans_apply, LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq] at this
      rw [MulEquiv.trans_apply]; rw [this]
    simp only [MulEquiv.trans_apply]
    have hgg' := Subgroup.centerCongr_apply_coe (Matrix.SpecialLinearGroup.toLin_equiv b) g
    rw [← Subtype.coe_inj]; rw [← LinearEquiv.toLinearMap_inj]; rw [LinearMap.ext_iff] at hgg'
    set g' := ((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)) g)
    ext x
    have := centerEquivRootsOfUnity_apply_apply g' x
    simp only [Subgroup.smul_def, Units.smul_def] at this
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [this]; rw [← LinearEquiv.coe_toLinearMap]; rw [hgg']; rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]; rw [Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity g]; rw [Matrix.toLin_scalar]
    simp

中文:
定理 centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq
  条件: (g)
  证明: by
  nontriviality R
  by_cases hV : Subsingleton V
  · convert! Eq.refl (1 : Rˣ) <;>
    · apply rootsOfUnity.eq_one
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simp only [hV, sup_eq_right, zero_le_one, ← Module.finrank_eq_card_basis b]
  · have hι : ¬ IsEmpty ι := fun hι => hV (by
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)]; rw [Module.finrank_eq_card_basis b]; rw [Fintype.card_of_isEmpty])
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    suffices (((((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).trans
      centerEquivRootsOfUnity g).val : R) • LinearMap.id) : V ->ₗ[R] V) =
        ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g).val : R) • LinearMap.id by
      rw [← Units.val_inj]
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp only [MulEquiv.trans_apply, LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq] at this
      rw [MulEquiv.trans_apply]; rw [this]
    simp only [MulEquiv.trans_apply]
    have hgg' := Subgroup.centerCongr_apply_coe (Matrix.SpecialLinearGroup.toLin_equiv b) g
    rw [← Subtype.coe_inj]; rw [← LinearEquiv.toLinearMap_inj]; rw [LinearMap.ext_iff] at hgg'
    set g' := ((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)) g)
    ext x
    have := centerEquivRootsOfUnity_apply_apply g' x
    simp only [Subgroup.smul_def, Units.smul_def] at this
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [this]; rw [← LinearEquiv.coe_toLinearMap]; rw [hgg']; rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]; rw [Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity g]; rw [Matrix.toLin_scalar]
    simp

Depends on / 依赖: Eq.refl, Fintype, Fintype.card_of_isEmpty, IsEmpty, Module, Module.Free.instFaithfulSMulOfNontrivial, Module.finrank_eq_card_basis, Module.finrank_eq_zero_iff_of_free, Subsingleton, card_of_isEmpty, convert, eq_one, finrank_eq_card_basis, finrank_eq_zero_iff_of_free, instFaithfulSMulOfNontrivial, nontriviality, not_subsingleton_iff_nontrivial, rootsOfUnity, rootsOfUnity.eq_one, sup_eq_right
-/
theorem centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq (g) :
    ((centerCongr (toLin_equiv b)).trans centerEquivRootsOfUnity g).val =
      Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g := by
  nontriviality R
  by_cases hV : Subsingleton V
  · convert! Eq.refl (1 : Rˣ) <;>
    · apply rootsOfUnity.eq_one
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simp only [hV, sup_eq_right, zero_le_one, ← Module.finrank_eq_card_basis b]
  · have hι : ¬ IsEmpty ι := fun hι => hV (by
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)]; rw [Module.finrank_eq_card_basis b]; rw [Fintype.card_of_isEmpty])
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    suffices (((((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).trans
      centerEquivRootsOfUnity g).val : R) • LinearMap.id) : V ->ₗ[R] V) =
        ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g).val : R) • LinearMap.id by
      rw [← Units.val_inj]
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp only [MulEquiv.trans_apply, LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq] at this
      rw [MulEquiv.trans_apply]; rw [this]
    simp only [MulEquiv.trans_apply]
    have hgg' := Subgroup.centerCongr_apply_coe (Matrix.SpecialLinearGroup.toLin_equiv b) g
    rw [← Subtype.coe_inj]; rw [← LinearEquiv.toLinearMap_inj]; rw [LinearMap.ext_iff] at hgg'
    set g' := ((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)) g)
    ext x
    have := centerEquivRootsOfUnity_apply_apply g' x
    simp only [Subgroup.smul_def, Units.smul_def] at this
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [this]; rw [← LinearEquiv.coe_toLinearMap]; rw [hgg']; rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]; rw [Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity g]; rw [Matrix.toLin_scalar]
    simp

end

end center

end SpecialLinearGroup
