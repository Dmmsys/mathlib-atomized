/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

import Mathlib.Algebra.Module.Torsion.Prod

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `QuaternionAlgebra R a b c`, `ℍ[R, a, b, c]` :
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b`, `c`
  (Many other references such as Wikipedia assume $\operatorname{char} R ≠ 2$ therefore one can
  complete the square and WLOG assume $b = 0$.)
* `Quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a.
  `QuaternionAlgebra R (-1) (0) (-1)`;
* `Quaternion.normSq` : square of the norm of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `Ring ℍ[R, a, b, c]`, `StarRing ℍ[R, a, b, c]`, and `Algebra R ℍ[R, a, b, c]` :
  for any commutative ring `R`;
* `Ring ℍ[R]`, `StarRing ℍ[R]`, and `Algebra R ℍ[R]` : for any commutative ring `R`;
* `IsDomain ℍ[R]` : for a linear ordered commutative ring `R`;
* `DivisionRing ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`.

* `ℍ[R,c₁,c₂,c₃]` : `QuaternionAlgebra R c₁ c₂ c₃`
* `ℍ[R,c₁,c₂]` : `QuaternionAlgebra R c₁ 0 c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/

@[expose] public section

open Module

/-- Quaternion algebra over a type with fixed coefficients where $i^2 = a + bi$ and $j^2 = c$,
denoted as `ℍ[R,a,b]`.
Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`. -/
@[ext]
/--
Definition of `QuaternionAlgebra` / `QuaternionAlgebra` 的定义

English:
structure QuaternionAlgebra
  parameters: (R : Type*) (a b c : R)
  axioms and operations (4):
    - re : R
    - imI : R
    - imJ : R
    - imK : R

中文:
结构 Quaternion代数
  参数: (R : 类型) (a b c : R)
  公理与运算 (4 个):
    - re : R
    - imI : R
    - imJ : R
    - imK : R
-/
structure QuaternionAlgebra (R : Type*) (a b c : R) where
  /-- Real part of a quaternion. -/
  re : R
  /-- First imaginary part (i) of a quaternion. -/
  imI : R
  /-- Second imaginary part (j) of a quaternion. -/
  imJ : R
  /-- Third imaginary part (k) of a quaternion. -/
  imK : R

initialize_simps_projections QuaternionAlgebra
  (as_prefix re, as_prefix imI, as_prefix imJ, as_prefix imK)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "," c "]" =>
    QuaternionAlgebra R a b c

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "]" => QuaternionAlgebra R a 0 b

namespace QuaternionAlgebra
open Quaternion

/-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
@[simps]
/--
Definition of `equivProd` / `equivProd` 的定义

English:
definition equivProd
  signature: {R : Type*} (c₁ c₂ c₃ : R)
  body: ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩

中文:
定义 equivProd
  签名: {R : 类型} (c₁ c₂ c₃ : R)
  定义体: ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
-/
def equivProd {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ R × R × R × R where
  toFun a := ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩

/-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
@[simps symm_apply]
/--
Definition of `equivTuple` / `equivTuple` 的定义

English:
definition equivTuple
  signature: {R : Type*} (c₁ c₂ c₃ : R)
  body: ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  right_inv _ := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]

中文:
定义 equivTuple
  签名: {R : 类型} (c₁ c₂ c₃ : R)
  定义体: ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  right_inv _ := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]
-/
def equivTuple {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ (Fin 4 -> R) where
  toFun a := ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  right_inv _ := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]
/--
theorem `equivTuple_apply` / 定理 `equivTuple_apply`

English:
theorem equivTuple_apply
  given: {R : Type*} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃])
  proof: rfl

@[simp]

中文:
定理 equivTuple_apply
  条件: {R : 类型} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃])
  证明: rfl

@[simp]
-/
theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃]) :
    equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

@[simp]
/--
theorem `mk.eta` / 定理 `mk.eta`

English:
theorem mk.eta
  given: {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃])
  statement: mk a.1 a.2 a.3 a.4 = a
  proof: rfl

中文:
定理 mk.eta
  条件: {R : 类型} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃])
  结论: mk a.1 a.2 a.3 a.4 = a
  证明: rfl
-/
theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃]) : mk a.1 a.2 a.3 a.4 = a := rfl

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : Subsingleton ℍ[R,c₁,c₂,c₃]
  body: (equivTuple c₁ c₂ c₃).subsingleton

中文:
实例 [子单例
  签名: R] : 子单例 ℍ[R,c₁,c₂,c₃]
  定义体: (equivTuple c₁ c₂ c₃).subsingleton

Depends on / 依赖: equivTuple, subsingleton
-/
instance [Subsingleton R] : Subsingleton ℍ[R,c₁,c₂,c₃] := (equivTuple c₁ c₂ c₃).subsingleton
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial ℍ[R,c₁,c₂,c₃]
  body: (equivTuple c₁ c₂ c₃).surjective.nontrivial

中文:
实例 [非平凡
  签名: R] : 非平凡 ℍ[R,c₁,c₂,c₃]
  定义体: (equivTuple c₁ c₂ c₃).surjective.nontrivial

Depends on / 依赖: equivTuple, nontrivial, surjective, surjective.nontrivial
-/
instance [Nontrivial R] : Nontrivial ℍ[R,c₁,c₂,c₃] := (equivTuple c₁ c₂ c₃).surjective.nontrivial

section Zero
variable [Zero R]

/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: (x : ℍ[R,c₁,c₂,c₃])
  body: ⟨0, x.imI, x.imJ, x.imK⟩

@[simp]

中文:
定义 im
  签名: (x : ℍ[R,c₁,c₂,c₃])
  定义体: ⟨0, x.imI, x.imJ, x.imK⟩

@[simp]

Depends on / 依赖: x.imI, x.imJ, x.imK
-/
def im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃] :=
  ⟨0, x.imI, x.imJ, x.imK⟩

@[simp]
/--
theorem `re_im` / 定理 `re_im`

English:
theorem re_im
  statement: a.im.re = 0
  proof: rfl

@[simp]

中文:
定理 re_im
  结论: a.im.re = 0
  证明: rfl

@[simp]
-/
theorem re_im : a.im.re = 0 :=
  rfl

@[simp]
/--
theorem `imI_im` / 定理 `imI_im`

English:
theorem imI_im
  statement: a.im.imI = a.imI
  proof: rfl

@[simp]

中文:
定理 imI_im
  结论: a.im.imI = a.imI
  证明: rfl

@[simp]
-/
theorem imI_im : a.im.imI = a.imI :=
  rfl

@[simp]
/--
theorem `imJ_im` / 定理 `imJ_im`

English:
theorem imJ_im
  statement: a.im.imJ = a.imJ
  proof: rfl

@[simp]

中文:
定理 imJ_im
  结论: a.im.imJ = a.imJ
  证明: rfl

@[simp]
-/
theorem imJ_im : a.im.imJ = a.imJ :=
  rfl

@[simp]
/--
theorem `imK_im` / 定理 `imK_im`

English:
theorem imK_im
  statement: a.im.imK = a.imK
  proof: rfl

@[simp]

中文:
定理 imK_im
  结论: a.im.imK = a.imK
  证明: rfl

@[simp]
-/
theorem imK_im : a.im.imK = a.imK :=
  rfl

@[simp]
/--
theorem `im_idem` / 定理 `im_idem`

English:
theorem im_idem
  statement: a.im.im = a.im
  proof: rfl

中文:
定理 im_idem
  结论: a.im.im = a.im
  证明: rfl
-/
theorem im_idem : a.im.im = a.im :=
  rfl

/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: (x : R)
  body: ⟨x, 0, 0, 0⟩

中文:
定义 coe
  签名: (x : R)
  定义体: ⟨x, 0, 0, 0⟩
-/
@[coe] def coe (x : R) : ℍ[R,c₁,c₂,c₃] := ⟨x, 0, 0, 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC R ℍ[R,c₁,c₂,c₃]
  body: ⟨coe⟩

@[simp, norm_cast]

中文:
实例 :
  签名: CoeTC R ℍ[R,c₁,c₂,c₃]
  定义体: ⟨coe⟩

@[simp, norm_cast]
-/
instance : CoeTC R ℍ[R,c₁,c₂,c₃] := ⟨coe⟩

@[simp, norm_cast]
/--
theorem `re_coe` / 定理 `re_coe`

English:
theorem re_coe
  statement: (x : ℍ[R,c₁,c₂,c₃]).re = x
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_coe
  结论: (x : ℍ[R,c₁,c₂,c₃]).re = x
  证明: rfl

@[simp, norm_cast]
-/
theorem re_coe : (x : ℍ[R,c₁,c₂,c₃]).re = x := rfl

@[simp, norm_cast]
/--
theorem `imI_coe` / 定理 `imI_coe`

English:
theorem imI_coe
  statement: (x : ℍ[R,c₁,c₂,c₃]).imI = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_coe
  结论: (x : ℍ[R,c₁,c₂,c₃]).imI = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_coe : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[simp, norm_cast]
/--
theorem `imJ_coe` / 定理 `imJ_coe`

English:
theorem imJ_coe
  statement: (x : ℍ[R,c₁,c₂,c₃]).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_coe
  结论: (x : ℍ[R,c₁,c₂,c₃]).imJ = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imJ_coe : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[simp, norm_cast]
/--
theorem `imK_coe` / 定理 `imK_coe`

English:
theorem imK_coe
  statement: (x : ℍ[R,c₁,c₂,c₃]).imK = 0
  proof: rfl

中文:
定理 imK_coe
  结论: (x : ℍ[R,c₁,c₂,c₃]).imK = 0
  证明: rfl
-/
theorem imK_coe : (x : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective (coe : R -> ℍ[R,c₁,c₂,c₃])
  proof: fun _ _ h => congr_arg re h

@[simp]

中文:
定理 coe_injective
  结论: 函数.单射 (coe : R -> ℍ[R,c₁,c₂,c₃])
  证明: fun _ _ h => congr_arg re h

@[simp]

Depends on / 依赖: congr_arg
-/
theorem coe_injective : Function.Injective (coe : R -> ℍ[R,c₁,c₂,c₃]) := fun _ _ h => congr_arg re h

@[simp]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {x y : R}
  statement: (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y
  proof: coe_injective.eq_iff

@[simps]

中文:
定理 coe_inj
  条件: {x y : R}
  结论: (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y
  证明: coe_injective.eq_iff

@[simps]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero ℍ[R,c₁,c₂,c₃]
  body: ⟨⟨0, 0, 0, 0⟩⟩

中文:
实例 :
  签名: 零 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨⟨0, 0, 0, 0⟩⟩
-/
instance : Zero ℍ[R,c₁,c₂,c₃] := ⟨⟨0, 0, 0, 0⟩⟩

/--
theorem `im_zero` / 定理 `im_zero`

English:
theorem im_zero
  statement: (0 : ℍ[R,c₁,c₂,c₃]).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 im_zero
  结论: (0 : ℍ[R,c₁,c₂,c₃]).im = 0
  证明: rfl

@[simp, norm_cast]
-/
@[scoped simp] theorem im_zero : (0 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ℍ[R,c₁,c₂,c₃]
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨0⟩
-/
instance : Inhabited ℍ[R,c₁,c₂,c₃] := ⟨0⟩

section One
variable [One R]

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One ℍ[R,c₁,c₂,c₃]
  body: ⟨⟨1, 0, 0, 0⟩⟩

中文:
实例 :
  签名: 幺 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨⟨1, 0, 0, 0⟩⟩
-/
instance : One ℍ[R,c₁,c₂,c₃] := ⟨⟨1, 0, 0, 0⟩⟩

/--
theorem `im_one` / 定理 `im_one`

English:
theorem im_one
  statement: (1 : ℍ[R,c₁,c₂,c₃]).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 im_one
  结论: (1 : ℍ[R,c₁,c₂,c₃]).im = 0
  证明: rfl

@[simp, norm_cast]
-/
@[scoped simp] theorem im_one : (1 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1
  证明: rfl
-/
theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1 := rfl

end One
end Zero
section Add
variable [Add R]

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add ℍ[R,c₁,c₂,c₃]
  body: ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp]

中文:
实例 :
  签名: 加法 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp]
-/
instance : Add ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp]
/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  given: (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R)
  proof: rfl

中文:
定理 mk_add_mk
  条件: (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R)
  证明: rfl
-/
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + mk b₁ b₂ b₃ b₄ =
    mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

/--
Definition of `addEquivTuple` / `addEquivTuple` 的定义

English:
definition addEquivTuple
  signature: (c₁ c₂ c₃ : R)
  body: (equivTuple ..).addEquiv

@[simp]

中文:
定义 addEquivTuple
  签名: (c₁ c₂ c₃ : R)
  定义体: (equivTuple ..).addEquiv

@[simp]

Depends on / 依赖: addEquiv, equivTuple
-/
def addEquivTuple (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ (Fin 4 -> R) := (equivTuple ..).addEquiv

@[simp]
/--
lemma `coe_addEquivTuple` / 引理 `coe_addEquivTuple`

English:
lemma coe_addEquivTuple
  given: (c₁ c₂ c₃ : R)
  statement: ⇑(addEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃
  proof: rfl

中文:
引理 coe_addEquivTuple
  条件: (c₁ c₂ c₃ : R)
  结论: ⇑(addEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃
  证明: rfl
-/
lemma coe_addEquivTuple (c₁ c₂ c₃ : R) : ⇑(addEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := rfl

/--
lemma `coe_symm_addEquivTuple` / 引理 `coe_symm_addEquivTuple`

English:
lemma coe_symm_addEquivTuple
  given: (c₁ c₂ c₃ : R)
  proof: rfl

中文:
引理 coe_symm_addEquivTuple
  条件: (c₁ c₂ c₃ : R)
  证明: rfl
-/
@[simp] lemma coe_symm_addEquivTuple (c₁ c₂ c₃ : R) :
    ⇑(addEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/--
Definition of `addEquivProd` / `addEquivProd` 的定义

English:
definition addEquivProd
  signature: (c₁ c₂ c₃ : R)
  body: (equivProd ..).addEquiv

@[simp]

中文:
定义 addEquivProd
  签名: (c₁ c₂ c₃ : R)
  定义体: (equivProd ..).addEquiv

@[simp]

Depends on / 依赖: addEquiv, equivProd
-/
def addEquivProd (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ R × R × R × R := (equivProd ..).addEquiv

@[simp]
/--
lemma `coe_addEquivProd` / 引理 `coe_addEquivProd`

English:
lemma coe_addEquivProd
  given: (c₁ c₂ c₃ : R)
  statement: ⇑(addEquivProd c₁ c₂ c₃) = equivProd c₁ c₂ c₃
  proof: rfl

中文:
引理 coe_addEquivProd
  条件: (c₁ c₂ c₃ : R)
  结论: ⇑(addEquivProd c₁ c₂ c₃) = equivProd c₁ c₂ c₃
  证明: rfl
-/
lemma coe_addEquivProd (c₁ c₂ c₃ : R) : ⇑(addEquivProd c₁ c₂ c₃) = equivProd c₁ c₂ c₃ := rfl

/--
lemma `coe_symm_addEquivProd` / 引理 `coe_symm_addEquivProd`

English:
lemma coe_symm_addEquivProd
  given: (c₁ c₂ c₃ : R)
  proof: rfl

中文:
引理 coe_symm_addEquivProd
  条件: (c₁ c₂ c₃ : R)
  证明: rfl
-/
@[simp] lemma coe_symm_addEquivProd (c₁ c₂ c₃ : R) :
    ⇑(addEquivProd c₁ c₂ c₃).symm = (equivProd c₁ c₂ c₃).symm := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

/--
theorem `im_add` / 定理 `im_add`

English:
theorem im_add
  statement: (a + b).im = a.im + b.im
  proof: QuaternionAlgebra.ext (zero_add _).symm rfl rfl rfl

@[simp, norm_cast]

中文:
定理 im_add
  结论: (a + b).im = a.im + b.im
  证明: QuaternionAlgebra.ext (zero_add _).symm rfl rfl rfl

@[simp, norm_cast]
-/
@[simp] theorem im_add : (a + b).im = a.im + b.im :=
  QuaternionAlgebra.ext (zero_add _).symm rfl rfl rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y
  proof: by ext <;> simp

中文:
定理 coe_add
  结论: ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y
  证明: by ext <;> simp
-/
theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y := by ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg ℍ[R,c₁,c₂,c₃]
  body: ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp]

中文:
实例 :
  签名: 取负 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp]
-/
instance : Neg ℍ[R,c₁,c₂,c₃] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp]
/--
theorem `neg_mk` / 定理 `neg_mk`

English:
theorem neg_mk
  given: (a₁ a₂ a₃ a₄ : R)
  statement: -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩
  proof: rfl

中文:
定理 neg_mk
  条件: (a₁ a₂ a₃ a₄ : R)
  结论: -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩
  证明: rfl
-/
theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
  rfl

end Neg

section AddGroup
variable [AddGroup R]

/--
theorem `im_neg` / 定理 `im_neg`

English:
theorem im_neg
  statement: (-a).im = -a.im
  proof: QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp, norm_cast]

中文:
定理 im_neg
  结论: (-a).im = -a.im
  证明: QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp, norm_cast]
-/
@[simp] theorem im_neg : (-a).im = -a.im :=
  QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x
  proof: by ext <;> simp

@[simps]

中文:
定理 coe_neg
  结论: ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x
  证明: by ext <;> simp

@[simps]
-/
theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x := by ext <;> simp

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub ℍ[R,c₁,c₂,c₃]
  body: ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

中文:
实例 :
  签名: 减法 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩
-/
instance : Sub ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

/--
theorem `im_sub` / 定理 `im_sub`

English:
theorem im_sub
  statement: (a - b).im = a.im - b.im
  proof: QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl

@[simp]

中文:
定理 im_sub
  结论: (a - b).im = a.im - b.im
  证明: QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl

@[simp]
-/
@[simp] theorem im_sub : (a - b).im = a.im - b.im :=
  QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl

@[simp]
/--
theorem `mk_sub_mk` / 定理 `mk_sub_mk`

English:
theorem mk_sub_mk
  given: (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_sub_mk
  条件: (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) - mk b₁ b₂ b₃ b₄ =
    mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl

@[simp, norm_cast]
/--
theorem `im_coe` / 定理 `im_coe`

English:
theorem im_coe
  statement: (x : ℍ[R,c₁,c₂,c₃]).im = 0
  proof: rfl

@[simp]

中文:
定理 im_coe
  结论: (x : ℍ[R,c₁,c₂,c₃]).im = 0
  证明: rfl

@[simp]
-/
theorem im_coe : (x : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[simp]
/--
theorem `re_add_im` / 定理 `re_add_im`

English:
theorem re_add_im
  statement: ↑a.re + a.im = a
  proof: QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

@[simp]

中文:
定理 re_add_im
  结论: ↑a.re + a.im = a
  证明: QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, add_zero, zero_add
-/
theorem re_add_im : ↑a.re + a.im = a :=
  QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

@[simp]
/--
theorem `sub_im_self` / 定理 `sub_im_self`

English:
theorem sub_im_self
  statement: a - a.im = a.re
  proof: QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

@[simp]

中文:
定理 sub_im_self
  结论: a - a.im = a.re
  证明: QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, sub_self, sub_zero
-/
theorem sub_im_self : a - a.im = a.re :=
  QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

@[simp]
/--
theorem `sub_re_self` / 定理 `sub_re_self`

English:
theorem sub_re_self
  statement: a - a.re = a.im
  proof: QuaternionAlgebra.ext (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

中文:
定理 sub_re_self
  结论: a - a.re = a.im
  证明: QuaternionAlgebra.ext (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, sub_self, sub_zero
-/
theorem sub_re_self : a - a.re = a.im :=
  QuaternionAlgebra.ext (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

end AddGroup

section Ring
variable [Ring R]

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁ + c₂ * i`;
* `j * j = c₃`;
* `i * j = k`, `j * i = c₂ * j - k`;
* `k * k = - c₁ * c₃`;
* `i * k = c₁ * j + c₂ * k`, `k * i = -c₁ * j`;
* `j * k = c₂ * c₃ - c₃ * i`, `k * j = c₃ * i`. -/
@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul ℍ[R,c₁,c₂,c₃]
  body: ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]

中文:
实例 :
  签名: 乘法 ℍ[R,c₁,c₂,c₃]
  定义体: ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
-/
instance : Mul ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R)
  proof: rfl

中文:
定理 mk_mul_mk
  条件: (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R)
  证明: rfl
-/
theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) * mk b₁ b₂ b₃ b₄ =
    mk
      (a₁ * b₁ + c₁ * a₂ * b₂ + c₃ * a₃ * b₃ + c₂ * c₃ * a₃ * b₄ - c₁ * c₃ * a₄ * b₄)
      (a₁ * b₂ + a₂ * b₁ + c₂ * a₂ * b₂ - c₃ * a₃ * b₄ + c₃ * a₄ * b₃)
      (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ + c₂ * a₃ * b₂ - c₁ * a₄ * b₂)
      (a₁ * b₄ + a₂ * b₃ + c₂ * a₂ * b₄ - a₃ * b₂ + a₄ * b₁) :=
  rfl

end Ring
section SMul

variable [SMul S R] [SMul T R] (s : S)

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S ℍ[R,c₁,c₂,c₃]
  body: ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

中文:
实例 :
  签名: 标量乘法 S ℍ[R,c₁,c₂,c₃]
  定义体: ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩
-/
instance : SMul S ℍ[R,c₁,c₂,c₃] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
  body: by ext <;> exact smul_assoc _ _ _

中文:
实例 [标量乘法
  签名: S T] [标量塔 S T R] : 标量塔 S T ℍ[R,c₁,c₂,c₃] where
  定义体: by ext <;> exact smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
  smul_assoc s t x := by ext <;> exact smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
  body: by ext <;> exact smul_comm _ _ _

中文:
实例 [标量交换类
  签名: S T R] : 标量交换类 S T ℍ[R,c₁,c₂,c₃] where
  定义体: by ext <;> exact smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
  smul_comm s t x := by ext <;> exact smul_comm _ _ _

/--
theorem `im_smul` / 定理 `im_smul`

English:
theorem im_smul
  given: {S} [CommRing R] [SMulZeroClass S R] (s : S)
  statement: (s • a).im = s • a.im
  proof: QuaternionAlgebra.ext (smul_zero s).symm rfl rfl rfl

@[simp]

中文:
定理 im_smul
  条件: {S} [交换环 R] [SMulZero类 S R] (s : S)
  结论: (s • a).im = s • a.im
  证明: QuaternionAlgebra.ext (smul_zero s).symm rfl rfl rfl

@[simp]
-/
@[simp] theorem im_smul {S} [CommRing R] [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.ext (smul_zero s).symm rfl rfl rfl

@[simp]
/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  given: (re im_i im_j im_k : R)
  proof: rfl

中文:
定理 smul_mk
  条件: (re im_i im_j im_k : R)
  证明: rfl
-/
theorem smul_mk (re im_i im_j im_k : R) :
    s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
  rfl

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [MulAction S R] : MulAction S ℍ[R,c₁,c₂,c₃]
  body: (equivProd ..).injective.mulAction _ fun _ _ => rfl

中文:
实例 [幺半群
  签名: S] [乘法作用 S R] : 乘法作用 S ℍ[R,c₁,c₂,c₃]
  定义体: (equivProd ..).injective.mulAction _ fun _ _ => rfl

Depends on / 依赖: equivProd, injective, injective.mulAction, mulAction
-/
instance [Monoid S] [MulAction S R] : MulAction S ℍ[R,c₁,c₂,c₃] :=
  (equivProd ..).injective.mulAction _ fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] : AddCommGroup ℍ[R,c₁,c₂,c₃]
  body: by
  apply (equivProd c₁ c₂ c₃).injective.addCommGroup <;> intros <;> rfl

@[simp, norm_cast]

中文:
实例 [加法交换群
  签名: R] : 加法交换群 ℍ[R,c₁,c₂,c₃]
  定义体: by
  apply (equivProd c₁ c₂ c₃).injective.addCommGroup <;> intros <;> rfl

@[simp, norm_cast]

Depends on / 依赖: addCommGroup, equivProd, injective, injective.addCommGroup, intros
-/
instance [AddCommGroup R] : AddCommGroup ℍ[R,c₁,c₂,c₃] := by
  apply (equivProd c₁ c₂ c₃).injective.addCommGroup <;> intros <;> rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [Zero R] [SMulZeroClass S R] (s : S) (r : R)
  proof: QuaternionAlgebra.ext rfl (smul_zero _).symm (smul_zero _).symm (smul_zero _).symm

中文:
定理 coe_smul
  条件: [零 R] [SMulZero类 S R] (s : S) (r : R)
  证明: QuaternionAlgebra.ext rfl (smul_zero _).symm (smul_zero _).symm (smul_zero _).symm

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, smul_zero
-/
theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃]) :=
  QuaternionAlgebra.ext rfl (smul_zero _).symm (smul_zero _).symm (smul_zero _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [AddCommGroup R] [DistribMulAction S R] : DistribMulAction S ℍ[R,c₁,c₂,c₃]
  body: (addEquivProd ..).injective.distribMulAction (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ => rfl

中文:
实例 [半环
  签名: S] [加法交换群 R] [分配乘法作用 S R] : 分配乘法作用 S ℍ[R,c₁,c₂,c₃]
  定义体: (addEquivProd ..).injective.distribMulAction (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ => rfl

Depends on / 依赖: addEquivProd, distribMulAction, injective, injective.distribMulAction, toAddMonoidHom
-/
instance [Semiring S] [AddCommGroup R] [DistribMulAction S R] : DistribMulAction S ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.distribMulAction (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [AddCommGroup R] [Module S R] : Module S ℍ[R,c₁,c₂,c₃]
  body: (addEquivProd ..).injective.module _ (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ => rfl

中文:
实例 [半环
  签名: S] [加法交换群 R] [模 S R] : 模 S ℍ[R,c₁,c₂,c₃]
  定义体: (addEquivProd ..).injective.module _ (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ => rfl

Depends on / 依赖: addEquivProd, injective, injective.module, module, toAddMonoidHom
-/
instance [Semiring S] [AddCommGroup R] [Module S R] : Module S ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.module _ (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ => rfl

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroupWithOne ℍ[R,c₁,c₂,c₃]
  body: ((n : R) : ℍ[R,c₁,c₂,c₃])
  natCast_zero := by simp
  natCast_succ := by simp
  intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
  intCast_negSucc n := by
    change coe _ = -coe _
    rw [Int.cast_negSucc]; rw [coe_neg]

@[simp, norm_cast]

中文:
实例 :
  签名: 加法交换带幺群 ℍ[R,c₁,c₂,c₃]
  定义体: ((n : R) : ℍ[R,c₁,c₂,c₃])
  natCast_zero := by simp
  natCast_succ := by simp
  intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
  intCast_negSucc n := by
    change coe _ = -coe _
    rw [Int.cast_negSucc]; rw [coe_neg]

@[simp, norm_cast]
-/
instance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃] where
  natCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  natCast_zero := by simp
  natCast_succ := by simp
  intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
  intCast_negSucc n := by
    change coe _ = -coe _
    rw [Int.cast_negSucc]; rw [coe_neg]

@[simp, norm_cast]
/--
theorem `re_natCast` / 定理 `re_natCast`

English:
theorem re_natCast
  given: (n : Nat)
  statement: (n : ℍ[R,c₁,c₂,c₃]).re = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R,c₁,c₂,c₃]).re = n
  证明: rfl

@[simp, norm_cast]
-/
theorem re_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).re = n :=
  rfl

@[simp, norm_cast]
/--
theorem `imI_natCast` / 定理 `imI_natCast`

English:
theorem imI_natCast
  given: (n : Nat)
  statement: (n : ℍ[R,c₁,c₂,c₃]).imI = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R,c₁,c₂,c₃]).imI = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `imJ_natCast` / 定理 `imJ_natCast`

English:
theorem imJ_natCast
  given: (n : Nat)
  statement: (n : ℍ[R,c₁,c₂,c₃]).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R,c₁,c₂,c₃]).imJ = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imJ_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `imK_natCast` / 定理 `imK_natCast`

English:
theorem imK_natCast
  given: (n : Nat)
  statement: (n : ℍ[R,c₁,c₂,c₃]).imK = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imK_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R,c₁,c₂,c₃]).imK = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imK_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `im_natCast` / 定理 `im_natCast`

English:
theorem im_natCast
  given: (n : Nat)
  statement: (n : ℍ[R,c₁,c₂,c₃]).im = 0
  proof: rfl

@[norm_cast]

中文:
定理 im_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R,c₁,c₂,c₃]).im = 0
  证明: rfl

@[norm_cast]
-/
theorem im_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃])
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃])
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_natCast (n : Nat) : ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃]) :=
  rfl

@[simp, norm_cast]
/--
theorem `re_intCast` / 定理 `re_intCast`

English:
theorem re_intCast
  given: (z : Int)
  statement: (z : ℍ[R,c₁,c₂,c₃]).re = z
  proof: rfl

@[scoped simp]

中文:
定理 re_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R,c₁,c₂,c₃]).re = z
  证明: rfl

@[scoped simp]
-/
theorem re_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).re = z :=
  rfl

@[scoped simp]
/--
theorem `re_ofNat` / 定理 `re_ofNat`

English:
theorem re_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(n)
  proof: rfl

@[scoped simp]

中文:
定理 re_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : ℍ[R,c₁,c₂,c₃]).re = of自然数(n)
  证明: rfl

@[scoped simp]
-/
theorem re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(n) := rfl

@[scoped simp]
/--
theorem `imI_ofNat` / 定理 `imI_ofNat`

English:
theorem imI_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0
  proof: rfl

@[scoped simp]

中文:
定理 imI_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : ℍ[R,c₁,c₂,c₃]).imI = 0
  证明: rfl

@[scoped simp]
-/
theorem imI_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[scoped simp]
/--
theorem `imJ_ofNat` / 定理 `imJ_ofNat`

English:
theorem imJ_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0
  proof: rfl

@[scoped simp]

中文:
定理 imJ_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0
  证明: rfl

@[scoped simp]
-/
theorem imJ_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[scoped simp]
/--
theorem `imK_ofNat` / 定理 `imK_ofNat`

English:
theorem imK_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0
  proof: rfl

@[scoped simp]

中文:
定理 imK_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : ℍ[R,c₁,c₂,c₃]).imK = 0
  证明: rfl

@[scoped simp]
-/
theorem imK_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

@[scoped simp]
/--
theorem `im_ofNat` / 定理 `im_ofNat`

English:
theorem im_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : ℍ[R,c₁,c₂,c₃]).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 im_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : ℍ[R,c₁,c₂,c₃]).im = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
/--
theorem `imI_intCast` / 定理 `imI_intCast`

English:
theorem imI_intCast
  given: (z : Int)
  statement: (z : ℍ[R,c₁,c₂,c₃]).imI = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R,c₁,c₂,c₃]).imI = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `imJ_intCast` / 定理 `imJ_intCast`

English:
theorem imJ_intCast
  given: (z : Int)
  statement: (z : ℍ[R,c₁,c₂,c₃]).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R,c₁,c₂,c₃]).imJ = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imJ_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `imK_intCast` / 定理 `imK_intCast`

English:
theorem imK_intCast
  given: (z : Int)
  statement: (z : ℍ[R,c₁,c₂,c₃]).imK = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imK_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R,c₁,c₂,c₃]).imK = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imK_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `im_intCast` / 定理 `im_intCast`

English:
theorem im_intCast
  given: (z : Int)
  statement: (z : ℍ[R,c₁,c₂,c₃]).im = 0
  proof: rfl

@[norm_cast]

中文:
定理 im_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R,c₁,c₂,c₃]).im = 0
  证明: rfl

@[norm_cast]
-/
theorem im_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (z : Int)
  statement: ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃])
  proof: rfl

中文:
定理 coe_intCast
  条件: (z : 整数)
  结论: ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃])
  证明: rfl
-/
theorem coe_intCast (z : Int) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃]) :=
  rfl

end AddCommGroupWithOne

-- For the remainder of the file we assume `CommRing R`.
variable [CommRing R]

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring ℍ[R,c₁,c₂,c₃] where
  body: (inferInstance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[norm_cast, simp]

中文:
实例 instRing
  签名: : 环 ℍ[R,c₁,c₂,c₃] where
  定义体: (inferInstance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[norm_cast, simp]

Depends on / 依赖: AddCommGroupWithOne
-/
instance instRing : Ring ℍ[R,c₁,c₂,c₃] where
  __ := (inferInstance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[norm_cast, simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y
  proof: by ext <;> simp

@[norm_cast, simp]

中文:
定理 coe_mul
  结论: ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y
  证明: by ext <;> simp

@[norm_cast, simp]
-/
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y := by ext <;> simp

@[norm_cast, simp]
/--
lemma `coe_ofNat` / 引理 `coe_ofNat`

English:
lemma coe_ofNat
  given: {n : Nat} [n.AtLeastTwo]
  proof: rfl

中文:
引理 coe_of自然数
  条件: {n : 自然数} [n.AtLeastTwo]
  证明: rfl
-/
lemma coe_ofNat {n : Nat} [n.AtLeastTwo] :
    ((ofNat(n) : R) : ℍ[R,c₁,c₂,c₃]) = (ofNat(n) : ℍ[R,c₁,c₂,c₃]) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂,c₃] where
  body: { toFun s := coe (algebraMap S R s)
    map_one' := by simp only [map_one, coe_one]
    map_zero' := by simp only [map_zero, coe_zero]
    map_mul' x y := by simp only [map_mul, coe_mul]
    map_add' x y := by simp only [map_add, coe_add] }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [Algebra.commutes]

中文:
实例 [交换半环
  签名: S] [代数 S R] : 代数 S ℍ[R,c₁,c₂,c₃] where
  定义体: { toFun s := coe (algebraMap S R s)
    map_one' := by simp only [map_one, coe_one]
    map_zero' := by simp only [map_zero, coe_zero]
    map_mul' x y := by simp only [map_mul, coe_mul]
    map_add' x y := by simp only [map_add, coe_add] }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [Algebra.commutes]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, algebraMap, coe_add, coe_mul, coe_one, coe_zero, commutes, map_add, map_mul, map_one, map_zero, smul_def
-/
instance [CommSemiring S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂,c₃] where
  algebraMap :=
  { toFun s := coe (algebraMap S R s)
    map_one' := by simp only [map_one, coe_one]
    map_zero' := by simp only [map_zero, coe_zero]
    map_mul' x y := by simp only [map_mul, coe_mul]
    map_add' x y := by simp only [map_add, coe_add] }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [Algebra.commutes]

/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  given: (r : R)
  statement: algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩
  proof: rfl

中文:
定理 algebraMap_eq
  条件: (r : R)
  结论: algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩
  证明: rfl
-/
theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩ :=
  rfl

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: (algebraMap R ℍ[R,c₁,c₂,c₃] : _ -> _).Injective
  proof: fun _ _ => by simp [algebraMap_eq]

中文:
定理 algebraMap_injective
  结论: (algebraMap R ℍ[R,c₁,c₂,c₃] : _ -> _).单射
  证明: fun _ _ => by simp [algebraMap_eq]

Depends on / 依赖: algebraMap_eq
-/
theorem algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ -> _).Injective :=
  fun _ _ => by simp [algebraMap_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree R ℍ[R,c₁,c₂,c₃]
  body: (addEquivProd ..).injective.moduleIsTorsionFree _ fun _ _ => rfl

中文:
实例 :
  签名: 是无挠 R ℍ[R,c₁,c₂,c₃]
  定义体: (addEquivProd ..).injective.moduleIsTorsionFree _ fun _ _ => rfl

Depends on / 依赖: addEquivProd, injective, injective.moduleIsTorsionFree, moduleIsTorsionFree
-/
instance : IsTorsionFree R ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.moduleIsTorsionFree _ fun _ _ => rfl

section

variable (c₁ c₂ c₃)

/-- `QuaternionAlgebra.re` as a `LinearMap` -/
@[simps]
/--
Definition of `reₗ` / `reₗ` 的定义

English:
definition reₗ
  signature: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  body: re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 reₗ
  签名: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  定义体: re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def reₗ : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imI` as a `LinearMap` -/
@[simps]
/--
Definition of `imIₗ` / `imIₗ` 的定义

English:
definition imIₗ
  signature: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  body: imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 imIₗ
  签名: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  定义体: imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def imIₗ : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  toFun := imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imJ` as a `LinearMap` -/
@[simps]
/--
Definition of `imJₗ` / `imJₗ` 的定义

English:
definition imJₗ
  signature: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  body: imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 imJₗ
  签名: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  定义体: imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def imJₗ : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  toFun := imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imK` as a `LinearMap` -/
@[simps]
/--
Definition of `imKₗ` / `imKₗ` 的定义

English:
definition imKₗ
  signature: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  body: imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 imKₗ
  签名: : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  定义体: imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def imKₗ : ℍ[R,c₁,c₂,c₃] ->ₗ[R] R where
  toFun := imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Definition of `linearEquivTuple` / `linearEquivTuple` 的定义

English:
definition linearEquivTuple
  signature: : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 -> R
  body: (equivTuple ..).linearEquiv _

@[simp]

中文:
定义 linearEquivTuple
  签名: : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] 有限集 4 -> R
  定义体: (equivTuple ..).linearEquiv _

@[simp]

Depends on / 依赖: equivTuple, linearEquiv
-/
def linearEquivTuple : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 -> R := (equivTuple ..).linearEquiv _

@[simp]
/--
theorem `coe_linearEquivTuple` / 定理 `coe_linearEquivTuple`

English:
theorem coe_linearEquivTuple
  proof: rfl

@[simp]

中文:
定理 coe_linearEquivTuple
  证明: rfl

@[simp]
-/
theorem coe_linearEquivTuple :
    ⇑(linearEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := rfl

@[simp]
/--
theorem `coe_linearEquivTuple_symm` / 定理 `coe_linearEquivTuple_symm`

English:
theorem coe_linearEquivTuple_symm
  proof: rfl

中文:
定理 coe_linearEquivTuple_symm
  证明: rfl
-/
theorem coe_linearEquivTuple_symm :
    ⇑(linearEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/--
Definition of `basisOneIJK` / `basisOneIJK` 的定义

English:
definition basisOneIJK
  signature: : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃]
  body: .ofEquivFun linearEquivTuple c₁ c₂ c₃

@[simp]

中文:
定义 basisOneIJK
  签名: : 基 (有限集 4) R ℍ[R,c₁,c₂,c₃]
  定义体: .ofEquivFun linearEquivTuple c₁ c₂ c₃

@[simp]

Depends on / 依赖: NonUnitalNonAssocSemiring, linearEquivTuple, ofEquivFun
-/
noncomputable def basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃] :=
.ofEquivFun linearEquivTuple c₁ c₂ c₃

@[simp]
/--
theorem `coe_basisOneIJK_repr` / 定理 `coe_basisOneIJK_repr`

English:
theorem coe_basisOneIJK_repr
  given: (q : ℍ[R,c₁,c₂,c₃])
  proof: rfl

中文:
定理 coe_basisOneIJK_repr
  条件: (q : ℍ[R,c₁,c₂,c₃])
  证明: rfl
-/
theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) :
    ((basisOneIJK c₁ c₂ c₃).repr q) = ![q.re, q.imI, q.imJ, q.imK] :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R ℍ[R,c₁,c₂,c₃]
  body: .of_basis (basisOneIJK c₁ c₂ c₃)

中文:
实例 :
  签名: 模.有限 R ℍ[R,c₁,c₂,c₃]
  定义体: .of_basis (basisOneIJK c₁ c₂ c₃)

Depends on / 依赖: basisOneIJK, of_basis
-/
instance : Module.Finite R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R ℍ[R,c₁,c₂,c₃]
  body: .of_basis (basisOneIJK c₁ c₂ c₃)

中文:
实例 :
  签名: 模.自由 R ℍ[R,c₁,c₂,c₃]
  定义体: .of_basis (basisOneIJK c₁ c₂ c₃)

Depends on / 依赖: basisOneIJK, of_basis
-/
instance : Module.Free R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)

/--
theorem `rank_eq_four` / 定理 `rank_eq_four`

English:
theorem rank_eq_four
  given: [StrongRankCondition R]
  statement: Module.rank R ℍ[R,c₁,c₂,c₃] = 4
  proof: by
  rw [rank_eq_card_basis (basisOneIJK c₁ c₂ c₃)]; rw [Fintype.card_fin]
  norm_num

中文:
定理 rank_eq_four
  条件: [StrongRankCondition R]
  结论: 模.rank R ℍ[R,c₁,c₂,c₃] = 4
  证明: by
  rw [rank_eq_card_basis (basisOneIJK c₁ c₂ c₃)]; rw [Fintype.card_fin]
  norm_num

Depends on / 依赖: Fintype, Fintype.card_fin, basisOneIJK, card_fin, rank_eq_card_basis
-/
theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [rank_eq_card_basis (basisOneIJK c₁ c₂ c₃)]; rw [Fintype.card_fin]
  norm_num

/--
theorem `finrank_eq_four` / 定理 `finrank_eq_four`

English:
theorem finrank_eq_four
  given: [StrongRankCondition R]
  statement: Module.finrank R ℍ[R,c₁,c₂,c₃] = 4
  proof: by
  rw [Module.finrank]; rw [rank_eq_four]; rw [Cardinal.toNat_ofNat]

中文:
定理 finrank_eq_four
  条件: [StrongRankCondition R]
  结论: 模.finrank R ℍ[R,c₁,c₂,c₃] = 4
  证明: by
  rw [Module.finrank]; rw [rank_eq_four]; rw [Cardinal.toNat_ofNat]

Depends on / 依赖: Cardinal, Cardinal.toNat_ofNat, Module, Module.finrank, finrank, rank_eq_four, toNat_ofNat
-/
theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [Module.finrank]; rw [rank_eq_four]; rw [Cardinal.toNat_ofNat]

/-- There is a natural equivalence when swapping the first and third coefficients of a
  quaternion algebra if `c₂` is 0. -/
@[simps]
/--
Definition of `swapEquiv` / `swapEquiv` 的定义

English:
definition swapEquiv
  signature: : ℍ[R,c₁,0,c₃] ≃ₐ[R] ℍ[R,c₃,0,c₁] where
  body: ⟨t.1, t.3, t.2, -t.4⟩
  invFun t := ⟨t.1, t.3, t.2, -t.4⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by ext <;> simp <;> ring
  map_add' _ _ := by ext <;> simp [add_comm]
  commutes' _ := by simp [algebraMap_eq]

中文:
定义 swapEquiv
  签名: : ℍ[R,c₁,0,c₃] ≃ₐ[R] ℍ[R,c₃,0,c₁] where
  定义体: ⟨t.1, t.3, t.2, -t.4⟩
  invFun t := ⟨t.1, t.3, t.2, -t.4⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by ext <;> simp <;> ring
  map_add' _ _ := by ext <;> simp [add_comm]
  commutes' _ := by simp [algebraMap_eq]
-/
def swapEquiv : ℍ[R,c₁,0,c₃] ≃ₐ[R] ℍ[R,c₃,0,c₁] where
  toFun t := ⟨t.1, t.3, t.2, -t.4⟩
  invFun t := ⟨t.1, t.3, t.2, -t.4⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by ext <;> simp <;> ring
  map_add' _ _ := by ext <;> simp [add_comm]
  commutes' _ := by simp [algebraMap_eq]

end

@[norm_cast, simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y
  proof: (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

@[norm_cast, simp]

中文:
定理 coe_sub
  结论: ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y
  证明: (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

@[norm_cast, simp]

Depends on / 依赖: algebraMap, map_sub
-/
theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y :=
  (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

@[norm_cast, simp]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (n : Nat)
  statement: (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n
  proof: (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n

中文:
定理 coe_pow
  条件: (n : 自然数)
  结论: (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n
  证明: (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n

Depends on / 依赖: algebraMap, map_pow
-/
theorem coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n :=
  (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n

/--
theorem `coe_commutes` / 定理 `coe_commutes`

English:
theorem coe_commutes
  statement: ↑r * a = a * r
  proof: Algebra.commutes r a

中文:
定理 coe_commutes
  结论: ↑r * a = a * r
  证明: Algebra.commutes r a

Depends on / 依赖: Algebra, Algebra.commutes, commutes
-/
theorem coe_commutes : ↑r * a = a * r :=
  Algebra.commutes r a

/--
theorem `coe_commute` / 定理 `coe_commute`

English:
theorem coe_commute
  statement: Commute (↑r) a
  proof: coe_commutes r a

中文:
定理 coe_commute
  结论: Commute (↑r) a
  证明: coe_commutes r a

Depends on / 依赖: coe_commutes
-/
theorem coe_commute : Commute (↑r) a :=
  coe_commutes r a

/--
theorem `coe_mul_eq_smul` / 定理 `coe_mul_eq_smul`

English:
theorem coe_mul_eq_smul
  statement: ↑r * a = r • a
  proof: (Algebra.smul_def r a).symm

中文:
定理 coe_mul_eq_smul
  结论: ↑r * a = r • a
  证明: (Algebra.smul_def r a).symm

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def
-/
theorem coe_mul_eq_smul : ↑r * a = r • a :=
  (Algebra.smul_def r a).symm

/--
theorem `mul_coe_eq_smul` / 定理 `mul_coe_eq_smul`

English:
theorem mul_coe_eq_smul
  statement: a * r = r • a
  proof: by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp]

中文:
定理 mul_coe_eq_smul
  结论: a * r = r • a
  证明: by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp]

Depends on / 依赖: coe_commutes, coe_mul_eq_smul
-/
theorem mul_coe_eq_smul : a * r = r • a := by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  statement: ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe
  proof: rfl

中文:
定理 coe_algebraMap
  结论: ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe
  证明: rfl
-/
theorem coe_algebraMap : ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe :=
  rfl

/--
theorem `smul_coe` / 定理 `smul_coe`

English:
theorem smul_coe
  statement: x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y)
  proof: by rw [coe_mul, coe_mul_eq_smul]

中文:
定理 smul_coe
  结论: x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y)
  证明: by rw [coe_mul, coe_mul_eq_smul]

Depends on / 依赖: coe_mul, coe_mul_eq_smul, e.symm
-/
theorem smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]

/--
Instance `instStarQuaternionAlgebra` / 实例 `instStarQuaternionAlgebra`

English:
instance instStarQuaternionAlgebra
  signature: : Star ℍ[R,c₁,c₂,c₃] where star a
  body: ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩

中文:
实例 instStarQuaternionAlgebra
  签名: : 对合 ℍ[R,c₁,c₂,c₃] where star a
  定义体: ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩
-/
instance instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂,c₃] where star a :=
  ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩

/--
theorem `re_star` / 定理 `re_star`

English:
theorem re_star
  statement: (star a).re = a.re + c₂ * a.imI
  proof: rfl

@[simp]

中文:
定理 re_star
  结论: (star a).re = a.re + c₂ * a.imI
  证明: rfl

@[simp]
-/
@[simp] theorem re_star : (star a).re = a.re + c₂ * a.imI := rfl

@[simp]
/--
theorem `imI_star` / 定理 `imI_star`

English:
theorem imI_star
  statement: (star a).imI = -a.imI
  proof: rfl

@[simp]

中文:
定理 imI_star
  结论: (star a).imI = -a.imI
  证明: rfl

@[simp]
-/
theorem imI_star : (star a).imI = -a.imI :=
  rfl

@[simp]
/--
theorem `imJ_star` / 定理 `imJ_star`

English:
theorem imJ_star
  statement: (star a).imJ = -a.imJ
  proof: rfl

@[simp]

中文:
定理 imJ_star
  结论: (star a).imJ = -a.imJ
  证明: rfl

@[simp]
-/
theorem imJ_star : (star a).imJ = -a.imJ :=
  rfl

@[simp]
/--
theorem `imK_star` / 定理 `imK_star`

English:
theorem imK_star
  statement: (star a).imK = -a.imK
  proof: rfl

@[simp]

中文:
定理 imK_star
  结论: (star a).imK = -a.imK
  证明: rfl

@[simp]
-/
theorem imK_star : (star a).imK = -a.imK :=
  rfl

@[simp]
/--
theorem `im_star` / 定理 `im_star`

English:
theorem im_star
  statement: (star a).im = -a.im
  proof: QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp]

中文:
定理 im_star
  结论: (star a).im = -a.im
  证明: QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, neg_zero, neg_zero.symm
-/
theorem im_star : (star a).im = -a.im :=
  QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp]
/--
theorem `star_mk` / 定理 `star_mk`

English:
theorem star_mk
  given: (a₁ a₂ a₃ a₄ : R)
  statement: star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
  proof: rfl

中文:
定理 star_mk
  条件: (a₁ a₂ a₃ a₄ : R)
  结论: star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
  证明: rfl
-/
theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
    ⟨a₁ + c₂ * a₂, -a₂, -a₃, -a₄⟩ := rfl

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: : StarRing ℍ[R,c₁,c₂,c₃] where
  body: by simp [Star.star]
  star_add a b := by ext <;> simp [add_comm]; ring
  star_mul a b := by ext <;> simp <;> ring

中文:
实例 instStarRing
  签名: : 对合环 ℍ[R,c₁,c₂,c₃] where
  定义体: by simp [Star.star]
  star_add a b := by ext <;> simp [add_comm]; ring
  star_mul a b := by ext <;> simp <;> ring

Depends on / 依赖: Star.star, add_comm, star_add, star_mul
-/
instance instStarRing : StarRing ℍ[R,c₁,c₂,c₃] where
  star_involutive x := by simp [Star.star]
  star_add a b := by ext <;> simp [add_comm]; ring
  star_mul a b := by ext <;> simp <;> ring

/--
theorem `self_add_star'` / 定理 `self_add_star'`

English:
theorem self_add_star'
  statement: a + star a = ↑(2 * a.re + c₂ * a.imI)
  proof: by ext <;> simp [two_mul]; ring

中文:
定理 self_add_star'
  结论: a + star a = ↑(2 * a.re + c₂ * a.imI)
  证明: by ext <;> simp [two_mul]; ring

Depends on / 依赖: two_mul
-/
theorem self_add_star' : a + star a = ↑(2 * a.re + c₂ * a.imI) := by ext <;> simp [two_mul]; ring

/--
theorem `self_add_star` / 定理 `self_add_star`

English:
theorem self_add_star
  statement: a + star a = 2 * a.re + c₂ * a.imI
  proof: by simp [self_add_star']

中文:
定理 self_add_star
  结论: a + star a = 2 * a.re + c₂ * a.imI
  证明: by simp [self_add_star']

Depends on / 依赖: self_add_star
-/
theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by simp [self_add_star']

/--
theorem `star_add_self'` / 定理 `star_add_self'`

English:
theorem star_add_self'
  statement: star a + a = ↑(2 * a.re + c₂ * a.imI)
  proof: by rw [add_comm, self_add_star']

中文:
定理 star_add_self'
  结论: star a + a = ↑(2 * a.re + c₂ * a.imI)
  证明: by rw [add_comm, self_add_star']

Depends on / 依赖: add_comm, self_add_star
-/
theorem star_add_self' : star a + a = ↑(2 * a.re + c₂ * a.imI) := by rw [add_comm, self_add_star']

/--
theorem `star_add_self` / 定理 `star_add_self`

English:
theorem star_add_self
  statement: star a + a = 2 * a.re + c₂ * a.imI
  proof: by rw [add_comm, self_add_star]

中文:
定理 star_add_self
  结论: star a + a = 2 * a.re + c₂ * a.imI
  证明: by rw [add_comm, self_add_star]

Depends on / 依赖: add_comm, self_add_star
-/
theorem star_add_self : star a + a = 2 * a.re + c₂ * a.imI := by rw [add_comm, self_add_star]

/--
theorem `star_eq_two_re_sub` / 定理 `star_eq_two_re_sub`

English:
theorem star_eq_two_re_sub
  statement: star a = ↑(2 * a.re + c₂ * a.imI) - a
  proof: eq_sub_iff_add_eq.2 a.star_add_self'

中文:
定理 star_eq_two_re_sub
  结论: star a = ↑(2 * a.re + c₂ * a.imI) - a
  证明: eq_sub_iff_add_eq.2 a.star_add_self'

Depends on / 依赖: a.star_add_self, eq_sub_iff_add_eq, star_add_self
-/
theorem star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a :=
  eq_sub_iff_add_eq.2 a.star_add_self'

/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  given: (r : R) (x : ℍ[R,c₁,c₂,c₃])
  statement: r * x = x * r
  proof: by
  ext <;> simp [mul_comm]

中文:
引理 comm
  条件: (r : R) (x : ℍ[R,c₁,c₂,c₃])
  结论: r * x = x * r
  证明: by
  ext <;> simp [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma comm (r : R) (x : ℍ[R,c₁,c₂,c₃]) : r * x = x * r := by
  ext <;> simp [mul_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStarNormal a
  body: ⟨by
    rw [commute_iff_eq]; rw [a.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 是StarNormal a
  定义体: ⟨by
    rw [commute_iff_eq]; rw [a.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[simp, norm_cast]

Depends on / 依赖: a.star_eq_two_re_sub, commute_iff_eq, star_eq_two_re_sub
-/
instance : IsStarNormal a :=
  ⟨by
    rw [commute_iff_eq]; rw [a.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[simp, norm_cast]
/--
theorem `star_coe` / 定理 `star_coe`

English:
theorem star_coe
  statement: star (x : ℍ[R,c₁,c₂,c₃]) = x
  proof: by ext <;> simp

中文:
定理 star_coe
  结论: star (x : ℍ[R,c₁,c₂,c₃]) = x
  证明: by ext <;> simp
-/
theorem star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x := by ext <;> simp

/--
theorem `star_im` / 定理 `star_im`

English:
theorem star_im
  statement: star a.im = -a.im + c₂ * a.imI
  proof: by ext <;> simp

@[simp]

中文:
定理 star_im
  结论: star a.im = -a.im + c₂ * a.imI
  证明: by ext <;> simp

@[simp]
-/
@[simp] theorem star_im : star a.im = -a.im + c₂ * a.imI := by ext <;> simp

@[simp]
/--
theorem `star_smul` / 定理 `star_smul`

English:
theorem star_smul
  statement: [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
  proof: QuaternionAlgebra.ext
    (by simp [mul_smul_comm]) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

中文:
定理 star_smul
  结论: [幺半群 S] [分配乘法作用 S R] [标量交换类 S R R]
  证明: QuaternionAlgebra.ext
    (by simp [mul_smul_comm]) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, mul_smul_comm, smul_neg
-/
theorem star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (s : S) (a : ℍ[R,c₁,c₂,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext
    (by simp [mul_smul_comm]) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

/--
theorem `star_smul'` / 定理 `star_smul'`

English:
theorem star_smul'
  given: [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃])
  proof: QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

中文:
定理 star_smul'
  条件: [幺半群 S] [分配乘法作用 S R] (s : S) (a : ℍ[R,c₁,0,c₃])
  证明: QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext, smul_neg
-/
theorem star_smul' [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

/--
theorem `eq_re_of_eq_coe` / 定理 `eq_re_of_eq_coe`

English:
theorem eq_re_of_eq_coe
  given: {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x)
  statement: a = a.re
  proof: by rw [h, re_coe]

中文:
定理 eq_re_of_eq_coe
  条件: {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x)
  结论: a = a.re
  证明: by rw [h, re_coe]

Depends on / 依赖: re_coe
-/
theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re := by rw [h, re_coe]

/--
theorem `eq_re_iff_mem_range_coe` / 定理 `eq_re_iff_mem_range_coe`

English:
theorem eq_re_iff_mem_range_coe
  given: {a : ℍ[R,c₁,c₂,c₃]}
  proof: ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩

中文:
定理 eq_re_iff_mem_range_coe
  条件: {a : ℍ[R,c₁,c₂,c₃]}
  证明: ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩

Depends on / 依赖: a.re, eq_re_of_eq_coe, h.symm
-/
theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} :
    a = a.re ↔ a in Set.range (coe : R -> ℍ[R,c₁,c₂,c₃]) :=
  ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
/--
theorem `star_eq_self` / 定理 `star_eq_self`

English:
theorem star_eq_self
  given: {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]}
  statement: star a = a ↔ a = a.re
  proof: by
  simp_all [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

中文:
定理 star_eq_self
  条件: {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]}
  结论: star a = a ↔ a = a.re
  证明: by
  simp_all [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

Depends on / 依赖: CanLift, QuaternionAlgebra, QuaternionAlgebra.ext_iff, StarSubalgebra, add_self_eq_zero, ext_iff, neg_eq_iff_add_eq_zero
-/
theorem star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re := by
  simp_all [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

/--
theorem `star_eq_neg` / 定理 `star_eq_neg`

English:
theorem star_eq_neg
  given: {c₁ : R} {a : ℍ[R,c₁,0,c₃]}
  statement: star a = -a ↔ a.re = 0
  proof: by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

中文:
定理 star_eq_neg
  条件: {c₁ : R} {a : ℍ[R,c₁,0,c₃]}
  结论: star a = -a ↔ a.re = 0
  证明: by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero, ext_iff
-/
theorem star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} : star a = -a ↔ a.re = 0 := by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

end CharZero

-- Can't use `rw ← star_eq_self` in the proof without additional assumptions
/--
theorem `star_mul_eq_coe` / 定理 `star_mul_eq_coe`

English:
theorem star_mul_eq_coe
  statement: star a * a = (star a * a).re
  proof: by ext <;> simp <;> ring

中文:
定理 star_mul_eq_coe
  结论: star a * a = (star a * a).re
  证明: by ext <;> simp <;> ring
-/
theorem star_mul_eq_coe : star a * a = (star a * a).re := by ext <;> simp <;> ring

/--
theorem `mul_star_eq_coe` / 定理 `mul_star_eq_coe`

English:
theorem mul_star_eq_coe
  statement: a * star a = (a * star a).re
  proof: by
  rw [← star_comm_self']
  exact a.star_mul_eq_coe

中文:
定理 mul_star_eq_coe
  结论: a * star a = (a * star a).re
  证明: by
  rw [← star_comm_self']
  exact a.star_mul_eq_coe

Depends on / 依赖: a.star_mul_eq_coe, star_comm_self, star_mul_eq_coe
-/
theorem mul_star_eq_coe : a * star a = (a * star a).re := by
  rw [← star_comm_self']
  exact a.star_mul_eq_coe

open MulOpposite

/--
Definition of `starAe` / `starAe` 的定义

English:
definition starAe
  signature: : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ
  body: { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by simp
    commutes' := fun r => by simp }

@[simp]

中文:
定义 starAe
  签名: : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ
  定义体: { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by simp
    commutes' := fun r => by simp }

@[simp]

Depends on / 依赖: commutes, invFun, map_mul, opAddEquiv, starAddEquiv, starAddEquiv.trans
-/
def starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ :=
  { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by simp
    commutes' := fun r => by simp }

@[simp]
/--
theorem `coe_starAe` / 定理 `coe_starAe`

English:
theorem coe_starAe
  statement: ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star
  proof: rfl

中文:
定理 coe_starAe
  结论: ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star
  证明: rfl
-/
theorem coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star :=
  rfl

end QuaternionAlgebra

/--
Definition of `Quaternion` / `Quaternion` 的定义

English:
definition Quaternion
  signature: (R : Type*) [Zero R] [One R] [Neg R]
  body: QuaternionAlgebra R (-1) (0) (-1)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

中文:
定义 Quaternion
  签名: (R : 类型) [零 R] [幺 R] [取负 R]
  定义体: QuaternionAlgebra R (-1) (0) (-1)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

Depends on / 依赖: QuaternionAlgebra
-/
def Quaternion (R : Type*) [Zero R] [One R] [Neg R] :=
  QuaternionAlgebra R (-1) (0) (-1)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

open Quaternion

/-- The equivalence between the quaternions over `R` and `R × R × R × R`. -/
@[simps!]
/--
Definition of `Quaternion.equivProd` / `Quaternion.equivProd` 的定义

English:
definition Quaternion.equivProd
  signature: (R : Type*) [Zero R] [One R] [Neg R]
  body: QuaternionAlgebra.equivProd _ _ _

中文:
定义 Quaternion.equivProd
  签名: (R : 类型) [零 R] [幺 R] [取负 R]
  定义体: QuaternionAlgebra.equivProd _ _ _

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.equivProd, equivProd
-/
def Quaternion.equivProd (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ R × R × R × R :=
  QuaternionAlgebra.equivProd _ _ _

/-- The equivalence between the quaternions over `R` and `Fin 4 → R`. -/
@[simps! symm_apply]
/--
Definition of `Quaternion.equivTuple` / `Quaternion.equivTuple` 的定义

English:
definition Quaternion.equivTuple
  signature: (R : Type*) [Zero R] [One R] [Neg R]
  body: QuaternionAlgebra.equivTuple _ _ _

@[simp]

中文:
定义 Quaternion.equivTuple
  签名: (R : 类型) [零 R] [幺 R] [取负 R]
  定义体: QuaternionAlgebra.equivTuple _ _ _

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.equivTuple, equivTuple
-/
def Quaternion.equivTuple (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ (Fin 4 -> R) :=
  QuaternionAlgebra.equivTuple _ _ _

@[simp]
/--
theorem `Quaternion.equivTuple_apply` / 定理 `Quaternion.equivTuple_apply`

English:
theorem Quaternion.equivTuple_apply
  given: (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R])
  proof: rfl

中文:
定理 Quaternion.equivTuple_apply
  条件: (R : 类型) [零 R] [幺 R] [取负 R] (x : ℍ[R])
  证明: rfl
-/
theorem Quaternion.equivTuple_apply (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R]) :
    Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

instance {R : Type*} [Zero R] [One R] [Neg R] [Subsingleton R] : Subsingleton ℍ[R] :=
inferInstanceAs Subsingleton ℍ[R,-1,0,-1]
instance {R : Type*} [Zero R] [One R] [Neg R] [Nontrivial R] : Nontrivial ℍ[R] :=
inferInstanceAs Nontrivial ℍ[R,-1,0,-1]

namespace Quaternion

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: : R -> ℍ[R]
  body: QuaternionAlgebra.coe

中文:
定义 coe
  签名: : R -> ℍ[R]
  定义体: QuaternionAlgebra.coe
-/
@[coe] def coe : R -> ℍ[R] := QuaternionAlgebra.coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC R ℍ[R]
  body: ⟨coe⟩

中文:
实例 :
  签名: CoeTC R ℍ[R]
  定义体: ⟨coe⟩
-/
instance : CoeTC R ℍ[R] := ⟨coe⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S R] : SMul S ℍ[R]
  body: inferInstanceAs SMul S ℍ[R,-1,0,-1]

中文:
实例 [标量乘法
  签名: S R] : 标量乘法 S ℍ[R]
  定义体: inferInstanceAs SMul S ℍ[R,-1,0,-1]
-/
instance [SMul S R] : SMul S ℍ[R] := inferInstanceAs SMul S ℍ[R,-1,0,-1]

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring ℍ[R] where
  body: letI := Quaternion.instSMul (S := Nat) (R := R); (· • ·)
  zsmul := letI := Quaternion.instSMul (S := Int) (R := R); (· • ·)
__ : Ring ℍ[R] := inferInstanceAs Ring ℍ[R,-1,0,-1]

中文:
实例 instRing
  签名: : 环 ℍ[R] where
  定义体: letI := Quaternion.instSMul (S := Nat) (R := R); (· • ·)
  zsmul := letI := Quaternion.instSMul (S := Int) (R := R); (· • ·)
__ : Ring ℍ[R] := inferInstanceAs Ring ℍ[R,-1,0,-1]

Depends on / 依赖: Quaternion, Quaternion.instSMul, instSMul
-/
instance instRing : Ring ℍ[R] where
  nsmul := letI := Quaternion.instSMul (S := Nat) (R := R); (· • ·)
  zsmul := letI := Quaternion.instSMul (S := Int) (R := R); (· • ·)
__ : Ring ℍ[R] := inferInstanceAs Ring ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ℍ[R]
  body: inferInstanceAs Inhabited ℍ[R,-1,0,-1]

中文:
实例 :
  签名: 可居 ℍ[R]
  定义体: inferInstanceAs Inhabited ℍ[R,-1,0,-1]

Depends on / 依赖: Inhabited
-/
instance : Inhabited ℍ[R] := inferInstanceAs Inhabited ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [SMul S R] [SMul T R] [IsScalarTower S T R] : IsScalarTower S T ℍ[R]
  body: inferInstanceAs IsScalarTower S T ℍ[R,-1,0,-1]

中文:
实例 [标量乘法
  签名: S T] [标量乘法 S R] [标量乘法 T R] [标量塔 S T R] : 标量塔 S T ℍ[R]
  定义体: inferInstanceAs IsScalarTower S T ℍ[R,-1,0,-1]

Depends on / 依赖: IsScalarTower
-/
instance [SMul S T] [SMul S R] [SMul T R] [IsScalarTower S T R] : IsScalarTower S T ℍ[R] :=
inferInstanceAs IsScalarTower S T ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S R] [SMul T R] [SMulCommClass S T R] : SMulCommClass S T ℍ[R]
  body: inferInstanceAs SMulCommClass S T ℍ[R,-1,0,-1]

中文:
实例 [标量乘法
  签名: S R] [标量乘法 T R] [标量交换类 S T R] : 标量交换类 S T ℍ[R]
  定义体: inferInstanceAs SMulCommClass S T ℍ[R,-1,0,-1]

Depends on / 依赖: SMulCommClass
-/
instance [SMul S R] [SMul T R] [SMulCommClass S T R] : SMulCommClass S T ℍ[R] :=
inferInstanceAs SMulCommClass S T ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [MulAction S R] : MulAction S ℍ[R]
  body: inferInstanceAs MulAction S ℍ[R,-1,0,-1]

中文:
实例 [幺半群
  签名: S] [乘法作用 S R] : 乘法作用 S ℍ[R]
  定义体: inferInstanceAs MulAction S ℍ[R,-1,0,-1]

Depends on / 依赖: MulAction
-/
instance [Monoid S] [MulAction S R] : MulAction S ℍ[R] :=
inferInstanceAs MulAction S ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [DistribMulAction S R] : DistribMulAction S ℍ[R]
  body: inferInstanceAs DistribMulAction S ℍ[R,-1,0,-1]

中文:
实例 [半环
  签名: S] [分配乘法作用 S R] : 分配乘法作用 S ℍ[R]
  定义体: inferInstanceAs DistribMulAction S ℍ[R,-1,0,-1]

Depends on / 依赖: DistribMulAction
-/
instance [Semiring S] [DistribMulAction S R] : DistribMulAction S ℍ[R] :=
inferInstanceAs DistribMulAction S ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [Module S R] : Module S ℍ[R]
  body: inferInstanceAs Module S ℍ[R,-1,0,-1]

中文:
实例 [半环
  签名: S] [模 S R] : 模 S ℍ[R]
  定义体: inferInstanceAs Module S ℍ[R,-1,0,-1]

Depends on / 依赖: Module
-/
instance [Semiring S] [Module S R] : Module S ℍ[R] :=
inferInstanceAs Module S ℍ[R,-1,0,-1]

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: [CommSemiring S] [Algebra S R]
  body: inferInstanceAs Algebra S ℍ[R,-1,0,-1]

中文:
实例 algebra
  签名: [交换半环 S] [代数 S R]
  定义体: inferInstanceAs Algebra S ℍ[R,-1,0,-1]
-/
protected instance algebra [CommSemiring S] [Algebra S R] : Algebra S ℍ[R] :=
inferInstanceAs Algebra S ℍ[R,-1,0,-1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star ℍ[R]
  body: inferInstanceAs Star ℍ[R,-1,0,-1]

中文:
实例 :
  签名: 对合 ℍ[R]
  定义体: inferInstanceAs Star ℍ[R,-1,0,-1]
-/
instance : Star ℍ[R] := inferInstanceAs Star ℍ[R,-1,0,-1]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing ℍ[R]
  body: inferInstanceAs StarRing ℍ[R,-1,0,-1]

中文:
实例 :
  签名: 对合环 ℍ[R]
  定义体: inferInstanceAs StarRing ℍ[R,-1,0,-1]

Depends on / 依赖: StarRing
-/
instance : StarRing ℍ[R] := inferInstanceAs StarRing ℍ[R,-1,0,-1]
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStarNormal a
  body: inferInstanceAs IsStarNormal (R := ℍ[R,-1,0,-1]) a

@[ext]

中文:
实例 :
  签名: 是StarNormal a
  定义体: inferInstanceAs IsStarNormal (R := ℍ[R,-1,0,-1]) a

@[ext]

Depends on / 依赖: IsStarNormal
-/
instance : IsStarNormal a := inferInstanceAs IsStarNormal (R := ℍ[R,-1,0,-1]) a

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a.imK = b.imK -> a = b
  proof: QuaternionAlgebra.ext

中文:
定理 ext
  结论: a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a.imK = b.imK -> a = b
  证明: QuaternionAlgebra.ext

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.ext
-/
theorem ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a.imK = b.imK -> a = b :=
  QuaternionAlgebra.ext

/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: (x : ℍ[R])
  body: QuaternionAlgebra.im x

中文:
定义 im
  签名: (x : ℍ[R])
  定义体: QuaternionAlgebra.im x

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.im
-/
def im (x : ℍ[R]) : ℍ[R] := QuaternionAlgebra.im x

/--
theorem `re_im` / 定理 `re_im`

English:
theorem re_im
  statement: a.im.re = 0
  proof: rfl

中文:
定理 re_im
  结论: a.im.re = 0
  证明: rfl
-/
@[simp] theorem re_im : a.im.re = 0 := rfl

/--
theorem `imI_im` / 定理 `imI_im`

English:
theorem imI_im
  statement: a.im.imI = a.imI
  proof: rfl

中文:
定理 imI_im
  结论: a.im.imI = a.imI
  证明: rfl
-/
@[simp] theorem imI_im : a.im.imI = a.imI := rfl

/--
theorem `imJ_im` / 定理 `imJ_im`

English:
theorem imJ_im
  statement: a.im.imJ = a.imJ
  proof: rfl

中文:
定理 imJ_im
  结论: a.im.imJ = a.imJ
  证明: rfl
-/
@[simp] theorem imJ_im : a.im.imJ = a.imJ := rfl

/--
theorem `imK_im` / 定理 `imK_im`

English:
theorem imK_im
  statement: a.im.imK = a.imK
  proof: rfl

中文:
定理 imK_im
  结论: a.im.imK = a.imK
  证明: rfl
-/
@[simp] theorem imK_im : a.im.imK = a.imK := rfl

/--
theorem `im_idem` / 定理 `im_idem`

English:
theorem im_idem
  statement: a.im.im = a.im
  proof: rfl

中文:
定理 im_idem
  结论: a.im.im = a.im
  证明: rfl
-/
@[simp] theorem im_idem : a.im.im = a.im := rfl

/--
theorem `re_add_im` / 定理 `re_add_im`

English:
theorem re_add_im
  statement: ↑a.re + a.im = a
  proof: QuaternionAlgebra.re_add_im a

中文:
定理 re_add_im
  结论: ↑a.re + a.im = a
  证明: QuaternionAlgebra.re_add_im a
-/
@[simp] theorem re_add_im : ↑a.re + a.im = a := QuaternionAlgebra.re_add_im a

/--
theorem `sub_im_self` / 定理 `sub_im_self`

English:
theorem sub_im_self
  statement: a - a.im = a.re
  proof: QuaternionAlgebra.sub_im_self a

中文:
定理 sub_im_self
  结论: a - a.im = a.re
  证明: QuaternionAlgebra.sub_im_self a
-/
@[simp] theorem sub_im_self : a - a.im = a.re := QuaternionAlgebra.sub_im_self a

/--
theorem `sub_re_self` / 定理 `sub_re_self`

English:
theorem sub_re_self
  statement: a - ↑a.re = a.im
  proof: QuaternionAlgebra.sub_re_self a

@[simp, norm_cast]

中文:
定理 sub_re_self
  结论: a - ↑a.re = a.im
  证明: QuaternionAlgebra.sub_re_self a

@[simp, norm_cast]
-/
@[simp] theorem sub_re_self : a - ↑a.re = a.im := QuaternionAlgebra.sub_re_self a

@[simp, norm_cast]
/--
theorem `re_coe` / 定理 `re_coe`

English:
theorem re_coe
  statement: (x : ℍ[R]).re = x
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_coe
  结论: (x : ℍ[R]).re = x
  证明: rfl

@[simp, norm_cast]
-/
theorem re_coe : (x : ℍ[R]).re = x := rfl

@[simp, norm_cast]
/--
theorem `imI_coe` / 定理 `imI_coe`

English:
theorem imI_coe
  statement: (x : ℍ[R]).imI = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_coe
  结论: (x : ℍ[R]).imI = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_coe : (x : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
/--
theorem `imJ_coe` / 定理 `imJ_coe`

English:
theorem imJ_coe
  statement: (x : ℍ[R]).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_coe
  结论: (x : ℍ[R]).imJ = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imJ_coe : (x : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
/--
theorem `imK_coe` / 定理 `imK_coe`

English:
theorem imK_coe
  statement: (x : ℍ[R]).imK = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imK_coe
  结论: (x : ℍ[R]).imK = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imK_coe : (x : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
/--
theorem `im_coe` / 定理 `im_coe`

English:
theorem im_coe
  statement: (x : ℍ[R]).im = 0
  proof: rfl

中文:
定理 im_coe
  结论: (x : ℍ[R]).im = 0
  证明: rfl
-/
theorem im_coe : (x : ℍ[R]).im = 0 := rfl

/--
theorem `re_zero` / 定理 `re_zero`

English:
theorem re_zero
  statement: (0 : ℍ[R]).re = 0
  proof: rfl

中文:
定理 re_zero
  结论: (0 : ℍ[R]).re = 0
  证明: rfl
-/
@[scoped simp] theorem re_zero : (0 : ℍ[R]).re = 0 := rfl

/--
theorem `imI_zero` / 定理 `imI_zero`

English:
theorem imI_zero
  statement: (0 : ℍ[R]).imI = 0
  proof: rfl

中文:
定理 imI_zero
  结论: (0 : ℍ[R]).imI = 0
  证明: rfl
-/
@[scoped simp] theorem imI_zero : (0 : ℍ[R]).imI = 0 := rfl

/--
theorem `imJ_zero` / 定理 `imJ_zero`

English:
theorem imJ_zero
  statement: (0 : ℍ[R]).imJ = 0
  proof: rfl

中文:
定理 imJ_zero
  结论: (0 : ℍ[R]).imJ = 0
  证明: rfl
-/
@[scoped simp] theorem imJ_zero : (0 : ℍ[R]).imJ = 0 := rfl

/--
theorem `imK_zero` / 定理 `imK_zero`

English:
theorem imK_zero
  statement: (0 : ℍ[R]).imK = 0
  proof: rfl

中文:
定理 imK_zero
  结论: (0 : ℍ[R]).imK = 0
  证明: rfl
-/
@[scoped simp] theorem imK_zero : (0 : ℍ[R]).imK = 0 := rfl

/--
theorem `im_zero` / 定理 `im_zero`

English:
theorem im_zero
  statement: (0 : ℍ[R]).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 im_zero
  结论: (0 : ℍ[R]).im = 0
  证明: rfl

@[simp, norm_cast]
-/
@[scoped simp] theorem im_zero : (0 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : R) : ℍ[R]) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : R) : ℍ[R]) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl

/--
theorem `re_one` / 定理 `re_one`

English:
theorem re_one
  statement: (1 : ℍ[R]).re = 1
  proof: rfl

中文:
定理 re_one
  结论: (1 : ℍ[R]).re = 1
  证明: rfl
-/
@[scoped simp] theorem re_one : (1 : ℍ[R]).re = 1 := rfl

/--
theorem `imI_one` / 定理 `imI_one`

English:
theorem imI_one
  statement: (1 : ℍ[R]).imI = 0
  proof: rfl

中文:
定理 imI_one
  结论: (1 : ℍ[R]).imI = 0
  证明: rfl
-/
@[scoped simp] theorem imI_one : (1 : ℍ[R]).imI = 0 := rfl

/--
theorem `imJ_one` / 定理 `imJ_one`

English:
theorem imJ_one
  statement: (1 : ℍ[R]).imJ = 0
  proof: rfl

中文:
定理 imJ_one
  结论: (1 : ℍ[R]).imJ = 0
  证明: rfl
-/
@[scoped simp] theorem imJ_one : (1 : ℍ[R]).imJ = 0 := rfl

/--
theorem `imK_one` / 定理 `imK_one`

English:
theorem imK_one
  statement: (1 : ℍ[R]).imK = 0
  proof: rfl

中文:
定理 imK_one
  结论: (1 : ℍ[R]).imK = 0
  证明: rfl
-/
@[scoped simp] theorem imK_one : (1 : ℍ[R]).imK = 0 := rfl

/--
theorem `im_one` / 定理 `im_one`

English:
theorem im_one
  statement: (1 : ℍ[R]).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 im_one
  结论: (1 : ℍ[R]).im = 0
  证明: rfl

@[simp, norm_cast]
-/
@[scoped simp] theorem im_one : (1 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : R) : ℍ[R]) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : R) : ℍ[R]) = 1
  证明: rfl
-/
theorem coe_one : ((1 : R) : ℍ[R]) = 1 := rfl

/--
theorem `re_add` / 定理 `re_add`

English:
theorem re_add
  statement: (a + b).re = a.re + b.re
  proof: rfl

中文:
定理 re_add
  结论: (a + b).re = a.re + b.re
  证明: rfl
-/
@[simp] theorem re_add : (a + b).re = a.re + b.re := rfl

/--
theorem `imI_add` / 定理 `imI_add`

English:
theorem imI_add
  statement: (a + b).imI = a.imI + b.imI
  proof: rfl

中文:
定理 imI_add
  结论: (a + b).imI = a.imI + b.imI
  证明: rfl
-/
@[simp] theorem imI_add : (a + b).imI = a.imI + b.imI := rfl

/--
theorem `imJ_add` / 定理 `imJ_add`

English:
theorem imJ_add
  statement: (a + b).imJ = a.imJ + b.imJ
  proof: rfl

中文:
定理 imJ_add
  结论: (a + b).imJ = a.imJ + b.imJ
  证明: rfl
-/
@[simp] theorem imJ_add : (a + b).imJ = a.imJ + b.imJ := rfl

/--
theorem `imK_add` / 定理 `imK_add`

English:
theorem imK_add
  statement: (a + b).imK = a.imK + b.imK
  proof: rfl

中文:
定理 imK_add
  结论: (a + b).imK = a.imK + b.imK
  证明: rfl
-/
@[simp] theorem imK_add : (a + b).imK = a.imK + b.imK := rfl

/--
theorem `im_add` / 定理 `im_add`

English:
theorem im_add
  statement: (a + b).im = a.im + b.im
  proof: QuaternionAlgebra.im_add a b

@[simp, norm_cast]

中文:
定理 im_add
  结论: (a + b).im = a.im + b.im
  证明: QuaternionAlgebra.im_add a b

@[simp, norm_cast]
-/
@[simp] theorem im_add : (a + b).im = a.im + b.im := QuaternionAlgebra.im_add a b

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ((x + y : R) : ℍ[R]) = x + y
  proof: QuaternionAlgebra.coe_add x y

中文:
定理 coe_add
  结论: ((x + y : R) : ℍ[R]) = x + y
  证明: QuaternionAlgebra.coe_add x y

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_add, coe_add
-/
theorem coe_add : ((x + y : R) : ℍ[R]) = x + y :=
  QuaternionAlgebra.coe_add x y

/--
theorem `re_neg` / 定理 `re_neg`

English:
theorem re_neg
  statement: (-a).re = -a.re
  proof: rfl

中文:
定理 re_neg
  结论: (-a).re = -a.re
  证明: rfl
-/
@[simp] theorem re_neg : (-a).re = -a.re := rfl

/--
theorem `imI_neg` / 定理 `imI_neg`

English:
theorem imI_neg
  statement: (-a).imI = -a.imI
  proof: rfl

中文:
定理 imI_neg
  结论: (-a).imI = -a.imI
  证明: rfl
-/
@[simp] theorem imI_neg : (-a).imI = -a.imI := rfl

/--
theorem `imJ_neg` / 定理 `imJ_neg`

English:
theorem imJ_neg
  statement: (-a).imJ = -a.imJ
  proof: rfl

中文:
定理 imJ_neg
  结论: (-a).imJ = -a.imJ
  证明: rfl
-/
@[simp] theorem imJ_neg : (-a).imJ = -a.imJ := rfl

/--
theorem `imK_neg` / 定理 `imK_neg`

English:
theorem imK_neg
  statement: (-a).imK = -a.imK
  proof: rfl

中文:
定理 imK_neg
  结论: (-a).imK = -a.imK
  证明: rfl
-/
@[simp] theorem imK_neg : (-a).imK = -a.imK := rfl

/--
theorem `im_neg` / 定理 `im_neg`

English:
theorem im_neg
  statement: (-a).im = -a.im
  proof: QuaternionAlgebra.im_neg a

@[simp, norm_cast]

中文:
定理 im_neg
  结论: (-a).im = -a.im
  证明: QuaternionAlgebra.im_neg a

@[simp, norm_cast]
-/
@[simp] theorem im_neg : (-a).im = -a.im := QuaternionAlgebra.im_neg a

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ((-x : R) : ℍ[R]) = -x
  proof: QuaternionAlgebra.coe_neg x

中文:
定理 coe_neg
  结论: ((-x : R) : ℍ[R]) = -x
  证明: QuaternionAlgebra.coe_neg x

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_neg, coe_neg
-/
theorem coe_neg : ((-x : R) : ℍ[R]) = -x :=
  QuaternionAlgebra.coe_neg x

/--
theorem `re_sub` / 定理 `re_sub`

English:
theorem re_sub
  statement: (a - b).re = a.re - b.re
  proof: rfl

中文:
定理 re_sub
  结论: (a - b).re = a.re - b.re
  证明: rfl
-/
@[simp] theorem re_sub : (a - b).re = a.re - b.re := rfl

/--
theorem `imI_sub` / 定理 `imI_sub`

English:
theorem imI_sub
  statement: (a - b).imI = a.imI - b.imI
  proof: rfl

中文:
定理 imI_sub
  结论: (a - b).imI = a.imI - b.imI
  证明: rfl
-/
@[simp] theorem imI_sub : (a - b).imI = a.imI - b.imI := rfl

/--
theorem `imJ_sub` / 定理 `imJ_sub`

English:
theorem imJ_sub
  statement: (a - b).imJ = a.imJ - b.imJ
  proof: rfl

中文:
定理 imJ_sub
  结论: (a - b).imJ = a.imJ - b.imJ
  证明: rfl
-/
@[simp] theorem imJ_sub : (a - b).imJ = a.imJ - b.imJ := rfl

/--
theorem `imK_sub` / 定理 `imK_sub`

English:
theorem imK_sub
  statement: (a - b).imK = a.imK - b.imK
  proof: rfl

中文:
定理 imK_sub
  结论: (a - b).imK = a.imK - b.imK
  证明: rfl
-/
@[simp] theorem imK_sub : (a - b).imK = a.imK - b.imK := rfl

/--
theorem `im_sub` / 定理 `im_sub`

English:
theorem im_sub
  statement: (a - b).im = a.im - b.im
  proof: QuaternionAlgebra.im_sub a b

@[simp, norm_cast]

中文:
定理 im_sub
  结论: (a - b).im = a.im - b.im
  证明: QuaternionAlgebra.im_sub a b

@[simp, norm_cast]
-/
@[simp] theorem im_sub : (a - b).im = a.im - b.im := QuaternionAlgebra.im_sub a b

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ((x - y : R) : ℍ[R]) = x - y
  proof: QuaternionAlgebra.coe_sub x y

@[simp]

中文:
定理 coe_sub
  结论: ((x - y : R) : ℍ[R]) = x - y
  证明: QuaternionAlgebra.coe_sub x y

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_sub, coe_sub
-/
theorem coe_sub : ((x - y : R) : ℍ[R]) = x - y :=
  QuaternionAlgebra.coe_sub x y

@[simp]
/--
theorem `re_mul` / 定理 `re_mul`

English:
theorem re_mul
  statement: (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK
  proof: (QuaternionAlgebra.re_mul a b).trans by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp]

中文:
定理 re_mul
  结论: (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK
  证明: (QuaternionAlgebra.re_mul a b).trans by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.re_mul, neg_mul, neg_neg, one_mul, re_mul, sub_eq_add_neg
-/
theorem re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK :=
(QuaternionAlgebra.re_mul a b).trans by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp]
/--
theorem `imI_mul` / 定理 `imI_mul`

English:
theorem imI_mul
  statement: (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ
  proof: (QuaternionAlgebra.imI_mul a b).trans by ring

@[simp]

中文:
定理 imI_mul
  结论: (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ
  证明: (QuaternionAlgebra.imI_mul a b).trans by ring

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.imI_mul, imI_mul
-/
theorem imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ :=
(QuaternionAlgebra.imI_mul a b).trans by ring

@[simp]
/--
theorem `imJ_mul` / 定理 `imJ_mul`

English:
theorem imJ_mul
  statement: (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI
  proof: (QuaternionAlgebra.imJ_mul a b).trans by ring

@[simp]

中文:
定理 imJ_mul
  结论: (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI
  证明: (QuaternionAlgebra.imJ_mul a b).trans by ring

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.imJ_mul, imJ_mul
-/
theorem imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI :=
(QuaternionAlgebra.imJ_mul a b).trans by ring

@[simp]
/--
theorem `imK_mul` / 定理 `imK_mul`

English:
theorem imK_mul
  statement: (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re
  proof: (QuaternionAlgebra.imK_mul a b).trans by ring

@[simp, norm_cast]

中文:
定理 imK_mul
  结论: (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re
  证明: (QuaternionAlgebra.imK_mul a b).trans by ring

@[simp, norm_cast]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.imK_mul, imK_mul
-/
theorem imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re :=
(QuaternionAlgebra.imK_mul a b).trans by ring

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ((x * y : R) : ℍ[R]) = x * y
  proof: QuaternionAlgebra.coe_mul x y

@[norm_cast, simp]

中文:
定理 coe_mul
  结论: ((x * y : R) : ℍ[R]) = x * y
  证明: QuaternionAlgebra.coe_mul x y

@[norm_cast, simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_mul, coe_mul
-/
theorem coe_mul : ((x * y : R) : ℍ[R]) = x * y := QuaternionAlgebra.coe_mul x y

@[norm_cast, simp]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (n : Nat)
  statement: (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n
  proof: QuaternionAlgebra.coe_pow x n

@[simp, norm_cast]

中文:
定理 coe_pow
  条件: (n : 自然数)
  结论: (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n
  证明: QuaternionAlgebra.coe_pow x n

@[simp, norm_cast]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_pow, coe_pow
-/
theorem coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n :=
  QuaternionAlgebra.coe_pow x n

@[simp, norm_cast]
/--
theorem `re_natCast` / 定理 `re_natCast`

English:
theorem re_natCast
  given: (n : Nat)
  statement: (n : ℍ[R]).re = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R]).re = n
  证明: rfl

@[simp, norm_cast]
-/
theorem re_natCast (n : Nat) : (n : ℍ[R]).re = n := rfl

@[simp, norm_cast]
/--
theorem `imI_natCast` / 定理 `imI_natCast`

English:
theorem imI_natCast
  given: (n : Nat)
  statement: (n : ℍ[R]).imI = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R]).imI = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_natCast (n : Nat) : (n : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
/--
theorem `imJ_natCast` / 定理 `imJ_natCast`

English:
theorem imJ_natCast
  given: (n : Nat)
  statement: (n : ℍ[R]).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R]).imJ = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imJ_natCast (n : Nat) : (n : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
/--
theorem `imK_natCast` / 定理 `imK_natCast`

English:
theorem imK_natCast
  given: (n : Nat)
  statement: (n : ℍ[R]).imK = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imK_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R]).imK = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imK_natCast (n : Nat) : (n : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
/--
theorem `im_natCast` / 定理 `im_natCast`

English:
theorem im_natCast
  given: (n : Nat)
  statement: (n : ℍ[R]).im = 0
  proof: rfl

@[norm_cast]

中文:
定理 im_natCast
  条件: (n : 自然数)
  结论: (n : ℍ[R]).im = 0
  证明: rfl

@[norm_cast]
-/
theorem im_natCast (n : Nat) : (n : ℍ[R]).im = 0 := rfl

@[norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ↑(n : R) = (n : ℍ[R])
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ↑(n : R) = (n : ℍ[R])
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_natCast (n : Nat) : ↑(n : R) = (n : ℍ[R]) := rfl

@[simp, norm_cast]
/--
theorem `re_intCast` / 定理 `re_intCast`

English:
theorem re_intCast
  given: (z : Int)
  statement: (z : ℍ[R]).re = z
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R]).re = z
  证明: rfl

@[simp, norm_cast]
-/
theorem re_intCast (z : Int) : (z : ℍ[R]).re = z := rfl

@[simp, norm_cast]
/--
theorem `imI_intCast` / 定理 `imI_intCast`

English:
theorem imI_intCast
  given: (z : Int)
  statement: (z : ℍ[R]).imI = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R]).imI = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_intCast (z : Int) : (z : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
/--
theorem `imJ_intCast` / 定理 `imJ_intCast`

English:
theorem imJ_intCast
  given: (z : Int)
  statement: (z : ℍ[R]).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R]).imJ = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imJ_intCast (z : Int) : (z : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
/--
theorem `imK_intCast` / 定理 `imK_intCast`

English:
theorem imK_intCast
  given: (z : Int)
  statement: (z : ℍ[R]).imK = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imK_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R]).imK = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imK_intCast (z : Int) : (z : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
/--
theorem `im_intCast` / 定理 `im_intCast`

English:
theorem im_intCast
  given: (z : Int)
  statement: (z : ℍ[R]).im = 0
  proof: rfl

@[norm_cast]

中文:
定理 im_intCast
  条件: (z : 整数)
  结论: (z : ℍ[R]).im = 0
  证明: rfl

@[norm_cast]
-/
theorem im_intCast (z : Int) : (z : ℍ[R]).im = 0 := rfl

@[norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (z : Int)
  statement: ↑(z : R) = (z : ℍ[R])
  proof: rfl

中文:
定理 coe_intCast
  条件: (z : 整数)
  结论: ↑(z : R) = (z : ℍ[R])
  证明: rfl
-/
theorem coe_intCast (z : Int) : ↑(z : R) = (z : ℍ[R]) := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective (coe : R -> ℍ[R])
  proof: QuaternionAlgebra.coe_injective

@[simp]

中文:
定理 coe_injective
  结论: 函数.单射 (coe : R -> ℍ[R])
  证明: QuaternionAlgebra.coe_injective

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective (coe : R -> ℍ[R]) :=
  QuaternionAlgebra.coe_injective

@[simp]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {x y : R}
  statement: (x : ℍ[R]) = y ↔ x = y
  proof: coe_injective.eq_iff

@[simp]

中文:
定理 coe_inj
  条件: {x y : R}
  结论: (x : ℍ[R]) = y ↔ x = y
  证明: coe_injective.eq_iff

@[simp]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
/--
theorem `re_smul` / 定理 `re_smul`

English:
theorem re_smul
  given: [SMul S R] (s : S)
  statement: (s • a).re = s • a.re
  proof: rfl

中文:
定理 re_smul
  条件: [标量乘法 S R] (s : S)
  结论: (s • a).re = s • a.re
  证明: rfl
-/
theorem re_smul [SMul S R] (s : S) : (s • a).re = s • a.re :=
  rfl

/--
theorem `imI_smul` / 定理 `imI_smul`

English:
theorem imI_smul
  given: [SMul S R] (s : S)
  statement: (s • a).imI = s • a.imI
  proof: rfl

中文:
定理 imI_smul
  条件: [标量乘法 S R] (s : S)
  结论: (s • a).imI = s • a.imI
  证明: rfl
-/
@[simp] theorem imI_smul [SMul S R] (s : S) : (s • a).imI = s • a.imI := rfl

/--
theorem `imJ_smul` / 定理 `imJ_smul`

English:
theorem imJ_smul
  given: [SMul S R] (s : S)
  statement: (s • a).imJ = s • a.imJ
  proof: rfl

中文:
定理 imJ_smul
  条件: [标量乘法 S R] (s : S)
  结论: (s • a).imJ = s • a.imJ
  证明: rfl
-/
@[simp] theorem imJ_smul [SMul S R] (s : S) : (s • a).imJ = s • a.imJ := rfl

/--
theorem `imK_smul` / 定理 `imK_smul`

English:
theorem imK_smul
  given: [SMul S R] (s : S)
  statement: (s • a).imK = s • a.imK
  proof: rfl

@[simp]

中文:
定理 imK_smul
  条件: [标量乘法 S R] (s : S)
  结论: (s • a).imK = s • a.imK
  证明: rfl

@[simp]
-/
@[simp] theorem imK_smul [SMul S R] (s : S) : (s • a).imK = s • a.imK := rfl

@[simp]
/--
theorem `im_smul` / 定理 `im_smul`

English:
theorem im_smul
  given: [SMulZeroClass S R] (s : S)
  statement: (s • a).im = s • a.im
  proof: QuaternionAlgebra.im_smul a s

@[simp, norm_cast]

中文:
定理 im_smul
  条件: [SMulZero类 S R] (s : S)
  结论: (s • a).im = s • a.im
  证明: QuaternionAlgebra.im_smul a s

@[simp, norm_cast]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.im_smul, im_smul
-/
theorem im_smul [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.im_smul a s

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMulZeroClass S R] (s : S) (r : R)
  statement: (↑(s • r) : ℍ[R]) = s • (r : ℍ[R])
  proof: QuaternionAlgebra.coe_smul _ _

中文:
定理 coe_smul
  条件: [SMulZero类 S R] (s : S) (r : R)
  结论: (↑(s • r) : ℍ[R]) = s • (r : ℍ[R])
  证明: QuaternionAlgebra.coe_smul _ _

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_smul, coe_smul
-/
theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r : ℍ[R]) :=
  QuaternionAlgebra.coe_smul _ _

/--
theorem `coe_commutes` / 定理 `coe_commutes`

English:
theorem coe_commutes
  statement: ↑r * a = a * r
  proof: QuaternionAlgebra.coe_commutes r a

中文:
定理 coe_commutes
  结论: ↑r * a = a * r
  证明: QuaternionAlgebra.coe_commutes r a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_commutes, coe_commutes
-/
theorem coe_commutes : ↑r * a = a * r :=
  QuaternionAlgebra.coe_commutes r a

/--
theorem `coe_commute` / 定理 `coe_commute`

English:
theorem coe_commute
  statement: Commute (↑r) a
  proof: QuaternionAlgebra.coe_commute r a

中文:
定理 coe_commute
  结论: Commute (↑r) a
  证明: QuaternionAlgebra.coe_commute r a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_commute, coe_commute
-/
theorem coe_commute : Commute (↑r) a :=
  QuaternionAlgebra.coe_commute r a

/--
theorem `coe_mul_eq_smul` / 定理 `coe_mul_eq_smul`

English:
theorem coe_mul_eq_smul
  statement: ↑r * a = r • a
  proof: QuaternionAlgebra.coe_mul_eq_smul r a

中文:
定理 coe_mul_eq_smul
  结论: ↑r * a = r • a
  证明: QuaternionAlgebra.coe_mul_eq_smul r a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.coe_mul_eq_smul, coe_mul_eq_smul
-/
theorem coe_mul_eq_smul : ↑r * a = r • a :=
  QuaternionAlgebra.coe_mul_eq_smul r a

/--
theorem `mul_coe_eq_smul` / 定理 `mul_coe_eq_smul`

English:
theorem mul_coe_eq_smul
  statement: a * r = r • a
  proof: QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]

中文:
定理 mul_coe_eq_smul
  结论: a * r = r • a
  证明: QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.mul_coe_eq_smul, mul_coe_eq_smul
-/
theorem mul_coe_eq_smul : a * r = r • a :=
  QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]
/--
theorem `algebraMap_def` / 定理 `algebraMap_def`

English:
theorem algebraMap_def
  statement: ⇑(algebraMap R ℍ[R]) = coe
  proof: rfl

中文:
定理 algebraMap_def
  结论: ⇑(algebraMap R ℍ[R]) = coe
  证明: rfl
-/
theorem algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe :=
  rfl

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: (algebraMap R ℍ[R] : _ -> _).Injective
  proof: QuaternionAlgebra.algebraMap_injective

中文:
定理 algebraMap_injective
  结论: (algebraMap R ℍ[R] : _ -> _).单射
  证明: QuaternionAlgebra.algebraMap_injective

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.algebraMap_injective, algebraMap_injective
-/
theorem algebraMap_injective : (algebraMap R ℍ[R] : _ -> _).Injective :=
  QuaternionAlgebra.algebraMap_injective

/--
theorem `smul_coe` / 定理 `smul_coe`

English:
theorem smul_coe
  statement: x • (y : ℍ[R]) = ↑(x * y)
  proof: QuaternionAlgebra.smul_coe x y

中文:
定理 smul_coe
  结论: x • (y : ℍ[R]) = ↑(x * y)
  证明: QuaternionAlgebra.smul_coe x y

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.smul_coe, smul_coe
-/
theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) :=
  QuaternionAlgebra.smul_coe x y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R ℍ[R]
  body: inferInstanceAs Module.Finite R ℍ[R,-1,0,-1]

中文:
实例 :
  签名: 模.有限 R ℍ[R]
  定义体: inferInstanceAs Module.Finite R ℍ[R,-1,0,-1]

Depends on / 依赖: Finite, Module, Module.Finite
-/
instance : Module.Finite R ℍ[R] := inferInstanceAs Module.Finite R ℍ[R,-1,0,-1]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R ℍ[R]
  body: inferInstanceAs Module.Free R ℍ[R,-1,0,-1]

中文:
实例 :
  签名: 模.自由 R ℍ[R]
  定义体: inferInstanceAs Module.Free R ℍ[R,-1,0,-1]

Depends on / 依赖: Module, Module.Free
-/
instance : Module.Free R ℍ[R] := inferInstanceAs Module.Free R ℍ[R,-1,0,-1]

/--
theorem `rank_eq_four` / 定理 `rank_eq_four`

English:
theorem rank_eq_four
  given: [StrongRankCondition R]
  statement: Module.rank R ℍ[R] = 4
  proof: QuaternionAlgebra.rank_eq_four _ _ _

中文:
定理 rank_eq_four
  条件: [StrongRankCondition R]
  结论: 模.rank R ℍ[R] = 4
  证明: QuaternionAlgebra.rank_eq_four _ _ _

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.rank_eq_four, rank_eq_four
-/
theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4 :=
  QuaternionAlgebra.rank_eq_four _ _ _

/--
theorem `finrank_eq_four` / 定理 `finrank_eq_four`

English:
theorem finrank_eq_four
  given: [StrongRankCondition R]
  statement: Module.finrank R ℍ[R] = 4
  proof: QuaternionAlgebra.finrank_eq_four _ _ _

中文:
定理 finrank_eq_four
  条件: [StrongRankCondition R]
  结论: 模.finrank R ℍ[R] = 4
  证明: QuaternionAlgebra.finrank_eq_four _ _ _

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.finrank_eq_four, finrank_eq_four
-/
theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4 :=
  QuaternionAlgebra.finrank_eq_four _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `re_star` / 定理 `re_star`

English:
theorem re_star
  statement: (star a).re = a.re
  proof: by
  rw [QuaternionAlgebra.re_star]; rw [zero_mul]; rw [add_zero]

中文:
定理 re_star
  结论: (star a).re = a.re
  证明: by
  rw [QuaternionAlgebra.re_star]; rw [zero_mul]; rw [add_zero]
-/
@[simp] theorem re_star : (star a).re = a.re := by
  rw [QuaternionAlgebra.re_star]; rw [zero_mul]; rw [add_zero]

/--
theorem `imI_star` / 定理 `imI_star`

English:
theorem imI_star
  statement: (star a).imI = -a.imI
  proof: rfl

中文:
定理 imI_star
  结论: (star a).imI = -a.imI
  证明: rfl
-/
@[simp] theorem imI_star : (star a).imI = -a.imI := rfl

/--
theorem `imJ_star` / 定理 `imJ_star`

English:
theorem imJ_star
  statement: (star a).imJ = -a.imJ
  proof: rfl

中文:
定理 imJ_star
  结论: (star a).imJ = -a.imJ
  证明: rfl
-/
@[simp] theorem imJ_star : (star a).imJ = -a.imJ := rfl

/--
theorem `imK_star` / 定理 `imK_star`

English:
theorem imK_star
  statement: (star a).imK = -a.imK
  proof: rfl

中文:
定理 imK_star
  结论: (star a).imK = -a.imK
  证明: rfl
-/
@[simp] theorem imK_star : (star a).imK = -a.imK := rfl

/--
theorem `im_star` / 定理 `im_star`

English:
theorem im_star
  statement: (star a).im = -a.im
  proof: QuaternionAlgebra.im_star a

中文:
定理 im_star
  结论: (star a).im = -a.im
  证明: QuaternionAlgebra.im_star a
-/
@[simp] theorem im_star : (star a).im = -a.im := QuaternionAlgebra.im_star a

/--
theorem `self_add_star'` / 定理 `self_add_star'`

English:
theorem self_add_star'
  statement: a + star a = ↑(2 * a.re)
  proof: by
  simpa using! QuaternionAlgebra.self_add_star' a

中文:
定理 self_add_star'
  结论: a + star a = ↑(2 * a.re)
  证明: by
  simpa using! QuaternionAlgebra.self_add_star' a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.self_add_star, self_add_star
-/
theorem self_add_star' : a + star a = ↑(2 * a.re) := by
  simpa using! QuaternionAlgebra.self_add_star' a

/--
theorem `self_add_star` / 定理 `self_add_star`

English:
theorem self_add_star
  statement: a + star a = 2 * a.re
  proof: by
  simpa using! QuaternionAlgebra.self_add_star a

中文:
定理 self_add_star
  结论: a + star a = 2 * a.re
  证明: by
  simpa using! QuaternionAlgebra.self_add_star a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.self_add_star, self_add_star
-/
theorem self_add_star : a + star a = 2 * a.re := by
  simpa using! QuaternionAlgebra.self_add_star a

/--
theorem `star_add_self'` / 定理 `star_add_self'`

English:
theorem star_add_self'
  statement: star a + a = ↑(2 * a.re)
  proof: by
  simpa using! QuaternionAlgebra.star_add_self' a

中文:
定理 star_add_self'
  结论: star a + a = ↑(2 * a.re)
  证明: by
  simpa using! QuaternionAlgebra.star_add_self' a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_add_self, star_add_self
-/
theorem star_add_self' : star a + a = ↑(2 * a.re) := by
  simpa using! QuaternionAlgebra.star_add_self' a

/--
theorem `star_add_self` / 定理 `star_add_self`

English:
theorem star_add_self
  statement: star a + a = 2 * a.re
  proof: by
  simpa using! QuaternionAlgebra.star_add_self a

中文:
定理 star_add_self
  结论: star a + a = 2 * a.re
  证明: by
  simpa using! QuaternionAlgebra.star_add_self a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_add_self, star_add_self
-/
theorem star_add_self : star a + a = 2 * a.re := by
  simpa using! QuaternionAlgebra.star_add_self a

/--
theorem `star_eq_two_re_sub` / 定理 `star_eq_two_re_sub`

English:
theorem star_eq_two_re_sub
  statement: star a = ↑(2 * a.re) - a
  proof: by
  simpa using! QuaternionAlgebra.star_eq_two_re_sub a

@[simp, norm_cast]

中文:
定理 star_eq_two_re_sub
  结论: star a = ↑(2 * a.re) - a
  证明: by
  simpa using! QuaternionAlgebra.star_eq_two_re_sub a

@[simp, norm_cast]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_eq_two_re_sub, star_eq_two_re_sub
-/
theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a := by
  simpa using! QuaternionAlgebra.star_eq_two_re_sub a

@[simp, norm_cast]
/--
theorem `star_coe` / 定理 `star_coe`

English:
theorem star_coe
  statement: star (x : ℍ[R]) = x
  proof: QuaternionAlgebra.star_coe x

@[simp]

中文:
定理 star_coe
  结论: star (x : ℍ[R]) = x
  证明: QuaternionAlgebra.star_coe x

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_coe, star_coe
-/
theorem star_coe : star (x : ℍ[R]) = x :=
  QuaternionAlgebra.star_coe x

@[simp]
/--
theorem `star_im` / 定理 `star_im`

English:
theorem star_im
  statement: star a.im = -a.im
  proof: by ext <;> simp

@[simp]

中文:
定理 star_im
  结论: star a.im = -a.im
  证明: by ext <;> simp

@[simp]
-/
theorem star_im : star a.im = -a.im := by ext <;> simp

@[simp]
/--
theorem `star_smul` / 定理 `star_smul`

English:
theorem star_smul
  given: [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R])
  proof: QuaternionAlgebra.star_smul' s a

中文:
定理 star_smul
  条件: [幺半群 S] [分配乘法作用 S R] (s : S) (a : ℍ[R])
  证明: QuaternionAlgebra.star_smul' s a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_smul, star_smul
-/
theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) :
    star (s • a) = s • star a := QuaternionAlgebra.star_smul' s a

/--
theorem `eq_re_of_eq_coe` / 定理 `eq_re_of_eq_coe`

English:
theorem eq_re_of_eq_coe
  given: {a : ℍ[R]} {x : R} (h : a = x)
  statement: a = a.re
  proof: QuaternionAlgebra.eq_re_of_eq_coe h

中文:
定理 eq_re_of_eq_coe
  条件: {a : ℍ[R]} {x : R} (h : a = x)
  结论: a = a.re
  证明: QuaternionAlgebra.eq_re_of_eq_coe h

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.eq_re_of_eq_coe, eq_re_of_eq_coe
-/
theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
  QuaternionAlgebra.eq_re_of_eq_coe h

/--
theorem `eq_re_iff_mem_range_coe` / 定理 `eq_re_iff_mem_range_coe`

English:
theorem eq_re_iff_mem_range_coe
  given: {a : ℍ[R]}
  statement: a = a.re ↔ a in Set.range (coe : R -> ℍ[R])
  proof: QuaternionAlgebra.eq_re_iff_mem_range_coe

中文:
定理 eq_re_iff_mem_range_coe
  条件: {a : ℍ[R]}
  结论: a = a.re ↔ a in 集合.range (coe : R -> ℍ[R])
  证明: QuaternionAlgebra.eq_re_iff_mem_range_coe

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.eq_re_iff_mem_range_coe, eq_re_iff_mem_range_coe
-/
theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a in Set.range (coe : R -> ℍ[R]) :=
  QuaternionAlgebra.eq_re_iff_mem_range_coe

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
/--
theorem `star_eq_self` / 定理 `star_eq_self`

English:
theorem star_eq_self
  given: {a : ℍ[R]}
  statement: star a = a ↔ a = a.re
  proof: QuaternionAlgebra.star_eq_self

@[simp]

中文:
定理 star_eq_self
  条件: {a : ℍ[R]}
  结论: star a = a ↔ a = a.re
  证明: QuaternionAlgebra.star_eq_self

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_eq_self, star_eq_self
-/
theorem star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re :=
  QuaternionAlgebra.star_eq_self

@[simp]
/--
theorem `star_eq_neg` / 定理 `star_eq_neg`

English:
theorem star_eq_neg
  given: {a : ℍ[R]}
  statement: star a = -a ↔ a.re = 0
  proof: QuaternionAlgebra.star_eq_neg

中文:
定理 star_eq_neg
  条件: {a : ℍ[R]}
  结论: star a = -a ↔ a.re = 0
  证明: QuaternionAlgebra.star_eq_neg

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_eq_neg, star_eq_neg
-/
theorem star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0 :=
  QuaternionAlgebra.star_eq_neg

end CharZero

/--
theorem `star_mul_eq_coe` / 定理 `star_mul_eq_coe`

English:
theorem star_mul_eq_coe
  statement: star a * a = (star a * a).re
  proof: QuaternionAlgebra.star_mul_eq_coe a

中文:
定理 star_mul_eq_coe
  结论: star a * a = (star a * a).re
  证明: QuaternionAlgebra.star_mul_eq_coe a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.star_mul_eq_coe, star_mul_eq_coe
-/
theorem star_mul_eq_coe : star a * a = (star a * a).re :=
  QuaternionAlgebra.star_mul_eq_coe a

/--
theorem `mul_star_eq_coe` / 定理 `mul_star_eq_coe`

English:
theorem mul_star_eq_coe
  statement: a * star a = (a * star a).re
  proof: QuaternionAlgebra.mul_star_eq_coe a

中文:
定理 mul_star_eq_coe
  结论: a * star a = (a * star a).re
  证明: QuaternionAlgebra.mul_star_eq_coe a

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.mul_star_eq_coe, mul_star_eq_coe
-/
theorem mul_star_eq_coe : a * star a = (a * star a).re :=
  QuaternionAlgebra.mul_star_eq_coe a

open MulOpposite

/--
Definition of `starAe` / `starAe` 的定义

English:
definition starAe
  signature: : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ
  body: QuaternionAlgebra.starAe

@[simp]

中文:
定义 starAe
  签名: : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ
  定义体: QuaternionAlgebra.starAe

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.starAe, starAe
-/
def starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ :=
  QuaternionAlgebra.starAe

@[simp]
/--
theorem `coe_starAe` / 定理 `coe_starAe`

English:
theorem coe_starAe
  statement: ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star
  proof: rfl

中文:
定理 coe_starAe
  结论: ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star
  证明: rfl
-/
theorem coe_starAe : ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star :=
  rfl

/--
Definition of `normSq` / `normSq` 的定义

English:
definition normSq
  signature: : ℍ[R] ->*₀ R where
  body: (a * star a).re
  map_zero' := by simp only [star_zero, zero_mul, re_zero]
  map_one' := by simp only [star_one, one_mul, re_one]
map_mul' x y := coe_injective by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]

中文:
定义 normSq
  签名: : ℍ[R] ->*₀ R where
  定义体: (a * star a).re
  map_zero' := by simp only [star_zero, zero_mul, re_zero]
  map_one' := by simp only [star_one, one_mul, re_one]
map_mul' x y := coe_injective by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]
-/
def normSq : ℍ[R] ->*₀ R where
  toFun a := (a * star a).re
  map_zero' := by simp only [star_zero, zero_mul, re_zero]
  map_one' := by simp only [star_one, one_mul, re_one]
map_mul' x y := coe_injective by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]

/--
theorem `normSq_def` / 定理 `normSq_def`

English:
theorem normSq_def
  statement: normSq a = (a * star a).re
  proof: rfl

中文:
定理 normSq_def
  结论: normSq a = (a * star a).re
  证明: rfl
-/
theorem normSq_def : normSq a = (a * star a).re := rfl

/--
theorem `normSq_def'` / 定理 `normSq_def'`

English:
theorem normSq_def'
  statement: normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2
  proof: by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, re_mul, re_star, imI_star, imJ_star,
    imK_star]

中文:
定理 normSq_def'
  结论: normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2
  证明: by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, re_mul, re_star, imI_star, imJ_star,
    imK_star]

Depends on / 依赖: imI_star, imJ_star, imK_star, mul_neg, normSq_def, re_mul, re_star, sub_neg_eq_add
-/
theorem normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, re_mul, re_star, imI_star, imJ_star,
    imK_star]

/--
theorem `normSq_coe` / 定理 `normSq_coe`

English:
theorem normSq_coe
  statement: normSq (x : ℍ[R]) = x ^ 2
  proof: by
  rw [normSq_def]; rw [star_coe]; rw [← coe_mul]; rw [re_coe]; rw [sq]

@[simp]

中文:
定理 normSq_coe
  结论: normSq (x : ℍ[R]) = x ^ 2
  证明: by
  rw [normSq_def]; rw [star_coe]; rw [← coe_mul]; rw [re_coe]; rw [sq]

@[simp]

Depends on / 依赖: coe_mul, normSq_def, re_coe, star_coe
-/
theorem normSq_coe : normSq (x : ℍ[R]) = x ^ 2 := by
  rw [normSq_def]; rw [star_coe]; rw [← coe_mul]; rw [re_coe]; rw [sq]

@[simp]
/--
theorem `normSq_star` / 定理 `normSq_star`

English:
theorem normSq_star
  statement: normSq (star a) = normSq a
  proof: by simp [normSq_def']

@[norm_cast]

中文:
定理 normSq_star
  结论: normSq (star a) = normSq a
  证明: by simp [normSq_def']

@[norm_cast]

Depends on / 依赖: normSq_def
-/
theorem normSq_star : normSq (star a) = normSq a := by simp [normSq_def']

@[norm_cast]
/--
theorem `normSq_natCast` / 定理 `normSq_natCast`

English:
theorem normSq_natCast
  given: (n : Nat)
  statement: normSq (n : ℍ[R]) = (n : R) ^ 2
  proof: by
  rw [← coe_natCast]; rw [normSq_coe]

@[norm_cast]

中文:
定理 normSq_natCast
  条件: (n : 自然数)
  结论: normSq (n : ℍ[R]) = (n : R) ^ 2
  证明: by
  rw [← coe_natCast]; rw [normSq_coe]

@[norm_cast]

Depends on / 依赖: coe_natCast, normSq_coe
-/
theorem normSq_natCast (n : Nat) : normSq (n : ℍ[R]) = (n : R) ^ 2 := by
  rw [← coe_natCast]; rw [normSq_coe]

@[norm_cast]
/--
theorem `normSq_intCast` / 定理 `normSq_intCast`

English:
theorem normSq_intCast
  given: (z : Int)
  statement: normSq (z : ℍ[R]) = (z : R) ^ 2
  proof: by
  rw [← coe_intCast]; rw [normSq_coe]

@[simp]

中文:
定理 normSq_intCast
  条件: (z : 整数)
  结论: normSq (z : ℍ[R]) = (z : R) ^ 2
  证明: by
  rw [← coe_intCast]; rw [normSq_coe]

@[simp]

Depends on / 依赖: coe_intCast, normSq_coe
-/
theorem normSq_intCast (z : Int) : normSq (z : ℍ[R]) = (z : R) ^ 2 := by
  rw [← coe_intCast]; rw [normSq_coe]

@[simp]
/--
theorem `normSq_neg` / 定理 `normSq_neg`

English:
theorem normSq_neg
  statement: normSq (-a) = normSq a
  proof: by simp only [normSq_def, star_neg, neg_mul_neg]

中文:
定理 normSq_neg
  结论: normSq (-a) = normSq a
  证明: by simp only [normSq_def, star_neg, neg_mul_neg]

Depends on / 依赖: neg_mul_neg, normSq_def, star_neg
-/
theorem normSq_neg : normSq (-a) = normSq a := by simp only [normSq_def, star_neg, neg_mul_neg]

/--
theorem `self_mul_star` / 定理 `self_mul_star`

English:
theorem self_mul_star
  statement: a * star a = normSq a
  proof: by rw [mul_star_eq_coe, normSq_def]

中文:
定理 self_mul_star
  结论: a * star a = normSq a
  证明: by rw [mul_star_eq_coe, normSq_def]

Depends on / 依赖: mul_star_eq_coe, normSq_def
-/
theorem self_mul_star : a * star a = normSq a := by rw [mul_star_eq_coe, normSq_def]

/--
theorem `star_mul_self` / 定理 `star_mul_self`

English:
theorem star_mul_self
  statement: star a * a = normSq a
  proof: by rw [star_comm_self, self_mul_star]

中文:
定理 star_mul_self
  结论: star a * a = normSq a
  证明: by rw [star_comm_self, self_mul_star]

Depends on / 依赖: self_mul_star, star_comm_self
-/
theorem star_mul_self : star a * a = normSq a := by rw [star_comm_self, self_mul_star]

/--
theorem `im_sq` / 定理 `im_sq`

English:
theorem im_sq
  statement: a.im ^ 2 = -normSq a.im
  proof: by
  simp_rw [sq, ← star_mul_self, star_im, neg_mul, neg_neg]

中文:
定理 im_sq
  结论: a.im ^ 2 = -normSq a.im
  证明: by
  simp_rw [sq, ← star_mul_self, star_im, neg_mul, neg_neg]

Depends on / 依赖: neg_mul, neg_neg, simp_rw, star_im, star_mul_self
-/
theorem im_sq : a.im ^ 2 = -normSq a.im := by
  simp_rw [sq, ← star_mul_self, star_im, neg_mul, neg_neg]

/--
theorem `coe_normSq_add` / 定理 `coe_normSq_add`

English:
theorem coe_normSq_add
  statement: normSq (a + b) = normSq a + a * star b + b * star a + normSq b
  proof: by
  simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]

中文:
定理 coe_normSq_add
  结论: normSq (a + b) = normSq a + a * star b + b * star a + normSq b
  证明: by
  simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]

Depends on / 依赖: add_assoc, add_left_comm, add_mul, mul_add, self_mul_star, star_add
-/
theorem coe_normSq_add : normSq (a + b) = normSq a + a * star b + b * star a + normSq b := by
  simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]

/--
theorem `normSq_smul` / 定理 `normSq_smul`

English:
theorem normSq_smul
  given: (r : R) (q : ℍ[R])
  statement: normSq (r • q) = r ^ 2 * normSq q
  proof: by
  simp only [normSq_def', re_smul, imI_smul, imJ_smul, imK_smul, mul_pow, mul_add, smul_eq_mul]

中文:
定理 normSq_smul
  条件: (r : R) (q : ℍ[R])
  结论: normSq (r • q) = r ^ 2 * normSq q
  证明: by
  simp only [normSq_def', re_smul, imI_smul, imJ_smul, imK_smul, mul_pow, mul_add, smul_eq_mul]

Depends on / 依赖: imI_smul, imJ_smul, imK_smul, mul_add, mul_pow, normSq_def, re_smul, smul_eq_mul
-/
theorem normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) = r ^ 2 * normSq q := by
  simp only [normSq_def', re_smul, imI_smul, imJ_smul, imK_smul, mul_pow, mul_add, smul_eq_mul]

/--
theorem `normSq_add` / 定理 `normSq_add`

English:
theorem normSq_add
  given: (a b : ℍ[R])
  statement: normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re
  proof: calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      simp_rw [normSq_def, star_add, add_mul, mul_add, re_add]
    _ = normSq a + normSq b + ((a * star b).re + (b * star a).re) := by abel
    _ = normSq a + normSq b + 2 * (a * star b).re := by
      rw [← re_add]; rw [← star_mul_star a b]; rw [self_add_star']; rw [re_coe]

中文:
定理 normSq_add
  条件: (a b : ℍ[R])
  结论: normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re
  证明: calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      simp_rw [normSq_def, star_add, add_mul, mul_add, re_add]
    _ = normSq a + normSq b + ((a * star b).re + (b * star a).re) := by abel
    _ = normSq a + normSq b + 2 * (a * star b).re := by
      rw [← re_add]; rw [← star_mul_star a b]; rw [self_add_star']; rw [re_coe]

Depends on / 依赖: add_mul, mul_add, normSq, normSq_def, re_add, re_coe, self_add_star, simp_rw, star_add, star_mul_star
-/
theorem normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re :=
  calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      simp_rw [normSq_def, star_add, add_mul, mul_add, re_add]
    _ = normSq a + normSq b + ((a * star b).re + (b * star a).re) := by abel
    _ = normSq a + normSq b + 2 * (a * star b).re := by
      rw [← re_add]; rw [← star_mul_star a b]; rw [self_add_star']; rw [re_coe]

end Quaternion

namespace Quaternion

variable {R : Type*}

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

@[simp]
/--
theorem `normSq_eq_zero` / 定理 `normSq_eq_zero`

English:
theorem normSq_eq_zero
  statement: normSq a = 0 ↔ a = 0
  proof: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ normSq.map_zero⟩
  rw [normSq_def']; rw [add_eq_zero_iff_of_nonneg]; rw [add_eq_zero_iff_of_nonneg]; rw [add_eq_zero_iff_of_nonneg]
    at h
  · apply ext a 0 <;> apply eq_zero_of_pow_eq_zero
    exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
  all_goals apply_rules [sq_nonneg, add_nonneg]

中文:
定理 normSq_eq_zero
  结论: normSq a = 0 ↔ a = 0
  证明: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ normSq.map_zero⟩
  rw [normSq_def']; rw [add_eq_zero_iff_of_nonneg]; rw [add_eq_zero_iff_of_nonneg]; rw [add_eq_zero_iff_of_nonneg]
    at h
  · apply ext a 0 <;> apply eq_zero_of_pow_eq_zero
    exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
  all_goals apply_rules [sq_nonneg, add_nonneg]

Depends on / 依赖: add_eq_zero_iff_of_nonneg, add_nonneg, all_goals, apply_rules, eq_zero_of_pow_eq_zero, exacts, h.symm, map_zero, normSq, normSq.map_zero, normSq_def, sq_nonneg
-/
theorem normSq_eq_zero : normSq a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ normSq.map_zero⟩
  rw [normSq_def']; rw [add_eq_zero_iff_of_nonneg]; rw [add_eq_zero_iff_of_nonneg]; rw [add_eq_zero_iff_of_nonneg]
    at h
  · apply ext a 0 <;> apply eq_zero_of_pow_eq_zero
    exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
  all_goals apply_rules [sq_nonneg, add_nonneg]

/--
theorem `normSq_ne_zero` / 定理 `normSq_ne_zero`

English:
theorem normSq_ne_zero
  statement: normSq a != 0 ↔ a != 0
  proof: normSq_eq_zero.not

@[simp]

中文:
定理 normSq_ne_zero
  结论: normSq a != 0 ↔ a != 0
  证明: normSq_eq_zero.not

@[simp]

Depends on / 依赖: normSq_eq_zero, normSq_eq_zero.not
-/
theorem normSq_ne_zero : normSq a != 0 ↔ a != 0 := normSq_eq_zero.not

@[simp]
/--
theorem `normSq_nonneg` / 定理 `normSq_nonneg`

English:
theorem normSq_nonneg
  statement: 0 <= normSq a
  proof: by
  rw [normSq_def']
  apply_rules [sq_nonneg, add_nonneg]

@[simp]

中文:
定理 normSq_nonneg
  结论: 0 <= normSq a
  证明: by
  rw [normSq_def']
  apply_rules [sq_nonneg, add_nonneg]

@[simp]

Depends on / 依赖: add_nonneg, apply_rules, normSq_def, sq_nonneg
-/
theorem normSq_nonneg : 0 <= normSq a := by
  rw [normSq_def']
  apply_rules [sq_nonneg, add_nonneg]

@[simp]
/--
theorem `normSq_le_zero` / 定理 `normSq_le_zero`

English:
theorem normSq_le_zero
  statement: normSq a <= 0 ↔ a = 0
  proof: normSq_nonneg.ge_iff_eq'.trans normSq_eq_zero

中文:
定理 normSq_le_zero
  结论: normSq a <= 0 ↔ a = 0
  证明: normSq_nonneg.ge_iff_eq'.trans normSq_eq_zero

Depends on / 依赖: ge_iff_eq, normSq_eq_zero, normSq_nonneg, normSq_nonneg.ge_iff_eq
-/
theorem normSq_le_zero : normSq a <= 0 ↔ a = 0 :=
  normSq_nonneg.ge_iff_eq'.trans normSq_eq_zero

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial ℍ[R] where
  body: ⟨0, 1, mt (congr_arg QuaternionAlgebra.re) zero_ne_one⟩

中文:
实例 instNontrivial
  签名: : 非平凡 ℍ[R] where
  定义体: ⟨0, 1, mt (congr_arg QuaternionAlgebra.re) zero_ne_one⟩

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.re, congr_arg, zero_ne_one
-/
instance instNontrivial : Nontrivial ℍ[R] where
  exists_pair_ne := ⟨0, 1, mt (congr_arg QuaternionAlgebra.re) zero_ne_one⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors ℍ[R]
  body: have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1

中文:
实例 :
  签名: 无零因子 ℍ[R]
  定义体: have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1

Depends on / 依赖: StarSubsemiring, eq_zero_or_eq_zero_of_mul_eq_zero, map_mul, normSq, normSq_eq_zero, ofSetLike
-/
instance : NoZeroDivisors ℍ[R] where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab :=
    have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain ℍ[R]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 :
  签名: 是整环 ℍ[R]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance : IsDomain ℍ[R] := NoZeroDivisors.to_isDomain _

/--
theorem `sq_eq_normSq` / 定理 `sq_eq_normSq`

English:
theorem sq_eq_normSq
  statement: a ^ 2 = normSq a ↔ a = a.re
  proof: by
  rw [← star_eq_self]; rw [← star_mul_self]; rw [sq]; rw [mul_eq_mul_right_iff]; rw [eq_comm]
  exact or_iff_left_of_imp fun ha => ha.symm ▸ star_zero _

中文:
定理 sq_eq_normSq
  结论: a ^ 2 = normSq a ↔ a = a.re
  证明: by
  rw [← star_eq_self]; rw [← star_mul_self]; rw [sq]; rw [mul_eq_mul_right_iff]; rw [eq_comm]
  exact or_iff_left_of_imp fun ha => ha.symm ▸ star_zero _

Depends on / 依赖: CanLift, StarSubsemiring, eq_comm, ha.symm, mul_eq_mul_right_iff, or_iff_left_of_imp, star_eq_self, star_mul_self, star_zero
-/
theorem sq_eq_normSq : a ^ 2 = normSq a ↔ a = a.re := by
  rw [← star_eq_self]; rw [← star_mul_self]; rw [sq]; rw [mul_eq_mul_right_iff]; rw [eq_comm]
  exact or_iff_left_of_imp fun ha => ha.symm ▸ star_zero _

/--
theorem `sq_eq_neg_normSq` / 定理 `sq_eq_neg_normSq`

English:
theorem sq_eq_neg_normSq
  statement: a ^ 2 = -normSq a ↔ a.re = 0
  proof: by
  simp_rw [← star_eq_neg]
  obtain rfl | hq0 := eq_or_ne a 0
  · simp
  · rw [← star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]

中文:
定理 sq_eq_neg_normSq
  结论: a ^ 2 = -normSq a ↔ a.re = 0
  证明: by
  simp_rw [← star_eq_neg]
  obtain rfl | hq0 := eq_or_ne a 0
  · simp
  · rw [← star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]

Depends on / 依赖: eq_comm, eq_or_ne, mul_left_inj, mul_neg, neg_ne_zero, neg_ne_zero.mpr, neg_sq, simp_rw, star_eq_neg, star_mul_self
-/
theorem sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re = 0 := by
  simp_rw [← star_eq_neg]
  obtain rfl | hq0 := eq_or_ne a 0
  · simp
  · rw [← star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]

end LinearOrderedCommRing

section Field

variable [Field R] (a b : ℍ[R])

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: : NNRatCast ℍ[R] where nnratCast q
  body: (q : R)

中文:
实例 instNNRatCast
  签名: : 非负有理数嵌入 ℍ[R] where nnratCast q
  定义体: (q : R)
-/
instance instNNRatCast : NNRatCast ℍ[R] where nnratCast q := (q : R)
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: : RatCast ℍ[R] where ratCast q
  body: (q : R)

中文:
实例 instRatCast
  签名: : 有理数嵌入 ℍ[R] where ratCast q
  定义体: (q : R)
-/
instance instRatCast : RatCast ℍ[R] where ratCast q := (q : R)

/--
lemma `re_nnratCast` / 引理 `re_nnratCast`

English:
lemma re_nnratCast
  given: (q : Rat>=0)
  statement: (q : ℍ[R]).re = q
  proof: rfl

中文:
引理 re_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : ℍ[R]).re = q
  证明: rfl
-/
@[simp, norm_cast] lemma re_nnratCast (q : Rat>=0) : (q : ℍ[R]).re = q := rfl
/--
lemma `im_nnratCast` / 引理 `im_nnratCast`

English:
lemma im_nnratCast
  given: (q : Rat>=0)
  statement: (q : ℍ[R]).im = 0
  proof: rfl

中文:
引理 im_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : ℍ[R]).im = 0
  证明: rfl
-/
@[simp, norm_cast] lemma im_nnratCast (q : Rat>=0) : (q : ℍ[R]).im = 0 := rfl
/--
lemma `imI_nnratCast` / 引理 `imI_nnratCast`

English:
lemma imI_nnratCast
  given: (q : Rat>=0)
  statement: (q : ℍ[R]).imI = 0
  proof: rfl

中文:
引理 imI_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : ℍ[R]).imI = 0
  证明: rfl
-/
@[simp, norm_cast] lemma imI_nnratCast (q : Rat>=0) : (q : ℍ[R]).imI = 0 := rfl
/--
lemma `imJ_nnratCast` / 引理 `imJ_nnratCast`

English:
lemma imJ_nnratCast
  given: (q : Rat>=0)
  statement: (q : ℍ[R]).imJ = 0
  proof: rfl

中文:
引理 imJ_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : ℍ[R]).imJ = 0
  证明: rfl
-/
@[simp, norm_cast] lemma imJ_nnratCast (q : Rat>=0) : (q : ℍ[R]).imJ = 0 := rfl
/--
lemma `imK_nnratCast` / 引理 `imK_nnratCast`

English:
lemma imK_nnratCast
  given: (q : Rat>=0)
  statement: (q : ℍ[R]).imK = 0
  proof: rfl

中文:
引理 imK_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : ℍ[R]).imK = 0
  证明: rfl
-/
@[simp, norm_cast] lemma imK_nnratCast (q : Rat>=0) : (q : ℍ[R]).imK = 0 := rfl
/--
lemma `re_ratCast` / 引理 `re_ratCast`

English:
lemma re_ratCast
  given: (q : Rat)
  statement: (q : ℍ[R]).re = q
  proof: rfl

中文:
引理 re_ratCast
  条件: (q : 有理数)
  结论: (q : ℍ[R]).re = q
  证明: rfl
-/
@[simp, norm_cast] lemma re_ratCast (q : Rat) : (q : ℍ[R]).re = q := rfl
/--
lemma `im_ratCast` / 引理 `im_ratCast`

English:
lemma im_ratCast
  given: (q : Rat)
  statement: (q : ℍ[R]).im = 0
  proof: rfl

中文:
引理 im_ratCast
  条件: (q : 有理数)
  结论: (q : ℍ[R]).im = 0
  证明: rfl
-/
@[simp, norm_cast] lemma im_ratCast (q : Rat) : (q : ℍ[R]).im = 0 := rfl
/--
lemma `imI_ratCast` / 引理 `imI_ratCast`

English:
lemma imI_ratCast
  given: (q : Rat)
  statement: (q : ℍ[R]).imI = 0
  proof: rfl

中文:
引理 imI_ratCast
  条件: (q : 有理数)
  结论: (q : ℍ[R]).imI = 0
  证明: rfl
-/
@[simp, norm_cast] lemma imI_ratCast (q : Rat) : (q : ℍ[R]).imI = 0 := rfl
/--
lemma `imJ_ratCast` / 引理 `imJ_ratCast`

English:
lemma imJ_ratCast
  given: (q : Rat)
  statement: (q : ℍ[R]).imJ = 0
  proof: rfl

中文:
引理 imJ_ratCast
  条件: (q : 有理数)
  结论: (q : ℍ[R]).imJ = 0
  证明: rfl
-/
@[simp, norm_cast] lemma imJ_ratCast (q : Rat) : (q : ℍ[R]).imJ = 0 := rfl
/--
lemma `imK_ratCast` / 引理 `imK_ratCast`

English:
lemma imK_ratCast
  given: (q : Rat)
  statement: (q : ℍ[R]).imK = 0
  proof: rfl

中文:
引理 imK_ratCast
  条件: (q : 有理数)
  结论: (q : ℍ[R]).imK = 0
  证明: rfl
-/
@[simp, norm_cast] lemma imK_ratCast (q : Rat) : (q : ℍ[R]).imK = 0 := rfl

/--
lemma `coe_nnratCast` / 引理 `coe_nnratCast`

English:
lemma coe_nnratCast
  given: (q : Rat>=0)
  statement: ↑(q : R) = (q : ℍ[R])
  proof: rfl

中文:
引理 coe_nnratCast
  条件: (q : 有理数>=0)
  结论: ↑(q : R) = (q : ℍ[R])
  证明: rfl
-/
@[norm_cast] lemma coe_nnratCast (q : Rat>=0) : ↑(q : R) = (q : ℍ[R]) := rfl

/--
lemma `coe_ratCast` / 引理 `coe_ratCast`

English:
lemma coe_ratCast
  given: (q : Rat)
  statement: ↑(q : R) = (q : ℍ[R])
  proof: rfl

中文:
引理 coe_ratCast
  条件: (q : 有理数)
  结论: ↑(q : R) = (q : ℍ[R])
  证明: rfl
-/
@[norm_cast] lemma coe_ratCast (q : Rat) : ↑(q : R) = (q : ℍ[R]) := rfl

section ofScientific
open OfScientific (ofScientific)
variable (m : Nat) (s : Bool) (e : Nat)

/--
lemma `coe_ofScientific` / 引理 `coe_ofScientific`

English:
lemma coe_ofScientific
  statement: ((ofScientific m s e : R) : ℍ[R]) = ofScientific m s e
  proof: rfl

中文:
引理 coe_ofScientific
  结论: ((ofScientific m s e : R) : ℍ[R]) = ofScientific m s e
  证明: rfl
-/
@[norm_cast] lemma coe_ofScientific : ((ofScientific m s e : R) : ℍ[R]) = ofScientific m s e := rfl
/--
lemma `re_ofScientific` / 引理 `re_ofScientific`

English:
lemma re_ofScientific
  statement: (ofScientific m s e : ℍ[R]).re = ofScientific m s e
  proof: rfl

中文:
引理 re_ofScientific
  结论: (ofScientific m s e : ℍ[R]).re = ofScientific m s e
  证明: rfl
-/
@[simp] lemma re_ofScientific : (ofScientific m s e : ℍ[R]).re = ofScientific m s e := rfl
/--
lemma `imI_ofScientific` / 引理 `imI_ofScientific`

English:
lemma imI_ofScientific
  statement: (ofScientific m s e : ℍ[R]).imI = 0
  proof: rfl

中文:
引理 imI_ofScientific
  结论: (ofScientific m s e : ℍ[R]).imI = 0
  证明: rfl
-/
@[simp] lemma imI_ofScientific : (ofScientific m s e : ℍ[R]).imI = 0 := rfl
/--
lemma `imJ_ofScientific` / 引理 `imJ_ofScientific`

English:
lemma imJ_ofScientific
  statement: (ofScientific m s e : ℍ[R]).imJ = 0
  proof: rfl

中文:
引理 imJ_ofScientific
  结论: (ofScientific m s e : ℍ[R]).imJ = 0
  证明: rfl
-/
@[simp] lemma imJ_ofScientific : (ofScientific m s e : ℍ[R]).imJ = 0 := rfl
/--
lemma `imK_ofScientific` / 引理 `imK_ofScientific`

English:
lemma imK_ofScientific
  statement: (ofScientific m s e : ℍ[R]).imK = 0
  proof: rfl

中文:
引理 imK_ofScientific
  结论: (ofScientific m s e : ℍ[R]).imK = 0
  证明: rfl
-/
@[simp] lemma imK_ofScientific : (ofScientific m s e : ℍ[R]).imK = 0 := rfl

end ofScientific

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

@[simps -isSimp]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv ℍ[R]
  body: ⟨fun a => (normSq a)⁻¹ • star a⟩

中文:
实例 instInv
  签名: : 取逆 ℍ[R]
  定义体: ⟨fun a => (normSq a)⁻¹ • star a⟩

Depends on / 依赖: normSq
-/
instance instInv : Inv ℍ[R] :=
  ⟨fun a => (normSq a)⁻¹ • star a⟩

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: : GroupWithZero ℍ[R]
  body: { Quaternion.instNontrivial with
    inv_zero := by rw [inv_def, star_zero, smul_zero]
    mul_inv_cancel := fun a ha => by
      rw [inv_def]; rw [Algebra.mul_smul_comm (normSq a)⁻¹ a (star a)]; rw [self_mul_star]; rw [smul_coe]; rw [inv_mul_cancel₀ (normSq_ne_zero.2 ha)]; rw [coe_one] }

@[norm_cast, simp]

中文:
实例 instGroupWithZero
  签名: : 带零群 ℍ[R]
  定义体: { Quaternion.instNontrivial with
    inv_zero := by rw [inv_def, star_zero, smul_zero]
    mul_inv_cancel := fun a ha => by
      rw [inv_def]; rw [Algebra.mul_smul_comm (normSq a)⁻¹ a (star a)]; rw [self_mul_star]; rw [smul_coe]; rw [inv_mul_cancel₀ (normSq_ne_zero.2 ha)]; rw [coe_one] }

@[norm_cast, simp]

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Quaternion, Quaternion.instNontrivial, coe_one, instNontrivial, inv_def, inv_zero, mul_inv_cancel, mul_smul_comm, normSq, normSq_ne_zero, self_mul_star, smul_coe, smul_zero, star_zero
-/
instance instGroupWithZero : GroupWithZero ℍ[R] :=
  { Quaternion.instNontrivial with
    inv_zero := by rw [inv_def, star_zero, smul_zero]
    mul_inv_cancel := fun a ha => by
      rw [inv_def]; rw [Algebra.mul_smul_comm (normSq a)⁻¹ a (star a)]; rw [self_mul_star]; rw [smul_coe]; rw [inv_mul_cancel₀ (normSq_ne_zero.2 ha)]; rw [coe_one] }

@[norm_cast, simp]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : R)
  statement: ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹
  proof: map_inv₀ (algebraMap R ℍ[R]) _

@[norm_cast, simp]

中文:
定理 coe_inv
  条件: (x : R)
  结论: ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹
  证明: map_inv₀ (algebraMap R ℍ[R]) _

@[norm_cast, simp]

Depends on / 依赖: algebraMap
-/
theorem coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹ :=
  map_inv₀ (algebraMap R ℍ[R]) _

@[norm_cast, simp]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (x y : R)
  statement: ((x / y : R) : ℍ[R]) = x / y
  proof: map_div₀ (algebraMap R ℍ[R]) x y

@[norm_cast, simp]

中文:
定理 coe_div
  条件: (x y : R)
  结论: ((x / y : R) : ℍ[R]) = x / y
  证明: map_div₀ (algebraMap R ℍ[R]) x y

@[norm_cast, simp]

Depends on / 依赖: algebraMap
-/
theorem coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y :=
  map_div₀ (algebraMap R ℍ[R]) x y

@[norm_cast, simp]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (x : R) (z : Int)
  statement: ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z
  proof: map_zpow₀ (algebraMap R ℍ[R]) x z

中文:
定理 coe_zpow
  条件: (x : R) (z : 整数)
  结论: ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z
  证明: map_zpow₀ (algebraMap R ℍ[R]) x z

Depends on / 依赖: algebraMap
-/
theorem coe_zpow (x : R) (z : Int) : ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z :=
  map_zpow₀ (algebraMap R ℍ[R]) x z

/--
Instance `instDivisionRing` / 实例 `instDivisionRing`

English:
instance instDivisionRing
  signature: : DivisionRing ℍ[R] where
  body: Quaternion.instRing
  __ := Quaternion.instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def _ := by rw [← coe_nnratCast, NNRat.cast_def, coe_div, coe_natCast, coe_natCast]
  ratCast_def _ := by rw [← coe_ratCast, Rat.cast_def, coe_div, coe_intCast, coe_natCast]
  nnqsmul_def _ _ := by rw [← coe_nnratCast, coe_mul_eq_smul]; ext <;> exact NNRat.smul_def ..
  qsmul_def _ _ := by rw [← coe_ratCast, coe_mul_eq_smul]; ext <;> exact Rat.smul_def ..

中文:
实例 instDivisionRing
  签名: : 除环 ℍ[R] where
  定义体: Quaternion.instRing
  __ := Quaternion.instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def _ := by rw [← coe_nnratCast, NNRat.cast_def, coe_div, coe_natCast, coe_natCast]
  ratCast_def _ := by rw [← coe_ratCast, Rat.cast_def, coe_div, coe_intCast, coe_natCast]
  nnqsmul_def _ _ := by rw [← coe_nnratCast, coe_mul_eq_smul]; ext <;> exact NNRat.smul_def ..
  qsmul_def _ _ := by rw [← coe_ratCast, coe_mul_eq_smul]; ext <;> exact Rat.smul_def ..

Depends on / 依赖: Quaternion, Quaternion.instRing, instRing
-/
instance instDivisionRing : DivisionRing ℍ[R] where
  __ := Quaternion.instRing
  __ := Quaternion.instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def _ := by rw [← coe_nnratCast, NNRat.cast_def, coe_div, coe_natCast, coe_natCast]
  ratCast_def _ := by rw [← coe_ratCast, Rat.cast_def, coe_div, coe_intCast, coe_natCast]
  nnqsmul_def _ _ := by rw [← coe_nnratCast, coe_mul_eq_smul]; ext <;> exact NNRat.smul_def ..
  qsmul_def _ _ := by rw [← coe_ratCast, coe_mul_eq_smul]; ext <;> exact Rat.smul_def ..

/--
theorem `normSq_inv` / 定理 `normSq_inv`

English:
theorem normSq_inv
  statement: normSq a⁻¹ = (normSq a)⁻¹
  proof: map_inv₀ normSq _

中文:
定理 normSq_inv
  结论: normSq a⁻¹ = (normSq a)⁻¹
  证明: map_inv₀ normSq _

Depends on / 依赖: normSq
-/
theorem normSq_inv : normSq a⁻¹ = (normSq a)⁻¹ :=
  map_inv₀ normSq _

/--
theorem `normSq_div` / 定理 `normSq_div`

English:
theorem normSq_div
  statement: normSq (a / b) = normSq a / normSq b
  proof: map_div₀ normSq a b

中文:
定理 normSq_div
  结论: normSq (a / b) = normSq a / normSq b
  证明: map_div₀ normSq a b

Depends on / 依赖: normSq
-/
theorem normSq_div : normSq (a / b) = normSq a / normSq b :=
  map_div₀ normSq a b

/--
theorem `normSq_zpow` / 定理 `normSq_zpow`

English:
theorem normSq_zpow
  given: (z : Int)
  statement: normSq (a ^ z) = normSq a ^ z
  proof: map_zpow₀ normSq a z

@[norm_cast]

中文:
定理 normSq_zpow
  条件: (z : 整数)
  结论: normSq (a ^ z) = normSq a ^ z
  证明: map_zpow₀ normSq a z

@[norm_cast]

Depends on / 依赖: normSq
-/
theorem normSq_zpow (z : Int) : normSq (a ^ z) = normSq a ^ z :=
  map_zpow₀ normSq a z

@[norm_cast]
/--
theorem `normSq_ratCast` / 定理 `normSq_ratCast`

English:
theorem normSq_ratCast
  given: (q : Rat)
  statement: normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2
  proof: by
  rw [← coe_ratCast]; rw [normSq_coe]; rw [coe_pow]

中文:
定理 normSq_ratCast
  条件: (q : 有理数)
  结论: normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2
  证明: by
  rw [← coe_ratCast]; rw [normSq_coe]; rw [coe_pow]

Depends on / 依赖: coe_pow, coe_ratCast, normSq_coe
-/
theorem normSq_ratCast (q : Rat) : normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2 := by
  rw [← coe_ratCast]; rw [normSq_coe]; rw [coe_pow]

end Field

end Quaternion

namespace Cardinal

open Quaternion

section QuaternionAlgebra

variable {R : Type*} (c₁ c₂ c₃ : R)

/--
theorem `pow_four` / 定理 `pow_four`

English:
theorem pow_four
  given: [Infinite R]
  statement: #R ^ 4 = #R
  proof: power_nat_eq (aleph0_le_mk R) by decide

中文:
定理 pow_four
  条件: [无限 R]
  结论: #R ^ 4 = #R
  证明: power_nat_eq (aleph0_le_mk R) by decide
-/
private theorem pow_four [Infinite R] : #R ^ 4 = #R :=
power_nat_eq (aleph0_le_mk R) by decide

/--
theorem `mk_quaternionAlgebra` / 定理 `mk_quaternionAlgebra`

English:
theorem mk_quaternionAlgebra
  statement: #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4
  proof: by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂ c₃)]
  simp only [mk_prod, lift_id]
  ring

@[simp]

中文:
定理 mk_quaternionAlgebra
  结论: #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4
  证明: by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂ c₃)]
  simp only [mk_prod, lift_id]
  ring

@[simp]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.equivProd, equivProd, lift_id, mk_congr, mk_prod
-/
theorem mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂ c₃)]
  simp only [mk_prod, lift_id]
  ring

@[simp]
/--
theorem `mk_quaternionAlgebra_of_infinite` / 定理 `mk_quaternionAlgebra_of_infinite`

English:
theorem mk_quaternionAlgebra_of_infinite
  given: [Infinite R]
  statement: #(ℍ[R,c₁,c₂,c₃]) = #R
  proof: by
  rw [mk_quaternionAlgebra]; rw [pow_four]

中文:
定理 mk_quaternionAlgebra_of_infinite
  条件: [无限 R]
  结论: #(ℍ[R,c₁,c₂,c₃]) = #R
  证明: by
  rw [mk_quaternionAlgebra]; rw [pow_four]

Depends on / 依赖: mk_quaternionAlgebra, pow_four
-/
theorem mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R := by
  rw [mk_quaternionAlgebra]; rw [pow_four]

/--
theorem `mk_univ_quaternionAlgebra` / 定理 `mk_univ_quaternionAlgebra`

English:
theorem mk_univ_quaternionAlgebra
  statement: #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4
  proof: by
  rw [mk_univ]; rw [mk_quaternionAlgebra]

中文:
定理 mk_univ_quaternionAlgebra
  结论: #(集合.univ : 集合 ℍ[R,c₁,c₂,c₃]) = #R ^ 4
  证明: by
  rw [mk_univ]; rw [mk_quaternionAlgebra]

Depends on / 依赖: mk_quaternionAlgebra, mk_univ
-/
theorem mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_univ]; rw [mk_quaternionAlgebra]

/--
theorem `mk_univ_quaternionAlgebra_of_infinite` / 定理 `mk_univ_quaternionAlgebra_of_infinite`

English:
theorem mk_univ_quaternionAlgebra_of_infinite
  given: [Infinite R]
  proof: by rw [mk_univ_quaternionAlgebra, pow_four]

中文:
定理 mk_univ_quaternionAlgebra_of_infinite
  条件: [无限 R]
  证明: by rw [mk_univ_quaternionAlgebra, pow_four]

Depends on / 依赖: mk_univ_quaternionAlgebra, pow_four
-/
theorem mk_univ_quaternionAlgebra_of_infinite [Infinite R] :
    #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R := by rw [mk_univ_quaternionAlgebra, pow_four]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Repr
  signature: R] {a b c
  body: s!"\{ re := {repr q.re}, imI := {repr q.imI}, imJ := {repr q.imJ}, imK := {repr q.imK} }"

中文:
实例 [Repr
  签名: R] {a b c
  定义体: s!"\{ re := {repr q.re}, imI := {repr q.imI}, imJ := {repr q.imJ}, imK := {repr q.imK} }"

Depends on / 依赖: q.imI, q.imJ, q.imK, q.re
-/
instance [Repr R] {a b c : R} : Repr ℍ[R,a,b,c] where
  reprPrec q _ :=
    s!"\{ re := {repr q.re}, imI := {repr q.imI}, imJ := {repr q.imJ}, imK := {repr q.imK} }"

end QuaternionAlgebra

section Quaternion

variable (R : Type*) [Zero R] [One R] [Neg R]

/-- The cardinality of the quaternions, as a type. -/
@[simp]
/--
theorem `mk_quaternion` / 定理 `mk_quaternion`

English:
theorem mk_quaternion
  statement: #(ℍ[R]) = #R ^ 4
  proof: mk_quaternionAlgebra _ _ _

中文:
定理 mk_quaternion
  结论: #(ℍ[R]) = #R ^ 4
  证明: mk_quaternionAlgebra _ _ _

Depends on / 依赖: mk_quaternionAlgebra
-/
theorem mk_quaternion : #(ℍ[R]) = #R ^ 4 :=
  mk_quaternionAlgebra _ _ _

/--
theorem `mk_quaternion_of_infinite` / 定理 `mk_quaternion_of_infinite`

English:
theorem mk_quaternion_of_infinite
  given: [Infinite R]
  statement: #(ℍ[R]) = #R
  proof: mk_quaternionAlgebra_of_infinite _ _ _

中文:
定理 mk_quaternion_of_infinite
  条件: [无限 R]
  结论: #(ℍ[R]) = #R
  证明: mk_quaternionAlgebra_of_infinite _ _ _

Depends on / 依赖: mk_quaternionAlgebra_of_infinite
-/
theorem mk_quaternion_of_infinite [Infinite R] : #(ℍ[R]) = #R :=
  mk_quaternionAlgebra_of_infinite _ _ _

/--
theorem `mk_univ_quaternion` / 定理 `mk_univ_quaternion`

English:
theorem mk_univ_quaternion
  statement: #(Set.univ : Set ℍ[R]) = #R ^ 4
  proof: mk_univ_quaternionAlgebra _ _ _

中文:
定理 mk_univ_quaternion
  结论: #(集合.univ : 集合 ℍ[R]) = #R ^ 4
  证明: mk_univ_quaternionAlgebra _ _ _

Depends on / 依赖: mk_univ_quaternionAlgebra
-/
theorem mk_univ_quaternion : #(Set.univ : Set ℍ[R]) = #R ^ 4 :=
  mk_univ_quaternionAlgebra _ _ _

/--
theorem `mk_univ_quaternion_of_infinite` / 定理 `mk_univ_quaternion_of_infinite`

English:
theorem mk_univ_quaternion_of_infinite
  given: [Infinite R]
  statement: #(Set.univ : Set ℍ[R]) = #R
  proof: mk_univ_quaternionAlgebra_of_infinite _ _ _

中文:
定理 mk_univ_quaternion_of_infinite
  条件: [无限 R]
  结论: #(集合.univ : 集合 ℍ[R]) = #R
  证明: mk_univ_quaternionAlgebra_of_infinite _ _ _

Depends on / 依赖: mk_univ_quaternionAlgebra_of_infinite
-/
theorem mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R :=
  mk_univ_quaternionAlgebra_of_infinite _ _ _

end Quaternion

end Cardinal
