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
/-
**QuaternionAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → R → R → R → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quaternion algebra over a type with fixed coefficients where $i^2 = a + bi$ and 
$j^2 = c$,
denoted as `ℍ[R,a,b]`.
Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`.
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
/-
**QuaternionAlgebra.equivProd** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：equivProd {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ R × R × R × R where
 toFun a
参数：c₁ c₂ c₃ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between a quaternion algebra over `R` and `R × R × R × R`.
-/
def equivProd {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ R × R × R × R where
  toFun a := ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩

/-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
@[simps symm_apply]
/-
**QuaternionAlgebra.equivTuple** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：equivTuple {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ (Fin 4 -> R) where
 toFun a
参数：c₁ c₂ c₃ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between a quaternion algebra over `R` and `Fin 4 → R`.
-/
def equivTuple {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ (Fin 4 → R) where
  toFun a := ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  right_inv _ := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]
/-
**QuaternionAlgebra.equivTuple_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebr
a`。
形式化陈述：equivTuple_apply {R : Type*} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃]) : equivTup
le c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK]
参数：c₁ c₂ c₃ : R；x : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃]) :
    equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

@[simp]
/-
**QuaternionAlgebra.mk.eta** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra.mk`。
形式化陈述：∀ {R : Type u_1} {c₁ c₂ c₃ : R} (a : QuaternionAlgebra R c₁ c₂ c₃),   { re
 := a.re, imI := a.imI, imJ := a.imJ, imK := a.imK } = a
参数：a : QuaternionAlgebra R c₁ c₂ c₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃]) : mk a.1 a.2 a.3 a.4 = a := rfl

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton R] : Subsingleton ℍ[R,c₁,c₂,c₃] := (equivTuple c₁ c₂ c₃).subsingleton
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial ℍ[R,c₁,c₂,c₃] := (equivTuple c₁ c₂ c₃).surjective.nontrivial

section Zero
variable [Zero R]

/-- The imaginary part of a quaternion.

Note that unless `c₂ = 0`, this definition is not particularly well-behaved;
for instance, `QuaternionAlgebra.star_im` only says that the star of an imaginary quaternion
is imaginary under this condition. -/
/-
**QuaternionAlgebra.im** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃]
参数：x : ℍ[R,c₁,c₂,c₃]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The imaginary part of a quaternion.

Note that unless `c₂ = 0`, this definition is not particularly well-behaved;
for instance, `QuaternionAlgebra.star_im` only says that the star of an imaginar
y quaternion
is imaginary under this condition.
-/
def im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃] :=
  ⟨0, x.imI, x.imJ, x.imK⟩

@[simp]
/-
**QuaternionAlgebra.re_im** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：re_im : a.im.re = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_im : a.im.re = 0 :=
  rfl

@[simp]
/-
**QuaternionAlgebra.imI_im** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imI_im : a.im.imI = a.imI
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_im : a.im.imI = a.imI :=
  rfl

@[simp]
/-
**QuaternionAlgebra.imJ_im** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imJ_im : a.im.imJ = a.imJ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_im : a.im.imJ = a.imJ :=
  rfl

@[simp]
/-
**QuaternionAlgebra.imK_im** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imK_im : a.im.imK = a.imK
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_im : a.im.imK = a.imK :=
  rfl

@[simp]
/-
**QuaternionAlgebra.im_idem** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im_idem : a.im.im = a.im
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_idem : a.im.im = a.im :=
  rfl

/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
/-
**QuaternionAlgebra.coe** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：{R : Type u_3} → {c₁ c₂ c₃ : R} → [Zero R] → R → QuaternionAlgebra R c₁ c₂
 c₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `R → ℍ[R,c₁,c₂,c₃]`.
-/
@[coe] def coe (x : R) : ℍ[R,c₁,c₂,c₃] := ⟨x, 0, 0, 0⟩
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `R → ℍ[R,c₁,c₂,c₃]`.
-/
instance : CoeTC R ℍ[R,c₁,c₂,c₃] := ⟨coe⟩

@[simp, norm_cast]
/-
**QuaternionAlgebra.re_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：re_coe : (x : ℍ[R,c₁,c₂,c₃]).re = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_coe : (x : ℍ[R,c₁,c₂,c₃]).re = x := rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imI_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imI_coe : (x : ℍ[R,c₁,c₂,c₃]).imI = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_coe : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imJ_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imJ_coe : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_coe : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imK_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imK_coe : (x : ℍ[R,c₁,c₂,c₃]).imK = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_coe : (x : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl
/-
**QuaternionAlgebra.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_injective : Function.Injective (coe : R -> ℍ[R,c₁,c₂,c₃])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂,c₃]) := fun _ _ h => congr_arg re h

@[simp]
/-
**QuaternionAlgebra.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `QuaternionAlgebra.coe_injective`：coe_injective : Function.Injective (coe
 : R -> ℍ[R,c₁,c₂,c₃])
-/
theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simps]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero ℍ[R,c₁,c₂,c₃] := ⟨⟨0, 0, 0, 0⟩⟩
/-
**QuaternionAlgebra.im_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} [inst : Zero R], QuaternionAlgebra.im 0 = 
0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem im_zero : (0 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0 := rfl
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℍ[R,c₁,c₂,c₃] := ⟨0⟩

section One
variable [One R]

@[simps]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ℍ[R,c₁,c₂,c₃] := ⟨⟨1, 0, 0, 0⟩⟩
/-
**QuaternionAlgebra.im_one** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} [inst : Zero R] [inst_1 : One R], Quaterni
onAlgebra.im 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem im_one : (1 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1 := rfl

end One
end Zero
section Add
variable [Add R]

@[simps]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp]
/-
**QuaternionAlgebra.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) : (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃])
 + mk b₁ b₂ b₃ b₄ = mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄)
参数：a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + mk b₁ b₂ b₃ b₄ =
    mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

/-- The additive equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
/-
**QuaternionAlgebra.addEquivTuple** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：addEquivTuple (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ (Fin 4 -> R)
参数：c₁ c₂ c₃ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence between a quaternion algebra over `R` and `Fin 4 → R`.
-/
def addEquivTuple (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ (Fin 4 → R) := (equivTuple ..).addEquiv

@[simp]
/-
**QuaternionAlgebra.coe_addEquivTuple** 是 Mathlib 中的一个引理，位于命名空间 `QuaternionAlgeb
ra`。
形式化陈述：coe_addEquivTuple (c₁ c₂ c₃ : R) : ⇑(addEquivTuple c₁ c₂ c₃) = equivTuple 
c₁ c₂ c₃
参数：c₁ c₂ c₃ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_addEquivTuple (c₁ c₂ c₃ : R) : ⇑(addEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := rfl
/-
**QuaternionAlgebra.coe_symm_addEquivTuple** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion
Algebra`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] (c₁ c₂ c₃ : R),   ⇑(QuaternionAlgebra.addE
quivTuple c₁ c₂ c₃).symm = ⇑(QuaternionAlgebra.equivTuple c₁ c₂ c₃).symm
参数：c₁ c₂ c₃ : R；QuaternionAlgebra.addEquivTuple c₁ c₂ c₃；QuaternionAlgebra.equiv
Tuple c₁ c₂ c₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_symm_addEquivTuple (c₁ c₂ c₃ : R) :
    ⇑(addEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/-- The additive equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
/-
**QuaternionAlgebra.addEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：addEquivProd (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ R × R × R × R
参数：c₁ c₂ c₃ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence between a quaternion algebra over `R` and `R × R × R × 
R`.
-/
def addEquivProd (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ R × R × R × R := (equivProd ..).addEquiv

@[simp]
/-
**QuaternionAlgebra.coe_addEquivProd** 是 Mathlib 中的一个引理，位于命名空间 `QuaternionAlgebr
a`。
形式化陈述：coe_addEquivProd (c₁ c₂ c₃ : R) : ⇑(addEquivProd c₁ c₂ c₃) = equivProd c₁ 
c₂ c₃
参数：c₁ c₂ c₃ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_addEquivProd (c₁ c₂ c₃ : R) : ⇑(addEquivProd c₁ c₂ c₃) = equivProd c₁ c₂ c₃ := rfl
/-
**QuaternionAlgebra.coe_symm_addEquivProd** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionA
lgebra`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] (c₁ c₂ c₃ : R),   ⇑(QuaternionAlgebra.addE
quivProd c₁ c₂ c₃).symm = ⇑(QuaternionAlgebra.equivProd c₁ c₂ c₃).symm
参数：c₁ c₂ c₃ : R；QuaternionAlgebra.addEquivProd c₁ c₂ c₃；QuaternionAlgebra.equivP
rod c₁ c₂ c₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_symm_addEquivProd (c₁ c₂ c₃ : R) :
    ⇑(addEquivProd c₁ c₂ c₃).symm = (equivProd c₁ c₂ c₃).symm := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

/-
**QuaternionAlgebra.im_add** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a b : QuaternionAlgebra R c₁ c₂ c₃) [inst
 : AddZeroClass R], (a + b).im = a.im + b.im
参数：a b : QuaternionAlgebra R c₁ c₂ c₃；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
@[simp] theorem im_add : (a + b).im = a.im + b.im :=
  QuaternionAlgebra.ext (zero_add _).symm rfl rfl rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y := by ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

@[simps]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg ℍ[R,c₁,c₂,c₃] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp]
/-
**QuaternionAlgebra.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, 
-a₃, -a₄⟩
参数：a₁ a₂ a₃ a₄ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
  rfl

end Neg

section AddGroup
variable [AddGroup R]

/-
**QuaternionAlgebra.im_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : QuaternionAlgebra R c₁ c₂ c₃) [inst :
 AddGroup R], (-a).im = -a.im
参数：a : QuaternionAlgebra R c₁ c₂ c₃；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
@[simp] theorem im_neg : (-a).im = -a.im :=
  QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x := by ext <;> simp

@[simps]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩
/-
**QuaternionAlgebra.im_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a b : QuaternionAlgebra R c₁ c₂ c₃) [inst
 : AddGroup R], (a - b).im = a.im - b.im
参数：a b : QuaternionAlgebra R c₁ c₂ c₃；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
@[simp] theorem im_sub : (a - b).im = a.im - b.im :=
  QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl

@[simp]
/-
**QuaternionAlgebra.mk_sub_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) : (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃])
 - mk b₁ b₂ b₃ b₄ = mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄)
参数：a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) - mk b₁ b₂ b₃ b₄ =
    mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.im_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im_coe : (x : ℍ[R,c₁,c₂,c₃]).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_coe : (x : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[simp]
/-
**QuaternionAlgebra.re_add_im** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：re_add_im : ↑a.re + a.im = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem re_add_im : ↑a.re + a.im = a :=
  QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

@[simp]
/-
**QuaternionAlgebra.sub_im_self** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：sub_im_self : a - a.im = a.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem sub_im_self : a - a.im = a.re :=
  QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

@[simp]
/-
**QuaternionAlgebra.sub_re_self** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：sub_re_self : a - a.re = a.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
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
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁ + c₂ * i`;
* `j * j = c₃`;
* `i * j = k`, `j * i = c₂ * j - k`;
* `k * k = - c₁ * c₃`;
* `i * k = c₁ * j + c₂ * k`, `k * i = -c₁ * j`;
* `j * k = c₂ * c₃ - c₃ * i`, `k * j = c₃ * i`.
-/
instance : Mul ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
/-
**QuaternionAlgebra.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) : (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃])
 * mk b₁ b₂ b₃ b₄ = mk (a₁ * b₁ + c₁ * a₂ * b₂ + c₃ * a₃ * b₃ + c₂ * c₃ * a₃ * b
₄ - c₁ * c₃ * a₄ * b₄) (a₁ * b₂ + a₂ * b₁ + c₂ * a₂ * b₂ - c₃ * a₃ * b₄ + c₃ * a
₄ * b₃) (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ + c₂ * a₃ * b₂ - c₁ * a₄ * b₂) (a₁ * b
₄ + a₂ * b₃ + c₂ * a₂ * b₄ - a₃ * b₂ + a₄ * b₁)
参数：a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S ℍ[R,c₁,c₂,c₃] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
  smul_assoc s t x := by ext <;> exact smul_assoc _ _ _
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
  smul_comm s t x := by ext <;> exact smul_comm _ _ _
/-
**QuaternionAlgebra.im_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : QuaternionAlgebra R c₁ c₂ c₃) {S : Ty
pe u_4} [inst : CommRing R]   [inst_1 : SMulZeroClass S R] (s : S), (s • a).im =
 s • a.im
参数：a : QuaternionAlgebra R c₁ c₂ c₃；s : S；s • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] theorem im_smul {S} [CommRing R] [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.ext (smul_zero s).symm rfl rfl rfl

@[simp]
/-
**QuaternionAlgebra.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：smul_mk (re im_i im_j im_k : R) : s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,
c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩
参数：re im_i im_j im_k : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mk (re im_i im_j im_k : R) :
    s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
  rfl

end SMul

/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [MulAction S R] : MulAction S ℍ[R,c₁,c₂,c₃] :=
  (equivProd ..).injective.mulAction _ fun _ _ ↦ rfl
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] : AddCommGroup ℍ[R,c₁,c₂,c₃] := by
  apply (equivProd c₁ c₂ c₃).injective.addCommGroup <;> intros <;> rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R,c₁
,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃])
参数：s : S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃]) :=
  QuaternionAlgebra.ext rfl (smul_zero _).symm (smul_zero _).symm (smul_zero _).symm
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [AddCommGroup R] [DistribMulAction S R] : DistribMulAction S ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.distribMulAction (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ ↦ rfl
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [AddCommGroup R] [Module S R] : Module S ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.module _ (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ ↦ rfl

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃] where
  natCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  natCast_zero := by simp
  natCast_succ := by simp
  intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
  intCast_negSucc n := by
    change coe _ = -coe _
    rw [Int.cast_negSucc, coe_neg]

@[simp, norm_cast]
/-
**QuaternionAlgebra.re_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：re_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).re = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).re = n :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imI_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imI_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imJ_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imJ_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imK_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imK_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.im_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im_natCast (n : Nat) : (n : ℍ[R,c₁,c₂,c₃]).im = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[norm_cast]
/-
**QuaternionAlgebra.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_natCast (n : Nat) : ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃]) :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.re_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：re_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).re = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).re = z :=
  rfl

@[scoped simp]
/-
**QuaternionAlgebra.re_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(
n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(n) := rfl

@[scoped simp]
/-
**QuaternionAlgebra.imI_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imI_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[scoped simp]
/-
**QuaternionAlgebra.imJ_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imJ_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[scoped simp]
/-
**QuaternionAlgebra.imK_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imK_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

@[scoped simp]
/-
**QuaternionAlgebra.im_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).im = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imI_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imI_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imJ_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imJ_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.imK_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imK_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[simp, norm_cast]
/-
**QuaternionAlgebra.im_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im_intCast (z : Int) : (z : ℍ[R,c₁,c₂,c₃]).im = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[norm_cast]
/-
**QuaternionAlgebra.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_intCast (z : Int) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃])
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃]) :=
  rfl

end AddCommGroupWithOne

-- For the remainder of the file we assume `CommRing R`.
variable [CommRing R]

/-
**QuaternionAlgebra.instRing** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
形式化陈述：instRing : Ring ℍ[R,c₁,c₂,c₃] where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**QuaternionAlgebra.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y := by ext <;> simp

@[norm_cast, simp]
/-
**QuaternionAlgebra.coe_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_ofNat {n : Nat} [n.AtLeastTwo] : ((ofNat(n) : R) : ℍ[R,c₁,c₂,c₃]) = (o
fNat(n) : ℍ[R,c₁,c₂,c₃])
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofNat {n : ℕ} [n.AtLeastTwo] :
    ((ofNat(n) : R) : ℍ[R,c₁,c₂,c₃]) = (ofNat(n) : ℍ[R,c₁,c₂,c₃]) :=
  rfl
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**QuaternionAlgebra.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩ :=
  rfl
/-
**QuaternionAlgebra.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAl
gebra`。
形式化陈述：algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ -> _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `QuaternionAlgebra.mk.injEq`：∀ {R : Type u_1} {a b c : R} (re imI imJ imK
 re_1 imI_1 imJ_1 imK_1 : R),   ({ re := re, imI := imI, imJ := imJ, imK := imK 
} = { re := re_1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree R ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.moduleIsTorsionFree _ fun _ _ ↦ rfl

section

variable (c₁ c₂ c₃)

/-- `QuaternionAlgebra.re` as a `LinearMap` -/
@[simps]
/-
**QuaternionAlgebra.re** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：{R : Type u_1} → {a b c : R} → QuaternionAlgebra R a b c → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuaternionAlgebra.re` as a `LinearMap`
-/
def reₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imI` as a `LinearMap` -/
@[simps]
/-
**QuaternionAlgebra.imI** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：{R : Type u_1} → {a b c : R} → QuaternionAlgebra R a b c → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuaternionAlgebra.imI` as a `LinearMap`
-/
def imIₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imJ` as a `LinearMap` -/
@[simps]
/-
**QuaternionAlgebra.imJ** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：{R : Type u_1} → {a b c : R} → QuaternionAlgebra R a b c → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuaternionAlgebra.imJ` as a `LinearMap`
-/
def imJₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imK` as a `LinearMap` -/
@[simps]
/-
**QuaternionAlgebra.imK** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：{R : Type u_1} → {a b c : R} → QuaternionAlgebra R a b c → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuaternionAlgebra.imK` as a `LinearMap`
-/
def imKₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.equivTuple` as a linear equivalence. -/
/-
**QuaternionAlgebra.linearEquivTuple** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebr
a`。
形式化陈述：linearEquivTuple : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuaternionAlgebra.equivTuple` as a linear equivalence.
-/
def linearEquivTuple : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 → R := (equivTuple ..).linearEquiv _

@[simp]
/-
**QuaternionAlgebra.coe_linearEquivTuple** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAl
gebra`。
形式化陈述：coe_linearEquivTuple : ⇑(linearEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_linearEquivTuple :
    ⇑(linearEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := rfl

@[simp]
/-
**QuaternionAlgebra.coe_linearEquivTuple_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quatern
ionAlgebra`。
形式化陈述：coe_linearEquivTuple_symm : ⇑(linearEquivTuple c₁ c₂ c₃).symm = (equivTupl
e c₁ c₂ c₃).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_linearEquivTuple_symm :
    ⇑(linearEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/-- `ℍ[R,c₁,c₂,c₃]` has a basis over `R` given by `1`, `i`, `j`, and `k`. -/
/-
**QuaternionAlgebra.basisOneIJK** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℍ[R,c₁,c₂,c₃]` has a basis over `R` given by `1`, `i`, `j`, and `k`.
-/
noncomputable def basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃] :=
  .ofEquivFun <| linearEquivTuple c₁ c₂ c₃

@[simp]
/-
**QuaternionAlgebra.coe_basisOneIJK_repr** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAl
gebra`。
形式化陈述：coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) : ((basisOneIJK c₁ c₂ c₃).repr q)
 = ![q.re, q.imI, q.imJ, q.imK]
参数：q : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) :
    ((basisOneIJK c₁ c₂ c₃).repr q) = ![q.re, q.imI, q.imJ, q.imK] :=
  rfl
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)
/-
**QuaternionAlgebra.rank_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [rank_eq_card_basis (basisOneIJK c₁ c₂ c₃), Fintype.card_fin]
  norm_num
/-
**QuaternionAlgebra.finrank_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
`。
形式化陈述：finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] =
 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuaternionAlgebra.rank_eq_four`：rank_eq_four [StrongRankCondition R] : M
odule.rank R ℍ[R,c₁,c₂,c₃] = 4
· 使用定理 `Cardinal.toNat_ofNat`：toNat_ofNat (n : Nat) [n.AtLeastTwo] : Cardinal.to
Nat ofNat(n) = OfNat.ofNat n
-/
theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [Module.finrank, rank_eq_four, Cardinal.toNat_ofNat]

/-- There is a natural equivalence when swapping the first and third coefficients of a
  quaternion algebra if `c₂` is 0. -/
@[simps]
/-
**QuaternionAlgebra.swapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：swapEquiv : ℍ[R,c₁,0,c₃] ≃ₐ[R] ℍ[R,c₃,0,c₁] where toFun t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a natural equivalence when swapping the first and third coefficients of
 a
  quaternion algebra if `c₂` is 0.
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
/-
**QuaternionAlgebra.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
-/
theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y :=
  (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

@[norm_cast, simp]
/-
**QuaternionAlgebra.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n :=
  (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n
/-
**QuaternionAlgebra.coe_commutes** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_commutes : ↑r * a = a * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
-/
theorem coe_commutes : ↑r * a = a * r :=
  Algebra.commutes r a
/-
**QuaternionAlgebra.coe_commute** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_commute : Commute (↑r) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_commutes`：coe_commutes : ↑r * a = a * r
-/
theorem coe_commute : Commute (↑r) a :=
  coe_commutes r a
/-
**QuaternionAlgebra.coe_mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
`。
形式化陈述：coe_mul_eq_smul : ↑r * a = r • a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem coe_mul_eq_smul : ↑r * a = r • a :=
  (Algebra.smul_def r a).symm
/-
**QuaternionAlgebra.mul_coe_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
`。
形式化陈述：mul_coe_eq_smul : a * r = r • a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.coe_commutes`：coe_commutes : ↑r * a = a * r
· 使用定理 `QuaternionAlgebra.coe_mul_eq_smul`：coe_mul_eq_smul : ↑r * a = r • a
-/
theorem mul_coe_eq_smul : a * r = r • a := by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp]
/-
**QuaternionAlgebra.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`
。
形式化陈述：coe_algebraMap : ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap : ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe :=
  rfl
/-
**QuaternionAlgebra.smul_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `QuaternionAlgebra.coe_mul_eq_smul`：coe_mul_eq_smul : ↑r * a = r • a
-/
theorem smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]

/-- Quaternion conjugate. -/
/-
**QuaternionAlgebra.instStarQuaternionAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Quatern
ionAlgebra`。
形式化陈述：instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂,c₃] where star a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quaternion conjugate.
-/
instance instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂,c₃] where star a :=
  ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩
/-
**QuaternionAlgebra.re_star** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : QuaternionAlgebra R c₁ c₂ c₃) [inst :
 CommRing R], (star a).re = a.re + c₂ * a.imI
参数：a : QuaternionAlgebra R c₁ c₂ c₃；star a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_star : (star a).re = a.re + c₂ * a.imI := rfl

@[simp]
/-
**QuaternionAlgebra.imI_star** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imI_star : (star a).imI = -a.imI
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_star : (star a).imI = -a.imI :=
  rfl

@[simp]
/-
**QuaternionAlgebra.imJ_star** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imJ_star : (star a).imJ = -a.imJ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_star : (star a).imJ = -a.imJ :=
  rfl

@[simp]
/-
**QuaternionAlgebra.imK_star** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：imK_star : (star a).imK = -a.imK
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_star : (star a).imK = -a.imK :=
  rfl

@[simp]
/-
**QuaternionAlgebra.im_star** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：im_star : (star a).im = -a.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem im_star : (star a).im = -a.im :=
  QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp]
/-
**QuaternionAlgebra.star_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨a₁ + 
c₂ * a₂, -a₂, -a₃, -a₄⟩
参数：a₁ a₂ a₃ a₄ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
    ⟨a₁ + c₂ * a₂, -a₂, -a₃, -a₄⟩ := rfl
/-
**QuaternionAlgebra.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
形式化陈述：instStarRing : StarRing ℍ[R,c₁,c₂,c₃] where star_involutive x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing : StarRing ℍ[R,c₁,c₂,c₃] where
  star_involutive x := by simp [Star.star]
  star_add a b := by ext <;> simp [add_comm]; ring
  star_mul a b := by ext <;> simp <;> ring
/-
**QuaternionAlgebra.self_add_star'** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`
。
形式化陈述：self_add_star' : a + star a = ↑(2 * a.re + c₂ * a.imI)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `QuaternionAlgebra.coe_add`：coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x +
 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
（共 38 条，此处仅展示前 30 条）
-/
theorem self_add_star' : a + star a = ↑(2 * a.re + c₂ * a.imI) := by ext <;> simp [two_mul]; ring
/-
**QuaternionAlgebra.self_add_star** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：self_add_star : a + star a = 2 * a.re + c₂ * a.imI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuaternionAlgebra.self_add_star'`：self_add_star' : a + star a = ↑(2 * a.
re + c₂ * a.imI)
· 使用定理 `QuaternionAlgebra.coe_add`：coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x +
 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by simp [self_add_star']
/-
**QuaternionAlgebra.star_add_self'** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`
。
形式化陈述：star_add_self' : star a + a = ↑(2 * a.re + c₂ * a.imI)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `QuaternionAlgebra.self_add_star'`：self_add_star' : a + star a = ↑(2 * a.
re + c₂ * a.imI)
-/
theorem star_add_self' : star a + a = ↑(2 * a.re + c₂ * a.imI) := by rw [add_comm, self_add_star']
/-
**QuaternionAlgebra.star_add_self** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_add_self : star a + a = 2 * a.re + c₂ * a.imI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `QuaternionAlgebra.self_add_star`：self_add_star : a + star a = 2 * a.re +
 c₂ * a.imI
-/
theorem star_add_self : star a + a = 2 * a.re + c₂ * a.imI := by rw [add_comm, self_add_star]
/-
**QuaternionAlgebra.star_eq_two_re_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlge
bra`。
形式化陈述：star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `QuaternionAlgebra.star_add_self'`：star_add_self' : star a + a = ↑(2 * a.
re + c₂ * a.imI)
-/
theorem star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a :=
  eq_sub_iff_add_eq.2 a.star_add_self'
/-
**QuaternionAlgebra.comm** 是 Mathlib 中的一个引理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：comm (r : R) (x : ℍ[R,c₁,c₂,c₃]) : r * x = x * r
参数：r : R；x : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma comm (r : R) (x : ℍ[R,c₁,c₂,c₃]) : r * x = x * r := by
  ext <;> simp [mul_comm]
/-
**QuaternionAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStarNormal a :=
  ⟨by
    rw [commute_iff_eq, a.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[simp, norm_cast]
/-
**QuaternionAlgebra.star_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x := by ext <;> simp
/-
**QuaternionAlgebra.star_im** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : QuaternionAlgebra R c₁ c₂ c₃) [inst :
 CommRing R], star a.im = -a.im + ↑c₂ * ↑a.imI
参数：a : QuaternionAlgebra R c₁ c₂ c₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
@[simp] theorem star_im : star a.im = -a.im + c₂ * a.imI := by ext <;> simp

@[simp]
/-
**QuaternionAlgebra.star_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (s : S) 
(a : ℍ[R,c₁,c₂,c₃]) : star (s • a) = s • star a
参数：s : S；a : ℍ[R,c₁,c₂,c₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (s : S) (a : ℍ[R,c₁,c₂,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext
    (by simp [mul_smul_comm]) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

/-- A version of `star_smul` for the special case when `c₂ = 0`, without `SMulCommClass S R R`. -/
/-
**QuaternionAlgebra.star_smul'** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_smul' [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃]) : 
star (s • a) = s • star a
参数：s : S；a : ℍ[R,c₁,0,c₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)

--- 原说明 ---
A version of `star_smul` for the special case when `c₂ = 0`, without `SMulCommCl
ass S R R`.
-/
theorem star_smul' [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm
/-
**QuaternionAlgebra.eq_re_of_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
`。
形式化陈述：eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re
参数：h : a = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuaternionAlgebra.re_coe`：re_coe : (x : ℍ[R,c₁,c₂,c₃]).re = x
-/
theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re := by rw [h, re_coe]
/-
**QuaternionAlgebra.eq_re_iff_mem_range_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternio
nAlgebra`。
形式化陈述：eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} : a = a.re ↔ a in Set.range (c
oe : R -> ℍ[R,c₁,c₂,c₃])
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuaternionAlgebra.eq_re_of_eq_coe`：eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {
x : R} (h : a = x) : a = a.re
-/
theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} :
    a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R,c₁,c₂,c₃]) :=
  ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
/-
**QuaternionAlgebra.star_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re := by
  simp_all [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]
/-
**QuaternionAlgebra.star_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} : star a = -a ↔ a.re = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} : star a = -a ↔ a.re = 0 := by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

end CharZero

-- Can't use `rw ← star_eq_self` in the proof without additional assumptions
/-
**QuaternionAlgebra.star_mul_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
`。
形式化陈述：star_mul_eq_coe : star a * a = (star a * a).re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `QuaternionAlgebra.coe_add`：coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x +
 y
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `QuaternionAlgebra.coe_neg`：coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 53 条，此处仅展示前 30 条）
-/
theorem star_mul_eq_coe : star a * a = (star a * a).re := by ext <;> simp <;> ring
/-
**QuaternionAlgebra.mul_star_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra
`。
形式化陈述：mul_star_eq_coe : a * star a = (a * star a).re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_comm_self'`：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal 
x] : star x * x = x * star x
· 使用定理 `QuaternionAlgebra.instIsStarNormal`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a :
 QuaternionAlgebra R c₁ c₂ c₃) [inst : CommRing R], IsStarNormal a
· 使用定理 `QuaternionAlgebra.star_mul_eq_coe`：star_mul_eq_coe : star a * a = (star 
a * a).re
-/
theorem mul_star_eq_coe : a * star a = (a * star a).re := by
  rw [← star_comm_self']
  exact a.star_mul_eq_coe

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
/-
**QuaternionAlgebra.starAe** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionAlgebra`。
形式化陈述：starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quaternion conjugate as an `AlgEquiv` to the opposite ring.
-/
def starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ :=
  { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by simp
    commutes' := fun r => by simp }

@[simp]
/-
**QuaternionAlgebra.coe_starAe** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionAlgebra`。
形式化陈述：coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star :=
  rfl

end QuaternionAlgebra

/-- Space of quaternions over a type, denoted as `ℍ[R]`.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
/-
**Quaternion** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quaternion (R : Type*) [Zero R] [One R] [Neg R]
参数：R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Space of quaternions over a type, denoted as `ℍ[R]`.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`.
-/
def Quaternion (R : Type*) [Zero R] [One R] [Neg R] :=
  QuaternionAlgebra R (-1) (0) (-1)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

open Quaternion

/-- The equivalence between the quaternions over `R` and `R × R × R × R`. -/
@[simps!]
/-
**Quaternion.equivProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quaternion.equivProd (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ R × R ×
 R × R
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the quaternions over `R` and `R × R × R × R`.
-/
def Quaternion.equivProd (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ R × R × R × R :=
  QuaternionAlgebra.equivProd _ _ _

/-- The equivalence between the quaternions over `R` and `Fin 4 → R`. -/
@[simps! symm_apply]
/-
**Quaternion.equivTuple** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quaternion.equivTuple (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ (Fin 4
 -> R)
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the quaternions over `R` and `Fin 4 → R`.
-/
def Quaternion.equivTuple (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ (Fin 4 → R) :=
  QuaternionAlgebra.equivTuple _ _ _

@[simp]
/-
**Quaternion.equivTuple_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quaternion.equivTuple_apply (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R]
) : Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK]
参数：R : Type*；x : ℍ[R]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quaternion.equivTuple_apply (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R]) :
    Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Zero R] [One R] [Neg R] [Subsingleton R] : Subsingleton ℍ[R] :=
  inferInstanceAs <| Subsingleton <| ℍ[R,-1,0,-1]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Zero R] [One R] [Neg R] [Nontrivial R] : Nontrivial ℍ[R] :=
  inferInstanceAs <| Nontrivial <| ℍ[R,-1,0,-1]

namespace Quaternion

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

/-- Coercion `R → ℍ[R]`. -/
/-
**Quaternion.coe** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：{R : Type u_3} → [inst : CommRing R] → R → Quaternion R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `R → ℍ[R]`.
-/
@[coe] def coe : R → ℍ[R] := QuaternionAlgebra.coe
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `R → ℍ[R]`.
-/
instance : CoeTC R ℍ[R] := ⟨coe⟩
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S R] : SMul S ℍ[R] := inferInstanceAs <| SMul S ℍ[R,-1,0,-1]
/-
**Quaternion.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instRing : Ring ℍ[R] where nsmul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing : Ring ℍ[R] where
  nsmul := letI := Quaternion.instSMul (S := ℕ) (R := R); (· • ·)
  zsmul := letI := Quaternion.instSMul (S := ℤ) (R := R); (· • ·)
  __ : Ring ℍ[R] := inferInstanceAs <| Ring ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℍ[R] := inferInstanceAs <| Inhabited ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [SMul S R] [SMul T R] [IsScalarTower S T R] : IsScalarTower S T ℍ[R] :=
  inferInstanceAs <| IsScalarTower S T ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S R] [SMul T R] [SMulCommClass S T R] : SMulCommClass S T ℍ[R] :=
  inferInstanceAs <| SMulCommClass S T ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [MulAction S R] : MulAction S ℍ[R] :=
  inferInstanceAs <| MulAction S ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [DistribMulAction S R] : DistribMulAction S ℍ[R] :=
  inferInstanceAs <| DistribMulAction S ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [Module S R] : Module S ℍ[R] :=
  inferInstanceAs <| Module S ℍ[R,-1,0,-1]
/-
**Quaternion.algebra** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：{S : Type u_1} →   {R : Type u_3} → [inst : CommRing R] → [inst_1 : CommSe
miring S] → [Algebra S R] → Algebra S (Quaternion R)
参数：Quaternion R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance algebra [CommSemiring S] [Algebra S R] : Algebra S ℍ[R] :=
  inferInstanceAs <| Algebra S ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star ℍ[R] := inferInstanceAs <| Star ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRing ℍ[R] := inferInstanceAs <| StarRing ℍ[R,-1,0,-1]
set_option backward.isDefEq.respectTransparency.types false in
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStarNormal a := inferInstanceAs <| IsStarNormal (R := ℍ[R,-1,0,-1]) a

@[ext]
/-
**Quaternion.ext** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a.imK = b.imK -> a 
= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.ext`：∀ {R : Type u_1} {a b c : R} {x y : QuaternionAlg
ebra R a b c},   x.re = y.re → x.imI = y.imI → x.imJ = y.imJ → x.imK = y.imK → x
 = y
-/
theorem ext : a.re = b.re → a.imI = b.imI → a.imJ = b.imJ → a.imK = b.imK → a = b :=
  QuaternionAlgebra.ext

/-- The imaginary part of a quaternion. -/
/-
**Quaternion.im** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：im (x : ℍ[R]) : ℍ[R]
参数：x : ℍ[R]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The imaginary part of a quaternion.
-/
def im (x : ℍ[R]) : ℍ[R] := QuaternionAlgebra.im x
/-
**Quaternion.re_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a.im.re = 0
参数：a : Quaternion R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_im : a.im.re = 0 := rfl
/-
**Quaternion.imI_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a.im.imI = a.imI
参数：a : Quaternion R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imI_im : a.im.imI = a.imI := rfl
/-
**Quaternion.imJ_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a.im.imJ = a.imJ
参数：a : Quaternion R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imJ_im : a.im.imJ = a.imJ := rfl
/-
**Quaternion.imK_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a.im.imK = a.imK
参数：a : Quaternion R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imK_im : a.im.imK = a.imK := rfl
/-
**Quaternion.im_idem** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a.im.im = a.im
参数：a : Quaternion R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_idem : a.im.im = a.im := rfl
/-
**Quaternion.re_add_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), ↑a.re + a.im = a
参数：a : Quaternion R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.re_add_im`：re_add_im : ↑a.re + a.im = a
-/
@[simp] theorem re_add_im : ↑a.re + a.im = a := QuaternionAlgebra.re_add_im a
/-
**Quaternion.sub_im_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a - a.im = ↑a.re
参数：a : Quaternion R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.sub_im_self`：sub_im_self : a - a.im = a.re
-/
@[simp] theorem sub_im_self : a - a.im = a.re := QuaternionAlgebra.sub_im_self a
/-
**Quaternion.sub_re_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), a - ↑a.re = a.im
参数：a : Quaternion R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.sub_re_self`：sub_re_self : a - a.re = a.im
-/
@[simp] theorem sub_re_self : a - ↑a.re = a.im := QuaternionAlgebra.sub_re_self a

@[simp, norm_cast]
/-
**Quaternion.re_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_coe : (x : ℍ[R]).re = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_coe : (x : ℍ[R]).re = x := rfl

@[simp, norm_cast]
/-
**Quaternion.imI_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_coe : (x : ℍ[R]).imI = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_coe : (x : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.imJ_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_coe : (x : ℍ[R]).imJ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_coe : (x : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.imK_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_coe : (x : ℍ[R]).imK = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_coe : (x : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.im_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：im_coe : (x : ℍ[R]).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_coe : (x : ℍ[R]).im = 0 := rfl
/-
**Quaternion.re_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.re 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem re_zero : (0 : ℍ[R]).re = 0 := rfl
/-
**Quaternion.imI_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.imI 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem imI_zero : (0 : ℍ[R]).imI = 0 := rfl
/-
**Quaternion.imJ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.imJ 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem imJ_zero : (0 : ℍ[R]).imJ = 0 := rfl
/-
**Quaternion.imK_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.imK 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem imK_zero : (0 : ℍ[R]).imK = 0 := rfl
/-
**Quaternion.im_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], Quaternion.im 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem im_zero : (0 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_zero : ((0 : R) : ℍ[R]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl
/-
**Quaternion.re_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.re 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem re_one : (1 : ℍ[R]).re = 1 := rfl
/-
**Quaternion.imI_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.imI 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem imI_one : (1 : ℍ[R]).imI = 0 := rfl
/-
**Quaternion.imJ_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.imJ 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem imJ_one : (1 : ℍ[R]).imJ = 0 := rfl
/-
**Quaternion.imK_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], QuaternionAlgebra.imK 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem imK_one : (1 : ℍ[R]).imK = 0 := rfl
/-
**Quaternion.im_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], Quaternion.im 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem im_one : (1 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_one : ((1 : R) : ℍ[R]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : R) : ℍ[R]) = 1 := rfl
/-
**Quaternion.re_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a + b).re = a.
re + b.re
参数：a b : Quaternion R；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_add : (a + b).re = a.re + b.re := rfl
/-
**Quaternion.imI_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a + b).imI = a
.imI + b.imI
参数：a b : Quaternion R；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imI_add : (a + b).imI = a.imI + b.imI := rfl
/-
**Quaternion.imJ_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a + b).imJ = a
.imJ + b.imJ
参数：a b : Quaternion R；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imJ_add : (a + b).imJ = a.imJ + b.imJ := rfl
/-
**Quaternion.imK_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a + b).imK = a
.imK + b.imK
参数：a b : Quaternion R；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imK_add : (a + b).imK = a.imK + b.imK := rfl
/-
**Quaternion.im_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a + b).im = a.
im + b.im
参数：a b : Quaternion R；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.im_add`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a b : Quatern
ionAlgebra R c₁ c₂ c₃) [inst : AddZeroClass R], (a + b).im = a.im + b.im
-/
@[simp] theorem im_add : (a + b).im = a.im + b.im := QuaternionAlgebra.im_add a b

@[simp, norm_cast]
/-
**Quaternion.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_add : ((x + y : R) : ℍ[R]) = x + y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_add`：coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x +
 y
-/
theorem coe_add : ((x + y : R) : ℍ[R]) = x + y :=
  QuaternionAlgebra.coe_add x y
/-
**Quaternion.re_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (-a).re = -a.re
参数：a : Quaternion R；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_neg : (-a).re = -a.re := rfl
/-
**Quaternion.imI_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (-a).imI = -a.imI
参数：a : Quaternion R；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imI_neg : (-a).imI = -a.imI := rfl
/-
**Quaternion.imJ_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (-a).imJ = -a.imJ
参数：a : Quaternion R；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imJ_neg : (-a).imJ = -a.imJ := rfl
/-
**Quaternion.imK_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (-a).imK = -a.imK
参数：a : Quaternion R；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imK_neg : (-a).imK = -a.imK := rfl
/-
**Quaternion.im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (-a).im = -a.im
参数：a : Quaternion R；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.im_neg`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : Quaternio
nAlgebra R c₁ c₂ c₃) [inst : AddGroup R], (-a).im = -a.im
-/
@[simp] theorem im_neg : (-a).im = -a.im := QuaternionAlgebra.im_neg a

@[simp, norm_cast]
/-
**Quaternion.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_neg : ((-x : R) : ℍ[R]) = -x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_neg`：coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x
-/
theorem coe_neg : ((-x : R) : ℍ[R]) = -x :=
  QuaternionAlgebra.coe_neg x
/-
**Quaternion.re_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a - b).re = a.
re - b.re
参数：a b : Quaternion R；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_sub : (a - b).re = a.re - b.re := rfl
/-
**Quaternion.imI_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a - b).imI = a
.imI - b.imI
参数：a b : Quaternion R；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imI_sub : (a - b).imI = a.imI - b.imI := rfl
/-
**Quaternion.imJ_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a - b).imJ = a
.imJ - b.imJ
参数：a b : Quaternion R；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imJ_sub : (a - b).imJ = a.imJ - b.imJ := rfl
/-
**Quaternion.imK_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a - b).imK = a
.imK - b.imK
参数：a b : Quaternion R；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imK_sub : (a - b).imK = a.imK - b.imK := rfl
/-
**Quaternion.im_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternion R), (a - b).im = a.
im - b.im
参数：a b : Quaternion R；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.im_sub`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a b : Quatern
ionAlgebra R c₁ c₂ c₃) [inst : AddGroup R], (a - b).im = a.im - b.im
-/
@[simp] theorem im_sub : (a - b).im = a.im - b.im := QuaternionAlgebra.im_sub a b

@[simp, norm_cast]
/-
**Quaternion.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_sub : ((x - y : R) : ℍ[R]) = x - y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_sub`：coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x -
 y
-/
theorem coe_sub : ((x - y : R) : ℍ[R]) = x - y :=
  QuaternionAlgebra.coe_sub x y

@[simp]
/-
**Quaternion.re_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK 
* b.imK
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuaternionAlgebra.re_mul`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} [inst : Ring R
] (a b : QuaternionAlgebra R c₁ c₂ c₃),   (a * b).re = a.re * b.re + c₁ * a.imI 
* b.imI + c₃ *…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK :=
  (QuaternionAlgebra.re_mul a b).trans <| by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp]
/-
**Quaternion.imI_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.im
K * b.imJ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuaternionAlgebra.imI_mul`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} [inst : Ring 
R] (a b : QuaternionAlgebra R c₁ c₂ c₃),   (a * b).imI = a.re * b.imI + a.imI * 
b.re + c₂ * a.i…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 37 条，此处仅展示前 30 条）
-/
theorem imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ :=
  (QuaternionAlgebra.imI_mul a b).trans <| by ring

@[simp]
/-
**Quaternion.imJ_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.im
K * b.imI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuaternionAlgebra.imJ_mul`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} [inst : Ring 
R] (a b : QuaternionAlgebra R c₁ c₂ c₃),   (a * b).imJ = a.re * b.imJ + c₁ * a.i
mI * b.imK + a.…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 37 条，此处仅展示前 30 条）
-/
theorem imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI :=
  (QuaternionAlgebra.imJ_mul a b).trans <| by ring

@[simp]
/-
**Quaternion.imK_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.i
mK * b.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuaternionAlgebra.imK_mul`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} [inst : Ring 
R] (a b : QuaternionAlgebra R c₁ c₂ c₃),   (a * b).imK = a.re * b.imK + a.imI * 
b.imJ + c₂ * a.…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
（共 31 条，此处仅展示前 30 条）
-/
theorem imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re :=
  (QuaternionAlgebra.imK_mul a b).trans <| by ring

@[simp, norm_cast]
/-
**Quaternion.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_mul : ((x * y : R) : ℍ[R]) = x * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
-/
theorem coe_mul : ((x * y : R) : ℍ[R]) = x * y := QuaternionAlgebra.coe_mul x y

@[norm_cast, simp]
/-
**Quaternion.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_pow`：coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]
) = (x : ℍ[R,c₁,c₂,c₃]) ^ n
-/
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n :=
  QuaternionAlgebra.coe_pow x n

@[simp, norm_cast]
/-
**Quaternion.re_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_natCast (n : Nat) : (n : ℍ[R]).re = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_natCast (n : ℕ) : (n : ℍ[R]).re = n := rfl

@[simp, norm_cast]
/-
**Quaternion.imI_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_natCast (n : Nat) : (n : ℍ[R]).imI = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_natCast (n : ℕ) : (n : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.imJ_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_natCast (n : Nat) : (n : ℍ[R]).imJ = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_natCast (n : ℕ) : (n : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.imK_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_natCast (n : Nat) : (n : ℍ[R]).imK = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_natCast (n : ℕ) : (n : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.im_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：im_natCast (n : Nat) : (n : ℍ[R]).im = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_natCast (n : ℕ) : (n : ℍ[R]).im = 0 := rfl

@[norm_cast]
/-
**Quaternion.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_natCast (n : Nat) : ↑(n : R) = (n : ℍ[R])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R]) := rfl

@[simp, norm_cast]
/-
**Quaternion.re_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_intCast (z : Int) : (z : ℍ[R]).re = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_intCast (z : ℤ) : (z : ℍ[R]).re = z := rfl

@[simp, norm_cast]
/-
**Quaternion.imI_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_intCast (z : Int) : (z : ℍ[R]).imI = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_intCast (z : ℤ) : (z : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.imJ_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_intCast (z : Int) : (z : ℍ[R]).imJ = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_intCast (z : ℤ) : (z : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.imK_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_intCast (z : Int) : (z : ℍ[R]).imK = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_intCast (z : ℤ) : (z : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
/-
**Quaternion.im_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：im_intCast (z : Int) : (z : ℍ[R]).im = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_intCast (z : ℤ) : (z : ℍ[R]).im = 0 := rfl

@[norm_cast]
/-
**Quaternion.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_intCast (z : Int) : ↑(z : R) = (z : ℍ[R])
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R]) := rfl
/-
**Quaternion.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_injective : Function.Injective (coe : R -> ℍ[R])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_injective`：coe_injective : Function.Injective (coe
 : R -> ℍ[R,c₁,c₂,c₃])
-/
theorem coe_injective : Function.Injective (coe : R → ℍ[R]) :=
  QuaternionAlgebra.coe_injective

@[simp]
/-
**Quaternion.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Quaternion.coe_injective`：coe_injective : Function.Injective (coe : R ->
 ℍ[R])
-/
theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
/-
**Quaternion.re_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_smul [SMul S R] (s : S) : (s • a).re = s • a.re
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_smul [SMul S R] (s : S) : (s • a).re = s • a.re :=
  rfl
/-
**Quaternion.imI_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {S : Type u_1} {R : Type u_3} [inst : CommRing R] (a : Quaternion R) [in
st_1 : SMul S R] (s : S),   (s • a).imI = s • a.imI
参数：a : Quaternion R；s : S；s • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imI_smul [SMul S R] (s : S) : (s • a).imI = s • a.imI := rfl
/-
**Quaternion.imJ_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {S : Type u_1} {R : Type u_3} [inst : CommRing R] (a : Quaternion R) [in
st_1 : SMul S R] (s : S),   (s • a).imJ = s • a.imJ
参数：a : Quaternion R；s : S；s • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imJ_smul [SMul S R] (s : S) : (s • a).imJ = s • a.imJ := rfl
/-
**Quaternion.imK_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {S : Type u_1} {R : Type u_3} [inst : CommRing R] (a : Quaternion R) [in
st_1 : SMul S R] (s : S),   (s • a).imK = s • a.imK
参数：a : Quaternion R；s : S；s • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imK_smul [SMul S R] (s : S) : (s • a).imK = s • a.imK := rfl

@[simp]
/-
**Quaternion.im_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：im_smul [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.im_smul`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : Quaterni
onAlgebra R c₁ c₂ c₃) {S : Type u_4} [inst : CommRing R]   [inst_1 : SMulZeroCla
ss S R] (s : S)…
-/
theorem im_smul [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.im_smul a s

@[simp, norm_cast]
/-
**Quaternion.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r 
: ℍ[R])
参数：s : S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_smul`：coe_smul [Zero R] [SMulZeroClass S R] (s : S
) (r : R) : (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃])
-/
theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r : ℍ[R]) :=
  QuaternionAlgebra.coe_smul _ _
/-
**Quaternion.coe_commutes** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_commutes : ↑r * a = a * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_commutes`：coe_commutes : ↑r * a = a * r
-/
theorem coe_commutes : ↑r * a = a * r :=
  QuaternionAlgebra.coe_commutes r a
/-
**Quaternion.coe_commute** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_commute : Commute (↑r) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_commute`：coe_commute : Commute (↑r) a
-/
theorem coe_commute : Commute (↑r) a :=
  QuaternionAlgebra.coe_commute r a
/-
**Quaternion.coe_mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_mul_eq_smul : ↑r * a = r • a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.coe_mul_eq_smul`：coe_mul_eq_smul : ↑r * a = r • a
-/
theorem coe_mul_eq_smul : ↑r * a = r • a :=
  QuaternionAlgebra.coe_mul_eq_smul r a
/-
**Quaternion.mul_coe_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：mul_coe_eq_smul : a * r = r • a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.mul_coe_eq_smul`：mul_coe_eq_smul : a * r = r • a
-/
theorem mul_coe_eq_smul : a * r = r • a :=
  QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]
/-
**Quaternion.algebraMap_def** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe :=
  rfl
/-
**Quaternion.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：algebraMap_injective : (algebraMap R ℍ[R] : _ -> _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.algebraMap_injective`：algebraMap_injective : (algebraM
ap R ℍ[R,c₁,c₂,c₃] : _ -> _).Injective
-/
theorem algebraMap_injective : (algebraMap R ℍ[R] : _ → _).Injective :=
  QuaternionAlgebra.algebraMap_injective
/-
**Quaternion.smul_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：smul_coe : x • (y : ℍ[R]) = ↑(x * y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.smul_coe`：smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y
)
-/
theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) :=
  QuaternionAlgebra.smul_coe x y
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite R ℍ[R] := inferInstanceAs <| Module.Finite R ℍ[R,-1,0,-1]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R ℍ[R] := inferInstanceAs <| Module.Free R ℍ[R,-1,0,-1]
/-
**Quaternion.rank_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.rank_eq_four`：rank_eq_four [StrongRankCondition R] : M
odule.rank R ℍ[R,c₁,c₂,c₃] = 4
-/
theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4 :=
  QuaternionAlgebra.rank_eq_four _ _ _
/-
**Quaternion.finrank_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.finrank_eq_four`：finrank_eq_four [StrongRankCondition 
R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4
-/
theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4 :=
  QuaternionAlgebra.finrank_eq_four _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Quaternion.re_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (star a).re = a.r
e
参数：a : Quaternion R；star a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuaternionAlgebra.re_star`：∀ {R : Type u_3} {c₁ c₂ c₃ : R} (a : Quaterni
onAlgebra R c₁ c₂ c₃) [inst : CommRing R], (star a).re = a.re + c₂ * a.imI
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
@[simp] theorem re_star : (star a).re = a.re := by
  rw [QuaternionAlgebra.re_star, zero_mul, add_zero]
/-
**Quaternion.imI_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (star a).imI = -a
.imI
参数：a : Quaternion R；star a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imI_star : (star a).imI = -a.imI := rfl
/-
**Quaternion.imJ_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (star a).imJ = -a
.imJ
参数：a : Quaternion R；star a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imJ_star : (star a).imJ = -a.imJ := rfl
/-
**Quaternion.imK_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (star a).imK = -a
.imK
参数：a : Quaternion R；star a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem imK_star : (star a).imK = -a.imK := rfl
/-
**Quaternion.im_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R), (star a).im = -a.
im
参数：a : Quaternion R；star a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.im_star`：im_star : (star a).im = -a.im
-/
@[simp] theorem im_star : (star a).im = -a.im := QuaternionAlgebra.im_star a
/-
**Quaternion.self_add_star'** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：self_add_star' : a + star a = ↑(2 * a.re)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.coe_mul`：coe_mul : ((x * y : R) : ℍ[R]) = x * y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `QuaternionAlgebra.self_add_star'`：self_add_star' : a + star a = ↑(2 * a.
re + c₂ * a.imI)
-/
theorem self_add_star' : a + star a = ↑(2 * a.re) := by
  simpa using! QuaternionAlgebra.self_add_star' a
/-
**Quaternion.self_add_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：self_add_star : a + star a = 2 * a.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `QuaternionAlgebra.self_add_star`：self_add_star : a + star a = 2 * a.re +
 c₂ * a.imI
-/
theorem self_add_star : a + star a = 2 * a.re := by
  simpa using! QuaternionAlgebra.self_add_star a
/-
**Quaternion.star_add_self'** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_add_self' : star a + a = ↑(2 * a.re)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.coe_mul`：coe_mul : ((x * y : R) : ℍ[R]) = x * y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `QuaternionAlgebra.star_add_self'`：star_add_self' : star a + a = ↑(2 * a.
re + c₂ * a.imI)
-/
theorem star_add_self' : star a + a = ↑(2 * a.re) := by
  simpa using! QuaternionAlgebra.star_add_self' a
/-
**Quaternion.star_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_add_self : star a + a = 2 * a.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `QuaternionAlgebra.star_add_self`：star_add_self : star a + a = 2 * a.re +
 c₂ * a.imI
-/
theorem star_add_self : star a + a = 2 * a.re := by
  simpa using! QuaternionAlgebra.star_add_self a
/-
**Quaternion.star_eq_two_re_sub** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_eq_two_re_sub : star a = ↑(2 * a.re) - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Quaternion.coe_mul`：coe_mul : ((x * y : R) : ℍ[R]) = x * y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `QuaternionAlgebra.coe_mul`：coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x *
 y
· 使用定理 `QuaternionAlgebra.star_eq_two_re_sub`：star_eq_two_re_sub : star a = ↑(2 
* a.re + c₂ * a.imI) - a
-/
theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a := by
  simpa using! QuaternionAlgebra.star_eq_two_re_sub a

@[simp, norm_cast]
/-
**Quaternion.star_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_coe : star (x : ℍ[R]) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.star_coe`：star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x
-/
theorem star_coe : star (x : ℍ[R]) = x :=
  QuaternionAlgebra.star_coe x

@[simp]
/-
**Quaternion.star_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_im : star a.im = -a.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quaternion.ext`：ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a
.imK = b.imK -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.re_star`：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion
 R), (star a).re = a.re
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_im : star a.im = -a.im := by ext <;> simp

@[simp]
/-
**Quaternion.star_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) : star (s •
 a) = s • star a
参数：s : S；a : ℍ[R]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.star_smul'`：star_smul' [Monoid S] [DistribMulAction S 
R] (s : S) (a : ℍ[R,c₁,0,c₃]) : star (s • a) = s • star a
-/
theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) :
    star (s • a) = s • star a := QuaternionAlgebra.star_smul' s a
/-
**Quaternion.eq_re_of_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re
参数：h : a = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.eq_re_of_eq_coe`：eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {
x : R} (h : a = x) : a = a.re
-/
theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
  QuaternionAlgebra.eq_re_of_eq_coe h
/-
**Quaternion.eq_re_iff_mem_range_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a in Set.range (coe : R ->
 ℍ[R])
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.eq_re_iff_mem_range_coe`：eq_re_iff_mem_range_coe {a : 
ℍ[R,c₁,c₂,c₃]} : a = a.re ↔ a in Set.range (coe : R -> ℍ[R,c₁,c₂,c₃])
-/
theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R]) :=
  QuaternionAlgebra.eq_re_iff_mem_range_coe

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
/-
**Quaternion.star_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.star_eq_self`：star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,
c₃]} : star a = a ↔ a = a.re
-/
theorem star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re :=
  QuaternionAlgebra.star_eq_self

@[simp]
/-
**Quaternion.star_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.star_eq_neg`：star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} :
 star a = -a ↔ a.re = 0
-/
theorem star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0 :=
  QuaternionAlgebra.star_eq_neg

end CharZero

/-
**Quaternion.star_mul_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_mul_eq_coe : star a * a = (star a * a).re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.star_mul_eq_coe`：star_mul_eq_coe : star a * a = (star 
a * a).re
-/
theorem star_mul_eq_coe : star a * a = (star a * a).re :=
  QuaternionAlgebra.star_mul_eq_coe a
/-
**Quaternion.mul_star_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：mul_star_eq_coe : a * star a = (a * star a).re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.mul_star_eq_coe`：mul_star_eq_coe : a * star a = (a * s
tar a).re
-/
theorem mul_star_eq_coe : a * star a = (a * star a).re :=
  QuaternionAlgebra.mul_star_eq_coe a

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
/-
**Quaternion.starAe** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quaternion conjugate as an `AlgEquiv` to the opposite ring.
-/
def starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ :=
  QuaternionAlgebra.starAe

@[simp]
/-
**Quaternion.coe_starAe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_starAe : ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_starAe : ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star :=
  rfl

/-- Square of the norm. -/
/-
**Quaternion.normSq** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：normSq : ℍ[R] ->*₀ R where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Square of the norm.
-/
def normSq : ℍ[R] →*₀ R where
  toFun a := (a * star a).re
  map_zero' := by simp only [star_zero, zero_mul, re_zero]
  map_one' := by simp only [star_one, one_mul, re_one]
  map_mul' x y := coe_injective <| by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]
/-
**Quaternion.normSq_def** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_def : normSq a = (a * star a).re
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normSq_def : normSq a = (a * star a).re := rfl
/-
**Quaternion.normSq_def'** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.re_mul`：re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a
.imJ * b.imJ - a.imK * b.imK
· 使用定理 `Quaternion.re_star`：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion
 R), (star a).re = a.re
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, re_mul, re_star, imI_star, imJ_star,
    imK_star]
/-
**Quaternion.normSq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_coe : normSq (x : ℍ[R]) = x ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.normSq_def`：normSq_def : normSq a = (a * star a).re
· 使用定理 `Quaternion.star_coe`：star_coe : star (x : ℍ[R]) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.coe_mul`：coe_mul : ((x * y : R) : ℍ[R]) = x * y
· 使用定理 `Quaternion.re_coe`：re_coe : (x : ℍ[R]).re = x
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem normSq_coe : normSq (x : ℍ[R]) = x ^ 2 := by
  rw [normSq_def, star_coe, ← coe_mul, re_coe, sq]

@[simp]
/-
**Quaternion.normSq_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_star : normSq (star a) = normSq a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.normSq_def'`：normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3
 ^ 2 + a.4 ^ 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Quaternion.re_star`：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion
 R), (star a).re = a.re
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_star : normSq (star a) = normSq a := by simp [normSq_def']

@[norm_cast]
/-
**Quaternion.normSq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_natCast (n : Nat) : normSq (n : ℍ[R]) = (n : R) ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.coe_natCast`：coe_natCast (n : Nat) : ↑(n : R) = (n : ℍ[R])
· 使用定理 `Quaternion.normSq_coe`：normSq_coe : normSq (x : ℍ[R]) = x ^ 2
-/
theorem normSq_natCast (n : ℕ) : normSq (n : ℍ[R]) = (n : R) ^ 2 := by
  rw [← coe_natCast, normSq_coe]

@[norm_cast]
/-
**Quaternion.normSq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_intCast (z : Int) : normSq (z : ℍ[R]) = (z : R) ^ 2
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.coe_intCast`：coe_intCast (z : Int) : ↑(z : R) = (z : ℍ[R])
· 使用定理 `Quaternion.normSq_coe`：normSq_coe : normSq (x : ℍ[R]) = x ^ 2
-/
theorem normSq_intCast (z : ℤ) : normSq (z : ℍ[R]) = (z : R) ^ 2 := by
  rw [← coe_intCast, normSq_coe]

@[simp]
/-
**Quaternion.normSq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_neg : normSq (-a) = normSq a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_neg : normSq (-a) = normSq a := by simp only [normSq_def, star_neg, neg_mul_neg]
/-
**Quaternion.self_mul_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：self_mul_star : a * star a = normSq a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.mul_star_eq_coe`：mul_star_eq_coe : a * star a = (a * star a).
re
· 使用定理 `Quaternion.normSq_def`：normSq_def : normSq a = (a * star a).re
-/
theorem self_mul_star : a * star a = normSq a := by rw [mul_star_eq_coe, normSq_def]
/-
**Quaternion.star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：star_mul_self : star a * a = normSq a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
· 使用定理 `Quaternion.instIsStarNormal`：∀ {R : Type u_3} [inst : CommRing R] (a : Q
uaternion R), IsStarNormal a
· 使用定理 `Quaternion.self_mul_star`：self_mul_star : a * star a = normSq a
-/
theorem star_mul_self : star a * a = normSq a := by rw [star_comm_self, self_mul_star]
/-
**Quaternion.im_sq** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：im_sq : a.im ^ 2 = -normSq a.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Quaternion.star_im`：star_im : star a.im = -a.im
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_sq : a.im ^ 2 = -normSq a.im := by
  simp_rw [sq, ← star_mul_self, star_im, neg_mul, neg_neg]
/-
**Quaternion.coe_normSq_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_normSq_add : normSq (a + b) = normSq a + a * star b + b * star a + nor
mSq b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_normSq_add : normSq (a + b) = normSq a + a * star b + b * star a + normSq b := by
  simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]
/-
**Quaternion.normSq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) = r ^ 2 * normSq q
参数：r : R；q : ℍ[R]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.normSq_def'`：normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3
 ^ 2 + a.4 ^ 2
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) = r ^ 2 * normSq q := by
  simp only [normSq_def', re_smul, imI_smul, imJ_smul, imK_smul, mul_pow, mul_add, smul_eq_mul]
/-
**Quaternion.normSq_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq a + normSq b + 2 * (a * 
star b).re
参数：a b : ℍ[R]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.Algebra.Quaternion.0.Quaternion.normSq_add._abel_1_1`：∀
 {R : Type u_1} [inst : CommRing R] (a b : Quaternion R),   Quaternion.normSq a 
+ (a * star b).re + ((b * star a).re + Quaternion.normSq b)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.re_add`：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternio
n R), (a + b).re = a.re + b.re
· 使用定理 `star_mul_star`：star_mul_star (x y : R) : star (x * star y) = y * star x
· 使用定理 `Quaternion.self_add_star'`：self_add_star' : a + star a = ↑(2 * a.re)
· 使用定理 `Quaternion.re_coe`：re_coe : (x : ℍ[R]).re = x
-/
theorem normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re :=
  calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      simp_rw [normSq_def, star_add, add_mul, mul_add, re_add]
    _ = normSq a + normSq b + ((a * star b).re + (b * star a).re) := by abel
    _ = normSq a + normSq b + 2 * (a * star b).re := by
      rw [← re_add, ← star_mul_star a b, self_add_star', re_coe]

end Quaternion

namespace Quaternion

variable {R : Type*}

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

@[simp]
/-
**Quaternion.normSq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_eq_zero : normSq a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quaternion.ext`：ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a
.imK = b.imK -> a = b
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero_iff_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [ins
t_1 : PartialOrder α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ 
b → (a + b = 0 …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `Quaternion.normSq_def'`：normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3
 ^ 2 + a.4 ^ 2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MonoidWithZeroHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem normSq_eq_zero : normSq a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ normSq.map_zero⟩
  rw [normSq_def', add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg]
    at h
  · apply ext a 0 <;> apply eq_zero_of_pow_eq_zero
    exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
  all_goals apply_rules [sq_nonneg, add_nonneg]
/-
**Quaternion.normSq_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_ne_zero : normSq a != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Quaternion.normSq_eq_zero`：normSq_eq_zero : normSq a = 0 ↔ a = 0
-/
theorem normSq_ne_zero : normSq a ≠ 0 ↔ a ≠ 0 := normSq_eq_zero.not

@[simp]
/-
**Quaternion.normSq_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_nonneg : 0 <= normSq a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.normSq_def'`：normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3
 ^ 2 + a.4 ^ 2
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem normSq_nonneg : 0 ≤ normSq a := by
  rw [normSq_def']
  apply_rules [sq_nonneg, add_nonneg]

@[simp]
/-
**Quaternion.normSq_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_le_zero : normSq a <= 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Quaternion.normSq_nonneg`：normSq_nonneg : 0 <= normSq a
· 使用定理 `Quaternion.normSq_eq_zero`：normSq_eq_zero : normSq a = 0 ↔ a = 0
-/
theorem normSq_le_zero : normSq a ≤ 0 ↔ a = 0 :=
  normSq_nonneg.ge_iff_eq'.trans normSq_eq_zero
/-
**Quaternion.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instNontrivial : Nontrivial ℍ[R] where exists_pair_ne
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
instance instNontrivial : Nontrivial ℍ[R] where
  exists_pair_ne := ⟨0, 1, mt (congr_arg QuaternionAlgebra.re) zero_ne_one⟩
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors ℍ[R] where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab :=
    have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain ℍ[R] := NoZeroDivisors.to_isDomain _
/-
**Quaternion.sq_eq_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：sq_eq_normSq : a ^ 2 = normSq a ↔ a = a.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.star_eq_self`：star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Quaternion.star_mul_self`：star_mul_self : star a * a = normSq a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_eq_mul_right_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRigh
tCancelMulZero M₀] {a b c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Quaternion.instIsDomain`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
LinearOrder R] [IsStrictOrderedRing R], IsDomain (Quaternion R)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem sq_eq_normSq : a ^ 2 = normSq a ↔ a = a.re := by
  rw [← star_eq_self, ← star_mul_self, sq, mul_eq_mul_right_iff, eq_comm]
  exact or_iff_left_of_imp fun ha ↦ ha.symm ▸ star_zero _
/-
**Quaternion.sq_eq_neg_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.star_mul_self`：star_mul_self : star a * a = normSq a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Quaternion.instIsDomain`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
LinearOrder R] [IsStrictOrderedRing R], IsDomain (Quaternion R)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
（共 31 条，此处仅展示前 30 条）
-/
theorem sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re = 0 := by
  simp_rw [← star_eq_neg]
  obtain rfl | hq0 := eq_or_ne a 0
  · simp
  · rw [← star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]

end LinearOrderedCommRing

section Field

variable [Field R] (a b : ℍ[R])

/-
**Quaternion.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instNNRatCast : NNRatCast ℍ[R] where nnratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatCast : NNRatCast ℍ[R] where nnratCast q := (q : R)
/-
**Quaternion.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instRatCast : RatCast ℍ[R] where ratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRatCast : RatCast ℍ[R] where ratCast q := (q : R)
/-
**Quaternion.re_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ≥0), (↑q).re = ↑q
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℍ[R]).re = q := rfl
/-
**Quaternion.im_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ≥0), (↑q).im = 0
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℍ[R]).im = 0 := rfl
/-
**Quaternion.imI_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ≥0), (↑q).imI = 0
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma imI_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imI = 0 := rfl
/-
**Quaternion.imJ_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ≥0), (↑q).imJ = 0
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma imJ_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imJ = 0 := rfl
/-
**Quaternion.imK_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ≥0), (↑q).imK = 0
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma imK_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imK = 0 := rfl
/-
**Quaternion.re_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ), (↑q).re = ↑q
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma re_ratCast (q : ℚ) : (q : ℍ[R]).re = q := rfl
/-
**Quaternion.im_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ), (↑q).im = 0
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma im_ratCast (q : ℚ) : (q : ℍ[R]).im = 0 := rfl
/-
**Quaternion.imI_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ), (↑q).imI = 0
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma imI_ratCast (q : ℚ) : (q : ℍ[R]).imI = 0 := rfl
/-
**Quaternion.imJ_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ), (↑q).imJ = 0
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma imJ_ratCast (q : ℚ) : (q : ℍ[R]).imJ = 0 := rfl
/-
**Quaternion.imK_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ), (↑q).imK = 0
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma imK_ratCast (q : ℚ) : (q : ℍ[R]).imK = 0 := rfl
/-
**Quaternion.coe_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ≥0), ↑↑q = ↑q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_nnratCast (q : ℚ≥0) : ↑(q : R) = (q : ℍ[R]) := rfl
/-
**Quaternion.coe_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (q : ℚ), ↑↑q = ↑q
参数：q : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_ratCast (q : ℚ) : ↑(q : R) = (q : ℍ[R]) := rfl

section ofScientific
open OfScientific (ofScientific)
variable (m : ℕ) (s : Bool) (e : ℕ)

/-
**Quaternion.coe_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (m : ℕ) (s : Bool) (e : ℕ),   ↑(OfScient
ific.ofScientific m s e) = OfScientific.ofScientific m s e
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_ofScientific : ((ofScientific m s e : R) : ℍ[R]) = ofScientific m s e := rfl
/-
**Quaternion.re_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (m : ℕ) (s : Bool) (e : ℕ),   Quaternion
Algebra.re (OfScientific.ofScientific m s e) = OfScientific.ofScientific m s e
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma re_ofScientific : (ofScientific m s e : ℍ[R]).re = ofScientific m s e := rfl
/-
**Quaternion.imI_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (m : ℕ) (s : Bool) (e : ℕ),   Quaternion
Algebra.imI (OfScientific.ofScientific m s e) = 0
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma imI_ofScientific : (ofScientific m s e : ℍ[R]).imI = 0 := rfl
/-
**Quaternion.imJ_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (m : ℕ) (s : Bool) (e : ℕ),   Quaternion
Algebra.imJ (OfScientific.ofScientific m s e) = 0
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma imJ_ofScientific : (ofScientific m s e : ℍ[R]).imJ = 0 := rfl
/-
**Quaternion.imK_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (m : ℕ) (s : Bool) (e : ℕ),   Quaternion
Algebra.imK (OfScientific.ofScientific m s e) = 0
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma imK_ofScientific : (ofScientific m s e : ℍ[R]).imK = 0 := rfl

end ofScientific

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

@[simps -isSimp]
/-
**Quaternion.instInv** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instInv : Inv ℍ[R]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv ℍ[R] :=
  ⟨fun a => (normSq a)⁻¹ • star a⟩
/-
**Quaternion.instGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instGroupWithZero : GroupWithZero ℍ[R]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupWithZero : GroupWithZero ℍ[R] :=
  { Quaternion.instNontrivial with
    inv_zero := by rw [inv_def, star_zero, smul_zero]
    mul_inv_cancel := fun a ha => by
      rw [inv_def, Algebra.mul_smul_comm (normSq a)⁻¹ a (star a), self_mul_star, smul_coe,
        inv_mul_cancel₀ (normSq_ne_zero.2 ha), coe_one] }

@[norm_cast, simp]
/-
**Quaternion.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹ :=
  map_inv₀ (algebraMap R ℍ[R]) _

@[norm_cast, simp]
/-
**Quaternion.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y :=
  map_div₀ (algebraMap R ℍ[R]) x y

@[norm_cast, simp]
/-
**Quaternion.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_zpow (x : R) (z : Int) : ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z
参数：x : R；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_zpow (x : R) (z : ℤ) : ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z :=
  map_zpow₀ (algebraMap R ℍ[R]) x z
/-
**Quaternion.instDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
形式化陈述：instDivisionRing : DivisionRing ℍ[R] where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Quaternion.normSq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_inv : normSq a⁻¹ = (normSq a)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
-/
theorem normSq_inv : normSq a⁻¹ = (normSq a)⁻¹ :=
  map_inv₀ normSq _
/-
**Quaternion.normSq_div** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_div : normSq (a / b) = normSq a / normSq b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
-/
theorem normSq_div : normSq (a / b) = normSq a / normSq b :=
  map_div₀ normSq a b
/-
**Quaternion.normSq_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_zpow (z : Int) : normSq (a ^ z) = normSq a ^ z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
-/
theorem normSq_zpow (z : ℤ) : normSq (a ^ z) = normSq a ^ z :=
  map_zpow₀ normSq a z

@[norm_cast]
/-
**Quaternion.normSq_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_ratCast (q : Rat) : normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.coe_ratCast`：∀ {R : Type u_1} [inst : Field R] (q : ℚ), ↑↑q =
 ↑q
· 使用定理 `Quaternion.normSq_coe`：normSq_coe : normSq (x : ℍ[R]) = x ^ 2
· 使用定理 `Quaternion.coe_pow`：coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^
 n
-/
theorem normSq_ratCast (q : ℚ) : normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2 := by
  rw [← coe_ratCast, normSq_coe, coe_pow]

end Field

end Quaternion

namespace Cardinal

open Quaternion

section QuaternionAlgebra

variable {R : Type*} (c₁ c₂ c₃ : R)

/-
**Cardinal.pow_four** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pow_four [Infinite R] : #R ^ 4 = #R :=
  power_nat_eq (aleph0_le_mk R) <| by decide

/-- The cardinality of a quaternion algebra, as a type. -/
/-
**Cardinal.mk_quaternionAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0

--- 原说明 ---
The cardinality of a quaternion algebra, as a type.
-/
theorem mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂ c₃)]
  simp only [mk_prod, lift_id]
  ring

@[simp]
/-
**Cardinal.mk_quaternionAlgebra_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_quaternionAlgebra`：mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) =
 #R ^ 4
· 使用定理 `_private.Mathlib.Algebra.Quaternion.0.Cardinal.pow_four`：∀ {R : Type u_1
} [Infinite R], Cardinal.mk R ^ 4 = Cardinal.mk R
-/
theorem mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R := by
  rw [mk_quaternionAlgebra, pow_four]

/-- The cardinality of a quaternion algebra, as a set. -/
/-
**Cardinal.mk_univ_quaternionAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `Cardinal.mk_quaternionAlgebra`：mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) =
 #R ^ 4

--- 原说明 ---
The cardinality of a quaternion algebra, as a set.
-/
theorem mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_univ, mk_quaternionAlgebra]
/-
**Cardinal.mk_univ_quaternionAlgebra_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Card
inal`。
形式化陈述：mk_univ_quaternionAlgebra_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R,
c₁,c₂,c₃]) = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_univ_quaternionAlgebra`：mk_univ_quaternionAlgebra : #(Set.un
iv : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4
· 使用定理 `_private.Mathlib.Algebra.Quaternion.0.Cardinal.pow_four`：∀ {R : Type u_1
} [Infinite R], Cardinal.mk R ^ 4 = Cardinal.mk R
-/
theorem mk_univ_quaternionAlgebra_of_infinite [Infinite R] :
    #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R := by rw [mk_univ_quaternionAlgebra, pow_four]

/-- Show the quaternion `⟨w, x, y, z⟩` as a string `"{ re := w, imI := x, imJ := y, imK := z }"`.

For the typical case of quaternions over ℝ, each component will show as a Cauchy sequence due to
the way Real numbers are represented.
-/
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show the quaternion `⟨w, x, y, z⟩` as a string `"{ re := w, imI := x, imJ := y, 
imK := z }"`.

For the typical case of quaternions over ℝ, each component will show as a Cauchy
 sequence due to
the way Real numbers are represented.
-/
instance [Repr R] {a b c : R} : Repr ℍ[R,a,b,c] where
  reprPrec q _ :=
    s!"\{ re := {repr q.re}, imI := {repr q.imI}, imJ := {repr q.imJ}, imK := {repr q.imK} }"

end QuaternionAlgebra

section Quaternion

variable (R : Type*) [Zero R] [One R] [Neg R]

/-- The cardinality of the quaternions, as a type. -/
@[simp]
/-
**Cardinal.mk_quaternion** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_quaternion : #(ℍ[R]) = #R ^ 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_quaternionAlgebra`：mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) =
 #R ^ 4

--- 原说明 ---
The cardinality of the quaternions, as a type.
-/
theorem mk_quaternion : #(ℍ[R]) = #R ^ 4 :=
  mk_quaternionAlgebra _ _ _
/-
**Cardinal.mk_quaternion_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_quaternion_of_infinite [Infinite R] : #(ℍ[R]) = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_quaternionAlgebra_of_infinite`：mk_quaternionAlgebra_of_infin
ite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R
-/
theorem mk_quaternion_of_infinite [Infinite R] : #(ℍ[R]) = #R :=
  mk_quaternionAlgebra_of_infinite _ _ _

/-- The cardinality of the quaternions, as a set. -/
/-
**Cardinal.mk_univ_quaternion** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_univ_quaternion : #(Set.univ : Set ℍ[R]) = #R ^ 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_univ_quaternionAlgebra`：mk_univ_quaternionAlgebra : #(Set.un
iv : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4

--- 原说明 ---
The cardinality of the quaternions, as a set.
-/
theorem mk_univ_quaternion : #(Set.univ : Set ℍ[R]) = #R ^ 4 :=
  mk_univ_quaternionAlgebra _ _ _
/-
**Cardinal.mk_univ_quaternion_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_univ_quaternionAlgebra_of_infinite`：mk_univ_quaternionAlgebr
a_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R
-/
theorem mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R :=
  mk_univ_quaternionAlgebra_of_infinite _ _ _

end Quaternion

end Cardinal

