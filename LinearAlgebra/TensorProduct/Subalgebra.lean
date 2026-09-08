/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.TensorProduct.Maps

/-!

# Some results on tensor product of subalgebras

## Linear maps induced by multiplication for subalgebras

Let `R` be a commutative ring, `S` be a commutative `R`-algebra.
Let `A` and `B` be `R`-subalgebras in `S` (`Subalgebra R S`). We define some linear maps
induced by the multiplication in `S`, which are
mainly used in the definition of linearly disjointness.

- `Subalgebra.mulMap`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₐ[R] S`
  induced by the multiplication in `S`, whose image is `A ⊔ B` (`Subalgebra.mulMap_range`).

- `Subalgebra.mulMap'`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₗ[R] A ⊔ B`
  induced by multiplication in `S`, which is surjective (`Subalgebra.mulMap'_surjective`).

- `Subalgebra.lTensorBot`, `Subalgebra.rTensorBot`: the natural isomorphism of `R`-algebras between
  `i(R) ⊗[R] A` and `A`, resp. `A ⊗[R] i(R)` and `A`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `Algebra.TensorProduct.lid`
  and `Algebra.TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  They are `Subalgebra` versions of `Submodule.lTensorOne` and `Submodule.rTensorOne`.

-/

@[expose] public section

open scoped TensorProduct

open Module

noncomputable section

variable {R S T : Type*}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T]

namespace Subalgebra

variable (A : Subalgebra R S)

/-- If `A` is a subalgebra of `S/R`, there is the natural `R`-algebra isomorphism between
`i(R) ⊗[R] A` and `A` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `Algebra.TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`.

This is the `Subalgebra` version of `Submodule.lTensorOne` -/
/-
**Subalgebra.lTensorBot** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：lTensorBot : (⊥ : Subalgebra R S) otimes[R] A ≃ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a subalgebra of `S/R`, there is the natural `R`-algebra isomorphism be
tween
`i(R) ⊗[R] A` and `A` induced by multiplication in `S`, here `i : R → S` is the 
structure map.
This generalizes `Algebra.TensorProduct.lid` as `i(R)` is not necessarily isomor
phic to `R`.

This is the `Subalgebra` version of `Submodule.lTensorOne`
-/
def lTensorBot : (⊥ : Subalgebra R S) ⊗[R] A ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul, (toSubmodule A).lTensorOne_tmul x' a,
      (toSubmodule A).lTensorOne_tmul y' b, (toSubmodule A).lTensorOne_tmul (x' * y') (a * b),
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.lTensorOne_one_tmul _

variable {A}

@[simp]
/-
**Subalgebra.lTensorBot_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：lTensorBot_tmul (x : R) (a : A) : A.lTensorBot (algebraMap R _ x otimesₜ[R
] a) = x • a
参数：x : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lTensorOne_tmul`：lTensorOne_tmul (y : R) (n : N) : N.lTensorOn
e (algebraMap R _ y otimesₜ[R] n) = y • n
-/
theorem lTensorBot_tmul (x : R) (a : A) : A.lTensorBot (algebraMap R _ x ⊗ₜ[R] a) = x • a :=
  (toSubmodule A).lTensorOne_tmul x a

@[simp]
/-
**Subalgebra.lTensorBot_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：lTensorBot_one_tmul (a : A) : A.lTensorBot (1 otimesₜ[R] a) = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lTensorOne_one_tmul`：lTensorOne_one_tmul (n : N) : N.lTensorOn
e (1 otimesₜ[R] n) = n
-/
theorem lTensorBot_one_tmul (a : A) : A.lTensorBot (1 ⊗ₜ[R] a) = a :=
  (toSubmodule A).lTensorOne_one_tmul a

@[simp]
/-
**Subalgebra.lTensorBot_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：lTensorBot_symm_apply (a : A) : A.lTensorBot.symm a = 1 otimesₜ[R] a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensorBot_symm_apply (a : A) : A.lTensorBot.symm a = 1 ⊗ₜ[R] a := rfl

variable (A) in
/-- If `A` is a subalgebra of `S/R`, there is the natural `R`-algebra isomorphism between
`A ⊗[R] i(R)` and `A` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `Algebra.TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`.

This is the `Subalgebra` version of `Submodule.rTensorOne` -/
/-
**Subalgebra.rTensorBot** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：rTensorBot : A otimes[R] (⊥ : Subalgebra R S) ≃ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a subalgebra of `S/R`, there is the natural `R`-algebra isomorphism be
tween
`A ⊗[R] i(R)` and `A` induced by multiplication in `S`, here `i : R → S` is the 
structure map.
This generalizes `Algebra.TensorProduct.rid` as `i(R)` is not necessarily isomor
phic to `R`.

This is the `Subalgebra` version of `Submodule.rTensorOne`
-/
def rTensorBot : A ⊗[R] (⊥ : Subalgebra R S) ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).rTensorOne ?_ ?_
  · rintro a b x y
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul, (toSubmodule A).rTensorOne_tmul x' a,
      (toSubmodule A).rTensorOne_tmul y' b, (toSubmodule A).rTensorOne_tmul (x' * y') (a * b),
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.rTensorOne_tmul_one _

@[simp]
/-
**Subalgebra.rTensorBot_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：rTensorBot_tmul (x : R) (a : A) : A.rTensorBot (a otimesₜ[R] algebraMap R 
_ x) = x • a
参数：x : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.rTensorOne_tmul`：rTensorOne_tmul (y : R) (m : M) : M.rTensorOn
e (m otimesₜ[R] algebraMap R _ y) = y • m
-/
theorem rTensorBot_tmul (x : R) (a : A) : A.rTensorBot (a ⊗ₜ[R] algebraMap R _ x) = x • a :=
  (toSubmodule A).rTensorOne_tmul x a

@[simp]
/-
**Subalgebra.rTensorBot_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：rTensorBot_tmul_one (a : A) : A.rTensorBot (a otimesₜ[R] 1) = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.rTensorOne_tmul_one`：rTensorOne_tmul_one (m : M) : M.rTensorOn
e (m otimesₜ[R] 1) = m
-/
theorem rTensorBot_tmul_one (a : A) : A.rTensorBot (a ⊗ₜ[R] 1) = a :=
  (toSubmodule A).rTensorOne_tmul_one a

@[simp]
/-
**Subalgebra.rTensorBot_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：rTensorBot_symm_apply (a : A) : A.rTensorBot.symm a = a otimesₜ[R] 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rTensorBot_symm_apply (a : A) : A.rTensorBot.symm a = a ⊗ₜ[R] 1 := rfl

variable (A)

@[simp]
/-
**Subalgebra.comm_trans_lTensorBot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：comm_trans_lTensorBot : (Algebra.TensorProduct.comm R _ _).trans A.lTensor
Bot = A.rTensorBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.toLinearEquiv_injective`：toLinearEquiv_injective : Function.Inj
ective (toLinearEquiv : _ -> A₁ ≃ₗ[R] A₂)
· 使用定理 `Submodule.comm_trans_lTensorOne`：comm_trans_lTensorOne : (TensorProduct.
comm R _ _).trans M.lTensorOne = M.rTensorOne
-/
theorem comm_trans_lTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.lTensorBot = A.rTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_lTensorOne

@[simp]
/-
**Subalgebra.comm_trans_rTensorBot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：comm_trans_rTensorBot : (Algebra.TensorProduct.comm R _ _).trans A.rTensor
Bot = A.lTensorBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.toLinearEquiv_injective`：toLinearEquiv_injective : Function.Inj
ective (toLinearEquiv : _ -> A₁ ≃ₗ[R] A₂)
· 使用定理 `Submodule.comm_trans_rTensorOne`：comm_trans_rTensorOne : (TensorProduct.
comm R _ _).trans M.rTensorOne = M.lTensorOne
-/
theorem comm_trans_rTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.rTensorBot = A.lTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_rTensorOne

end Subalgebra

namespace Algebra.TensorProduct

variable (R S T)

set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-algebras `S,T`, there is a natural `R`-linear isomorphism from `S ⊗[R] T` to
`S' ⊗[R] T'` where `S',T'` are the images of `S,T` in `S ⊗[R] T` respectively.
This is promoted to an `R`-algebra isomorphism `Algebra.TensorProduct.algEquivIncludeRange`. -/
/-
**Algebra.TensorProduct.linearEquivIncludeRange** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.TensorProduct`。
形式化陈述：linearEquivIncludeRange : S otimes[R] T ≃ₗ[R] (includeLeft : S ->ₐ[R] S ot
imes[R] T).range otimes[R] (includeRight : T ->ₐ[R] S otimes[R] T).range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-algebras `S,T`, there is a natural `R`-linear isomorphism from `S ⊗[R]
 T` to
`S' ⊗[R] T'` where `S',T'` are the images of `S,T` in `S ⊗[R] T` respectively.
This is promoted to an `R`-algebra isomorphism `Algebra.TensorProduct.algEquivIn
cludeRange`.
-/
def linearEquivIncludeRange :
    S ⊗[R] T ≃ₗ[R] (includeLeft : S →ₐ[R] S ⊗[R] T).range ⊗[R]
      (includeRight : T →ₐ[R] S ⊗[R] T).range := .ofLinearMap
  (_root_.TensorProduct.map
    includeLeft.toLinearMap.rangeRestrict includeRight.toLinearMap.rangeRestrict)
  (includeLeft.toLinearMap.range.mulMap includeRight.toLinearMap.range)
  (_root_.TensorProduct.ext' <| by
    rintro ⟨x', x, rfl : x ⊗ₜ 1 = x'⟩ ⟨y', y, rfl : 1 ⊗ₜ y = y'⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    erw [Submodule.mulMap_tmul]
    rw [tmul_mul_tmul, mul_one, one_mul, _root_.TensorProduct.map_tmul]
    rfl)
  (_root_.TensorProduct.ext' fun x y ↦ by
    rw [LinearMap.comp_apply, LinearMap.id_apply, _root_.TensorProduct.map_tmul]
    erw [Submodule.mulMap_tmul]
    change (x ⊗ₜ 1) * (1 ⊗ₜ y) = _
    rw [tmul_mul_tmul, mul_one, one_mul])
/-
**Algebra.TensorProduct.linearEquivIncludeRange_toLinearMap** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.TensorProduct`。
形式化陈述：linearEquivIncludeRange_toLinearMap : (linearEquivIncludeRange R S T).toLi
nearMap = _root_.TensorProduct.map includeLeft.toLinearMap.rangeRestrict include
Right.toLinearMap.rangeRestrict
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivIncludeRange_toLinearMap :
    (linearEquivIncludeRange R S T).toLinearMap =
      _root_.TensorProduct.map includeLeft.toLinearMap.rangeRestrict
        includeRight.toLinearMap.rangeRestrict := rfl
/-
**Algebra.TensorProduct.linearEquivIncludeRange_symm_toLinearMap** 是 Mathlib 中的一
个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：linearEquivIncludeRange_symm_toLinearMap : (linearEquivIncludeRange R S T)
.symm.toLinearMap = includeLeft.toLinearMap.range.mulMap includeRight.toLinearMa
p.range
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivIncludeRange_symm_toLinearMap :
    (linearEquivIncludeRange R S T).symm.toLinearMap =
      includeLeft.toLinearMap.range.mulMap includeRight.toLinearMap.range := rfl

@[simp]
/-
**Algebra.TensorProduct.linearEquivIncludeRange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.TensorProduct`。
形式化陈述：linearEquivIncludeRange_tmul (x y) : linearEquivIncludeRange R S T (x otim
esₜ[R] y) = ((includeLeft : S ->ₐ[R] S otimes[R] T).rangeRestrict x) otimesₜ[R] 
((includeRight : T ->ₐ[R] S otimes[R] T).rangeRestrict y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivIncludeRange_tmul (x y) :
    linearEquivIncludeRange R S T (x ⊗ₜ[R] y) =
      ((includeLeft : S →ₐ[R] S ⊗[R] T).rangeRestrict x) ⊗ₜ[R]
        ((includeRight : T →ₐ[R] S ⊗[R] T).rangeRestrict y) := rfl

@[simp]
/-
**Algebra.TensorProduct.linearEquivIncludeRange_symm_tmul** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.TensorProduct`。
形式化陈述：linearEquivIncludeRange_symm_tmul (x y) : (linearEquivIncludeRange R S T).
symm (x otimesₜ[R] y) = x.1 * y.1
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivIncludeRange_symm_tmul (x y) :
    (linearEquivIncludeRange R S T).symm (x ⊗ₜ[R] y) = x.1 * y.1 := rfl

/-- Given `R`-algebras `S,T`, there is a natural `R`-algebra isomorphism from `S ⊗[R] T` to
`S' ⊗[R] T'` where `S',T'` are the images of `S,T` in `S ⊗[R] T` respectively. -/
/-
**Algebra.TensorProduct.algEquivIncludeRange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.
TensorProduct`。
形式化陈述：algEquivIncludeRange : S otimes[R] T ≃ₐ[R] (includeLeft : S ->ₐ[R] S otime
s[R] T).range otimes[R] (includeRight : T ->ₐ[R] S otimes[R] T).range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-algebras `S,T`, there is a natural `R`-algebra isomorphism from `S ⊗[R
] T` to
`S' ⊗[R] T'` where `S',T'` are the images of `S,T` in `S ⊗[R] T` respectively.
-/
def algEquivIncludeRange :
    S ⊗[R] T ≃ₐ[R] (includeLeft : S →ₐ[R] S ⊗[R] T).range ⊗[R]
      (includeRight : T →ₐ[R] S ⊗[R] T).range :=
  algEquivOfLinearEquivTensorProduct (linearEquivIncludeRange R S T) (by simp) rfl
/-
**Algebra.TensorProduct.algEquivIncludeRange_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 
`Algebra.TensorProduct`。
形式化陈述：algEquivIncludeRange_toAlgHom : (algEquivIncludeRange R S T).toAlgHom = ma
p includeLeft.rangeRestrict includeRight.rangeRestrict
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquivIncludeRange_toAlgHom :
    (algEquivIncludeRange R S T).toAlgHom =
      map includeLeft.rangeRestrict includeRight.rangeRestrict := rfl

@[simp]
/-
**Algebra.TensorProduct.algEquivIncludeRange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.TensorProduct`。
形式化陈述：algEquivIncludeRange_tmul (x y) : algEquivIncludeRange R S T (x otimesₜ[R]
 y) = ((includeLeft : S ->ₐ[R] S otimes[R] T).rangeRestrict x) otimesₜ[R] ((incl
udeRight : T ->ₐ[R] S otimes[R] T).rangeRestrict y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquivIncludeRange_tmul (x y) :
    algEquivIncludeRange R S T (x ⊗ₜ[R] y) =
      ((includeLeft : S →ₐ[R] S ⊗[R] T).rangeRestrict x) ⊗ₜ[R]
        ((includeRight : T →ₐ[R] S ⊗[R] T).rangeRestrict y) := rfl

@[simp]
/-
**Algebra.TensorProduct.algEquivIncludeRange_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：algEquivIncludeRange_symm_tmul (x y) : (algEquivIncludeRange R S T).symm (
x otimesₜ[R] y) = x.1 * y.1
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquivIncludeRange_symm_tmul (x y) :
    (algEquivIncludeRange R S T).symm (x ⊗ₜ[R] y) = x.1 * y.1 := rfl

end Algebra.TensorProduct

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`,
there is the natural `R`-algebra homomorphism
`A ⊗[R] B →ₐ[R] S` induced by multiplication in `S`. -/
/-
**Subalgebra.mulMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.mulMap : A otimes[R] B ->ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`,
there is the natural `R`-algebra homomorphism
`A ⊗[R] B →ₐ[R] S` induced by multiplication in `S`.
-/
def Subalgebra.mulMap : A ⊗[R] B →ₐ[R] S := Algebra.TensorProduct.productMap A.val B.val

variable (R S T) in
/-
**Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom : (algEquivInclud
eRange R S T).symm.toAlgHom = (includeLeft : S ->ₐ[R] S otimes[R] T).range.mulMa
p includeRight.range
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom :
    (algEquivIncludeRange R S T).symm.toAlgHom =
      (includeLeft : S →ₐ[R] S ⊗[R] T).range.mulMap includeRight.range := rfl

namespace Subalgebra

@[simp]
/-
**Subalgebra.mulMap_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_tmul (a : A) (b : B) : mulMap A B (a otimesₜ[R] b) = a.1 * b.1
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulMap_tmul (a : A) (b : B) : mulMap A B (a ⊗ₜ[R] b) = a.1 * b.1 := rfl
/-
**Subalgebra.mulMap_map_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_map_comp_eq (f : S ->ₐ[R] T) : (mulMap (A.map f) (B.map f)).comp (A
lgebra.TensorProduct.map (f.subalgebraMap A) (f.subalgebraMap B)) = f.comp (mulM
ap A B)
参数：f : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulMap_map_comp_eq (f : S →ₐ[R] T) :
    (mulMap (A.map f) (B.map f)).comp
      (Algebra.TensorProduct.map (f.subalgebraMap A) (f.subalgebraMap B))
        = f.comp (mulMap A B) := by
  ext <;> simp
/-
**Subalgebra.mulMap_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (to
Submodule B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B) :=
  rfl
/-
**Subalgebra.mulMap_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R
 B A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A) := by
  ext <;> simp
/-
**Subalgebra.mulMap_range** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_range : (A.mulMap B).range = A ⊔ B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.productMap_range`：productMap_range : (productMap f
 g).range = f.range ⊔ g.range
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subalgebra.range_val`：range_val : S.val.range = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulMap_range : (A.mulMap B).range = A ⊔ B := by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]
/-
**Subalgebra.mulMap_bot_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_bot_left_eq : mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `Submodule.mulMap_one_left_eq`：mulMap_one_left_eq : mulMap (Subalgebra.to
Submodule ⊥) N = N.subtype ∘ₗ N.lTensorOne.toLinearMap
-/
theorem mulMap_bot_left_eq : mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_left_eq
/-
**Subalgebra.mulMap_bot_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mulMap_bot_right_eq : mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `Submodule.mulMap_one_right_eq`：mulMap_one_right_eq : mulMap M (Subalgebr
a.toSubmodule ⊥) = M.subtype ∘ₗ M.rTensorOne.toLinearMap
-/
theorem mulMap_bot_right_eq : mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_right_eq

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`,
there is the natural `R`-algebra homomorphism
`A ⊗[R] B →ₐ[R] A ⊔ B` induced by multiplication in `S`,
which is surjective (`Subalgebra.mulMap'_surjective`). -/
/-
**Subalgebra.mulMap'** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：mulMap' : A otimes[R] B ->ₐ[R] ↥(A ⊔ B)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.mulMap_range`：mulMap_range : (A.mulMap B).range = A ⊔ B

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`,
there is the natural `R`-algebra homomorphism
`A ⊗[R] B →ₐ[R] A ⊔ B` induced by multiplication in `S`,
which is surjective (`Subalgebra.mulMap'_surjective`).
-/
def mulMap' : A ⊗[R] B →ₐ[R] ↥(A ⊔ B) :=
  (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

variable {A B} in
@[simp]
/-
**Subalgebra.val_mulMap'_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   {A B : Subalgebra R S} (a : ↥A) (b : ↥B), ↑((A.
mulMap' B) (a ⊗ₜ[R] b)) = ↑a * ↑b
参数：a : ↥A；b : ↥B；(A.mulMap' B) (a ⊗ₜ[R] b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mulMap'_tmul (a : A) (b : B) : (mulMap' A B (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl
/-
**Subalgebra.mulMap'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   (A B : Subalgebra R S), Function.Surjective ⇑(A
.mulMap' B)
参数：A B : Subalgebra R S；A.mulMap' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.mulMap_range`：mulMap_range : (A.mulMap B).range = A ⊔ B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem mulMap'_surjective : Function.Surjective (mulMap' A B) := by
  simp_rw [mulMap', AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]

end Subalgebra

end CommSemiring

