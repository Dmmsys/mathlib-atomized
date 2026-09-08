/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Constructions relating multilinear maps and tensor products.
-/

@[expose] public section

namespace MultilinearMap

section DomCoprod

open TensorProduct

variable {R ι₁ ι₂ ι₃ ι₄ : Type*}
variable [CommSemiring R]
variable {N₁ : Type*} [AddCommMonoid N₁] [Module R N₁]
variable {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

attribute [local simp] add_tmul tmul_add smul_tmul

section

variable {N : ι₁ ⊕ ι₂ → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Given a family of modules `N` indexed by a type `ι₁ ⊕ ι₂`,
a multilinear map from the modules `N (.inl i₁)` to `N₁` and
a multilinear map from the modules `N (.inr i₁)` to `N₂`, this
is the induced multilinear map from all the modules `N i` to `N₁ ⊗ N₂`. -/
@[simps apply]
/-
**MultilinearMap.domCoprodDep** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domCoprodDep (a : MultilinearMap R (fun i₁ => N (.inl i₁)) N₁) (b : Multil
inearMap R (fun i₂ => N (.inr i₂)) N₂) : MultilinearMap R N (N₁ otimes[R] N₂) wh
ere toFun v
参数：a : MultilinearMap R (fun i₁ => N (.inl i₁)) N₁；b : MultilinearMap R (fun i₂ 
=> N (.inr i₂)) N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of modules `N` indexed by a type `ι₁ ⊕ ι₂`,
a multilinear map from the modules `N (.inl i₁)` to `N₁` and
a multilinear map from the modules `N (.inr i₁)` to `N₂`, this
is the induced multilinear map from all the modules `N i` to `N₁ ⊗ N₂`.
-/
def domCoprodDep (a : MultilinearMap R (fun i₁ ↦ N (.inl i₁)) N₁)
    (b : MultilinearMap R (fun i₂ ↦ N (.inr i₂)) N₂) :
    MultilinearMap R N (N₁ ⊗[R] N₂) where
  toFun v := a (fun i₁ ↦ v (.inl i₁)) ⊗ₜ b (fun i₂ ↦ v (.inr i₂))
  map_update_add' := by
    rintro _ _ (_ | _) _ _
    · let := Classical.decEq ι₁; simp
    · let := Classical.decEq ι₂; simp
  map_update_smul' := by
    rintro _ m (i₁ | i₂) p q
    · let := Classical.decEq ι₁; simp
    · let := Classical.decEq ι₂; simp

/-- A more bundled version of `MultilinearMap.domCoprodDep`, as a linear map
from the tensor product of spaces of multilinear maps. -/
/-
**MultilinearMap.domCoprodDep'** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domCoprodDep' : MultilinearMap R (fun i₁ => N (.inl i₁)) N₁ otimes[R] Mult
ilinearMap R (fun i₂ => N (.inr i₂)) N₂ ->ₗ[R] MultilinearMap R N (N₁ otimes[R] 
N₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A more bundled version of `MultilinearMap.domCoprodDep`, as a linear map
from the tensor product of spaces of multilinear maps.
-/
def domCoprodDep' :
    MultilinearMap R (fun i₁ ↦ N (.inl i₁)) N₁ ⊗[R] MultilinearMap R (fun i₂ ↦ N (.inr i₂)) N₂ →ₗ[R]
        MultilinearMap R N (N₁ ⊗[R] N₂) :=
  TensorProduct.lift (LinearMap.mk₂ R domCoprodDep
    (by aesop) (by aesop) (by aesop) (by aesop))

@[simp]
/-
**MultilinearMap.domCoprodDep'_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：∀ {R : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} [inst : CommSemiring R] {
N₁ : Type u_6} [inst_1 : AddCommMonoid N₁]   [inst_2 : _root_.Module R N₁] {N₂ :
 Type u_7} [inst_3 : AddCommMonoid N₂] [inst_4 : _root_.Module R N₂]   {N : ι₁ ⊕
 ι₂ → Type u_8} [inst_5 : (i : ι₁ ⊕ ι₂) → AddCommMonoid (N i)]   [inst_6 : (i : 
ι₁ ⊕ ι₂) → _root_.Module R (N i)] (a : MultilinearMap R (fun i₁ => N (Sum.inl i₁
)) N₁)   (b : MultilinearMap R (fun i₂ => N (Sum.inr i₂)) N₂), MultilinearMap.do
mCoprodDep' (a ⊗ₜ[R] b) = a.domCoprodDep b
参数：i : ι₁ ⊕ ι₂；N i；i : ι₁ ⊕ ι₂；N i；a : MultilinearMap R (fun i₁ => N (Sum.inl i₁
)) N₁；b : MultilinearMap R (fun i₂ => N (Sum.inr i₂)) N₂；a ⊗ₜ[R] b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domCoprodDep'_apply (a : MultilinearMap R (fun i₁ ↦ N (.inl i₁)) N₁)
    (b : MultilinearMap R (fun i₂ ↦ N (.inr i₂)) N₂) :
    domCoprodDep' (a ⊗ₜ b) = domCoprodDep a b := by
  rfl

end

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces the map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor product
of the codomain.

This can be thought of as combining `Equiv.sumArrowEquivProdArrow.symm` with
`TensorProduct.map`, noting that the two operations can't be separated as the intermediate result
is not a `MultilinearMap`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of `ι₁ → N`, doing so
introduces `Sum.elim N'₁ N'₂` types in the result which are difficult to work with and not defeq
to the simple case defined here. See
[this zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near/218484619).
-/
@[simps! apply]
/-
**MultilinearMap.domCoprod** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domCoprod (a : MultilinearMap R (fun _ : ι₁ => N) N₁) (b : MultilinearMap 
R (fun _ : ι₂ => N) N₂) : MultilinearMap R (fun _ : ι₁ oplus ι₂ => N) (N₁ otimes
[R] N₂)
参数：a : MultilinearMap R (fun _ : ι₁ => N) N₁；b : MultilinearMap R (fun _ : ι₂ =>
 N) N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces th
e map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor p
roduct
of the codomain.

This can be thought of as combining `Equiv.sumArrowEquivProdArrow.symm` with
`TensorProduct.map`, noting that the two operations can't be separated as the in
termediate result
is not a `MultilinearMap`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of
 `ι₁ → N`, doing so
introduces `Sum.elim N'₁ N'₂` types in the result which are difficult to work wi
th and not defeq
to the simple case defined here. See
[this zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-th
ere.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near
/218484619).
-/
def domCoprod (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) :
    MultilinearMap R (fun _ : ι₁ ⊕ ι₂ => N) (N₁ ⊗[R] N₂) :=
  domCoprodDep a b

/-- A more bundled version of `MultilinearMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
/-
**MultilinearMap.domCoprod'** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domCoprod' : MultilinearMap R (fun _ : ι₁ => N) N₁ otimes[R] MultilinearMa
p R (fun _ : ι₂ => N) N₂ ->ₗ[R] MultilinearMap R (fun _ : ι₁ oplus ι₂ => N) (N₁ 
otimes[R] N₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A more bundled version of `MultilinearMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`.
-/
def domCoprod' :
    MultilinearMap R (fun _ : ι₁ => N) N₁ ⊗[R] MultilinearMap R (fun _ : ι₂ => N) N₂ →ₗ[R]
      MultilinearMap R (fun _ : ι₁ ⊕ ι₂ => N) (N₁ ⊗[R] N₂) :=
  domCoprodDep' (R := R) (N := fun (_ : ι₁ ⊕ ι₂) ↦ N)

@[simp]
/-
**MultilinearMap.domCoprod'_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：∀ {R : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} [inst : CommSemiring R] {
N₁ : Type u_6} [inst_1 : AddCommMonoid N₁]   [inst_2 : _root_.Module R N₁] {N₂ :
 Type u_7} [inst_3 : AddCommMonoid N₂] [inst_4 : _root_.Module R N₂] {N : Type u
_8}   [inst_5 : AddCommMonoid N] [inst_6 : _root_.Module R N] (a : MultilinearMa
p R (fun x => N) N₁)   (b : MultilinearMap R (fun x => N) N₂), MultilinearMap.do
mCoprod' (a ⊗ₜ[R] b) = a.domCoprod b
参数：a : MultilinearMap R (fun x => N) N₁；b : MultilinearMap R (fun x => N) N₂；a ⊗
ₜ[R] b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domCoprod'_apply (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) : domCoprod' (a ⊗ₜ[R] b) = domCoprod a b :=
  rfl

/-- When passed an `Equiv.sumCongr`, `MultilinearMap.domDomCongr` distributes over
`MultilinearMap.domCoprod`. -/
/-
**MultilinearMap.domCoprod_domDomCongr_sumCongr** 是 Mathlib 中的一个定理，位于命名空间 `Multi
linearMap`。
形式化陈述：domCoprod_domDomCongr_sumCongr (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
 (b : MultilinearMap R (fun _ : ι₂ => N) N₂) (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) : (a.
domCoprod b).domDomCongr (σa.sumCongr σb) = (a.domDomCongr σa).domCoprod (b.domD
omCongr σb)
参数：a : MultilinearMap R (fun _ : ι₁ => N) N₁；b : MultilinearMap R (fun _ : ι₂ =>
 N) N₂；σa : ι₁ ≃ ι₃；σb : ι₂ ≃ ι₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When passed an `Equiv.sumCongr`, `MultilinearMap.domDomCongr` distributes over
`MultilinearMap.domCoprod`.
-/
theorem domCoprod_domDomCongr_sumCongr (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) :
    (a.domCoprod b).domDomCongr (σa.sumCongr σb) =
      (a.domDomCongr σa).domCoprod (b.domDomCongr σb) :=
  rfl

end DomCoprod

end MultilinearMap

