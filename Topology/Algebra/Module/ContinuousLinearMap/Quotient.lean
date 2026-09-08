/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sharvil Kesarwani
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear maps and quotient topological modules

In this file, we collect various continuous linear maps associated to quotient spaces.

## Main definitions

* `Submodule.mkQL S` is the quotient map `M →L[R] M ⧸ S`. In other words, it is
  `Submodule.mkQ S` bundled as a `ContinuousLinearMap`.
* `Submodule.liftQL S f h` is the map `M ⧸ S →SL[σ] N` given by `f : M →SL[σ] N` and a proof
  `h : S ≤ f.ker` that `f` vanishes on `S`. In other words, it is `Submodule.liftQ S f h` bundled
  as a `ContinuousLinearMap`.

## TODO

* Define `Submodule.mapQL`, the continuous linear bundling of `Submodule.mapQ`.
-/

@[expose] public section

open Topology

namespace Submodule

section Ring

variable {R R₂ : Type*} [Ring R] [Ring R₂] {σ : R →+* R₂} {M M₂ : Type*}
  [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]
  (S : Submodule R M)

open ContinuousLinearMap

/-- `Submodule.mkQ` as a `ContinuousLinearMap`. -/
/-
**Submodule.mkQL** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mkQL : M ->L[R] M ⧸ S where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.mkQ` as a `ContinuousLinearMap`.
-/
def mkQL : M →L[R] M ⧸ S where
  toLinearMap := S.mkQ
  cont := continuous_quot_mk

@[simp, norm_cast]
/-
**Submodule.toLinearMap_mkQL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearMap_mkQL : (S.mkQL : M ->ₗ[R] M ⧸ S) = S.mkQ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_mkQL : (S.mkQL : M →ₗ[R] M ⧸ S) = S.mkQ := rfl

@[simp]
/-
**Submodule.coe_mkQL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_mkQL : ⇑S.mkQL = S.mkQ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkQL : ⇑S.mkQL = S.mkQ := rfl
/-
**Submodule.mkQL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mkQL_apply (x : M) : S.mkQL x = S.mkQ x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkQL_apply (x : M) : S.mkQL x = S.mkQ x := by simp
/-
**Submodule.isQuotientMap_mkQL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isQuotientMap_mkQL : IsQuotientMap S.mkQL
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem isQuotientMap_mkQL : IsQuotientMap S.mkQL := isQuotientMap_quot_mk
/-
**Submodule.isOpenQuotientMap_mkQL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOpenQuotientMap_mkQL [ContinuousAdd M] : IsOpenQuotientMap S.mkQL
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isOpenQuotientMap_mkQ`：isOpenQuotientMap_mkQ [ContinuousAdd M]
 : IsOpenQuotientMap S.mkQ
-/
theorem isOpenQuotientMap_mkQL [ContinuousAdd M] : IsOpenQuotientMap S.mkQL :=
  S.isOpenQuotientMap_mkQ

/-- `Submodule.liftQ` as a `ContinuousLinearMap`. -/
/-
**Submodule.liftQL** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：liftQL (f : M ->SL[σ] M₂) (h : S <= f.ker) : M ⧸ S ->SL[σ] M₂ where toLine
arMap
参数：f : M ->SL[σ] M₂；h : S <= f.ker。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.liftQ` as a `ContinuousLinearMap`.
-/
def liftQL (f : M →SL[σ] M₂) (h : S ≤ f.ker) : M ⧸ S →SL[σ] M₂ where
  toLinearMap := S.liftQ f h
  cont := continuous_quot_lift _ f.continuous

@[simp, norm_cast]
/-
**Submodule.toLinearMap_liftQL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearMap_liftQL (f : M ->SL[σ] M₂) (h : S <= f.ker) : (S.liftQL f h).to
LinearMap = S.liftQ f.toLinearMap h
参数：f : M ->SL[σ] M₂；h : S <= f.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_liftQL (f : M →SL[σ] M₂) (h : S ≤ f.ker) :
    (S.liftQL f h).toLinearMap = S.liftQ f.toLinearMap h := rfl

@[simp]
/-
**Submodule.coe_liftQL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_liftQL (f : M ->SL[σ] M₂) (h : S <= f.ker) : ⇑(S.liftQL f h) = S.liftQ
 f.toLinearMap h
参数：f : M ->SL[σ] M₂；h : S <= f.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftQL (f : M →SL[σ] M₂) (h : S ≤ f.ker) :
    ⇑(S.liftQL f h) = S.liftQ f.toLinearMap h :=
  rfl
/-
**Submodule.liftQL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：liftQL_apply (f : M ->SL[σ] M₂) (h : S <= f.ker) (x : M ⧸ S) : S.liftQL f 
h x = S.liftQ f.toLinearMap h x
参数：f : M ->SL[σ] M₂；h : S <= f.ker；x : M ⧸ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftQL_apply (f : M →SL[σ] M₂) (h : S ≤ f.ker) (x : M ⧸ S) :
    S.liftQL f h x = S.liftQ f.toLinearMap h x := by
  simp

end Ring

end Submodule

