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

variable {R R₂ : Type*} [Ring R] [Ring R₂] {σ : R ->+* R₂} {M M₂ : Type*}
  [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]
  (S : Submodule R M)

open ContinuousLinearMap

/--
Definition of `mkQL` / `mkQL` 的定义

English:
definition mkQL
  signature: : M ->L[R] M ⧸ S where
  body: S.mkQ
  cont := continuous_quot_mk

@[simp, norm_cast]

中文:
定义 mkQL
  签名: : M ->L[R] M ⧸ S where
  定义体: S.mkQ
  cont := continuous_quot_mk

@[simp, norm_cast]

Depends on / 依赖: S.mkQ
-/
def mkQL : M ->L[R] M ⧸ S where
  toLinearMap := S.mkQ
  cont := continuous_quot_mk

@[simp, norm_cast]
/--
theorem `toLinearMap_mkQL` / 定理 `toLinearMap_mkQL`

English:
theorem toLinearMap_mkQL
  statement: (S.mkQL : M ->ₗ[R] M ⧸ S) = S.mkQ
  proof: rfl

@[simp]

中文:
定理 toLinearMap_mkQL
  结论: (S.mkQL : M ->ₗ[R] M ⧸ S) = S.mkQ
  证明: rfl

@[simp]
-/
theorem toLinearMap_mkQL : (S.mkQL : M ->ₗ[R] M ⧸ S) = S.mkQ := rfl

@[simp]
/--
theorem `coe_mkQL` / 定理 `coe_mkQL`

English:
theorem coe_mkQL
  statement: ⇑S.mkQL = S.mkQ
  proof: rfl

中文:
定理 coe_mkQL
  结论: ⇑S.mkQL = S.mkQ
  证明: rfl
-/
theorem coe_mkQL : ⇑S.mkQL = S.mkQ := rfl

/--
theorem `mkQL_apply` / 定理 `mkQL_apply`

English:
theorem mkQL_apply
  given: (x : M)
  statement: S.mkQL x = S.mkQ x
  proof: by simp

中文:
定理 mkQL_apply
  条件: (x : M)
  结论: S.mkQL x = S.mkQ x
  证明: by simp
-/
theorem mkQL_apply (x : M) : S.mkQL x = S.mkQ x := by simp

/--
theorem `isQuotientMap_mkQL` / 定理 `isQuotientMap_mkQL`

English:
theorem isQuotientMap_mkQL
  statement: IsQuotientMap S.mkQL
  proof: isQuotientMap_quot_mk

中文:
定理 isQuotientMap_mkQL
  结论: 是商映射 S.mkQL
  证明: isQuotientMap_quot_mk

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem isQuotientMap_mkQL : IsQuotientMap S.mkQL := isQuotientMap_quot_mk

/--
theorem `isOpenQuotientMap_mkQL` / 定理 `isOpenQuotientMap_mkQL`

English:
theorem isOpenQuotientMap_mkQL
  given: [ContinuousAdd M]
  statement: IsOpenQuotientMap S.mkQL
  proof: S.isOpenQuotientMap_mkQ

中文:
定理 isOpenQuotientMap_mkQL
  条件: [连续加法 M]
  结论: 是OpenQuotient映射 S.mkQL
  证明: S.isOpenQuotientMap_mkQ

Depends on / 依赖: S.isOpenQuotientMap_mkQ, isOpenQuotientMap_mkQ
-/
theorem isOpenQuotientMap_mkQL [ContinuousAdd M] : IsOpenQuotientMap S.mkQL :=
  S.isOpenQuotientMap_mkQ

/--
Definition of `liftQL` / `liftQL` 的定义

English:
definition liftQL
  signature: (f : M ->SL[σ] M₂) (h : S <= f.ker)
  body: S.liftQ f h
  cont := continuous_quot_lift _ f.continuous

@[simp, norm_cast]

中文:
定义 liftQL
  签名: (f : M ->SL[σ] M₂) (h : S <= f.ker)
  定义体: S.liftQ f h
  cont := continuous_quot_lift _ f.continuous

@[simp, norm_cast]

Depends on / 依赖: S.liftQ
-/
def liftQL (f : M ->SL[σ] M₂) (h : S <= f.ker) : M ⧸ S ->SL[σ] M₂ where
  toLinearMap := S.liftQ f h
  cont := continuous_quot_lift _ f.continuous

@[simp, norm_cast]
/--
theorem `toLinearMap_liftQL` / 定理 `toLinearMap_liftQL`

English:
theorem toLinearMap_liftQL
  given: (f : M ->SL[σ] M₂) (h : S <= f.ker)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_liftQL
  条件: (f : M ->SL[σ] M₂) (h : S <= f.ker)
  证明: rfl

@[simp]
-/
theorem toLinearMap_liftQL (f : M ->SL[σ] M₂) (h : S <= f.ker) :
    (S.liftQL f h).toLinearMap = S.liftQ f.toLinearMap h := rfl

@[simp]
/--
theorem `coe_liftQL` / 定理 `coe_liftQL`

English:
theorem coe_liftQL
  given: (f : M ->SL[σ] M₂) (h : S <= f.ker)
  proof: rfl

中文:
定理 coe_liftQL
  条件: (f : M ->SL[σ] M₂) (h : S <= f.ker)
  证明: rfl
-/
theorem coe_liftQL (f : M ->SL[σ] M₂) (h : S <= f.ker) :
    ⇑(S.liftQL f h) = S.liftQ f.toLinearMap h :=
  rfl

/--
theorem `liftQL_apply` / 定理 `liftQL_apply`

English:
theorem liftQL_apply
  given: (f : M ->SL[σ] M₂) (h : S <= f.ker) (x : M ⧸ S)
  proof: by
  simp

中文:
定理 liftQL_apply
  条件: (f : M ->SL[σ] M₂) (h : S <= f.ker) (x : M ⧸ S)
  证明: by
  simp
-/
theorem liftQL_apply (f : M ->SL[σ] M₂) (h : S <= f.ker) (x : M ⧸ S) :
    S.liftQL f h x = S.liftQ f.toLinearMap h x := by
  simp

end Ring

end Submodule
