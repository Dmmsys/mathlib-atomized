/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Conformal maps between inner product spaces

A function between inner product spaces which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/

@[expose] public section


noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace Real E] [InnerProductSpace Real F]

open RealInnerProductSpace

/--
theorem `conformalAt_iff'` / 定理 `conformalAt_iff'`

English:
theorem conformalAt_iff'
  given: {f : E -> F} {x : E}
  statement: ConformalAt f x ↔
  proof: by
  rw [conformalAt_iff_isConformalMap_fderiv]; rw [isConformalMap_iff]

中文:
定理 conformalAt_iff'
  条件: {f : E -> F} {x : E}
  结论: ConformalAt f x ↔
  证明: by
  rw [conformalAt_iff_isConformalMap_fderiv]; rw [isConformalMap_iff]

Depends on / 依赖: conformalAt_iff_isConformalMap_fderiv, isConformalMap_iff
-/
theorem conformalAt_iff' {f : E -> F} {x : E} : ConformalAt f x ↔
    exists c : Real, 0 < c ∧ forall u v : E, ⟪fderiv Real f x u, fderiv Real f x v⟫ = c * ⟪u, v⟫ := by
  rw [conformalAt_iff_isConformalMap_fderiv]; rw [isConformalMap_iff]

/--
theorem `conformalAt_iff` / 定理 `conformalAt_iff`

English:
theorem conformalAt_iff
  given: {f : E -> F} {x : E} {f' : E ->L[Real] F} (h : HasFDerivAt f f' x)
  proof: by
  simp only [conformalAt_iff', h.fderiv]

中文:
定理 conformalAt_iff
  条件: {f : E -> F} {x : E} {f' : E ->L[实数] F} (h : 在点处Fréchet可导 f f' x)
  证明: by
  simp only [conformalAt_iff', h.fderiv]

Depends on / 依赖: conformalAt_iff, fderiv, h.fderiv
-/
theorem conformalAt_iff {f : E -> F} {x : E} {f' : E ->L[Real] F} (h : HasFDerivAt f f' x) :
    ConformalAt f x ↔ exists c : Real, 0 < c ∧ forall u v : E, ⟪f' u, f' v⟫ = c * ⟪u, v⟫ := by
  simp only [conformalAt_iff', h.fderiv]

/--
Definition of `conformalFactorAt` / `conformalFactorAt` 的定义

English:
definition conformalFactorAt
  signature: {f : E -> F} {x : E} (h : ConformalAt f x)
  body: Classical.choose (conformalAt_iff'.mp h)

中文:
定义 conformalFactorAt
  签名: {f : E -> F} {x : E} (h : ConformalAt f x)
  定义体: Classical.choose (conformalAt_iff'.mp h)

Depends on / 依赖: Classical, Classical.choose, conformalAt_iff
-/
def conformalFactorAt {f : E -> F} {x : E} (h : ConformalAt f x) : Real :=
  Classical.choose (conformalAt_iff'.mp h)

/--
theorem `conformalFactorAt_pos` / 定理 `conformalFactorAt_pos`

English:
theorem conformalFactorAt_pos
  given: {f : E -> F} {x : E} (h : ConformalAt f x)
  statement: 0 < conformalFactorAt h
  proof: (Classical.choose_spec <| conformalAt_iff'.mp h).1

中文:
定理 conformalFactorAt_pos
  条件: {f : E -> F} {x : E} (h : ConformalAt f x)
  结论: 0 < conformalFactorAt h
  证明: (Classical.choose_spec <| conformalAt_iff'.mp h).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, conformalAt_iff
-/
theorem conformalFactorAt_pos {f : E -> F} {x : E} (h : ConformalAt f x) : 0 < conformalFactorAt h :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).1

/--
theorem `conformalFactorAt_inner_eq_mul_inner'` / 定理 `conformalFactorAt_inner_eq_mul_inner'`

English:
theorem conformalFactorAt_inner_eq_mul_inner'
  given: {f : E -> F} {x : E} (h : ConformalAt f x) (u v : E)
  proof: (Classical.choose_spec <| conformalAt_iff'.mp h).2 u v

中文:
定理 conformalFactorAt_inner_eq_mul_inner'
  条件: {f : E -> F} {x : E} (h : ConformalAt f x) (u v : E)
  证明: (Classical.choose_spec <| conformalAt_iff'.mp h).2 u v

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, conformalAt_iff
-/
theorem conformalFactorAt_inner_eq_mul_inner' {f : E -> F} {x : E} (h : ConformalAt f x) (u v : E) :
    ⟪(fderiv Real f x) u, (fderiv Real f x) v⟫ = (conformalFactorAt h : Real) * ⟪u, v⟫ :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).2 u v

/--
theorem `conformalFactorAt_inner_eq_mul_inner` / 定理 `conformalFactorAt_inner_eq_mul_inner`

English:
theorem conformalFactorAt_inner_eq_mul_inner
  statement: {f : E -> F} {x : E} {f' : E ->L[Real] F}
  proof: H.differentiableAt.hasFDerivAt.unique h ▸ conformalFactorAt_inner_eq_mul_inner' H u v

中文:
定理 conformalFactorAt_inner_eq_mul_inner
  结论: {f : E -> F} {x : E} {f' : E ->L[实数] F}
  证明: H.differentiableAt.hasFDerivAt.unique h ▸ conformalFactorAt_inner_eq_mul_inner' H u v

Depends on / 依赖: H.differentiableAt.hasFDerivAt.unique, conformalFactorAt_inner_eq_mul_inner, differentiableAt, hasFDerivAt, unique
-/
theorem conformalFactorAt_inner_eq_mul_inner {f : E -> F} {x : E} {f' : E ->L[Real] F}
    (h : HasFDerivAt f f' x) (H : ConformalAt f x) (u v : E) :
    ⟪f' u, f' v⟫ = (conformalFactorAt H : Real) * ⟪u, v⟫ :=
  H.differentiableAt.hasFDerivAt.unique h ▸ conformalFactorAt_inner_eq_mul_inner' H u v
