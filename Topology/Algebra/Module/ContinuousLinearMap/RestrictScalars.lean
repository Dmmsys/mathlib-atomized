/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Restriction of scalars for continuous linear maps

In this file, we define and study `ContinuousLinearMap.restrictScalars`, which reinterprets
a continuous `R`-linear map as a continuous `S`-linear map, for suitable `R` and `S`.
This is the continuous version of `LinearMap.restrictScalars`.
-/

@[expose] public section

section RestrictScalars

namespace ContinuousLinearMap

section Semiring

variable {A M₁ M₂ R S : Type*} [Semiring A] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommMonoid M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A]

variable (R) in
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : M₁ ->L[A] M₂)
  body: ⟨(f : M₁ ->ₗ[A] M₂).restrictScalars R, f.continuous⟩

@[simp]

中文:
定义 restrictScalars
  签名: (f : M₁ ->L[A] M₂)
  定义体: ⟨(f : M₁ ->ₗ[A] M₂).restrictScalars R, f.continuous⟩

@[simp]

Depends on / 依赖: continuous, f.continuous, restrictScalars
-/
def restrictScalars (f : M₁ ->L[A] M₂) : M₁ ->L[R] M₂ :=
  ⟨(f : M₁ ->ₗ[A] M₂).restrictScalars R, f.continuous⟩

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : M₁ ->L[A] M₂)
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: (f : M₁ ->L[A] M₂)
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars (f : M₁ ->L[A] M₂) :
    (f.restrictScalars R : M₁ ->ₗ[R] M₂) = (f : M₁ ->ₗ[A] M₂).restrictScalars R := rfl

@[simp]
/--
theorem `coe_restrictScalars'` / 定理 `coe_restrictScalars'`

English:
theorem coe_restrictScalars'
  given: (f : M₁ ->L[A] M₂)
  statement: ⇑(f.restrictScalars R) = f
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars'
  条件: (f : M₁ ->L[A] M₂)
  结论: ⇑(f.restrictScalars R) = f
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars' (f : M₁ ->L[A] M₂) : ⇑(f.restrictScalars R) = f := rfl

@[simp]
/--
theorem `toContinuousAddMonoidHom_restrictScalars` / 定理 `toContinuousAddMonoidHom_restrictScalars`

English:
theorem toContinuousAddMonoidHom_restrictScalars
  given: (f : M₁ ->L[A] M₂)
  proof: rfl

中文:
定理 toContinuousAddMonoidHom_restrictScalars
  条件: (f : M₁ ->L[A] M₂)
  证明: rfl
-/
theorem toContinuousAddMonoidHom_restrictScalars (f : M₁ ->L[A] M₂) :
    ↑(f.restrictScalars R) = (f : ContinuousAddMonoidHom M₁ M₂) := rfl

/--
lemma `restrictScalars_zero` / 引理 `restrictScalars_zero`

English:
lemma restrictScalars_zero
  statement: (0 : M₁ ->L[A] M₂).restrictScalars R = 0
  proof: rfl

@[simp]

中文:
引理 restrictScalars_zero
  结论: (0 : M₁ ->L[A] M₂).restrictScalars R = 0
  证明: rfl

@[simp]
-/
@[simp] lemma restrictScalars_zero : (0 : M₁ ->L[A] M₂).restrictScalars R = 0 := rfl

@[simp]
/--
lemma `restrictScalars_add` / 引理 `restrictScalars_add`

English:
lemma restrictScalars_add
  given: [ContinuousAdd M₂] (f g : M₁ ->L[A] M₂)
  proof: rfl

中文:
引理 restrictScalars_add
  条件: [ContinuousAdd M₂] (f g : M₁ ->L[A] M₂)
  证明: rfl
-/
lemma restrictScalars_add [ContinuousAdd M₂] (f g : M₁ ->L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := rfl

variable [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂] [SMulCommClass R S M₂]

@[simp]
/--
theorem `restrictScalars_smul` / 定理 `restrictScalars_smul`

English:
theorem restrictScalars_smul
  given: (c : S) (f : M₁ ->L[A] M₂)
  proof: rfl

中文:
定理 restrictScalars_smul
  条件: (c : S) (f : M₁ ->L[A] M₂)
  证明: rfl
-/
theorem restrictScalars_smul (c : S) (f : M₁ ->L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

variable [ContinuousAdd M₂]

variable (A R S M₁ M₂) in
/--
Definition of `restrictScalarsₗ` / `restrictScalarsₗ` 的定义

English:
definition restrictScalarsₗ
  signature: : (M₁ ->L[A] M₂) ->ₗ[S] M₁ ->L[R] M₂ where
  body: restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

@[simp]

中文:
定义 restrictScalarsₗ
  签名: : (M₁ ->L[A] M₂) ->ₗ[S] M₁ ->L[R] M₂ where
  定义体: restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

@[simp]

Depends on / 依赖: restrictScalars
-/
def restrictScalarsₗ : (M₁ ->L[A] M₂) ->ₗ[S] M₁ ->L[R] M₂ where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

@[simp]
/--
theorem `coe_restrictScalarsₗ` / 定理 `coe_restrictScalarsₗ`

English:
theorem coe_restrictScalarsₗ
  statement: ⇑(restrictScalarsₗ A M₁ M₂ R S) = restrictScalars R
  proof: rfl

中文:
定理 coe_restrictScalarsₗ
  结论: ⇑(restrictScalarsₗ A M₁ M₂ R S) = restrictScalars R
  证明: rfl
-/
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M₁ M₂ R S) = restrictScalars R := rfl

end Semiring

section Ring
variable {A R S M₁ M₂ : Type*} [Ring A] [Ring R] [Ring S]
  [AddCommGroup M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A] [IsTopologicalAddGroup M₂]

@[simp]
/--
lemma `restrictScalars_sub` / 引理 `restrictScalars_sub`

English:
lemma restrictScalars_sub
  given: (f g : M₁ ->L[A] M₂)
  proof: rfl

@[simp]

中文:
引理 restrictScalars_sub
  条件: (f g : M₁ ->L[A] M₂)
  证明: rfl

@[simp]
-/
lemma restrictScalars_sub (f g : M₁ ->L[A] M₂) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := rfl

@[simp]
/--
lemma `restrictScalars_neg` / 引理 `restrictScalars_neg`

English:
lemma restrictScalars_neg
  given: (f : M₁ ->L[A] M₂)
  statement: (-f).restrictScalars R = -f.restrictScalars R
  proof: rfl

中文:
引理 restrictScalars_neg
  条件: (f : M₁ ->L[A] M₂)
  结论: (-f).restrictScalars R = -f.restrictScalars R
  证明: rfl
-/
lemma restrictScalars_neg (f : M₁ ->L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R := rfl

end Ring

end ContinuousLinearMap

end RestrictScalars
