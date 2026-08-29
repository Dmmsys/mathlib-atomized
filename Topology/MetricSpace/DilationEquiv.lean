/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.Dilation

/-!
# Dilation equivalence

In this file we define `DilationEquiv X Y`, a type of bundled equivalences between `X` and `Y` such
that `edist (f x) (f y) = r * edist x y` for some `r : ℝ≥0`, `r ≠ 0`.

We also develop basic API about these equivalences.

## TODO

- Add missing lemmas (compare to other `*Equiv` structures).
- [after-port] Add `DilationEquivInstance` for `IsometryEquiv`.
-/

@[expose] public section

open scoped NNReal ENNReal
open Function Set Filter Bornology
open Dilation (ratio ratio_ne_zero ratio_pos edist_eq)

section Class

variable (F : Type*) (X Y : outParam Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/--
Definition of `DilationEquivClass` / `DilationEquivClass` 的定义

English:
class DilationEquivClass
  parameters: [EquivLike F X Y]
  axioms and operations (1):
    - edist_eq' : forall f : F, exists r : Real>=0, r != 0 ∧ forall x y : X, edist (f x) (f y) = r * edist x y

中文:
类 DilationEquivClass
  参数: [EquivLike F X Y]
  公理与运算 (1 个):
    - edist_eq' : 对任意 f : F, 存在 r : 实数>=0, r != 0 ∧ 对任意 x y : X, edist (f x) (f y) = r * edist x y
-/
class DilationEquivClass [EquivLike F X Y] : Prop where
  edist_eq' : forall f : F, exists r : Real>=0, r != 0 ∧ forall x y : X, edist (f x) (f y) = r * edist x y

instance (priority := 100) [EquivLike F X Y] [DilationEquivClass F X Y] : DilationClass F X Y :=
  { (inferInstance : FunLike F X Y), ‹DilationEquivClass F X Y› with }

end Class

/--
Definition of `DilationEquiv` / `DilationEquiv` 的定义

English:
structure DilationEquiv
  parameters: (X Y : Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  extends: X ≃ Y, Dilation X Y
  (no additional axioms)

中文:
结构 DilationEquiv
  参数: (X Y : 类型) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  继承: X ≃ Y, Dilation X Y
  (无附加公理)
-/
structure DilationEquiv (X Y : Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    extends X ≃ Y, Dilation X Y

@[inherit_doc] infixl:25 " ≃ᵈ " => DilationEquiv

namespace DilationEquiv

section PseudoEMetricSpace

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (X ≃ᵈ Y) X Y
  body: f.1
  inv f := f.1.symm
  left_inv f := f.left_inv'
  right_inv f := f.right_inv'
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h -; congr; exact DFunLike.ext' h

中文:
实例 :
  签名: EquivLike (X ≃ᵈ Y) X Y
  定义体: f.1
  inv f := f.1.symm
  left_inv f := f.left_inv'
  right_inv f := f.right_inv'
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h -; congr; exact DFunLike.ext' h
-/
instance : EquivLike (X ≃ᵈ Y) X Y where
  coe f := f.1
  inv f := f.1.symm
  left_inv f := f.left_inv'
  right_inv f := f.right_inv'
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h -; congr; exact DFunLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DilationEquivClass (X ≃ᵈ Y) X Y
  body: f.edist_eq'

中文:
实例 :
  签名: DilationEquivClass (X ≃ᵈ Y) X Y
  定义体: f.edist_eq'

Depends on / 依赖: edist_eq, f.edist_eq
-/
instance : DilationEquivClass (X ≃ᵈ Y) X Y where
  edist_eq' f := f.edist_eq'

/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (e : X ≃ᵈ Y)
  statement: ⇑e.toEquiv = e
  proof: rfl

@[ext]

中文:
定理 coe_toEquiv
  条件: (e : X ≃ᵈ Y)
  结论: ⇑e.toEquiv = e
  证明: rfl

@[ext]
-/
@[simp] theorem coe_toEquiv (e : X ≃ᵈ Y) : ⇑e.toEquiv = e := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {e e' : X ≃ᵈ Y} (h : forall x, e x = e' x)
  statement: e = e'
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {e e' : X ≃ᵈ Y} (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: DFunLike.ext _ _ h
-/
protected theorem ext {e e' : X ≃ᵈ Y} (h : forall x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : X ≃ᵈ Y)
  body: e.1.symm
  edist_eq' := by
refine ⟨(ratio e)⁻¹, inv_ne_zero ratio_ne_zero e, e.surjective.forall₂.2 fun x y => ?_⟩
    simp_rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, edist_eq]
    rw [← mul_assoc]; rw [← ENNReal.coe_mul]; rw [inv_mul_cancel₀ (ratio_ne_zero e)]; rw [ENNReal.coe_one

中文:
定义 symm
  签名: (e : X ≃ᵈ Y)
  定义体: e.1.symm
  edist_eq' := by
refine ⟨(ratio e)⁻¹, inv_ne_zero ratio_ne_zero e, e.surjective.forall₂.2 fun x y => ?_⟩
    simp_rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, edist_eq]
    rw [← mul_assoc]; rw [← ENNReal.coe_mul]; rw [inv_mul_cancel₀ (ratio_ne_zero e)]; rw [ENNReal.coe_one
-/
def symm (e : X ≃ᵈ Y) : Y ≃ᵈ X where
  toEquiv := e.1.symm
  edist_eq' := by
refine ⟨(ratio e)⁻¹, inv_ne_zero ratio_ne_zero e, e.surjective.forall₂.2 fun x y => ?_⟩
    simp_rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, edist_eq]
    rw [← mul_assoc]; rw [← ENNReal.coe_mul]; rw [inv_mul_cancel₀ (ratio_ne_zero e)]; rw [ENNReal.coe_one]; rw [one_mul]

/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : X ≃ᵈ Y)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : X ≃ᵈ Y)
  结论: e.symm.symm = e
  证明: rfl
-/
@[simp] theorem symm_symm (e : X ≃ᵈ Y) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (DilationEquiv.symm : (X ≃ᵈ Y) -> Y ≃ᵈ X)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (DilationEquiv.symm : (X ≃ᵈ Y) -> Y ≃ᵈ X)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (DilationEquiv.symm : (X ≃ᵈ Y) -> Y ≃ᵈ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : X ≃ᵈ Y) (x : Y)
  statement: e (e.symm x) = x
  proof: e.right_inv x

中文:
定理 apply_symm_apply
  条件: (e : X ≃ᵈ Y) (x : Y)
  结论: e (e.symm x) = x
  证明: e.right_inv x
-/
@[simp] theorem apply_symm_apply (e : X ≃ᵈ Y) (x : Y) : e (e.symm x) = x := e.right_inv x
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : X ≃ᵈ Y) (x : X)
  statement: e.symm (e x) = x
  proof: e.left_inv x

中文:
定理 symm_apply_apply
  条件: (e : X ≃ᵈ Y) (x : X)
  结论: e.symm (e x) = x
  证明: e.left_inv x
-/
@[simp] theorem symm_apply_apply (e : X ≃ᵈ Y) (x : X) : e.symm (e x) = x := e.left_inv x

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : X ≃ᵈ Y) {x : X} {y : Y}
  statement: e.symm y = x ↔ y = e x
  proof: Equiv.symm_apply_eq _

中文:
定理 symm_apply_eq
  条件: (e : X ≃ᵈ Y) {x : X} {y : Y}
  结论: e.symm y = x ↔ y = e x
  证明: Equiv.symm_apply_eq _

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem symm_apply_eq (e : X ≃ᵈ Y) {x : X} {y : Y} : e.symm y = x ↔ y = e x :=
  Equiv.symm_apply_eq _

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : X ≃ᵈ Y) {x : X} {y : Y}
  statement: x = e.symm y ↔ e x = y
  proof: Equiv.eq_symm_apply _

中文:
定理 eq_symm_apply
  条件: (e : X ≃ᵈ Y) {x : X} {y : Y}
  结论: x = e.symm y ↔ e x = y
  证明: Equiv.eq_symm_apply _

Depends on / 依赖: Equiv.eq_symm_apply, eq_symm_apply
-/
theorem eq_symm_apply (e : X ≃ᵈ Y) {x : X} {y : Y} : x = e.symm y ↔ e x = y :=
  Equiv.eq_symm_apply _

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : X ≃ᵈ Y)
  body: e.symm

initialize_simps_projections DilationEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : X ≃ᵈ Y)
  定义体: e.symm

initialize_simps_projections DilationEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (e : X ≃ᵈ Y) : Y -> X := e.symm

initialize_simps_projections DilationEquiv (toFun -> apply, invFun -> symm_apply)

/--
lemma `ratio_toDilation` / 引理 `ratio_toDilation`

English:
lemma ratio_toDilation
  given: (e : X ≃ᵈ Y)
  statement: ratio e.toDilation = ratio e
  proof: rfl

中文:
引理 ratio_toDilation
  条件: (e : X ≃ᵈ Y)
  结论: ratio e.toDilation = ratio e
  证明: rfl
-/
lemma ratio_toDilation (e : X ≃ᵈ Y) : ratio e.toDilation = ratio e := rfl

/-- Identity map as a `DilationEquiv`. -/
@[simps! -fullyApplied apply]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (X : Type*) [PseudoEMetricSpace X]
  body: .refl X
  edist_eq' := ⟨1, one_ne_zero, fun _ _ => by simp⟩

中文:
定义 refl
  签名: (X : 类型) [PseudoEMetricSpace X]
  定义体: .refl X
  edist_eq' := ⟨1, one_ne_zero, fun _ _ => by simp⟩
-/
def refl (X : Type*) [PseudoEMetricSpace X] : X ≃ᵈ X where
  toEquiv := .refl X
  edist_eq' := ⟨1, one_ne_zero, fun _ _ => by simp⟩

/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (refl X).symm = refl X
  proof: rfl

中文:
定理 refl_symm
  结论: (refl X).symm = refl X
  证明: rfl
-/
@[simp] theorem refl_symm : (refl X).symm = refl X := rfl
/--
theorem `ratio_refl` / 定理 `ratio_refl`

English:
theorem ratio_refl
  statement: ratio (refl X) = 1
  proof: Dilation.ratio_id

中文:
定理 ratio_refl
  结论: ratio (refl X) = 1
  证明: Dilation.ratio_id
-/
@[simp] theorem ratio_refl : ratio (refl X) = 1 := Dilation.ratio_id

/-- Composition of `DilationEquiv`s. -/
@[simps! -fullyApplied apply]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z)
  body: e₁.1.trans e₂.1
  __ := e₂.toDilation.comp e₁.toDilation

中文:
定义 trans
  签名: (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z)
  定义体: e₁.1.trans e₂.1
  __ := e₂.toDilation.comp e₁.toDilation
-/
def trans (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z) : X ≃ᵈ Z where
  toEquiv := e₁.1.trans e₂.1
  __ := e₂.toDilation.comp e₁.toDilation

/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (e : X ≃ᵈ Y)
  statement: (refl X).trans e = e
  proof: rfl

中文:
定理 refl_trans
  条件: (e : X ≃ᵈ Y)
  结论: (refl X).trans e = e
  证明: rfl
-/
@[simp] theorem refl_trans (e : X ≃ᵈ Y) : (refl X).trans e = e := rfl
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (e : X ≃ᵈ Y)
  statement: e.trans (refl Y) = e
  proof: rfl

中文:
定理 trans_refl
  条件: (e : X ≃ᵈ Y)
  结论: e.trans (refl Y) = e
  证明: rfl
-/
@[simp] theorem trans_refl (e : X ≃ᵈ Y) : e.trans (refl Y) = e := rfl

/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : X ≃ᵈ Y)
  statement: e.symm.trans e = refl Y
  proof: DilationEquiv.ext e.apply_symm_apply

中文:
定理 symm_trans_self
  条件: (e : X ≃ᵈ Y)
  结论: e.symm.trans e = refl Y
  证明: DilationEquiv.ext e.apply_symm_apply
-/
@[simp] theorem symm_trans_self (e : X ≃ᵈ Y) : e.symm.trans e = refl Y :=
  DilationEquiv.ext e.apply_symm_apply

/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : X ≃ᵈ Y)
  statement: e.trans e.symm = refl X
  proof: DilationEquiv.ext e.symm_apply_apply

中文:
定理 self_trans_symm
  条件: (e : X ≃ᵈ Y)
  结论: e.trans e.symm = refl X
  证明: DilationEquiv.ext e.symm_apply_apply
-/
@[simp] theorem self_trans_symm (e : X ≃ᵈ Y) : e.trans e.symm = refl X :=
  DilationEquiv.ext e.symm_apply_apply

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : X ≃ᵈ Y)
  statement: Surjective e
  proof: e.1.surjective

中文:
定理 surjective
  条件: (e : X ≃ᵈ Y)
  结论: Surjective e
  证明: e.1.surjective
-/
protected theorem surjective (e : X ≃ᵈ Y) : Surjective e := e.1.surjective
/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : X ≃ᵈ Y)
  statement: Bijective e
  proof: e.1.bijective

中文:
定理 bijective
  条件: (e : X ≃ᵈ Y)
  结论: Bijective e
  证明: e.1.bijective
-/
protected theorem bijective (e : X ≃ᵈ Y) : Bijective e := e.1.bijective
/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : X ≃ᵈ Y)
  statement: Injective e
  proof: e.1.injective

@[simp]

中文:
定理 injective
  条件: (e : X ≃ᵈ Y)
  结论: Injective e
  证明: e.1.injective

@[simp]
-/
protected theorem injective (e : X ≃ᵈ Y) : Injective e := e.1.injective

@[simp]
/--
theorem `ratio_trans` / 定理 `ratio_trans`

English:
theorem ratio_trans
  given: (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z)
  statement: ratio (e.trans e') = ratio e * ratio e'
  proof: by
  -- If `X` is trivial, then so is `Y`, otherwise we apply `Dilation.ratio_comp'`
  by_cases! hX : forall x y : X, edist x y = 0 ∨ edist x y = ∞
  · have hY : forall x y : Y, edist x y = 0 ∨ edist x y = ∞ := e.surjective.forall₂.2 fun x y => by
      refine (hX x y).imp (fun h => ?_) fun h => ?_ 

中文:
定理 ratio_trans
  条件: (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z)
  结论: ratio (e.trans e') = ratio e * ratio e'
  证明: by
  -- If `X` is trivial, then so is `Y`, otherwise we apply `Dilation.ratio_comp'`
  by_cases! hX : forall x y : X, edist x y = 0 ∨ edist x y = ∞
  · have hY : forall x y : Y, edist x y = 0 ∨ edist x y = ∞ := e.surjective.forall₂.2 fun x y => by
      refine (hX x y).imp (fun h => ?_) fun h => ?_ 
-/
theorem ratio_trans (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z) : ratio (e.trans e') = ratio e * ratio e' := by
  -- If `X` is trivial, then so is `Y`, otherwise we apply `Dilation.ratio_comp'`
  by_cases! hX : forall x y : X, edist x y = 0 ∨ edist x y = ∞
  · have hY : forall x y : Y, edist x y = 0 ∨ edist x y = ∞ := e.surjective.forall₂.2 fun x y => by
      refine (hX x y).imp (fun h => ?_) fun h => ?_ <;> simp [*, Dilation.ratio_ne_zero]
    simp [Dilation.ratio_of_trivial, *]
  exact (Dilation.ratio_comp' (g := e'.toDilation) (f := e.toDilation) hX).trans (mul_comm _ _)

@[simp]
/--
theorem `ratio_symm` / 定理 `ratio_symm`

English:
theorem ratio_symm
  given: (e : X ≃ᵈ Y)
  statement: ratio e.symm = (ratio e)⁻¹
  proof: eq_inv_of_mul_eq_one_left by rw [← ratio_trans, symm_trans_self, ratio_refl]

中文:
定理 ratio_symm
  条件: (e : X ≃ᵈ Y)
  结论: ratio e.symm = (ratio e)⁻¹
  证明: eq_inv_of_mul_eq_one_left by rw [← ratio_trans, symm_trans_self, ratio_refl]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, ratio_refl, ratio_trans, symm_trans_self
-/
theorem ratio_symm (e : X ≃ᵈ Y) : ratio e.symm = (ratio e)⁻¹ :=
eq_inv_of_mul_eq_one_left by rw [← ratio_trans, symm_trans_self, ratio_refl]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (X ≃ᵈ X)
  body: e'.trans e
  mul_assoc _ _ _ := rfl
  one := refl _
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  inv_mul_cancel := self_trans_symm

中文:
实例 :
  签名: Group (X ≃ᵈ X)
  定义体: e'.trans e
  mul_assoc _ _ _ := rfl
  one := refl _
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  inv_mul_cancel := self_trans_symm
-/
instance : Group (X ≃ᵈ X) where
  mul e e' := e'.trans e
  mul_assoc _ _ _ := rfl
  one := refl _
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  inv_mul_cancel := self_trans_symm

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (e e' : X ≃ᵈ X)
  statement: e * e' = e'.trans e
  proof: rfl

中文:
定理 mul_def
  条件: (e e' : X ≃ᵈ X)
  结论: e * e' = e'.trans e
  证明: rfl
-/
theorem mul_def (e e' : X ≃ᵈ X) : e * e' = e'.trans e := rfl
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : X ≃ᵈ X) = refl X
  proof: rfl

中文:
定理 one_def
  结论: (1 : X ≃ᵈ X) = refl X
  证明: rfl
-/
theorem one_def : (1 : X ≃ᵈ X) = refl X := rfl
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (e : X ≃ᵈ X)
  statement: e⁻¹ = e.symm
  proof: rfl

中文:
定理 inv_def
  条件: (e : X ≃ᵈ X)
  结论: e⁻¹ = e.symm
  证明: rfl
-/
theorem inv_def (e : X ≃ᵈ X) : e⁻¹ = e.symm := rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (e e' : X ≃ᵈ X)
  statement: ⇑(e * e') = e ∘ e'
  proof: rfl

中文:
定理 coe_mul
  条件: (e e' : X ≃ᵈ X)
  结论: ⇑(e * e') = e ∘ e'
  证明: rfl
-/
@[simp] theorem coe_mul (e e' : X ≃ᵈ X) : ⇑(e * e') = e ∘ e' := rfl
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : X ≃ᵈ X) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : X ≃ᵈ X) = id
  证明: rfl
-/
@[simp] theorem coe_one : ⇑(1 : X ≃ᵈ X) = id := rfl
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (e : X ≃ᵈ X)
  statement: ⇑(e⁻¹) = e.symm
  proof: rfl

中文:
定理 coe_inv
  条件: (e : X ≃ᵈ X)
  结论: ⇑(e⁻¹) = e.symm
  证明: rfl
-/
theorem coe_inv (e : X ≃ᵈ X) : ⇑(e⁻¹) = e.symm := rfl

/--
Definition of `ratioHom` / `ratioHom` 的定义

English:
definition ratioHom
  signature: : (X ≃ᵈ X) ->* Real>=0 where
  body: Dilation.ratio
  map_one' := ratio_refl
  map_mul' _ _ := (ratio_trans _ _).trans (mul_comm _ _)

@[simp]

中文:
定义 ratioHom
  签名: : (X ≃ᵈ X) ->* 实数>=0 where
  定义体: Dilation.ratio
  map_one' := ratio_refl
  map_mul' _ _ := (ratio_trans _ _).trans (mul_comm _ _)

@[simp]

Depends on / 依赖: Dilation, Dilation.ratio
-/
noncomputable def ratioHom : (X ≃ᵈ X) ->* Real>=0 where
  toFun := Dilation.ratio
  map_one' := ratio_refl
  map_mul' _ _ := (ratio_trans _ _).trans (mul_comm _ _)

@[simp]
/--
theorem `ratio_inv` / 定理 `ratio_inv`

English:
theorem ratio_inv
  given: (e : X ≃ᵈ X)
  statement: ratio (e⁻¹) = (ratio e)⁻¹
  proof: ratio_symm e

@[simp]

中文:
定理 ratio_inv
  条件: (e : X ≃ᵈ X)
  结论: ratio (e⁻¹) = (ratio e)⁻¹
  证明: ratio_symm e

@[simp]

Depends on / 依赖: ratio_symm
-/
theorem ratio_inv (e : X ≃ᵈ X) : ratio (e⁻¹) = (ratio e)⁻¹ := ratio_symm e

@[simp]
/--
theorem `ratio_pow` / 定理 `ratio_pow`

English:
theorem ratio_pow
  given: (e : X ≃ᵈ X) (n : Nat)
  statement: ratio (e ^ n) = ratio e ^ n
  proof: ratioHom.map_pow _ _

@[simp]

中文:
定理 ratio_pow
  条件: (e : X ≃ᵈ X) (n : 自然数)
  结论: ratio (e ^ n) = ratio e ^ n
  证明: ratioHom.map_pow _ _

@[simp]

Depends on / 依赖: map_pow, ratioHom, ratioHom.map_pow
-/
theorem ratio_pow (e : X ≃ᵈ X) (n : Nat) : ratio (e ^ n) = ratio e ^ n :=
  ratioHom.map_pow _ _

@[simp]
/--
theorem `ratio_zpow` / 定理 `ratio_zpow`

English:
theorem ratio_zpow
  given: (e : X ≃ᵈ X) (n : Int)
  statement: ratio (e ^ n) = ratio e ^ n
  proof: ratioHom.map_zpow _ _

中文:
定理 ratio_zpow
  条件: (e : X ≃ᵈ X) (n : 整数)
  结论: ratio (e ^ n) = ratio e ^ n
  证明: ratioHom.map_zpow _ _

Depends on / 依赖: map_zpow, ratioHom, ratioHom.map_zpow
-/
theorem ratio_zpow (e : X ≃ᵈ X) (n : Int) : ratio (e ^ n) = ratio e ^ n :=
  ratioHom.map_zpow _ _

/-- `DilationEquiv.toEquiv` as a monoid homomorphism. -/
@[simps]
/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: : (X ≃ᵈ X) ->* Equiv.Perm X where
  body: e.1
  map_mul' _ _ := rfl
  map_one' := rfl

@[norm_cast]

中文:
定义 toPerm
  签名: : (X ≃ᵈ X) ->* Equiv.Perm X where
  定义体: e.1
  map_mul' _ _ := rfl
  map_one' := rfl

@[norm_cast]
-/
def toPerm : (X ≃ᵈ X) ->* Equiv.Perm X where
  toFun e := e.1
  map_mul' _ _ := rfl
  map_one' := rfl

@[norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (e : X ≃ᵈ X) (n : Nat)
  statement: ⇑(e ^ n) = e^[n]
  proof: by
  rw [← coe_toEquiv]; rw [← toPerm_apply]; rw [map_pow]; rw [Equiv.Perm.coe_pow]; rfl

中文:
定理 coe_pow
  条件: (e : X ≃ᵈ X) (n : 自然数)
  结论: ⇑(e ^ n) = e^[n]
  证明: by
  rw [← coe_toEquiv]; rw [← toPerm_apply]; rw [map_pow]; rw [Equiv.Perm.coe_pow]; rfl

Depends on / 依赖: Equiv.Perm.coe_pow, coe_pow, coe_toEquiv, map_pow, toPerm_apply
-/
theorem coe_pow (e : X ≃ᵈ X) (n : Nat) : ⇑(e ^ n) = e^[n] := by
  rw [← coe_toEquiv]; rw [← toPerm_apply]; rw [map_pow]; rw [Equiv.Perm.coe_pow]; rfl

-- TODO: Once `IsometryEquiv` follows the `*EquivClass` pattern, replace this with an instance
-- of `DilationEquivClass` assuming `IsometryEquivClass`.
/--
Definition of `_root_.IsometryEquiv.toDilationEquiv` / `_root_.IsometryEquiv.toDilationEquiv` 的定义

English:
definition _root_.IsometryEquiv.toDilationEquiv
  signature: (e : X ≃ᵢ Y)
  body: ⟨1, one_ne_zero, by simpa using! e.isometry⟩
  __ := e.toEquiv

@[simp]

中文:
定义 _root_.IsometryEquiv.toDilationEquiv
  签名: (e : X ≃ᵢ Y)
  定义体: ⟨1, one_ne_zero, by simpa using! e.isometry⟩
  __ := e.toEquiv

@[simp]

Depends on / 依赖: e.isometry, isometry, one_ne_zero
-/
def _root_.IsometryEquiv.toDilationEquiv (e : X ≃ᵢ Y) : X ≃ᵈ Y where
  edist_eq' := ⟨1, one_ne_zero, by simpa using! e.isometry⟩
  __ := e.toEquiv

@[simp]
/--
lemma `_root_.IsometryEquiv.toDilationEquiv_apply` / 引理 `_root_.IsometryEquiv.toDilationEquiv_apply`

English:
lemma _root_.IsometryEquiv.toDilationEquiv_apply
  given: (e : X ≃ᵢ Y) (x : X)
  proof: rfl

@[simp]

中文:
引理 _root_.IsometryEquiv.toDilationEquiv_apply
  条件: (e : X ≃ᵢ Y) (x : X)
  证明: rfl

@[simp]
-/
lemma _root_.IsometryEquiv.toDilationEquiv_apply (e : X ≃ᵢ Y) (x : X) :
    e.toDilationEquiv x = e x :=
  rfl

@[simp]
/--
lemma `_root_.IsometryEquiv.toDilationEquiv_symm` / 引理 `_root_.IsometryEquiv.toDilationEquiv_symm`

English:
lemma _root_.IsometryEquiv.toDilationEquiv_symm
  given: (e : X ≃ᵢ Y)
  proof: rfl

@[simp]

中文:
引理 _root_.IsometryEquiv.toDilationEquiv_symm
  条件: (e : X ≃ᵢ Y)
  证明: rfl

@[simp]
-/
lemma _root_.IsometryEquiv.toDilationEquiv_symm (e : X ≃ᵢ Y) :
    e.symm.toDilationEquiv = e.toDilationEquiv.symm :=
  rfl

@[simp]
/--
lemma `_root_.IsometryEquiv.coe_toDilationEquiv` / 引理 `_root_.IsometryEquiv.coe_toDilationEquiv`

English:
lemma _root_.IsometryEquiv.coe_toDilationEquiv
  given: (e : X ≃ᵢ Y)
  statement: ⇑e.toDilationEquiv = e
  proof: rfl

@[simp]

中文:
引理 _root_.IsometryEquiv.coe_toDilationEquiv
  条件: (e : X ≃ᵢ Y)
  结论: ⇑e.toDilationEquiv = e
  证明: rfl

@[simp]
-/
lemma _root_.IsometryEquiv.coe_toDilationEquiv (e : X ≃ᵢ Y) : ⇑e.toDilationEquiv = e :=
  rfl

@[simp]
/--
lemma `_root_.IsometryEquiv.coe_symm_toDilationEquiv` / 引理 `_root_.IsometryEquiv.coe_symm_toDilationEquiv`

English:
lemma _root_.IsometryEquiv.coe_symm_toDilationEquiv
  given: (e : X ≃ᵢ Y)
  proof: rfl

@[simp]

中文:
引理 _root_.IsometryEquiv.coe_symm_toDilationEquiv
  条件: (e : X ≃ᵢ Y)
  证明: rfl

@[simp]
-/
lemma _root_.IsometryEquiv.coe_symm_toDilationEquiv (e : X ≃ᵢ Y) :
    ⇑e.toDilationEquiv.symm = e.symm :=
  rfl

@[simp]
/--
lemma `_root_.IsometryEquiv.toDilationEquiv_toDilation` / 引理 `_root_.IsometryEquiv.toDilationEquiv_toDilation`

English:
lemma _root_.IsometryEquiv.toDilationEquiv_toDilation
  given: (e : X ≃ᵢ Y)
  proof: rfl

@[simp]

中文:
引理 _root_.IsometryEquiv.toDilationEquiv_toDilation
  条件: (e : X ≃ᵢ Y)
  证明: rfl

@[simp]
-/
lemma _root_.IsometryEquiv.toDilationEquiv_toDilation (e : X ≃ᵢ Y) :
    (e.toDilationEquiv.toDilation : X ->ᵈ Y) = e.isometry.toDilation :=
  rfl

@[simp]
/--
lemma `_root_.IsometryEquiv.toDilationEquiv_ratio` / 引理 `_root_.IsometryEquiv.toDilationEquiv_ratio`

English:
lemma _root_.IsometryEquiv.toDilationEquiv_ratio
  given: (e : X ≃ᵢ Y)
  statement: ratio e.toDilationEquiv = 1
  proof: by
  rw [← ratio_toDilation]; rw [IsometryEquiv.toDilationEquiv_toDilation]; rw [Isometry.toDilation_ratio]

中文:
引理 _root_.IsometryEquiv.toDilationEquiv_ratio
  条件: (e : X ≃ᵢ Y)
  结论: ratio e.toDilationEquiv = 1
  证明: by
  rw [← ratio_toDilation]; rw [IsometryEquiv.toDilationEquiv_toDilation]; rw [Isometry.toDilation_ratio]

Depends on / 依赖: Isometry, Isometry.toDilation_ratio, IsometryEquiv, IsometryEquiv.toDilationEquiv_toDilation, ratio_toDilation, toDilationEquiv_toDilation, toDilation_ratio
-/
lemma _root_.IsometryEquiv.toDilationEquiv_ratio (e : X ≃ᵢ Y) : ratio e.toDilationEquiv = 1 := by
  rw [← ratio_toDilation]; rw [IsometryEquiv.toDilationEquiv_toDilation]; rw [Isometry.toDilation_ratio]

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (e : X ≃ᵈ Y)
  body: Dilation.toContinuous e
  continuous_invFun := Dilation.toContinuous e.symm
  __ := e.toEquiv

@[simp]

中文:
定义 toHomeomorph
  签名: (e : X ≃ᵈ Y)
  定义体: Dilation.toContinuous e
  continuous_invFun := Dilation.toContinuous e.symm
  __ := e.toEquiv

@[simp]

Depends on / 依赖: Dilation, Dilation.toContinuous, toContinuous
-/
def toHomeomorph (e : X ≃ᵈ Y) : X ≃ₜ Y where
  continuous_toFun := Dilation.toContinuous e
  continuous_invFun := Dilation.toContinuous e.symm
  __ := e.toEquiv

@[simp]
/--
lemma `toHomeomorph_symm` / 引理 `toHomeomorph_symm`

English:
lemma toHomeomorph_symm
  given: (e : X ≃ᵈ Y)
  statement: e.symm.toHomeomorph = e.toHomeomorph.symm
  proof: rfl

@[simp]

中文:
引理 toHomeomorph_symm
  条件: (e : X ≃ᵈ Y)
  结论: e.symm.toHomeomorph = e.toHomeomorph.symm
  证明: rfl

@[simp]
-/
lemma toHomeomorph_symm (e : X ≃ᵈ Y) : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/--
lemma `coe_toHomeomorph` / 引理 `coe_toHomeomorph`

English:
lemma coe_toHomeomorph
  given: (e : X ≃ᵈ Y)
  statement: ⇑e.toHomeomorph = e
  proof: rfl

@[simp]

中文:
引理 coe_toHomeomorph
  条件: (e : X ≃ᵈ Y)
  结论: ⇑e.toHomeomorph = e
  证明: rfl

@[simp]
-/
lemma coe_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph = e :=
  rfl

@[simp]
/--
lemma `coe_symm_toHomeomorph` / 引理 `coe_symm_toHomeomorph`

English:
lemma coe_symm_toHomeomorph
  given: (e : X ≃ᵈ Y)
  statement: ⇑e.toHomeomorph.symm = e.symm
  proof: rfl

中文:
引理 coe_symm_toHomeomorph
  条件: (e : X ≃ᵈ Y)
  结论: ⇑e.toHomeomorph.symm = e.symm
  证明: rfl
-/
lemma coe_symm_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

end PseudoEMetricSpace

section PseudoMetricSpace

variable {X Y F : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable [EquivLike F X Y] [DilationEquivClass F X Y]

@[simp]
/--
lemma `map_cobounded` / 引理 `map_cobounded`

English:
lemma map_cobounded
  given: (e : F)
  statement: map e (cobounded X) = cobounded Y
  proof: by
  rw [← Dilation.comap_cobounded e]; rw [map_comap_of_surjective (EquivLike.surjective e)]

中文:
引理 map_cobounded
  条件: (e : F)
  结论: map e (cobounded X) = cobounded Y
  证明: by
  rw [← Dilation.comap_cobounded e]; rw [map_comap_of_surjective (EquivLike.surjective e)]

Depends on / 依赖: Dilation, Dilation.comap_cobounded, EquivLike, EquivLike.surjective, comap_cobounded, map_comap_of_surjective, surjective
-/
lemma map_cobounded (e : F) : map e (cobounded X) = cobounded Y := by
  rw [← Dilation.comap_cobounded e]; rw [map_comap_of_surjective (EquivLike.surjective e)]

end PseudoMetricSpace

end DilationEquiv
