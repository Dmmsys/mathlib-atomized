/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Kähler differential module under base change

## Main results
- `KaehlerDifferential.tensorKaehlerEquivBase`: `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.tensorKaehlerEquiv`: `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`:
  `Ω[Aₚ/Rₚ]` is the localization of `Ω[A/R]` at `p`.

-/

@[expose] public section

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

open TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local irreducible] KaehlerDifferential

namespace KaehlerDifferential

/-- (Implementation). `A`-action on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
/--
Definition of `mulActionBaseChange` / `mulActionBaseChange` 的定义

English:
abbreviation mulActionBaseChange
  signature: : MulAction A (S otimes[R] Ω[A⁄R])
  body: (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A

中文:
缩写 mulActionBaseChange
  签名: : 乘法作用 A (S otimes[R] Ω[A⁄R])
  定义体: (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A

Depends on / 依赖: TensorProduct, TensorProduct.comm, mulAction, toEquiv, toEquiv.mulAction
-/
abbrev mulActionBaseChange : MulAction A (S otimes[R] Ω[A⁄R]) :=
  (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A

attribute [local instance] mulActionBaseChange

@[simp]
/--
lemma `mulActionBaseChange_smul_tmul` / 引理 `mulActionBaseChange_smul_tmul`

English:
lemma mulActionBaseChange_smul_tmul
  given: (a : A) (s : S) (x : Ω[A⁄R])
  proof: rfl

@[local simp]

中文:
引理 mulActionBaseChange_smul_tmul
  条件: (a : A) (s : S) (x : Ω[A⁄R])
  证明: rfl

@[local simp]
-/
lemma mulActionBaseChange_smul_tmul (a : A) (s : S) (x : Ω[A⁄R]) :
    a • (s otimesₜ[R] x) = s otimesₜ (a • x) := rfl

@[local simp]
/--
lemma `mulActionBaseChange_smul_zero` / 引理 `mulActionBaseChange_smul_zero`

English:
lemma mulActionBaseChange_smul_zero
  given: (a : A)
  proof: by
  rw [← zero_tmul _ (0 : Ω[A⁄R]), mulActionBaseChange_smul_tmul, smul_zero]

@[local simp]

中文:
引理 mulActionBaseChange_smul_zero
  条件: (a : A)
  证明: by
  rw [← zero_tmul _ (0 : Ω[A⁄R]), mulActionBaseChange_smul_tmul, smul_zero]

@[local simp]

Depends on / 依赖: mulActionBaseChange_smul_tmul, smul_zero, zero_tmul
-/
lemma mulActionBaseChange_smul_zero (a : A) :
    a • (0 : S otimes[R] Ω[A⁄R]) = 0 := by
  rw [← zero_tmul _ (0 : Ω[A⁄R]), mulActionBaseChange_smul_tmul, smul_zero]

@[local simp]
/--
lemma `mulActionBaseChange_smul_add` / 引理 `mulActionBaseChange_smul_add`

English:
lemma mulActionBaseChange_smul_add
  given: (a : A) (x y : S otimes[R] Ω[A⁄R])
  proof: by
  change (TensorProduct.comm R S Ω[A⁄R]).symm (a • (TensorProduct.comm R S Ω[A⁄R]) (x + y)) = _
  rw [map_add]; rw [smul_add]; rw [map_add]
  rfl

中文:
引理 mulActionBaseChange_smul_add
  条件: (a : A) (x y : S otimes[R] Ω[A⁄R])
  证明: by
  change (TensorProduct.comm R S Ω[A⁄R]).symm (a • (TensorProduct.comm R S Ω[A⁄R]) (x + y)) = _
  rw [map_add]; rw [smul_add]; rw [map_add]
  rfl

Depends on / 依赖: TensorProduct, TensorProduct.comm, map_add, smul_add
-/
lemma mulActionBaseChange_smul_add (a : A) (x y : S otimes[R] Ω[A⁄R]) :
    a • (x + y) = a • x + a • y := by
  change (TensorProduct.comm R S Ω[A⁄R]).symm (a • (TensorProduct.comm R S Ω[A⁄R]) (x + y)) = _
  rw [map_add]; rw [smul_add]; rw [map_add]
  rfl

/-- (Implementation). `A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
/--
Definition of `moduleBaseChange` / `moduleBaseChange` 的定义

English:
abbreviation moduleBaseChange
  signature: :
  body: (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A
  add_smul r s x := by induction x <;> simp [add_smul, tmul_add, *, add_add_add_comm]
  zero_smul x := by induction x <;> simp [*]
  smul_zero := by simp
  smul_add := by simp

中文:
缩写 moduleBaseChange
  签名: :
  定义体: (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A
  add_smul r s x := by induction x <;> simp [add_smul, tmul_add, *, add_add_add_comm]
  zero_smul x := by induction x <;> simp [*]
  smul_zero := by simp
  smul_add := by simp

Depends on / 依赖: TensorProduct, TensorProduct.comm, mulAction, toEquiv, toEquiv.mulAction
-/
abbrev moduleBaseChange :
    Module A (S otimes[R] Ω[A⁄R]) where
  __ := (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A
  add_smul r s x := by induction x <;> simp [add_smul, tmul_add, *, add_add_add_comm]
  zero_smul x := by induction x <;> simp [*]
  smul_zero := by simp
  smul_add := by simp

attribute [local instance] moduleBaseChange

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R A (S otimes[R] Ω[A⁄R])
  body: by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x
  · simp only [smul_zero]
  · rw [mulActionBaseChange_smul_tmul, algebraMap_smul, tmul_smul]
  · simp only [smul_add, *]

中文:
实例 :
  签名: 标量塔 R A (S otimes[R] Ω[A⁄R])
  定义体: by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x
  · simp only [smul_zero]
  · rw [mulActionBaseChange_smul_tmul, algebraMap_smul, tmul_smul]
  · simp only [smul_add, *]

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_smul, algebraMap_smul, mulActionBaseChange_smul_tmul, of_algebraMap_smul, smul_add, smul_zero, tmul_smul
-/
instance : IsScalarTower R A (S otimes[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x
  · simp only [smul_zero]
  · rw [mulActionBaseChange_smul_tmul, algebraMap_smul, tmul_smul]
  · simp only [smul_add, *]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass S A (S otimes[R] Ω[A⁄R])
  body: by
    induction x
    · simp only [smul_zero]
    · rw [mulActionBaseChange_smul_tmul, smul_tmul', smul_tmul', mulActionBaseChange_smul_tmul]
    · simp only [smul_add, *]

中文:
实例 :
  签名: 标量交换类 S A (S otimes[R] Ω[A⁄R])
  定义体: by
    induction x
    · simp only [smul_zero]
    · rw [mulActionBaseChange_smul_tmul, smul_tmul', smul_tmul', mulActionBaseChange_smul_tmul]
    · simp only [smul_add, *]

Depends on / 依赖: mulActionBaseChange_smul_tmul, smul_add, smul_tmul, smul_zero
-/
instance : SMulCommClass S A (S otimes[R] Ω[A⁄R]) where
  smul_comm s a x := by
    induction x
    · simp only [smul_zero]
    · rw [mulActionBaseChange_smul_tmul, smul_tmul', smul_tmul', mulActionBaseChange_smul_tmul]
    · simp only [smul_add, *]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass A S (S otimes[R] Ω[A⁄R])
  body: by rw [← smul_comm]

中文:
实例 :
  签名: 标量交换类 A S (S otimes[R] Ω[A⁄R])
  定义体: by rw [← smul_comm]

Depends on / 依赖: smul_comm
-/
instance : SMulCommClass A S (S otimes[R] Ω[A⁄R]) where
  smul_comm s a x := by rw [← smul_comm]

/-- (Implementation). `B = S ⊗[R] A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
@[reducible] noncomputable
/--
Definition of `moduleBaseChange'` / `moduleBaseChange'` 的定义

English:
definition moduleBaseChange'
  signature: [Algebra.IsPushout R S A B]
  body: Module.compHom _ (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)).toRingHom

中文:
定义 moduleBaseChange'
  签名: [代数.是推出 R S A B]
  定义体: Module.compHom _ (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)).toRingHom

Depends on / 依赖: Algebra, Algebra.lsmul, Algebra.pushoutDesc, LinearMap, LinearMap.ext, Module, Module.compHom, compHom, otimes, pushoutDesc, smul_comm, toRingHom
-/
def moduleBaseChange' [Algebra.IsPushout R S A B] :
    Module B (S otimes[R] Ω[A⁄R]) :=
  Module.compHom _ (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)).toRingHom

attribute [local instance] moduleBaseChange'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsPushout
  signature: R S A B] :
  body: by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap A B r)) • x = r • x
  simp only [Algebra.pushoutDesc_right, Module.End.smul_def, Algebra.lsmul_coe]

中文:
实例 [代数.是推出
  签名: R S A B] :
  定义体: by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap A B r)) • x = r • x
  simp only [Algebra.pushoutDesc_right, Module.End.smul_def, Algebra.lsmul_coe]

Depends on / 依赖: Algebra, Algebra.lsmul, Algebra.lsmul_coe, Algebra.pushoutDesc, Algebra.pushoutDesc_right, IsScalarTower, IsScalarTower.of_algebraMap_smul, LinearMap, LinearMap.ext, Module, Module.End.smul_def, algebraMap, lsmul_coe, of_algebraMap_smul, otimes, pushoutDesc, pushoutDesc_right, smul_comm, smul_def
-/
instance [Algebra.IsPushout R S A B] :
    IsScalarTower A B (S otimes[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap A B r)) • x = r • x
  simp only [Algebra.pushoutDesc_right, Module.End.smul_def, Algebra.lsmul_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsPushout
  signature: R S A B] :
  body: by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap S B r)) • x = r • x
  simp only [Algebra.pushoutDesc_left, Module.End.smul_def, Algebra.lsmul_coe]

中文:
实例 [代数.是推出
  签名: R S A B] :
  定义体: by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap S B r)) • x = r • x
  simp only [Algebra.pushoutDesc_left, Module.End.smul_def, Algebra.lsmul_coe]

Depends on / 依赖: Algebra, Algebra.lsmul, Algebra.lsmul_coe, Algebra.pushoutDesc, Algebra.pushoutDesc_left, IsScalarTower, IsScalarTower.of_algebraMap_smul, LinearMap, LinearMap.ext, Module, Module.End.smul_def, algebraMap, lsmul_coe, of_algebraMap_smul, otimes, pushoutDesc, pushoutDesc_left, smul_comm, smul_def
-/
instance [Algebra.IsPushout R S A B] :
    IsScalarTower S B (S otimes[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S otimes[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap S B r)) • x = r • x
  simp only [Algebra.pushoutDesc_left, Module.End.smul_def, Algebra.lsmul_coe]

/--
lemma `map_liftBaseChange_smul` / 引理 `map_liftBaseChange_smul`

English:
lemma map_liftBaseChange_smul
  given: [h : Algebra.IsPushout R S A B] (b : B) (x)
  proof: by
  induction b using h.1.inductionOn with
  | zero => simp only [zero_smul, map_zero]
  | smul s b e => rw [smul_assoc, map_smul, e, smul_assoc]
  | add b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂, add_smul]
  | tmul a =>
    induction x
    · simp only [smul_zero, map_zero]
    · simp [smul_comm]
    · simp only [map_add, smul_add, *]

中文:
引理 map_liftBaseChange_smul
  条件: [h : 代数.是推出 R S A B] (b : B) (x)
  证明: by
  induction b using h.1.inductionOn with
  | zero => simp only [zero_smul, map_zero]
  | smul s b e => rw [smul_assoc, map_smul, e, smul_assoc]
  | add b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂, add_smul]
  | tmul a =>
    induction x
    · simp only [smul_zero, map_zero]
    · simp [smul_comm]
    · simp only [map_add, smul_add, *]

Depends on / 依赖: add_smul, inductionOn, map_add, map_smul, map_zero, smul_add, smul_assoc, smul_comm, smul_zero, zero_smul
-/
lemma map_liftBaseChange_smul [h : Algebra.IsPushout R S A B] (b : B) (x) :
    ((map R S A B).restrictScalars R).liftBaseChange S (b • x) =
    b • ((map R S A B).restrictScalars R).liftBaseChange S x := by
  induction b using h.1.inductionOn with
  | zero => simp only [zero_smul, map_zero]
  | smul s b e => rw [smul_assoc, map_smul, e, smul_assoc]
  | add b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂, add_smul]
  | tmul a =>
    induction x
    · simp only [smul_zero, map_zero]
    · simp [smul_comm]
    · simp only [map_add, smul_add, *]

/-- (Implementation).
The `S`-derivation `B = S ⊗[R] A` to `S ⊗[R] Ω[A⁄R]` sending `a ⊗ b` to `a ⊗ d b`. -/
noncomputable
/--
Definition of `derivationTensorProduct` / `derivationTensorProduct` 的定义

English:
definition derivationTensorProduct
  signature: [h : Algebra.IsPushout R S A B]
  body: h.out.lift ((TensorProduct.mk R S Ω[A⁄R] 1).comp (D R A).toLinearMap)
  map_one_eq_zero' := by
    rw [← (algebraMap A B).map_one]
    refine (h.out.lift_eq _ _).trans ?_
    dsimp
    rw [Derivation.map_one_eq_zero]; rw [TensorProduct.tmul_zero]
  leibniz' a b := by
    induction a using h.out.inductionOn with
    | zero => rw [map_zero, zero_smul, smul_zero, zero_add, zero_mul, map_zero]
    | smul x y e =>
      rw [smul_mul_assoc]; rw [map_smul]; rw [e]; rw [map_smul]; rw [smul_add]; rw [smul_comm x b]; rw [smul_assoc]
    | add b₁ b₂ e₁ e₂ => simp only [add_mul, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
    | tmul z =>
      dsimp
      induction b using h.out.inductionOn with
      | zero => rw [map_zero, zero_smul, smul_zero, zero_add, mul_zero, map_zero]
      | tmul =>
        simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          algebraMap_smul, ← map_mul]
        rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]; rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]; rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]
        simp only [LinearMap.coe_comp, Derivation.coeFn_coe, Function.comp_apply,
          Derivation.leibniz, mk_apply, mulActionBaseChange_smul_tmul, TensorProduct.tmul_add]
      | smul _ _ e =>
        rw [mul_comm]; rw [smul_mul_assoc]; rw [map_smul]; rw [mul_comm]; rw [e]; rw [map_smul]; rw [smul_add]; rw [smul_comm]; rw [smul_assoc]
      | add _ _ e₁ e₂ => simp only [mul_add, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]

中文:
定义 derivationTensorProduct
  签名: [h : 代数.是推出 R S A B]
  定义体: h.out.lift ((TensorProduct.mk R S Ω[A⁄R] 1).comp (D R A).toLinearMap)
  map_one_eq_zero' := by
    rw [← (algebraMap A B).map_one]
    refine (h.out.lift_eq _ _).trans ?_
    dsimp
    rw [Derivation.map_one_eq_zero]; rw [TensorProduct.tmul_zero]
  leibniz' a b := by
    induction a using h.out.inductionOn with
    | zero => rw [map_zero, zero_smul, smul_zero, zero_add, zero_mul, map_zero]
    | smul x y e =>
      rw [smul_mul_assoc]; rw [map_smul]; rw [e]; rw [map_smul]; rw [smul_add]; rw [smul_comm x b]; rw [smul_assoc]
    | add b₁ b₂ e₁ e₂ => simp only [add_mul, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
    | tmul z =>
      dsimp
      induction b using h.out.inductionOn with
      | zero => rw [map_zero, zero_smul, smul_zero, zero_add, mul_zero, map_zero]
      | tmul =>
        simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          algebraMap_smul, ← map_mul]
        rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]; rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]; rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]
        simp only [LinearMap.coe_comp, Derivation.coeFn_coe, Function.comp_apply,
          Derivation.leibniz, mk_apply, mulActionBaseChange_smul_tmul, TensorProduct.tmul_add]
      | smul _ _ e =>
        rw [mul_comm]; rw [smul_mul_assoc]; rw [map_smul]; rw [mul_comm]; rw [e]; rw [map_smul]; rw [smul_add]; rw [smul_comm]; rw [smul_assoc]
      | add _ _ e₁ e₂ => simp only [mul_add, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]

Depends on / 依赖: TensorProduct, TensorProduct.mk, h.out.lift, toLinearMap
-/
def derivationTensorProduct [h : Algebra.IsPushout R S A B] :
    Derivation S B (S otimes[R] Ω[A⁄R]) where
  __ := h.out.lift ((TensorProduct.mk R S Ω[A⁄R] 1).comp (D R A).toLinearMap)
  map_one_eq_zero' := by
    rw [← (algebraMap A B).map_one]
    refine (h.out.lift_eq _ _).trans ?_
    dsimp
    rw [Derivation.map_one_eq_zero]; rw [TensorProduct.tmul_zero]
  leibniz' a b := by
    induction a using h.out.inductionOn with
    | zero => rw [map_zero, zero_smul, smul_zero, zero_add, zero_mul, map_zero]
    | smul x y e =>
      rw [smul_mul_assoc]; rw [map_smul]; rw [e]; rw [map_smul]; rw [smul_add]; rw [smul_comm x b]; rw [smul_assoc]
    | add b₁ b₂ e₁ e₂ => simp only [add_mul, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
    | tmul z =>
      dsimp
      induction b using h.out.inductionOn with
      | zero => rw [map_zero, zero_smul, smul_zero, zero_add, mul_zero, map_zero]
      | tmul =>
        simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          algebraMap_smul, ← map_mul]
        rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]; rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]; rw [← IsScalarTower.toAlgHom_apply R]; rw [← AlgHom.toLinearMap_apply]; rw [h.out.lift_eq]
        simp only [LinearMap.coe_comp, Derivation.coeFn_coe, Function.comp_apply,
          Derivation.leibniz, mk_apply, mulActionBaseChange_smul_tmul, TensorProduct.tmul_add]
      | smul _ _ e =>
        rw [mul_comm]; rw [smul_mul_assoc]; rw [map_smul]; rw [mul_comm]; rw [e]; rw [map_smul]; rw [smul_add]; rw [smul_comm]; rw [smul_assoc]
      | add _ _ e₁ e₂ => simp only [mul_add, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]

/--
lemma `derivationTensorProduct_algebraMap` / 引理 `derivationTensorProduct_algebraMap`

English:
lemma derivationTensorProduct_algebraMap
  given: [Algebra.IsPushout R S A B] (x)
  proof: IsBaseChange.lift_eq _ _ _

中文:
引理 derivationTensorProduct_algebraMap
  条件: [代数.是推出 R S A B] (x)
  证明: IsBaseChange.lift_eq _ _ _

Depends on / 依赖: IsBaseChange, IsBaseChange.lift_eq, lift_eq
-/
lemma derivationTensorProduct_algebraMap [Algebra.IsPushout R S A B] (x) :
    derivationTensorProduct R S A B (algebraMap A B x) =
    1 otimesₜ D _ _ x :=
IsBaseChange.lift_eq _ _ _

/--
lemma `tensorKaehlerEquiv_left_inv` / 引理 `tensorKaehlerEquiv_left_inv`

English:
lemma tensorKaehlerEquiv_left_inv
  given: [Algebra.IsPushout R S A B]
  proof: by
  refine LinearMap.restrictScalars_injective R ?_
  apply TensorProduct.ext'
  intro x y
  obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
  induction y
  · simp only [map_zero, TensorProduct.tmul_zero]
  · simp only [LinearMap.restrictScalars_comp, Derivation.tensorProductTo_tmul, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.liftBaseChange_tmul, map_smul,
      map_D, LinearMap.map_smul_of_tower, Derivation.liftKaehlerDifferential_comp_D,
      LinearMap.id_coe, id_eq, derivationTensorProduct_algebraMap]
    rw [smul_comm]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
    rfl
  · simp only [map_add, TensorProduct.tmul_add, *]

中文:
引理 tensorKaehlerEquiv_left_inv
  条件: [代数.是推出 R S A B]
  证明: by
  refine LinearMap.restrictScalars_injective R ?_
  apply TensorProduct.ext'
  intro x y
  obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
  induction y
  · simp only [map_zero, TensorProduct.tmul_zero]
  · simp only [LinearMap.restrictScalars_comp, Derivation.tensorProductTo_tmul, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.liftBaseChange_tmul, map_smul,
      map_D, LinearMap.map_smul_of_tower, Derivation.liftKaehlerDifferential_comp_D,
      LinearMap.id_coe, id_eq, derivationTensorProduct_algebraMap]
    rw [smul_comm]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
    rfl
  · simp only [map_add, TensorProduct.tmul_add, *]

Depends on / 依赖: Derivation, Derivation.liftKaehlerDifferential_comp_D, Derivation.tensorProductTo_tmul, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.id_coe, LinearMap.liftBaseChange_tmul, LinearMap.map_smul_of_tower, LinearMap.restrictScalars_comp, LinearMap.restrictScalars_injective, TensorProduct, TensorProduct.ext, TensorProduct.tmul_zero, coe_comp, coe_restrictScalars, comp_apply, derivat
-/
lemma tensorKaehlerEquiv_left_inv [Algebra.IsPushout R S A B] :
    ((derivationTensorProduct R S A B).liftKaehlerDifferential.restrictScalars S).comp
    (((map R S A B).restrictScalars R).liftBaseChange S) = LinearMap.id := by
  refine LinearMap.restrictScalars_injective R ?_
  apply TensorProduct.ext'
  intro x y
  obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
  induction y
  · simp only [map_zero, TensorProduct.tmul_zero]
  · simp only [LinearMap.restrictScalars_comp, Derivation.tensorProductTo_tmul, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.liftBaseChange_tmul, map_smul,
      map_D, LinearMap.map_smul_of_tower, Derivation.liftKaehlerDifferential_comp_D,
      LinearMap.id_coe, id_eq, derivationTensorProduct_algebraMap]
    rw [smul_comm]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
    rfl
  · simp only [map_add, TensorProduct.tmul_add, *]

/-- The canonical isomorphism `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquiv` for the version with `B ⊗[A] Ω[A⁄R]`. -/
@[simps! symm_apply] noncomputable
/--
Definition of `tensorKaehlerEquivBase` / `tensorKaehlerEquivBase` 的定义

English:
definition tensorKaehlerEquivBase
  signature: [h : Algebra.IsPushout R S A B]
  body: ((map R S A B).restrictScalars R).liftBaseChange S
  invFun := (derivationTensorProduct R S A B).liftKaehlerDifferential
  left_inv := LinearMap.congr_fun (tensorKaehlerEquiv_left_inv R S A B)
  right_inv x := by
    obtain ⟨x, rfl⟩ := tensorProductTo_surjective _ _ x
    dsimp
    induction x with
    | zero => simp
    | add x y e₁ e₂ => simp only [map_add, e₁, e₂]
    | tmul x y =>
      -- We use the specialized version of `map_smul` here for performance.
      simp only [Derivation.tensorProductTo_tmul, LinearMap.map_smul,
        Derivation.liftKaehlerDifferential_comp_D, map_liftBaseChange_smul]
      induction y using h.1.inductionOn
      · simp only [map_zero, smul_zero]
      · simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          derivationTensorProduct_algebraMap, LinearMap.liftBaseChange_tmul,
          LinearMap.coe_restrictScalars, map_D, one_smul]
      · -- We use the specialized version of `map_smul` here for performance.
        simp only [Derivation.map_smul, LinearMap.map_smul, *, smul_comm x]
      · simp only [map_add, smul_add, *]

@[simp]

中文:
定义 tensorKaehlerEquivBase
  签名: [h : 代数.是推出 R S A B]
  定义体: ((map R S A B).restrictScalars R).liftBaseChange S
  invFun := (derivationTensorProduct R S A B).liftKaehlerDifferential
  left_inv := LinearMap.congr_fun (tensorKaehlerEquiv_left_inv R S A B)
  right_inv x := by
    obtain ⟨x, rfl⟩ := tensorProductTo_surjective _ _ x
    dsimp
    induction x with
    | zero => simp
    | add x y e₁ e₂ => simp only [map_add, e₁, e₂]
    | tmul x y =>
      -- We use the specialized version of `map_smul` here for performance.
      simp only [Derivation.tensorProductTo_tmul, LinearMap.map_smul,
        Derivation.liftKaehlerDifferential_comp_D, map_liftBaseChange_smul]
      induction y using h.1.inductionOn
      · simp only [map_zero, smul_zero]
      · simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          derivationTensorProduct_algebraMap, LinearMap.liftBaseChange_tmul,
          LinearMap.coe_restrictScalars, map_D, one_smul]
      · -- We use the specialized version of `map_smul` here for performance.
        simp only [Derivation.map_smul, LinearMap.map_smul, *, smul_comm x]
      · simp only [map_add, smul_add, *]

@[simp]

Depends on / 依赖: liftBaseChange, restrictScalars
-/
def tensorKaehlerEquivBase [h : Algebra.IsPushout R S A B] :
    (S otimes[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S] where
  __ := ((map R S A B).restrictScalars R).liftBaseChange S
  invFun := (derivationTensorProduct R S A B).liftKaehlerDifferential
  left_inv := LinearMap.congr_fun (tensorKaehlerEquiv_left_inv R S A B)
  right_inv x := by
    obtain ⟨x, rfl⟩ := tensorProductTo_surjective _ _ x
    dsimp
    induction x with
    | zero => simp
    | add x y e₁ e₂ => simp only [map_add, e₁, e₂]
    | tmul x y =>
      -- We use the specialized version of `map_smul` here for performance.
      simp only [Derivation.tensorProductTo_tmul, LinearMap.map_smul,
        Derivation.liftKaehlerDifferential_comp_D, map_liftBaseChange_smul]
      induction y using h.1.inductionOn
      · simp only [map_zero, smul_zero]
      · simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          derivationTensorProduct_algebraMap, LinearMap.liftBaseChange_tmul,
          LinearMap.coe_restrictScalars, map_D, one_smul]
      · -- We use the specialized version of `map_smul` here for performance.
        simp only [Derivation.map_smul, LinearMap.map_smul, *, smul_comm x]
      · simp only [map_add, smul_add, *]

@[simp]
/--
lemma `tensorKaehlerEquivBase_tmul` / 引理 `tensorKaehlerEquivBase_tmul`

English:
lemma tensorKaehlerEquivBase_tmul
  given: [Algebra.IsPushout R S A B] (a b)
  proof: LinearMap.liftBaseChange_tmul _ _ _ _

@[deprecated (since := "2026-01-01")] alias tensorKaehlerEquiv_tmul := tensorKaehlerEquivBase_tmul

中文:
引理 tensorKaehlerEquivBase_tmul
  条件: [代数.是推出 R S A B] (a b)
  证明: LinearMap.liftBaseChange_tmul _ _ _ _

@[deprecated (since := "2026-01-01")] alias tensorKaehlerEquiv_tmul := tensorKaehlerEquivBase_tmul

Depends on / 依赖: LinearMap, LinearMap.liftBaseChange_tmul, liftBaseChange_tmul
-/
lemma tensorKaehlerEquivBase_tmul [Algebra.IsPushout R S A B] (a b) :
    tensorKaehlerEquivBase R S A B (a otimesₜ b) = a • map R S A B b :=
  LinearMap.liftBaseChange_tmul _ _ _ _

@[deprecated (since := "2026-01-01")] alias tensorKaehlerEquiv_tmul := tensorKaehlerEquivBase_tmul

/--
lemma `isBaseChange` / 引理 `isBaseChange`

English:
lemma isBaseChange
  given: [h : Algebra.IsPushout R S A B]
  proof: by
  convert!
    (TensorProduct.isBaseChange R Ω[A⁄R] S).comp
      (IsBaseChange.ofEquiv (tensorKaehlerEquivBase R S A B))
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, mk_apply, tensorKaehlerEquivBase_tmul, one_smul]

中文:
引理 isBaseChange
  条件: [h : 代数.是推出 R S A B]
  证明: by
  convert!
    (TensorProduct.isBaseChange R Ω[A⁄R] S).comp
      (IsBaseChange.ofEquiv (tensorKaehlerEquivBase R S A B))
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, mk_apply, tensorKaehlerEquivBase_tmul, one_smul]

Depends on / 依赖: Function, Function.comp_apply, IsBaseChange, IsBaseChange.ofEquiv, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.ext, TensorProduct, TensorProduct.isBaseChange, coe_coe, coe_comp, coe_restrictScalars, comp_apply, convert, isBaseChange, mk_apply, ofEquiv
-/
lemma isBaseChange [h : Algebra.IsPushout R S A B] :
    IsBaseChange S ((map R S A B).restrictScalars R) := by
  convert!
    (TensorProduct.isBaseChange R Ω[A⁄R] S).comp
      (IsBaseChange.ofEquiv (tensorKaehlerEquivBase R S A B))
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, mk_apply, tensorKaehlerEquivBase_tmul, one_smul]

/--
Instance `isLocalizedModule` / 实例 `isLocalizedModule`

English:
instance isLocalizedModule
  signature: (p : Submonoid R) [IsLocalization p S]
  body: have := (Algebra.isPushout_of_isLocalization p S A B).symm
  (isLocalizedModule_iff_isBaseChange p S _).mpr (isBaseChange R S A B)

中文:
实例 isLocalizedModule
  签名: (p : 子幺半群 R) [是Localization p S]
  定义体: have := (Algebra.isPushout_of_isLocalization p S A B).symm
  (isLocalizedModule_iff_isBaseChange p S _).mpr (isBaseChange R S A B)

Depends on / 依赖: Algebra, Algebra.isPushout_of_isLocalization, isBaseChange, isLocalizedModule_iff_isBaseChange, isPushout_of_isLocalization
-/
instance isLocalizedModule (p : Submonoid R) [IsLocalization p S]
      [IsLocalization (Algebra.algebraMapSubmonoid A p) B] :
    IsLocalizedModule p ((map R S A B).restrictScalars R) :=
  have := (Algebra.isPushout_of_isLocalization p S A B).symm
  (isLocalizedModule_iff_isBaseChange p S _).mpr (isBaseChange R S A B)

/--
Instance `isLocalizedModule_of_isLocalizedModule` / 实例 `isLocalizedModule_of_isLocalizedModule`

English:
instance isLocalizedModule_of_isLocalizedModule
  signature: (p : Submonoid R) [IsLocalization p S]
  body: have : IsLocalization (Algebra.algebraMapSubmonoid A p) B :=
    isLocalizedModule_iff_isLocalization.mp inferInstance
  inferInstance

中文:
实例 isLocalizedModule_of_isLocalizedModule
  签名: (p : 子幺半群 R) [是Localization p S]
  定义体: have : IsLocalization (Algebra.algebraMapSubmonoid A p) B :=
    isLocalizedModule_iff_isLocalization.mp inferInstance
  inferInstance

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, IsLocalization, algebraMapSubmonoid, isLocalizedModule_iff_isLocalization, isLocalizedModule_iff_isLocalization.mp
-/
instance isLocalizedModule_of_isLocalizedModule (p : Submonoid R) [IsLocalization p S]
      [IsLocalizedModule p (IsScalarTower.toAlgHom R A B).toLinearMap] :
    IsLocalizedModule p ((map R S A B).restrictScalars R) :=
  have : IsLocalization (Algebra.algebraMapSubmonoid A p) B :=
    isLocalizedModule_iff_isLocalization.mp inferInstance
  inferInstance

/-- The canonical isomorphism `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquivBase` for the version with `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
/--
Definition of `tensorKaehlerEquiv` / `tensorKaehlerEquiv` 的定义

English:
definition tensorKaehlerEquiv
  signature: [h : Algebra.IsPushout R S A B]
  body: by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B otimes[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] otimes[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv (.refl _ _)
      ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B otimes[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquivBase R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *]
  | tmul x y =>
  obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
  | tmul x z =>
  suffices b • z • a • x • KaehlerDifferential.map R S A B y =
      (algebraMap A B a * algebraMap S B b) • z • x • KaehlerDifferential.map R S A B y by
    simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
      Algebra.IsPushout.equiv_symm_algebraMap_left, Algebra.IsPushout.equiv_symm_algebraMap_right]
  simp only [← mul_smul, ← @algebraMap_smul S _ B, ← @algebraMap_smul A _ B]
  ring_nf

@[simp]

中文:
定义 tensorKaehlerEquiv
  签名: [h : 代数.是推出 R S A B]
  定义体: by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B otimes[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] otimes[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv (.refl _ _)
      ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B otimes[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquivBase R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *]
  | tmul x y =>
  obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
  | tmul x z =>
  suffices b • z • a • x • KaehlerDifferential.map R S A B y =
      (algebraMap A B a * algebraMap S B b) • z • x • KaehlerDifferential.map R S A B y by
    simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
      Algebra.IsPushout.equiv_symm_algebraMap_left, Algebra.IsPushout.equiv_symm_algebraMap_right]
  simp only [← mul_smul, ← @algebraMap_smul S _ B, ← @algebraMap_smul A _ B]
  ring_nf

@[simp]

Depends on / 依赖: Algebra, Algebra.IsPushout, Algebra.IsPushout.equiv, AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AlgebraTensorModule.congr, IsPushout, KaehlerDifferential, KaehlerDifferential.tensorKaehlerEquivBase, TensorProduct, _root_, _root_.TensorProduct.comm, cancelBaseChange, map_smul, otimes, restrictScalars, symm.toLinearEquiv, tensorKaehlerEquivBase, toLinearEquiv
-/
def tensorKaehlerEquiv [h : Algebra.IsPushout R S A B] :
    B otimes[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B otimes[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] otimes[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv (.refl _ _)
      ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B otimes[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquivBase R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *]
  | tmul x y =>
  obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
  | tmul x z =>
  suffices b • z • a • x • KaehlerDifferential.map R S A B y =
      (algebraMap A B a * algebraMap S B b) • z • x • KaehlerDifferential.map R S A B y by
    simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
      Algebra.IsPushout.equiv_symm_algebraMap_left, Algebra.IsPushout.equiv_symm_algebraMap_right]
  simp only [← mul_smul, ← @algebraMap_smul S _ B, ← @algebraMap_smul A _ B]
  ring_nf

@[simp]
/--
lemma `tensorKaehlerEquiv_tmul_D` / 引理 `tensorKaehlerEquiv_tmul_D`

English:
lemma tensorKaehlerEquiv_tmul_D
  given: [Algebra.IsPushout R S A B] (b a)
  proof: by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
  trans s • a' • D S B (algebraMap A B a)
  · simp [tensorKaehlerEquiv]
  · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

中文:
引理 tensorKaehlerEquiv_tmul_D
  条件: [代数.是推出 R S A B] (b a)
  证明: by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
  trans s • a' • D S B (algebraMap A B a)
  · simp [tensorKaehlerEquiv]
  · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

Depends on / 依赖: Algebra, Algebra.IsPushout, Algebra.IsPushout.equiv, Algebra.IsPushout.equiv_tmul, IsPushout, add_smul, add_tmul, algebraMap, equiv_tmul, map_add, mul_smul, smul_comm, surjective, tensorKaehlerEquiv
-/
lemma tensorKaehlerEquiv_tmul_D [Algebra.IsPushout R S A B] (b a) :
    tensorKaehlerEquiv R S A B (b otimesₜ D _ _ a) = b • D S B (algebraMap A B a) := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
  trans s • a' • D S B (algebraMap A B a)
  · simp [tensorKaehlerEquiv]
  · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `tensorKaehlerEquiv_symm_D_tmul` / 引理 `tensorKaehlerEquiv_symm_D_tmul`

English:
lemma tensorKaehlerEquiv_symm_D_tmul
  given: (s a)
  proof: by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [show s otimesₜ 1 = algebraMap S (S otimes A) s by simp]; rw [Algebra.TensorProduct.right_algebraMap_apply]; rw [algebraMap_smul]; rw [← Derivation.map_smul]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

中文:
引理 tensorKaehlerEquiv_symm_D_tmul
  条件: (s a)
  证明: by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [show s otimesₜ 1 = algebraMap S (S otimes A) s by simp]; rw [Algebra.TensorProduct.right_algebraMap_apply]; rw [algebraMap_smul]; rw [← Derivation.map_smul]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply, Algebra.algebraMap_self, Derivation, Derivation.map_smul, RingHom, RingHom.id_apply, TensorProduct, algebraMap, algebraMap_apply, algebraMap_self, algebraMap_smul, id_apply, map_smul, mul_one, otimes, right_algebraMap_apply, smul_eq_mul, smul_tmul
-/
lemma tensorKaehlerEquiv_symm_D_tmul (s a) :
    (tensorKaehlerEquiv R S A (S otimes[R] A)).symm (D _ _ (s otimesₜ a)) = algebraMap _ _ s otimesₜ D _ _ a := by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [show s otimesₜ 1 = algebraMap S (S otimes A) s by simp]; rw [Algebra.TensorProduct.right_algebraMap_apply]; rw [algebraMap_smul]; rw [← Derivation.map_smul]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `tensorKaehlerEquiv_symm_D_tmul'` / 引理 `tensorKaehlerEquiv_symm_D_tmul'`

English:
lemma tensorKaehlerEquiv_symm_D_tmul'
  given: (s a)
  proof: by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [algebraMap_smul]; rw [← Derivation.map_smul]; rw [Algebra.smul_def]; rw [Algebra.TensorProduct.right_algebraMap_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

中文:
引理 tensorKaehlerEquiv_symm_D_tmul'
  条件: (s a)
  证明: by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [algebraMap_smul]; rw [← Derivation.map_smul]; rw [Algebra.smul_def]; rw [Algebra.TensorProduct.right_algebraMap_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

Depends on / 依赖: Algebra, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_self, Algebra.smul_def, Derivation, Derivation.map_smul, RingHom, RingHom.id_apply, TensorProduct, algebraMap_apply, algebraMap_self, algebraMap_smul, id_apply, map_smul, mul_one, one_mul, right_algebraMap_apply, smul_def
-/
lemma tensorKaehlerEquiv_symm_D_tmul' (s a) :
    (tensorKaehlerEquiv R S A (A otimes[R] S)).symm (D _ _ (a otimesₜ s)) = algebraMap _ _ s otimesₜ D _ _ a := by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [algebraMap_smul]; rw [← Derivation.map_smul]; rw [Algebra.smul_def]; rw [Algebra.TensorProduct.right_algebraMap_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end KaehlerDifferential
