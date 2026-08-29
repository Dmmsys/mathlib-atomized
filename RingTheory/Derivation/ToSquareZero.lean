/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Derivations into Square-Zero Ideals

## Main statements

- `derivationToSquareZeroOfLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

-/

@[expose] public section


section ToSquareZero

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [CommRing B]
variable [Algebra R A] [Algebra R B] (I : Ideal B)

/--
Definition of `diffToIdealOfQuotientCompEq` / `diffToIdealOfQuotientCompEq` 的定义

English:
definition diffToIdealOfQuotientCompEq
  signature: (f₁ f₂ : A ->ₐ[R] B)
  body: LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap)
    (fun x => by simpa [Ideal.Quotient.eq] using congr($e x))

@[simp]

中文:
定义 diffToIdealOfQuotientCompEq
  签名: (f₁ f₂ : A ->ₐ[R] B)
  定义体: LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap)
    (fun x => by simpa [Ideal.Quotient.eq] using congr($e x))

@[simp]

Depends on / 依赖: I.restrictScalars, Ideal.Quotient.eq, LinearMap, LinearMap.codRestrict, Quotient, codRestrict, restrictScalars, toLinearMap
-/
def diffToIdealOfQuotientCompEq (f₁ f₂ : A ->ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) : A ->ₗ[R] I :=
  LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap)
    (fun x => by simpa [Ideal.Quotient.eq] using congr($e x))

@[simp]
/--
theorem `diffToIdealOfQuotientCompEq_apply` / 定理 `diffToIdealOfQuotientCompEq_apply`

English:
theorem diffToIdealOfQuotientCompEq_apply
  statement: (f₁ f₂ : A ->ₐ[R] B)
  proof: rfl

中文:
定理 diffToIdealOfQuotientCompEq_apply
  结论: (f₁ f₂ : A ->ₐ[R] B)
  证明: rfl
-/
theorem diffToIdealOfQuotientCompEq_apply (f₁ f₂ : A ->ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) (x : A) :
    ((diffToIdealOfQuotientCompEq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
  rfl

variable [Algebra A B]

/--
Definition of `derivationToSquareZeroOfLift` / `derivationToSquareZeroOfLift` 的定义

English:
definition derivationToSquareZeroOfLift
  signature: [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : A ->ₐ[R] B)
  body: by
  refine
    { diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) ?_ with
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · ext; simp [e]
  · ext; simp
  · intro x y
    let F := diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (by rw [e]; ext; rfl)
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 := by
      rw [← Ideal.mem_bot]; rw [← hI]; rw [pow_two]
      convert! Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk,
      diffToIdealOfQuotientCompEq_apply, Submodule.coe_smul_of_tower, IsScalarTower.coe_toAlgHom',
      LinearMap.toFun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this ⊢
    rw [sub_eq_iff_eq_add]; rw [sub_eq_iff_eq_add] at this
    simp only [this]
    ring

中文:
定义 derivationToSquareZeroOfLift
  签名: [标量塔 R A B] (hI : I ^ 2 = ⊥) (f : A ->ₐ[R] B)
  定义体: by
  refine
    { diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) ?_ with
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · ext; simp [e]
  · ext; simp
  · intro x y
    let F := diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (by rw [e]; ext; rfl)
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 := by
      rw [← Ideal.mem_bot]; rw [← hI]; rw [pow_two]
      convert! Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk,
      diffToIdealOfQuotientCompEq_apply, Submodule.coe_smul_of_tower, IsScalarTower.coe_toAlgHom',
      LinearMap.toFun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this ⊢
    rw [sub_eq_iff_eq_add]; rw [sub_eq_iff_eq_add] at this
    simp only [this]
    ring

Depends on / 依赖: Ideal.mem_bot, Ideal.mul_mem_mul, IsScalarTower, IsScalarTower.toAlgHom, LinearMap, LinearMap.coe_mk, Submodule, Submodule.coe_add, Submodule.coe_mk, algebraMap, coe_add, coe_mk, convert, diffTo, diffToIdealOfQuotientCompEq, leibniz, map_one_eq_zero, mem_bot, mul_mem_mul, pow_two
-/
def derivationToSquareZeroOfLift [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : A ->ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) :
    Derivation R A I := by
  refine
    { diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) ?_ with
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · ext; simp [e]
  · ext; simp
  · intro x y
    let F := diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (by rw [e]; ext; rfl)
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 := by
      rw [← Ideal.mem_bot]; rw [← hI]; rw [pow_two]
      convert! Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk,
      diffToIdealOfQuotientCompEq_apply, Submodule.coe_smul_of_tower, IsScalarTower.coe_toAlgHom',
      LinearMap.toFun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this ⊢
    rw [sub_eq_iff_eq_add]; rw [sub_eq_iff_eq_add] at this
    simp only [this]
    ring

variable (hI : I ^ 2 = ⊥)

/--
theorem `derivationToSquareZeroOfLift_apply` / 定理 `derivationToSquareZeroOfLift_apply`

English:
theorem derivationToSquareZeroOfLift_apply
  statement: [IsScalarTower R A B] (f : A ->ₐ[R] B)
  proof: rfl

中文:
定理 derivationToSquareZeroOfLift_apply
  结论: [标量塔 R A B] (f : A ->ₐ[R] B)
  证明: rfl
-/
theorem derivationToSquareZeroOfLift_apply [IsScalarTower R A B] (f : A ->ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) (x : A) :
    (derivationToSquareZeroOfLift I hI f e x : B) = f x - algebraMap A B x :=
  rfl

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps -isSimp]
/--
Definition of `liftOfDerivationToSquareZero` / `liftOfDerivationToSquareZero` 的定义

English:
definition liftOfDerivationToSquareZero
  signature: [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : Derivation R A I)
  body: { ((I.restrictScalars R).subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap :
      A ->ₗ[R] B) with
    toFun := fun x => f x + algebraMap A B x
    map_one' := by
      rw [map_one (algebraMap _ _)]; rw [f.map_one_eq_zero]; rw [Submodule.coe_zero]; rw [zero_add]
    map_mul' := fun x y => by
      have : (f x : B) * f y = 0 := by
        rw [← Ideal.mem_bot]; rw [← hI]; rw [pow_two]
        convert! Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add,
        Submodule.coe_smul_of_tower, Algebra.smul_def, this]
      ring
    commutes' := fun r => by
      simp only [Derivation.map_algebraMap, zero_add, Submodule.coe_zero, ←
        IsScalarTower.algebraMap_apply R A B r]
    map_zero' := ((I.restrictScalars R).subtype.comp f.toLinearMap +
      (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }

中文:
定义 liftOfDerivationToSquareZero
  签名: [标量塔 R A B] (hI : I ^ 2 = ⊥) (f : 导子 R A I)
  定义体: { ((I.restrictScalars R).subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap :
      A ->ₗ[R] B) with
    toFun := fun x => f x + algebraMap A B x
    map_one' := by
      rw [map_one (algebraMap _ _)]; rw [f.map_one_eq_zero]; rw [Submodule.coe_zero]; rw [zero_add]
    map_mul' := fun x y => by
      have : (f x : B) * f y = 0 := by
        rw [← Ideal.mem_bot]; rw [← hI]; rw [pow_two]
        convert! Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add,
        Submodule.coe_smul_of_tower, Algebra.smul_def, this]
      ring
    commutes' := fun r => by
      simp only [Derivation.map_algebraMap, zero_add, Submodule.coe_zero, ←
        IsScalarTower.algebraMap_apply R A B r]
    map_zero' := ((I.restrictScalars R).subtype.comp f.toLinearMap +
      (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }

Depends on / 依赖: I.restrictScalars, Ideal.mem_bot, Ideal.mul_mem_mul, IsScalarTower, IsScalarTower.toAlgHom, Submodule, Submodule.coe_add, Submodule.coe_zero, add_mul, algebraMap, coe_add, coe_zero, convert, f.leibniz, f.map_one_eq_zero, f.toLinearMap, leibniz, map_mul, map_one, map_one_eq_zero
-/
def liftOfDerivationToSquareZero [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : Derivation R A I) :
    A ->ₐ[R] B :=
  { ((I.restrictScalars R).subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap :
      A ->ₗ[R] B) with
    toFun := fun x => f x + algebraMap A B x
    map_one' := by
      rw [map_one (algebraMap _ _)]; rw [f.map_one_eq_zero]; rw [Submodule.coe_zero]; rw [zero_add]
    map_mul' := fun x y => by
      have : (f x : B) * f y = 0 := by
        rw [← Ideal.mem_bot]; rw [← hI]; rw [pow_two]
        convert! Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add,
        Submodule.coe_smul_of_tower, Algebra.smul_def, this]
      ring
    commutes' := fun r => by
      simp only [Derivation.map_algebraMap, zero_add, Submodule.coe_zero, ←
        IsScalarTower.algebraMap_apply R A B r]
    map_zero' := ((I.restrictScalars R).subtype.comp f.toLinearMap +
      (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }

-- simp normal form is `liftOfDerivationToSquareZero_mk_apply'`
/--
theorem `liftOfDerivationToSquareZero_mk_apply` / 定理 `liftOfDerivationToSquareZero_mk_apply`

English:
theorem liftOfDerivationToSquareZero_mk_apply
  given: [IsScalarTower R A B] (d : Derivation R A I) (x : A)
  proof: by
  rw [liftOfDerivationToSquareZero_apply]; rw [map_add]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop]; rw [zero_add]; rw [Ideal.Quotient.mk_algebraMap]

@[simp]

中文:
定理 liftOfDerivationToSquareZero_mk_apply
  条件: [标量塔 R A B] (d : 导子 R A I) (x : A)
  证明: by
  rw [liftOfDerivationToSquareZero_apply]; rw [map_add]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop]; rw [zero_add]; rw [Ideal.Quotient.mk_algebraMap]

@[simp]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem.mpr, Ideal.Quotient.mk_algebraMap, Quotient, eq_zero_iff_mem, liftOfDerivationToSquareZero_apply, map_add, mk_algebraMap, zero_add
-/
theorem liftOfDerivationToSquareZero_mk_apply [IsScalarTower R A B] (d : Derivation R A I) (x : A) :
    Ideal.Quotient.mk I (liftOfDerivationToSquareZero I hI d x) = algebraMap A (B ⧸ I) x := by
  rw [liftOfDerivationToSquareZero_apply]; rw [map_add]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop]; rw [zero_add]; rw [Ideal.Quotient.mk_algebraMap]

@[simp]
/--
theorem `liftOfDerivationToSquareZero_mk_apply'` / 定理 `liftOfDerivationToSquareZero_mk_apply'`

English:
theorem liftOfDerivationToSquareZero_mk_apply'
  given: (d : Derivation R A I) (x : A)
  proof: by
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add]

中文:
定理 liftOfDerivationToSquareZero_mk_apply'
  条件: (d : 导子 R A I) (x : A)
  证明: by
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem.mpr, Quotient, eq_zero_iff_mem, zero_add
-/
theorem liftOfDerivationToSquareZero_mk_apply' (d : Derivation R A I) (x : A) :
    (Ideal.Quotient.mk I) (d x) + (algebraMap A (B ⧸ I)) x = algebraMap A (B ⧸ I) x := by
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add]

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`,
there is a 1-1 correspondence between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps!]
/--
Definition of `derivationToSquareZeroEquivLift` / `derivationToSquareZeroEquivLift` 的定义

English:
definition derivationToSquareZeroEquivLift
  signature: [IsScalarTower R A B]
  body: by
  refine ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, ?_⟩, fun f =>
    (derivationToSquareZeroOfLift I hI f.1 f.2 :), ?_, ?_⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
  · intro d; ext x; exact add_sub_cancel_right (d x : B) (algebraMap A B x)
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)

中文:
定义 derivationToSquareZeroEquivLift
  签名: [标量塔 R A B]
  定义体: by
  refine ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, ?_⟩, fun f =>
    (derivationToSquareZeroOfLift I hI f.1 f.2 :), ?_, ?_⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
  · intro d; ext x; exact add_sub_cancel_right (d x : B) (algebraMap A B x)
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)

Depends on / 依赖: add_sub_cancel_right, algebraMap, derivationToSquareZeroOfLift, liftOfDerivationToSquareZero, liftOfDerivationToSquareZero_mk_apply, sub_add_cancel
-/
def derivationToSquareZeroEquivLift [IsScalarTower R A B] : Derivation R A I ≃
    { f : A ->ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } := by
  refine ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, ?_⟩, fun f =>
    (derivationToSquareZeroOfLift I hI f.1 f.2 :), ?_, ?_⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
  · intro d; ext x; exact add_sub_cancel_right (d x : B) (algebraMap A B x)
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)

end ToSquareZero
