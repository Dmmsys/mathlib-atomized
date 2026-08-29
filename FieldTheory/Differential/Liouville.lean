/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Algebra.Field
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.FieldTheory.Differential.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Liouville's theorem

A proof of Liouville's theorem. Follows
[Rosenlicht, M. Integration in finite terms][Rosenlicht_1972].

## Liouville field extension

This file defines Liouville field extensions, which are differential field extensions which satisfy
a slight generalization of Liouville's theorem. Note that this definition doesn't appear in the
literature, and we introduce it as part of the formalization of Liouville's theorem.

## Main declarations
- `IsLiouville`: A field extension being Liouville
- `isLiouville_of_finiteDimensional`: all finite-dimensional field extensions
  (of a field with characteristic 0) are Liouville.

-/

public section

open Differential algebraMap IntermediateField Finset Polynomial

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K] [DifferentialAlgebra F K]

/--
Definition of `IsLiouville` / `IsLiouville` 的定义

English:
class IsLiouville
  parameters: : Prop where
  axioms and operations (1):
    - isLiouville((a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0) (u : ι -> K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′)) : exists (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ -> F) (_ : forall x, (c₀ x)′ = 0) (u₀ : ι₀ -> F) (v₀ : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀′

中文:
类 是Liouville
  参数: : 命题 where
  公理与运算 (1 个):
    - isLiouville((a : F) (ι : 类型) [有限类型 ι] (c : ι -> F) (hc : 对任意 x, (c x)′ = 0) (u : ι -> K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′)) : 存在 (ι₀ : 类型) (_ : 有限类型 ι₀) (c₀ : ι₀ -> F) (_ : 对任意 x, (c₀ x)′ = 0) (u₀ : ι₀ -> F) (v₀ : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀′
-/
class IsLiouville : Prop where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0)
    (u : ι -> K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    exists (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ -> F) (_ : forall x, (c₀ x)′ = 0)
      (u₀ : ι₀ -> F) (v₀ : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀′

/--
Instance `IsLiouville.rfl` / 实例 `IsLiouville.rfl`

English:
instance IsLiouville.rfl
  signature: : IsLiouville F F where
  body: ⟨ι, _, c, hc, u, v, h⟩

中文:
实例 是Liouville.rfl
  签名: : 是Liouville F F where
  定义体: ⟨ι, _, c, hc, u, v, h⟩
-/
instance IsLiouville.rfl : IsLiouville F F where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0)
      (u : ι -> F) (v : F) (h : a = ∑ x, c x * logDeriv (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩

/--
lemma `IsLiouville.trans` / 引理 `IsLiouville.trans`

English:
lemma IsLiouville.trans
  statement: {A : Type*} [Field A] [Algebra K A] [Algebra F A]
  proof: by
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, h₀⟩ := inst2.isLiouville (a : K) ι
        ((↑) ∘ c)
        (fun _ => by simp only [Function.comp_apply, ← coe_deriv, coe_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι₀) := mem_

中文:
引理 是Liouville.trans
  结论: {A : 类型} [域 A] [代数 K A] [代数 F A]
  证明: by
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, h₀⟩ := inst2.isLiouville (a : K) ι
        ((↑) ∘ c)
        (fun _ => by simp only [Function.comp_apply, ← coe_deriv, coe_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι₀) := mem_

Depends on / 依赖: FaithfulSMul, FaithfulSMul.alge, Function, Function.comp_apply, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap.coe_zero, algebraMap_apply, apply_fun, coe_deriv, coe_eq_zero_iff, coe_zero, comp_apply, inst1.isLiouville, inst2.isLiouville, isLiouville, mem_range_of_deriv_eq_zero
-/
lemma IsLiouville.trans {A : Type*} [Field A] [Algebra K A] [Algebra F A]
    [Differential A] [IsScalarTower F K A] [Differential.ContainConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0)
      (u : ι -> A) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, h₀⟩ := inst2.isLiouville (a : K) ι
        ((↑) ∘ c)
        (fun _ => by simp only [Function.comp_apply, ← coe_deriv, coe_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι₀) := mem_range_of_deriv_eq_zero F (hc₀ x)
    choose c₀ hc using hc
    apply inst1.isLiouville a ι₀ c₀ _ u₀ v₀
    · rw [h₀]
      simp [hc]
    · intro
      apply_fun ((↑) : F -> K)
      · simp only [coe_deriv, hc, algebraMap.coe_zero]
        apply hc₀
      · apply FaithfulSMul.algebraMap_injective

section Algebraic
/-
The case of Liouville's theorem for algebraic extensions.
-/

variable {F K} [CharZero F]

/--
If `K` is a Liouville extension of `F` and `B` is a finite-dimensional intermediate
field `K / B / F`, then it's also a Liouville extension of `F`.
-/
instance (B : IntermediateField F K)
    [FiniteDimensional F B] [inst : IsLiouville F K] :
    IsLiouville F B where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0)
      (u : ι -> B) (v : B) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.isLiouville a ι c hc (B.val ∘ u) (B.val v)
    dsimp only [coe_val, Function.comp_apply]
    conv =>
      rhs
      congr
      · rhs
        intro x
        rhs
        apply logDeriv_algebraMap (u x)
      · apply (deriv_algebraMap v)
    simp_rw [IsScalarTower.algebraMap_apply F B K]
    norm_cast


/--
lemma `IsLiouville.equiv` / 引理 `IsLiouville.equiv`

English:
lemma IsLiouville.equiv
  statement: {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
  proof: by
    apply inst.isLiouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

中文:
引理 是Liouville.equiv
  结论: {K' : 类型} [域 K'] [微分 K'] [代数 F K']
  证明: by
    apply inst.isLiouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, algEquiv_deriv, apply_fun, commutes, e.symm, inst.isLiouville, isLiouville, logDeriv, map_add, map_mul, map_sum
-/
lemma IsLiouville.equiv {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
    [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K']
    [inst : IsLiouville F K] (e : K ≃ₐ[F] K') : IsLiouville F K' where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0)
      (u : ι -> K') (v : K') (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.isLiouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

/--
A finite-dimensional Galois extension of `F` is a Liouville extension.
This is private because it's generalized by all finite-dimensional extensions being Liouville.
-/
private local instance isLiouville_of_finiteDimensional_galois [FiniteDimensional F K]
    [IsGalois F K] : IsLiouville F K where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0)
      (u : ι -> K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    have : CharZero K := charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective F K)
    -- We sum `e x` over all isomorphisms `e : K ≃ₐ[F] K`.
    -- Because this is a Galois extension each of the relevant values will be in `F`.
    -- We need to divide by `Fintype.card (K ≃ₐ[F] K)` to get the original answer.
    let c₀ (i : ι) := (c i) / (Fintype.card (K ≃ₐ[F] K))
    -- logDeriv turns sums to products, so the new `u` will be the product of the old `u` over all
    -- isomorphisms
    let u₁ (i : ι) := ∏ x : (K ≃ₐ[F] K), x (u i)
    -- Each of the values of u₁ are fixed by all isomorphisms.
    have : forall i, u₁ i in fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro i ⟨e, _⟩
      change e (u₁ i) = u₁ i
      simp only [u₁, map_prod]
      apply Fintype.prod_equiv (Equiv.mulLeft e)
      simp
    have ffb : fixedField ⊤ = ⊥ := (IsGalois.tfae.out 0 1).mp (inferInstance : IsGalois F K)
    simp_rw [ffb, IntermediateField.mem_bot, Set.mem_range] at this
    -- Therefore they are all in `F`. We use `choose` to get their values in `F`.
    choose u₀ hu₀ using this
    -- We do almost the same thing for `v₁`, just with sum instead of product.
    let v₁ := (∑ x : (K ≃ₐ[F] K), x v) / (Fintype.card ((K ≃ₐ[F] K)))
    have : v₁ in fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro ⟨e, _⟩
      change e v₁ = v₁
      simp only [v₁, map_div₀, map_sum, map_natCast]
      congr 1
      apply Fintype.sum_equiv (Equiv.mulLeft e)
      simp
    rw [ffb]; rw [IntermediateField.mem_bot] at this
    obtain ⟨v₀, hv₀⟩ := this
    exists ι, inferInstance, c₀, ?_, u₀, v₀
    · -- We need to prove that all `c₀` are constants.
      -- This is true because they are the division of a constant by
      -- a natural number (which is also constant)
      intro x
      simp [c₀, Derivation.leibniz_div, hc]
    · -- Proving that this works is mostly straightforward algebraic manipulation,
      apply_fun (algebraMap F K)
      case inj =>
        exact FaithfulSMul.algebraMap_injective F K
      simp only [map_add, map_sum, map_mul, ← logDeriv_algebraMap, hu₀, ← deriv_algebraMap, hv₀]
      unfold u₁ v₁ c₀
      clear c₀ u₁ u₀ hu₀ v₁ v₀ hv₀
      push_cast
      rw [Derivation.leibniz_div_const]; rw [smul_eq_mul]; rw [inv_mul_eq_div]
      case h => simp
      simp only [map_sum, div_mul_eq_mul_div]
      rw [← sum_div]; rw [← add_div]
      field_simp
      -- Here we rewrite logDeriv (∏ x : K ≃ₐ[F] K, x (u i)) to ∑ x : K ≃ₐ[F] K, logDeriv (x (u i))
      conv =>
        enter [2, 1, 2, i, 2]
        equals ∑ x : K ≃ₐ[F] K, logDeriv (x (u i)) =>
          by_cases h : u i = 0 <;>
          simp [logDeriv_prod, h]
      simp_rw [mul_sum]
      rw [sum_comm]; rw [← sum_add_distrib]
      trans ∑ _ : (K ≃ₐ[F] K), a
      · simp [mul_comm]
      · rcongr e
        apply_fun e at h
        simp only [AlgEquiv.commutes, map_add, map_sum, map_mul] at h
        convert! h using 2
        · rcongr x
          simp [logDeriv, algEquiv_deriv']
        · rw [algEquiv_deriv']

/--
Instance `isLiouville_of_finiteDimensional` / 实例 `isLiouville_of_finiteDimensional`

English:
instance isLiouville_of_finiteDimensional
  signature: [FiniteDimensional F K]
  body: let map := IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K)
  let K' := map.fieldRange
  have : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.rest

中文:
实例 isLiouville_of_finiteDimensional
  签名: [有限维 F K]
  定义体: let map := IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K)
  let K' := map.fieldRange
  have : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.rest

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, AlgebraicClosure, FiniteDimensional, IntermediateField, IntermediateField.le_normalClosure, IntermediateField.restrict, IntermediateField.restrictAlgEquiv, IsAlgClosed, IsAlgClosed.lift, IsLiouville, IsLiouville.equiv, LinearMap, LinearMap.finiteDimensional_range, fieldRange, finiteDimensional_range, kequiv, kequiv.symm, le_normalClosure, map.fieldRange
-/
instance isLiouville_of_finiteDimensional [FiniteDimensional F K] :
    IsLiouville F K :=
  let map := IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K)
  let K' := map.fieldRange
  have : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.restrict
    (F := K') (IntermediateField.le_normalClosure ..)
  have kequiv : K ≃ₐ[F] ↥B := (show K ≃ₐ[F] K' from AlgEquiv.ofInjectiveField map).trans
    (IntermediateField.restrictAlgEquiv _)
  IsLiouville.equiv kequiv.symm

end Algebraic
