/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yury Kudryashov, Joseph Myers, Heather Macbeth, Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Tactic.Contrapose

/-!
# `NoZeroSMulDivisors`

This file defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).

## Usage notes

Note that `NoZeroSMulDivisors` is deprecated in favor of `Module.IsTorsionFree`, which is the
mathematically correct generalisation to semimodules.
-/

public section

assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀

variable {R M G : Type*}

/-- `NoZeroSMulDivisors R M` states that a scalar multiple is `0` only if either argument is `0`.
This is a version of saying that `M` is torsion free, without assuming `R` is zero-divisor free.

The main application of `NoZeroSMulDivisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0`.

It is a generalization of the `NoZeroDivisors` class to heterogeneous multiplication.
-/
@[mk_iff]
/--
Definition of `NoZeroSMulDivisors` / `NoZeroSMulDivisors` 的定义

English:
class NoZeroSMulDivisors
  parameters: (R M : Type*) [Zero R] [Zero M] [SMul R M]
  axioms and operations (1):
    - eq_zero_or_eq_zero_of_smul_eq_zero : forall {c : R} {x : M}, c • x = 0 -> c = 0 ∨ x = 0

中文:
类 NoZeroSMulDivisors
  参数: (R M : 类型) [Zero R] [Zero M] [SMul R M]
  公理与运算 (1 个):
    - eq_zero_or_eq_zero_of_smul_eq_zero : 对任意 {c : R} {x : M}, c • x = 0 -> c = 0 ∨ x = 0
-/
class NoZeroSMulDivisors (R M : Type*) [Zero R] [Zero M] [SMul R M] : Prop where
  /-- If scalar multiplication yields zero, either the scalar or the vector was zero. -/
  eq_zero_or_eq_zero_of_smul_eq_zero : forall {c : R} {x : M}, c • x = 0 -> c = 0 ∨ x = 0

export NoZeroSMulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

/--
theorem `Function.Injective.noZeroSMulDivisors` / 定理 `Function.Injective.noZeroSMulDivisors`

English:
theorem Function.Injective.noZeroSMulDivisors
  statement: {R M N : Type*} [Zero R] [Zero M] [Zero N]
  proof: ⟨fun {_ _} h =>
Or.imp_right (@hf _ _) h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

中文:
定理 Function.Injective.noZeroSMulDivisors
  结论: {R M N : 类型} [Zero R] [Zero M] [Zero N]
  证明: ⟨fun {_ _} h =>
Or.imp_right (@hf _ _) h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

Depends on / 依赖: Or.imp_right, eq_zero_or_eq_zero_of_smul_eq_zero, h0.symm, imp_right
-/
theorem Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Zero N]
    [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M -> N) (hf : Function.Injective f)
    (h0 : f 0 = 0) (hs : forall (c : R) (x : M), f (c • x) = c • f x) : NoZeroSMulDivisors R M :=
  ⟨fun {_ _} h =>
Or.imp_right (@hf _ _) h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

-- See note [lower instance priority]
instance (priority := 100) NoZeroDivisors.toNoZeroSMulDivisors [Zero R] [Mul R]
    [NoZeroDivisors R] : NoZeroSMulDivisors R R :=
  ⟨fun {_ _} => eq_zero_or_eq_zero_of_mul_eq_zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [IsDomain R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] :
  body: by
    dsimp at hm
    rw [← sub_eq_zero]; rw [← smul_sub] at hm
    simpa [hr.ne_zero, sub_eq_zero] using eq_zero_or_eq_zero_of_smul_eq_zero hm

中文:
实例 [Semiring
  签名: R] [IsDomain R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] :
  定义体: by
    dsimp at hm
    rw [← sub_eq_zero]; rw [← smul_sub] at hm
    simpa [hr.ne_zero, sub_eq_zero] using eq_zero_or_eq_zero_of_smul_eq_zero hm

Depends on / 依赖: eq_zero_or_eq_zero_of_smul_eq_zero, hr.ne_zero, ne_zero, smul_sub, sub_eq_zero
-/
instance [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] :
    Module.IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := by
    dsimp at hm
    rw [← sub_eq_zero]; rw [← smul_sub] at hm
    simpa [hr.ne_zero, sub_eq_zero] using eq_zero_or_eq_zero_of_smul_eq_zero hm

/--
theorem `noZeroSMulDivisors_iff_right_eq_zero_of_smul` / 定理 `noZeroSMulDivisors_iff_right_eq_zero_of_smul`

English:
theorem noZeroSMulDivisors_iff_right_eq_zero_of_smul
  given: [Zero R] [Zero M] [SMul R M]
  proof: by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq => h eq hr, fun h r m eq hr => h r hr m eq⟩

中文:
定理 noZeroSMulDivisors_iff_right_eq_zero_of_smul
  条件: [Zero R] [Zero M] [SMul R M]
  证明: by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq => h eq hr, fun h r m eq hr => h r hr m eq⟩

Depends on / 依赖: noZeroSMulDivisors_iff, or_iff_not_imp_left, simp_rw
-/
theorem noZeroSMulDivisors_iff_right_eq_zero_of_smul [Zero R] [Zero M] [SMul R M] :
    NoZeroSMulDivisors R M ↔ forall r : R, r != 0 -> forall m : M, r • m = 0 -> m = 0 := by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq => h eq hr, fun h r m eq hr => h r hr m eq⟩

/--
Instance `IsAddTorsionFree.to_noZeroSMulDivisors_nat` / 实例 `IsAddTorsionFree.to_noZeroSMulDivisors_nat`

English:
instance IsAddTorsionFree.to_noZeroSMulDivisors_nat
  signature: [AddMonoid M] [IsAddTorsionFree M]
  body: by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2

中文:
实例 IsAddTorsionFree.to_noZeroSMulDivisors_nat
  签名: [AddMonoid M] [IsAddTorsionFree M]
  定义体: by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2

Depends on / 依赖: contrapose, nsmul_right_injective
-/
instance IsAddTorsionFree.to_noZeroSMulDivisors_nat [AddMonoid M] [IsAddTorsionFree M] :
    NoZeroSMulDivisors Nat M where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2

/--
Instance `IsAddTorsionFree.to_noZeroSMulDivisors_int` / 实例 `IsAddTorsionFree.to_noZeroSMulDivisors_int`

English:
instance IsAddTorsionFree.to_noZeroSMulDivisors_int
  signature: [AddGroup G] [IsAddTorsionFree G]
  body: by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2

中文:
实例 IsAddTorsionFree.to_noZeroSMulDivisors_int
  签名: [AddGroup G] [IsAddTorsionFree G]
  定义体: by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2

Depends on / 依赖: contrapose, zsmul_right_injective
-/
instance IsAddTorsionFree.to_noZeroSMulDivisors_int [AddGroup G] [IsAddTorsionFree G] :
    NoZeroSMulDivisors Int G where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2
