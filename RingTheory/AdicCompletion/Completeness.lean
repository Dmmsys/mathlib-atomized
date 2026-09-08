/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `AdicCompletion.ofPowSMul`: The canonical inclusion between adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.ofValEqZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `ofValEqZero` constructs the corresponding element in
  the adic completion of `I ^ n • M`.

## Main results

* `AdicCompletion.pow_smul_top_eq_ker_eval`: `I ^ n • AdicCompletion I M` is exactly the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.isAdicComplete`: `AdicCompletion I M` is `I`-adically complete if `I` is
  finitely generated.

* `MvPowerSeries.isAdicComplete`: Multivariate power series is adic complete with respect to
  the ideal spanned by all variables when the index is finite.

-/

public section

noncomputable section

open Submodule Finsupp

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {a b c : ℕ}

namespace AdicCompletion

variable (M) in
/-- The canonical inclusion from the adic completion of `I ^ n • M` to
the adic completion of `M`. -/
/-
**AdicCompletion.ofPowSMul** 是 Mathlib 中的一个缩写定义，位于命名空间 `AdicCompletion`。
形式化陈述：ofPowSMul (n : Nat) : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M) ->ₗ[Ad
icCompletion I R] AdicCompletion I M
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from the adic completion of `I ^ n • M` to
the adic completion of `M`.
-/
abbrev ofPowSMul (n : ℕ) : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)
    →ₗ[AdicCompletion I R] AdicCompletion I M := map I (I ^ n • ⊤ : Submodule R M).subtype

set_option backward.isDefEq.respectTransparency.types false in
/-
**AdicCompletion.ofPowSMul_val_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：ofPowSMul_val_apply (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : Su
bmodule R M)} : (ofPowSMul I M a x).val c = powSMulQuotInclusion I M h ⊤ (x.val 
b)
参数：h : c = b + a；I ^ a • ⊤ : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AdicCompletion.map_val_apply`：map_val_apply (f : M ->ₗ[R] N) {n : Nat} (
x : AdicCompletion I M) : (map I f x).val n = f.reduceModIdeal (I ^ n) (x.val n)
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPowSMul_val_apply (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} :
    (ofPowSMul I M a x).val c = powSMulQuotInclusion I M h ⊤ (x.val b) := by
  rw [← x.prop (show b ≤ c by lia), map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z ↦ ?_
  simp [powSMulQuotInclusion]
/-
**AdicCompletion.ofPowSMul_val_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AdicComp
letion`。
形式化陈述：ofPowSMul_val_apply_eq_zero (h : a <= b) {x : AdicCompletion I ↥(I ^ b • ⊤
 : Submodule R M)} : (ofPowSMul I M b x).val a = 0
参数：h : a <= b；I ^ b • ⊤ : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.map_val_apply`：map_val_apply (f : M ->ₗ[R] N) {n : Nat} (
x : AdicCompletion I M) : (map I f x).val n = f.reduceModIdeal (I ^ n) (x.val n)
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
· 使用引理 `Submodule.pow_smul_top_le`：pow_smul_top_le {m n : Nat} (h : m <= n) : (I
 ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem ofPowSMul_val_apply_eq_zero (h : a ≤ b)
    {x : AdicCompletion I ↥(I ^ b • ⊤ : Submodule R M)} : (ofPowSMul I M b x).val a = 0 := by
  rw [map_val_apply]
  refine Quotient.induction_on _ (x.val a) fun z ↦ ?_
  simpa using pow_smul_top_le _ _ h z.prop
/-
**AdicCompletion.ofPowSMul_injective** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：ofPowSMul_injective (n : Nat) : Function.Injective (ofPowSMul I M n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `Submodule.powSMulQuotInclusion_injective`：powSMulQuotInclusion_injective
 {a b c : Nat} (h : c = b + a) (N : Submodule R M) : Function.Injective (powSMul
QuotInclusion I M h N)
· 使用定理 `AdicCompletion.ofPowSMul_val_apply`：ofPowSMul_val_apply (h : c = b + a) 
{x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} : (ofPowSMul I M a x).val c 
= powSMulQuotInclusion I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPowSMul_injective (n : ℕ) : Function.Injective (ofPowSMul I M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSMul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSMulQuotInclusion_injective ..)] at hx
  simp [hx]
/-
**AdicCompletion.ofValEqZeroAux_exists** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ofValEqZeroAux_exists {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : ∃ t, powSMulQuotInclusion I M h ⊤ t = x.val c := by
  simpa [← LinearMap.mem_range, range_powSMulQuotInclusion] using
    (val_apply_mem_smul_top_iff I (show a ≤ c by lia)).mpr ha

/-- An auxiliary lift function used in the definition of `ofValEqZero`.
Use `ofValEqZero` instead. -/
/-
**AdicCompletion.ofValEqZeroAux** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：ofValEqZeroAux {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0)
 : ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodu
le R M))
参数：h : c = b + a；ha : x.val a = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.Completeness.0.AdicCompletion
.ofValEqZeroAux_exists`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) {M : 
Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {a b c : ℕ} {
x : …

--- 原说明 ---
An auxiliary lift function used in the definition of `ofValEqZero`.
Use `ofValEqZero` instead.
-/
def ofValEqZeroAux {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0) :
    ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodule R M)) :=
  Exists.choose (ofValEqZeroAux_exists I h ha)
/-
**AdicCompletion.ofValEqZeroAux_prop** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ofValEqZeroAux_prop {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : (powSMulQuotInclusion I M h ⊤) (ofValEqZeroAux I h ha) = x.val c :=
  Exists.choose_spec (ofValEqZeroAux_exists I h ha)

/-- Given an element `x` in the adic completion of `M` whose projection to `M / I ^ n • M` is zero,
`ofValEqZero` constructs the corresponding element in the adic completion of `I ^ n • M`. -/
/-
**AdicCompletion.ofValEqZero** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：ofValEqZero {n : Nat} {x : AdicCompletion I M} (hxn : x.val n = 0) : AdicC
ompletion I ↥(I ^ n • (⊤ : Submodule R M)) where val i
参数：hxn : x.val n = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `x` in the adic completion of `M` whose projection to `M / I ^ 
n • M` is zero,
`ofValEqZero` constructs the corresponding element in the adic completion of `I 
^ n • M`.
-/
def ofValEqZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    AdicCompletion I ↥(I ^ n • (⊤ : Submodule R M)) where
  val i := ofValEqZeroAux I (Eq.refl (i + n)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSMulQuotInclusion_injective I rfl ⊤).eq_iff, ofValEqZeroAux_prop,
      ← LinearMap.comp_apply, ← factorPow_comp_powSMulQuotInclusion I rfl
      (show i + k + n = k + (i + n) by ring), LinearMap.comp_apply, ofValEqZeroAux_prop]
    exact x.prop (by lia)

@[simp]
/-
**AdicCompletion.ofPowSMul_ofValEqZero** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion
`。
形式化陈述：ofPowSMul_ofValEqZero {n : Nat} {x : AdicCompletion I M} (hxn : x.val n = 
0) : ofPowSMul I M n (ofValEqZero I hxn) = x
参数：hxn : x.val n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.ofPowSMul_val_apply`：ofPowSMul_val_apply (h : c = b + a) 
{x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} : (ofPowSMul I M a x).val c 
= powSMulQuotInclusion I…
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.Completeness.0.AdicCompletion
.ofValEqZero.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) {M : Type 
u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {n : ℕ} {x : Adic…
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.Completeness.0.AdicCompletion
.ofValEqZeroAux_prop`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) {M : Ty
pe u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {a b c : ℕ} {x 
: …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.ofPowSMul_val_apply_eq_zero`：ofPowSMul_val_apply_eq_zero 
(h : a <= b) {x : AdicCompletion I ↥(I ^ b • ⊤ : Submodule R M)} : (ofPowSMul I 
M b x).val a = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem ofPowSMul_ofValEqZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    ofPowSMul I M n (ofValEqZero I hxn) = x := by
  ext i; by_cases! h : n ≤ i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [ofPowSMul_val_apply _ rfl, ofValEqZero, ofValEqZeroAux_prop]
  rw [ofPowSMul_val_apply_eq_zero _ h.le, ← x.prop h.le, hxn, _root_.map_zero]
/-
**AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval** 是 Mathlib 中的一个定理，
位于命名空间 `AdicCompletion`。
形式化陈述：restrictScalars_range_ofPowSMul_eq_ker_eval {n : Nat} : (ofPowSMul I M n).
range.restrictScalars R = (eval I M n).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AdicCompletion.instIsScalarTower_1`：∀ {R : Type u_1} [inst : CommRing R]
 (I : Ideal R) {M : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M], IsScalarTower R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `AdicCompletion.eval_apply`：eval_apply (n : Nat) (f : AdicCompletion I M)
 : eval I M n f = f.1 n
· 使用定理 `AdicCompletion.ofPowSMul_val_apply_eq_zero`：ofPowSMul_val_apply_eq_zero 
(h : a <= b) {x : AdicCompletion I ↥(I ^ b • ⊤ : Submodule R M)} : (ofPowSMul I 
M b x).val a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdicCompletion.ofPowSMul_ofValEqZero`：ofPowSMul_ofValEqZero {n : Nat} {x
 : AdicCompletion I M} (hxn : x.val n = 0) : ofPowSMul I M n (ofValEqZero I hxn)
 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrictScalars_range_ofPowSMul_eq_ker_eval {n : ℕ} :
    (ofPowSMul I M n).range.restrictScalars R = (eval I M n).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker, eval_apply, ofPowSMul_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use ofValEqZero I hx; simp

/- An intermediate helper lemma for the theorem below to avoid introducing
`AdicCompletion.finsuppSum` (the `Finsupp` version of `AdicCompletion.sum`).
It proves the equality of two linear maps:

The LHS evaluates a linear combination with coefficients `f i` on
the direct sum of the completed modules `AdicCompletion I M`.

The RHS first commutes the direct sum and the completion via `sumEquivOfFintype`,
and then applies the completion of the standard linear combination operator on `M`. -/
/-
**AdicCompletion.lsum_smul_comp_finsuppLEquivDirectSum_symm** 是 Mathlib 中的一个引理，位
于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An intermediate helper lemma for the theorem below to avoid introducing
`AdicCompletion.finsuppSum` (the `Finsupp` version of `AdicCompletion.sum`).
It proves the equality of two linear maps:

The LHS evaluates a linear combination with coefficients `f i` on
the direct sum of the completed modules `AdicCompletion I M`.

The RHS first commutes the direct sum and the completion via `sumEquivOfFintype`
,
and then applies the completion of the standard linear combination operator on `
M`.
-/
private lemma lsum_smul_comp_finsuppLEquivDirectSum_symm {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : ι → R) : ((lsum (AdicCompletion I R))
      fun i ↦ ((algebraMap R (AdicCompletion I R)) (f i) • .id :
        AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I M)) ∘ₗ
      (finsuppLEquivDirectSum (AdicCompletion I R) (AdicCompletion I M) ι).symm.toLinearMap =
    (map I (lsum R fun i ↦ f i • .id) ∘ₗ map I (finsuppLEquivDirectSum R M ι).symm.toLinearMap) ∘ₗ
      (sumEquivOfFintype I (fun _ : ι ↦ M)) := by
  ext
  -- simp [-algebraMap_smul, algebraMap_apply, -smul_eq_mul]
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
    coe_lsum, LinearMap.coe_smul, LinearMap.id_coe, LinearEquiv.coe_coe, Function.comp_apply,
    finsuppLEquivDirectSum_symm_lof, Pi.smul_apply, id_eq, smul_zero, sum_single_index, smul_eval,
    mapQ_eq_factor, factor_eq_factor, of_apply, mkQ_apply, Ideal.Quotient.mk_eq_mk, mk_apply_coe,
    sumEquivOfFintype_apply, sum_lof, map_mk, AdicCauchySequence.map_apply_coe, map_smul]
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

set_option backward.isDefEq.respectTransparency.types false in
variable {I} in
@[stacks 05GG "(2)"]
/-
**AdicCompletion.pow_smul_top_eq_ker_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicComplet
ion`。
形式化陈述：pow_smul_top_eq_ker_eval {n : Nat} (h : I.FG) : I ^ n • ⊤ = (eval I M n).k
er
参数：h : I.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AdicCompletion.pow_smul_top_le_ker_eval`：pow_smul_top_le_ker_eval (n : N
at) : I ^ n • ⊤ <= (eval I M n).ker
· 使用定理 `Ideal.FG.pow`：∀ {R : Type u_1} [inst : Semiring R] {I : Ideal R} [I.IsTw
oSided] {n : ℕ}, I.FG → (I ^ n).FG
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.span_smul_eq`：span_smul_eq (s : Set R) (N : Submodule R M) : I
deal.span s • N = s • N
· 使用定理 `AdicCompletion.instIsScalarTower_1`：∀ {R : Type u_1} [inst : CommRing R]
 (I : Ideal R) {M : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M], IsScalarTower R …
· 使用定理 `Submodule.restrictScalars_top`：restrictScalars_top : restrictScalars S (
⊤ : Submodule R M) = ⊤
· 使用定理 `Submodule.restrictScalars_image_smul_eq`：restrictScalars_image_smul_eq {
S M : Type*} [CommSemiring S] [Algebra S R] [AddCommMonoid M] [Module R M] [Modu
le S M] [IsScalarTower S R M]…
· 使用定理 `AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval`：restrictScal
ars_range_ofPowSMul_eq_ker_eval {n : Nat} : (ofPowSMul I M n).range.restrictScal
ars R = (eval I M n).ker
· 使用定理 `Submodule.restrictScalars_le`：∀ (S : Type u_1) {R : Type u_2} {M : Type 
u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S]   [ins
t_3 : _root_.Modul…
· 使用定理 `Submodule.image_smul_top_eq_range_lsum`：image_smul_top_eq_range_lsum (s 
: Set σ) (f : σ -> R) : (f '' s • ⊤ : Submodule R M) = (lsum (S
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.Completeness.0.AdicCompletion
.lsum_smul_comp_finsuppLEquivDirectSum_symm`：∀ {R : Type u_1} [inst : CommRing R
] (I : Ideal R) {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   {ι : Type u_3} [i…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `AdicCompletion.map_comp`：map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) : ma
p I g ∘ₗ map I f = map I (g ∘ₗ f)
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `AdicCompletion.map_id`：map_id : map I (LinearMap.id (M
· 使用定理 `Submodule.smul_top_eq_range_lsum`：smul_top_eq_range_lsum (s : Set R) : (
s • ⊤ : Submodule R M) = (lsum (S
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.range_codRestrict`：range_codRestrict {τ₂₁ : R₂ ->+* R} [RingHo
mSurjective τ₂₁] (p : Submodule R M) (f : M₂ ->ₛₗ[τ₂₁] M) (hf) : range (codRestr
ict p f hf) = com…
（共 34 条，此处仅展示前 30 条）
-/
theorem pow_smul_top_eq_ker_eval {n : ℕ} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M),
    ← restrictScalars_image_smul_eq (R := AdicCompletion I R),
    ← restrictScalars_range_ofPowSMul_eq_ker_eval, restrictScalars_le,
    image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top (f := (finsuppLEquivDirectSum ..).symm.toLinearMap)
    _ (by simp), lsum_smul_comp_finsuppLEquivDirectSum_symm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ ↦ by
      simp [← LinearMap.comp_apply, map_comp]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((lsum R fun i : s ↦ i.val • (LinearMap.id : M →ₗ[R] M)).codRestrict
    (I ^ n • ⊤) (fun _ ↦ by simp [← hs, span_smul_eq, smul_top_eq_range_lsum])) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, ← hs, span_smul_eq,
      smul_top_eq_range_lsum]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

set_option backward.isDefEq.respectTransparency.types false in
variable {I} in
/-- `AdicCompletion I M` is adic complete when `I` is finitely generated. -/
@[stacks 05GG "(1)"]
/-
**AdicCompletion.isAdicComplete** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：isAdicComplete (h : I.FG) : IsAdicComplete I (AdicCompletion I M) where pr
ec' x hx
参数：h : I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.instIsHausdorff`：∀ {R : Type u_1} [inst : CommRing R] (I 
: Ideal R) (M : Type u_4) [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R 
M], IsHausdorff I (A…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.transitionMap_comp_eval_apply`：transitionMap_comp_eval_ap
ply {m n : Nat} (hmn : m <= n) (x : AdicCompletion I M) : transitionMap I M hmn 
(x.val n) = x.val m
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AdicCompletion.eval_apply`：eval_apply (n : Nat) (f : AdicCompletion I M)
 : eval I M n f = f.1 n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `AdicCompletion.pow_smul_top_eq_ker_eval`：pow_smul_top_eq_ker_eval {n : N
at} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker
· 使用定理 `SModEq.sub_mem`：sub_mem : x ≡ y [SMOD U] ↔ x - y in U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`AdicCompletion I M` is adic complete when `I` is finitely generated.
-/
theorem isAdicComplete (h : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  prec' x hx := by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_ker_eval h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem, pow_smul_top_eq_ker_eval h]
    simp [L]
/-
**AdicCompletion.ker_evalOne** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_evalOneₐ_eq_map (fg : I.FG) :
    RingHom.ker (evalOneₐ I).toRingHom = I.map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (AdicCompletion.eval I R 1).ker
  · have eq : I ^ 1 * ⊤ = I := by simp
    have : Function.Injective (Ideal.Quotient.factor ((le_of_eq eq))) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← factorₐ_evalₐ_one, ← factor_eval_eq_evalₐ] using map_eq_zero_iff _ this
  · simp [← pow_smul_top_eq_ker_eval fg]

end AdicCompletion

namespace MvPowerSeries

/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : Type*} [Finite σ] :
    IsAdicComplete (.span (.range X) : Ideal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by
  have : Ideal.map (toAdicCompletionAlgEquiv σ R).toRingEquiv (Ideal.span (Set.range X)) =
    (MvPolynomial.idealOfVars σ R).map (algebraMap ..) := by
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2; ext1
    simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X, toAdicCompletion_coe]
  rw [← IsAdicComplete.congr_ringEquiv _ (toAdicCompletionAlgEquiv σ R).toRingEquiv, this,
    IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (MvPolynomial.idealOfVars_fg σ R)

end MvPowerSeries

namespace PowerSeries

/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAdicComplete (.span {X} : Ideal (PowerSeries R)) (PowerSeries R) := by
  have : IsAdicComplete (.span (.range MvPowerSeries.X) : Ideal (MvPowerSeries Unit R))
    (MvPowerSeries Unit R) := inferInstance
  rwa [Set.range_unique] at this

end PowerSeries

