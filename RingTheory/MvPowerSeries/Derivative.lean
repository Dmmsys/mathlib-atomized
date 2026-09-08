/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Formal partial derivatives of multivariate power series

This file defines `MvPowerSeries.pderiv R i`, the formal partial derivative of a multivariate
power series with respect to variable `i`, as a
`Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R)`.

See also `PowerSeries.derivative` for the univariate setting.

## Main definitions

- `MvPowerSeries.pderiv R i`: the formal partial derivative with respect to `i`, as a derivation.

## Main results

- `MvPowerSeries.coeff_pderiv`: coefficient formula
  `coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)`.
- `MvPowerSeries.pderiv_coe`: compatibility with `MvPolynomial.pderiv`.
- `MvPowerSeries.trunc_pderiv`: truncation commutes with partial differentiation.
- `MvPowerSeries.pderiv.ext`: a power series is determined by its constant term and its partial
  derivatives.
- `MvPowerSeries.pderiv_pow`: power rule.
- `MvPowerSeries.pderiv_inv`, `MvPowerSeries.pderiv_inv'`: derivative of an inverse.

-/

@[expose] public section

namespace MvPowerSeries

open MvPolynomial Finsupp

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- The underlying function of the formal partial derivative with respect to variable `i`.
This is packaged as a derivation in `MvPowerSeries.pderiv`. -/
/-
**MvPowerSeries.pderivFun** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：pderivFun (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R
参数：i : σ；f : MvPowerSeries σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function of the formal partial derivative with respect to variabl
e `i`.
This is packaged as a derivation in `MvPowerSeries.pderiv`.
-/
noncomputable def pderivFun (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ coeff (d + single i 1) f * (d i + 1)
/-
**MvPowerSeries.coeff_pderivFun** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_pderivFun {i : σ} (f : MvPowerSeries σ R) (d : σ ->₀ Nat) : coeff d 
(f.pderivFun i) = coeff (d + single i 1) f * (d i + 1)
参数：f : MvPowerSeries σ R；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_pderivFun {i : σ} (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d i + 1) := by
  rfl
/-
**MvPowerSeries.pderivFun_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderivFun_add {i : σ} (f g : MvPowerSeries σ R) : pderivFun i (f + g) = pd
erivFun i f + pderivFun i g
参数：f g : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_pderivFun`：coeff_pderivFun {i : σ} (f : MvPowerSerie
s σ R) (d : σ ->₀ Nat) : coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d
 i + 1)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem pderivFun_add {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f + g) = pderivFun i f + pderivFun i g := by
  ext
  rw [coeff_pderivFun, map_add, map_add, coeff_pderivFun, coeff_pderivFun, add_mul]
/-
**MvPowerSeries.pderivFun_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderivFun_C {i : σ} (r : R) : pderivFun i (C r) = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_pderivFun`：coeff_pderivFun {i : σ} (f : MvPowerSerie
s σ R) (d : σ ->₀ Nat) : coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d
 i + 1)
· 使用定理 `MvPowerSeries.coeff_add_single_C`：coeff_add_single_C {m : Nat} [NeZero m
] {n : σ ->₀ Nat} (a : R) (i : σ) : coeff (n + single i m) (C a) = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem pderivFun_C {i : σ} (r : R) : pderivFun i (C r) = 0 := by
  ext n
  rw [coeff_pderivFun, coeff_add_single_C, zero_mul, (coeff n).map_zero]
/-
**MvPowerSeries.pderivFun_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderivFun_one {i : σ} : pderivFun i (1 : MvPowerSeries σ R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.pderivFun_C`：pderivFun_C {i : σ} (r : R) : pderivFun i (C 
r) = 0
-/
theorem pderivFun_one {i : σ} : pderivFun i (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one C, pderivFun_C (1 : R)]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-
**MvPowerSeries.pderivFun_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pderivFun_coe {i : σ} (f : MvPolynomial σ R) :
    (f : MvPowerSeries σ R).pderivFun i = f.pderiv i := by
  ext
  rw [coeff_pderivFun, coeff_coe, coeff_coe, coeff_pderiv]
/-
**MvPowerSeries.trunc_pderivFun** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem trunc_pderivFun [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    trunc R n (pderivFun i f) = pderiv i (trunc R (n + single i 1) f) := by
  ext
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_pderivFun, coeff_pderiv, coeff_trunc, if_pos (add_lt_add_left h _)]
  · rw [coeff_pderiv, coeff_trunc, if_neg ((add_lt_add_iff_right _).not.mpr h), zero_mul]

-- A special case of `pderivFun_mul`, used in its proof.
/-
**MvPowerSeries.pderivFun_coe_mul_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pderivFun_coe_mul_coe {i : σ} (f g : MvPolynomial σ R) :
    pderivFun i (f * g : MvPowerSeries σ R) = f * pderiv i g + g * pderiv i f := by
  rw [← coe_mul, pderivFun_coe, pderiv_mul, add_comm, mul_comm _ g, ← coe_mul, ← coe_mul,
    MvPolynomial.coe_add]
/-
**MvPowerSeries.pderivFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pderivFun_mul {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f * g) = f • g.pderivFun i + g • f.pderivFun i := by
  classical
  ext n
  have h₁ : n < n + single i 1 := lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₂ : n + single i 1 < n + single i 1 + single i 1 :=
    lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₃ : n < n + single i 1 + single i 1 := lt_trans h₁ h₂
  rw [coeff_pderivFun, map_add, ← coeff_trunc_mul_trunc_eq_coeff_mul _ _ _ h₂, smul_eq_mul,
    smul_eq_mul, ← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ g (f.pderivFun i) h₃ h₁,
    ← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ f (g.pderivFun i) h₃ h₁, trunc_pderivFun,
    trunc_pderivFun, ← coeff_coe, ← coeff_coe, ← coeff_coe, ← map_add, coe_mul, coe_mul, coe_mul,
    ← pderivFun_coe_mul_coe, coeff_pderivFun]
/-
**MvPowerSeries.pderivFun_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pderivFun_smul {i : σ} (r : R) (f : MvPowerSeries σ R) :
    pderivFun i (r • f) = r • pderivFun i f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, pderivFun_mul, pderivFun_C, smul_zero, add_zero, smul_eq_mul]

variable (R) in
/-- The formal partial derivative of a multivariate formal power series with respect to
variable `i`, as an `R`-derivation on `MvPowerSeries σ R`. -/
@[no_expose]
/-
**MvPowerSeries.pderiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) wher
e toFun
参数：i : σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Derivative.0.MvPowerSeries.pde
rivFun_smul`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] {i : σ} (r 
: R) (f : MvPowerSeries σ R),   MvPowerSeries.pderivFun i (r • f) = r • M…
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Derivative.0.MvPowerSeries.pde
rivFun_mul`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] {i : σ} (f g
 : MvPowerSeries σ R),   MvPowerSeries.pderivFun i (f * g) = f • MvPower…

--- 原说明 ---
The formal partial derivative of a multivariate formal power series with respect
 to
variable `i`, as an `R`-derivation on `MvPowerSeries σ R`.
-/
noncomputable def pderiv (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := pderivFun i
  map_add' := pderivFun_add
  map_smul' := pderivFun_smul
  map_one_eq_zero' := pderivFun_one
  leibniz' := pderivFun_mul
/-
**MvPowerSeries.pderiv_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] {i : σ} {r : R},  
 (MvPowerSeries.pderiv R i) (MvPowerSeries.C r) = 0
参数：MvPowerSeries.pderiv R i；MvPowerSeries.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderivFun_C`：pderivFun_C {i : σ} (r : R) : pderivFun i (C 
r) = 0
-/
@[simp] theorem pderiv_C {i : σ} {r : R} : pderiv R i (C r) = 0 := pderivFun_C r
/-
**MvPowerSeries.pderiv_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_one {i : σ} : pderiv R i 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_C`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemi
ring R] {i : σ} {r : R},   (MvPowerSeries.pderiv R i) (MvPowerSeries.C r) = 0
-/
theorem pderiv_one {i : σ} : pderiv R i 1 = 0 := pderiv_C
/-
**MvPowerSeries.coeff_pderiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_pderiv {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat) : coeff n (pd
eriv R i f) = coeff (n + single i 1) f * (n i + 1)
参数：f : MvPowerSeries σ R；n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_pderivFun`：coeff_pderivFun {i : σ} (f : MvPowerSerie
s σ R) (d : σ ->₀ Nat) : coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d
 i + 1)
-/
theorem coeff_pderiv {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1) :=
  coeff_pderivFun f n
/-
**MvPowerSeries.pderiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_coe {i : σ} (f : MvPolynomial σ R) : pderiv R i f = MvPolynomial.pd
eriv i f
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Derivative.0.MvPowerSeries.pde
rivFun_coe`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] {i : σ} (f :
 MvPolynomial σ R),   MvPowerSeries.pderivFun i ↑f = ↑((MvPolynomial.pde…
-/
theorem pderiv_coe {i : σ} (f : MvPolynomial σ R) :
    pderiv R i f = MvPolynomial.pderiv i f := pderivFun_coe f

@[simp]
/-
**MvPowerSeries.pderiv_X_self** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_X_self {i : σ} : pderiv R i (X i) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_pderiv`：coeff_pderiv {i : σ} (f : MvPowerSeries σ R)
 (n : σ ->₀ Nat) : coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `boole_mul`：boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (if P then 1 else 0) * a = if P then a else 0
· 使用定理 `MvPowerSeries.coeff_one`：coeff_one [DecidableEq σ] : coeff n (1 : MvPowe
rSeries σ R) = if n = 0 then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem pderiv_X_self {i : σ} : pderiv R i (X i) = 1 := by
  classical
  ext n
  simp only [coeff_pderiv, coeff_X, boole_mul, add_eq_right, coeff_one]
  split_ifs <;> simp_all

@[simp]
/-
**MvPowerSeries.pderiv_X_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_X_of_ne {i j : σ} (h : j != i) : pderiv R i (X j) = 0
参数：h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_pderiv`：coeff_pderiv {i : σ} (f : MvPowerSeries σ R)
 (n : σ ->₀ Nat) : coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `boole_mul`：boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (if P then 1 else 0) * a = if P then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finsupp.ne_iff`：ne_iff {f g : α ->₀ M} : f != g ↔ exists a, f a != g a
-/
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv R i (X j) = 0 := by
  classical
  ext n
  simpa only [coeff_pderiv, coeff_X, boole_mul, coeff_zero] using
    if_neg (ne_iff.mpr ⟨i, by grind [Finsupp.add_apply]⟩)
/-
**MvPowerSeries.pderiv_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_X [DecidableEq σ] (i j : σ) : pderiv R i (X j) = Pi.single (M
参数：i j : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.pderiv_X_self`：pderiv_X_self {i : σ} : pderiv R i (X i) = 
1
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv R i (X j) = Pi.single (M := fun _ => MvPowerSeries σ R) i 1 j := by
  by_cases h : i = j
  · subst h; simp only [pderiv_X_self, Pi.single_eq_same]
  · grind [pderiv_X_of_ne]
/-
**MvPowerSeries.trunc_pderiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc_pderiv [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Na
t) : trunc R n (pderiv R i f) = MvPolynomial.pderiv i (trunc R (n + single i 1) 
f)
参数：f : MvPowerSeries σ R；n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Derivative.0.MvPowerSeries.tru
nc_pderivFun`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] [inst_1 : 
DecidableEq σ] {i : σ} (f : MvPowerSeries σ R)   (n : σ →₀ ℕ),   (MvPowerS…
-/
theorem trunc_pderiv [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    trunc R n (pderiv R i f) = MvPolynomial.pderiv i (trunc R (n + single i 1) f) :=
  trunc_pderivFun ..

/-- The partial derivative of `g^n` equals `n * g^(n-1) * g'`. -/
/-
**MvPowerSeries.pderiv_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_pow {i : σ} (g : MvPowerSeries σ R) (n : Nat) : pderiv R i (g ^ n) 
= n * g ^ (n - 1) * pderiv R i g
参数：g : MvPowerSeries σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.leibniz_pow`：leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n -
 1) • D a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
The partial derivative of `g^n` equals `n * g^(n-1) * g'`.
-/
theorem pderiv_pow {i : σ} (g : MvPowerSeries σ R) (n : ℕ) :
    pderiv R i (g ^ n) = n * g ^ (n - 1) * pderiv R i g := by
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, mul_assoc]

end CommSemiring

/-- If `f` and `g` have the same constant term and all partial derivatives, then they are equal.

The `CommRing` assumption is needed because the proof uses `smul_right_inj`, which requires
cancellation of addition in `R`; `IsAddTorsionFree` alone does not suffice. -/
/-
**MvPowerSeries.pderiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.pderiv`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] [IsAddTorsionFree R] {
f g : MvPowerSeries σ R},   (∀ (i : σ), (MvPowerSeries.pderiv R i) f = (MvPowerS
eries.pderiv R i) g) →     MvPowerSeries.constantCoeff f = MvPowerSeries.constan
tCoeff g → f = g
参数：∀ (i : σ), (MvPowerSeries.pderiv R i) f = (MvPowerSeries.pderiv R i) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff :
 ⇑(coeff (R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finsupp.ne_iff`：ne_iff {f g : α ->₀ M} : f != g ↔ exists a, f a != g a
· 使用定理 `smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Modul
e.Is…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Finsupp.coe_tsub`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid 
α] [inst_1 : PartialOrder α] [inst_2 : CanonicallyOrderedAdd α]   [inst_3 : Sub 
α] [in…
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MvPowerSeries.coeff_pderiv`：coeff_pderiv {i : σ} (f : MvPowerSeries σ R)
 (n : σ ->₀ Nat) : coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)

--- 原说明 ---
If `f` and `g` have the same constant term and all partial derivatives, then the
y are equal.

The `CommRing` assumption is needed because the proof uses `smul_right_inj`, whi
ch requires
cancellation of addition in `R`; `IsAddTorsionFree` alone does not suffice.
-/
theorem pderiv.ext [CommRing R] [IsAddTorsionFree R] {f g : MvPowerSeries σ R}
    (hD : ∀ i, pderiv R i f = pderiv R i g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  by_cases h : n = 0
  · rw [h, coeff_zero_eq_constantCoeff, hc]
  obtain ⟨i, hi : n i ≠ 0⟩ := ne_iff.mp h
  have : single i 1 ≤ n := fun j ↦ by
    by_cases hj : j = i <;> grind [single_eq_same, single_eq_of_ne]
  have e := congr(coeff (n - single i 1) $(hD i))
  rwa [coeff_pderiv, coeff_pderiv, tsub_add_cancel_of_le this, coe_tsub, Pi.sub_apply,
    single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel,
    mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul, smul_right_inj hi] at e

@[simp]
/-
**MvPowerSeries.pderiv_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_inv {i : σ} [CommRing R] (f : (MvPowerSeries σ R)ˣ) : pderiv R i ↑f
⁻¹ = -(↑f⁻¹ : MvPowerSeries σ R) ^ 2 * pderiv R i f
参数：f : (MvPowerSeries σ R)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.leibniz_of_mul_eq_one`：leibniz_of_mul_eq_one {a b : A} (h : a
 * b = 1) : D a = -a ^ 2 • D b
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
theorem pderiv_inv {i : σ} [CommRing R] (f : (MvPowerSeries σ R)ˣ) :
    pderiv R i ↑f⁻¹ = -(↑f⁻¹ : MvPowerSeries σ R) ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_of_mul_eq_one f.inv_mul

@[simp]
/-
**MvPowerSeries.pderiv_invOf** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_invOf {i : σ} [CommRing R] (f : MvPowerSeries σ R) [Invertible f] :
 pderiv R i ⅟f = -⅟f ^ 2 * pderiv R i f
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.leibniz_invOf`：leibniz_invOf [Invertible a] : D (⅟a) = -⅟a ^ 
2 • D a
-/
theorem pderiv_invOf {i : σ} [CommRing R] (f : MvPowerSeries σ R) [Invertible f] :
    pderiv R i ⅟f = -⅟f ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_invOf f

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv (MvPowerSeries σ R)` for more general base rings `R`.
-/

@[simp]
/-
**MvPowerSeries.pderiv_inv'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：pderiv_inv' {i : σ} [Field R] (f : MvPowerSeries σ R) : pderiv R i f⁻¹ = -
f⁻¹ ^ 2 * pderiv R i f
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.inv_eq_zero`：inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0
 ↔ constantCoeff φ = 0
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `Derivation.leibniz_of_mul_eq_one`：leibniz_of_mul_eq_one {a b : A} (h : a
 * b = 1) : D a = -a ^ 2 • D b
· 使用定理 `MvPowerSeries.inv_mul_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ⁻¹ * φ = 
1

--- 原说明 ---
The following theorem is stated only in the case that `R` is a field. This is be
cause
there is currently no instance of `Inv (MvPowerSeries σ R)` for more general bas
e rings `R`.
-/
theorem pderiv_inv' {i : σ} [Field R] (f : MvPowerSeries σ R) :
    pderiv R i f⁻¹ = -f⁻¹ ^ 2 * pderiv R i f := by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact MvPowerSeries.inv_mul_cancel (h := h)

end MvPowerSeries

