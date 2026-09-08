/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Data.ENat.Lattice

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` for
the construction.)

Formal (univariate) power series over a local ring form a local ring.

Formal (univariate) power series over a field form a discrete valuation ring, and a normalization
monoid. The definition `residueFieldOfPowerSeries` provides the isomorphism between the residue
field of `k⟦X⟧` and `k`, when `k` is a field.

-/

@[expose] public section


noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}


section Ring

variable [Ring R]

/-- Auxiliary function used for computing inverse of a power series -/
/-
**PowerSeries.inv.aux** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.inv`。
形式化陈述：{R : Type u_1} → [Ring R] → R → PowerSeries R → PowerSeries R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function used for computing inverse of a power series
-/
protected def inv.aux : R → R⟦X⟧ → R⟦X⟧ :=
  MvPowerSeries.inv.aux
/-
**PowerSeries.coeff_inv_aux** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_inv_aux (n : Nat) (a : R) (φ : R⟦X⟧) : coeff n (inv.aux a φ) = if n 
= 0 then a else -a * ∑ x in antidiagonal n, if x.2 < n then coeff x.1 φ * coeff 
x.2 (inv.aux a φ) else 0
参数：n : Nat；a : R；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `PowerSeries.inv.aux.eq_1`：∀ {R : Type u_1} [inst : Ring R], PowerSeries.
inv.aux = MvPowerSeries.inv.aux
· 使用定理 `MvPowerSeries.coeff_inv_aux`：coeff_inv_aux [DecidableEq σ] (n : σ ->₀ Na
t) (a : R) (φ : MvPowerSeries σ R) : coeff n (inv.aux a φ) = if n = 0 then a els
e -a * ∑ x in ant…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
· 使用定理 `Finsupp.antidiagonal_single`：antidiagonal_single (a : α) (n : Nat) : ant
idiagonal (single a n) = (antidiagonal n).map (Function.Embedding.prodMap ⟨_, si
ngle_injective a⟩…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
（共 35 条，此处仅展示前 30 条）
-/
theorem coeff_inv_aux (n : ℕ) (a : R) (φ : R⟦X⟧) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 := by
  rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) ↦ (single () a, single () b))
    fun (f, g) ↦ (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
    obtain H | H := le_or_gt n j
    · aesop
    rw [if_pos H, if_pos]
    · rfl
    refine ⟨?_, fun hh ↦ H.not_ge ?_⟩
    · rintro ⟨⟩
      simpa [Finsupp.single_eq_same] using le_of_lt H
    · simpa [Finsupp.single_eq_same] using hh ()

/-- A formal power series is invertible if the constant coefficient is invertible. -/
/-
**PowerSeries.invOfUnit** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧
参数：φ : R⟦X⟧；u : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A formal power series is invertible if the constant coefficient is invertible.
-/
def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u
/-
**PowerSeries.coeff_invOfUnit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_invOfUnit (n : Nat) (φ : R⟦X⟧) (u : Rˣ) : coeff n (invOfUnit φ u) = 
if n = 0 then ↑u⁻¹ else -↑u⁻¹ * ∑ x in antidiagonal n, if x.2 < n then coeff x.1
 φ * coeff x.2 (invOfUnit φ u) else 0
参数：n : Nat；φ : R⟦X⟧；u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_inv_aux`：coeff_inv_aux (n : Nat) (a : R) (φ : R⟦X⟧) : 
coeff n (inv.aux a φ) = if n = 0 then a else -a * ∑ x in antidiagonal n, if x.2 
< n then coeff …
-/
theorem coeff_invOfUnit (n : ℕ) (φ : R⟦X⟧) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ

@[simp]
/-
**PowerSeries.constantCoeff_invOfUnit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_invOfUnit (φ : R⟦X⟧) (u : Rˣ) : constantCoeff (invOfUnit φ u
) = ↑u⁻¹
参数：φ : R⟦X⟧；u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantCoe
ff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
· 使用定理 `PowerSeries.coeff_invOfUnit`：coeff_invOfUnit (n : Nat) (φ : R⟦X⟧) (u : R
ˣ) : coeff n (invOfUnit φ u) = if n = 0 then ↑u⁻¹ else -↑u⁻¹ * ∑ x in antidiagon
al n, if x.2 < n …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem constantCoeff_invOfUnit (φ : R⟦X⟧) (u : Rˣ) :
    constantCoeff (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]

@[simp]
/-
**PowerSeries.mul_invOfUnit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) : φ * invOfUni
t φ u = 1
参数：φ : R⟦X⟧；u : Rˣ；h : constantCoeff φ = u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : φ * invOfUnit φ u = 1
-/
theorem mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    φ * invOfUnit φ u = 1 :=
  MvPowerSeries.mul_invOfUnit φ u <| h

@[simp]
/-
**PowerSeries.invOfUnit_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invOfUnit_mul (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) : invOfUnit φ 
u * φ = 1
参数：φ : R⟦X⟧；u : Rˣ；h : constantCoeff φ = u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.invOfUnit_mul`：invOfUnit_mul (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : invOfUnit φ u * φ = 1
-/
theorem invOfUnit_mul (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u * φ = 1 :=
  MvPowerSeries.invOfUnit_mul φ u h
/-
**PowerSeries.isUnit_iff_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：isUnit_iff_constantCoeff {φ : R⟦X⟧} : IsUnit φ ↔ IsUnit (constantCoeff φ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isUnit_iff_constantCoeff`：isUnit_iff_constantCoeff {φ : Mv
PowerSeries σ R} : IsUnit φ ↔ IsUnit (constantCoeff φ)
-/
theorem isUnit_iff_constantCoeff {φ : R⟦X⟧} :
    IsUnit φ ↔ IsUnit (constantCoeff φ) :=
  MvPowerSeries.isUnit_iff_constantCoeff

/-- Two ways of removing the constant coefficient of a power series are the same. -/
/-
**PowerSeries.sub_const_eq_shift_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：sub_const_eq_shift_mul_X (φ : R⟦X⟧) : φ - C (constantCoeff φ) = (mk fun p 
=> coeff (p + 1) φ) * X
参数：φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `PowerSeries.eq_shift_mul_X_add_const`：eq_shift_mul_X_add_const (φ : R⟦X⟧
) : φ = (mk fun p => coeff (p + 1) φ) * X + C (constantCoeff φ)

--- 原说明 ---
Two ways of removing the constant coefficient of a power series are the same.
-/
theorem sub_const_eq_shift_mul_X (φ : R⟦X⟧) :
    φ - C (constantCoeff φ) = (mk fun p ↦ coeff (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)
/-
**PowerSeries.sub_const_eq_X_mul_shift** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：sub_const_eq_X_mul_shift (φ : R⟦X⟧) : φ - C (constantCoeff φ) = X * mk fun
 p => coeff (p + 1) φ
参数：φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `PowerSeries.eq_X_mul_shift_add_const`：eq_X_mul_shift_add_const (φ : R⟦X⟧
) : φ = (X * mk fun p => coeff (p + 1) φ) + C (constantCoeff φ)
-/
theorem sub_const_eq_X_mul_shift (φ : R⟦X⟧) :
    φ - C (constantCoeff φ) = X * mk fun p ↦ coeff (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

end Ring

section Field

variable {k : Type*} [Field k]

/-- The inverse 1/f of a power series f defined over a field -/
/-
**PowerSeries.inv** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：{k : Type u_2} → [Field k] → PowerSeries k → PowerSeries k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse 1/f of a power series f defined over a field
-/
protected abbrev inv : k⟦X⟧ → k⟦X⟧ :=
  MvPowerSeries.inv
/-
**PowerSeries.inv_eq_inv_aux** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：inv_eq_inv_aux (φ : k⟦X⟧) : φ⁻¹ = inv.aux (constantCoeff φ)⁻¹ φ
参数：φ : k⟦X⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_eq_inv_aux (φ : k⟦X⟧) : φ⁻¹ = inv.aux (constantCoeff φ)⁻¹ φ :=
  rfl
/-
**PowerSeries.coeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_inv (n) (φ : k⟦X⟧) : coeff n φ⁻¹ = if n = 0 then (constantCoeff φ)⁻¹
 else -(constantCoeff φ)⁻¹ * ∑ x in antidiagonal n, if x.2 < n then coeff x.1 φ 
* coeff x.2 φ⁻¹ else 0
参数：n；φ : k⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.inv_eq_inv_aux`：inv_eq_inv_aux (φ : k⟦X⟧) : φ⁻¹ = inv.aux (c
onstantCoeff φ)⁻¹ φ
· 使用定理 `PowerSeries.coeff_inv_aux`：coeff_inv_aux (n : Nat) (a : R) (φ : R⟦X⟧) : 
coeff n (inv.aux a φ) = if n = 0 then a else -a * ∑ x in antidiagonal n, if x.2 
< n then coeff …
-/
theorem coeff_inv (n) (φ : k⟦X⟧) :
    coeff n φ⁻¹ =
      if n = 0 then (constantCoeff φ)⁻¹
      else
        -(constantCoeff φ)⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0 := by
  rw [inv_eq_inv_aux, coeff_inv_aux n (constantCoeff φ)⁻¹ φ]

@[simp]
/-
**PowerSeries.constantCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_inv (φ : k⟦X⟧) : constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹
参数：φ : k⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.constantCoeff_inv`：constantCoeff_inv (φ : MvPowerSeries σ 
k) : constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹
-/
theorem constantCoeff_inv (φ : k⟦X⟧) : constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹ :=
  MvPowerSeries.constantCoeff_inv φ
/-
**PowerSeries.inv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：inv_eq_zero {φ : k⟦X⟧} : φ⁻¹ = 0 ↔ constantCoeff φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.inv_eq_zero`：inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0
 ↔ constantCoeff φ = 0
-/
theorem inv_eq_zero {φ : k⟦X⟧} : φ⁻¹ = 0 ↔ constantCoeff φ = 0 :=
  MvPowerSeries.inv_eq_zero
/-
**PowerSeries.zero_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：zero_inv : (0 : k⟦X⟧)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.zero_inv`：zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0
-/
theorem zero_inv : (0 : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.zero_inv

@[simp]
/-
**PowerSeries.invOfUnit_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invOfUnit_eq (φ : k⟦X⟧) (h : constantCoeff φ != 0) : invOfUnit φ (Units.mk
0 _ h) = φ⁻¹
参数：φ : k⟦X⟧；h : constantCoeff φ != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invOfUnit_eq (φ : k⟦X⟧) (h : constantCoeff φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl

@[simp]
/-
**PowerSeries.invOfUnit_eq'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invOfUnit_eq' (φ : k⟦X⟧) (u : Units k) (h : constantCoeff φ = u) : invOfUn
it φ u = φ⁻¹
参数：φ : k⟦X⟧；u : Units k；h : constantCoeff φ = u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.invOfUnit_eq'`：invOfUnit_eq' (φ : MvPowerSeries σ k) (u : 
Units k) (h : constantCoeff φ = u) : invOfUnit φ u = φ⁻¹
-/
theorem invOfUnit_eq' (φ : k⟦X⟧) (u : Units k) (h : constantCoeff φ = u) :
    invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq' φ _ h

@[simp]
/-
**PowerSeries.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {k : Type u_2} [inst : Field k] (φ : PowerSeries k), PowerSeries.constan
tCoeff φ ≠ 0 → φ * φ⁻¹ = 1
参数：φ : PowerSeries k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.mul_inv_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ * φ⁻¹ = 
1
-/
protected theorem mul_inv_cancel (φ : k⟦X⟧) (h : constantCoeff φ ≠ 0) : φ * φ⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel φ h

@[simp]
/-
**PowerSeries.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {k : Type u_2} [inst : Field k] (φ : PowerSeries k), PowerSeries.constan
tCoeff φ ≠ 0 → φ⁻¹ * φ = 1
参数：φ : PowerSeries k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.inv_mul_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ⁻¹ * φ = 
1
-/
protected theorem inv_mul_cancel (φ : k⟦X⟧) (h : constantCoeff φ ≠ 0) : φ⁻¹ * φ = 1 :=
  MvPowerSeries.inv_mul_cancel φ h
/-
**PowerSeries.eq_mul_inv_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : k⟦X⟧} (h : constantCoeff φ₃ != 0) : φ₁ =
 φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂
参数：h : constantCoeff φ₃ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.eq_mul_inv_iff_mul_eq`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ₁ φ₂ φ₃ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff φ₃ ≠
 0 → (φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁…
-/
theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : k⟦X⟧} (h : constantCoeff φ₃ ≠ 0) :
    φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h
/-
**PowerSeries.eq_inv_iff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：eq_inv_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0) : φ = ψ⁻¹ ↔ 
φ * ψ = 1
参数：h : constantCoeff ψ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.eq_inv_iff_mul_eq_one`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ ψ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff ψ ≠ 0 → (
φ = ψ⁻¹ ↔ φ * ψ = 1)
-/
theorem eq_inv_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h
/-
**PowerSeries.inv_eq_iff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：inv_eq_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0) : ψ⁻¹ = φ ↔ 
φ * ψ = 1
参数：h : constantCoeff ψ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.inv_eq_iff_mul_eq_one`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ ψ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff ψ ≠ 0 → (
ψ⁻¹ = φ ↔ φ * ψ = 1)
-/
theorem inv_eq_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h
/-
**PowerSeries.mul_inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {k : Type u_2} [inst : Field k] (φ ψ : PowerSeries k), (φ * ψ)⁻¹ = ψ⁻¹ *
 φ⁻¹
参数：φ ψ : PowerSeries k；φ * ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.mul_inv_rev`：∀ {σ : Type u_1} {k : Type u_3} [inst : Field
 k] (φ ψ : MvPowerSeries σ k), (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹
-/
protected theorem mul_inv_rev (φ ψ : k⟦X⟧) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _

@[simp]
/-
**PowerSeries.C_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：C_inv (r : k) : (C r)⁻¹ = C r⁻¹
参数：r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.C_inv`：C_inv (r : k) : (C (σ
-/
theorem C_inv (r : k) : (C r)⁻¹ = C r⁻¹ :=
  MvPowerSeries.C_inv _

@[simp]
/-
**PowerSeries.X_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_inv : (X : k⟦X⟧)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.X_inv`：X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0
-/
theorem X_inv : (X : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.X_inv _
/-
**PowerSeries.smul_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：smul_inv (r : k) (φ : k⟦X⟧) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹
参数：r : k；φ : k⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.smul_inv`：smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • 
φ)⁻¹ = r⁻¹ • φ⁻¹
-/
theorem smul_inv (r : k) (φ : k⟦X⟧) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _

/-- `firstUnitCoeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
  field. It is obtained using `divided_by_X_pow_order`, defined in `PowerSeries.Order`. -/
/-
**PowerSeries.firstUnitCoeff** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：firstUnitCoeff {f : k⟦X⟧} (hf : f != 0) : kˣ
参数：hf : f != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`firstUnitCoeff` is the non-zero coefficient whose index is `f.order`, seen as a
 unit of the
  field. It is obtained using `divided_by_X_pow_order`, defined in `PowerSeries.
Order`.
-/
def firstUnitCoeff {f : k⟦X⟧} (hf : f ≠ 0) : kˣ :=
  have : Invertible (constantCoeff (divXPowOrder f)) := by
    apply invertibleOfNonzero
    simpa [constantCoeff_divXPowOrder_eq_zero_iff.not]
  unitOfInvertible (constantCoeff (divXPowOrder f))

/-- `Inv_divided_by_X_pow_order` is the inverse of the element obtained by diving a non-zero power
series by the largest power of `X` dividing it. Useful to create a term of type `Units`, done in
`Unit_divided_by_X_pow_order` -/
/-
**PowerSeries.Inv_divided_by_X_pow_order** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`
。
形式化陈述：Inv_divided_by_X_pow_order {f : k⟦X⟧} (hf : f != 0) : k⟦X⟧
参数：hf : f != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Inv_divided_by_X_pow_order` is the inverse of the element obtained by diving a 
non-zero power
series by the largest power of `X` dividing it. Useful to create a term of type 
`Units`, done in
`Unit_divided_by_X_pow_order`
-/
def Inv_divided_by_X_pow_order {f : k⟦X⟧} (hf : f ≠ 0) : k⟦X⟧ :=
  invOfUnit (divXPowOrder f) (firstUnitCoeff hf)

@[simp]
/-
**PowerSeries.Inv_divided_by_X_pow_order_rightInv** 是 Mathlib 中的一个定理，位于命名空间 `Pow
erSeries`。
形式化陈述：Inv_divided_by_X_pow_order_rightInv {f : k⟦X⟧} (hf : f != 0) : divXPowOrde
r f * Inv_divided_by_X_pow_order hf = 1
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : consta
ntCoeff φ = u) : φ * invOfUnit φ u = 1
-/
theorem Inv_divided_by_X_pow_order_rightInv {f : k⟦X⟧} (hf : f ≠ 0) :
    divXPowOrder f * Inv_divided_by_X_pow_order hf = 1 :=
  mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

@[simp]
/-
**PowerSeries.Inv_divided_by_X_pow_order_leftInv** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：Inv_divided_by_X_pow_order_leftInv {f : k⟦X⟧} (hf : f != 0) : Inv_divided_
by_X_pow_order hf * divXPowOrder f = 1
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : consta
ntCoeff φ = u) : φ * invOfUnit φ u = 1
-/
theorem Inv_divided_by_X_pow_order_leftInv {f : k⟦X⟧} (hf : f ≠ 0) :
    Inv_divided_by_X_pow_order hf * divXPowOrder f = 1 := by
  rw [mul_comm]
  exact mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

open scoped Classical in
/-- `Unit_of_divided_by_X_pow_order` is the unit power series obtained by dividing a non-zero
power series by the largest power of `X` that divides it. -/
/-
**PowerSeries.Unit_of_divided_by_X_pow_order** 是 Mathlib 中的一个定义，位于命名空间 `PowerSer
ies`。
形式化陈述：Unit_of_divided_by_X_pow_order (f : k⟦X⟧) : k⟦X⟧ˣ
参数：f : k⟦X⟧。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_rightInv`：Inv_divided_by_X_pow_or
der_rightInv {f : k⟦X⟧} (hf : f != 0) : divXPowOrder f * Inv_divided_by_X_pow_or
der hf = 1
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_leftInv`：Inv_divided_by_X_pow_ord
er_leftInv {f : k⟦X⟧} (hf : f != 0) : Inv_divided_by_X_pow_order hf * divXPowOrd
er f = 1

--- 原说明 ---
`Unit_of_divided_by_X_pow_order` is the unit power series obtained by dividing a
 non-zero
power series by the largest power of `X` that divides it.
-/
def Unit_of_divided_by_X_pow_order (f : k⟦X⟧) : k⟦X⟧ˣ :=
  if hf : f = 0 then 1
  else
    { val := divXPowOrder f
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }
/-
**PowerSeries.isUnit_divided_by_X_pow_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeri
es`。
形式化陈述：isUnit_divided_by_X_pow_order {f : k⟦X⟧} (hf : f != 0) : IsUnit (divXPowOr
der f)
参数：hf : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_rightInv`：Inv_divided_by_X_pow_or
der_rightInv {f : k⟦X⟧} (hf : f != 0) : divXPowOrder f * Inv_divided_by_X_pow_or
der hf = 1
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_leftInv`：Inv_divided_by_X_pow_ord
er_leftInv {f : k⟦X⟧} (hf : f != 0) : Inv_divided_by_X_pow_order hf * divXPowOrd
er f = 1
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isUnit_divided_by_X_pow_order {f : k⟦X⟧} (hf : f ≠ 0) :
    IsUnit (divXPowOrder f) :=
  ⟨Unit_of_divided_by_X_pow_order f,
    by simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]⟩
/-
**PowerSeries.Unit_of_divided_by_X_pow_order_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries`。
形式化陈述：Unit_of_divided_by_X_pow_order_nonzero {f : k⟦X⟧} (hf : f != 0) : ↑(Unit_o
f_divided_by_X_pow_order f) = divXPowOrder f
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_rightInv`：Inv_divided_by_X_pow_or
der_rightInv {f : k⟦X⟧} (hf : f != 0) : divXPowOrder f * Inv_divided_by_X_pow_or
der hf = 1
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_leftInv`：Inv_divided_by_X_pow_ord
er_leftInv {f : k⟦X⟧} (hf : f != 0) : Inv_divided_by_X_pow_order hf * divXPowOrd
er f = 1
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Unit_of_divided_by_X_pow_order_nonzero {f : k⟦X⟧} (hf : f ≠ 0) :
    ↑(Unit_of_divided_by_X_pow_order f) = divXPowOrder f := by
  simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]

@[simp]
/-
**PowerSeries.Unit_of_divided_by_X_pow_order_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pow
erSeries`。
形式化陈述：Unit_of_divided_by_X_pow_order_zero : Unit_of_divided_by_X_pow_order (0 : 
k⟦X⟧) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_rightInv`：Inv_divided_by_X_pow_or
der_rightInv {f : k⟦X⟧} (hf : f != 0) : divXPowOrder f * Inv_divided_by_X_pow_or
der hf = 1
· 使用定理 `PowerSeries.Inv_divided_by_X_pow_order_leftInv`：Inv_divided_by_X_pow_ord
er_leftInv {f : k⟦X⟧} (hf : f != 0) : Inv_divided_by_X_pow_order hf * divXPowOrd
er f = 1
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem Unit_of_divided_by_X_pow_order_zero : Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1 := by
  simp only [Unit_of_divided_by_X_pow_order, dif_pos]
/-
**PowerSeries.eq_divided_by_X_pow_order_Iff_Unit** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：eq_divided_by_X_pow_order_Iff_Unit {f : k⟦X⟧} (hf : f != 0) : f = divXPowO
rder f ↔ IsUnit f
参数：hf : f != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.isUnit_divided_by_X_pow_order`：isUnit_divided_by_X_pow_order
 {f : k⟦X⟧} (hf : f != 0) : IsUnit (divXPowOrder f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.order_zero_of_unit`：order_zero_of_unit {f : R⟦X⟧} : IsUnit f
 -> f.order = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.X_pow_order_mul_divXPowOrder`：X_pow_order_mul_divXPowOrder {
f : R⟦X⟧} : X ^ f.order.toNat * divXPowOrder f = f
· 使用定理 `ENat.toNat_zero`：toNat_zero : toNat 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem eq_divided_by_X_pow_order_Iff_Unit {f : k⟦X⟧} (hf : f ≠ 0) :
    f = divXPowOrder f ↔ IsUnit f :=
  ⟨fun h ↦ by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h ↦ by
    have : f.order = 0 := by
      simp [order_zero_of_unit h]
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f), this, ENat.toNat_zero,
      pow_zero, one_mul]⟩

end Field

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f]

@[instance]
/-
**PowerSeries.map.isLocalHom** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.map`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
(f : R →+* S) [IsLocalHom f],   IsLocalHom (PowerSeries.map f)
参数：f : R →+* S；PowerSeries.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.map.isLocalHom`：∀ {σ : Type u_1} {R : Type u_2} {S : Type 
u_3} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S) [IsLocalHom f],   I
sLocalHom (MvPower…
-/
theorem map.isLocalHom : IsLocalHom (map f) :=
  MvPowerSeries.map.isLocalHom f

end IsLocalRing

section IsDiscreteValuationRing

variable {k : Type*} [Field k]

open IsDiscreteValuationRing

/-
**PowerSeries.hasUnitMulPowIrreducibleFactorization** 是 Mathlib 中的一个定理，位于命名空间 `P
owerSeries`。
形式化陈述：hasUnitMulPowIrreducibleFactorization : HasUnitMulPowIrreducibleFactorizat
ion k⟦X⟧
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.X_irreducible`：X_irreducible : Irreducible (X : R⟦X⟧)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.Unit_of_divided_by_X_pow_order_nonzero`：Unit_of_divided_by_X
_pow_order_nonzero {f : k⟦X⟧} (hf : f != 0) : ↑(Unit_of_divided_by_X_pow_order f
) = divXPowOrder f
· 使用定理 `PowerSeries.X_pow_order_mul_divXPowOrder`：X_pow_order_mul_divXPowOrder {
f : R⟦X⟧} : X ^ f.order.toNat * divXPowOrder f = f
-/
theorem hasUnitMulPowIrreducibleFactorization :
    HasUnitMulPowIrreducibleFactorization k⟦X⟧ :=
  ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.toNat
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact X_pow_order_mul_divXPowOrder)⟩
/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniqueFactorizationMonoid k⟦X⟧ :=
  hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid
/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscreteValuationRing k⟦X⟧ :=
  ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization
/-
**PowerSeries.** 是 Mathlib 中的一个示例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsNoetherianRing k⟦X⟧ := inferInstance

/-- The maximal ideal of `k⟦X⟧` is generated by `X`. -/
/-
**PowerSeries.maximalIdeal_eq_span_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：maximalIdeal_eq_span_X : IsLocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Prime.not_dvd_one`：not_dvd_one : ¬p ∣ 1
· 使用定理 `PowerSeries.X_prime`：X_prime : Prime (X : R⟦X⟧)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `PowerSeries.X_dvd_iff`：X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantC
oeff φ = 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `PowerSeries.constantCoeff_C`：constantCoeff_C (a : R) : constantCoeff (C 
a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantCoe
ff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `MvPowerSeries.instIsLocalRing`：∀ {σ : Type u_1} {R : Type u_2} [inst : C
ommRing R] [IsLocalRing R], IsLocalRing (MvPowerSeries σ R)
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationRing.of_field`：∀ (K : Type u) [inst : Field K], ValuationRing K
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R

--- 原说明 ---
The maximal ideal of `k⟦X⟧` is generated by `X`.
-/
theorem maximalIdeal_eq_span_X : IsLocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X} := by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton, X_dvd_iff] at hfX
      have hfI0 : C (f 0) ∈ I := by
        have : C (f 0) = f - (f - C (f 0)) := by rw [sub_sub_cancel]
        rw [this]
        apply Ideal.sub_mem I hfI
        apply hI
        rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, ←
          coeff_zero_eq_constantCoeff_apply, sub_eq_zero, coeff_zero_eq_constantCoeff]
        rfl
      rw [← Ideal.eq_top_iff_one]
      apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map C (Ne.isUnit hfX))
  rw [IsLocalRing.eq_maximalIdeal hX]
/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StrongNormalizationMonoid k⟦X⟧ where
  normUnit f := (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul hf hg := by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf, Unit_of_divided_by_X_pow_order_nonzero hg,
      Units.ext_iff, Units.val_mul, ← divXPowOrder_mul]
  normUnit_coe_units u := by
    set u₀ := u.1 with hu
    have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
    rw [inv_inj, Units.ext_iff, ← hu, Unit_of_divided_by_X_pow_order_nonzero h₀.ne_zero]
    exact ((eq_divided_by_X_pow_order_Iff_Unit h₀.ne_zero).mpr h₀).symm
/-
**PowerSeries.normUnit_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：normUnit_X : normUnit (X : k⟦X⟧) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.Unit_of_divided_by_X_pow_order_nonzero`：Unit_of_divided_by_X
_pow_order_nonzero {f : k⟦X⟧} (hf : f != 0) : ↑(Unit_of_divided_by_X_pow_order f
) = divXPowOrder f
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `PowerSeries.divXPowOrder_X`：divXPowOrder_X : divXPowOrder X = (1 : R⟦X⟧)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normUnit_X : normUnit (X : k⟦X⟧) = 1 := by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]
/-
**PowerSeries.X_eq_normalizeX** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_eq_normalizeX : (X : k⟦X⟧) = normalize X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.normUnit_X`：normUnit_X : normUnit (X : k⟦X⟧) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem X_eq_normalizeX : (X : k⟦X⟧) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

open UniqueFactorizationMonoid

open scoped Classical in
/-
**PowerSeries.normalized_count_X_eq_of_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：normalized_count_X_eq_of_coe {P : k[X]} (hP : P != 0) : Multiset.count Pow
erSeries.X (normalizedFactors (P : k⟦X⟧)) = Multiset.count Polynomial.X (normali
zedFactors P)
参数：hP : P != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `PowerSeries.instUniqueFactorizationMonoid`：∀ {k : Type u_2} [inst : Fiel
d k], UniqueFactorizationMonoid (PowerSeries k)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Polynomial.X_eq_normalize`：X_eq_normalize : X = normalize (X : R[X])
· 使用定理 `PowerSeries.X_eq_normalizeX`：X_eq_normalizeX : (X : k⟦X⟧) = normalize X
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Polynomial.irreducible_X`：irreducible_X : Irreducible (X : R[X])
· 使用定理 `PowerSeries.X_irreducible`：X_irreducible : Irreducible (X : R⟦X⟧)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 31 条，此处仅展示前 30 条）
-/
theorem normalized_count_X_eq_of_coe {P : k[X]} (hP : P ≠ 0) :
    Multiset.count PowerSeries.X (normalizedFactors (P : k⟦X⟧)) =
      Multiset.count Polynomial.X (normalizedFactors P) := by
  apply eq_of_forall_le_iff
  simp only [← Nat.cast_le (α := ℕ∞)]
  rw [X_eq_normalize, PowerSeries.X_eq_normalizeX, ← emultiplicity_eq_count_normalizedFactors
    irreducible_X hP, ← emultiplicity_eq_count_normalizedFactors X_irreducible] <;>
  simp only [← pow_dvd_iff_le_emultiplicity, Polynomial.X_pow_dvd_iff,
    PowerSeries.X_pow_dvd_iff, Polynomial.coeff_coe P, implies_true, ne_eq, coe_eq_zero_iff, hP,
    not_false_eq_true]

open IsLocalRing
/-
**PowerSeries.ker_coeff_eq_max_ideal** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：ker_coeff_eq_max_ideal : RingHom.ker (constantCoeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `MvPowerSeries.instIsLocalRing`：∀ {σ : Type u_1} {R : Type u_2} [inst : C
ommRing R] [IsLocalRing R], IsLocalRing (MvPowerSeries σ R)
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationRing.of_field`：∀ (K : Type u) [inst : Field K], ValuationRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `PowerSeries.maximalIdeal_eq_span_X`：maximalIdeal_eq_span_X : IsLocalRing
.maximalIdeal (k⟦X⟧) = Ideal.span {X}
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `PowerSeries.X_dvd_iff`：X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantC
oeff φ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_coeff_eq_max_ideal : RingHom.ker (constantCoeff (R := k)) = maximalIdeal _ :=
  Ideal.ext fun _ ↦ by
    rw [RingHom.mem_ker, maximalIdeal_eq_span_X, Ideal.mem_span_singleton, X_dvd_iff]

/-- The ring isomorphism between the residue field of the ring of power series valued in a field `K`
and `K` itself. -/
/-
**PowerSeries.residueFieldOfPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：residueFieldOfPowerSeries : ResidueField k⟦X⟧ ≃+* k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring isomorphism between the residue field of the ring of power series value
d in a field `K`
and `K` itself.
-/
def residueFieldOfPowerSeries : ResidueField k⟦X⟧ ≃+* k :=
  Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm |>.trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

end IsDiscreteValuationRing


end PowerSeries

end

