/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Formal (multivariate) power series - Inverses

This file defines multivariate formal power series and develops the basic
properties of these objects, when it comes about multiplicative inverses.

For `φ : MvPowerSeries σ R` and `u : Rˣ` is the constant coefficient of `φ`,
`MvPowerSeries.invOfUnit φ u` is a formal power series such,
and `MvPowerSeries.mul_invOfUnit` proves that `φ * invOfUnit φ u = 1`.
The construction of the power series `invOfUnit` is done by writing that
relation and solving and for its coefficients by induction.

Over a field, all power series `φ` have an “inverse” `MvPowerSeries.inv φ`,
which is `0` if and only if the constant coefficient of `φ` is zero
(by `MvPowerSeries.inv_eq_zero`),
and `MvPowerSeries.mul_inv_cancel` asserts the equality `φ * φ⁻¹ = 1` when
the constant coefficient of `φ` is nonzero.

Instances are defined:

* Formal power series over a local ring form a local ring.
* The morphism `MvPowerSeries.map σ f : MvPowerSeries σ A →* MvPowerSeries σ B`
  induced by a local morphism `f : A →+* B` (`IsLocalHom f`)
  of commutative rings is a *local* morphism.

-/

@[expose] public section


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Ring

variable [Ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coefficients of the inverse.
-/
/-- Auxiliary definition that unifies
the totalised inverse formal power series `(_)⁻¹` and
the inverse formal power series that depends on
an inverse of the constant coefficient `invOfUnit`. -/
/-
**MvPowerSeries.inv.aux** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries.inv`。
形式化陈述：{σ : Type u_1} → {R : Type u_2} → [Ring R] → R → MvPowerSeries σ R → MvPow
erSeries σ R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition that unifies
the totalised inverse formal power series `(_)⁻¹` and
the inverse formal power series that depends on
an inverse of the constant coefficient `invOfUnit`.
-/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    letI := Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x ∈ antidiagonal n, if _ : x.2 < n then coeff x.1 φ * inv.aux a φ x.2 else 0
termination_by n => n
/-
**MvPowerSeries.coeff_inv_aux** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_inv_aux [DecidableEq σ] (n : σ ->₀ Nat) (a : R) (φ : MvPowerSeries σ
 R) : coeff n (inv.aux a φ) = if n = 0 then a else -a * ∑ x in antidiagonal n, i
f x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0
参数：n : σ ->₀ Nat；a : R；φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.inv.aux.eq_1`：∀ {σ : Type u_1} {R : Type u_2} [inst : Ring
 R] (a : R) (φ : MvPowerSeries σ R) (x : σ →₀ ℕ),   MvPowerSeries.inv.aux a φ x 
=     if x = 0 t…
-/
theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl

/-- A multivariate formal power series is invertible if the constant coefficient is invertible. -/
/-
**MvPowerSeries.invOfUnit** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R
参数：φ : MvPowerSeries σ R；u : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multivariate formal power series is invertible if the constant coefficient is 
invertible.
-/
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ
/-
**MvPowerSeries.coeff_invOfUnit** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_invOfUnit [DecidableEq σ] (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (u
 : Rˣ) : coeff n (invOfUnit φ u) = if n = 0 then ↑u⁻¹ else -↑u⁻¹ * ∑ x in antidi
agonal n, if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0
参数：n : σ ->₀ Nat；φ : MvPowerSeries σ R；u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPowerSeries.coeff_inv_aux`：coeff_inv_aux [DecidableEq σ] (n : σ ->₀ Na
t) (a : R) (φ : MvPowerSeries σ R) : coeff n (inv.aux a φ) = if n = 0 then a els
e -a * ∑ x in ant…
-/
theorem coeff_invOfUnit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 := by
  convert! coeff_inv_aux n (↑u⁻¹) φ

@[simp]
/-
**MvPowerSeries.constantCoeff_invOfUnit** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : constantCoeff (
invOfUnit φ u) = ↑u⁻¹
参数：φ : MvPowerSeries σ R；u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `MvPowerSeries.coeff_invOfUnit`：coeff_invOfUnit [DecidableEq σ] (n : σ ->
₀ Nat) (φ : MvPowerSeries σ R) (u : Rˣ) : coeff n (invOfUnit φ u) = if n = 0 the
n ↑u⁻¹ else -↑u⁻¹ *…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) :
    constantCoeff (invOfUnit φ u) = ↑u⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]

@[simp]
/-
**MvPowerSeries.mul_invOfUnit** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
 φ * invOfUnit φ u = 1
参数：φ : MvPowerSeries σ R；u : Rˣ；h : constantCoeff φ = u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPowerSeries.constantCoeff_invOfUnit`：constantCoeff_invOfUnit (φ : MvPo
werSeries σ R) (u : Rˣ) : constantCoeff (invOfUnit φ u) = ↑u⁻¹
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPowerSeries.coeff_one`：coeff_one [DecidableEq σ] : coeff n (1 : MvPowe
rSeries σ R) = if n = 0 then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `MvPowerSeries.coeff_invOfUnit`：coeff_invOfUnit [DecidableEq σ] (n : σ ->
₀ Nat) (φ : MvPowerSeries σ R) (u : Rˣ) : coeff n (invOfUnit φ u) = if n = 0 the
n ↑u⁻¹ else -↑u⁻¹ *…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
（共 47 条，此处仅展示前 30 条）
-/
theorem mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    φ * invOfUnit φ u = 1 :=
  ext fun n =>
    letI := Classical.decEq (σ →₀ ℕ)
    if H : n = 0 then by
      rw [H]
      simp [h]
    else by
      classical
      have : ((0 : σ →₀ ℕ), n) ∈ antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one, if_neg H, coeff_mul, ← Finset.insert_erase this,
        Finset.sum_insert (Finset.notMem_erase _ _), coeff_zero_eq_constantCoeff_apply, h,
        coeff_invOfUnit, if_neg H, neg_mul, mul_neg, Units.mul_inv_cancel_left, ←
        Finset.insert_erase this, Finset.sum_insert (Finset.notMem_erase _ _),
        Finset.insert_erase this, if_neg (not_lt_of_ge <| le_rfl), zero_add, add_comm, ←
        sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase, mem_antidiagonal] at hij
      obtain ⟨h₁, rfl⟩ := hij
      rw [if_pos]
      refine lt_add_of_pos_left _ <| pos_iff_ne_zero.2 ?_
      rintro rfl
      simp at h₁

-- TODO : can one prove equivalence?
@[simp]
/-
**MvPowerSeries.invOfUnit_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：invOfUnit_mul (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
 invOfUnit φ u * φ = 1
参数：φ : MvPowerSeries σ R；u : Rˣ；h : constantCoeff φ = u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_cancel_right_mem_nonZeroDivisors`：mul_cancel_right_mem_nonZeroDiviso
rs (hr : r in R⁰) : x * r = y * r ↔ x = y
· 使用定理 `MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff`：mem_nonZeroDivisors_
of_constantCoeff {φ : MvPowerSeries σ R} (hφ : constantCoeff φ in R⁰) : φ in (Mv
PowerSeries σ R)⁰
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.constantCoeff_invOfUnit`：constantCoeff_invOfUnit (φ : MvPo
werSeries σ R) (u : Rˣ) : constantCoeff (invOfUnit φ u) = ↑u⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MvPowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : φ * invOfUnit φ u = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem invOfUnit_mul (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u * φ = 1 := by
  rw [← mul_cancel_right_mem_nonZeroDivisors (r := φ.invOfUnit u), mul_assoc, one_mul,
    mul_invOfUnit _ _ h, mul_one]
  apply mem_nonZeroDivisors_of_constantCoeff
  simp only [constantCoeff_invOfUnit, IsUnit.mem_nonZeroDivisors (Units.isUnit u⁻¹)]
/-
**MvPowerSeries.isUnit_iff_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：isUnit_iff_constantCoeff {φ : MvPowerSeries σ R} : IsUnit φ ↔ IsUnit (cons
tantCoeff φ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : φ * invOfUnit φ u = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.invOfUnit_mul`：invOfUnit_mul (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : invOfUnit φ u * φ = 1
-/
theorem isUnit_iff_constantCoeff {φ : MvPowerSeries σ R} :
    IsUnit φ ↔ IsUnit (constantCoeff φ) := by
  constructor
  · exact IsUnit.map _
  · intro ⟨u, hu⟩
    exact ⟨⟨_, φ.invOfUnit u, mul_invOfUnit φ u hu.symm, invOfUnit_mul φ u hu.symm⟩, rfl⟩

end Ring

section CommRing

variable [CommRing R]

/-- Multivariate formal power series over a local ring form a local ring. -/
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multivariate formal power series over a local ring form a local ring.
-/
instance [IsLocalRing R] : IsLocalRing (MvPowerSeries σ R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self <| by
    intro φ
    obtain ⟨u, h⟩ | ⟨u, h⟩ := IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff φ) <;>
        [left; right] <;>
      · refine .of_mul_eq_one _ (mul_invOfUnit _ u ?_)
        simpa using h.symm

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRing

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f]

-- Thanks to the linter for informing us that this instance does
-- not actually need R and S to be local rings!
/-- The map between multivariate formal power series over the same indexing set
induced by a local ring hom `A → B` is local -/
@[instance]
/-
**MvPowerSeries.map.isLocalHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.map`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} {S : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] (f : R →+* S) [IsLocalHom f],   IsLocalHom (MvPowerSeries.map f)
参数：f : R →+* S；MvPowerSeries.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MvPowerSeries.isUnit_constantCoeff`：isUnit_constantCoeff (φ : MvPowerSer
ies σ R) (h : IsUnit φ) : IsUnit (constantCoeff φ)
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_map`：constantCoeff_map (φ : MvPowerSeries σ 
R) : constantCoeff (map f φ) = f (constantCoeff φ)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `MvPowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : φ * invOfUnit φ u = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The map between multivariate formal power series over the same indexing set
induced by a local ring hom `A → B` is local
-/
theorem map.isLocalHom : IsLocalHom (map (σ := σ) f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg constantCoeff h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff ψ.val) := isUnit_constantCoeff _ ψ.isUnit
    rw [h] at this
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    exact .of_mul_eq_one (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩

end IsLocalRing

section Field

open MvPowerSeries

variable {k : Type*} [Field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
/-
**MvPowerSeries.inv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：{σ : Type u_1} → {k : Type u_3} → [Field k] → MvPowerSeries σ k → MvPowerS
eries σ k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse `1/f` of a multivariable power series `f` over a field
-/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  inv.aux (constantCoeff φ)⁻¹ φ
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩
/-
**MvPowerSeries.coeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_inv [DecidableEq σ] (n : σ ->₀ Nat) (φ : MvPowerSeries σ k) : coeff 
n φ⁻¹ = if n = 0 then (constantCoeff φ)⁻¹ else -(constantCoeff φ)⁻¹ * ∑ x in ant
idiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0
参数：n : σ ->₀ Nat；φ : MvPowerSeries σ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_inv_aux`：coeff_inv_aux [DecidableEq σ] (n : σ ->₀ Na
t) (a : R) (φ : MvPowerSeries σ R) : coeff n (inv.aux a φ) = if n = 0 then a els
e -a * ∑ x in ant…
-/
theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ k) :
    coeff n φ⁻¹ =
      if n = 0 then (constantCoeff φ)⁻¹
      else
        -(constantCoeff φ)⁻¹ *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0 :=
  coeff_inv_aux n _ φ

@[simp]
/-
**MvPowerSeries.constantCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_inv (φ : MvPowerSeries σ k) : constantCoeff φ⁻¹ = (constantC
oeff φ)⁻¹
参数：φ : MvPowerSeries σ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `MvPowerSeries.coeff_inv`：coeff_inv [DecidableEq σ] (n : σ ->₀ Nat) (φ : 
MvPowerSeries σ k) : coeff n φ⁻¹ = if n = 0 then (constantCoeff φ)⁻¹ else -(cons
tantCoeff φ)⁻…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem constantCoeff_inv (φ : MvPowerSeries σ k) :
    constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_inv, if_pos rfl]
/-
**MvPowerSeries.inv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_inv`：constantCoeff_inv (φ : MvPowerSeries σ 
k) : constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `MvPowerSeries.coeff_inv`：coeff_inv [DecidableEq σ] (n : σ ->₀ Nat) (φ : 
MvPowerSeries σ k) : coeff n φ⁻¹ = if n = 0 then (constantCoeff φ)⁻¹ else -(cons
tantCoeff φ)⁻…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff φ = 0 :=
  ⟨fun h => by simpa using congr_arg constantCoeff h, fun h =>
    ext fun n => by
      classical
      rw [coeff_inv]
      split_ifs <;>
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩

@[simp]
/-
**MvPowerSeries.zero_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.inv_eq_zero`：inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0
 ↔ constantCoeff φ = 0
· 使用定理 `MvPowerSeries.constantCoeff_zero`：constantCoeff_zero : constantCoeff (0 
: MvPowerSeries σ R) = 0
-/
theorem zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_zero]

@[simp]
/-
**MvPowerSeries.invOfUnit_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0) : invOfUni
t φ (Units.mk0 _ h) = φ⁻¹
参数：φ : MvPowerSeries σ k；h : constantCoeff φ != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl

@[simp]
/-
**MvPowerSeries.invOfUnit_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：invOfUnit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff φ =
 u) : invOfUnit φ u = φ⁻¹
参数：φ : MvPowerSeries σ k；u : Units k；h : constantCoeff φ = u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.invOfUnit_eq`：invOfUnit_eq (φ : MvPowerSeries σ k) (h : co
nstantCoeff φ != 0) : invOfUnit φ (Units.mk0 _ h) = φ⁻¹
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
-/
theorem invOfUnit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff φ = u) :
    invOfUnit φ u = φ⁻¹ := by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  apply congrArg (invOfUnit φ)
  rw [Units.ext_iff]
  exact h.symm

@[simp]
/-
**MvPowerSeries.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {k : Type u_3} [inst : Field k] (φ : MvPowerSeries σ k), 
  MvPowerSeries.constantCoeff φ ≠ 0 → φ * φ⁻¹ = 1
参数：φ : MvPowerSeries σ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.invOfUnit_eq`：invOfUnit_eq (φ : MvPowerSeries σ k) (h : co
nstantCoeff φ != 0) : invOfUnit φ (Units.mk0 _ h) = φ⁻¹
· 使用定理 `MvPowerSeries.mul_invOfUnit`：mul_invOfUnit (φ : MvPowerSeries σ R) (u : 
Rˣ) (h : constantCoeff φ = u) : φ * invOfUnit φ u = 1
-/
protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff φ ≠ 0) :
    φ * φ⁻¹ = 1 := by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]

@[simp]
/-
**MvPowerSeries.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {k : Type u_3} [inst : Field k] (φ : MvPowerSeries σ k), 
  MvPowerSeries.constantCoeff φ ≠ 0 → φ⁻¹ * φ = 1
参数：φ : MvPowerSeries σ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MvPowerSeries.mul_inv_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ * φ⁻¹ = 
1
-/
protected theorem inv_mul_cancel (φ : MvPowerSeries σ k) (h : constantCoeff φ ≠ 0) :
    φ⁻¹ * φ = 1 := by rw [mul_comm, φ.mul_inv_cancel h]
/-
**MvPowerSeries.eq_mul_inv_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {k : Type u_3} [inst : Field k] {φ₁ φ₂ φ₃ : MvPowerSeries
 σ k},   MvPowerSeries.constantCoeff φ₃ ≠ 0 → (φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂)
参数：φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MvPowerSeries.inv_mul_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ⁻¹ * φ = 
1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.mul_inv_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ * φ⁻¹ = 
1
-/
protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
    (h : constantCoeff φ₃ ≠ 0) : φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩
/-
**MvPowerSeries.eq_inv_iff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {k : Type u_3} [inst : Field k] {φ ψ : MvPowerSeries σ k}
,   MvPowerSeries.constantCoeff ψ ≠ 0 → (φ = ψ⁻¹ ↔ φ * ψ = 1)
参数：φ = ψ⁻¹ ↔ φ * ψ = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.eq_mul_inv_iff_mul_eq`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ₁ φ₂ φ₃ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff φ₃ ≠
 0 → (φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 := by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]
/-
**MvPowerSeries.inv_eq_iff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {k : Type u_3} [inst : Field k] {φ ψ : MvPowerSeries σ k}
,   MvPowerSeries.constantCoeff ψ ≠ 0 → (ψ⁻¹ = φ ↔ φ * ψ = 1)
参数：ψ⁻¹ = φ ↔ φ * ψ = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MvPowerSeries.eq_inv_iff_mul_eq_one`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ ψ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff ψ ≠ 0 → (
φ = ψ⁻¹ ↔ φ * ψ = 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 := by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]

@[simp]
/-
**MvPowerSeries.mul_inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {k : Type u_3} [inst : Field k] (φ ψ : MvPowerSeries σ k)
, (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹
参数：φ ψ : MvPowerSeries σ k；φ * ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPowerSeries.inv_eq_zero`：inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0
 ↔ constantCoeff φ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPowerSeries.inv_eq_iff_mul_eq_one`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ ψ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff ψ ≠ 0 → (
ψ⁻¹ = φ ↔ φ * ψ = 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MvPowerSeries.inv_mul_cancel`：∀ {σ : Type u_1} {k : Type u_3} [inst : Fi
eld k] (φ : MvPowerSeries σ k),   MvPowerSeries.constantCoeff φ ≠ 0 → φ⁻¹ * φ = 
1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem mul_inv_rev (φ ψ : MvPowerSeries σ k) :
    (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ := by
  by_cases h : constantCoeff (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [map_mul, mul_eq_zero] at h
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    rcases h with h | h <;> simp [inv_eq_zero.mpr h]
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [not_or, map_mul, mul_eq_zero] at h
    rw [← mul_assoc, mul_assoc _⁻¹, MvPowerSeries.inv_mul_cancel _ h.left, mul_one,
      MvPowerSeries.inv_mul_cancel _ h.right]
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvOneClass (MvPowerSeries σ k) :=
  { (inferInstance : One (MvPowerSeries σ k)),
    (inferInstance : Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one, mul_one]
      simp }

@[simp]
/-
**MvPowerSeries.C_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：C_inv (r : k) : (C (σ
参数：r : k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.zero_inv`：zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.inv_eq_iff_mul_eq_one`：∀ {σ : Type u_1} {k : Type u_3} [in
st : Field k] {φ ψ : MvPowerSeries σ k},   MvPowerSeries.constantCoeff ψ ≠ 0 → (
ψ⁻¹ = φ ↔ φ * ψ = 1)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem C_inv (r : k) : (C (σ := σ) r)⁻¹ = C r⁻¹ := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ← map_mul, inv_mul_cancel₀ hr, map_one]
  simpa using hr

@[simp]
/-
**MvPowerSeries.X_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.inv_eq_zero`：inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0
 ↔ constantCoeff φ = 0
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
-/
theorem X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_X]

@[simp]
/-
**MvPowerSeries.smul_inv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹
参数：r : k；φ : MvPowerSeries σ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.smul_eq_C_mul`：smul_eq_C_mul (f : MvPowerSeries σ R) (a : 
R) : a • f = C a * f
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MvPowerSeries.mul_inv_rev`：∀ {σ : Type u_1} {k : Type u_3} [inst : Field
 k] (φ ψ : MvPowerSeries σ k), (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.C_inv`：C_inv (r : k) : (C (σ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ := by
  simp [smul_eq_C_mul, mul_comm]

end Field

end MvPowerSeries

end

