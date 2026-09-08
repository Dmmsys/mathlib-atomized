/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Schröder Numbers Power Series

This file defines lemmas and theorems about the power series for large and small Schröder numbers.

## Main Definitions
* `PowerSeries.largeSchroderSeries`: The power series for large Schröder numbers.
* `PowerSeries.smallSchroderSeries`: The power series for small Schröder numbers.

## Main Results
* `largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`:
  The functional equation for the large Schröder numbers power series.

## TODO

* Prove the small Schröder numbers power series.

-/

@[expose] public section

open Finset Nat

namespace PowerSeries

/-- The power series for large Schröder numbers -/
/-
**PowerSeries.largeSchroderSeries** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：largeSchroderSeries : PowerSeries Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series for large Schröder numbers
-/
def largeSchroderSeries : PowerSeries ℕ :=
  PowerSeries.mk largeSchroder

@[simp]
/-
**PowerSeries.coeff_largeSchroderSeries** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_largeSchroderSeries (n : Nat) : (coeff n) largeSchroderSeries = larg
eSchroder n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_largeSchroderSeries (n : ℕ) :
    (coeff n) largeSchroderSeries = largeSchroder n := by
  simp [largeSchroderSeries]

@[simp]
/-
**PowerSeries.constantCoeff_largeSchroderSeries** 是 Mathlib 中的一个引理，位于命名空间 `Power
Series`。
形式化陈述：constantCoeff_largeSchroderSeries : constantCoeff largeSchroderSeries = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.coeff_largeSchroderSeries`：coeff_largeSchroderSeries (n : Na
t) : (coeff n) largeSchroderSeries = largeSchroder n
· 使用定理 `Nat.largeSchroder_zero`：Nat.largeSchroder 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma constantCoeff_largeSchroderSeries :
    constantCoeff largeSchroderSeries = 1 := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_largeSchroderSeries, largeSchroder_zero]

@[simp]
/-
**PowerSeries.coeff_X_mul_largeSchroderSeries** 是 Mathlib 中的一个引理，位于命名空间 `PowerSe
ries`。
形式化陈述：coeff_X_mul_largeSchroderSeries (n : Nat) (hn : 0 < n) : coeff n (X * larg
eSchroderSeries) = largeSchroder (n - 1)
参数：n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `PowerSeries.coeff_largeSchroderSeries`：coeff_largeSchroderSeries (n : Na
t) : (coeff n) largeSchroderSeries = largeSchroder n
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma coeff_X_mul_largeSchroderSeries (n : ℕ) (hn : 0 < n) :
    coeff n (X * largeSchroderSeries) = largeSchroder (n - 1) := by
  simp only [coeff_mul, coeff_largeSchroderSeries,
    Nat.sum_antidiagonal_eq_sum_range_succ (coeff · X * largeSchroder ·),
    succ_eq_add_one]
  simp only [coeff_X, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, lt_add_iff_pos_left,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  rintro rfl
  simp_all only [lt_self_iff_false]
/-
**PowerSeries.coeff_X_mul_largeSchroderSeriesSeries_sq** 是 Mathlib 中的一个引理，位于命名空间
 `PowerSeries`。
形式化陈述：coeff_X_mul_largeSchroderSeriesSeries_sq (n : Nat) (hn : 0 < n) : coeff n 
(X * largeSchroderSeries ^ 2) = ∑ i in range n, largeSchroder i * largeSchroder 
(n - 1 - i)
参数：n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `PowerSeries.coeff_largeSchroderSeries`：coeff_largeSchroderSeries (n : Na
t) : (coeff n) largeSchroderSeries = largeSchroder n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PowerSeries.coeff_X_mul_largeSchroderSeries`：coeff_X_mul_largeSchroderSe
ries (n : Nat) (hn : 0 < n) : coeff n (X * largeSchroderSeries) = largeSchroder 
(n - 1)
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.largeSchroder_zero`：Nat.largeSchroder 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用引理 `PowerSeries.constantCoeff_largeSchroderSeries`：constantCoeff_largeSchrod
erSeries : constantCoeff largeSchroderSeries = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 38 条，此处仅展示前 30 条）
-/
lemma coeff_X_mul_largeSchroderSeriesSeries_sq (n : ℕ) (hn : 0 < n) :
    coeff n (X * largeSchroderSeries ^ 2) =
      ∑ i ∈ range n, largeSchroder i * largeSchroder (n - 1 - i) := by
  rw [pow_two, ← mul_assoc, coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * largeSchroderSeries) * (coeff y) largeSchroderSeries) n,
    Nat.succ_eq_add_one, sum_range_succ]
  simp only [coeff_largeSchroderSeries, coeff_X_mul_largeSchroderSeries n hn, tsub_self,
    largeSchroder_zero, mul_one]
  have : ∑ x ∈ range n, (coeff x) (X * largeSchroderSeries) * largeSchroder (n - x) =
      ∑ x ∈ range n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [coeff_X_mul_largeSchroderSeries x (by lia)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, constantCoeff_largeSchroderSeries, mul_one, tsub_zero, zero_mul]
  rw [this, sum_range_eq_add_Ico _ (by lia)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x ∈ Ico 1 n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0) =
    ∑ x ∈ Ico 1 n, largeSchroder (x - 1) * largeSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    have hx' : 0 < x := by grind
    rw [if_pos hx']
  rw [this, sum_Ico_eq_sum_range, show n = n - 1 + 1 by lia,
    sum_range_succ]
  grind [largeSchroder_zero]
/-
**PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul
_largeSchroderSeries_sq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSc
hroderSeries_sq : largeSchroderSeries = 1 + X * largeSchroderSeries + X * largeS
chroderSeries ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.coeff_largeSchroderSeries`：coeff_largeSchroderSeries (n : Na
t) : (coeff n) largeSchroderSeries = largeSchroder n
· 使用定理 `Nat.largeSchroder_zero`：Nat.largeSchroder 0 = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用引理 `PowerSeries.constantCoeff_largeSchroderSeries`：constantCoeff_largeSchrod
erSeries : constantCoeff largeSchroderSeries = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
（共 43 条，此处仅展示前 30 条）
-/
theorem largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq :
    largeSchroderSeries = 1 + X * largeSchroderSeries + X * largeSchroderSeries ^ 2 := by
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp only [coeff_largeSchroderSeries, map_add, coeff_one, hn, ↓reduceIte, zero_add]
    rw [coeff_X_mul_largeSchroderSeriesSeries_sq _ hn', coeff_X_mul_largeSchroderSeries _ hn',
      show n = n - 1 + 1 by omega, largeSchroder_succ (n - 1)]
    simp only [add_tsub_cancel_right, Nat.add_left_cancel_iff]
    rw [Iic_eq_Icc, Nat.bot_eq_zero, ← range_succ_eq_Icc_zero]

end PowerSeries

