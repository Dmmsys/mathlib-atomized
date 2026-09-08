/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm

/-!
# Gauss norm for power series

This file defines the Gauss norm for power series using the gaussNorm for multivariate power series.
Given a power series `f` in `R⟦X⟧`, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
defined as the supremum of the set of all values of `v (f.coeff i) * c ^ i` for all `i : ℕ`.

In case `f` is a polynomial, `v` is a non-negative function with `v 0 = 0` and `c ≥ 0`,
`f.gaussNorm v c` reduces to the Gauss norm defined in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`, see `Polynomial.gaussNorm_coe_powerSeries`.

## Main Definitions and Results
* Using `PowerSeries.gaussNorm_eq`, `PowerSeries.gaussNorm` is the supremum of the set of all values
  of `v (f.coeff i) * c ^ i` for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is
  a function and `c` is a real number.

* `PowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `PowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
  all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
  zero.

* `PowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `PowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * c ^ t` is bounded above (similarly for `g`), then
  the Gauss norm has the non-archimedean property.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R)

/-- Given a power series `f` in, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
  defined as the supremum of the set of all values of `v (coeff t f) * c ^ t` for all `t : ℕ`. -/
noncomputable
/-
**PowerSeries.gaussNorm** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev gaussNorm : ℝ := MvPowerSeries.gaussNorm v (fun _ => c) f
/-
**PowerSeries.gaussNorm_eq** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_eq : gaussNorm v c f = ⨆ i : Nat, v (f.coeff i) * c ^ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.uniqueEquiv_apply`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (a : α) [inst_1 : Subsingleton α] (f : α →₀ M),   (Finsupp.uniqueEquiv a) f =
 f a
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussNorm_eq : gaussNorm v c f = ⨆ i : ℕ, v (f.coeff i) * c ^ i := by
  refine Equiv.iSup_congr (Finsupp.uniqueEquiv ()) ?_
  intro x
  simp only [coeff, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit, Finsupp.prod_pow,
    Finset.univ_unique, Finset.prod_singleton, show (Finsupp.single () (x PUnit.unit)) = x by grind]

/-- We say `f` HasGaussNorm if the values `v (coeff t f) * c ^ t` is bounded above, that is
  `gaussNormC f` is finite. -/
/-
**PowerSeries.HasGaussNorm** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：HasGaussNorm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `f` HasGaussNorm if the values `v (coeff t f) * c ^ t` is bounded above, 
that is
  `gaussNormC f` is finite.
-/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t)))
/-
**PowerSeries.HasGaussNorm.hasMvGaussNorm** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries
.HasGaussNorm`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries 
R),   PowerSeries.HasGaussNorm v c f → MvPowerSeries.HasGaussNorm v (fun x => c)
 f
参数：v : R → ℝ；c : ℝ；f : PowerSeries R；fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Finsupp.uniqueEquiv_symm_apply`：∀ {α : Type u_1} {M : Type u_5} [inst : 
Zero M] (a : α) [inst_1 : Subsingleton α] (b : M),   (Finsupp.uniqueEquiv a).sym
m b = fun₀ | a => b
· 使用定理 `Finsupp.uniqueEquiv_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_5} [i
nst : Zero M] (a : α) [inst_1 : Subsingleton α] (m : M) (b : α),   ((Finsupp.uni
queEquiv a).symm m) b = m
· 使用定理 `Finsupp.uniqueEquiv_apply`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (a : α) [inst_1 : Subsingleton α] (f : α →₀ M),   (Finsupp.uniqueEquiv a) f =
 f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma HasGaussNorm.hasMvGaussNorm (h : HasGaussNorm v c f) :
    MvPowerSeries.HasGaussNorm v (fun _ ↦ c) f := by
  suffices (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t))) =
      Set.range fun t ↦ v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 ↦ c ^ x2 by
    simpa only [MvPowerSeries.HasGaussNorm, ← this]
  refine Set.ext (fun _ ↦ ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_singleton]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    use (Finsupp.uniqueEquiv ()).symm y
    simpa [coeff] using hy
  · intro h
    obtain ⟨y, hy⟩ := h
    use Finsupp.uniqueEquiv () y
    simpa [coeff, show (Finsupp.single () (y PUnit.unit)) = y by grind]

@[deprecated (since := "2026-05-06")]
alias HasGaussNorm.HasMvGaussNorm := HasGaussNorm.hasMvGaussNorm
/-
**PowerSeries.gaussNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0
参数：vZero : v 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.gaussNorm_zero`：gaussNorm_zero (vZero : v 0 = 0) : gaussNo
rm v c 0 = 0
-/
theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 :=
  MvPowerSeries.gaussNorm_zero v (fun _ ↦ c) vZero
/-
**PowerSeries.le_gaussNorm** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：le_gaussNorm (hbd : HasGaussNorm v c f) (t : Nat) : v (coeff t f) * c ^ t 
<= gaussNorm v c f
参数：hbd : HasGaussNorm v c f；t : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.gaussNorm_eq`：gaussNorm_eq : gaussNorm v c f = ⨆ i : Nat, v 
(f.coeff i) * c ^ i
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : ℕ) :
    v (coeff t f) * c ^ t ≤ gaussNorm v c f := by
  rw [gaussNorm_eq]
  apply le_ciSup hbd
/-
**PowerSeries.gaussNorm_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_nonneg (vNonneg : forall a, v a >= 0) : 0 <= gaussNorm v c f
参数：vNonneg : forall a, v a >= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.gaussNorm_nonneg`：gaussNorm_nonneg (vNonneg : forall a, v 
a >= 0) : 0 <= gaussNorm v c f
-/
lemma gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f :=
  MvPowerSeries.gaussNorm_nonneg v (fun _ ↦ c) f vNonneg
/-
**PowerSeries.gaussNorm_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : forall a, v a >= 0) (h_
eq_zero : forall x : R, v x = 0 -> x = 0) (hc : 0 < c) (hbd : HasGaussNorm v c f
) : gaussNorm v c f = 0 ↔ f = 0
参数：vZero : v 0 = 0；vNonneg : forall a, v a >= 0；h_eq_zero : forall x : R, v x = 
0 -> x = 0；hc : 0 < c；hbd : HasGaussNorm v c f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.gaussNorm_eq_zero_iff`：gaussNorm_eq_zero_iff (vZero : v 0 
= 0) (vNonneg : forall a, v a >= 0) (h_eq_zero : forall x : R, v x = 0 -> x = 0)
 (hc : forall i, 0 < c i)…
· 使用定理 `PowerSeries.HasGaussNorm.hasMvGaussNorm`：∀ {R : Type u_1} [inst : Semiri
ng R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R),   PowerSeries.HasGaussNorm v c f 
→ MvPowerSeries.HasGaussNorm …
-/
lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 :=
  MvPowerSeries.gaussNorm_eq_zero_iff v (fun _ ↦ c) f vZero vNonneg h_eq_zero
    (by grind) hbd.hasMvGaussNorm
/-
**PowerSeries.gaussNorm_add_le_max** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_add_le_max (g : PowerSeries R) (hc : 0 <= c) (vNonneg : forall a
, v a >= 0) (hv : forall x y, v (x + y) <= max (v x) (v y)) (hbfd : HasGaussNorm
 v c f) (hbgd : HasGaussNorm v c g) : gaussNorm v c (f + g) <= max (gaussNorm v 
c f) (gaussNorm v c g)
参数：g : PowerSeries R；hc : 0 <= c；vNonneg : forall a, v a >= 0；hv : forall x y, v
 (x + y) <= max (v x) (v y)；hbfd : HasGaussNorm v c f；hbgd : HasGaussNorm v c g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.gaussNorm_add_le_max`：gaussNorm_add_le_max (f g : MvPowerS
eries σ R) (hc : 0 <= c) (vNonneg : forall a, v a >= 0) (hv : IsNonarchimedean v
) (hbfd : HasGaussNorm v…
· 使用定理 `PowerSeries.HasGaussNorm.hasMvGaussNorm`：∀ {R : Type u_1} [inst : Semiri
ng R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R),   PowerSeries.HasGaussNorm v c f 
→ MvPowerSeries.HasGaussNorm …
-/
lemma gaussNorm_add_le_max (g : PowerSeries R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) :=
  MvPowerSeries.gaussNorm_add_le_max v (fun _ ↦ c) f g (fun _ => by simp [hc]) vNonneg hv
    hbfd.hasMvGaussNorm hbgd.hasMvGaussNorm

end PowerSeries

