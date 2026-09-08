/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Univariate restricted power series

`IsRestricted` : We say a univariate power series over a normed ring `R` is restricted for a
real number `c` if `‖coeff t f‖ * c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section
namespace PowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] (c : ℝ) (f : PowerSeries R)

/-- Predicate for when `f` is a restricted power series. -/
/-
**PowerSeries.IsRestricted** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：IsRestricted
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for when `f` is a restricted power series.
-/
abbrev IsRestricted :=
  MvPowerSeries.IsRestricted (σ := Unit) (fun _ ↦ c) f
/-
**PowerSeries.isRestricted_comp_uniqueEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeri
es`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isRestricted_comp_uniqueEquiv :
    (fun (t : Unit →₀ ℕ) ↦ ‖MvPowerSeries.coeff t f‖ * t.prod (fun _ x ↦ c ^ x)) =
    (fun (n : ℕ) ↦ ‖coeff n f‖ * c ^ n) ∘ Finsupp.uniqueEquiv () := by
  funext t
  simp only [Function.comp_apply, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit,
    Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
    show (Finsupp.single () (t ())) = t by grind]
/-
**PowerSeries.isRestricted_iff** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_iff : IsRestricted c f ↔ Tendsto (fun (t : Nat) => ‖coeff t f
‖ * c ^ t) cofinite (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsRestricted.eq_1`：∀ {R : Type u_1} [inst : NormedRing R] (c
 : ℝ) (f : PowerSeries R),   PowerSeries.IsRestricted c f = MvPowerSeries.IsRest
ricted (fun x => c)…
· 使用定理 `MvPowerSeries.IsRestricted.eq_1`：∀ {R : Type u_1} [inst : NormedRing R] 
{σ : Type u_2} (c : σ → ℝ) (f : MvPowerSeries σ R),   MvPowerSeries.IsRestricted
 c f =     Filter.Ten…
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `_private.Mathlib.RingTheory.PowerSeries.Restricted.0.PowerSeries.isRestr
icted_comp_uniqueEquiv`：∀ {R : Type u_1} [inst : NormedRing R] (c : ℝ) (f : Powe
rSeries R),   (fun t => ‖(MvPowerSeries.coeff t) f‖ * t.prod fun x x_1 => c ^ x_
1) =…
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.uniqueEquiv_symm_apply`：∀ {α : Type u_1} {M : Type u_5} [inst : 
Zero M] (a : α) [inst_1 : Subsingleton α] (b : M),   (Finsupp.uniqueEquiv a).sym
m b = fun₀ | a => b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.uniqueEquiv_apply`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (a : α) [inst_1 : Subsingleton α] (f : α →₀ M),   (Finsupp.uniqueEquiv a) f =
 f a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma isRestricted_iff : IsRestricted c f ↔
    Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) cofinite (𝓝 0) := by
  rw [IsRestricted, MvPowerSeries.IsRestricted, isRestricted_comp_uniqueEquiv]
  exact ⟨fun H ↦ (H.comp (Finsupp.uniqueEquiv ()).symm.injective.tendsto_cofinite).congr fun n ↦
    by simp, fun H ↦ H.comp (Finsupp.uniqueEquiv ()).injective.tendsto_cofinite⟩
/-
**PowerSeries.isRestricted_iff'** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_iff' : IsRestricted c f ↔ Tendsto (fun (t : Nat) => ‖coeff t 
f‖ * c ^ t) atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isRestricted_iff' : IsRestricted c f ↔
    Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) atTop (𝓝 0) := by
  simp_rw [isRestricted_iff, Nat.cofinite_eq_atTop]

@[simp]
/-
**PowerSeries.isRestricted_abs_iff** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_abs_iff : IsRestricted |c| f ↔ IsRestricted c f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_abs_iff`：isRestricted_abs_iff (c : σ -> Real)
 (f : MvPowerSeries σ R) : IsRestricted |c| f ↔ IsRestricted c f
-/
lemma isRestricted_abs_iff : IsRestricted |c| f ↔ IsRestricted c f :=
  MvPowerSeries.isRestricted_abs_iff (fun _ ↦ c) f
/-
**PowerSeries.isRestricted_zero** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_zero : IsRestricted c (0 : PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_zero`：isRestricted_zero (c : σ -> Real) : IsR
estricted c (0 : MvPowerSeries σ R)
-/
lemma isRestricted_zero : IsRestricted c (0 : PowerSeries R) :=
 MvPowerSeries.isRestricted_zero (fun _ ↦ c)
/-
**PowerSeries.isRestricted_monomial** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_monomial (n : Nat) (a : R) : IsRestricted c (monomial n a)
参数：n : Nat；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_monomial`：isRestricted_monomial (c : σ -> Rea
l) (n : σ ->₀ Nat) (a : R) : IsRestricted c (monomial n a)
-/
lemma isRestricted_monomial (n : ℕ) (a : R) : IsRestricted c (monomial n a) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) ((Finsupp.single () n)) a
/-
**PowerSeries.isRestricted_one** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_one : IsRestricted c (1 : PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_monomial`：isRestricted_monomial (c : σ -> Rea
l) (n : σ ->₀ Nat) (a : R) : IsRestricted c (monomial n a)
-/
lemma isRestricted_one : IsRestricted c (1 : PowerSeries R) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) 0 1
/-
**PowerSeries.isRestricted_C** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：isRestricted_C (a : R) : IsRestricted c (C a)
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_C`：isRestricted_C (c : σ -> Real) (a : R) : I
sRestricted c (C a)
-/
lemma isRestricted_C (a : R) : IsRestricted c (C a) :=
  MvPowerSeries.isRestricted_C (fun _ ↦ c) a

variable {f} in
/-
**PowerSeries.isRestricted.add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.isRestrict
ed`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] (c : ℝ) {f g : PowerSeries R},   Po
werSeries.IsRestricted c f → PowerSeries.IsRestricted c g → PowerSeries.IsRestri
cted c (f + g)
参数：c : ℝ；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isRestricted.add`：∀ {R : Type u_1} [inst : NormedRing R] {
σ : Type u_2} (c : σ → ℝ) {f g : MvPowerSeries σ R},   MvPowerSeries.IsRestricte
d c f → MvPowerSerie…
-/
lemma isRestricted.add {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) :=
  MvPowerSeries.isRestricted.add (fun _ ↦ c) hf hg

variable {f} in
/-
**PowerSeries.isRestricted.neg** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.isRestrict
ed`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] (c : ℝ) {f : PowerSeries R},   Powe
rSeries.IsRestricted c f → PowerSeries.IsRestricted c (-f)
参数：c : ℝ；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isRestricted.neg`：∀ {R : Type u_1} [inst : NormedRing R] {
σ : Type u_2} (c : σ → ℝ) {f : MvPowerSeries σ R},   MvPowerSeries.IsRestricted 
c f → MvPowerSeries.…
-/
lemma isRestricted.neg (hf : IsRestricted c f) : IsRestricted c (-f) :=
  MvPowerSeries.isRestricted.neg (fun _ ↦ c) hf
/-
**PowerSeries.isRestricted.mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.isRestrict
ed`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] [IsUltrametricDist R] (c : ℝ) {f g 
: PowerSeries R},   PowerSeries.IsRestricted c f → PowerSeries.IsRestricted c g 
→ PowerSeries.IsRestricted c (f * g)
参数：c : ℝ；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isRestricted.mul`：∀ {R : Type u_1} [inst : NormedRing R] {
σ : Type u_2} [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R},   MvP
owerSeries.IsRestric…
-/
lemma isRestricted.mul [IsUltrametricDist R] (c : ℝ) {f g : PowerSeries R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) :=
  MvPowerSeries.isRestricted.mul (fun _ ↦ c) hf hg

namespace IsRestricted

/-- Restricted power series as an additive subgroup of `PowerSeries R`. -/
/-
**PowerSeries.IsRestricted.addSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.Is
Restricted`。
形式化陈述：addSubgroup (c : Real) : AddSubgroup (PowerSeries R)
参数：c : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricted power series as an additive subgroup of `PowerSeries R`.
-/
def addSubgroup (c : ℝ) : AddSubgroup (PowerSeries R) :=
  MvPowerSeries.IsRestricted.addSubgroup (fun _ ↦ c)

variable [IsUltrametricDist R]

/-- Restricted power series as an subring of `PowerSeries R`. -/
/-
**PowerSeries.IsRestricted.subring** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.IsRest
ricted`。
形式化陈述：subring (c : Real) : Subring (PowerSeries R)
参数：c : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricted power series as an subring of `PowerSeries R`.
-/
def subring (c : ℝ) :  Subring (PowerSeries R) :=
  MvPowerSeries.IsRestricted.subring (fun _ ↦ c)

end PowerSeries.IsRestricted

