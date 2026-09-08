/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Factorized Rational Functions

This file discusses functions `𝕜 → 𝕜` of the form `∏ᶠ u, (· - u) ^ d u`, where `d : 𝕜 → ℤ` is
integer-valued. We show that these "factorized rational functions" are meromorphic in normal form,
with divisor equal to `d`.

Under suitable assumptions, we show that meromorphic functions are equivalent, modulo equality on
codiscrete sets, to the product of a factorized rational function and an analytic function without
zeros.

Implementation Note: For consistency, we use `∏ᶠ u, (· - u) ^ d u` throughout. If the support of `d`
is finite, then evaluation of functions commutes with finprod, and the helper lemma
`Function.FactorizedRational.finprod_eval` asserts that `∏ᶠ u, (· - u) ^ d u` equals the function
`fun x ↦ ∏ᶠ u, (x - u) ^ d u`. If `d` has infinite support, this equality is wrong in general.
There are elementary examples of functions `d` where `∏ᶠ u, (· - u) ^ d u` is constant one, while
`fun x ↦ ∏ᶠ u, (x - u) ^ d u` is not continuous.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜}

open Filter Function Real Set

namespace Function.FactorizedRational

/-!
## Elementary Properties of Factorized Rational Functions
-/

/--
Helper Lemma: Identify the support of `d` as the mulsupport of the product defining the factorized
rational function.
-/
/-
**Function.FactorizedRational.mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fac
torizedRational`。
形式化陈述：mulSupport (d : 𝕜 -> Int) : (fun u => (· - u) ^ d u).mulSupport = d.suppor
t
参数：d : 𝕜 -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Helper Lemma: Identify the support of `d` as the mulsupport of the product defin
ing the factorized
rational function.
-/
lemma mulSupport (d : 𝕜 → ℤ) :
    (fun u ↦ (· - u) ^ d u).mulSupport = d.support := by
  ext u
  constructor <;> intro h
  · simp_all only [mem_mulSupport, ne_eq, mem_support]
    by_contra hCon
    simp_all
  · simp_all only [mem_mulSupport, ne_eq, ne_iff]
    use u
    simp_all [zero_zpow_eq_one₀]

set_option backward.isDefEq.respectTransparency false in
/--
Helper Lemma: If the support of `d` is finite, then evaluation of functions commutes with finprod,
and the function `∏ᶠ u, (· - u) ^ d u` equals `fun x ↦ ∏ᶠ u, (x - u) ^ d u`.
-/
/-
**Function.FactorizedRational.finprod_eq_fun** 是 Mathlib 中的一个引理，位于命名空间 `Function
.FactorizedRational`。
形式化陈述：finprod_eq_fun {d : 𝕜 -> Int} (h : d.HasFiniteSupport) : (∏ᶠ u, (· - u) ^ 
d u) = fun x => ∏ᶠ u, (x - u) ^ d u
参数：h : d.HasFiniteSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Function.FactorizedRational.mulSupport`：mulSupport (d : 𝕜 -> Int) : (fun
 u => (· - u) ^ d u).mulSupport = d.support
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g

--- 原说明 ---
Helper Lemma: If the support of `d` is finite, then evaluation of functions comm
utes with finprod,
and the function `∏ᶠ u, (· - u) ^ d u` equals `fun x ↦ ∏ᶠ u, (x - u) ^ d u`.
-/
lemma finprod_eq_fun {d : 𝕜 → ℤ} (h : d.HasFiniteSupport) :
    (∏ᶠ u, (· - u) ^ d u) = fun x ↦ ∏ᶠ u, (x - u) ^ d u := by
  ext x
  rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset),
    finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]
  · simp
  · intro u
    contrapose
    simp_all
  · simp [mulSupport d]

/--
Factorized rational functions are analytic wherever the exponent is non-negative.
-/
/-
**Function.FactorizedRational.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `Function.Fac
torizedRational`。
形式化陈述：analyticAt {d : 𝕜 -> Int} {x : 𝕜} (h : 0 <= d x) : AnalyticAt 𝕜 (∏ᶠ u, (· 
- u) ^ d u) x
参数：h : 0 <= d x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_finprod`：analyticAt_finprod {α : Type*} {A : Type*} [NormedCo
mmRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} (h : forall a, AnalyticA
t 𝕜 (f a…
· 使用定理 `AnalyticAt.fun_zpow_nonneg`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {𝕝 : Type u_…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.fun_zpow`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {𝕝 
: Type u_…
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b

--- 原说明 ---
Factorized rational functions are analytic wherever the exponent is non-negative
.
-/
theorem analyticAt {d : 𝕜 → ℤ} {x : 𝕜} (h : 0 ≤ d x) :
    AnalyticAt 𝕜 (∏ᶠ u, (· - u) ^ d u) x := by
  apply analyticAt_finprod
  intro u
  by_cases h₂ : x = u
  · apply AnalyticAt.fun_zpow_nonneg (by fun_prop)
    rwa [← h₂]
  · apply AnalyticAt.fun_zpow (by fun_prop)
    rwa [sub_ne_zero]

/--
Factorized rational functions are non-zero wherever the exponent is zero.
-/
/-
**Function.FactorizedRational.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Factor
izedRational`。
形式化陈述：ne_zero {d : 𝕜 -> Int} {x : 𝕜} (h : d x = 0) : (∏ᶠ u, (· - u) ^ d u) x != 
0
参数：h : d x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1

--- 原说明 ---
Factorized rational functions are non-zero wherever the exponent is zero.
-/
theorem ne_zero {d : 𝕜 → ℤ} {x : 𝕜} (h : d x = 0) :
    (∏ᶠ u, (· - u) ^ d u) x ≠ 0 := by
  by_cases h₁ : (fun u ↦ (· - u) ^ d u).HasFiniteMulSupport
  · rw [finprod_eq_prod _ h₁, Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Pi.pow_apply, ne_eq]
    by_cases h₂ : x = z <;> simp_all [zpow_ne_zero, sub_ne_zero]
  · simp [finprod_of_infinite_mulSupport h₁]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Helper Lemma for Computations: Extract one factor out of a factorized rational function.
-/
/-
**Function.FactorizedRational.extractFactor** 是 Mathlib 中的一个引理，位于命名空间 `Function.
FactorizedRational`。
形式化陈述：extractFactor {d : 𝕜 -> Int} (u₀ : 𝕜) (hd : d.HasFiniteSupport) : (∏ᶠ u, (
· - u) ^ d u) = ((· - u₀) ^ d u₀) * (∏ᶠ u, (· - u) ^ (update d u₀ 0 u))
参数：u₀ : 𝕜；hd : d.HasFiniteSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.eq_update_self_iff`：∀ {α : Sort u} {β : α → Sort v} [inst : Dec
idableEq α] {f : (a : α) → β a} {a : α} {b : β a},   f = Function.update f a b ↔
 f a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.FactorizedRational.mulSupport`：mulSupport (d : 𝕜 -> Int) : (fun
 u => (· - u) ^ d u).mulSupport = d.support
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Helper Lemma for Computations: Extract one factor out of a factorized rational f
unction.
-/
lemma extractFactor {d : 𝕜 → ℤ} (u₀ : 𝕜) (hd : d.HasFiniteSupport) :
    (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) * (∏ᶠ u, (· - u) ^ (update d u₀ 0 u)) := by
  by_cases h₁d : d u₀ = 0
  · simp [← eq_update_self_iff.2 h₁d, h₁d]
  · have : (fun u ↦ (fun x ↦ x - u) ^ d u).mulSupport ⊆ hd.toFinset := by
      simp [mulSupport]
    rw [finprod_eq_prod_of_mulSupport_subset _ this]
    have : u₀ ∈ hd.toFinset := by simp_all
    rw [← Finset.mul_prod_erase hd.toFinset _ this]
    congr 1
    have : (fun u ↦ (· - u) ^ (update d u₀ 0 u)).mulSupport ⊆ hd.toFinset.erase u₀ := by
      rw [mulSupport]
      intro x hx
      by_cases h₁x : x = u₀ <;> simp_all
    simp_all [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]

/--
Factorized rational functions are meromorphic in normal form on `univ`.
-/
/-
**Function.FactorizedRational.meromorphicNFOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction.FactorizedRational`。
形式化陈述：meromorphicNFOn_univ (d : 𝕜 -> Int) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u
) univ
参数：d : 𝕜 -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.FactorizedRational.extractFactor`：extractFactor {d : 𝕜 -> Int} 
(u₀ : 𝕜) (hd : d.HasFiniteSupport) : (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) *
 (∏ᶠ u, (· - u) ^ (update d u₀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.FactorizedRational.mulSupport`：mulSupport (d : 𝕜 -> Int) : (fun
 u => (· - u) ^ d u).mulSupport = d.support
· 使用定理 `AnalyticOnNhd.meromorphicNFOn`：AnalyticOnNhd.meromorphicNFOn (h₁f : Anal
yticOnNhd 𝕜 f U) : MeromorphicNFOn f U
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s

--- 原说明 ---
Factorized rational functions are meromorphic in normal form on `univ`.
-/
theorem meromorphicNFOn_univ (d : 𝕜 → ℤ) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) univ := by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [extractFactor z hd]
    right
    use d z, (∏ᶠ u, (· - u) ^ update d z 0 u)
    simp [analyticAt, ne_zero]
  · rw [← mulSupport d] at hd
    rw [finprod_of_infinite_mulSupport hd]
    exact AnalyticOnNhd.meromorphicNFOn analyticOnNhd_const

/--
Factorized rational functions are meromorphic in normal form on arbitrary subsets of `𝕜`.
-/
/-
**Function.FactorizedRational.meromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.FactorizedRational`。
形式化陈述：meromorphicNFOn (d : 𝕜 -> Int) (U : Set 𝕜) : MeromorphicNFOn (∏ᶠ u, (· - u
) ^ d u) U
参数：d : 𝕜 -> Int；U : Set 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FactorizedRational.meromorphicNFOn_univ`：meromorphicNFOn_univ (
d : 𝕜 -> Int) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) univ
· 使用定理 `trivial`：True

--- 原说明 ---
Factorized rational functions are meromorphic in normal form on arbitrary subset
s of `𝕜`.
-/
theorem meromorphicNFOn (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U := fun _ _ ↦ meromorphicNFOn_univ d (trivial)

/-!
## Orders and Divisors of Factorized Rational Functions
-/

/--
The order of the factorized rational function `(∏ᶠ u, fun z ↦ (z - u) ^ d u)` at `z` equals `d z`.
-/
/-
**Function.FactorizedRational.meromorphicOrderAt_eq** 是 Mathlib 中的一个定理，位于命名空间 `F
unction.FactorizedRational`。
形式化陈述：meromorphicOrderAt_eq {z : 𝕜} (d : 𝕜 -> Int) (h₁d : d.HasFiniteSupport) : 
meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z = d z
参数：d : 𝕜 -> Int；h₁d : d.HasFiniteSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Function.FactorizedRational.meromorphicNFOn_univ`：meromorphicNFOn_univ (
d : 𝕜 -> Int) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Function.FactorizedRational.extractFactor`：extractFactor {d : 𝕜 -> Int} 
(u₀ : 𝕜) (hd : d.HasFiniteSupport) : (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) *
 (∏ᶠ u, (· - u) ^ (update d u₀ …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The order of the factorized rational function `(∏ᶠ u, fun z ↦ (z - u) ^ d u)` at
 `z` equals `d z`.
-/
theorem meromorphicOrderAt_eq {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : d.HasFiniteSupport) :
    meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z = d z := by
  classical
  rw [meromorphicOrderAt_eq_int_iff ((meromorphicNFOn_univ d).meromorphicOn _ (mem_univ _))]
  use ∏ᶠ u, (· - u) ^ update d z 0 u
  simp only [update_self, le_refl, analyticAt, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul,
    true_and]
  filter_upwards
  simp [extractFactor z h₁d]

/--
Factorized rational functions are nowhere locally constant zero.
-/
/-
**Function.FactorizedRational.meromorphicOrderAt_ne_top** 是 Mathlib 中的一个定理，位于命名空
间 `Function.FactorizedRational`。
形式化陈述：meromorphicOrderAt_ne_top {z : 𝕜} (d : 𝕜 -> Int) : meromorphicOrderAt (∏ᶠ 
u, (· - u) ^ d u) z != ⊤
参数：d : 𝕜 -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.FactorizedRational.meromorphicOrderAt_eq`：meromorphicOrderAt_eq
 {z : 𝕜} (d : 𝕜 -> Int) (h₁d : d.HasFiniteSupport) : meromorphicOrderAt (∏ᶠ u, (
· - u) ^ d u) z = d z
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.FactorizedRational.mulSupport`：mulSupport (d : 𝕜 -> Int) : (fun
 u => (· - u) ^ d u).mulSupport = d.support
· 使用定理 `meromorphicOrderAt_const_ofNat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : No
rmedAlgebra 𝕜 𝕜'] (z…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K

--- 原说明 ---
Factorized rational functions are nowhere locally constant zero.
-/
theorem meromorphicOrderAt_ne_top {z : 𝕜} (d : 𝕜 → ℤ) :
    meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z ≠ ⊤ := by
  classical
  by_cases hd : d.support.Finite
  · simp [meromorphicOrderAt_eq d hd]
  · rw [← mulSupport] at hd
    simp [finprod_of_infinite_mulSupport hd]

/--
If `D` is a divisor, then the divisor of the factorized rational function equals `D`.
-/
/-
**Function.FactorizedRational.divisor** 是 Mathlib 中的一个定理，位于命名空间 `Function.Factor
izedRational`。
形式化陈述：divisor {U : Set 𝕜} {D : locallyFinsuppWithin U Int} (hD : D.support.Finit
e) : MeromorphicOn.divisor (∏ᶠ u, (· - u) ^ D u) U = D
参数：hD : D.support.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Function.FactorizedRational.meromorphicNFOn`：meromorphicNFOn (d : 𝕜 -> I
nt) (U : Set 𝕜) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U
· 使用定理 `Function.FactorizedRational.meromorphicOrderAt_eq`：meromorphicOrderAt_eq
 {z : 𝕜} (d : 𝕜 -> Int) (h₁d : d.HasFiniteSupport) : meromorphicOrderAt (∏ᶠ u, (
· - u) ^ d u) z = d z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `D` is a divisor, then the divisor of the factorized rational function equals
 `D`.
-/
theorem divisor {U : Set 𝕜} {D : locallyFinsuppWithin U ℤ} (hD : D.support.Finite) :
    MeromorphicOn.divisor (∏ᶠ u, (· - u) ^ D u) U = D := by
  ext z
  by_cases hz : z ∈ U
  <;> simp [(meromorphicNFOn D U).meromorphicOn, hz, meromorphicOrderAt_eq D hD]

open scoped Classical in
/-
**Function.FactorizedRational.mulSupport_update** 是 Mathlib 中的一个引理，位于命名空间 `Funct
ion.FactorizedRational`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mulSupport_update {d : 𝕜 → ℤ} {x : 𝕜}
    (h : d.support.Finite) :
    (fun u ↦ (x - u) ^ Function.update d x 0 u).mulSupport ⊆ h.toFinset := by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Compute the trailing coefficient of the factorized rational function associated with `d : 𝕜 → ℤ`.
-/
/-
Low-priority TODO: Using that non-trivially normed fields contain infinitely many elements that are
no roots of unity, it might be possible to drop assumption `h` here and in some of the theorems
below.
-/
/-
**Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational** 是 
Mathlib 中的一个定理，位于命名空间 `Function.FactorizedRational`。
形式化陈述：meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 -> Int} {x : 𝕜} (h : 
d.HasFiniteSupport) : meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u,
 (x - u) ^ update d x 0 u
参数：h : d.HasFiniteSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.FactorizedRational.mulSupport`：mulSupport (d : 𝕜 -> Int) : (fun
 u => (· - u) ^ d u).mulSupport = d.support
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `meromorphicTrailingCoeffAt_prod`：meromorphicTrailingCoeffAt_prod {ι : Ty
pe*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} {x : 𝕜} (h : forall σ in s, MeromorphicAt 
(f σ) x) : meromorphi…
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `_private.Mathlib.Analysis.Meromorphic.FactorizedRational.0.Function.Fact
orizedRational.mulSupport_update`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {d : 𝕜 → ℤ} {x : 𝕜} (h : (Function.support d).Finite),   (Function.mulSupp
ort fun u => (…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_zpow`：MeromorphicAt.meromorphic
TrailingCoeffAt_zpow {n : Int} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x) : meromorph
icTrailingCoeffAt (f ^ n) x = (mero…
· 使用定理 `meromorphicTrailingCoeffAt_id_sub_const`：meromorphicTrailingCoeffAt_id_s
ub_const [DecidableEq 𝕜] {x y : 𝕜} : meromorphicTrailingCoeffAt (· - y) x = if x
 = y then 1 else x - y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1

--- 原说明 ---
Low-priority TODO: Using that non-trivially normed fields contain infinitely man
y elements that are
no roots of unity, it might be possible to drop assumption `h` here and in some 
of the theorems
below.
-/
theorem meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 → ℤ} {x : 𝕜} (h : d.HasFiniteSupport) :
    meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ update d x 0 u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this, meromorphicTrailingCoeffAt_prod
      (fun _ ↦ by fun_prop), finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  apply Finset.prod_congr rfl
  intro y hy
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]
  by_cases hxy : x = y
  · rw [hxy, meromorphicTrailingCoeffAt_id_sub_const]
    simp_all
  · grind [meromorphicTrailingCoeffAt_id_sub_const]

set_option backward.isDefEq.respectTransparency false in
/--
Variant of `meromorphicTrailingCoeffAt_factorizedRational`: Compute the trailing coefficient of the
factorized rational function associated with `d : 𝕜 → ℤ` at points outside the support of `d`.
-/
/-
**Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational_off_
support** 是 Mathlib 中的一个定理，位于命名空间 `Function.FactorizedRational`。
形式化陈述：meromorphicTrailingCoeffAt_factorizedRational_off_support {d : 𝕜 -> Int} {
x : 𝕜} (h₁ : d.HasFiniteSupport) (h₂ : x ∉ d.support) : meromorphicTrailingCoeff
At (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u
参数：h₁ : d.HasFiniteSupport；h₂ : x ∉ d.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRationa
l`：meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 -> Int} {x : 𝕜} (h : d.H
asFiniteSupport) : meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ …
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `_private.Mathlib.Analysis.Meromorphic.FactorizedRational.0.Function.Fact
orizedRational.mulSupport_update`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {d : 𝕜 → ℤ} {x : 𝕜} (h : (Function.support d).Finite),   (Function.mulSupp
ort fun u => (…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a

--- 原说明 ---
Variant of `meromorphicTrailingCoeffAt_factorizedRational`: Compute the trailing
 coefficient of the
factorized rational function associated with `d : 𝕜 → ℤ` at points outside the s
upport of `d`.
-/
theorem meromorphicTrailingCoeffAt_factorizedRational_off_support {d : 𝕜 → ℤ} {x : 𝕜}
    (h₁ : d.HasFiniteSupport) (h₂ : x ∉ d.support) :
    meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h₁,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u ↦ (x - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]
  intro y hy
  congr
  apply Function.update_of_ne
  by_contra hCon
  simp_all

set_option backward.isDefEq.respectTransparency false in
/--
Variant of `meromorphicTrailingCoeffAt_factorizedRational`: Compute log of the norm of the trailing
coefficient.  The convention that `log 0 = 0` gives a closed formula easier than the one in
`meromorphicTrailingCoeffAt_factorizedRational`.
-/
/-
**Function.FactorizedRational.log_norm_meromorphicTrailingCoeffAt** 是 Mathlib 中的
一个定理，位于命名空间 `Function.FactorizedRational`。
形式化陈述：log_norm_meromorphicTrailingCoeffAt {d : 𝕜 -> Int} {x : 𝕜} (h : d.HasFinit
eSupport) : log ‖meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d 
u) * log ‖x - u‖
参数：h : d.HasFiniteSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRationa
l`：meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 -> Int} {x : 𝕜} (h : d.H
asFiniteSupport) : meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ …
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `_private.Mathlib.Analysis.Meromorphic.FactorizedRational.0.Function.Fact
orizedRational.mulSupport_update`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {d : 𝕜 → ℤ} {x : 𝕜} (h : (Function.support d).Finite),   (Function.mulSupp
ort fun u => (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.log_prod`：log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf :
 forall x in s, f x != 0) : log (∏ i in s, f i) = ∑ i in s, log (f i)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Variant of `meromorphicTrailingCoeffAt_factorizedRational`: Compute log of the n
orm of the trailing
coefficient.  The convention that `log 0 = 0` gives a closed formula easier than
 the one in
`meromorphicTrailingCoeffAt_factorizedRational`.
-/
theorem log_norm_meromorphicTrailingCoeffAt {d : 𝕜 → ℤ} {x : 𝕜} (h : d.HasFiniteSupport) :
    log ‖meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖ := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : ∀ y ∈ h.toFinset, ‖(x - y) ^ update d x 0 y‖ ≠ 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [zpow_ne_zero, sub_ne_zero]
  rw [norm_prod, log_prod this]
  have : (fun u ↦ (d u) * log ‖x - u‖).support ⊆ h.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Finset.sum_congr rfl
  intro y hy
  rw [norm_zpow, Real.log_zpow]
  by_cases h : x = y
  · simp [h]
  · rw [Function.update_of_ne (by tauto)]

end Function.FactorizedRational

open Function.FactorizedRational

/-!
## Elimination of Zeros and Poles

This section shows that every meromorphic function with finitely many zeros and poles is equivalent,
modulo equality on codiscrete sets, to the product of a factorized rational function and an analytic
function without zeros.

We provide analogous results for functions of the form `log ‖meromorphic‖`.
-/

/-
TODO: Identify some of the terms that appear in the decomposition.
-/

/--
If `f` is meromorphic on an open set `U`, if `f` is nowhere locally constant zero, and if the
support of the divisor of `f` is finite, then there exists an analytic function `g` on `U` without
zeros such that `f` is equivalent, modulo equality on codiscrete sets, to the product of `g` and the
factorized rational function associated with the divisor of `f`.
-/
/-
**MeromorphicOn.extract_zeros_poles** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.extract_zeros_poles {f : 𝕜 -> E} (h₁f : MeromorphicOn f U) (
h₂f : forall u : U, meromorphicOrderAt f u != ⊤) (h₃f : (divisor f U).support.Fi
nite) : exists g : 𝕜 -> E, AnalyticOnNhd 𝕜 g U ∧ (forall u : U, g u != 0) ∧ f =ᶠ
[codiscreteWithin U] (∏ᶠ u, (· - u) ^ divisor f U u) • g
参数：h₁f : MeromorphicOn f U；h₂f : forall u : U, meromorphicOrderAt f u != ⊤；h₃f :
 (divisor f U).support.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Function.FactorizedRational.meromorphicNFOn`：meromorphicNFOn (d : 𝕜 -> I
nt) (U : Set 𝕜) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U
· 使用定理 `meromorphicNFOn_toMeromorphicNFOn`：meromorphicNFOn_toMeromorphicNFOn : M
eromorphicNFOn (toMeromorphicNFOn f U) U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`：MeromorphicNFOn.diviso
r_nonneg_iff_analyticOnNhd (h₁f : MeromorphicNFOn f U) : 0 <= MeromorphicOn.divi
sor f U ↔ AnalyticOnNhd 𝕜 f U
· 使用定理 `MeromorphicOn.divisor_of_toMeromorphicNFOn`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用引理 `MeromorphicOn.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 
𝕜 -> R} (hs : MeromorphicOn s U) {f : 𝕜 -> E} (hf : MeromorphicOn f U) : Meromor
phicOn (…
· 使用定理 `MeromorphicOn.inv`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivially
NormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜
 𝕜'] {s…
· 使用定理 `MeromorphicOn.divisor_smul`：divisor_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁
f₁ : MeromorphicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, mero
morphicOrderAt f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `meromorphicOrderAt_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `Function.FactorizedRational.meromorphicOrderAt_ne_top`：meromorphicOrderA
t_ne_top {z : 𝕜} (d : 𝕜 -> Int) : meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z != 
⊤
· 使用定理 `MeromorphicOn.divisor_inv`：divisor_inv {f : 𝕜 -> 𝕜} : divisor f⁻¹ U = -d
ivisor f U
· 使用定理 `Function.FactorizedRational.divisor`：divisor {U : Set 𝕜} {D : locallyFin
suppWithin U Int} (hD : D.support.Finite) : MeromorphicOn.divisor (∏ᶠ u, (· - u)
 ^ D u) U = D
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE`：MeromorphicOn.toMerom
orphicNFOn_eq_self_on_nhdsNE (hf : MeromorphicOn f U) (hx : x in U) : toMeromorp
hicNFOn f U =ᶠ[𝓝[!=] x] f
· 使用定理 `meromorphicOrderAt_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {R : Type u_…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
· 使用定理 `Function.FactorizedRational.meromorphicOrderAt_eq`：meromorphicOrderAt_eq
 {z : 𝕜} (d : 𝕜 -> Int) (h₁d : d.HasFiniteSupport) : meromorphicOrderAt (∏ᶠ u, (
· - u) ^ d u) z = d z
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is meromorphic on an open set `U`, if `f` is nowhere locally constant zer
o, and if the
support of the divisor of `f` is finite, then there exists an analytic function 
`g` on `U` without
zeros such that `f` is equivalent, modulo equality on codiscrete sets, to the pr
oduct of `g` and the
factorized rational function associated with the divisor of `f`.
-/
theorem MeromorphicOn.extract_zeros_poles {f : 𝕜 → E} (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) (h₃f : (divisor f U).support.Finite) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
      f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ divisor f U u) • g := by
  -- Take `g` as the inverse of the Laurent polynomial defined below, converted to a meromorphic
  -- function in normal form. Then check all the properties.
  let φ := ∏ᶠ u, (· - u) ^ (divisor f U u)
  have hφ : MeromorphicOn φ U := (meromorphicNFOn (divisor f U) U).meromorphicOn
  let g := toMeromorphicNFOn (φ⁻¹ • f) U
  have hg : MeromorphicNFOn g U := by apply meromorphicNFOn_toMeromorphicNFOn
  refine ⟨g, ?_, ?_, ?_⟩
  · -- AnalyticOnNhd 𝕜 g U
    rw [← hg.divisor_nonneg_iff_analyticOnNhd, divisor_of_toMeromorphicNFOn (hφ.inv.smul h₁f),
      divisor_smul hφ.inv h₁f _ (fun z hz ↦ h₂f ⟨z, hz⟩), divisor_inv,
      Function.FactorizedRational.divisor h₃f, neg_add_cancel]
    intro z hz
    simpa [meromorphicOrderAt_inv] using meromorphicOrderAt_ne_top (divisor f U)
  · -- ∀ (u : ↑U), g ↑u ≠ 0
    intro ⟨u, hu⟩
    rw [← (hg hu).meromorphicOrderAt_eq_zero_iff, ← meromorphicOrderAt_congr
        (toMeromorphicNFOn_eq_self_on_nhdsNE (hφ.inv.smul h₁f) hu).symm,
      meromorphicOrderAt_smul (hφ u hu).inv (h₁f u hu), meromorphicOrderAt_inv,
      meromorphicOrderAt_eq _ h₃f]
    simp only [h₁f, hu, divisor_apply]
    lift meromorphicOrderAt f u to ℤ using (h₂f ⟨u, hu⟩) with n hn
    rw [WithTop.untop₀_coe, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    simp
  · -- f =ᶠ[codiscreteWithin U] (∏ᶠ (u : 𝕜), fun z ↦ (z - u) ^ (divisor f U) u) * g
    filter_upwards [(divisor f U).eq_zero_codiscreteWithin,
      (hφ.inv.smul h₁f).meromorphicNFAt_mem_codiscreteWithin,
      self_mem_codiscreteWithin U] with a h₂a h₃a h₄a
    unfold g
    simp only [Pi.smul_apply', toMeromorphicNFOn_eq_toMeromorphicNFAt (hφ.inv.smul h₁f) h₄a,
      toMeromorphicNFAt_eq_self.2 h₃a, Pi.inv_apply]
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ _, one_smul]
    rwa [← ((meromorphicNFOn_univ (divisor f U)) trivial).meromorphicOrderAt_eq_zero_iff,
      meromorphicOrderAt_eq, h₂a, Pi.zero_apply, WithTop.coe_zero]

/--
In the setting of `MeromorphicOn.extract_zeros_poles`, the function `log ‖f‖` is equivalent, modulo
equality on codiscrete subsets, to `∑ᶠ u, (divisor f U u * log ‖· - u‖) + log ‖g ·‖`.
-/
/-
**MeromorphicOn.extract_zeros_poles_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.extract_zeros_poles_log {f g : 𝕜 -> E} {D : Function.locally
FinsuppWithin U Int} (hg : forall u : U, g u != 0) (h : f =ᶠ[codiscreteWithin U]
 (∏ᶠ u, (· - u) ^ D u) • g) : (log ‖f ·‖) =ᶠ[codiscreteWithin U] ∑ᶠ u, (D u * lo
g ‖· - u‖) + (log ‖g ·‖)
参数：hg : forall u : U, g u != 0；h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u
) • g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
In the setting of `MeromorphicOn.extract_zeros_poles`, the function `log ‖f‖` is
 equivalent, modulo
equality on codiscrete subsets, to `∑ᶠ u, (divisor f U u * log ‖· - u‖) + log ‖g
 ·‖`.
-/
theorem MeromorphicOn.extract_zeros_poles_log {f g : 𝕜 → E} {D : Function.locallyFinsuppWithin U ℤ}
    (hg : ∀ u : U, g u ≠ 0) (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    (log ‖f ·‖) =ᶠ[codiscreteWithin U] ∑ᶠ u, (D u * log ‖· - u‖) + (log ‖g ·‖) := by
  -- Identify support of the sum in the goal
  have t₁ : (fun u ↦ (D u * log ‖· - u‖)).support = D.support := by
    ext u
    rw [← not_iff_not]
    simp only [ne_eq, not_not, Function.mem_support]
    constructor <;> intro hx
    · obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm 𝕜
      have := congrFun hx (y + u)
      simp only [add_sub_cancel_right, Pi.zero_apply, mul_eq_zero, Int.cast_eq_zero, log_eq_zero,
        norm_eq_zero] at this
      rcases this with h | h | h | h
      · assumption
      · simp only [h, norm_zero] at hy
        linarith
      · simp only [h, lt_self_iff_false] at hy
      · simp only [h, lt_neg_self_iff] at hy
        linarith
    · simp_all [Pi.zero_def]
  -- Trivial case: the support of D is infinite
  by_cases h₃f : D.support.Finite
  case neg =>
    rw [finsum_of_infinite_support (by simpa [t₁] using h₃f)]
    rw [finprod_of_infinite_mulSupport (by simpa [FactorizedRational.mulSupport] using h₃f)] at h
    filter_upwards [h] with x hx
    simp [hx]
  -- General case
  filter_upwards [h, D.eq_zero_codiscreteWithin, self_mem_codiscreteWithin U] with z hz h₂z h₃z
  rw [Pi.zero_apply] at h₂z
  rw [hz, finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _
      (by simp_all [FactorizedRational.mulSupport]),
    finsum_eq_sum_of_support_subset (s := h₃f.toFinset) _ (by simp_all)]
  have : ∀ x ∈ h₃f.toFinset, ‖z - x‖ ^ D x ≠ 0 := by
    intro x hx
    rw [Finite.mem_toFinset, Function.mem_support] at hx
    rw [ne_eq, zpow_eq_zero_iff hx, norm_eq_zero, sub_eq_zero, eq_comm]
    apply ne_of_apply_ne D
    rwa [h₂z]
  simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply, norm_smul, norm_prod, norm_zpow]
  rw [log_mul (Finset.prod_ne_zero_iff.2 this) (by simp [hg ⟨z, h₃z⟩]), log_prod this]
  simp [log_zpow]

open scoped Classical in
/--
In the setting of `MeromorphicOn.extract_zeros_poles`, compute the trailing
coefficient of `f` in terms of `divisor f U` and `g x`.
-/
/-
**MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles {x : 𝕜} {f g 
: 𝕜 -> E} {D : 𝕜 -> Int} (hD : D.HasFiniteSupport) (h₁x : x in U) (h₂x : AccPt x
 (𝓟 U)) (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) (h : 
f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) : meromorphicTrailingCoeffAt
 f x = (∏ᶠ u, (x - u) ^ Function.update D x 0 u) • g x
参数：hD : D.HasFiniteSupport；h₁x : x in U；h₂x : AccPt x (𝓟 U)；hf : MeromorphicAt f
 x；h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0；h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· 
- u) ^ D u) • g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Function.FactorizedRational.meromorphicNFOn`：meromorphicNFOn (d : 𝕜 -> I
nt) (U : Set 𝕜) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`：even
tuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x) (hg : 
MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) …
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用定理 `MeromorphicAt.finprod`：finprod {x : 𝕜} (hf : forall i, MeromorphicAt (F 
i) x) : MeromorphicAt (∏ᶠ i, F i) x
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`：MeromorphicAt.meromorphic
TrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf₂
 : MeromorphicAt f₂ x) : meromorphi…
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRationa
l`：meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 -> Int} {x : 𝕜} (h : d.H
asFiniteSupport) : meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the setting of `MeromorphicOn.extract_zeros_poles`, compute the trailing
coefficient of `f` in terms of `divisor f U` and `g x`.
-/
theorem MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 → E} {D : 𝕜 → ℤ} (hD : D.HasFiniteSupport) (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x ≠ 0)
    (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    meromorphicTrailingCoeffAt f x = (∏ᶠ u, (x - u) ^ Function.update D x 0 u) • g x := by
  have t₀ : MeromorphicAt (∏ᶠ u, (· - u) ^ D u) x :=
    (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (by fun_prop) h₁x h₂x h),
    t₀.meromorphicTrailingCoeffAt_smul h₁g.meromorphicAt,
    h₁g.meromorphicTrailingCoeffAt_of_ne_zero h₂g]
  simp [meromorphicTrailingCoeffAt_factorizedRational hD]

/--
In the setting of `MeromorphicOn.extract_zeros_poles`, compute the log of the
norm of the trailing coefficient of `f` in terms of `divisor f U` and `g x`.
-/
/-
**MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles** 是 Math
lib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles {x :
 𝕜} {f g : 𝕜 -> E} {D : 𝕜 -> Int} (hD : D.HasFiniteSupport) (h₁x : x in U) (h₂x 
: AccPt x (𝓟 U)) (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x !=
 0) (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) : log ‖meromorphicT
railingCoeffAt f x‖ = ∑ᶠ u, (D u) * log ‖x - u‖ + log ‖g x‖
参数：hD : D.HasFiniteSupport；h₁x : x in U；h₂x : AccPt x (𝓟 U)；hf : MeromorphicAt f
 x；h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0；h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· 
- u) ^ D u) • g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`：even
tuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x) (hg : 
MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) …
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Function.FactorizedRational.meromorphicNFOn`：meromorphicNFOn (d : 𝕜 -> I
nt) (U : Set 𝕜) : MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`：MeromorphicAt.meromorphic
TrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf₂
 : MeromorphicAt f₂ x) : meromorphi…
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero`：MeromorphicAt.meromorp
hicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x) (h₂ : meromorphicOrderAt f x
 != ⊤) : meromorphicTrailingCoeffAt f …
· 使用定理 `Function.FactorizedRational.meromorphicOrderAt_ne_top`：meromorphicOrderA
t_ne_top {z : 𝕜} (d : 𝕜 -> Int) : meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z != 
⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.FactorizedRational.log_norm_meromorphicTrailingCoeffAt`：log_nor
m_meromorphicTrailingCoeffAt {d : 𝕜 -> Int} {x : 𝕜} (h : d.HasFiniteSupport) : l
og ‖meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) …

--- 原说明 ---
In the setting of `MeromorphicOn.extract_zeros_poles`, compute the log of the
norm of the trailing coefficient of `f` in terms of `divisor f U` and `g x`.
-/
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 → E} {D : 𝕜 → ℤ} (hD : D.HasFiniteSupport) (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x ≠ 0)
    (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    log ‖meromorphicTrailingCoeffAt f x‖ = ∑ᶠ u, (D u) * log ‖x - u‖ + log ‖g x‖ := by
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).smul h₁g.meromorphicAt)
          h₁x h₂x h),
    ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).meromorphicTrailingCoeffAt_smul
      h₁g.meromorphicAt, h₁g.meromorphicTrailingCoeffAt_of_ne_zero h₂g,
    norm_smul, log_mul, log_norm_meromorphicTrailingCoeffAt hD]
  · simp only [ne_eq, norm_eq_zero]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero
      ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x)
    apply FactorizedRational.meromorphicOrderAt_ne_top
  · simp_all
