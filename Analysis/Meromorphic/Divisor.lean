/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.LocallyFinsupp

/-!
# The Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those
divisors. The lemma `MeromorphicOn.divisor_restrict` guarantees compatibility between restrictions
of divisors and of meromorphic functions to subsets of their domain of definition.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter Metric Topology

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open scoped Classical in
/--
The divisor of a meromorphic function `f`, mapping a point `z` to the order of `f` at `z`, and to
zero if the order is infinite.
-/
/-
**MeromorphicOn.divisor** 是 Mathlib 中的一个定义，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor (f : 𝕜 -> E) (U : Set 𝕜) : Function.locallyFinsuppWithin U Int whe
re toFun
参数：f : 𝕜 -> E；U : Set 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The divisor of a meromorphic function `f`, mapping a point `z` to the order of `
f` at `z`, and to
zero if the order is infinite.
-/
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ where
  toFun := fun z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, ite_eq_right_iff, WithTop.untop₀_eq_zero,
      and_imp, Classical.not_imp, not_or, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Pi.ofNat_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
      tauto
    · simp [hf, Pi.zero_def]

open scoped Classical in
/-- Definition of the divisor -/
/-
**MeromorphicOn.divisor_def** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_def (f : 𝕜 -> E) (U : Set 𝕜) : divisor f U z = if MeromorphicOn f 
U ∧ z in U then (meromorphicOrderAt f z).untop₀ else 0
参数：f : 𝕜 -> E；U : Set 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of the divisor
-/
theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) :
    divisor f U z = if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0 :=
  rfl

/--
Simplifier lemma: on `U`, the divisor of a function `f` that is meromorphic on `U` evaluates to
`order.untop₀`.
-/
@[simp]
/-
**MeromorphicOn.divisor_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_apply {f : 𝕜 -> E} (hf : MeromorphicOn f U) (hz : z in U) : diviso
r f U z = (meromorphicOrderAt f z).untop₀
参数：hf : MeromorphicOn f U；hz : z in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Simplifier lemma: on `U`, the divisor of a function `f` that is meromorphic on `
U` evaluates to
`order.untop₀`.
-/
lemma divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    divisor f U z = (meromorphicOrderAt f z).untop₀ := by simp_all [MeromorphicOn.divisor_def]

/-- The divisor of a function `f` evaluates to zero if `f` is not meromorphic. -/
/-
**MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn** 是 Mathlib 中的一个定理，位于命名空间 `
MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜} {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜
 → E}, ¬MeromorphicOn f U → (MeromorphicOn.divisor f U) z = 0
参数：MeromorphicOn.divisor f U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Function.locallyFinsuppWithin.mk.congr_simp`：∀ {X : Type u_1} [inst : To
pologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y] (toFun toFun_1 : 
X → Y)   (e_toFun : toFun = toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The divisor of a function `f` evaluates to zero if `f` is not meromorphic.
-/
@[simp] theorem divisor_eq_zero_of_not_meromorphicOn {f : 𝕜 → E} (hf : ¬ MeromorphicOn f U) :
    divisor f U z = 0 := by
  unfold divisor
  aesop
/-
**MeromorphicOn.AnalyticOnNhd.divisor_apply** 是 Mathlib 中的一个定理，位于命名空间 `Meromorph
icOn.AnalyticOnNhd`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜} {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜
 → E},   AnalyticOnNhd 𝕜 f U → z ∈ U → (MeromorphicOn.divisor f U) z = (ENat.map
 Nat.cast (analyticOrderAt f z)).untop₀
参数：MeromorphicOn.divisor f U；ENat.map Nat.cast (analyticOrderAt f z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
-/
lemma AnalyticOnNhd.divisor_apply {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z ∈ U) :
    divisor f U z = ((analyticOrderAt f z).map (↑)).untop₀ := by
  rw [hf.meromorphicOn.divisor_apply hz, (hf z hz).meromorphicOrderAt_eq]

/-!
## Support Properties
-/

/--
Special case of `Function.locallyFinsuppWithin.finiteSupport` that frequently shows in complex
analysis: Divisors on spheres have finite support.
-/
/-
**MeromorphicOn._root_.divisor_sphere_support_finite** 是 Mathlib 中的一个引理，位于命名空间 `
MeromorphicOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Special case of `Function.locallyFinsuppWithin.finiteSupport` that frequently sh
ows in complex
analysis: Divisors on spheres have finite support.
-/
lemma _root_.divisor_sphere_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜} :
    (divisor f (sphere c R)).support.Finite :=
  (divisor f (sphere c R)).finiteSupport (isCompact_sphere c R)

/--
If `f` is meromorphic on a compact set `U` and `V ⊆ U`, then the divisor of `f` on `V` has finite
support.
-/
/-
**MeromorphicOn.divisor_support_finite_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Mero
morphicOn`。
形式化陈述：divisor_support_finite_of_subset {f : 𝕜 -> E} {V : Set 𝕜} (hf : Meromorphi
cOn f U) (hU : IsCompact U) (hV : V subseteq U) : (divisor f V).support.Finite
参数：hf : MeromorphicOn f U；hU : IsCompact U；hV : V subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U

--- 原说明 ---
If `f` is meromorphic on a compact set `U` and `V ⊆ U`, then the divisor of `f` 
on `V` has finite
support.
-/
lemma divisor_support_finite_of_subset {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U)
    (hU : IsCompact U) (hV : V ⊆ U) :
    (divisor f V).support.Finite := by
  apply ((divisor f U).finiteSupport hU).subset
  intro b hb
  rw [Function.mem_support, ne_eq, divisor_apply hf (hV ((divisor f V).supportWithinDomain hb))]
  rwa [Function.mem_support, ne_eq, divisor_apply (fun x hx ↦ hf x (hV hx))
    ((divisor f V).supportWithinDomain hb)] at hb

/--
Special case of `MeromorphicOn.divisor_subset_finiteSupport` that frequently shows in complex
analysis, where  `U` is a closed ball and `V` is its interior.
-/
/-
**MeromorphicOn.divisor_ball_support_finite** 是 Mathlib 中的一个引理，位于命名空间 `Meromorph
icOn`。
形式化陈述：divisor_ball_support_finite [ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜
} (hf : MeromorphicOn f (closedBall c R)) : (divisor f (ball c R)).support.Finit
e
参数：hf : MeromorphicOn f (closedBall c R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicOn.divisor_support_finite_of_subset`：divisor_support_finite_o
f_subset {f : 𝕜 -> E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hU : IsCompact U) (h
V : V subseteq U) : (divisor f V).su…
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
Special case of `MeromorphicOn.divisor_subset_finiteSupport` that frequently sho
ws in complex
analysis, where  `U` is a closed ball and `V` is its interior.
-/
lemma divisor_ball_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜}
    (hf : MeromorphicOn f (closedBall c R)) :
    (divisor f (ball c R)).support.Finite :=
  hf.divisor_support_finite_of_subset (isCompact_closedBall c R) ball_subset_closedBall

/-!
## Congruence Lemmas
-/

/--
If `f₁` is meromorphic on `U`, if `f₂` agrees with `f₁` on a codiscrete subset of `U` and outside of
`U`, then `f₁` and `f₂` induce the same divisors on `U`.
-/
/-
**MeromorphicOn.divisor_congr_codiscreteWithin_of_eqOn_compl** 是 Mathlib 中的一个定理，
位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_congr_codiscreteWithin_of_eqOn_compl {f₁ f₂ : 𝕜 -> E} (hf₁ : Merom
orphicOn f₁ U) (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) : di
visor f₁ U = divisor f₂ U
参数：hf₁ : MeromorphicOn f₁ U；h₁ : f₁ =ᶠ[codiscreteWithin U] f₂；h₂ : Set.EqOn f₁ f
₂ Uᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.congr_codiscreteWithin_of_eqOn_compl`：congr_codiscreteWith
in_of_eqOn_compl (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ 
: Set.EqOn f g Uᶜ) : MeromorphicOn g U
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f₁` is meromorphic on `U`, if `f₂` agrees with `f₁` on a codiscrete subset o
f `U` and outside of
`U`, then `f₁` and `f₂` induce the same divisors on `U`.
-/
theorem divisor_congr_codiscreteWithin_of_eqOn_compl {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    divisor f₁ U = divisor f₂ U := by
  ext x
  by_cases hx : x ∈ U
  · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin_of_eqOn_compl h₁ h₂]
    congr 1
    apply meromorphicOrderAt_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto
  · simp [hx]

/-
If two meromorphic functions agree outside a set codiscrete within a perfect set, then they define
the same divisors there.
-/
/-
**MeromorphicOn.divisor_of_eventuallyEq_codiscreteWithin_preperfect** 是 Mathlib 
中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_of_eventuallyEq_codiscreteWithin_preperfect {f₁ f₂ : 𝕜 -> E} (hf₁ 
: MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) (hU : Preperfect U) (h : f₁ =ᶠ[
codiscreteWithin U] f₂) : divisor f₁ U = divisor f₂ U
参数：hf₁ : MeromorphicOn f₁ U；hf₂ : MeromorphicOn f₂ U；hU : Preperfect U；h : f₁ =ᶠ
[codiscreteWithin U] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_prepe
rfect`：eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf : Mer
omorphicAt f x) (hg : MeromorphicAt g x) (hx : x in U) (hU : Preper…

--- 原说明 ---
If two meromorphic functions agree outside a set codiscrete within a perfect set
, then they define
the same divisors there.
-/
theorem divisor_of_eventuallyEq_codiscreteWithin_preperfect {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) (hU : Preperfect U)
    (h : f₁ =ᶠ[codiscreteWithin U] f₂) :
    divisor f₁ U = divisor f₂ U := by
  ext z
  by_cases hz : z ∉ U
  · simp_all
  rw [not_not] at hz
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz]
  congr 1
  apply meromorphicOrderAt_congr
  apply (hf₁ z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf₂ z hz) hz hU h

/--
If two functions differ only on a discrete set of an open, then they induce the same divisors.
-/
/-
**MeromorphicOn.divisor_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `Meromo
rphicOn`。
形式化陈述：divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 -> E} (h₁ : f₁ =ᶠ[codiscreteWith
in U] f₂) (h₂ : IsOpen U) : divisor f₁ U = divisor f₂ U
参数：h₁ : f₁ =ᶠ[codiscreteWithin U] f₂；h₂ : IsOpen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.congr_codiscreteWithin`：congr_codiscreteWithin (hf : Merom
orphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ : IsOpen U) : MeromorphicOn 
g U
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `meromorphicOn_congr_codiscreteWithin`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {U : Set 𝕜} …
· 使用定理 `Function.locallyFinsuppWithin.mk.congr_simp`：∀ {X : Type u_1} [inst : To
pologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y] (toFun toFun_1 : 
X → Y)   (e_toFun : toFun = toFun…

--- 原说明 ---
If two functions differ only on a discrete set of an open, then they induce the 
same divisors.
-/
theorem divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
    (h₂ : IsOpen U) :
    divisor f₁ U = divisor f₂ U := by
  by_cases hf₁ : MeromorphicOn f₁ U
  · ext x
    by_cases hx : x ∈ U
    · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin h₁ h₂]
      congr 1
      apply meromorphicOrderAt_congr
      simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
        disjoint_principal_right] at h₁
      have : U ∈ 𝓝[≠] x := by
        apply mem_nhdsWithin.mpr
        use U, h₂, hx, Set.inter_subset_left
      filter_upwards [this, h₁ x hx] with a h₁a h₂a
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
      tauto
    · simp [hx]
  · simp [divisor, hf₁, (meromorphicOn_congr_codiscreteWithin h₁ h₂).not.1 hf₁]

/-!
## Divisors of Analytic Functions
-/

/-- Analytic functions have non-negative divisors. -/
/-
**MeromorphicOn.AnalyticOnNhd.divisor_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Meromorp
hicOn.AnalyticOnNhd`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {U : Set 𝕜} {E : Type 
u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E}, A
nalyticOnNhd 𝕜 f U → 0 ≤ MeromorphicOn.divisor f U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AnalyticAt.meromorphicOrderAt_nonneg`：AnalyticAt.meromorphicOrderAt_nonn
eg (hf : AnalyticAt 𝕜 f x) : 0 <= meromorphicOrderAt f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Analytic functions have non-negative divisors.
-/
theorem AnalyticOnNhd.divisor_nonneg {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) :
    0 ≤ MeromorphicOn.divisor f U := by
  intro x
  by_cases hx : x ∈ U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicOrderAt_nonneg]
  simp [hx]

/--
The divisor of a constant function is `0`.
-/
@[simp]
/-
**MeromorphicOn.divisor_const** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_const (e : E) : divisor (fun _ => e) U = 0
参数：e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `meromorphicOrderAt_const`：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Dec
idable (e = 0)] : meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 :
 WithTop Int)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p

--- 原说明 ---
The divisor of a constant function is `0`.
-/
theorem divisor_const (e : E) :
    divisor (fun _ ↦ e) U = 0 := by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

/--
The divisor of a constant function is `0`.
-/
@[simp]
/-
**MeromorphicOn.divisor_intCast** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_intCast (n : Int) : divisor (n : 𝕜 -> 𝕜) U = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_const`：divisor_const (e : E) : divisor (fun _ => e
) U = 0

--- 原说明 ---
The divisor of a constant function is `0`.
-/
theorem divisor_intCast (n : ℤ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp]
/-
**MeromorphicOn.divisor_natCast** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_natCast (n : Nat) : divisor (n : 𝕜 -> 𝕜) U = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_const`：divisor_const (e : E) : divisor (fun _ => e
) U = 0

--- 原说明 ---
The divisor of a constant function is `0`.
-/
theorem divisor_natCast (n : ℕ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
/-
**MeromorphicOn.divisor_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {U : Set 𝕜} (n : ℕ), M
eromorphicOn.divisor (OfNat.ofNat n) U = 0
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semiring.toGrindSemiring_ofNat`：Semiring.toGrindSemiring_ofNat [Semiring
 α] (n : Nat) : @OfNat.ofNat α n (Lean.Grind.Semiring.ofNat n) = n.cast
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicOn.divisor_const`：divisor_const (e : E) : divisor (fun _ => e
) U = 0

--- 原说明 ---
The divisor of a constant function is `0`.
-/
@[simp] theorem divisor_ofNat (n : ℕ) :
    divisor (ofNat(n) : 𝕜 → 𝕜) U = 0 := by
  convert! divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

/-!
## Behavior under Standard Operations
-/

/--
The divisor of `f₁ + f₂` is larger than or equal to the minimum of the divisors of `f₁` and `f₂`,
respectively.
-/
/-
**MeromorphicOn.min_divisor_le_divisor_add** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphi
cOn`。
形式化陈述：min_divisor_le_divisor_add {f₁ f₂ : 𝕜 -> E} {z : 𝕜} {U : Set 𝕜} (hf₁ : Mer
omorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) (h₁z : z in U) (h₃ : meromorphicOrde
rAt (f₁ + f₂) z != ⊤) : min (divisor f₁ U z) (divisor f₂ U z) <= divisor (f₁ + f
₂) U z
参数：hf₁ : MeromorphicOn f₁ U；hf₂ : MeromorphicOn f₂ U；h₁z : z in U；h₃ : meromorph
icOrderAt (f₁ + f₂) z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f g 
: 𝕜 → E…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `WithTop.untop₀_top`：untop₀_top : untop₀ ⊤ = (0 : α)
· 使用定理 `meromorphicOrderAt_add_of_top_left`：meromorphicOrderAt_add_of_top_left {
f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) : meromorphicOrderAt
 (f₁ + f₂) x = meromorph…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `meromorphicOrderAt_add_of_top_right`：meromorphicOrderAt_add_of_top_right
 {f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₂ : meromorphicOrderAt f₂ x = ⊤) : meromorphicOrder
At (f₁ + f₂) x = meromorp…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.untop₀_min`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : L
inearOrder α] {a b : WithTop α},   a ≠ ⊤ → b ≠ ⊤ → (min a b).untop₀ = min a.unto
p₀ b.unt…
· 使用定理 `WithTop.untop₀_le_untop₀`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst
_1 : PartialOrder α] {a b : WithTop α},   b ≠ ⊤ → a ≤ b → a.untop₀ ≤ b.untop₀
· 使用定理 `meromorphicOrderAt_add`：meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x
) (hf₂ : MeromorphicAt f₂ x) : min (meromorphicOrderAt f₁ x) (meromorphicOrderAt
 f₂ x) <= me…

--- 原说明 ---
The divisor of `f₁ + f₂` is larger than or equal to the minimum of the divisors 
of `f₁` and `f₂`,
respectively.
-/
theorem min_divisor_le_divisor_add {f₁ f₂ : 𝕜 → E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z ∈ U) (h₃ : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) ≤ divisor (f₁ + f₂) U z := by
  by_cases! hz : z ∉ U
  · simp_all
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz, divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · simp_all
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · simp_all
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀ h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the maximum of the pole divisors of `f₁`
and `f₂`, respectively.
-/
/-
**MeromorphicOn.negPart_divisor_add_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphi
cOn`。
形式化陈述：negPart_divisor_add_le_max {f₁ f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : Meromorphic
On f₁ U) (hf₂ : MeromorphicOn f₂ U) : (divisor (f₁ + f₂) U)⁻ <= max (divisor f₁ 
U)⁻ (divisor f₂ U)⁻
参数：hf₁ : MeromorphicOn f₁ U；hf₂ : MeromorphicOn f₂ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f g 
: 𝕜 → E…
· 使用引理 `WithTop.untop₀_top`：untop₀_top : untop₀ ⊤ = (0 : α)
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `negPart_min`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [
AddLeftMono α] [AddRightMono α] (a b : α), (a ⊓ b)⁻ = a⁻ ⊔ b⁻
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_posPart_negPart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ad
dCommGroup α] [AddLeftMono α] (a b : α), a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻
· 使用定理 `MeromorphicOn.min_divisor_le_divisor_add`：min_divisor_le_divisor_add {f₁
 f₂ : 𝕜 -> E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicO
n f₂ U) (h₁z : z in U) (h₃ : m…

--- 原说明 ---
The pole divisor of `f₁ + f₂` is smaller than or equal to the maximum of the pol
e divisors of `f₁`
and `f₂`, respectively.
-/
theorem negPart_divisor_add_le_max {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ := by
  intro z
  by_cases! hz : z ∉ U
  · simp [hz]
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the sum of the pole divisors of `f₁` and
`f₂`, respectively.
-/
/-
**MeromorphicOn.negPart_divisor_add_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphi
cOn`。
形式化陈述：negPart_divisor_add_le_add {f₁ f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : Meromorphic
On f₁ U) (hf₂ : MeromorphicOn f₂ U) : (divisor (f₁ + f₂) U)⁻ <= (divisor f₁ U)⁻ 
+ (divisor f₂ U)⁻
参数：hf₁ : MeromorphicOn f₁ U；hf₂ : MeromorphicOn f₂ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.negPart_divisor_add_le_max`：negPart_divisor_add_le_max {f₁
 f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) 
: (divisor (f₁ + f₂) U)⁻ <= ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Function.locallyFinsuppWithin.instIsOrderedAddMonoid`：∀ {X : Type u_1} [
inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommGroup Y] 
  [inst_2 : LinearOrder Y] [IsOrderedAddMo…
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
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The pole divisor of `f₁ + f₂` is smaller than or equal to the sum of the pole di
visors of `f₁` and
`f₂`, respectively.
-/
theorem negPart_divisor_add_le_add {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  calc (divisor (f₁ + f₂) U)⁻
    _ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
      negPart_divisor_add_le_max hf₁ hf₂
    _ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
      by_cases h : (divisor f₁ U)⁻ ≤ (divisor f₂ U)⁻
      <;> simp_all [negPart_nonneg]

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
/-
**MeromorphicOn.divisor_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U) (h₁f₂
 : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤) (h₂f
₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤) : divisor (f₁ • f₂) U = divisor
 f₁ U + divisor f₂ U
参数：h₁f₁ : MeromorphicOn f₁ U；h₁f₂ : MeromorphicOn f₂ U；h₂f₁ : forall z in U, mer
omorphicOrderAt f₁ z != ⊤；h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用引理 `MeromorphicOn.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 
𝕜 -> R} (hs : MeromorphicOn s U) {f : 𝕜 -> E} (hf : MeromorphicOn f U) : Meromor
phicOn (…
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If orders are finite, the divisor of the scalar product of two meromorphic funct
ions is the sum of
the divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to gu
arantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (f₁ • f₂) U = divisor f₁ U + divisor f₂ U := by
  ext z
  by_cases hz : z ∈ U
  · lift meromorphicOrderAt f₁ z to ℤ using (h₂f₁ z hz) with a₁ ha₁
    lift meromorphicOrderAt f₂ z to ℤ using (h₂f₂ z hz) with a₂ ha₂
    simp [h₁f₁, h₁f₂, h₁f₁.smul h₁f₂, hz, meromorphicOrderAt_smul (h₁f₁ z hz) (h₁f₂ z hz),
      ← ha₁, ← ha₂, ← WithTop.coe_add]
  · simp [hz]

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.
-/
/-
**MeromorphicOn.divisor_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_fun_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U) (
h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤) 
(h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤) : divisor (fun z => f₁ z • 
f₂ z) U = divisor f₁ U + divisor f₂ U
参数：h₁f₁ : MeromorphicOn f₁ U；h₁f₂ : MeromorphicOn f₂ U；h₂f₁ : forall z in U, mer
omorphicOrderAt f₁ z != ⊤；h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_smul`：divisor_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁
f₁ : MeromorphicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, mero
morphicOrderAt f…

--- 原说明 ---
If orders are finite, the divisor of the scalar product of two meromorphic funct
ions is the sum of
the divisors.
-/
theorem divisor_fun_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (fun z ↦ f₁ z • f₂ z) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
/-
**MeromorphicOn.divisor_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U) (h₁f₂ : Meromorph
icOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤) (h₂f₂ : forall z
 in U, meromorphicOrderAt f₂ z != ⊤) : divisor (f₁ * f₂) U = divisor f₁ U + divi
sor f₂ U
参数：h₁f₁ : MeromorphicOn f₁ U；h₁f₂ : MeromorphicOn f₂ U；h₂f₁ : forall z in U, mer
omorphicOrderAt f₁ z != ⊤；h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_smul`：divisor_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁
f₁ : MeromorphicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, mero
morphicOrderAt f…

--- 原说明 ---
If orders are finite, the divisor of the product of two meromorphic functions is
 the sum of the
divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to gu
arantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U := divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.
-/
/-
**MeromorphicOn.divisor_fun_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_fun_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U) (h₁f₂ : Merom
orphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤) (h₂f₂ : fora
ll z in U, meromorphicOrderAt f₂ z != ⊤) : divisor (fun z => f₁ z * f₂ z) U = di
visor f₁ U + divisor f₂ U
参数：h₁f₁ : MeromorphicOn f₁ U；h₁f₂ : MeromorphicOn f₂ U；h₂f₁ : forall z in U, mer
omorphicOrderAt f₁ z != ⊤；h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_smul`：divisor_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁
f₁ : MeromorphicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, mero
morphicOrderAt f…

--- 原说明 ---
If orders are finite, the divisor of the product of two meromorphic functions is
 the sum of the
divisors.
-/
theorem divisor_fun_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) :
    divisor (fun z ↦ f₁ z * f₂ z) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

open Finset in
/--
If orders are finite, the divisor of a product of meromorphic functions is the sum of the divisors.
-/
/-
**MeromorphicOn.divisor_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i 
in s, MeromorphicOn (f i) U) (h₂f : forall i in s, forall z in U, meromorphicOrd
erAt (f i) z != ⊤) : divisor (∏ i in s, f i) U = ∑ i in s, divisor (f i) U
参数：h₁f : forall i in s, MeromorphicOn (f i) U；h₂f : forall i in s, forall z in U
, meromorphicOrderAt (f i) z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `MeromorphicOn.divisor_ofNat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {U : Set 𝕜} (n : ℕ), MeromorphicOn.divisor (OfNat.ofNat n) U = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `meromorphicOrderAt_prod`：meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s 
: Finset ι} {f : ι -> 𝕜 -> 𝕜'} (hf : forall i in s, MeromorphicAt (f i) x) : mer
omorphicOrder…
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `MeromorphicOn.divisor_mul`：divisor_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : Meromorp
hicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderA
t f₁ z != ⊤) (h…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MeromorphicOn.prod`：prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -
> 𝕜 -> 𝕜'} (h : forall σ in s, MeromorphicOn (f σ) U) : MeromorphicOn (∏ n in s,
 f n) U
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s

--- 原说明 ---
If orders are finite, the divisor of a product of meromorphic functions is the s
um of the divisors.
-/
theorem divisor_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i ∈ s, ∀ z ∈ U, meromorphicOrderAt (f i) z ≠ ⊤) :
    divisor (∏ i ∈ s, f i) U = ∑ i ∈ s, divisor (f i) U := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [prod_empty, sum_empty]
    exact divisor_ofNat 1
  | insert a s ha hs =>
    have (z) (hz : z ∈ U) : meromorphicOrderAt (∏ i ∈ s, f i) z ≠ ⊤ := by
      simpa [meromorphicOrderAt_prod (fun i hi ↦ h₁f i (mem_insert_of_mem hi) z hz)]
        using fun i hi ↦ h₂f i (mem_insert_of_mem hi) z hz
    rw [prod_insert ha, sum_insert ha, divisor_mul (by aesop)
        (prod (fun i hi ↦ h₁f i (mem_insert_of_mem hi)))
        (h₂f a (mem_insert_self a s)) this,
      hs (fun i hi ↦ h₁f i (mem_insert_of_mem hi))
        (fun i hi ↦ h₂f i (mem_insert_of_mem hi))]

/--
If orders are finite, the divisor of a product of meromorphic functions is the sum of the divisors.
-/
/-
**MeromorphicOn.divisor_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_fun_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} (h₁f : foral
l i in s, MeromorphicOn (f i) U) (h₂f : forall i in s, forall z in U, meromorphi
cOrderAt (f i) z != ⊤) : divisor (fun x => ∏ i in s, f i x) U = ∑ i in s, diviso
r (f i) U
参数：h₁f : forall i in s, MeromorphicOn (f i) U；h₂f : forall i in s, forall z in U
, meromorphicOrderAt (f i) z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `MeromorphicOn.divisor_prod`：divisor_prod {ι : Type*} {s : Finset ι} {f :
 ι -> 𝕜 -> 𝕜} (h₁f : forall i in s, MeromorphicOn (f i) U) (h₂f : forall i in s,
 forall z in U, …

--- 原说明 ---
If orders are finite, the divisor of a product of meromorphic functions is the s
um of the divisors.
-/
theorem divisor_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i ∈ s, ∀ z ∈ U, meromorphicOrderAt (f i) z ≠ ⊤) :
    divisor (fun x ↦ ∏ i ∈ s, f i x) U = ∑ i ∈ s, divisor (f i) U := by
  convert! divisor_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
/-
**MeromorphicOn.divisor_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_inv {f : 𝕜 -> 𝕜} : divisor f⁻¹ U = -divisor f U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `meromorphicOrderAt_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `WithTop.untop₀_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] (a : WithTo
p α), (-a).untop₀ = -a.untop₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0

--- 原说明 ---
The divisor of the inverse is the negative of the divisor.
-/
theorem divisor_inv {f : 𝕜 → 𝕜} :
    divisor f⁻¹ U = -divisor f U := by
  ext z
  by_cases h : MeromorphicOn f U ∧ z ∈ U
  · simp [divisor_apply, h, meromorphicOrderAt_inv]
  · simp [divisor_def, h]

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
/-
**MeromorphicOn.divisor_fun_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_fun_inv {f : 𝕜 -> 𝕜} : divisor (fun z => (f z)⁻¹) U = -divisor f U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_inv`：divisor_inv {f : 𝕜 -> 𝕜} : divisor f⁻¹ U = -d
ivisor f U

--- 原说明 ---
The divisor of the inverse is the negative of the divisor.
-/
theorem divisor_fun_inv {f : 𝕜 → 𝕜} : divisor (fun z ↦ (f z)⁻¹) U = -divisor f U := divisor_inv

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
/-
**MeromorphicOn.divisor_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_pow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Nat) : divisor (f ^
 n) U = n • divisor f U
参数：hf : MeromorphicOn f U；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MeromorphicOn.divisor_ofNat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {U : Set 𝕜} (n : ℕ), MeromorphicOn.divisor (OfNat.ofNat n) U = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeromorphicOn.pow`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivially
NormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜
 𝕜'] {s…
· 使用定理 `meromorphicOrderAt_pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {f…
· 使用引理 `WithTop.untop₀_mul`：untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : W
ithTop α) : (a * b).untop₀ = a.untop₀ * b.untop₀
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `
f`.
-/
theorem divisor_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z ∈ U
  · simp [hf.pow, divisor_apply, meromorphicOrderAt_pow (hf z hz), hf, hz]
  · simp [hz]

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
/-
**MeromorphicOn.divisor_fun_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_fun_pow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Nat) : divisor 
(fun z => f z ^ n) U = n • divisor f U
参数：hf : MeromorphicOn f U；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_pow`：divisor_pow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn 
f U) (n : Nat) : divisor (f ^ n) U = n • divisor f U

--- 原说明 ---
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `
f`.
-/
theorem divisor_fun_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := divisor_pow hf n

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
/-
**MeromorphicOn.divisor_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_zpow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Int) : divisor (f 
^ n) U = n • divisor f U
参数：hf : MeromorphicOn f U；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MeromorphicOn.divisor_ofNat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {U : Set 𝕜} (n : ℕ), MeromorphicOn.divisor (OfNat.ofNat n) U = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeromorphicOn.zpow`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 
𝕜 𝕜'] {s…
· 使用定理 `meromorphicOrderAt_zpow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlg
ebra 𝕜 𝕜'] {f…
· 使用引理 `WithTop.untop₀_mul`：untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : W
ithTop α) : (a * b).untop₀ = a.untop₀ * b.untop₀
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `
f`.
-/
theorem divisor_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z ∈ U
  · simp [hf.zpow, divisor_apply, meromorphicOrderAt_zpow (hf z hz), hf, hz]
  · simp [hz]

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
/-
**MeromorphicOn.divisor_fun_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_fun_zpow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Int) : divisor
 (fun z => f z ^ n) U = n • divisor f U
参数：hf : MeromorphicOn f U；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.divisor_zpow`：divisor_zpow {f : 𝕜 -> 𝕜} (hf : MeromorphicO
n f U) (n : Int) : divisor (f ^ n) U = n • divisor f U

--- 原说明 ---
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `
f`.
-/
theorem divisor_fun_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := divisor_zpow hf n

/--
Taking the divisor of a meromorphic function commutes with restriction.
-/
@[simp]
/-
**MeromorphicOn.divisor_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_restrict {f : 𝕜 -> E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V
 subseteq U) : (divisor f U).restrict hV = divisor f V
参数：hf : MeromorphicOn f U；hV : V subseteq U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.restrict_apply`：restrict_apply [Zero Y] {V
 : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) (z : X) : (D.restric
t h) z = if z in V then D z else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用引理 `MeromorphicOn.mono_set`：mono_set {V : Set 𝕜} (hv : V subseteq U) : Merom
orphicOn f V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Taking the divisor of a meromorphic function commutes with restriction.
-/
theorem divisor_restrict {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V ⊆ U) :
    (divisor f U).restrict hV = divisor f V := by
  ext x
  by_cases hx : x ∈ V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hf, hx, hf.mono_set hV, hV hx]
  · simp [hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
/-
**MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right** 是 Mathlib 中的一个定理，位于
命名空间 `MeromorphicOn`。
形式化陈述：negPart_divisor_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 -> E} (hf₁ : Meromor
phicOn f₁ U) (hf₂ : AnalyticOnNhd 𝕜 f₂ U) : (divisor (f₁ + f₂) U)⁻ = (divisor f₁
 U)⁻
参数：hf₁ : MeromorphicOn f₁ U；hf₂ : AnalyticOnNhd 𝕜 f₂ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `AnalyticAt.meromorphicOrderAt_nonneg`：AnalyticAt.meromorphicOrderAt_nonn
eg (hf : AnalyticAt 𝕜 f x) : 0 <= meromorphicOrderAt f x
· 使用定理 `meromorphicOrderAt_add`：meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x
) (hf₂ : MeromorphicAt f₂ x) : min (meromorphicOrderAt f₁ x) (meromorphicOrderAt
 f₂ x) <= me…
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `meromorphicOrderAt_add_eq_left_of_lt`：meromorphicOrderAt_add_eq_left_of_
lt (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt 
f₂ x) : meromorphicOrderAt…
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f g 
: 𝕜 → E…
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Adding an analytic function to a meromorphic one does not change the pole diviso
r.
-/
theorem negPart_divisor_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : AnalyticOnNhd 𝕜 f₂ U) :
    (divisor (f₁ + f₂) U)⁻ = (divisor f₁ U)⁻ := by
  ext x
  by_cases hx : x ∈ U
  · suffices -(meromorphicOrderAt (f₁ + f₂) x).untop₀ ⊔ 0 = -(meromorphicOrderAt f₁ x).untop₀ ⊔ 0 by
      simpa [negPart_def, hx, hf₁, hf₁.add hf₂.meromorphicOn]
    by_cases h : 0 ≤ meromorphicOrderAt f₁ x
    · suffices 0 ≤ meromorphicOrderAt (f₁ + f₂) x by simp_all
      calc 0
      _ ≤ min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) :=
        le_inf h (hf₂ x hx).meromorphicOrderAt_nonneg
      _ ≤ meromorphicOrderAt (f₁ + f₂) x :=
        meromorphicOrderAt_add (hf₁ x hx) (hf₂ x hx).meromorphicAt
    · suffices meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x by
        rwa [meromorphicOrderAt_add_eq_left_of_lt (hf₂.meromorphicOn x hx)]
      calc meromorphicOrderAt f₁ x
      _ < 0 := by simpa using h
      _ ≤ meromorphicOrderAt f₂ x := (hf₂ x hx).meromorphicOrderAt_nonneg
  simp [hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
/-
**MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_left** 是 Mathlib 中的一个定理，位于命
名空间 `MeromorphicOn`。
形式化陈述：negPart_divisor_add_of_analyticNhdOn_left {f₁ f₂ : 𝕜 -> E} (hf₁ : Analytic
OnNhd 𝕜 f₁ U) (hf₂ : MeromorphicOn f₂ U) : (divisor (f₁ + f₂) U)⁻ = (divisor f₂ 
U)⁻
参数：hf₁ : AnalyticOnNhd 𝕜 f₁ U；hf₂ : MeromorphicOn f₂ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right`：negPart_diviso
r_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U) (hf₂ : 
AnalyticOnNhd 𝕜 f₂ U) : (divisor (f₁ + f₂) U)⁻…

--- 原说明 ---
Adding an analytic function to a meromorphic one does not change the pole diviso
r.
-/
theorem negPart_divisor_add_of_analyticNhdOn_left {f₁ f₂ : 𝕜 → E} (hf₁ : AnalyticOnNhd 𝕜 f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ = (divisor f₂ U)⁻ := by
  rw [add_comm]
  exact negPart_divisor_add_of_analyticNhdOn_right hf₂ hf₁

open WithTop in
/-- The divisor of the function `z ↦ z - z₀` at `x` is `0` if `x ≠ z₀`. -/
/-
**MeromorphicOn.divisor_sub_const_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn
`。
形式化陈述：divisor_sub_const_of_ne {U : Set 𝕜} {z₀ x : 𝕜} (hx : x != z₀) : divisor (·
 - z₀) U x = 0
参数：hx : x != z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
f g : 𝕜 → E…
· 使用引理 `MeromorphicOn.id`：id {U : Set 𝕜} : MeromorphicOn id U
· 使用引理 `MeromorphicOn.const`：const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ =>
 e) U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithTop.untop₀_coe`：untop₀_coe (a : α) : (a : WithTop α).untop₀ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0

--- 原说明 ---
The divisor of the function `z ↦ z - z₀` at `x` is `0` if `x ≠ z₀`.
-/
lemma divisor_sub_const_of_ne {U : Set 𝕜} {z₀ x : 𝕜} (hx : x ≠ z₀) : divisor (· - z₀) U x = 0 := by
  by_cases hu : x ∈ U
  · rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) hu,
      ← untop₀_coe 0]
    congr
    exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr
      ⟨(· - z₀), analyticAt_id.fun_sub analyticAt_const, by simp [sub_ne_zero_of_ne hx]⟩
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

open WithTop in
/-- The divisor of the function `z ↦ z - z₀` at `z₀` is `1`. -/
/-
**MeromorphicOn.divisor_sub_const_self** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`
。
形式化陈述：divisor_sub_const_self {z₀ : 𝕜} {U : Set 𝕜} (h : z₀ in U) : divisor (· - z
₀) U z₀ = 1
参数：h : z₀ in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicOn.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
f g : 𝕜 → E…
· 使用引理 `MeromorphicOn.id`：id {U : Set 𝕜} : MeromorphicOn id U
· 使用引理 `MeromorphicOn.const`：const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ =>
 e) U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithTop.untop₀_coe`：untop₀_coe (a : α) : (a : WithTop α).untop₀ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The divisor of the function `z ↦ z - z₀` at `z₀` is `1`.
-/
lemma divisor_sub_const_self {z₀ : 𝕜} {U : Set 𝕜} (h : z₀ ∈ U) : divisor (· - z₀) U z₀ = 1 := by
  rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) h, ← untop₀_coe 1]
  congr
  exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr ⟨fun _ ↦ 1, analyticAt_const, by simp⟩

open scoped Pointwise

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_add_const_eq_divisor]
/-
**MeromorphicOn.divisor_comp_add_const_eq_divisor** 是 Mathlib 中的一个定理，位于命名空间 `Mer
omorphicOn`。
形式化陈述：divisor_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 -> E} : divisor (f ∘ (·
 + c)) U (x - c) = divisor f (U + {c}) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeromorphicOn.meromorphicOn_comp_add_const_iff_meromorphicOn`：meromorphi
cOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} : MeromorphicOn (f ∘ (·
 + c)) U ↔ MeromorphicOn f (U + {c})
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn`：∀ {𝕜 : Type u_1} [in
st : NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜} {E : Type u_2} [inst_1 : Nor
medAddCommGroup E]   [inst_2 : NormedSpa…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.add_singleton`：∀ {α : Type u_2} [inst : Add α] {s : Set α} {b : α}, 
s + {b} = (fun x => x + b) '' s
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt`：meromorphicOrde
rAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 -> E} : meromorphicOrder
At (f ∘ (· + c)) x = meromorphicOrderAt f (x …
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
Divisors are invariant under translation.
-/
theorem divisor_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· + c)) U (x - c) = divisor f (U + {c}) x := by
  by_cases h : ¬ MeromorphicOn f (U + {c})
  · have := meromorphicOn_comp_add_const_iff_meromorphicOn.not.2 h
    simp_all
  rw [not_not] at h
  have := meromorphicOn_comp_add_const_iff_meromorphicOn.2 h
  by_cases h₁ : ¬ x ∈ (U + {c})
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> simp_all [← sub_eq_add_neg]
  rw [divisor_apply, divisor_apply]
  <;> simp_all [← sub_eq_add_neg, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_sub_const_eq_divisor]
/-
**MeromorphicOn.divisor_comp_sub_const_eq_divisor** 是 Mathlib 中的一个定理，位于命名空间 `Mer
omorphicOn`。
形式化陈述：divisor_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 -> E} : divisor (f ∘ (· -
 c)) U (z + c) = divisor f (U - {c}) z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.neg_singleton`：∀ {α : Type u_2} [inst : InvolutiveNeg α] (a : α), -{
a} = {-a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicOn.divisor_comp_add_const_eq_divisor`：divisor_comp_add_const_
eq_divisor {c x : 𝕜} {f : 𝕜 -> E} : divisor (f ∘ (· + c)) U (x - c) = divisor f 
(U + {c}) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Divisors are invariant under translation.
-/
theorem divisor_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) U (z + c) = divisor f (U - {c}) z := by
  rw [sub_eq_add_neg, Set.neg_singleton, ← divisor_comp_add_const_eq_divisor]
  simp_rw [← sub_eq_add_neg, sub_neg_eq_add]

/-- Divisors are invariant under translation, special case where the set is a ball.. -/
@[to_fun (attr := simp) divisor_ball_fun_comp_sub_const_eq_divisor_ball]
/-
**MeromorphicOn.divisor_ball_comp_sub_const_eq_divisor_ball** 是 Mathlib 中的一个定理，位
于命名空间 `MeromorphicOn`。
形式化陈述：divisor_ball_comp_sub_const_eq_divisor_ball {c : 𝕜} {R : Real} {f : 𝕜 -> E
} : divisor (f ∘ (· - c)) (ball c R) (z + c) = divisor f (ball 0 R) z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.divisor_comp_sub_const_eq_divisor`：divisor_comp_sub_const_
eq_divisor {c : 𝕜} {f : 𝕜 -> E} : divisor (f ∘ (· - c)) U (z + c) = divisor f (U
 - {c}) z
· 使用定理 `ball_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (
δ : ℝ) (x y : E), Metric.ball x δ - {y} = Metric.ball (x - y) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Divisors are invariant under translation, special case where the set is a ball..
-/
theorem divisor_ball_comp_sub_const_eq_divisor_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (ball c R) (z + c) = divisor f (ball 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor, ball_sub_singleton, sub_self]

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) divisor_closedBall_fun_comp_sub_const_eq_divisor_closedBall]
/-
**MeromorphicOn.divisor_closedBall_comp_sub_const_eq_divisor_closedBall** 是 Math
lib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_closedBall_comp_sub_const_eq_divisor_closedBall {c : 𝕜} {R : Real}
 {f : 𝕜 -> E} : divisor (f ∘ (· - c)) (closedBall c R) (z + c) = divisor f (clos
edBall 0 R) z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.divisor_comp_sub_const_eq_divisor`：divisor_comp_sub_const_
eq_divisor {c : 𝕜} {f : 𝕜 -> E} : divisor (f ∘ (· - c)) U (z + c) = divisor f (U
 - {c}) z
· 使用定理 `closedBall_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGrou
p E] (δ : ℝ) (x y : E),   Metric.closedBall x δ - {y} = Metric.closedBall (x - y
) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Divisors are invariant under translation, special case where the set is a closed
 ball.
-/
theorem divisor_closedBall_comp_sub_const_eq_divisor_closedBall {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (closedBall c R) (z + c) = divisor f (closedBall 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor, closedBall_sub_singleton, sub_self]

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) divisor_sphere_fun_comp_sub_const_eq_divisor_sphere]
/-
**MeromorphicOn.divisor_sphere_comp_sub_const_eq_divisor_sphere** 是 Mathlib 中的一个
定理，位于命名空间 `MeromorphicOn`。
形式化陈述：divisor_sphere_comp_sub_const_eq_divisor_sphere {c : 𝕜} {R : Real} {f : 𝕜 
-> E} : divisor (f ∘ (· - c)) (sphere c R) (z + c) = divisor f (sphere 0 R) z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.divisor_comp_sub_const_eq_divisor`：divisor_comp_sub_const_
eq_divisor {c : 𝕜} {f : 𝕜 -> E} : divisor (f ∘ (· - c)) U (z + c) = divisor f (U
 - {c}) z
· 使用定理 `sphere_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E]
 (δ : ℝ) (x y : E), Metric.sphere x δ - {y} = Metric.sphere (x - y) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Divisors are invariant under translation, special case where the set is a sphere
.
-/
theorem divisor_sphere_comp_sub_const_eq_divisor_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (sphere c R) (z + c) = divisor f (sphere 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor, sphere_sub_singleton, sub_self]

end MeromorphicOn

