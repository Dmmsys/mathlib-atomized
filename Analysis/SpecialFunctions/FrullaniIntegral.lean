/-
Copyright (c) 2026 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Frullani's integral

This file proves **Frullani's integral**: if `f : ℝ → E` is locally integrable on `(0, ∞)` with
`f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`, and `0 < a` and `0 < b`, then
`∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R)`
(`Frullani.integral_Ioi_eq`), provided the integrand is integrable on `(0, ∞)`.

We also prove a limit form `Frullani.tendsto_intervalIntegral`, which does not require global
integrability of the integrand.
-/

public section

open Real Set Filter MeasureTheory intervalIntegral Topology Metric

namespace Frullani

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
         {a b c : ℝ} {L R : E}

/-
**Frullani.intervalIntegrable_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 `Frullani`。
形式化陈述：intervalIntegrable_inv_smul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 <
 a) (hb : 0 < b) : IntervalIntegrable (fun x => x⁻¹ • f x) volume a b
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `IntervalIntegrable.continuousOn_smul`：continuousOn_smul (hg : IntervalIn
tegrable g μ a b) (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_inv₀`：continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ -> G₀)
 {0}ᶜ
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma intervalIntegrable_inv_smul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (fun x ↦ x⁻¹ • f x) volume a b := by
  have hsub : uIcc a b ⊆ Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_int : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset hsub isCompact_uIcc).mono_set uIoc_subset_uIcc)
  exact hf_int.continuousOn_smul (continuousOn_inv₀.mono fun x hx ↦ ne_of_gt (hsub hx))
/-
**Frullani.intervalIntegrable_inv_smul_comp_mul** 是 Mathlib 中的一个引理，位于命名空间 `Frull
ani`。
形式化陈述：intervalIntegrable_inv_smul_comp_mul (hf : LocallyIntegrableOn f (Ioi 0)) 
(ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : IntervalIntegrable (fun x => x⁻¹ • f (c
 * x)) volume a b
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `IntervalIntegrable.comp_mul_left`：comp_mul_left (hf : IntervalIntegrable
 f volume a b) {c : Real} (h : ‖f (min a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IntervalIntegrable.continuousOn_smul`：continuousOn_smul (hg : IntervalIn
tegrable g μ a b) (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_inv₀`：continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ -> G₀)
 {0}ᶜ
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma intervalIntegrable_inv_smul_comp_mul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) :
    IntervalIntegrable (fun x ↦ x⁻¹ • f (c * x)) volume a b := by
  have hsub : uIcc a b ⊆ Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_cint : IntervalIntegrable f volume (c * a) (c * b) :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset (by simp [uIcc, Icc_subset_Ioi_iff, mul_pos hc ha,
        mul_pos hc hb]) isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hf_comp : IntervalIntegrable (fun x ↦ f (c * x)) volume a b := by
    have h := hf_cint.comp_mul_left (c := c)
    rwa [mul_div_cancel_left₀ a hc.ne', mul_div_cancel_left₀ b hc.ne'] at h
  exact hf_comp.continuousOn_smul (continuousOn_inv₀.mono fun x hx ↦ ne_of_gt (hsub hx))
/-
**Frullani.integral_comp_mul_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 `Frullani`。
形式化陈述：integral_comp_mul_inv_smul {ε r : Real} (hc : c != 0) : ∫ x in ε..r, x⁻¹ •
 f (c * x) = ∫ x in c * ε..c * r, x⁻¹ • f x
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_subst`：eq_div_of_subst {M : Type*} [D
iv M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n) (hd : l_d = d) : l 
= n / d
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div'`：cons_eq_div_of_eq_di
v' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.
eval / t_d.eval) : ((-n, e) ::ᵣ t).eval …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 33 条，此处仅展示前 30 条）
-/
lemma integral_comp_mul_inv_smul {ε r : ℝ} (hc : c ≠ 0) :
    ∫ x in ε..r, x⁻¹ • f (c * x) = ∫ x in c * ε..c * r, x⁻¹ • f x := by
  let u : ℝ → E := fun x ↦ x⁻¹ • f x
  have key : (fun x ↦ x⁻¹ • f (c * x)) = fun x ↦ c • u (c * x) := by
    funext x
    simp only [u, smul_smul]
    congr 1
    field_simp
  rw [key, intervalIntegral.integral_smul, smul_integral_comp_mul_left]

variable [CompleteSpace E]
/-
**Frullani.norm_integral_inv_smul_sub_le** 是 Mathlib 中的一个引理，位于命名空间 `Frullani`。
形式化陈述：norm_integral_inv_smul_sub_le (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0
 < a) (hb : 0 < b) {V : E} {δ : Real} (hδ : 0 <= δ) (h : forall x in uIoc a b, ‖
f x - V‖ <= δ) : ‖(∫ x in a..b, x⁻¹ • f x) - log (b / a) • V‖ <= δ * |log (b / a
)|
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hδ : 0 <= δ；h : fora
ll x in uIoc a b, ‖f x - V‖ <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Frullani.intervalIntegrable_inv_smul`：intervalIntegrable_inv_smul (hf : 
LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable (f
un x => x⁻¹ • f x) volume …
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_inv₀`：continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ -> G₀)
 {0}ᶜ
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `intervalIntegral.integral_smul_const`：∀ {E : Type u_5} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {μ : MeasureTheory.Measure ℝ} 
  [CompleteSpace E] {𝕜 : T…
· 使用定理 `integral_inv_of_pos`：integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x
 in a..b, x⁻¹ = log (b / a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `intervalIntegral.norm_integral_le_abs_of_norm_le`：norm_integral_le_abs_o
f_norm_le {g : Real -> Real} (h : forallᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ <= g t) 
(hbound : IntervalIntegrable g μ a b) …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 59 条，此处仅展示前 30 条）
-/
lemma norm_integral_inv_smul_sub_le (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) {V : E} {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ x ∈ uIoc a b, ‖f x - V‖ ≤ δ) :
    ‖(∫ x in a..b, x⁻¹ • f x) - log (b / a) • V‖ ≤ δ * |log (b / a)| := by
  have hsub : uIcc a b ⊆ Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hint_f : IntervalIntegrable (fun x ↦ x⁻¹ • f x) volume a b :=
    intervalIntegrable_inv_smul hf ha hb
  have hint_V : IntervalIntegrable (fun x ↦ x⁻¹ • V) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_inv₀.mono (fun x hx ↦ ne_of_gt (hsub hx))).smul continuousOn_const
  have hint_inv : IntervalIntegrable (fun x : ℝ ↦ x⁻¹ * δ) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_inv₀.mono (fun x hx ↦ ne_of_gt (hsub hx))).mul continuousOn_const
  calc ‖(∫ x in a..b, x⁻¹ • f x) - log (b / a) • V‖
    _ = ‖∫ x in a..b, x⁻¹ • (f x - V)‖ := by
        congr 1
        have : log (b / a) • V = ∫ x in a..b, x⁻¹ • V := by
          rw [intervalIntegral.integral_smul_const (f := fun x ↦ (x⁻¹ : ℝ)) (c := V),
              integral_inv_of_pos ha hb]
        rw [this, ← integral_sub hint_f hint_V]
        congr 1
        funext x
        exact (smul_sub _ _ _).symm
    _ ≤ |∫ x in a..b, x⁻¹ * δ| := by
        apply norm_integral_le_abs_of_norm_le
        · exact (ae_restrict_mem measurableSet_uIoc).mono fun x hx ↦ by
            have hx_pos : 0 < x :=
              lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hx).1
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hx_pos)]
            exact mul_le_mul_of_nonneg_left (h x hx) (inv_nonneg.2 hx_pos.le)
        · exact hint_inv
    _ = δ * |log (b / a)| := by
        simp_rw [mul_comm, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
        exact (abs_mul δ (log (b / a))).trans (by rw [abs_of_nonneg hδ])
/-
**Frullani.tendsto_integral_inv_smul_of_tendsto_uniform** 是 Mathlib 中的一个引理，位于命名空
间 `Frullani`。
形式化陈述：tendsto_integral_inv_smul_of_tendsto_uniform (hf : LocallyIntegrableOn f (
Ioi 0)) (ha : 0 < a) (hb : 0 < b) {F : Filter Real} (hpos : forallᶠ t in F, 0 < 
t) {V : E} (huni : forall δ > 0, forallᶠ t in F, forall x in uIoc (a * t) (b * t
), ‖f x - V‖ <= δ) : Tendsto (fun t => ∫ x in (a * t)..(b * t), x⁻¹ • f x) F (𝓝 
(log (b / a) • V))
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hpos : forallᶠ t in 
F, 0 < t；huni : forall δ > 0, forallᶠ t in F, forall x in uIoc (a * t) (b * t), 
‖f x - V‖ <= δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `Frullani.norm_integral_inv_smul_sub_le`：norm_integral_inv_smul_sub_le (h
f : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) {V : E} {δ : Real} 
(hδ : 0 <= δ) (h : forall x …
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 50 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_inv_smul_of_tendsto_uniform (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) {F : Filter ℝ} (hpos : ∀ᶠ t in F, 0 < t) {V : E}
    (huni : ∀ δ > 0, ∀ᶠ t in F, ∀ x ∈ uIoc (a * t) (b * t), ‖f x - V‖ ≤ δ) :
    Tendsto (fun t ↦ ∫ x in (a * t)..(b * t), x⁻¹ • f x) F (𝓝 (log (b / a) • V)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set C := |log (b / a)| with hC_def
  set δ' := δ / (C + 1)
  filter_upwards [hpos, huni δ' (by positivity)] with t ht_pos hbound
  have hlog_eq : log (b * t / (a * t)) = log (b / a) := by
    rw [mul_div_mul_right b a (ne_of_gt ht_pos)]
  calc dist (∫ x in a * t..b * t, x⁻¹ • f x) (log (b / a) • V)
    _ = ‖(∫ x in a * t..b * t, x⁻¹ • f x) - log (b / a) • V‖ := dist_eq_norm _ _
    _ = ‖(∫ x in a * t..b * t, x⁻¹ • f x) - log (b * t / (a * t)) • V‖ := by rw [hlog_eq]
    _ ≤ δ' * |log (b * t / (a * t))| :=
        norm_integral_inv_smul_sub_le hf (by positivity) (by positivity) (by positivity) hbound
    _ = δ' * C := by rw [hlog_eq]
    _ = δ * (C / (C + 1)) := by ring
    _ < δ * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (lt_add_one C)) hδ
    _ = δ := mul_one δ
/-
**Frullani.tendsto_integral_inv_smul_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 `Frull
ani`。
形式化陈述：tendsto_integral_inv_smul_nhdsWithin (hf : LocallyIntegrableOn f (Ioi 0)) 
(ha : 0 < a) (hb : 0 < b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) : Tendsto (fun ε => ∫ 
x in (a * ε)..(b * ε), x⁻¹ • f x) (𝓝[>] 0) (𝓝 (log (b / a) • L))
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hL : Tendsto f (𝓝[>]
 0) (𝓝 L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Frullani.tendsto_integral_inv_smul_of_tendsto_uniform`：tendsto_integral_
inv_smul_of_tendsto_uniform (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (h
b : 0 < b) {F : Filter Real} (hpos : forall…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `max_mul_of_nonneg`：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <=
 c) : max a b * c = max (a * c) (b * c)
（共 40 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_inv_smul_nhdsWithin (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε ↦ ∫ x in (a * ε)..(b * ε), x⁻¹ • f x) (𝓝[>] 0) (𝓝 (log (b / a) • L)) := by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb self_mem_nhdsWithin
  intro δ hδ
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), dist (f x) L < δ :=
    hL.eventually (ball_mem_nhds L hδ)
  rw [Filter.Eventually, mem_nhdsWithin_iff] at hev
  obtain ⟨η, hη, hη_sub⟩ := hev
  set M := max a b with hM_def
  have hM : 0 < M := lt_max_of_lt_left ha
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hη hM))] with t ht_pos ht_bound
  intro x hx
  have hx_pos : 0 < x := (lt_min (by positivity) (by positivity)).trans_le (uIoc_subset_uIcc hx).1
  have hx_lt_η : dist x 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    calc x
      _ ≤ max (a * t) (b * t) := (uIoc_subset_uIcc hx).2
      _ = M * t := by rw [hM_def, max_mul_of_nonneg _ _ ht_pos.le]
      _ < M * (η / M) := mul_lt_mul_of_pos_left ht_bound hM
      _ = η := mul_div_cancel₀ η (ne_of_gt hM)
  have := hη_sub ⟨mem_ball.2 hx_lt_η, hx_pos⟩
  rw [mem_ofPred_eq, dist_eq_norm] at this
  exact le_of_lt this

/-- If `f → R` as `x → +∞` and `f` is locally integrable on `(0, ∞)`, then the weighted integral
`∫ x in a*r..b*r, x⁻¹ • f x` converges to `log(b/a) • R` as `r → +∞`. -/
/-
**Frullani.tendsto_integral_inv_smul_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Frullani`。
形式化陈述：tendsto_integral_inv_smul_atTop (hf : LocallyIntegrableOn f (Ioi 0)) (ha :
 0 < a) (hb : 0 < b) (hR : Tendsto f atTop (𝓝 R)) : Tendsto (fun r => ∫ x in (a 
* r)..(b * r), x⁻¹ • f x) atTop (𝓝 (log (b / a) • R))
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hR : Tendsto f atTop
 (𝓝 R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Frullani.tendsto_integral_inv_smul_of_tendsto_uniform`：tendsto_integral_
inv_smul_of_tendsto_uniform (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (h
b : 0 < b) {F : Filter Real} (hpos : forall…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
If `f → R` as `x → +∞` and `f` is locally integrable on `(0, ∞)`, then the weigh
ted integral
`∫ x in a*r..b*r, x⁻¹ • f x` converges to `log(b/a) • R` as `r → +∞`.
-/
lemma tendsto_integral_inv_smul_atTop (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun r ↦ ∫ x in (a * r)..(b * r), x⁻¹ • f x) atTop (𝓝 (log (b / a) • R)) := by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb
    (eventually_atTop.2 ⟨1, fun r hr ↦ zero_lt_one.trans_le hr⟩)
  intro δ hδ
  have hev : ∀ᶠ x in atTop, dist (f x) R < δ :=
    hR.eventually (ball_mem_nhds R hδ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hm : 0 < min a b := lt_min ha hb
  filter_upwards [eventually_atTop.2 ⟨max 1 (N / min a b), fun r hr ↦ hr⟩] with t ht
  intro x hx
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos ((le_max_left 1 _).trans ht)
  have hNx : N ≤ x :=
    calc N
      _ = min a b * (N / min a b) := by field_simp
      _ ≤ min a b * t :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans ht) hm.le
      _ = min (a * t) (b * t) := by rw [min_mul_of_nonneg _ _ ht_pos.le]
      _ ≤ x := (uIoc_subset_uIcc hx).1
  have hdist := hN x hNx
  rw [dist_eq_norm] at hdist
  exact le_of_lt hdist

/-- **Frullani's integral**, limit form, for functions valued in a complete normed space.
If `f` is locally integrable on `(0, ∞)` with `f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`,
and `0 < a` and `0 < b`, then `∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) → log (b / a) • (L - R)`
as `ε → 0⁺` and `r → +∞`. -/
/-
**Frullani.tendsto_intervalIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Frullani`。
形式化陈述：tendsto_intervalIntegral (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
 (hb : 0 < b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R)) : Ten
dsto (fun p : Real × Real => ∫ x in p.1..p.2, x⁻¹ • (f (a * x) - f (b * x))) ((𝓝
[>] 0) ×ˢ atTop) (𝓝 (log (b / a) • (L - R)))
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hL : Tendsto f (𝓝[>]
 0) (𝓝 L)；hR : Tendsto f atTop (𝓝 R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Frullani.intervalIntegrable_inv_smul`：intervalIntegrable_inv_smul (hf : 
LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable (f
un x => x⁻¹ • f x) volume …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用引理 `Frullani.intervalIntegrable_inv_smul_comp_mul`：intervalIntegrable_inv_sm
ul_comp_mul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) (hc :
 0 < c) : IntervalIntegrable (fun x…
· 使用引理 `Frullani.integral_comp_mul_inv_smul`：integral_comp_mul_inv_smul {ε r : R
eal} (hc : c != 0) : ∫ x in ε..r, x⁻¹ • f (c * x) = ∫ x in c * ε..c * r, x⁻¹ • f
 x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `intervalIntegral.integral_interval_sub_interval_comm`：integral_interval_
sub_interval_comm (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable f
 μ c d) (hac : IntervalIntegrable f μ a c)…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Frullani.tendsto_integral_inv_smul_nhdsWithin`：tendsto_integral_inv_smul
_nhdsWithin (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) (hL :
 Tendsto f (𝓝[>] 0) (𝓝 L)) : Tendst…
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**Frullani's integral**, limit form, for functions valued in a complete normed s
pace.
If `f` is locally integrable on `(0, ∞)` with `f x → L` as `x → 0⁺` and `f x → R
` as `x → +∞`,
and `0 < a` and `0 < b`, then `∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) → log 
(b / a) • (L - R)`
as `ε → 0⁺` and `r → +∞`.
-/
theorem tendsto_intervalIntegral (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun p : ℝ × ℝ ↦ ∫ x in p.1..p.2, x⁻¹ • (f (a * x) - f (b * x)))
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 (log (b / a) • (L - R))) := by
  let u := fun x ↦ x⁻¹ • f x
  have hint {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : IntervalIntegrable u volume p q :=
    intervalIntegrable_inv_smul hf hp hq
  have hsplit {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
      ∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) =
      (∫ x in (a * ε)..(b * ε), u x) - ∫ x in (a * r)..(b * r), u x := by
    calc ∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x))
      _ = (∫ x in ε..r, x⁻¹ • f (a * x)) - ∫ x in ε..r, x⁻¹ • f (b * x) := by
        simp_rw [smul_sub]
        exact integral_sub (intervalIntegrable_inv_smul_comp_mul hf hε hr ha)
          (intervalIntegrable_inv_smul_comp_mul hf hε hr hb)
      _ = (∫ y in a * ε..a * r, u y) - ∫ y in b * ε..b * r, u y := by
        rw [integral_comp_mul_inv_smul ha.ne', integral_comp_mul_inv_smul hb.ne']
      _ = _ := integral_interval_sub_interval_comm
                 (hint (mul_pos ha hε) (mul_pos ha hr))
                 (hint (mul_pos hb hε) (mul_pos hb hr))
                 (hint (mul_pos ha hε) (mul_pos hb hε))
  have h_ev : (fun p : ℝ × ℝ ↦ ∫ x in p.1..p.2, x⁻¹ • (f (a * x) - f (b * x))) =ᶠ[(𝓝[>] 0) ×ˢ atTop]
      fun p ↦ (∫ x in (a * p.1)..(b * p.1), u x) - ∫ x in (a * p.2)..(b * p.2), u x := by
    filter_upwards [prod_mem_prod (eventually_nhdsWithin_of_forall fun _ h ↦ h)
      (eventually_atTop.2 ⟨1, fun _ h ↦ lt_of_lt_of_le one_pos h⟩)] with ⟨ε, r⟩ ⟨hε, hr⟩
    exact hsplit hε hr
  rw [tendsto_congr' h_ev, show log (b / a) • (L - R) =
    log (b / a) • L - log (b / a) • R from smul_sub _ _ _]
  exact ((tendsto_integral_inv_smul_nhdsWithin hf ha hb hL).comp tendsto_fst).sub
    ((tendsto_integral_inv_smul_atTop hf ha hb hR).comp tendsto_snd)

/-- **Frullani's integral** for functions valued in a complete normed space.
If `f` is locally integrable on `(0, ∞)` with `f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`,
`0 < a` and `0 < b`, and `x ↦ x⁻¹ • (f (a * x) - f (b * x))` is integrable on `(0, ∞)`, then
`∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R)`. -/
/-
**Frullani.integral_Ioi_eq** 是 Mathlib 中的一个定理，位于命名空间 `Frullani`。
形式化陈述：integral_Ioi_eq (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 
< b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R)) (hint : Integr
ableOn (fun x => x⁻¹ • (f (a * x) - f (b * x))) (Ioi 0)) : ∫ x in Ioi 0, x⁻¹ • (
f (a * x) - f (b * x)) = log (b / a) • (L - R)
参数：hf : LocallyIntegrableOn f (Ioi 0)；ha : 0 < a；hb : 0 < b；hL : Tendsto f (𝓝[>]
 0) (𝓝 L)；hR : Tendsto f atTop (𝓝 R)；hint : IntegrableOn (fun x => x⁻¹ • (f (a *
 x) - f (b * x))) (Ioi 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Frullani.tendsto_intervalIntegral`：tendsto_intervalIntegral (hf : Locall
yIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L
)) (hR : Tendsto f atTo…
· 使用定理 `Filter.curry_le_prod`：curry_le_prod : l.curry m <= l ×ˢ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `MeasureTheory.IntegrableOn.continuousWithinAt_Ici_primitive_Ioi`：continu
ousWithinAt_Ici_primitive_Ioi {a₀ : Real} (hf : IntegrableOn f (Ioi a₀) μ) : Con
tinuousWithinAt (fun b => ∫ x in Ioi b, f x ∂μ) (Ici …
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Metric.tendsto_nhdsWithin_nhds`：tendsto_nhdsWithin_nhds [PseudoMetricSpa
ce β] {f : α -> β} {a b} : Tendsto f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0
, forall ⦃x : α⦄, x …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Filter.eventually_curry_iff`：eventually_curry_iff {p : α × β -> Prop} : 
(forallᶠ x : α × β in l.curry m, p x) ↔ forallᶠ x : α in l, forallᶠ y : β in m, 
p (x, y)
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
（共 102 条，此处仅展示前 30 条）

--- 原说明 ---
**Frullani's integral** for functions valued in a complete normed space.
If `f` is locally integrable on `(0, ∞)` with `f x → L` as `x → 0⁺` and `f x → R
` as `x → +∞`,
`0 < a` and `0 < b`, and `x ↦ x⁻¹ • (f (a * x) - f (b * x))` is integrable on `(
0, ∞)`, then
`∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R)`.
-/
theorem integral_Ioi_eq (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R))
    (hint : IntegrableOn (fun x ↦ x⁻¹ • (f (a * x) - f (b * x))) (Ioi 0)) :
    ∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R) := by
  have h_lim := (tendsto_intervalIntegral hf ha hb hL hR).mono_left curry_le_prod
  set g := fun x ↦ x⁻¹ • (f (a * x) - f (b * x)) with hg
  apply tendsto_nhds_unique
    (hint.continuousWithinAt_Ici_primitive_Ioi.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
  rw [tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds] at h_lim
  specialize h_lim (ε / 2) (by positivity)
  rw [eventually_curry_iff, Filter.Eventually, mem_nhdsWithin_iff] at h_lim
  obtain ⟨δ, hδ_pos, hδ⟩ := h_lim
  simp_rw [subset_def, mem_inter_iff, mem_ball] at hδ
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx hdist
  specialize hδ x ⟨hdist, hx⟩
  rw [mem_ofPred] at hδ
  have hint' : IntegrableOn g (Ioi x) := hint.mono (by grind) (by simp)
  have htends := intervalIntegral_tendsto_integral_Ioi x hint' tendsto_id
  have hle := le_of_tendsto (htends.dist tendsto_const_nhds) (hδ.mono (fun _ hy ↦ hy.le))
  linarith

end Frullani

