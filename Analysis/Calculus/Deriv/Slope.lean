/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Derivative as the limit of the slope

In this file we relate the derivative of a function with its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`.
Since we are talking about functions taking values in a normed space instead of the base field, we
use `slope f x y = (y - x)⁻¹ • (f y - f x)` instead of division.

We also prove some estimates on the upper/lower limits of the slope in terms of the derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, slope
-/

public section

universe u v

open scoped Topology

open Filter TopologicalSpace Set

section NormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `{x}ᶜ`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
/-
**hasDerivAtFilter_iff_tendsto_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} : HasDerivAtFilt
er f f' (L ×ˢ pure x) ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `tendsto_inf_principal_nhds_iff_of_forall_eq`：tendsto_inf_principal_nhds_
iff_of_forall_eq {f : α -> X} {l : Filter α} {s : Set α} (h : forall a ∉ s, f a 
= x) : Tendsto f (l ⊓ 𝓟 s) (𝓝 x) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `slope_same`：slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If the domain has dimension one, then Fréchet derivative is equivalent to the cl
assical
definition with a limit. In this version we have to take the limit along the sub
set `{x}ᶜ`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`.
-/
theorem hasDerivAtFilter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' (L ×ˢ pure x) ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') :=
  calc HasDerivAtFilter f f' (L ×ˢ pure x)
    _ ↔ Tendsto (fun y ↦ slope f x y - (y - x)⁻¹ • (y - x) • f') L (𝓝 0) := by
      simp only [hasDerivAtFilter_iff_tendsto, prod_pure, tendsto_map'_iff, Function.comp_def,
        ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero, slope_def_module, smul_sub]
    _ ↔ Tendsto (fun y ↦ slope f x y - (y - x)⁻¹ • (y - x) • f') (L ⊓ 𝓟 {x}ᶜ) (𝓝 0) :=
      .symm <| tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp
    _ ↔ Tendsto (fun y ↦ slope f x y - f') (L ⊓ 𝓟 {x}ᶜ) (𝓝 0) := tendsto_congr' <| by
      refine (EqOn.eventuallyEq fun y hy ↦ ?_).filter_mono inf_le_right
      rw [inv_smul_smul₀ (sub_ne_zero.2 hy) f']
    _ ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') := by
      rw [← nhds_translation_sub f', tendsto_comap_iff]; rfl
/-
**hasDerivWithinAt_iff_tendsto_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_iff_tendsto_slope : HasDerivWithinAt f f' s x ↔ Tendsto (
slope f x) (𝓝[s \ {x}] x) (𝓝 f')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `hasDerivAtFilter_iff_tendsto_slope`：hasDerivAtFilter_iff_tendsto_slope {
x : 𝕜} {L : Filter 𝕜} : HasDerivAtFilter f f' (L ×ˢ pure x) ↔ Tendsto (slope f x
) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f')
-/
theorem hasDerivWithinAt_iff_tendsto_slope :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') := by
  simp only [HasDerivWithinAt, nhdsWithin, sdiff_eq, ← inf_assoc, inf_principal.symm]
  exact hasDerivAtFilter_iff_tendsto_slope
/-
**hasDerivWithinAt_iff_tendsto_slope'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) : HasDerivWithinAt f f' s
 x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f')
参数：hs : x ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope`：hasDerivWithinAt_iff_tendsto_slope :
 HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f')
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f') := by
  rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self hs]
/-
**hasDerivAt_iff_tendsto_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[
!=] x) (𝓝 f')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_iff_tendsto_slope`：hasDerivAtFilter_iff_tendsto_slope {
x : 𝕜} {L : Filter 𝕜} : HasDerivAtFilter f f' (L ×ˢ pure x) ↔ Tendsto (slope f x
) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f')
-/
theorem hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
  hasDerivAtFilter_iff_tendsto_slope

alias ⟨HasDerivAt.tendsto_slope, _⟩ := hasDerivAt_iff_tendsto_slope
/-
**hasDerivAt_iff_tendsto_slope_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_tendsto_slope_left_right [LinearOrder 𝕜] : HasDerivAt f f' 
x ↔ Tendsto (slope f x) (𝓝[<] x) (𝓝 f') ∧ Tendsto (slope f x) (𝓝[>] x) (𝓝 f')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasDerivAt_iff_tendsto_slope_left_right [LinearOrder 𝕜] : HasDerivAt f f' x ↔
    Tendsto (slope f x) (𝓝[<] x) (𝓝 f') ∧ Tendsto (slope f x) (𝓝[>] x) (𝓝 f') := by
  simp [hasDerivAt_iff_tendsto_slope, ← Iio_union_Ioi, nhdsWithin_union]
/-
**hasDerivAt_iff_tendsto_slope_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_iff_tendsto_slope_zero : HasDerivAt f f' x ↔ Tendsto (fun t => 
t⁻¹ • (f (x + t) - f x)) (𝓝[!=] 0) (𝓝 f')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_add_left_nhdsNE`：∀ {G : Type w} [inst : TopologicalSpace G] [
inst_1 : AddGroup G] [SeparatelyContinuousAdd G] {c a : G},   Filter.map (fun x 
=> c + x) (nhdsW…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasDerivAt_iff_tendsto_slope_zero :
    HasDerivAt f f' x ↔ Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[≠] 0) (𝓝 f') := by
  have : 𝓝[≠] x = Filter.map (fun t ↦ x + t) (𝓝[≠] 0) := by simp
  simp [hasDerivAt_iff_tendsto_slope, this, -map_add_left_nhdsNE, slope, Function.comp_def]

alias ⟨HasDerivAt.tendsto_slope_zero, _⟩ := hasDerivAt_iff_tendsto_slope_zero
/-
**HasDerivAt.tendsto_slope_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasDerivAt f f' x) :
 Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[>] 0) (𝓝 f')
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `HasDerivAt.tendsto_slope_zero`：∀ {𝕜 : Type u} [inst : NontriviallyNormed
Field 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 
F] {f : 𝕜 → F} {f' …
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
-/
theorem HasDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[>] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)
/-
**HasDerivAt.tendsto_slope_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasDerivAt f f' x) : 
Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[<] 0) (𝓝 f')
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `HasDerivAt.tendsto_slope_zero`：∀ {𝕜 : Type u} [inst : NontriviallyNormed
Field 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 
F] {f : 𝕜 → F} {f' …
· 使用定理 `nhdsLT_le_nhdsNE`：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
-/
theorem HasDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[<] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

/-- Given a set `t` such that `s ∩ t` is dense in `s`, then the range of `derivWithin f s` is
contained in the closure of the submodule spanned by the image of `t`. -/
/-
**range_derivWithin_subset_closure_span_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_derivWithin_subset_closure_span_image (f : 𝕜 -> F) {s t : Set 𝕜} (h 
: s subseteq closure (s inter t)) : range (derivWithin f s) subseteq closure (Su
bmodule.span 𝕜 (f '' t))
参数：f : 𝕜 -> F；h : s subseteq closure (s inter t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `accPt_principal_iff_nhdsWithin`：accPt_principal_iff_nhdsWithin : AccPt x
 (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
· 使用定理 `uniqueDiffWithinAt_iff_accPt`：uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {
x : 𝕜} : UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s)
· 使用定理 `UniqueDiffWithinAt.mono_closure`：UniqueDiffWithinAt.mono_closure (h : Un
iqueDiffWithinAt 𝕜 s x) (st : s subseteq closure t) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope`：hasDerivWithinAt_iff_tendsto_slope :
 HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f')
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Submodule.topologicalClosure_coe`：Submodule.topologicalClosure_coe (s : 
Submodule R M) : (s.topologicalClosure : Set M) = closure (s : Set M)
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
Given a set `t` such that `s ∩ t` is dense in `s`, then the range of `derivWithi
n f s` is
contained in the closure of the submodule spanned by the image of `t`.
-/
theorem range_derivWithin_subset_closure_span_image
    (f : 𝕜 → F) {s t : Set 𝕜} (h : s ⊆ closure (s ∩ t)) :
    range (derivWithin f s) ⊆ closure (Submodule.span 𝕜 (f '' t)) := by
  rintro - ⟨x, rfl⟩
  by_cases H : UniqueDiffWithinAt 𝕜 s x; swap
  · simpa [derivWithin_zero_of_not_uniqueDiffWithinAt H] using subset_closure (zero_mem _)
  by_cases H' : DifferentiableWithinAt 𝕜 f s x; swap
  · rw [derivWithin_zero_of_not_differentiableWithinAt H']
    exact subset_closure (zero_mem _)
  have I : (𝓝[(s ∩ t) \ {x}] x).NeBot := by
    rw [← accPt_principal_iff_nhdsWithin, ← uniqueDiffWithinAt_iff_accPt]
    exact H.mono_closure h
  have : Tendsto (slope f x) (𝓝[(s ∩ t) \ {x}] x) (𝓝 (derivWithin f s x)) := by
    apply Tendsto.mono_left (hasDerivWithinAt_iff_tendsto_slope.1 H'.hasDerivWithinAt)
    rw [inter_comm, inter_sdiff_assoc]
    exact nhdsWithin_mono _ inter_subset_right
  rw [← closure_closure, ← Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto this
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope, vsub_eq_sub, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact mem_image_of_mem _ hy.1.2
  · apply Submodule.closure_subset_topologicalClosure_span
    suffices A : f x ∈ closure (f '' (s ∩ t)) from
      closure_mono (image_mono inter_subset_right) A
    apply ContinuousWithinAt.mem_closure_image
    · apply H'.continuousWithinAt.mono inter_subset_left
    rw [mem_closure_iff_nhdsWithin_neBot]
    exact I.mono (nhdsWithin_mono _ sdiff_subset)

/-- Given a dense set `t`, then the range of `deriv f` is contained in the closure of the submodule
spanned by the image of `t`. -/
/-
**range_deriv_subset_closure_span_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_deriv_subset_closure_span_image (f : 𝕜 -> F) {t : Set 𝕜} (h : Dense 
t) : range (deriv f) subseteq closure (Submodule.span 𝕜 (f '' t))
参数：f : 𝕜 -> F；h : Dense t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `range_derivWithin_subset_closure_span_image`：range_derivWithin_subset_cl
osure_span_image (f : 𝕜 -> F) {s t : Set 𝕜} (h : s subseteq closure (s inter t))
 : range (derivWithin f s) subset…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ

--- 原说明 ---
Given a dense set `t`, then the range of `deriv f` is contained in the closure o
f the submodule
spanned by the image of `t`.
-/
theorem range_deriv_subset_closure_span_image
    (f : 𝕜 → F) {t : Set 𝕜} (h : Dense t) :
    range (deriv f) ⊆ closure (Submodule.span 𝕜 (f '' t)) := by
  rw [← derivWithin_univ]
  apply range_derivWithin_subset_closure_span_image
  simp [dense_iff_closure_eq.1 h]
/-
**isSeparable_range_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeparable_range_derivWithin [SeparableSpace 𝕜] (f : 𝕜 -> F) (s : Set 𝕜) 
: IsSeparable (range (derivWithin f s))
参数：f : 𝕜 -> F；s : Set 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsSeparable.exists_countable_dense_subset`：∀ {X : Type 
u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s :
 Set X},   TopologicalSpace.IsSeparable s → ∃ t …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsSeparable.of_separableSpace`：∀ {α : Type u} [t : Topo
logicalSpace α] [h : TopologicalSpace.SeparableSpace α] (s : Set α),   Topologic
alSpace.IsSeparable s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `TopologicalSpace.IsSeparable.mono`：∀ {α : Type u} [t : TopologicalSpace 
α] {s u : Set α},   TopologicalSpace.IsSeparable s → u ⊆ s → TopologicalSpace.Is
Separable u
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用引理 `TopologicalSpace.IsSeparable.span`：TopologicalSpace.IsSeparable.span {R 
M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] [TopologicalSpace M] [Top
ologicalSpace R] [Separ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.Countable.isSeparable`：∀ {α : Type u} [t : TopologicalSpace α] {s : 
Set α}, s.Countable → TopologicalSpace.IsSeparable s
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `range_derivWithin_subset_closure_span_image`：range_derivWithin_subset_cl
osure_span_image (f : 𝕜 -> F) {s t : Set 𝕜} (h : s subseteq closure (s inter t))
 : range (derivWithin f s) subset…
-/
theorem isSeparable_range_derivWithin [SeparableSpace 𝕜] (f : 𝕜 → F) (s : Set 𝕜) :
    IsSeparable (range (derivWithin f s)) := by
  obtain ⟨t, ts, t_count, ht⟩ : ∃ t, t ⊆ s ∧ Set.Countable t ∧ s ⊆ closure t :=
    (IsSeparable.of_separableSpace s).exists_countable_dense_subset
  have : s ⊆ closure (s ∩ t) := by rwa [inter_eq_self_of_subset_right ts]
  apply IsSeparable.mono _ (range_derivWithin_subset_closure_span_image f this)
  exact (Countable.image t_count f).isSeparable.span.closure
/-
**isSeparable_range_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeparable_range_deriv [SeparableSpace 𝕜] (f : 𝕜 -> F) : IsSeparable (ran
ge (deriv f))
参数：f : 𝕜 -> F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `isSeparable_range_derivWithin`：isSeparable_range_derivWithin [SeparableS
pace 𝕜] (f : 𝕜 -> F) (s : Set 𝕜) : IsSeparable (range (derivWithin f s))
-/
theorem isSeparable_range_deriv [SeparableSpace 𝕜] (f : 𝕜 → F) :
    IsSeparable (range (deriv f)) := by
  rw [← derivWithin_univ]
  exact isSeparable_range_derivWithin _ _
/-
**HasDerivAt.continuousAt_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.continuousAt_div [DecidableEq 𝕜] {f : 𝕜 -> 𝕜} {c a : 𝕜} (hf : H
asDerivAt f a c) : ContinuousAt (Function.update (fun x => (f x - f c) / (x - c)
) c a) c
参数：hf : HasDerivAt f a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `slope_fun_def_field`：slope_fun_def_field (f : k -> k) (a : k) : slope f 
a = fun b => (f b - f a) / (b - a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_update_same`：continuousAt_update_same [DecidableEq α] {y : 
β} : ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[!=] x) (𝓝 y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_iff_tendsto_slope`：hasDerivAt_iff_tendsto_slope : HasDerivAt 
f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f')
-/
lemma HasDerivAt.continuousAt_div [DecidableEq 𝕜] {f : 𝕜 → 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c) :
    ContinuousAt (Function.update (fun x ↦ (f x - f c) / (x - c)) c a) c := by
  rw [← slope_fun_def_field]
  exact continuousAt_update_same.mpr <| hasDerivAt_iff_tendsto_slope.mp hf

section Order

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {g : 𝕜 → 𝕜} {g' : 𝕜}

/-- If a monotone function has a derivative within a set at a non-isolated point, then this
derivative is nonnegative. -/
/-
**HasDerivWithinAt.nonneg_of_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.nonneg_of_monotoneOn (hx : AccPt x (𝓟 s)) (hd : HasDerivW
ithinAt g g' s x) (hg : MonotoneOn g s) : 0 <= g'
参数：hx : AccPt x (𝓟 s)；hd : HasDerivWithinAt g g' s x；hg : MonotoneOn g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `accPt_principal_iff_nhdsWithin`：accPt_principal_iff_nhdsWithin : AccPt x
 (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
· 使用引理 `MonotoneOn.insert_of_continuousWithinAt`：MonotoneOn.insert_of_continuous
WithinAt [TopologicalSpace β] [OrderClosedTopology β] (hf : MonotoneOn f s) (hx 
: ClusterPt x (𝓟 s)) (h'x : C…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `AccPt.clusterPt`：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) 
: ClusterPt x F
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope`：hasDerivWithinAt_iff_tendsto_slope :
 HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f')
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `MonotoneOn.slope_nonneg`：MonotoneOn.slope_nonneg {s : Set k} (hf : Monot
oneOn f s) (hx : x in s) (hy : y in s) : 0 <= slope f x y
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If a monotone function has a derivative within a set at a non-isolated point, th
en this
derivative is nonnegative.
-/
lemma HasDerivWithinAt.nonneg_of_monotoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s) : 0 ≤ g' := by
  have : (𝓝[s \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp hx
  have h'g : MonotoneOn g (insert x s) :=
    hg.insert_of_continuousWithinAt hx.clusterPt hd.continuousWithinAt
  have : Tendsto (slope g x) (𝓝[s \ {x}] x) (𝓝 g') := hasDerivWithinAt_iff_tendsto_slope.mp hd
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Set.mem_sdiff, mem_singleton_iff] at hy
  exact h'g.slope_nonneg (by simp) (by simp [hy])

/-- The derivative within a set of a monotone function is nonnegative. -/
/-
**MonotoneOn.derivWithin_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.derivWithin_nonneg (hg : MonotoneOn g s) : 0 <= derivWithin g s
 x
参数：hg : MonotoneOn g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasDerivWithinAt.nonneg_of_monotoneOn`：HasDerivWithinAt.nonneg_of_monoto
neOn (hx : AccPt x (𝓟 s)) (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s)
 : 0 <= g'
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_accPt`：derivWithin_zero_of_not_accPt (h : ¬AccPt
 x (𝓟 s)) : derivWithin f s x = 0
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0

--- 原说明 ---
The derivative within a set of a monotone function is nonnegative.
-/
lemma MonotoneOn.derivWithin_nonneg (hg : MonotoneOn g s) :
    0 ≤ derivWithin g s x := by
  by_cases hd : DifferentiableWithinAt 𝕜 g s x; swap
  · simp [derivWithin_zero_of_not_differentiableWithinAt hd]
  by_cases hx : AccPt x (𝓟 s); swap
  · simp [derivWithin_zero_of_not_accPt hx]
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hx hg

/-- If a monotone function has a derivative, then this derivative is nonnegative. -/
/-
**HasDerivAt.nonneg_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.nonneg_of_monotone (hd : HasDerivAt g g' x) (hg : Monotone g) :
 0 <= g'
参数：hd : HasDerivAt g g' x；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HasDerivWithinAt.nonneg_of_monotoneOn`：HasDerivWithinAt.nonneg_of_monoto
neOn (hx : AccPt x (𝓟 s)) (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s)
 : 0 <= g'
· 使用定理 `PerfectSpace.univ_preperfect`：∀ {α : Type u_1} {inst : TopologicalSpace 
α} [self : PerfectSpace α], Preperfect Set.univ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
If a monotone function has a derivative, then this derivative is nonnegative.
-/
lemma HasDerivAt.nonneg_of_monotone (hd : HasDerivAt g g' x) (hg : Monotone g) : 0 ≤ g' := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonneg_of_monotoneOn _ (hg.monotoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/-- The derivative of a monotone function is nonnegative. -/
/-
**Monotone.deriv_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.deriv_nonneg (hg : Monotone g) : 0 <= deriv g x
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用引理 `MonotoneOn.derivWithin_nonneg`：MonotoneOn.derivWithin_nonneg (hg : Monot
oneOn g s) : 0 <= derivWithin g s x
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
The derivative of a monotone function is nonnegative.
-/
lemma Monotone.deriv_nonneg (hg : Monotone g) : 0 ≤ deriv g x := by
  rw [← derivWithin_univ]
  exact (hg.monotoneOn univ).derivWithin_nonneg

/-- If an antitone function has a derivative within a set at a non-isolated point, then this
derivative is nonpositive. -/
/-
**HasDerivWithinAt.nonpos_of_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.nonpos_of_antitoneOn (hx : AccPt x (𝓟 s)) (hd : HasDerivW
ithinAt g g' s x) (hg : AntitoneOn g s) : g' <= 0
参数：hx : AccPt x (𝓟 s)；hd : HasDerivWithinAt g g' s x；hg : AntitoneOn g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `HasDerivWithinAt.nonneg_of_monotoneOn`：HasDerivWithinAt.nonneg_of_monoto
neOn (hx : AccPt x (𝓟 s)) (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s)
 : 0 <= g'
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x

--- 原说明 ---
If an antitone function has a derivative within a set at a non-isolated point, t
hen this
derivative is nonpositive.
-/
lemma HasDerivWithinAt.nonpos_of_antitoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : AntitoneOn g s) : g' ≤ 0 := by
  have : MonotoneOn (-g) s := fun x hx y hy hxy ↦ by simpa using hg hx hy hxy
  simpa using hd.neg.nonneg_of_monotoneOn hx this

/-- The derivative within a set of an antitone function is nonpositive. -/
/-
**AntitoneOn.derivWithin_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.derivWithin_nonpos (hg : AntitoneOn g s) : derivWithin g s x <=
 0
参数：hg : AntitoneOn g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {
F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 
→ F} {x :…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `MonotoneOn.derivWithin_nonneg`：MonotoneOn.derivWithin_nonneg (hg : Monot
oneOn g s) : 0 <= derivWithin g s x
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
The derivative within a set of an antitone function is nonpositive.
-/
lemma AntitoneOn.derivWithin_nonpos (hg : AntitoneOn g s) :
    derivWithin g s x ≤ 0 := by
  simpa [derivWithin.fun_neg] using hg.neg.derivWithin_nonneg

/-- If an antitone function has a derivative, then this derivative is nonpositive. -/
/-
**HasDerivAt.nonpos_of_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.nonpos_of_antitone (hd : HasDerivAt g g' x) (hg : Antitone g) :
 g' <= 0
参数：hd : HasDerivAt g g' x；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HasDerivWithinAt.nonpos_of_antitoneOn`：HasDerivWithinAt.nonpos_of_antito
neOn (hx : AccPt x (𝓟 s)) (hd : HasDerivWithinAt g g' s x) (hg : AntitoneOn g s)
 : g' <= 0
· 使用定理 `PerfectSpace.univ_preperfect`：∀ {α : Type u_1} {inst : TopologicalSpace 
α} [self : PerfectSpace α], Preperfect Set.univ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s

--- 原说明 ---
If an antitone function has a derivative, then this derivative is nonpositive.
-/
lemma HasDerivAt.nonpos_of_antitone (hd : HasDerivAt g g' x) (hg : Antitone g) : g' ≤ 0 := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonpos_of_antitoneOn _ (hg.antitoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/-- The derivative of an antitone function is nonpositive. -/
/-
**Antitone.deriv_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.deriv_nonpos (hg : Antitone g) : deriv g x <= 0
参数：hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用引理 `AntitoneOn.derivWithin_nonpos`：AntitoneOn.derivWithin_nonpos (hg : Antit
oneOn g s) : derivWithin g s x <= 0
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s

--- 原说明 ---
The derivative of an antitone function is nonpositive.
-/
lemma Antitone.deriv_nonpos (hg : Antitone g) : deriv g x ≤ 0 := by
  rw [← derivWithin_univ]
  exact (hg.antitoneOn univ).derivWithin_nonpos

end Order

end NormedField

/-! ### Upper estimates on liminf and limsup -/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ} {r : ℝ}

/-
**HasDerivWithinAt.limsup_slope_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f'
 < r) : forallᶠ z in 𝓝[s \ {x}] x, slope f x z < r
参数：hf : HasDerivWithinAt f f' s x；hr : f' < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope`：hasDerivWithinAt_iff_tendsto_slope :
 HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f')
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    ∀ᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
  hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)
/-
**HasDerivWithinAt.limsup_slope_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x
 ∉ s) (hr : f' < r) : forallᶠ z in 𝓝[s] x, slope f x z < r
参数：hf : HasDerivWithinAt f f' s x；hs : x ∉ s；hr : f' < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope'`：hasDerivWithinAt_iff_tendsto_slope'
 (hs : x ∉ s) : HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f')
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
    (hr : f' < r) : ∀ᶠ z in 𝓝[s] x, slope f x z < r :=
  (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)
/-
**HasDerivWithinAt.liminf_right_slope_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x)
 x) (hr : f' < r) : existsᶠ z in 𝓝[>] x, slope f x z < r
参数：hf : HasDerivWithinAt f f' (Ici x) x；hr : f' < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
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
· 使用定理 `HasDerivWithinAt.limsup_slope_le'`：HasDerivWithinAt.limsup_slope_le' (hf
 : HasDerivWithinAt f f' s x) (hs : x ∉ s) (hr : f' < r) : forallᶠ z in 𝓝[s] x, 
slope f x z < r
· 使用定理 `HasDerivWithinAt.Ioi_of_Ici`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {f' …
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : f' < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r :=
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

end Real

section RealSpace

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {s : Set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`. -/
/-
**HasDerivWithinAt.limsup_norm_slope_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr
 : ‖f'‖ < r) : forallᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r
参数：hf : HasDerivWithinAt f f' s x；hr : ‖f'‖ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope`：hasDerivWithinAt_iff_tendsto_slope :
 HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f')
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.
-/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r := by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)
  have B : ∀ᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    mem_of_superset self_mem_nhdsWithin (singleton_subset_iff.2 <| by simp [hr₀])
  have C := mem_sup.2 ⟨A, B⟩
  rw [← nhdsWithin_union, sdiff_union_self, nhdsWithin_union, mem_sup] at C
  filter_upwards [C.1]
  simp only [norm_smul, mem_Iio, norm_inv]
  exact fun _ => id

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `HasDerivWithinAt.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`. -/
/-
**HasDerivWithinAt.limsup_slope_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr
 : ‖f'‖ < r) : forallᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r
参数：hf : HasDerivWithinAt f f' s x；hr : ‖f'‖ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasDerivWithinAt.limsup_norm_slope_le`：HasDerivWithinAt.limsup_norm_slop
e_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) : forallᶠ z in 𝓝[s] x, ‖z 
- x‖⁻¹ * ‖f z - f x‖ < r
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖
· 使用定理 `inv_nonneg_of_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_
1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a → 0 ≤ a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` in some neighborhood of `x` within 
`s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `HasDerivWithinAt.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`.
-/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) (by positivity)) hz

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `HasDerivWithinAt.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
/-
**HasDerivWithinAt.liminf_right_norm_slope_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (I
ci x) x) (hr : ‖f'‖ < r) : existsᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r
参数：hf : HasDerivWithinAt f f' (Ici x) x；hr : ‖f'‖ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
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
· 使用定理 `HasDerivWithinAt.limsup_norm_slope_le`：HasDerivWithinAt.limsup_norm_slop
e_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) : forallᶠ z in 𝓝[s] x, ‖z 
- x‖⁻¹ * ‖f z - f x‖ < r
· 使用定理 `HasDerivWithinAt.Ioi_of_Ici`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {f' …

--- 原说明 ---
If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the 
ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `HasDerivWithinAt.limsup_norm_slope_le
`
for a stronger version using limit superior and any set `s`.
-/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
  (hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `HasDerivWithinAt.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `HasDerivWithinAt.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f xp‖` instead of `‖f z‖ - ‖f x‖`. -/
/-
**HasDerivWithinAt.liminf_right_slope_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (I
ci x) x) (hr : ‖f'‖ < r) : existsᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r
参数：hf : HasDerivWithinAt f f' (Ici x) x；hr : ‖f'‖ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
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
· 使用定理 `HasDerivWithinAt.limsup_slope_norm_le`：HasDerivWithinAt.limsup_slope_nor
m_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) : forallᶠ z in 𝓝[s] x, ‖z 
- x‖⁻¹ * (‖f z‖ - ‖f x‖) < …
· 使用定理 `HasDerivWithinAt.Ioi_of_Ici`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {f' …
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|

--- 原说明 ---
If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the 
ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `HasDerivWithinAt.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `HasDerivWithinAt.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f xp‖` instead of `‖f z‖ - ‖f x‖`.
-/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently
  refine this.mp (Eventually.mono self_mem_nhdsWithin fun z hxz hz ↦ ?_)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz

end RealSpace

