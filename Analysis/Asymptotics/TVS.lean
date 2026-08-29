/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Convex.EGauge
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Asymptotics in a Topological Vector Space

This file defines `Asymptotics.IsLittleOTVS`, `Asymptotics.IsBigOTVS`, and `Asymptotics.IsThetaTVS`
as generalizations of `Asymptotics.IsLittleO`, `Asymptotics.IsBigO`, and `Asymptotics.IsTheta`
from normed spaces to topological vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ (resp., $f = O(g)$)
if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g(x)))$
(resp., $\operatorname{gauge}_{K, U} (f(x)) = O(\operatorname{gauge}_{K, V} (g(x)))$),
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

We say that $f=Θ(g)$, if both $f=O(g)$ and $g=O(f)$.

In a normed space, we can use balls of positive radius as both `U` and `V`,
thus reducing the definition to the classical one.

These modifications of the definitions free the user from having to chose a canonical norm,
at the expense of having to pick a specific base field.
This is exactly the tradeoff we want in `HasFDerivAtFilter`,
as there the base field is already chosen,
and this removes the choice of norm being part of the statement.

These definitions were added to the library in order to migrate Fréchet derivatives
from normed vector spaces to topological vector spaces.
The definitions are motivated by
https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative#Generalization_to_topological_vector_spaces
but the definition there doesn't work for topological vector spaces over general normed fields.
[This Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/generalizing.20deriv.20to.20TVS)
led to the current choice of the definition of `Asymptotics.IsLittleOTVS`,
and `Asymptotics.IsBigOTVS` was defined in a similar manner.

## Main results

* `isLittleOTVS_iff_isLittleO`: the equivalence between these two definitions in the case of a
  normed space.

* `isLittleOTVS_iff_tendsto_inv_smul`: the equivalence to convergence of the ratio to zero
  in case of a topological vector space.

## TODO

- Add `Asymptotics.IsEquivalentTVS`.
- Prove a version of `Asymptotics.isBigO_one` for `IsBigOTVS`.

-/

@[expose] public section

open Set Filter Asymptotics Metric
open scoped Topology Pointwise ENNReal NNReal

namespace Asymptotics

section Defs

variable (𝕜 : Type*) {α E F : Type*}
  [ENorm 𝕜] [TopologicalSpace E] [TopologicalSpace F] [Zero E] [Zero F] [SMul 𝕜 E] [SMul 𝕜 F]

/-- `f =o[𝕜; l] g` (`IsLittleOTVS 𝕜 l f g`) is a generalization of `f =o[l] g` (`IsLittleO l f g`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g(x)))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

We use an `ENNReal`-valued function `egauge` for the gauge,
so we unfold the definition of little o instead of reusing it. -/
@[mk_iff]
/--
Definition of `IsLittleOTVS` / `IsLittleOTVS` 的定义

English:
structure IsLittleOTVS
  parameters: (l : Filter α) (f : α -> E) (g : α -> F)
  axioms and operations (1):
    - exists_eventuallyLE_mul : forall U in 𝓝 (0 : E), exists V in 𝓝 (0 : F), forall ε != (0 : Real>=0), (fun x => egauge 𝕜 U (f x)) <=ᶠ[l] (fun x => ε * egauge 𝕜 V (g x))

中文:
结构 是LittleOTVS
  参数: (l : 滤子 α) (f : α -> E) (g : α -> F)
  公理与运算 (1 个):
    - exists_eventuallyLE_mul : 对任意 U in 𝓝 (0 : E), 存在 V in 𝓝 (0 : F), 对任意 ε != (0 : 实数>=0), (fun x => egauge 𝕜 U (f x)) <=ᶠ[l] (fun x => ε * egauge 𝕜 V (g x))
-/
structure IsLittleOTVS (l : Filter α) (f : α -> E) (g : α -> F) : Prop where
  exists_eventuallyLE_mul : forall U in 𝓝 (0 : E), exists V in 𝓝 (0 : F), forall ε != (0 : Real>=0),
    (fun x => egauge 𝕜 U (f x)) <=ᶠ[l] (fun x => ε * egauge 𝕜 V (g x))

@[inherit_doc]
notation:100 f " =o[" 𝕜 "; " l "] " g:100 => IsLittleOTVS 𝕜 l f g

/-- `f =O[𝕜; l] g` (`IsBigOTVS 𝕜 l f g`) is a generalization of `f =O[l] g` (`IsBigO l f g`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `𝕜`,
we say that $f = O(g)$ if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) \le \operatorname{gauge}_{K, V} (g(x))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.
-/
@[mk_iff]
/--
Definition of `IsBigOTVS` / `IsBigOTVS` 的定义

English:
structure IsBigOTVS
  parameters: (l : Filter α) (f : α -> E) (g : α -> F)
  axioms and operations (1):
    - exists_eventuallyLE : forall U in 𝓝 (0 : E), exists V in 𝓝 (0 : F), (egauge 𝕜 U <| f ·) <=ᶠ[l] (egauge 𝕜 V <| g ·)

中文:
结构 是BigOTVS
  参数: (l : 滤子 α) (f : α -> E) (g : α -> F)
  公理与运算 (1 个):
    - exists_eventuallyLE : 对任意 U in 𝓝 (0 : E), 存在 V in 𝓝 (0 : F), (egauge 𝕜 U <| f ·) <=ᶠ[l] (egauge 𝕜 V <| g ·)
-/
structure IsBigOTVS (l : Filter α) (f : α -> E) (g : α -> F) : Prop where
  exists_eventuallyLE : forall U in 𝓝 (0 : E), exists V in 𝓝 (0 : F),
    (egauge 𝕜 U <| f ·) <=ᶠ[l] (egauge 𝕜 V <| g ·)

@[inherit_doc]
notation:100 f " =O[" 𝕜 "; " l "] " g:100 => IsBigOTVS 𝕜 l f g

/--
Definition of `IsThetaTVS` / `IsThetaTVS` 的定义

English:
definition IsThetaTVS
  signature: (l : Filter α) (f : α -> E) (g : α -> F)
  body: (f =O[𝕜; l] g) ∧ (g =O[𝕜; l] f)

@[inherit_doc]
notation:100 f " =Θ[" 𝕜 "; " l "] " g:100 => IsThetaTVS 𝕜 l f g

中文:
定义 IsThetaTVS
  签名: (l : 滤子 α) (f : α -> E) (g : α -> F)
  定义体: (f =O[𝕜; l] g) ∧ (g =O[𝕜; l] f)

@[inherit_doc]
notation:100 f " =Θ[" 𝕜 "; " l "] " g:100 => IsThetaTVS 𝕜 l f g
-/
def IsThetaTVS (l : Filter α) (f : α -> E) (g : α -> F) : Prop :=
  (f =O[𝕜; l] g) ∧ (g =O[𝕜; l] f)

@[inherit_doc]
notation:100 f " =Θ[" 𝕜 "; " l "] " g:100 => IsThetaTVS 𝕜 l f g

end Defs

variable {α β 𝕜 E F G : Type*}

section TopologicalSpace

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

section congr

variable {f f₁ f₂ : α -> E} {g g₁ g₂ : α -> F} {l : Filter α}

/--
theorem `isLittleOTVS_iff_tendsto_div` / 定理 `isLittleOTVS_iff_tendsto_div`

English:
theorem isLittleOTVS_iff_tendsto_div
  proof: by
  simp only [isLittleOTVS_iff, ← ENNReal.coe_zero, ENNReal.nhds_coe, ← NNReal.bot_eq_zero,
    (nhds_bot_basis_Iic.map _).tendsto_right_iff]
  simp +contextual [ENNReal.div_le_iff_le_mul, pos_iff_ne_zero, EventuallyLE]

alias ⟨IsLittleOTVS.tendsto_div, IsLittleOTVS.of_tendsto_div⟩ := isLittleOTVS_iff_tendsto_div

中文:
定理 isLittleOTVS_iff_tendsto_div
  证明: by
  simp only [isLittleOTVS_iff, ← ENNReal.coe_zero, ENNReal.nhds_coe, ← NNReal.bot_eq_zero,
    (nhds_bot_basis_Iic.map _).tendsto_right_iff]
  simp +contextual [ENNReal.div_le_iff_le_mul, pos_iff_ne_zero, EventuallyLE]

alias ⟨IsLittleOTVS.tendsto_div, IsLittleOTVS.of_tendsto_div⟩ := isLittleOTVS_iff_tendsto_div

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.div_le_iff_le_mul, ENNReal.nhds_coe, EventuallyLE, NNReal, NNReal.bot_eq_zero, bot_eq_zero, coe_zero, contextual, div_le_iff_le_mul, isLittleOTVS_iff, nhds_bot_basis_Iic, nhds_bot_basis_Iic.map, nhds_coe, pos_iff_ne_zero, tendsto_right_iff
-/
theorem isLittleOTVS_iff_tendsto_div :
    f =o[𝕜; l] g ↔ forall U in 𝓝 0, exists V in 𝓝 0,
      Tendsto (fun x => egauge 𝕜 U (f x) / egauge 𝕜 V (g x)) l (𝓝 0) := by
  simp only [isLittleOTVS_iff, ← ENNReal.coe_zero, ENNReal.nhds_coe, ← NNReal.bot_eq_zero,
    (nhds_bot_basis_Iic.map _).tendsto_right_iff]
  simp +contextual [ENNReal.div_le_iff_le_mul, pos_iff_ne_zero, EventuallyLE]

alias ⟨IsLittleOTVS.tendsto_div, IsLittleOTVS.of_tendsto_div⟩ := isLittleOTVS_iff_tendsto_div

/--
theorem `IsLittleOTVS.exists_eventuallyLE_mul_ennreal` / 定理 `IsLittleOTVS.exists_eventuallyLE_mul_ennreal`

English:
theorem IsLittleOTVS.exists_eventuallyLE_mul_ennreal
  given: (h : f =o[𝕜; l] g) {U : Set E} (hU : U in 𝓝 0)
  proof: by
  obtain ⟨V, hV₀, hV⟩ := h.exists_eventuallyLE_mul U hU
  refine ⟨V, hV₀, fun ε hε => ?_⟩
  cases ε with
| top => exact (hV 1 one_ne_zero).trans .of_forall fun _ => by dsimp; grw [← le_top]
  | coe ε => exact hV ε (mod_cast hε)

中文:
定理 是LittleOTVS.存在_eventuallyLE_mul_ennreal
  条件: (h : f =o[𝕜; l] g) {U : 集合 E} (hU : U in 𝓝 0)
  证明: by
  obtain ⟨V, hV₀, hV⟩ := h.exists_eventuallyLE_mul U hU
  refine ⟨V, hV₀, fun ε hε => ?_⟩
  cases ε with
| top => exact (hV 1 one_ne_zero).trans .of_forall fun _ => by dsimp; grw [← le_top]
  | coe ε => exact hV ε (mod_cast hε)

Depends on / 依赖: exists_eventuallyLE_mul, h.exists_eventuallyLE_mul, le_top, mod_cast, of_forall, one_ne_zero
-/
theorem IsLittleOTVS.exists_eventuallyLE_mul_ennreal (h : f =o[𝕜; l] g) {U : Set E} (hU : U in 𝓝 0) :
    exists V in 𝓝 (0 : F), forall ε != 0, (fun x => egauge 𝕜 U (f x)) <=ᶠ[l] (fun x => ε * egauge 𝕜 V (g x)) := by
  obtain ⟨V, hV₀, hV⟩ := h.exists_eventuallyLE_mul U hU
  refine ⟨V, hV₀, fun ε hε => ?_⟩
  cases ε with
| top => exact (hV 1 one_ne_zero).trans .of_forall fun _ => by dsimp; grw [← le_top]
  | coe ε => exact hV ε (mod_cast hε)

/--
theorem `isLittleOTVS_congr` / 定理 `isLittleOTVS_congr`

English:
theorem isLittleOTVS_congr
  given: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  proof: by
  simp only [isLittleOTVS_iff_tendsto_div]
  peel with U hU V hV
  exact tendsto_congr' (hf.comp₂ (egauge _ _ · / egauge _ _ ·) hg)

中文:
定理 isLittleOTVS_congr
  条件: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  证明: by
  simp only [isLittleOTVS_iff_tendsto_div]
  peel with U hU V hV
  exact tendsto_congr' (hf.comp₂ (egauge _ _ · / egauge _ _ ·) hg)

Depends on / 依赖: egauge, hf.comp, isLittleOTVS_iff_tendsto_div, tendsto_congr
-/
theorem isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =o[𝕜; l] g₁ ↔ f₂ =o[𝕜; l] g₂ := by
  simp only [isLittleOTVS_iff_tendsto_div]
  peel with U hU V hV
  exact tendsto_congr' (hf.comp₂ (egauge _ _ · / egauge _ _ ·) hg)

/--
theorem `IsLittleOTVS.congr'` / 定理 `IsLittleOTVS.congr'`

English:
theorem IsLittleOTVS.congr'
  given: (h : f₁ =o[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  proof: (isLittleOTVS_congr hf hg).mp h

中文:
定理 是LittleOTVS.congr'
  条件: (h : f₁ =o[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  证明: (isLittleOTVS_congr hf hg).mp h

Depends on / 依赖: isLittleOTVS_congr
-/
theorem IsLittleOTVS.congr' (h : f₁ =o[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =o[𝕜; l] g₂ :=
  (isLittleOTVS_congr hf hg).mp h

/--
theorem `IsLittleOTVS.congr` / 定理 `IsLittleOTVS.congr`

English:
theorem IsLittleOTVS.congr
  given: (h : f₁ =o[𝕜; l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x)
  proof: h.congr' (univ_mem' hf) (univ_mem' hg)

中文:
定理 是LittleOTVS.congr
  条件: (h : f₁ =o[𝕜; l] g₁) (hf : 对任意 x, f₁ x = f₂ x) (hg : 对任意 x, g₁ x = g₂ x)
  证明: h.congr' (univ_mem' hf) (univ_mem' hg)

Depends on / 依赖: h.congr, univ_mem
-/
theorem IsLittleOTVS.congr (h : f₁ =o[𝕜; l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x) :
    f₂ =o[𝕜; l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

/--
theorem `IsLittleOTVS.congr_left` / 定理 `IsLittleOTVS.congr_left`

English:
theorem IsLittleOTVS.congr_left
  given: (h : f₁ =o[𝕜; l] g) (hf : forall x, f₁ x = f₂ x)
  statement: f₂ =o[𝕜; l] g
  proof: h.congr hf fun _ => rfl

中文:
定理 是LittleOTVS.congr_left
  条件: (h : f₁ =o[𝕜; l] g) (hf : 对任意 x, f₁ x = f₂ x)
  结论: f₂ =o[𝕜; l] g
  证明: h.congr hf fun _ => rfl

Depends on / 依赖: h.congr
-/
theorem IsLittleOTVS.congr_left (h : f₁ =o[𝕜; l] g) (hf : forall x, f₁ x = f₂ x) : f₂ =o[𝕜; l] g :=
  h.congr hf fun _ => rfl

/--
theorem `IsLittleOTVS.congr_right` / 定理 `IsLittleOTVS.congr_right`

English:
theorem IsLittleOTVS.congr_right
  given: (h : f =o[𝕜; l] g₁) (hg : forall x, g₁ x = g₂ x)
  statement: f =o[𝕜; l] g₂
  proof: h.congr (fun _ => rfl) hg

中文:
定理 是LittleOTVS.congr_right
  条件: (h : f =o[𝕜; l] g₁) (hg : 对任意 x, g₁ x = g₂ x)
  结论: f =o[𝕜; l] g₂
  证明: h.congr (fun _ => rfl) hg

Depends on / 依赖: h.congr
-/
theorem IsLittleOTVS.congr_right (h : f =o[𝕜; l] g₁) (hg : forall x, g₁ x = g₂ x) : f =o[𝕜; l] g₂ :=
  h.congr (fun _ => rfl) hg

/--
theorem `isBigOTVS_congr` / 定理 `isBigOTVS_congr`

English:
theorem isBigOTVS_congr
  given: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  proof: by
  simp only [isBigOTVS_iff]
  peel with U hU V hV
  exact eventuallyLE_congr (hf.fun_comp (egauge 𝕜 U)) (hg.fun_comp (egauge 𝕜 V))

中文:
定理 isBigOTVS_congr
  条件: (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  证明: by
  simp only [isBigOTVS_iff]
  peel with U hU V hV
  exact eventuallyLE_congr (hf.fun_comp (egauge 𝕜 U)) (hg.fun_comp (egauge 𝕜 V))

Depends on / 依赖: egauge, eventuallyLE_congr, fun_comp, hf.fun_comp, hg.fun_comp, isBigOTVS_iff
-/
theorem isBigOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =O[𝕜; l] g₁ ↔ f₂ =O[𝕜; l] g₂ := by
  simp only [isBigOTVS_iff]
  peel with U hU V hV
  exact eventuallyLE_congr (hf.fun_comp (egauge 𝕜 U)) (hg.fun_comp (egauge 𝕜 V))

/--
theorem `IsBigOTVS.congr'` / 定理 `IsBigOTVS.congr'`

English:
theorem IsBigOTVS.congr'
  given: (h : f₁ =O[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  proof: (isBigOTVS_congr hf hg).mp h

中文:
定理 是BigOTVS.congr'
  条件: (h : f₁ =O[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂)
  证明: (isBigOTVS_congr hf hg).mp h

Depends on / 依赖: isBigOTVS_congr
-/
theorem IsBigOTVS.congr' (h : f₁ =O[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =O[𝕜; l] g₂ :=
  (isBigOTVS_congr hf hg).mp h

/--
theorem `IsBigOTVS.congr` / 定理 `IsBigOTVS.congr`

English:
theorem IsBigOTVS.congr
  given: (h : f₁ =O[𝕜; l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x)
  proof: h.congr' (univ_mem' hf) (univ_mem' hg)

中文:
定理 是BigOTVS.congr
  条件: (h : f₁ =O[𝕜; l] g₁) (hf : 对任意 x, f₁ x = f₂ x) (hg : 对任意 x, g₁ x = g₂ x)
  证明: h.congr' (univ_mem' hf) (univ_mem' hg)

Depends on / 依赖: h.congr, univ_mem
-/
theorem IsBigOTVS.congr (h : f₁ =O[𝕜; l] g₁) (hf : forall x, f₁ x = f₂ x) (hg : forall x, g₁ x = g₂ x) :
    f₂ =O[𝕜; l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

/--
theorem `IsBigOTVS.congr_left` / 定理 `IsBigOTVS.congr_left`

English:
theorem IsBigOTVS.congr_left
  given: (h : f₁ =O[𝕜; l] g) (hf : forall x, f₁ x = f₂ x)
  statement: f₂ =O[𝕜; l] g
  proof: h.congr hf fun _ => rfl

中文:
定理 是BigOTVS.congr_left
  条件: (h : f₁ =O[𝕜; l] g) (hf : 对任意 x, f₁ x = f₂ x)
  结论: f₂ =O[𝕜; l] g
  证明: h.congr hf fun _ => rfl

Depends on / 依赖: h.congr
-/
theorem IsBigOTVS.congr_left (h : f₁ =O[𝕜; l] g) (hf : forall x, f₁ x = f₂ x) : f₂ =O[𝕜; l] g :=
  h.congr hf fun _ => rfl

/--
theorem `IsBigOTVS.congr_right` / 定理 `IsBigOTVS.congr_right`

English:
theorem IsBigOTVS.congr_right
  given: (h : f =O[𝕜; l] g₁) (hg : forall x, g₁ x = g₂ x)
  statement: f =O[𝕜; l] g₂
  proof: h.congr (fun _ => rfl) hg

中文:
定理 是BigOTVS.congr_right
  条件: (h : f =O[𝕜; l] g₁) (hg : 对任意 x, g₁ x = g₂ x)
  结论: f =O[𝕜; l] g₂
  证明: h.congr (fun _ => rfl) hg

Depends on / 依赖: h.congr
-/
theorem IsBigOTVS.congr_right (h : f =O[𝕜; l] g₁) (hg : forall x, g₁ x = g₂ x) : f =O[𝕜; l] g₂ :=
  h.congr (fun _ => rfl) hg

end congr

variable {l l₁ l₂ : Filter α} {f : α -> E} {g : α -> F}

/--
theorem `IsBigOTVS.refl` / 定理 `IsBigOTVS.refl`

English:
theorem IsBigOTVS.refl
  given: (f : α -> E) (l : Filter α)
  statement: f =O[𝕜; l] f
  proof: by
  rw [isBigOTVS_iff]
  exact fun U hU => ⟨U, hU, EventuallyLE.rfl⟩

中文:
定理 是BigOTVS.refl
  条件: (f : α -> E) (l : 滤子 α)
  结论: f =O[𝕜; l] f
  证明: by
  rw [isBigOTVS_iff]
  exact fun U hU => ⟨U, hU, EventuallyLE.rfl⟩
-/
protected theorem IsBigOTVS.refl (f : α -> E) (l : Filter α) : f =O[𝕜; l] f := by
  rw [isBigOTVS_iff]
  exact fun U hU => ⟨U, hU, EventuallyLE.rfl⟩

/--
theorem `IsBigOTVS.rfl` / 定理 `IsBigOTVS.rfl`

English:
theorem IsBigOTVS.rfl
  statement: f =O[𝕜; l] f
  proof: .refl f l

中文:
定理 是BigOTVS.rfl
  结论: f =O[𝕜; l] f
  证明: .refl f l
-/
protected theorem IsBigOTVS.rfl : f =O[𝕜; l] f := .refl f l

/--
theorem `IsThetaTVS.refl` / 定理 `IsThetaTVS.refl`

English:
theorem IsThetaTVS.refl
  given: (f : α -> E) (l : Filter α)
  statement: f =Θ[𝕜; l] f
  proof: ⟨.rfl, .rfl⟩

中文:
定理 IsThetaTVS.refl
  条件: (f : α -> E) (l : 滤子 α)
  结论: f =Θ[𝕜; l] f
  证明: ⟨.rfl, .rfl⟩
-/
protected theorem IsThetaTVS.refl (f : α -> E) (l : Filter α) : f =Θ[𝕜; l] f :=
  ⟨.rfl, .rfl⟩

/--
theorem `IsThetaTVS.rfl` / 定理 `IsThetaTVS.rfl`

English:
theorem IsThetaTVS.rfl
  statement: f =Θ[𝕜; l] f
  proof: .refl f l

中文:
定理 IsThetaTVS.rfl
  结论: f =Θ[𝕜; l] f
  证明: .refl f l
-/
protected theorem IsThetaTVS.rfl : f =Θ[𝕜; l] f := .refl f l

/--
theorem `IsLittleOTVS.isBigOTVS` / 定理 `IsLittleOTVS.isBigOTVS`

English:
theorem IsLittleOTVS.isBigOTVS
  given: (h : f =o[𝕜; l] g)
  statement: f =O[𝕜; l] g
  proof: by
  refine ⟨fun U hU => ?_⟩
  rcases h.1 U hU with ⟨V, hV₀, hV⟩
  use V, hV₀
  simpa using hV 1 one_ne_zero

中文:
定理 是LittleOTVS.isBigOTVS
  条件: (h : f =o[𝕜; l] g)
  结论: f =O[𝕜; l] g
  证明: by
  refine ⟨fun U hU => ?_⟩
  rcases h.1 U hU with ⟨V, hV₀, hV⟩
  use V, hV₀
  simpa using hV 1 one_ne_zero

Depends on / 依赖: one_ne_zero
-/
theorem IsLittleOTVS.isBigOTVS (h : f =o[𝕜; l] g) : f =O[𝕜; l] g := by
  refine ⟨fun U hU => ?_⟩
  rcases h.1 U hU with ⟨V, hV₀, hV⟩
  use V, hV₀
  simpa using hV 1 one_ne_zero

/--
theorem `IsThetaTVS.isBigOTVS` / 定理 `IsThetaTVS.isBigOTVS`

English:
theorem IsThetaTVS.isBigOTVS
  given: (h : f =Θ[𝕜; l] g)
  statement: f =O[𝕜; l] g
  proof: h.left

@[symm]

中文:
定理 IsThetaTVS.isBigOTVS
  条件: (h : f =Θ[𝕜; l] g)
  结论: f =O[𝕜; l] g
  证明: h.left

@[symm]

Depends on / 依赖: h.left
-/
theorem IsThetaTVS.isBigOTVS (h : f =Θ[𝕜; l] g) : f =O[𝕜; l] g := h.left

@[symm]
/--
theorem `IsThetaTVS.symm` / 定理 `IsThetaTVS.symm`

English:
theorem IsThetaTVS.symm
  given: (h : f =Θ[𝕜; l] g)
  statement: g =Θ[𝕜; l] f
  proof: And.symm h

中文:
定理 IsThetaTVS.symm
  条件: (h : f =Θ[𝕜; l] g)
  结论: g =Θ[𝕜; l] f
  证明: And.symm h

Depends on / 依赖: And.symm
-/
theorem IsThetaTVS.symm (h : f =Θ[𝕜; l] g) : g =Θ[𝕜; l] f := And.symm h

/--
theorem `isThetaTVS_comm` / 定理 `isThetaTVS_comm`

English:
theorem isThetaTVS_comm
  statement: f =Θ[𝕜; l] g ↔ g =Θ[𝕜; l] f
  proof: and_comm

中文:
定理 isThetaTVS_comm
  结论: f =Θ[𝕜; l] g ↔ g =Θ[𝕜; l] f
  证明: and_comm

Depends on / 依赖: and_comm
-/
theorem isThetaTVS_comm : f =Θ[𝕜; l] g ↔ g =Θ[𝕜; l] f := and_comm

/-!
### Transitivity lemmas
-/

section Trans

variable {k : α -> G}

@[trans]
/--
theorem `IsBigOTVS.trans` / 定理 `IsBigOTVS.trans`

English:
theorem IsBigOTVS.trans
  given: (hfg : f =O[𝕜; l] g) (hgk : g =O[𝕜; l] k)
  statement: f =O[𝕜; l] k
  proof: by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, ?_⟩
  filter_upwards [hV, hW] with x hx₁ hx₂ using hx₁.trans hx₂

中文:
定理 是BigOTVS.trans
  条件: (hfg : f =O[𝕜; l] g) (hgk : g =O[𝕜; l] k)
  结论: f =O[𝕜; l] k
  证明: by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, ?_⟩
  filter_upwards [hV, hW] with x hx₁ hx₂ using hx₁.trans hx₂

Depends on / 依赖: filter_upwards
-/
theorem IsBigOTVS.trans (hfg : f =O[𝕜; l] g) (hgk : g =O[𝕜; l] k) : f =O[𝕜; l] k := by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, ?_⟩
  filter_upwards [hV, hW] with x hx₁ hx₂ using hx₁.trans hx₂

/--
Instance `instTransIsBigOTVSIsBigOTVS` / 实例 `instTransIsBigOTVSIsBigOTVS`

English:
instance instTransIsBigOTVSIsBigOTVS
  signature: :
  body: IsBigOTVS.trans

中文:
实例 instTransIsBigOTVSIsBigOTVS
  签名: :
  定义体: IsBigOTVS.trans

Depends on / 依赖: IsBigOTVS, IsBigOTVS.trans
-/
instance instTransIsBigOTVSIsBigOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsBigOTVS.trans

/--
theorem `IsBigOTVS.trans_isThetaTVS` / 定理 `IsBigOTVS.trans_isThetaTVS`

English:
theorem IsBigOTVS.trans_isThetaTVS
  given: (hfg : f =O[𝕜; l] g) (hgk : g =Θ[𝕜; l] k)
  proof: hfg.trans hgk.isBigOTVS

中文:
定理 是BigOTVS.trans_isThetaTVS
  条件: (hfg : f =O[𝕜; l] g) (hgk : g =Θ[𝕜; l] k)
  证明: hfg.trans hgk.isBigOTVS

Depends on / 依赖: hfg.trans, hgk.isBigOTVS, isBigOTVS
-/
theorem IsBigOTVS.trans_isThetaTVS (hfg : f =O[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) :
    f =O[𝕜; l] k :=
  hfg.trans hgk.isBigOTVS

/--
Instance `instTransIsBigOTVSIsThetaTVS` / 实例 `instTransIsBigOTVSIsThetaTVS`

English:
instance instTransIsBigOTVSIsThetaTVS
  signature: :
  body: IsBigOTVS.trans_isThetaTVS

中文:
实例 instTransIsBigOTVSIsThetaTVS
  签名: :
  定义体: IsBigOTVS.trans_isThetaTVS

Depends on / 依赖: IsBigOTVS, IsBigOTVS.trans_isThetaTVS, trans_isThetaTVS
-/
instance instTransIsBigOTVSIsThetaTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsBigOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsBigOTVS.trans_isThetaTVS

/--
theorem `IsThetaTVS.trans_isBigOTVS` / 定理 `IsThetaTVS.trans_isBigOTVS`

English:
theorem IsThetaTVS.trans_isBigOTVS
  given: (hfg : f =Θ[𝕜; l] g) (hgk : g =O[𝕜; l] k)
  proof: hfg.isBigOTVS.trans hgk

中文:
定理 IsThetaTVS.trans_isBigOTVS
  条件: (hfg : f =Θ[𝕜; l] g) (hgk : g =O[𝕜; l] k)
  证明: hfg.isBigOTVS.trans hgk

Depends on / 依赖: hfg.isBigOTVS.trans, isBigOTVS
-/
theorem IsThetaTVS.trans_isBigOTVS (hfg : f =Θ[𝕜; l] g) (hgk : g =O[𝕜; l] k) :
    f =O[𝕜; l] k :=
  hfg.isBigOTVS.trans hgk

/--
Instance `instTransIsThetaOTVSIsBigOTVS` / 实例 `instTransIsThetaOTVSIsBigOTVS`

English:
instance instTransIsThetaOTVSIsBigOTVS
  signature: :
  body: IsThetaTVS.trans_isBigOTVS

@[trans]

中文:
实例 instTransIsThetaOTVSIsBigOTVS
  签名: :
  定义体: IsThetaTVS.trans_isBigOTVS

@[trans]

Depends on / 依赖: IsThetaTVS, IsThetaTVS.trans_isBigOTVS, trans_isBigOTVS
-/
instance instTransIsThetaOTVSIsBigOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsThetaTVS.trans_isBigOTVS

@[trans]
/--
theorem `IsThetaTVS.trans` / 定理 `IsThetaTVS.trans`

English:
theorem IsThetaTVS.trans
  given: (hfg : f =Θ[𝕜; l] g) (hgk : g =Θ[𝕜; l] k)
  statement: f =Θ[𝕜; l] k
  proof: ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩

中文:
定理 IsThetaTVS.trans
  条件: (hfg : f =Θ[𝕜; l] g) (hgk : g =Θ[𝕜; l] k)
  结论: f =Θ[𝕜; l] k
  证明: ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩
-/
theorem IsThetaTVS.trans (hfg : f =Θ[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) : f =Θ[𝕜; l] k :=
  ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩

/--
Instance `instTransIsThetaOTVS` / 实例 `instTransIsThetaOTVS`

English:
instance instTransIsThetaOTVS
  signature: :
  body: IsThetaTVS.trans

中文:
实例 instTransIsThetaOTVS
  签名: :
  定义体: IsThetaTVS.trans

Depends on / 依赖: IsThetaTVS, IsThetaTVS.trans
-/
instance instTransIsThetaOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) where
  trans := IsThetaTVS.trans

/--
theorem `IsLittleOTVS.trans_isBigOTVS` / 定理 `IsLittleOTVS.trans_isBigOTVS`

English:
theorem IsLittleOTVS.trans_isBigOTVS
  given: (hfg : f =o[𝕜; l] g) (hgk : g =O[𝕜; l] k)
  proof: by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε => ?_⟩
filter_upwards [hV ε hε, hW] with x hx₁ hx₂ using hx₁.trans by gcongr

中文:
定理 是LittleOTVS.trans_isBigOTVS
  条件: (hfg : f =o[𝕜; l] g) (hgk : g =O[𝕜; l] k)
  证明: by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε => ?_⟩
filter_upwards [hV ε hε, hW] with x hx₁ hx₂ using hx₁.trans by gcongr

Depends on / 依赖: filter_upwards
-/
theorem IsLittleOTVS.trans_isBigOTVS (hfg : f =o[𝕜; l] g) (hgk : g =O[𝕜; l] k) :
    f =o[𝕜; l] k := by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε => ?_⟩
filter_upwards [hV ε hε, hW] with x hx₁ hx₂ using hx₁.trans by gcongr

/--
Instance `instTransIsLittleOTVSIsBigOTVS` / 实例 `instTransIsLittleOTVSIsBigOTVS`

English:
instance instTransIsLittleOTVSIsBigOTVS
  signature: :
  body: IsLittleOTVS.trans_isBigOTVS

中文:
实例 instTransIsLittleOTVSIsBigOTVS
  签名: :
  定义体: IsLittleOTVS.trans_isBigOTVS

Depends on / 依赖: IsLittleOTVS, IsLittleOTVS.trans_isBigOTVS, trans_isBigOTVS
-/
instance instTransIsLittleOTVSIsBigOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsLittleOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans_isBigOTVS

/--
theorem `IsLittleOTVS.trans_isThetaTVS` / 定理 `IsLittleOTVS.trans_isThetaTVS`

English:
theorem IsLittleOTVS.trans_isThetaTVS
  given: (hfg : f =o[𝕜; l] g) (hgk : g =Θ[𝕜; l] k)
  proof: hfg.trans_isBigOTVS hgk.isBigOTVS

中文:
定理 是LittleOTVS.trans_isThetaTVS
  条件: (hfg : f =o[𝕜; l] g) (hgk : g =Θ[𝕜; l] k)
  证明: hfg.trans_isBigOTVS hgk.isBigOTVS

Depends on / 依赖: hfg.trans_isBigOTVS, hgk.isBigOTVS, isBigOTVS, trans_isBigOTVS
-/
theorem IsLittleOTVS.trans_isThetaTVS (hfg : f =o[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) :
    f =o[𝕜; l] k :=
  hfg.trans_isBigOTVS hgk.isBigOTVS

/--
Instance `instTransIsLittleOTVSIsThetaTVS` / 实例 `instTransIsLittleOTVSIsThetaTVS`

English:
instance instTransIsLittleOTVSIsThetaTVS
  signature: :
  body: IsLittleOTVS.trans_isThetaTVS

中文:
实例 instTransIsLittleOTVSIsThetaTVS
  签名: :
  定义体: IsLittleOTVS.trans_isThetaTVS

Depends on / 依赖: IsLittleOTVS, IsLittleOTVS.trans_isThetaTVS, trans_isThetaTVS
-/
instance instTransIsLittleOTVSIsThetaTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsLittleOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans_isThetaTVS

/--
theorem `IsBigOTVS.trans_isLittleOTVS` / 定理 `IsBigOTVS.trans_isLittleOTVS`

English:
theorem IsBigOTVS.trans_isLittleOTVS
  given: (hfg : f =O[𝕜; l] g) (hgk : g =o[𝕜; l] k)
  proof: by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε => ?_⟩
  filter_upwards [hV, hW ε hε] with x hx₁ hx₂ using hx₁.trans hx₂

中文:
定理 是BigOTVS.trans_isLittleOTVS
  条件: (hfg : f =O[𝕜; l] g) (hgk : g =o[𝕜; l] k)
  证明: by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε => ?_⟩
  filter_upwards [hV, hW ε hε] with x hx₁ hx₂ using hx₁.trans hx₂

Depends on / 依赖: filter_upwards
-/
theorem IsBigOTVS.trans_isLittleOTVS (hfg : f =O[𝕜; l] g) (hgk : g =o[𝕜; l] k) :
    f =o[𝕜; l] k := by
  refine ⟨fun U hU₀ => ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε => ?_⟩
  filter_upwards [hV, hW ε hε] with x hx₁ hx₂ using hx₁.trans hx₂

/--
Instance `instTransIsBigOTVSIsLittleOTVS` / 实例 `instTransIsBigOTVSIsLittleOTVS`

English:
instance instTransIsBigOTVSIsLittleOTVS
  signature: :
  body: IsBigOTVS.trans_isLittleOTVS

中文:
实例 instTransIsBigOTVSIsLittleOTVS
  签名: :
  定义体: IsBigOTVS.trans_isLittleOTVS

Depends on / 依赖: IsBigOTVS, IsBigOTVS.trans_isLittleOTVS, trans_isLittleOTVS
-/
instance instTransIsBigOTVSIsLittleOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsBigOTVS.trans_isLittleOTVS

/--
theorem `IsThetaTVS.trans_isLittleOTVS` / 定理 `IsThetaTVS.trans_isLittleOTVS`

English:
theorem IsThetaTVS.trans_isLittleOTVS
  given: (hfg : f =Θ[𝕜; l] g) (hgk : g =o[𝕜; l] k)
  proof: hfg.isBigOTVS.trans_isLittleOTVS hgk

中文:
定理 IsThetaTVS.trans_isLittleOTVS
  条件: (hfg : f =Θ[𝕜; l] g) (hgk : g =o[𝕜; l] k)
  证明: hfg.isBigOTVS.trans_isLittleOTVS hgk

Depends on / 依赖: hfg.isBigOTVS.trans_isLittleOTVS, isBigOTVS, trans_isLittleOTVS
-/
theorem IsThetaTVS.trans_isLittleOTVS (hfg : f =Θ[𝕜; l] g) (hgk : g =o[𝕜; l] k) :
    f =o[𝕜; l] k :=
  hfg.isBigOTVS.trans_isLittleOTVS hgk

/--
Instance `instTransIsThetaTVSIsLittleOTVS` / 实例 `instTransIsThetaTVSIsLittleOTVS`

English:
instance instTransIsThetaTVSIsLittleOTVS
  signature: :
  body: IsThetaTVS.trans_isLittleOTVS

@[trans]

中文:
实例 instTransIsThetaTVSIsLittleOTVS
  签名: :
  定义体: IsThetaTVS.trans_isLittleOTVS

@[trans]

Depends on / 依赖: IsThetaTVS, IsThetaTVS.trans_isLittleOTVS, trans_isLittleOTVS
-/
instance instTransIsThetaTVSIsLittleOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsThetaTVS.trans_isLittleOTVS

@[trans]
/--
theorem `IsLittleOTVS.trans` / 定理 `IsLittleOTVS.trans`

English:
theorem IsLittleOTVS.trans
  given: (hfg : f =o[𝕜; l] g) (hgk : g =o[𝕜; l] k)
  statement: f =o[𝕜; l] k
  proof: hfg.trans_isBigOTVS hgk.isBigOTVS

中文:
定理 是LittleOTVS.trans
  条件: (hfg : f =o[𝕜; l] g) (hgk : g =o[𝕜; l] k)
  结论: f =o[𝕜; l] k
  证明: hfg.trans_isBigOTVS hgk.isBigOTVS

Depends on / 依赖: hfg.trans_isBigOTVS, hgk.isBigOTVS, isBigOTVS, trans_isBigOTVS
-/
theorem IsLittleOTVS.trans (hfg : f =o[𝕜; l] g) (hgk : g =o[𝕜; l] k) : f =o[𝕜; l] k :=
  hfg.trans_isBigOTVS hgk.isBigOTVS

/--
Instance `instTransIsLittleOTVSIsLittleOTVS` / 实例 `instTransIsLittleOTVSIsLittleOTVS`

English:
instance instTransIsLittleOTVSIsLittleOTVS
  signature: :
  body: IsLittleOTVS.trans

中文:
实例 instTransIsLittleOTVSIsLittleOTVS
  签名: :
  定义体: IsLittleOTVS.trans

Depends on / 依赖: IsLittleOTVS, IsLittleOTVS.trans
-/
instance instTransIsLittleOTVSIsLittleOTVS :
    @Trans (α -> E) (α -> F) (α -> G) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans

end Trans

/--
theorem `_root_.Filter.HasBasis.isLittleOTVS_iff` / 定理 `_root_.Filter.HasBasis.isLittleOTVS_iff`

English:
theorem _root_.Filter.HasBasis.isLittleOTVS_iff
  proof: by
  rw [isLittleOTVS_iff]
refine (hE.forall_iff ?_).trans forall₂_congr fun _ _ => hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
exact ⟨V, hV₀, fun ε hε => (hV ε hε).mono fun x => le_trans egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε => (h ε hε).mono fun x hx => hx.trans ?_
    simp only
    gcongr

中文:
定理 _root_.滤子.有基.isLittleOTVS_iff
  证明: by
  rw [isLittleOTVS_iff]
refine (hE.forall_iff ?_).trans forall₂_congr fun _ _ => hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
exact ⟨V, hV₀, fun ε hε => (hV ε hε).mono fun x => le_trans egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε => (h ε hε).mono fun x hx => hx.trans ?_
    simp only
    gcongr
-/
protected theorem _root_.Filter.HasBasis.isLittleOTVS_iff
    {ιE ιF : Sort*} {pE : ιE -> Prop} {pF : ιF -> Prop}
    {sE : ιE -> Set E} {sF : ιF -> Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) :
    f =o[𝕜; l] g ↔ forall i, pE i -> exists j, pF j ∧ forall ε != (0 : Real>=0),
      forallᶠ x in l, egauge 𝕜 (sE i) (f x) <= ε * egauge 𝕜 (sF j) (g x) := by
  rw [isLittleOTVS_iff]
refine (hE.forall_iff ?_).trans forall₂_congr fun _ _ => hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
exact ⟨V, hV₀, fun ε hε => (hV ε hε).mono fun x => le_trans egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε => (h ε hε).mono fun x hx => hx.trans ?_
    simp only
    gcongr

/--
theorem `_root_.Filter.HasBasis.isBigOTVS_iff` / 定理 `_root_.Filter.HasBasis.isBigOTVS_iff`

English:
theorem _root_.Filter.HasBasis.isBigOTVS_iff
  proof: by
  rw [isBigOTVS_iff]
refine (hE.forall_iff ?_).trans forall₂_congr fun _ _ => hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
exact ⟨V, hV₀, hV.mono fun x => le_trans egauge_anti _ hsub _⟩
· exact fun s t hsub h => h.mono fun x hx => hx.trans egauge_anti 𝕜 hsub (g x)

中文:
定理 _root_.滤子.有基.isBigOTVS_iff
  证明: by
  rw [isBigOTVS_iff]
refine (hE.forall_iff ?_).trans forall₂_congr fun _ _ => hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
exact ⟨V, hV₀, hV.mono fun x => le_trans egauge_anti _ hsub _⟩
· exact fun s t hsub h => h.mono fun x hx => hx.trans egauge_anti 𝕜 hsub (g x)
-/
protected theorem _root_.Filter.HasBasis.isBigOTVS_iff
    {ιE ιF : Sort*} {pE : ιE -> Prop} {pF : ιF -> Prop}
    {sE : ιE -> Set E} {sF : ιF -> Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) :
    f =O[𝕜; l] g ↔ forall i, pE i -> exists j, pF j ∧
      forallᶠ x in l, egauge 𝕜 (sE i) (f x) <= egauge 𝕜 (sF j) (g x) := by
  rw [isBigOTVS_iff]
refine (hE.forall_iff ?_).trans forall₂_congr fun _ _ => hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
exact ⟨V, hV₀, hV.mono fun x => le_trans egauge_anti _ hsub _⟩
· exact fun s t hsub h => h.mono fun x hx => hx.trans egauge_anti 𝕜 hsub (g x)

/--
theorem `IsBigOTVS.of_egauge_le_mul` / 定理 `IsBigOTVS.of_egauge_le_mul`

English:
theorem IsBigOTVS.of_egauge_le_mul
  statement: [ContinuousConstSMul 𝕜 F] {ι} {p : ι -> Prop} {U : ι -> Set E}
  proof: by
  rw [hb.isBigOTVS_iff (basis_sets _)]
  intro i hi
  rcases h i hi with ⟨C, V, hV₀, hV⟩
  rcases NormedField.exists_lt_nnnorm 𝕜 C with ⟨c, hc⟩
  have hc₀ : c != 0 := by rintro rfl; simp at hc
  refine ⟨c⁻¹ • V, (set_smul_mem_nhds_zero_iff <| inv_ne_zero hc₀).mpr hV₀, ?_⟩
refine hV.trans .of_forall fun x => ?_
  simp only
  grw [hc]
  simp [egauge_smul_left, hc₀, enorm_eq_nnnorm, ENNReal.div_eq_inv_mul]

中文:
定理 是BigOTVS.of_egauge_le_mul
  结论: [连续常数标量乘法 𝕜 F] {ι} {p : ι -> 命题} {U : ι -> 集合 E}
  证明: by
  rw [hb.isBigOTVS_iff (basis_sets _)]
  intro i hi
  rcases h i hi with ⟨C, V, hV₀, hV⟩
  rcases NormedField.exists_lt_nnnorm 𝕜 C with ⟨c, hc⟩
  have hc₀ : c != 0 := by rintro rfl; simp at hc
  refine ⟨c⁻¹ • V, (set_smul_mem_nhds_zero_iff <| inv_ne_zero hc₀).mpr hV₀, ?_⟩
refine hV.trans .of_forall fun x => ?_
  simp only
  grw [hc]
  simp [egauge_smul_left, hc₀, enorm_eq_nnnorm, ENNReal.div_eq_inv_mul]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, NormedField, NormedField.exists_lt_nnnorm, basis_sets, div_eq_inv_mul, egauge_smul_left, enorm_eq_nnnorm, exists_lt_nnnorm, hV.trans, hb.isBigOTVS_iff, inv_ne_zero, isBigOTVS_iff, of_forall, set_smul_mem_nhds_zero_iff
-/
theorem IsBigOTVS.of_egauge_le_mul [ContinuousConstSMul 𝕜 F] {ι} {p : ι -> Prop} {U : ι -> Set E}
    (hb : (𝓝 0).HasBasis p U)
    (h : forall i, p i -> exists C : Real>=0, exists V in 𝓝 (0 : F),
      (egauge 𝕜 (U i) <| f ·) <=ᶠ[l] (fun x => C * egauge 𝕜 V (g x))) :
    f =O[𝕜; l] g := by
  rw [hb.isBigOTVS_iff (basis_sets _)]
  intro i hi
  rcases h i hi with ⟨C, V, hV₀, hV⟩
  rcases NormedField.exists_lt_nnnorm 𝕜 C with ⟨c, hc⟩
  have hc₀ : c != 0 := by rintro rfl; simp at hc
  refine ⟨c⁻¹ • V, (set_smul_mem_nhds_zero_iff <| inv_ne_zero hc₀).mpr hV₀, ?_⟩
refine hV.trans .of_forall fun x => ?_
  simp only
  grw [hc]
  simp [egauge_smul_left, hc₀, enorm_eq_nnnorm, ENNReal.div_eq_inv_mul]

/--
theorem `isLittleOTVS_iff_smallSets` / 定理 `isLittleOTVS_iff_smallSets`

English:
theorem isLittleOTVS_iff_smallSets
  proof: (isLittleOTVS_iff ..).trans forall₂_congr fun U hU => .symm
eventually_smallSets' fun V₁ V₂ hV hV₂ ε hε => (hV₂ ε hε).mono fun x hx => hx.trans by gcongr

alias ⟨IsLittleOTVS.eventually_smallSets, _⟩ := isLittleOTVS_iff_smallSets

中文:
定理 isLittleOTVS_iff_smallSets
  证明: (isLittleOTVS_iff ..).trans forall₂_congr fun U hU => .symm
eventually_smallSets' fun V₁ V₂ hV hV₂ ε hε => (hV₂ ε hε).mono fun x hx => hx.trans by gcongr

alias ⟨IsLittleOTVS.eventually_smallSets, _⟩ := isLittleOTVS_iff_smallSets

Depends on / 依赖: eventually_smallSets, hx.trans, isLittleOTVS_iff
-/
theorem isLittleOTVS_iff_smallSets :
    f =o[𝕜; l] g ↔ forall U in 𝓝 0, forallᶠ V in (𝓝 0).smallSets, forall ε != (0 : Real>=0),
      forallᶠ x in l, egauge 𝕜 U (f x) <= ε * egauge 𝕜 V (g x) :=
(isLittleOTVS_iff ..).trans forall₂_congr fun U hU => .symm
eventually_smallSets' fun V₁ V₂ hV hV₂ ε hε => (hV₂ ε hε).mono fun x hx => hx.trans by gcongr

alias ⟨IsLittleOTVS.eventually_smallSets, _⟩ := isLittleOTVS_iff_smallSets

/--
theorem `isBigOTVS_iff_smallSets` / 定理 `isBigOTVS_iff_smallSets`

English:
theorem isBigOTVS_iff_smallSets
  proof: (isBigOTVS_iff ..).trans forall₂_congr fun U hU => .symm
eventually_smallSets' fun V₁ V₂ hV hV₂ => hV₂.mono fun x hx => hx.trans by gcongr

alias ⟨IsBigOTVS.eventually_smallSets, _⟩ := isBigOTVS_iff_smallSets

@[simp]

中文:
定理 isBigOTVS_iff_smallSets
  证明: (isBigOTVS_iff ..).trans forall₂_congr fun U hU => .symm
eventually_smallSets' fun V₁ V₂ hV hV₂ => hV₂.mono fun x hx => hx.trans by gcongr

alias ⟨IsBigOTVS.eventually_smallSets, _⟩ := isBigOTVS_iff_smallSets

@[simp]

Depends on / 依赖: eventually_smallSets, hx.trans, isBigOTVS_iff
-/
theorem isBigOTVS_iff_smallSets :
    f =O[𝕜; l] g ↔ forall U in 𝓝 0, forallᶠ V in (𝓝 0).smallSets,
      forallᶠ x in l, egauge 𝕜 U (f x) <= egauge 𝕜 V (g x) :=
(isBigOTVS_iff ..).trans forall₂_congr fun U hU => .symm
eventually_smallSets' fun V₁ V₂ hV hV₂ => hV₂.mono fun x hx => hx.trans by gcongr

alias ⟨IsBigOTVS.eventually_smallSets, _⟩ := isBigOTVS_iff_smallSets

@[simp]
/--
theorem `isLittleOTVS_map` / 定理 `isLittleOTVS_map`

English:
theorem isLittleOTVS_map
  given: {k : β -> α} {l : Filter β}
  proof: by
  simp [isLittleOTVS_iff, EventuallyLE]

@[simp]

中文:
定理 isLittleOTVS_map
  条件: {k : β -> α} {l : 滤子 β}
  证明: by
  simp [isLittleOTVS_iff, EventuallyLE]

@[simp]

Depends on / 依赖: EventuallyLE, isLittleOTVS_iff
-/
theorem isLittleOTVS_map {k : β -> α} {l : Filter β} :
    f =o[𝕜; map k l] g ↔ (f ∘ k) =o[𝕜; l] (g ∘ k) := by
  simp [isLittleOTVS_iff, EventuallyLE]

@[simp]
/--
theorem `isBigOTVS_map` / 定理 `isBigOTVS_map`

English:
theorem isBigOTVS_map
  given: {k : β -> α} {l : Filter β}
  proof: by
  simp [isBigOTVS_iff, EventuallyLE]

中文:
定理 isBigOTVS_map
  条件: {k : β -> α} {l : 滤子 β}
  证明: by
  simp [isBigOTVS_iff, EventuallyLE]

Depends on / 依赖: EventuallyLE, isBigOTVS_iff
-/
theorem isBigOTVS_map {k : β -> α} {l : Filter β} :
    f =O[𝕜; map k l] g ↔ (f ∘ k) =O[𝕜; l] (g ∘ k) := by
  simp [isBigOTVS_iff, EventuallyLE]

/--
lemma `IsLittleOTVS.mono` / 引理 `IsLittleOTVS.mono`

English:
lemma IsLittleOTVS.mono
  given: (hf : f =o[𝕜; l₁] g) (h : l₂ <= l₁)
  statement: f =o[𝕜; l₂] g
  proof: ⟨fun U hU => let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, fun ε hε => (hV ε hε).filter_mono h⟩⟩

中文:
引理 是LittleOTVS.mono
  条件: (hf : f =o[𝕜; l₁] g) (h : l₂ <= l₁)
  结论: f =o[𝕜; l₂] g
  证明: ⟨fun U hU => let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, fun ε hε => (hV ε hε).filter_mono h⟩⟩

Depends on / 依赖: filter_mono
-/
lemma IsLittleOTVS.mono (hf : f =o[𝕜; l₁] g) (h : l₂ <= l₁) : f =o[𝕜; l₂] g :=
  ⟨fun U hU => let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, fun ε hε => (hV ε hε).filter_mono h⟩⟩

/--
lemma `IsBigOTVS.mono` / 引理 `IsBigOTVS.mono`

English:
lemma IsBigOTVS.mono
  given: (hf : f =O[𝕜; l₁] g) (h : l₂ <= l₁)
  statement: f =O[𝕜; l₂] g
  proof: ⟨fun U hU => let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, hV.filter_mono h⟩⟩

中文:
引理 是BigOTVS.mono
  条件: (hf : f =O[𝕜; l₁] g) (h : l₂ <= l₁)
  结论: f =O[𝕜; l₂] g
  证明: ⟨fun U hU => let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, hV.filter_mono h⟩⟩

Depends on / 依赖: filter_mono, hV.filter_mono
-/
lemma IsBigOTVS.mono (hf : f =O[𝕜; l₁] g) (h : l₂ <= l₁) : f =O[𝕜; l₂] g :=
  ⟨fun U hU => let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, hV.filter_mono h⟩⟩

/--
lemma `IsLittleOTVS.comp_tendsto` / 引理 `IsLittleOTVS.comp_tendsto`

English:
lemma IsLittleOTVS.comp_tendsto
  statement: {k : β -> α} {lb : Filter β} (h : f =o[𝕜; l] g)
  proof: isLittleOTVS_map.mp (h.mono hk)

中文:
引理 是LittleOTVS.comp_tendsto
  结论: {k : β -> α} {lb : 滤子 β} (h : f =o[𝕜; l] g)
  证明: isLittleOTVS_map.mp (h.mono hk)

Depends on / 依赖: h.mono, isLittleOTVS_map, isLittleOTVS_map.mp
-/
lemma IsLittleOTVS.comp_tendsto {k : β -> α} {lb : Filter β} (h : f =o[𝕜; l] g)
    (hk : Tendsto k lb l) : (f ∘ k) =o[𝕜; lb] (g ∘ k) :=
  isLittleOTVS_map.mp (h.mono hk)

/--
lemma `IsBigOTVS.comp_tendsto` / 引理 `IsBigOTVS.comp_tendsto`

English:
lemma IsBigOTVS.comp_tendsto
  statement: {k : β -> α} {lb : Filter β} (h : f =O[𝕜; l] g)
  proof: isBigOTVS_map.mp (h.mono hk)

中文:
引理 是BigOTVS.comp_tendsto
  结论: {k : β -> α} {lb : 滤子 β} (h : f =O[𝕜; l] g)
  证明: isBigOTVS_map.mp (h.mono hk)

Depends on / 依赖: h.mono, isBigOTVS_map, isBigOTVS_map.mp
-/
lemma IsBigOTVS.comp_tendsto {k : β -> α} {lb : Filter β} (h : f =O[𝕜; l] g)
    (hk : Tendsto k lb l) : (f ∘ k) =O[𝕜; lb] (g ∘ k) :=
  isBigOTVS_map.mp (h.mono hk)

/--
lemma `isLittleOTVS_sup` / 引理 `isLittleOTVS_sup`

English:
lemma isLittleOTVS_sup
  statement: f =o[𝕜; l₁ ⊔ l₂] g ↔ f =o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g
  proof: by
  simp only [isLittleOTVS_iff_smallSets, ← forall_and, ← eventually_and, eventually_sup]

中文:
引理 isLittleOTVS_sup
  结论: f =o[𝕜; l₁ ⊔ l₂] g ↔ f =o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g
  证明: by
  simp only [isLittleOTVS_iff_smallSets, ← forall_and, ← eventually_and, eventually_sup]

Depends on / 依赖: eventually_and, eventually_sup, forall_and, isLittleOTVS_iff_smallSets
-/
lemma isLittleOTVS_sup : f =o[𝕜; l₁ ⊔ l₂] g ↔ f =o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g := by
  simp only [isLittleOTVS_iff_smallSets, ← forall_and, ← eventually_and, eventually_sup]

/--
lemma `IsLittleOTVS.sup` / 引理 `IsLittleOTVS.sup`

English:
lemma IsLittleOTVS.sup
  given: (hf₁ : f =o[𝕜; l₁] g) (hf₂ : f =o[𝕜; l₂] g)
  statement: f =o[𝕜; l₁ ⊔ l₂] g
  proof: isLittleOTVS_sup.mpr ⟨hf₁, hf₂⟩

中文:
引理 是LittleOTVS.上确界
  条件: (hf₁ : f =o[𝕜; l₁] g) (hf₂ : f =o[𝕜; l₂] g)
  结论: f =o[𝕜; l₁ ⊔ l₂] g
  证明: isLittleOTVS_sup.mpr ⟨hf₁, hf₂⟩

Depends on / 依赖: isLittleOTVS_sup, isLittleOTVS_sup.mpr
-/
lemma IsLittleOTVS.sup (hf₁ : f =o[𝕜; l₁] g) (hf₂ : f =o[𝕜; l₂] g) : f =o[𝕜; l₁ ⊔ l₂] g :=
  isLittleOTVS_sup.mpr ⟨hf₁, hf₂⟩

/--
lemma `_root_.ContinuousLinearMap.isBigOTVS_id` / 引理 `_root_.ContinuousLinearMap.isBigOTVS_id`

English:
lemma _root_.ContinuousLinearMap.isBigOTVS_id
  given: {l : Filter E} (f : E ->L[𝕜] F)
  statement: f =O[𝕜; l] id
  proof: ⟨fun U hU => ⟨f ⁻¹' U, (map_continuous f).tendsto' 0 0 (map_zero f) hU, .of_forall
    (mapsTo_preimage f U).egauge_le 𝕜 f⟩⟩

中文:
引理 _root_.连续线性映射.isBigOTVS_id
  条件: {l : 滤子 E} (f : E ->L[𝕜] F)
  结论: f =O[𝕜; l] id
  证明: ⟨fun U hU => ⟨f ⁻¹' U, (map_continuous f).tendsto' 0 0 (map_zero f) hU, .of_forall
    (mapsTo_preimage f U).egauge_le 𝕜 f⟩⟩

Depends on / 依赖: egauge_le, map_continuous, map_zero, mapsTo_preimage, of_forall, tendsto
-/
lemma _root_.ContinuousLinearMap.isBigOTVS_id {l : Filter E} (f : E ->L[𝕜] F) : f =O[𝕜; l] id :=
⟨fun U hU => ⟨f ⁻¹' U, (map_continuous f).tendsto' 0 0 (map_zero f) hU, .of_forall
    (mapsTo_preimage f U).egauge_le 𝕜 f⟩⟩

/--
lemma `_root_.ContinuousLinearMap.isBigOTVS_comp` / 引理 `_root_.ContinuousLinearMap.isBigOTVS_comp`

English:
lemma _root_.ContinuousLinearMap.isBigOTVS_comp
  given: (g : E ->L[𝕜] F)
  statement: (g ∘ f) =O[𝕜; l] f
  proof: g.isBigOTVS_id.comp_tendsto tendsto_top

中文:
引理 _root_.连续线性映射.isBigOTVS_comp
  条件: (g : E ->L[𝕜] F)
  结论: (g ∘ f) =O[𝕜; l] f
  证明: g.isBigOTVS_id.comp_tendsto tendsto_top

Depends on / 依赖: comp_tendsto, g.isBigOTVS_id.comp_tendsto, isBigOTVS_id, tendsto_top
-/
lemma _root_.ContinuousLinearMap.isBigOTVS_comp (g : E ->L[𝕜] F) : (g ∘ f) =O[𝕜; l] f :=
  g.isBigOTVS_id.comp_tendsto tendsto_top

/--
lemma `_root_.ContinuousLinearMap.isBigOTVS_fun_comp` / 引理 `_root_.ContinuousLinearMap.isBigOTVS_fun_comp`

English:
lemma _root_.ContinuousLinearMap.isBigOTVS_fun_comp
  given: (g : E ->L[𝕜] F)
  statement: (g <| f ·) =O[𝕜; l] f
  proof: g.isBigOTVS_comp

中文:
引理 _root_.连续线性映射.isBigOTVS_fun_comp
  条件: (g : E ->L[𝕜] F)
  结论: (g <| f ·) =O[𝕜; l] f
  证明: g.isBigOTVS_comp

Depends on / 依赖: g.isBigOTVS_comp, isBigOTVS_comp
-/
lemma _root_.ContinuousLinearMap.isBigOTVS_fun_comp (g : E ->L[𝕜] F) : (g <| f ·) =O[𝕜; l] f :=
  g.isBigOTVS_comp

/--
lemma `_root_.LinearMap.isBigOTVS_rev_comp` / 引理 `_root_.LinearMap.isBigOTVS_rev_comp`

English:
lemma _root_.LinearMap.isBigOTVS_rev_comp
  given: (g : E ->ₗ[𝕜] F) (hg : comap g (𝓝 0) <= 𝓝 0)
  proof: by
  constructor
  intro U hU
  rcases mem_comap.1 (hg hU) with ⟨V, hV, hgV⟩
  use V, hV
  filter_upwards with a
  refine le_egauge_of_forall_ne_zero (mem_of_mem_nhds hV) fun c hc₀ hc => ?_
  apply egauge_le_of_mem_smul
  grw [← hgV, ← (IsUnit.mk0 _ hc₀).preimage_smul_set]
  exact hc

中文:
引理 _root_.线性映射.isBigOTVS_rev_comp
  条件: (g : E ->ₗ[𝕜] F) (hg : comap g (𝓝 0) <= 𝓝 0)
  证明: by
  constructor
  intro U hU
  rcases mem_comap.1 (hg hU) with ⟨V, hV, hgV⟩
  use V, hV
  filter_upwards with a
  refine le_egauge_of_forall_ne_zero (mem_of_mem_nhds hV) fun c hc₀ hc => ?_
  apply egauge_le_of_mem_smul
  grw [← hgV, ← (IsUnit.mk0 _ hc₀).preimage_smul_set]
  exact hc

Depends on / 依赖: IsUnit, IsUnit.mk0, egauge_le_of_mem_smul, filter_upwards, le_egauge_of_forall_ne_zero, mem_comap, mem_of_mem_nhds, preimage_smul_set
-/
lemma _root_.LinearMap.isBigOTVS_rev_comp (g : E ->ₗ[𝕜] F) (hg : comap g (𝓝 0) <= 𝓝 0) :
    f =O[𝕜; l] (g ∘ f) := by
  constructor
  intro U hU
  rcases mem_comap.1 (hg hU) with ⟨V, hV, hgV⟩
  use V, hV
  filter_upwards with a
  refine le_egauge_of_forall_ne_zero (mem_of_mem_nhds hV) fun c hc₀ hc => ?_
  apply egauge_le_of_mem_smul
  grw [← hgV, ← (IsUnit.mk0 _ hc₀).preimage_smul_set]
  exact hc

/--
lemma `_root_.ContinuousLinearMap.isThetaTVS_comp` / 引理 `_root_.ContinuousLinearMap.isThetaTVS_comp`

English:
lemma _root_.ContinuousLinearMap.isThetaTVS_comp
  given: (g : E ->L[𝕜] F) (hg : Topology.IsInducing g)
  proof: ⟨g.isBigOTVS_comp, g.isBigOTVS_rev_comp by simp [hg.nhds_eq_comap]⟩

@[simp]

中文:
引理 _root_.连续线性映射.isThetaTVS_comp
  条件: (g : E ->L[𝕜] F) (hg : 拓扑.是Inducing g)
  证明: ⟨g.isBigOTVS_comp, g.isBigOTVS_rev_comp by simp [hg.nhds_eq_comap]⟩

@[simp]

Depends on / 依赖: g.isBigOTVS_comp, g.isBigOTVS_rev_comp, hg.nhds_eq_comap, isBigOTVS_comp, isBigOTVS_rev_comp, nhds_eq_comap
-/
lemma _root_.ContinuousLinearMap.isThetaTVS_comp (g : E ->L[𝕜] F) (hg : Topology.IsInducing g) :
    (g ∘ f) =Θ[𝕜; l] f :=
⟨g.isBigOTVS_comp, g.isBigOTVS_rev_comp by simp [hg.nhds_eq_comap]⟩

@[simp]
/--
lemma `IsLittleOTVS.zero` / 引理 `IsLittleOTVS.zero`

English:
lemma IsLittleOTVS.zero
  given: (g : α -> F) (l : Filter α)
  statement: (0 : α -> E) =o[𝕜; l] g
  proof: by
  refine ⟨fun U hU => ?_⟩
  use univ
  simp [egauge_zero_right _ (Filter.nonempty_of_mem hU), EventuallyLE]

中文:
引理 是LittleOTVS.zero
  条件: (g : α -> F) (l : 滤子 α)
  结论: (0 : α -> E) =o[𝕜; l] g
  证明: by
  refine ⟨fun U hU => ?_⟩
  use univ
  simp [egauge_zero_right _ (Filter.nonempty_of_mem hU), EventuallyLE]

Depends on / 依赖: EventuallyLE, Filter, Filter.nonempty_of_mem, egauge_zero_right, nonempty_of_mem
-/
lemma IsLittleOTVS.zero (g : α -> F) (l : Filter α) : (0 : α -> E) =o[𝕜; l] g := by
  refine ⟨fun U hU => ?_⟩
  use univ
  simp [egauge_zero_right _ (Filter.nonempty_of_mem hU), EventuallyLE]

/--
lemma `isLittleOTVS_insert` / 引理 `isLittleOTVS_insert`

English:
lemma isLittleOTVS_insert
  given: [TopologicalSpace α] {x : α} {s : Set α} (h : f x = 0)
  proof: by
  rw [nhdsWithin_insert]; rw [isLittleOTVS_sup]; rw [and_iff_right]
  exact .congr' (.zero g _) h.symm .rfl

中文:
引理 isLittleOTVS_insert
  条件: [拓扑空间 α] {x : α} {s : 集合 α} (h : f x = 0)
  证明: by
  rw [nhdsWithin_insert]; rw [isLittleOTVS_sup]; rw [and_iff_right]
  exact .congr' (.zero g _) h.symm .rfl

Depends on / 依赖: and_iff_right, h.symm, isLittleOTVS_sup, nhdsWithin_insert
-/
lemma isLittleOTVS_insert [TopologicalSpace α] {x : α} {s : Set α} (h : f x = 0) :
    f =o[𝕜; 𝓝[insert x s] x] g ↔ f =o[𝕜; (𝓝[s] x)] g := by
  rw [nhdsWithin_insert]; rw [isLittleOTVS_sup]; rw [and_iff_right]
  exact .congr' (.zero g _) h.symm .rfl

/--
lemma `IsLittleOTVS.insert` / 引理 `IsLittleOTVS.insert`

English:
lemma IsLittleOTVS.insert
  statement: [TopologicalSpace α] {x : α} {s : Set α}
  proof: (isLittleOTVS_insert hf).2 h

@[simp]

中文:
引理 是LittleOTVS.insert
  结论: [拓扑空间 α] {x : α} {s : 集合 α}
  证明: (isLittleOTVS_insert hf).2 h

@[simp]

Depends on / 依赖: isLittleOTVS_insert
-/
lemma IsLittleOTVS.insert [TopologicalSpace α] {x : α} {s : Set α}
    (h : f =o[𝕜; 𝓝[s] x] g) (hf : f x = 0) :
    f =o[𝕜; 𝓝[insert x s] x] g :=
  (isLittleOTVS_insert hf).2 h

@[simp]
/--
lemma `IsLittleOTVS.bot` / 引理 `IsLittleOTVS.bot`

English:
lemma IsLittleOTVS.bot
  statement: f =o[𝕜; ⊥] g
  proof: ⟨fun u hU => ⟨univ, by simp [EventuallyLE]⟩⟩

中文:
引理 是LittleOTVS.bot
  结论: f =o[𝕜; ⊥] g
  证明: ⟨fun u hU => ⟨univ, by simp [EventuallyLE]⟩⟩

Depends on / 依赖: EventuallyLE
-/
lemma IsLittleOTVS.bot : f =o[𝕜; ⊥] g :=
  ⟨fun u hU => ⟨univ, by simp [EventuallyLE]⟩⟩

/--
theorem `IsLittleOTVS.prodMk` / 定理 `IsLittleOTVS.prodMk`

English:
theorem IsLittleOTVS.prodMk
  statement: [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G}
  proof: by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isLittleOTVS_iff
    (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, fun ε hε => ?_⟩
  filter_upwards [hWf ε hε, hWg ε hε] with x hfx hgx
  simp [egauge_prod_mk, *]

中文:
定理 是LittleOTVS.prodMk
  结论: [连续标量乘法 𝕜 E] [连续标量乘法 𝕜 F] {k : α -> G}
  证明: by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isLittleOTVS_iff
    (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, fun ε hε => ?_⟩
  filter_upwards [hWf ε hε, hWg ε hε] with x hfx hgx
  simp [egauge_prod_mk, *]

Depends on / 依赖: basis_sets, egauge_prod_mk, eventually_smallSets, exists_mem_of_smallSets, filter_upwards, hf.eventually_smallSets, hg.eventually_smallSets, isLittleOTVS_iff, nhds_basis_balanced, prod_nhds
-/
theorem IsLittleOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G}
    (hf : f =o[𝕜; l] k) (hg : g =o[𝕜; l] k) : (fun x => (f x, g x)) =o[𝕜; l] k := by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isLittleOTVS_iff
    (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, fun ε hε => ?_⟩
  filter_upwards [hWf ε hε, hWg ε hε] with x hfx hgx
  simp [egauge_prod_mk, *]

/--
theorem `IsLittleOTVS.fst` / 定理 `IsLittleOTVS.fst`

English:
theorem IsLittleOTVS.fst
  given: {f : α -> E × F} {g : α -> G} (h : f =o[𝕜; l] g)
  proof: .trans_isLittleOTVS h .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E F

中文:
定理 是LittleOTVS.fst
  条件: {f : α -> E × F} {g : α -> G} (h : f =o[𝕜; l] g)
  证明: .trans_isLittleOTVS h .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E F
-/
protected theorem IsLittleOTVS.fst {f : α -> E × F} {g : α -> G} (h : f =o[𝕜; l] g) :
    (f · |>.fst) =o[𝕜; l] g :=
.trans_isLittleOTVS h .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E F

/--
theorem `IsLittleOTVS.snd` / 定理 `IsLittleOTVS.snd`

English:
theorem IsLittleOTVS.snd
  given: {f : α -> E × F} {g : α -> G} (h : f =o[𝕜; l] g)
  proof: .trans_isLittleOTVS h .isBigOTVS_comp ContinuousLinearMap.snd 𝕜 E F

@[simp]

中文:
定理 是LittleOTVS.snd
  条件: {f : α -> E × F} {g : α -> G} (h : f =o[𝕜; l] g)
  证明: .trans_isLittleOTVS h .isBigOTVS_comp ContinuousLinearMap.snd 𝕜 E F

@[simp]
-/
protected theorem IsLittleOTVS.snd {f : α -> E × F} {g : α -> G} (h : f =o[𝕜; l] g) :
    (f · |>.snd) =o[𝕜; l] g :=
.trans_isLittleOTVS h .isBigOTVS_comp ContinuousLinearMap.snd 𝕜 E F

@[simp]
/--
theorem `isLittleOTVS_prodMk_left` / 定理 `isLittleOTVS_prodMk_left`

English:
theorem isLittleOTVS_prodMk_left
  given: [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G}
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.elim .prodMk⟩

中文:
定理 isLittleOTVS_prodMk_left
  条件: [连续标量乘法 𝕜 E] [连续标量乘法 𝕜 F] {k : α -> G}
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.elim .prodMk⟩

Depends on / 依赖: h.elim, h.fst, h.snd, prodMk
-/
theorem isLittleOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G} :
    (fun x => (f x, g x)) =o[𝕜; l] k ↔ f =o[𝕜; l] k ∧ g =o[𝕜; l] k :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.elim .prodMk⟩

/--
theorem `IsBigOTVS.prodMk` / 定理 `IsBigOTVS.prodMk`

English:
theorem IsBigOTVS.prodMk
  statement: [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G}
  proof: by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isBigOTVS_iff (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, ?_⟩
  filter_upwards [hWf, hWg] with x hfx hgx
  simp [egauge_prod_mk, *]

中文:
定理 是BigOTVS.prodMk
  结论: [连续标量乘法 𝕜 E] [连续标量乘法 𝕜 F] {k : α -> G}
  证明: by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isBigOTVS_iff (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, ?_⟩
  filter_upwards [hWf, hWg] with x hfx hgx
  simp [egauge_prod_mk, *]

Depends on / 依赖: basis_sets, egauge_prod_mk, eventually_smallSets, exists_mem_of_smallSets, filter_upwards, hf.eventually_smallSets, hg.eventually_smallSets, isBigOTVS_iff, nhds_basis_balanced, prod_nhds
-/
theorem IsBigOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G}
    (hf : f =O[𝕜; l] k) (hg : g =O[𝕜; l] k) : (fun x => (f x, g x)) =O[𝕜; l] k := by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isBigOTVS_iff (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, ?_⟩
  filter_upwards [hWf, hWg] with x hfx hgx
  simp [egauge_prod_mk, *]

/--
theorem `IsBigOTVS.fst` / 定理 `IsBigOTVS.fst`

English:
theorem IsBigOTVS.fst
  given: {f : α -> E × F} {g : α -> G} (h : f =O[𝕜; l] g)
  proof: .trans h .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E F

中文:
定理 是BigOTVS.fst
  条件: {f : α -> E × F} {g : α -> G} (h : f =O[𝕜; l] g)
  证明: .trans h .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E F
-/
protected theorem IsBigOTVS.fst {f : α -> E × F} {g : α -> G} (h : f =O[𝕜; l] g) :
    (f · |>.fst) =O[𝕜; l] g :=
.trans h .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E F

/--
theorem `IsBigOTVS.snd` / 定理 `IsBigOTVS.snd`

English:
theorem IsBigOTVS.snd
  given: {f : α -> E × F} {g : α -> G} (h : f =O[𝕜; l] g)
  proof: .trans h .isBigOTVS_comp ContinuousLinearMap.snd 𝕜 E F

@[simp]

中文:
定理 是BigOTVS.snd
  条件: {f : α -> E × F} {g : α -> G} (h : f =O[𝕜; l] g)
  证明: .trans h .isBigOTVS_comp ContinuousLinearMap.snd 𝕜 E F

@[simp]
-/
protected theorem IsBigOTVS.snd {f : α -> E × F} {g : α -> G} (h : f =O[𝕜; l] g) :
    (f · |>.snd) =O[𝕜; l] g :=
.trans h .isBigOTVS_comp ContinuousLinearMap.snd 𝕜 E F

@[simp]
/--
theorem `isBigOTVS_prodMk_left` / 定理 `isBigOTVS_prodMk_left`

English:
theorem isBigOTVS_prodMk_left
  given: [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G}
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.elim .prodMk⟩

@[to_fun]

中文:
定理 isBigOTVS_prodMk_left
  条件: [连续标量乘法 𝕜 E] [连续标量乘法 𝕜 F] {k : α -> G}
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.elim .prodMk⟩

@[to_fun]

Depends on / 依赖: h.elim, h.fst, h.snd, prodMk
-/
theorem isBigOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> G} :
    (fun x => (f x, g x)) =O[𝕜; l] k ↔ f =O[𝕜; l] k ∧ g =O[𝕜; l] k :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.elim .prodMk⟩

@[to_fun]
/--
theorem `IsLittleOTVS.add` / 定理 `IsLittleOTVS.add`

English:
theorem IsLittleOTVS.add
  statement: [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  proof: .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E
.trans_isLittleOTVS h₁.prodMk h₂

@[to_fun]

中文:
定理 是LittleOTVS.add
  结论: [连续加法 E] [连续标量乘法 𝕜 E]
  证明: .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E
.trans_isLittleOTVS h₁.prodMk h₂

@[to_fun]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, ContinuousLinearMap.snd, isBigOTVS_comp, prodMk, trans_isLittleOTVS
-/
theorem IsLittleOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α -> E} {g : α -> F} {l : Filter α}
    (h₁ : f₁ =o[𝕜; l] g) (h₂ : f₂ =o[𝕜; l] g) : (f₁ + f₂) =o[𝕜; l] g :=
.isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E
.trans_isLittleOTVS h₁.prodMk h₂

@[to_fun]
/--
theorem `IsBigOTVS.add` / 定理 `IsBigOTVS.add`

English:
theorem IsBigOTVS.add
  statement: [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  proof: .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E
.trans h₁.prodMk h₂

中文:
定理 是BigOTVS.add
  结论: [连续加法 E] [连续标量乘法 𝕜 E]
  证明: .isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E
.trans h₁.prodMk h₂

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, ContinuousLinearMap.snd, isBigOTVS_comp, prodMk
-/
theorem IsBigOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α -> E} {g : α -> F} {l : Filter α}
    (h₁ : f₁ =O[𝕜; l] g) (h₂ : f₂ =O[𝕜; l] g) : (f₁ + f₂) =O[𝕜; l] g :=
.isBigOTVS_comp ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E
.trans h₁.prodMk h₂

/--
theorem `IsLittleOTVS.triangle` / 定理 `IsLittleOTVS.triangle`

English:
theorem IsLittleOTVS.triangle
  statement: [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  proof: by
  simpa using h₁.add h₂

中文:
定理 是LittleOTVS.triangle
  结论: [连续加法 E] [连续标量乘法 𝕜 E]
  证明: by
  simpa using h₁.add h₂
-/
theorem IsLittleOTVS.triangle [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ f₃ : α -> E} {g : α -> F} {l : Filter α}
    (h₁ : (f₁ - f₂) =o[𝕜; l] g) (h₂ : (f₂ - f₃) =o[𝕜; l] g) : (f₁ - f₃) =o[𝕜; l] g := by
  simpa using h₁.add h₂

/--
theorem `IsBigOTVS.triangle` / 定理 `IsBigOTVS.triangle`

English:
theorem IsBigOTVS.triangle
  statement: [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  proof: by
  simpa using h₁.add h₂

中文:
定理 是BigOTVS.triangle
  结论: [连续加法 E] [连续标量乘法 𝕜 E]
  证明: by
  simpa using h₁.add h₂
-/
theorem IsBigOTVS.triangle [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ f₃ : α -> E} {g : α -> F} {l : Filter α}
    (h₁ : (f₁ - f₂) =O[𝕜; l] g) (h₂ : (f₂ - f₃) =O[𝕜; l] g) : (f₁ - f₃) =O[𝕜; l] g := by
  simpa using h₁.add h₂

section NegLeft

variable [ContinuousNeg E]

/--
theorem `IsBigOTVS.neg_left` / 定理 `IsBigOTVS.neg_left`

English:
theorem IsBigOTVS.neg_left
  given: (h : f =O[𝕜; l] g)
  statement: (-f) =O[𝕜; l] g
  proof: .trans ((ContinuousLinearMap.mk (-.id (R := 𝕜)) continuous_neg).isBigOTVS_comp) h

@[simp]

中文:
定理 是BigOTVS.neg_left
  条件: (h : f =O[𝕜; l] g)
  结论: (-f) =O[𝕜; l] g
  证明: .trans ((ContinuousLinearMap.mk (-.id (R := 𝕜)) continuous_neg).isBigOTVS_comp) h

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mk, continuous_neg, isBigOTVS_comp
-/
theorem IsBigOTVS.neg_left (h : f =O[𝕜; l] g) : (-f) =O[𝕜; l] g :=
  .trans ((ContinuousLinearMap.mk (-.id (R := 𝕜)) continuous_neg).isBigOTVS_comp) h

@[simp]
/--
theorem `isBigOTVS_neg_left` / 定理 `isBigOTVS_neg_left`

English:
theorem isBigOTVS_neg_left
  statement: (-f) =O[𝕜; l] g ↔ f =O[𝕜; l] g
  proof: ⟨fun h => by simpa using h.neg_left, .neg_left⟩

@[simp]

中文:
定理 isBigOTVS_neg_left
  结论: (-f) =O[𝕜; l] g ↔ f =O[𝕜; l] g
  证明: ⟨fun h => by simpa using h.neg_left, .neg_left⟩

@[simp]

Depends on / 依赖: h.neg_left, neg_left
-/
theorem isBigOTVS_neg_left : (-f) =O[𝕜; l] g ↔ f =O[𝕜; l] g :=
  ⟨fun h => by simpa using h.neg_left, .neg_left⟩

@[simp]
/--
theorem `isBigOTVS_fun_neg_left` / 定理 `isBigOTVS_fun_neg_left`

English:
theorem isBigOTVS_fun_neg_left
  statement: (-f ·) =O[𝕜; l] g ↔ f =O[𝕜; l] g
  proof: isBigOTVS_neg_left

中文:
定理 isBigOTVS_fun_neg_left
  结论: (-f ·) =O[𝕜; l] g ↔ f =O[𝕜; l] g
  证明: isBigOTVS_neg_left

Depends on / 依赖: isBigOTVS_neg_left
-/
theorem isBigOTVS_fun_neg_left : (-f ·) =O[𝕜; l] g ↔ f =O[𝕜; l] g :=
  isBigOTVS_neg_left

/--
theorem `IsLittleOTVS.neg_left` / 定理 `IsLittleOTVS.neg_left`

English:
theorem IsLittleOTVS.neg_left
  given: (h : f =o[𝕜; l] g)
  statement: (-f) =o[𝕜; l] g
  proof: IsBigOTVS.rfl.neg_left.trans_isLittleOTVS h

@[simp]

中文:
定理 是LittleOTVS.neg_left
  条件: (h : f =o[𝕜; l] g)
  结论: (-f) =o[𝕜; l] g
  证明: IsBigOTVS.rfl.neg_left.trans_isLittleOTVS h

@[simp]

Depends on / 依赖: IsBigOTVS, IsBigOTVS.rfl.neg_left.trans_isLittleOTVS, neg_left, trans_isLittleOTVS
-/
theorem IsLittleOTVS.neg_left (h : f =o[𝕜; l] g) : (-f) =o[𝕜; l] g :=
  IsBigOTVS.rfl.neg_left.trans_isLittleOTVS h

@[simp]
/--
theorem `isLittleOTVS_neg_left` / 定理 `isLittleOTVS_neg_left`

English:
theorem isLittleOTVS_neg_left
  statement: (-f) =o[𝕜; l] g ↔ f =o[𝕜; l] g
  proof: ⟨fun h => by simpa using h.neg_left, .neg_left⟩

@[simp]

中文:
定理 isLittleOTVS_neg_left
  结论: (-f) =o[𝕜; l] g ↔ f =o[𝕜; l] g
  证明: ⟨fun h => by simpa using h.neg_left, .neg_left⟩

@[simp]

Depends on / 依赖: h.neg_left, neg_left
-/
theorem isLittleOTVS_neg_left : (-f) =o[𝕜; l] g ↔ f =o[𝕜; l] g :=
  ⟨fun h => by simpa using h.neg_left, .neg_left⟩

@[simp]
/--
theorem `isLittleOTVS_fun_neg_left` / 定理 `isLittleOTVS_fun_neg_left`

English:
theorem isLittleOTVS_fun_neg_left
  statement: (-f ·) =o[𝕜; l] g ↔ f =o[𝕜; l] g
  proof: isLittleOTVS_neg_left

@[to_fun]

中文:
定理 isLittleOTVS_fun_neg_left
  结论: (-f ·) =o[𝕜; l] g ↔ f =o[𝕜; l] g
  证明: isLittleOTVS_neg_left

@[to_fun]

Depends on / 依赖: isLittleOTVS_neg_left
-/
theorem isLittleOTVS_fun_neg_left : (-f ·) =o[𝕜; l] g ↔ f =o[𝕜; l] g :=
  isLittleOTVS_neg_left

@[to_fun]
/--
theorem `IsLittleOTVS.symm` / 定理 `IsLittleOTVS.symm`

English:
theorem IsLittleOTVS.symm
  given: {f₁ f₂ : α -> E} (h : (f₁ - f₂) =o[𝕜; l] g)
  proof: by
  simpa using h.neg_left

中文:
定理 是LittleOTVS.symm
  条件: {f₁ f₂ : α -> E} (h : (f₁ - f₂) =o[𝕜; l] g)
  证明: by
  simpa using h.neg_left
-/
protected theorem IsLittleOTVS.symm {f₁ f₂ : α -> E} (h : (f₁ - f₂) =o[𝕜; l] g) :
    (f₂ - f₁) =o[𝕜; l] g := by
  simpa using h.neg_left

/--
theorem `isLittleOTVS_comm` / 定理 `isLittleOTVS_comm`

English:
theorem isLittleOTVS_comm
  given: {f₁ f₂ : α -> E}
  proof: ⟨.symm, .symm⟩

中文:
定理 isLittleOTVS_comm
  条件: {f₁ f₂ : α -> E}
  证明: ⟨.symm, .symm⟩
-/
theorem isLittleOTVS_comm {f₁ f₂ : α -> E} :
    (f₁ - f₂) =o[𝕜; l] g ↔ (f₂ - f₁) =o[𝕜; l] g :=
  ⟨.symm, .symm⟩

/--
theorem `isLittleOTVS_fun_comm` / 定理 `isLittleOTVS_fun_comm`

English:
theorem isLittleOTVS_fun_comm
  given: {f₁ f₂ : α -> E}
  proof: isLittleOTVS_comm

@[to_fun]

中文:
定理 isLittleOTVS_fun_comm
  条件: {f₁ f₂ : α -> E}
  证明: isLittleOTVS_comm

@[to_fun]

Depends on / 依赖: isLittleOTVS_comm
-/
theorem isLittleOTVS_fun_comm {f₁ f₂ : α -> E} :
    (fun a => f₁ a - f₂ a) =o[𝕜; l] g ↔ (fun a => f₂ a - f₁ a) =o[𝕜; l] g :=
  isLittleOTVS_comm

@[to_fun]
/--
theorem `IsBigOTVS.symm` / 定理 `IsBigOTVS.symm`

English:
theorem IsBigOTVS.symm
  given: {f₁ f₂ : α -> E} (h : (f₁ - f₂) =O[𝕜; l] g)
  proof: by
  simpa using h.neg_left

中文:
定理 是BigOTVS.symm
  条件: {f₁ f₂ : α -> E} (h : (f₁ - f₂) =O[𝕜; l] g)
  证明: by
  simpa using h.neg_left
-/
protected theorem IsBigOTVS.symm {f₁ f₂ : α -> E} (h : (f₁ - f₂) =O[𝕜; l] g) :
    (f₂ - f₁) =O[𝕜; l] g := by
  simpa using h.neg_left

/--
theorem `isBigOTVS_comm` / 定理 `isBigOTVS_comm`

English:
theorem isBigOTVS_comm
  given: {f₁ f₂ : α -> E}
  proof: ⟨.symm, .symm⟩

中文:
定理 isBigOTVS_comm
  条件: {f₁ f₂ : α -> E}
  证明: ⟨.symm, .symm⟩
-/
theorem isBigOTVS_comm {f₁ f₂ : α -> E} :
    (f₁ - f₂) =O[𝕜; l] g ↔ (f₂ - f₁) =O[𝕜; l] g :=
  ⟨.symm, .symm⟩

/--
theorem `isBigOTVS_fun_comm` / 定理 `isBigOTVS_fun_comm`

English:
theorem isBigOTVS_fun_comm
  given: {f₁ f₂ : α -> E}
  proof: isBigOTVS_comm

中文:
定理 isBigOTVS_fun_comm
  条件: {f₁ f₂ : α -> E}
  证明: isBigOTVS_comm

Depends on / 依赖: isBigOTVS_comm
-/
theorem isBigOTVS_fun_comm {f₁ f₂ : α -> E} :
    (fun a => f₁ a - f₂ a) =O[𝕜; l] g ↔ (fun a => f₂ a - f₁ a) =O[𝕜; l] g :=
  isBigOTVS_comm

end NegLeft

section NegRight

variable [ContinuousNeg F]

/--
theorem `IsBigOTVS.neg_right` / 定理 `IsBigOTVS.neg_right`

English:
theorem IsBigOTVS.neg_right
  given: (h : f =O[𝕜; l] g)
  statement: f =O[𝕜; l] (-g)
  proof: h.trans by simpa using (IsBigOTVS.refl (-g) l).neg_left

@[simp]

中文:
定理 是BigOTVS.neg_right
  条件: (h : f =O[𝕜; l] g)
  结论: f =O[𝕜; l] (-g)
  证明: h.trans by simpa using (IsBigOTVS.refl (-g) l).neg_left

@[simp]

Depends on / 依赖: IsBigOTVS, IsBigOTVS.refl, h.trans, neg_left
-/
theorem IsBigOTVS.neg_right (h : f =O[𝕜; l] g) : f =O[𝕜; l] (-g) :=
h.trans by simpa using (IsBigOTVS.refl (-g) l).neg_left

@[simp]
/--
theorem `isBigOTVS_neg_right` / 定理 `isBigOTVS_neg_right`

English:
theorem isBigOTVS_neg_right
  statement: f =O[𝕜; l] (-g) ↔ f =O[𝕜; l] g
  proof: ⟨fun h => by simpa using h.neg_right, .neg_right⟩

@[simp]

中文:
定理 isBigOTVS_neg_right
  结论: f =O[𝕜; l] (-g) ↔ f =O[𝕜; l] g
  证明: ⟨fun h => by simpa using h.neg_right, .neg_right⟩

@[simp]

Depends on / 依赖: h.neg_right, neg_right
-/
theorem isBigOTVS_neg_right : f =O[𝕜; l] (-g) ↔ f =O[𝕜; l] g :=
  ⟨fun h => by simpa using h.neg_right, .neg_right⟩

@[simp]
/--
theorem `isBigOTVS_fun_neg_right` / 定理 `isBigOTVS_fun_neg_right`

English:
theorem isBigOTVS_fun_neg_right
  statement: f =O[𝕜; l] (-g ·) ↔ f =O[𝕜; l] g
  proof: isBigOTVS_neg_right

中文:
定理 isBigOTVS_fun_neg_right
  结论: f =O[𝕜; l] (-g ·) ↔ f =O[𝕜; l] g
  证明: isBigOTVS_neg_right

Depends on / 依赖: isBigOTVS_neg_right
-/
theorem isBigOTVS_fun_neg_right : f =O[𝕜; l] (-g ·) ↔ f =O[𝕜; l] g :=
  isBigOTVS_neg_right

/--
theorem `IsLittleOTVS.neg_right` / 定理 `IsLittleOTVS.neg_right`

English:
theorem IsLittleOTVS.neg_right
  given: (h : f =o[𝕜; l] g)
  statement: f =o[𝕜; l] (-g)
  proof: h.trans_isBigOTVS (.neg_right .rfl)

@[simp]

中文:
定理 是LittleOTVS.neg_right
  条件: (h : f =o[𝕜; l] g)
  结论: f =o[𝕜; l] (-g)
  证明: h.trans_isBigOTVS (.neg_right .rfl)

@[simp]

Depends on / 依赖: h.trans_isBigOTVS, neg_right, trans_isBigOTVS
-/
theorem IsLittleOTVS.neg_right (h : f =o[𝕜; l] g) : f =o[𝕜; l] (-g) :=
  h.trans_isBigOTVS (.neg_right .rfl)

@[simp]
/--
theorem `isLittleOTVS_neg_right` / 定理 `isLittleOTVS_neg_right`

English:
theorem isLittleOTVS_neg_right
  statement: f =o[𝕜; l] (-g) ↔ f =o[𝕜; l] g
  proof: ⟨fun h => by simpa using h.neg_right, .neg_right⟩

@[simp]

中文:
定理 isLittleOTVS_neg_right
  结论: f =o[𝕜; l] (-g) ↔ f =o[𝕜; l] g
  证明: ⟨fun h => by simpa using h.neg_right, .neg_right⟩

@[simp]

Depends on / 依赖: h.neg_right, neg_right
-/
theorem isLittleOTVS_neg_right : f =o[𝕜; l] (-g) ↔ f =o[𝕜; l] g :=
  ⟨fun h => by simpa using h.neg_right, .neg_right⟩

@[simp]
/--
theorem `isLittleOTVS_fun_neg_right` / 定理 `isLittleOTVS_fun_neg_right`

English:
theorem isLittleOTVS_fun_neg_right
  statement: f =o[𝕜; l] (-g ·) ↔ f =o[𝕜; l] g
  proof: isLittleOTVS_neg_right

中文:
定理 isLittleOTVS_fun_neg_right
  结论: f =o[𝕜; l] (-g ·) ↔ f =o[𝕜; l] g
  证明: isLittleOTVS_neg_right

Depends on / 依赖: isLittleOTVS_neg_right
-/
theorem isLittleOTVS_fun_neg_right : f =o[𝕜; l] (-g ·) ↔ f =o[𝕜; l] g :=
  isLittleOTVS_neg_right

end NegRight

/--
theorem `IsLittleOTVS.pi` / 定理 `IsLittleOTVS.pi`

English:
theorem IsLittleOTVS.pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
  proof: by
  have := hasBasis_pi fun i => nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi]; rw [← Pi.zero_def] at this
  simp only [this.isLittleOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi => (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε => ?_⟩
  refine (hIf.eventually_all.mpr (hV · · ε hε)).mono fun x hx => ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]

中文:
定理 是LittleOTVS.pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换群 (E i)]
  证明: by
  have := hasBasis_pi fun i => nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi]; rw [← Pi.zero_def] at this
  simp only [this.isLittleOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi => (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε => ?_⟩
  refine (hIf.eventually_all.mpr (hV · · ε hε)).mono fun x hx => ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]
-/
protected theorem IsLittleOTVS.pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
    [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] [forall i, ContinuousSMul 𝕜 (E i)]
    {f : forall i, α -> E i} (h : forall i, f i =o[𝕜; l] g) : (fun x i => f i x) =o[𝕜; l] g := by
  have := hasBasis_pi fun i => nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi]; rw [← Pi.zero_def] at this
  simp only [this.isLittleOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi => (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε => ?_⟩
  refine (hIf.eventually_all.mpr (hV · · ε hε)).mono fun x hx => ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]

/--
theorem `IsLittleOTVS.proj` / 定理 `IsLittleOTVS.proj`

English:
theorem IsLittleOTVS.proj
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
  proof: .trans_isLittleOTVS h .isBigOTVS_fun_comp ContinuousLinearMap.proj i

中文:
定理 是LittleOTVS.proj
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换群 (E i)]
  证明: .trans_isLittleOTVS h .isBigOTVS_fun_comp ContinuousLinearMap.proj i

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.proj, isBigOTVS_fun_comp, trans_isLittleOTVS
-/
theorem IsLittleOTVS.proj {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
    [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] {f : α -> forall i, E i}
    (h : f =o[𝕜; l] g) (i : ι) : (f · i) =o[𝕜; l] g :=
.trans_isLittleOTVS h .isBigOTVS_fun_comp ContinuousLinearMap.proj i

/--
theorem `isLittleOTVS_pi` / 定理 `isLittleOTVS_pi`

English:
theorem isLittleOTVS_pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
  proof: ⟨.proj, .pi⟩

中文:
定理 isLittleOTVS_pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换群 (E i)]
  证明: ⟨.proj, .pi⟩
-/
theorem isLittleOTVS_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
    [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] [forall i, ContinuousSMul 𝕜 (E i)]
    {f : α -> forall i, E i} : f =o[𝕜; l] g ↔ forall i, (f · i) =o[𝕜; l] g :=
  ⟨.proj, .pi⟩

/--
theorem `IsBigOTVS.pi` / 定理 `IsBigOTVS.pi`

English:
theorem IsBigOTVS.pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
  proof: by
  have := hasBasis_pi fun i => nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi]; rw [← Pi.zero_def] at this
  simp only [this.isBigOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi => (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  use V, hV₀
  refine (hIf.eventually_all.mpr hV).mono fun x hx => ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]

中文:
定理 是BigOTVS.pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换群 (E i)]
  证明: by
  have := hasBasis_pi fun i => nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi]; rw [← Pi.zero_def] at this
  simp only [this.isBigOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi => (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  use V, hV₀
  refine (hIf.eventually_all.mpr hV).mono fun x hx => ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]
-/
protected theorem IsBigOTVS.pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
    [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] [forall i, ContinuousSMul 𝕜 (E i)]
    {f : forall i, α -> E i} (h : forall i, f i =O[𝕜; l] g) : (fun x i => f i x) =O[𝕜; l] g := by
  have := hasBasis_pi fun i => nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi]; rw [← Pi.zero_def] at this
  simp only [this.isBigOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi => (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  use V, hV₀
  refine (hIf.eventually_all.mpr hV).mono fun x hx => ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]

/--
theorem `IsBigOTVS.proj` / 定理 `IsBigOTVS.proj`

English:
theorem IsBigOTVS.proj
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
  proof: .trans h .isBigOTVS_fun_comp ContinuousLinearMap.proj i

中文:
定理 是BigOTVS.proj
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换群 (E i)]
  证明: .trans h .isBigOTVS_fun_comp ContinuousLinearMap.proj i

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.proj, isBigOTVS_fun_comp
-/
theorem IsBigOTVS.proj {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
    [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] {f : α -> forall i, E i}
    (h : f =O[𝕜; l] g) (i : ι) : (f · i) =O[𝕜; l] g :=
.trans h .isBigOTVS_fun_comp ContinuousLinearMap.proj i

/--
theorem `isBigOTVS_pi` / 定理 `isBigOTVS_pi`

English:
theorem isBigOTVS_pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
  proof: ⟨.proj, .pi⟩

中文:
定理 isBigOTVS_pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换群 (E i)]
  证明: ⟨.proj, .pi⟩
-/
theorem isBigOTVS_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)]
    [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] [forall i, ContinuousSMul 𝕜 (E i)]
    {f : α -> forall i, E i} : f =O[𝕜; l] g ↔ forall i, (f · i) =O[𝕜; l] g :=
  ⟨.proj, .pi⟩

/--
lemma `IsLittleOTVS.smul_left` / 引理 `IsLittleOTVS.smul_left`

English:
lemma IsLittleOTVS.smul_left
  given: (h : f =o[𝕜; l] g) (c : α -> 𝕜)
  proof: by
  simp only [isLittleOTVS_iff] at *
  peel h with U hU V hV ε hε x hx
  simp only at *
  rw [egauge_smul_right]; rw [egauge_smul_right]; rw [mul_left_comm]
  · gcongr
  all_goals exact fun _ => Filter.nonempty_of_mem ‹_›

中文:
引理 是LittleOTVS.smul_left
  条件: (h : f =o[𝕜; l] g) (c : α -> 𝕜)
  证明: by
  simp only [isLittleOTVS_iff] at *
  peel h with U hU V hV ε hε x hx
  simp only at *
  rw [egauge_smul_right]; rw [egauge_smul_right]; rw [mul_left_comm]
  · gcongr
  all_goals exact fun _ => Filter.nonempty_of_mem ‹_›
-/
protected lemma IsLittleOTVS.smul_left (h : f =o[𝕜; l] g) (c : α -> 𝕜) :
    (fun x => c x • f x) =o[𝕜; l] (fun x => c x • g x) := by
  simp only [isLittleOTVS_iff] at *
  peel h with U hU V hV ε hε x hx
  simp only at *
  rw [egauge_smul_right]; rw [egauge_smul_right]; rw [mul_left_comm]
  · gcongr
  all_goals exact fun _ => Filter.nonempty_of_mem ‹_›

/--
lemma `isLittleOTVS_one` / 引理 `isLittleOTVS_one`

English:
lemma isLittleOTVS_one
  given: [ContinuousSMul 𝕜 E]
  statement: f =o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto f l (𝓝 0)
  proof: by
  constructor
  · intro hf
    rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at hf
    rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
    rintro U ⟨hU, hUb⟩
    rcases hf U hU with ⟨r, hr₀, hr⟩
    lift r to Real>=0 using hr₀.le
    norm_cast at hr₀
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    obtain ⟨ε, hε₀, hε⟩ : exists ε : Real>=0, 0 < ε ∧ (ε * ‖c‖₊ / r : Real>=0∞) < 1 := by
      apply Eventually.exists_gt
.eventually_lt_const zero_lt_one refine Continuous.tendsto' ?_ _ _ (by simp)
      fun_prop (disch := intros; first | apply ENNReal.coe_ne_top | positivity)
    filter_upwards [hr ε hε₀.ne'] with x hx
    refine mem_of_egauge_lt_one hUb (hx.trans_lt ?_)
    calc
      (ε : Real>=0∞) * egauge 𝕜 (ball (0 : 𝕜) r) 1 <= (ε * ‖c‖₊ / r : Real>=0∞) := by
        rw [mul_div_assoc]
        gcongr
        simpa using! egauge_ball_le_of_one_lt_norm (r := r) (x := (1 : 𝕜)) hc (by simp)
      _ < 1 := ‹_›
  · simp only [isLittleOTVS_iff]
    intro hf U hU
    refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε => ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε⟩
    replace hc₀ : c != 0 := by simpa using! hc₀
    filter_upwards [hf ((set_smul_mem_nhds_zero_iff hc₀).2 hU)] with a ha
    calc
      egauge 𝕜 U (f a) <= ‖c‖₊ := egauge_le_of_mem_smul ha
      _ <= ε := mod_cast hcε.le
      _ <= ε * egauge 𝕜 (ball (0 : 𝕜) 1) 1 := by
        apply le_mul_of_one_le_right'
        simpa using! le_egauge_ball_one 𝕜 (1 : 𝕜)

中文:
引理 isLittleOTVS_one
  条件: [连续标量乘法 𝕜 E]
  结论: f =o[𝕜; l] (1 : α -> 𝕜) ↔ 收敛 f l (𝓝 0)
  证明: by
  constructor
  · intro hf
    rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at hf
    rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
    rintro U ⟨hU, hUb⟩
    rcases hf U hU with ⟨r, hr₀, hr⟩
    lift r to Real>=0 using hr₀.le
    norm_cast at hr₀
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    obtain ⟨ε, hε₀, hε⟩ : exists ε : Real>=0, 0 < ε ∧ (ε * ‖c‖₊ / r : Real>=0∞) < 1 := by
      apply Eventually.exists_gt
.eventually_lt_const zero_lt_one refine Continuous.tendsto' ?_ _ _ (by simp)
      fun_prop (disch := intros; first | apply ENNReal.coe_ne_top | positivity)
    filter_upwards [hr ε hε₀.ne'] with x hx
    refine mem_of_egauge_lt_one hUb (hx.trans_lt ?_)
    calc
      (ε : Real>=0∞) * egauge 𝕜 (ball (0 : 𝕜) r) 1 <= (ε * ‖c‖₊ / r : Real>=0∞) := by
        rw [mul_div_assoc]
        gcongr
        simpa using! egauge_ball_le_of_one_lt_norm (r := r) (x := (1 : 𝕜)) hc (by simp)
      _ < 1 := ‹_›
  · simp only [isLittleOTVS_iff]
    intro hf U hU
    refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε => ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε⟩
    replace hc₀ : c != 0 := by simpa using! hc₀
    filter_upwards [hf ((set_smul_mem_nhds_zero_iff hc₀).2 hU)] with a ha
    calc
      egauge 𝕜 U (f a) <= ‖c‖₊ := egauge_le_of_mem_smul ha
      _ <= ε := mod_cast hcε.le
      _ <= ε * egauge 𝕜 (ball (0 : 𝕜) 1) 1 := by
        apply le_mul_of_one_le_right'
        simpa using! le_egauge_ball_one 𝕜 (1 : 𝕜)

Depends on / 依赖: Continuous, Continuous.tendsto, Eventually, Eventually.exists_gt, NormedField, NormedField.exists_one_lt_norm, basis_sets, eventually_lt_const, exists_gt, exists_one_lt_norm, fun_prop, isLittleOTVS_iff, nhds_basis_balanced, nhds_basis_ball, tendsto, tendsto_right_iff, zero_lt_one
-/
lemma isLittleOTVS_one [ContinuousSMul 𝕜 E] : f =o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro hf
    rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at hf
    rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
    rintro U ⟨hU, hUb⟩
    rcases hf U hU with ⟨r, hr₀, hr⟩
    lift r to Real>=0 using hr₀.le
    norm_cast at hr₀
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    obtain ⟨ε, hε₀, hε⟩ : exists ε : Real>=0, 0 < ε ∧ (ε * ‖c‖₊ / r : Real>=0∞) < 1 := by
      apply Eventually.exists_gt
.eventually_lt_const zero_lt_one refine Continuous.tendsto' ?_ _ _ (by simp)
      fun_prop (disch := intros; first | apply ENNReal.coe_ne_top | positivity)
    filter_upwards [hr ε hε₀.ne'] with x hx
    refine mem_of_egauge_lt_one hUb (hx.trans_lt ?_)
    calc
      (ε : Real>=0∞) * egauge 𝕜 (ball (0 : 𝕜) r) 1 <= (ε * ‖c‖₊ / r : Real>=0∞) := by
        rw [mul_div_assoc]
        gcongr
        simpa using! egauge_ball_le_of_one_lt_norm (r := r) (x := (1 : 𝕜)) hc (by simp)
      _ < 1 := ‹_›
  · simp only [isLittleOTVS_iff]
    intro hf U hU
    refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε => ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε⟩
    replace hc₀ : c != 0 := by simpa using! hc₀
    filter_upwards [hf ((set_smul_mem_nhds_zero_iff hc₀).2 hU)] with a ha
    calc
      egauge 𝕜 U (f a) <= ‖c‖₊ := egauge_le_of_mem_smul ha
      _ <= ε := mod_cast hcε.le
      _ <= ε * egauge 𝕜 (ball (0 : 𝕜) 1) 1 := by
        apply le_mul_of_one_le_right'
        simpa using! le_egauge_ball_one 𝕜 (1 : 𝕜)

/--
lemma `IsLittleOTVS.tendsto_inv_smul` / 引理 `IsLittleOTVS.tendsto_inv_smul`

English:
lemma IsLittleOTVS.tendsto_inv_smul
  statement: [ContinuousSMul 𝕜 E] {f : α -> 𝕜} {g : α -> E}
  proof: by
  rw [← isLittleOTVS_one (𝕜 := 𝕜)]; rw [isLittleOTVS_iff]
  intro U hU
  rcases (h.smul_left f⁻¹).1 U hU with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε => (hV ε hε).mono fun x hx => hx.trans ?_⟩
  by_cases hx₀ : f x = 0 <;> simp [hx₀, egauge_zero_right _ (Filter.nonempty_of_mem hV₀)]

中文:
引理 是LittleOTVS.tendsto_inv_smul
  结论: [连续标量乘法 𝕜 E] {f : α -> 𝕜} {g : α -> E}
  证明: by
  rw [← isLittleOTVS_one (𝕜 := 𝕜)]; rw [isLittleOTVS_iff]
  intro U hU
  rcases (h.smul_left f⁻¹).1 U hU with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε => (hV ε hε).mono fun x hx => hx.trans ?_⟩
  by_cases hx₀ : f x = 0 <;> simp [hx₀, egauge_zero_right _ (Filter.nonempty_of_mem hV₀)]

Depends on / 依赖: Filter, Filter.nonempty_of_mem, egauge_zero_right, h.smul_left, hx.trans, isLittleOTVS_iff, isLittleOTVS_one, nonempty_of_mem, smul_left
-/
lemma IsLittleOTVS.tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α -> 𝕜} {g : α -> E}
    (h : g =o[𝕜; l] f) : Tendsto (fun x => (f x)⁻¹ • g x) l (𝓝 0) := by
  rw [← isLittleOTVS_one (𝕜 := 𝕜)]; rw [isLittleOTVS_iff]
  intro U hU
  rcases (h.smul_left f⁻¹).1 U hU with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε => (hV ε hε).mono fun x hx => hx.trans ?_⟩
  by_cases hx₀ : f x = 0 <;> simp [hx₀, egauge_zero_right _ (Filter.nonempty_of_mem hV₀)]

/--
lemma `isLittleOTVS_iff_tendsto_inv_smul` / 引理 `isLittleOTVS_iff_tendsto_inv_smul`

English:
lemma isLittleOTVS_iff_tendsto_inv_smul
  statement: [ContinuousSMul 𝕜 E] {f : α -> 𝕜} {g : α -> E} {l : Filter α}
  proof: by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h => ?_⟩
  refine (((isLittleOTVS_one (𝕜 := 𝕜)).mpr h).smul_left f).congr' (h₀.mono fun x hx => ?_) (by simp)
  by_cases h : f x = 0 <;> simp [h, hx]

中文:
引理 isLittleOTVS_iff_tendsto_inv_smul
  结论: [连续标量乘法 𝕜 E] {f : α -> 𝕜} {g : α -> E} {l : 滤子 α}
  证明: by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h => ?_⟩
  refine (((isLittleOTVS_one (𝕜 := 𝕜)).mpr h).smul_left f).congr' (h₀.mono fun x hx => ?_) (by simp)
  by_cases h : f x = 0 <;> simp [h, hx]

Depends on / 依赖: IsLittleOTVS, IsLittleOTVS.tendsto_inv_smul, isLittleOTVS_one, smul_left, tendsto_inv_smul
-/
lemma isLittleOTVS_iff_tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α -> 𝕜} {g : α -> E} {l : Filter α}
    (h₀ : forallᶠ x in l, f x = 0 -> g x = 0) :
    g =o[𝕜; l] f ↔ Tendsto (fun x => (f x)⁻¹ • g x) l (𝓝 0) := by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h => ?_⟩
  refine (((isLittleOTVS_one (𝕜 := 𝕜)).mpr h).smul_left f).congr' (h₀.mono fun x hx => ?_) (by simp)
  by_cases h : f x = 0 <;> simp [h, hx]

variable (𝕜) in
/--
lemma `Filter.Tendsto.isBigOTVS_one` / 引理 `Filter.Tendsto.isBigOTVS_one`

English:
lemma Filter.Tendsto.isBigOTVS_one
  statement: [ContinuousAdd E] [ContinuousSMul 𝕜 E] {x : E}
  proof: by
  replace h : Tendsto (f · - x) l (𝓝 0) := by
    simpa [sub_eq_add_neg] using h.add (tendsto_const_nhds (x := -x))
  rw [(nhds_basis_balanced 𝕜 E).add_self.isBigOTVS_iff nhds_basis_ball]
  rintro U ⟨hU₀, hUb⟩
  obtain ⟨r, hr₀, hr₁, hr⟩ : exists r : Real>=0, 0 < r ∧ r <= 1 ∧ (r : Real>=0∞) <= (egauge 𝕜 U x)⁻¹ := by
    apply Eventually.exists_gt
    refine .and (eventually_le_nhds one_pos) ?_
    refine (ENNReal.tendsto_coe.mpr tendsto_id).eventually_le_const ?_
    suffices exists c : 𝕜, x in c • U by simpa [egauge_eq_top]
    simpa using (absorbent_nhds_zero (𝕜 := 𝕜) hU₀ x).exists
  use r, by positivity
  filter_upwards [h.eventually_mem hU₀] with a ha
  calc
    egauge 𝕜 (U + U) (f a) <= max (egauge 𝕜 U (f a - x)) (egauge 𝕜 U x) := by
      simpa using egauge_add_add_le hUb hUb (f a - x) x
    _ <= (r : Real>=0∞)⁻¹ := by
      apply max_le
      · refine (egauge_le_one _ ha).trans ?_
        simp [hr₁]
      · rwa [ENNReal.le_inv_iff_le_inv]
    _ <= egauge 𝕜 (ball (0 : 𝕜) _) 1 := by simpa using div_le_egauge_ball 𝕜 r (1 : 𝕜)

中文:
引理 滤子.收敛.isBigOTVS_one
  结论: [连续加法 E] [连续标量乘法 𝕜 E] {x : E}
  证明: by
  replace h : Tendsto (f · - x) l (𝓝 0) := by
    simpa [sub_eq_add_neg] using h.add (tendsto_const_nhds (x := -x))
  rw [(nhds_basis_balanced 𝕜 E).add_self.isBigOTVS_iff nhds_basis_ball]
  rintro U ⟨hU₀, hUb⟩
  obtain ⟨r, hr₀, hr₁, hr⟩ : exists r : Real>=0, 0 < r ∧ r <= 1 ∧ (r : Real>=0∞) <= (egauge 𝕜 U x)⁻¹ := by
    apply Eventually.exists_gt
    refine .and (eventually_le_nhds one_pos) ?_
    refine (ENNReal.tendsto_coe.mpr tendsto_id).eventually_le_const ?_
    suffices exists c : 𝕜, x in c • U by simpa [egauge_eq_top]
    simpa using (absorbent_nhds_zero (𝕜 := 𝕜) hU₀ x).exists
  use r, by positivity
  filter_upwards [h.eventually_mem hU₀] with a ha
  calc
    egauge 𝕜 (U + U) (f a) <= max (egauge 𝕜 U (f a - x)) (egauge 𝕜 U x) := by
      simpa using egauge_add_add_le hUb hUb (f a - x) x
    _ <= (r : Real>=0∞)⁻¹ := by
      apply max_le
      · refine (egauge_le_one _ ha).trans ?_
        simp [hr₁]
      · rwa [ENNReal.le_inv_iff_le_inv]
    _ <= egauge 𝕜 (ball (0 : 𝕜) _) 1 := by simpa using div_le_egauge_ball 𝕜 r (1 : 𝕜)

Depends on / 依赖: ENNReal, ENNReal.tendsto_coe.mpr, Eventually, Eventually.exists_gt, Tendsto, add_self, add_self.isBigOTVS_iff, egauge, egauge_eq_, eventually_le_const, eventually_le_nhds, exists_gt, h.add, isBigOTVS_iff, nhds_basis_balanced, nhds_basis_ball, one_pos, replace, sub_eq_add_neg, tendsto_coe
-/
lemma Filter.Tendsto.isBigOTVS_one [ContinuousAdd E] [ContinuousSMul 𝕜 E] {x : E}
    (h : Tendsto f l (𝓝 x)) : f =O[𝕜; l] (fun _ => 1 : α -> 𝕜) := by
  replace h : Tendsto (f · - x) l (𝓝 0) := by
    simpa [sub_eq_add_neg] using h.add (tendsto_const_nhds (x := -x))
  rw [(nhds_basis_balanced 𝕜 E).add_self.isBigOTVS_iff nhds_basis_ball]
  rintro U ⟨hU₀, hUb⟩
  obtain ⟨r, hr₀, hr₁, hr⟩ : exists r : Real>=0, 0 < r ∧ r <= 1 ∧ (r : Real>=0∞) <= (egauge 𝕜 U x)⁻¹ := by
    apply Eventually.exists_gt
    refine .and (eventually_le_nhds one_pos) ?_
    refine (ENNReal.tendsto_coe.mpr tendsto_id).eventually_le_const ?_
    suffices exists c : 𝕜, x in c • U by simpa [egauge_eq_top]
    simpa using (absorbent_nhds_zero (𝕜 := 𝕜) hU₀ x).exists
  use r, by positivity
  filter_upwards [h.eventually_mem hU₀] with a ha
  calc
    egauge 𝕜 (U + U) (f a) <= max (egauge 𝕜 U (f a - x)) (egauge 𝕜 U x) := by
      simpa using egauge_add_add_le hUb hUb (f a - x) x
    _ <= (r : Real>=0∞)⁻¹ := by
      apply max_le
      · refine (egauge_le_one _ ha).trans ?_
        simp [hr₁]
      · rwa [ENNReal.le_inv_iff_le_inv]
    _ <= egauge 𝕜 (ball (0 : 𝕜) _) 1 := by simpa using div_le_egauge_ball 𝕜 r (1 : 𝕜)

end TopologicalSpace

section NormedSpace

variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
variable {f : α -> E} {g : α -> F} {l : Filter α}

/--
lemma `isLittleOTVS_iff_isLittleO` / 引理 `isLittleOTVS_iff_isLittleO`

English:
lemma isLittleOTVS_iff_isLittleO
  statement: f =o[𝕜; l] g ↔ f =o[l] g
  proof: by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ⟨1, one_pos, fun δ hδ => ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to Real>=0 using hε.le; lift δ to Real>=0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : Real>=0∞) <= ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff₀' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : Real>=0∞) <= egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ <= ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ <= (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ <= 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ <= ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to Real>=0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) <= ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ <= ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ <= 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ <= δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one

alias ⟨isLittleOTVS.isLittleO, IsLittleO.isLittleOTVS⟩ := isLittleOTVS_iff_isLittleO

中文:
引理 isLittleOTVS_iff_isLittleO
  结论: f =o[𝕜; l] g ↔ f =o[l] g
  证明: by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ⟨1, one_pos, fun δ hδ => ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to Real>=0 using hε.le; lift δ to Real>=0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : Real>=0∞) <= ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff₀' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : Real>=0∞) <= egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ <= ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ <= (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ <= 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ <= ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to Real>=0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) <= ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ <= ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ <= 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ <= δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one

alias ⟨isLittleOTVS.isLittleO, IsLittleO.isLittleOTVS⟩ := isLittleOTVS_iff_isLittleO

Depends on / 依赖: ENNReal, ENNReal.coe_div, NormedField, NormedField.exists_one_lt_norm, coe_div, div_pos, exists_one_lt_norm, filter_upwards, isLittleOTVS_iff, isLittleO_iff, nhds_basis_ball, nhds_basis_ball.isLittleOTVS_iff, one_pos, one_pos.trans
-/
lemma isLittleOTVS_iff_isLittleO : f =o[𝕜; l] g ↔ f =o[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ⟨1, one_pos, fun δ hδ => ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to Real>=0 using hε.le; lift δ to Real>=0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : Real>=0∞) <= ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff₀' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : Real>=0∞) <= egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ <= ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ <= (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ <= 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ <= ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to Real>=0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) <= ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ <= ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ <= 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ <= δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one

alias ⟨isLittleOTVS.isLittleO, IsLittleO.isLittleOTVS⟩ := isLittleOTVS_iff_isLittleO

/--
lemma `isBigOTVS_iff_isBigO` / 引理 `isBigOTVS_iff_isBigO`

English:
lemma isBigOTVS_iff_isBigO
  statement: f =O[𝕜; l] g ↔ f =O[l] g
  proof: by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  constructor
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff]
    intro h
    rcases h 1 one_pos with ⟨r, hr₀, hr⟩
    lift r to Real>=0 using hr₀.le
    norm_cast at hr₀
    refine ⟨(‖c‖₊ / r : Real>=0), hr.mono fun x hx => ?_⟩
    suffices ‖f x‖ₑ <= (‖c‖₊ / r : Real>=0) * ‖g x‖ₑ by
      simp only [enorm_eq_nnnorm, ← coe_nnnorm] at this ⊢
      exact mod_cast this
    calc
      ‖f x‖ₑ <= egauge 𝕜 (ball 0 1) (f x) := le_egauge_ball_one ..
      _ <= egauge 𝕜 (ball 0 r) (g x) := hx
      _ <= ‖c‖ₑ * ‖g x‖ₑ / ↑r :=
egauge_ball_le_of_one_lt_norm hc .inl hr₀.ne'
      _ = (‖c‖₊ / r : Real>=0) * ‖g x‖ₑ := by
        simp [hr₀.ne', ENNReal.mul_div_right_comm, enorm_eq_nnnorm]
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff']
    have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
    rintro ⟨C, hC₀, hC⟩ r hr₀
    lift C to Real>=0 using hC₀.le; norm_cast at hC₀
    lift r to Real>=0 using hr₀.le; norm_cast at hr₀
    refine ⟨r / (C * ‖c‖₊), by positivity, hC.mono fun x hx => ?_⟩
    calc
      egauge 𝕜 (ball 0 r) (f x) <= ‖c‖ₑ * ‖f x‖ₑ / r :=
egauge_ball_le_of_one_lt_norm hc .inl hr₀.ne'
      _ <= ‖c‖ₑ * (C * ‖g x‖ₑ) / r := by
        gcongr
        simp only [enorm_eq_nnnorm, ← coe_nnnorm] at hx ⊢
        exact mod_cast hx
      _ = ‖g x‖ₑ / (r / (C * ‖c‖₊) : Real>=0) := by
        simp_all [pos_iff_ne_zero, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        ac_rfl
      _ <= _ := div_le_egauge_ball _ _ _

alias ⟨IsBigOTVS.isBigO, IsBigO.isBigOTVS⟩ := isBigOTVS_iff_isBigO

@[deprecated (since := "2026-02-03")]
alias isBigOTVS.isBigO := IsBigOTVS.isBigO

中文:
引理 isBigOTVS_iff_isBigO
  结论: f =O[𝕜; l] g ↔ f =O[l] g
  证明: by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  constructor
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff]
    intro h
    rcases h 1 one_pos with ⟨r, hr₀, hr⟩
    lift r to Real>=0 using hr₀.le
    norm_cast at hr₀
    refine ⟨(‖c‖₊ / r : Real>=0), hr.mono fun x hx => ?_⟩
    suffices ‖f x‖ₑ <= (‖c‖₊ / r : Real>=0) * ‖g x‖ₑ by
      simp only [enorm_eq_nnnorm, ← coe_nnnorm] at this ⊢
      exact mod_cast this
    calc
      ‖f x‖ₑ <= egauge 𝕜 (ball 0 1) (f x) := le_egauge_ball_one ..
      _ <= egauge 𝕜 (ball 0 r) (g x) := hx
      _ <= ‖c‖ₑ * ‖g x‖ₑ / ↑r :=
egauge_ball_le_of_one_lt_norm hc .inl hr₀.ne'
      _ = (‖c‖₊ / r : Real>=0) * ‖g x‖ₑ := by
        simp [hr₀.ne', ENNReal.mul_div_right_comm, enorm_eq_nnnorm]
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff']
    have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
    rintro ⟨C, hC₀, hC⟩ r hr₀
    lift C to Real>=0 using hC₀.le; norm_cast at hC₀
    lift r to Real>=0 using hr₀.le; norm_cast at hr₀
    refine ⟨r / (C * ‖c‖₊), by positivity, hC.mono fun x hx => ?_⟩
    calc
      egauge 𝕜 (ball 0 r) (f x) <= ‖c‖ₑ * ‖f x‖ₑ / r :=
egauge_ball_le_of_one_lt_norm hc .inl hr₀.ne'
      _ <= ‖c‖ₑ * (C * ‖g x‖ₑ) / r := by
        gcongr
        simp only [enorm_eq_nnnorm, ← coe_nnnorm] at hx ⊢
        exact mod_cast hx
      _ = ‖g x‖ₑ / (r / (C * ‖c‖₊) : Real>=0) := by
        simp_all [pos_iff_ne_zero, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        ac_rfl
      _ <= _ := div_le_egauge_ball _ _ _

alias ⟨IsBigOTVS.isBigO, IsBigO.isBigOTVS⟩ := isBigOTVS_iff_isBigO

@[deprecated (since := "2026-02-03")]
alias isBigOTVS.isBigO := IsBigOTVS.isBigO

Depends on / 依赖: NormedField, NormedField.exists_one_lt_norm, coe_nnnorm, egauge, enorm_eq_nnnorm, exists_one_lt_norm, hr.mono, isBigOTVS_iff, isBigO_iff, le_egauge_ball_one, mod_cast, nhds_basis_ball, nhds_basis_ball.isBigOTVS_iff, one_pos
-/
lemma isBigOTVS_iff_isBigO : f =O[𝕜; l] g ↔ f =O[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  constructor
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff]
    intro h
    rcases h 1 one_pos with ⟨r, hr₀, hr⟩
    lift r to Real>=0 using hr₀.le
    norm_cast at hr₀
    refine ⟨(‖c‖₊ / r : Real>=0), hr.mono fun x hx => ?_⟩
    suffices ‖f x‖ₑ <= (‖c‖₊ / r : Real>=0) * ‖g x‖ₑ by
      simp only [enorm_eq_nnnorm, ← coe_nnnorm] at this ⊢
      exact mod_cast this
    calc
      ‖f x‖ₑ <= egauge 𝕜 (ball 0 1) (f x) := le_egauge_ball_one ..
      _ <= egauge 𝕜 (ball 0 r) (g x) := hx
      _ <= ‖c‖ₑ * ‖g x‖ₑ / ↑r :=
egauge_ball_le_of_one_lt_norm hc .inl hr₀.ne'
      _ = (‖c‖₊ / r : Real>=0) * ‖g x‖ₑ := by
        simp [hr₀.ne', ENNReal.mul_div_right_comm, enorm_eq_nnnorm]
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff']
    have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
    rintro ⟨C, hC₀, hC⟩ r hr₀
    lift C to Real>=0 using hC₀.le; norm_cast at hC₀
    lift r to Real>=0 using hr₀.le; norm_cast at hr₀
    refine ⟨r / (C * ‖c‖₊), by positivity, hC.mono fun x hx => ?_⟩
    calc
      egauge 𝕜 (ball 0 r) (f x) <= ‖c‖ₑ * ‖f x‖ₑ / r :=
egauge_ball_le_of_one_lt_norm hc .inl hr₀.ne'
      _ <= ‖c‖ₑ * (C * ‖g x‖ₑ) / r := by
        gcongr
        simp only [enorm_eq_nnnorm, ← coe_nnnorm] at hx ⊢
        exact mod_cast hx
      _ = ‖g x‖ₑ / (r / (C * ‖c‖₊) : Real>=0) := by
        simp_all [pos_iff_ne_zero, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        ac_rfl
      _ <= _ := div_le_egauge_ball _ _ _

alias ⟨IsBigOTVS.isBigO, IsBigO.isBigOTVS⟩ := isBigOTVS_iff_isBigO

@[deprecated (since := "2026-02-03")]
alias isBigOTVS.isBigO := IsBigOTVS.isBigO

/--
lemma `isThetaTVS_iff_isTheta` / 引理 `isThetaTVS_iff_isTheta`

English:
lemma isThetaTVS_iff_isTheta
  statement: f =Θ[𝕜; l] g ↔ f =Θ[l] g
  proof: .and isBigOTVS_iff_isBigO isBigOTVS_iff_isBigO

alias ⟨IsThetaTVS.isTheta, IsTheta.isThetaTVS⟩ := isThetaTVS_iff_isTheta

中文:
引理 isThetaTVS_iff_isTheta
  结论: f =Θ[𝕜; l] g ↔ f =Θ[l] g
  证明: .and isBigOTVS_iff_isBigO isBigOTVS_iff_isBigO

alias ⟨IsThetaTVS.isTheta, IsTheta.isThetaTVS⟩ := isThetaTVS_iff_isTheta

Depends on / 依赖: isBigOTVS_iff_isBigO
-/
lemma isThetaTVS_iff_isTheta : f =Θ[𝕜; l] g ↔ f =Θ[l] g :=
  .and isBigOTVS_iff_isBigO isBigOTVS_iff_isBigO

alias ⟨IsThetaTVS.isTheta, IsTheta.isThetaTVS⟩ := isThetaTVS_iff_isTheta

end NormedSpace

end Asymptotics
