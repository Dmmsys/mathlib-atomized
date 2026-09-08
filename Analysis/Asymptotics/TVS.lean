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
/-
**Asymptotics.IsLittleOTVS** 是 Mathlib 中的一个归纳类型，位于命名空间 `Asymptotics`。
形式化陈述：(𝕜 : Type u_1) →   {α : Type u_2} →     {E : Type u_3} →       {F : Type u
_4} →         [ENorm 𝕜] →           [TopologicalSpace E] →             [Topologi
calSpace F] → [Zero E] → [Zero F] → [SMul 𝕜 E] → [SMul 𝕜 F] → Filter α → (α → E)
 → (α → F) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f =o[𝕜; l] g` (`IsLittleOTVS 𝕜 l f g`) is a generalization of `f =o[l] g` (`IsL
ittleO l f g`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ if for any neighborhood of zero `U` in the codomain of `f
`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g
(x)))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

We use an `ENNReal`-valued function `egauge` for the gauge,
so we unfold the definition of little o instead of reusing it.
-/
structure IsLittleOTVS (l : Filter α) (f : α → E) (g : α → F) : Prop where
  exists_eventuallyLE_mul : ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ (0 : ℝ≥0),
    (fun x ↦ egauge 𝕜 U (f x)) ≤ᶠ[l] (fun x ↦ ε * egauge 𝕜 V (g x))

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
/-
**Asymptotics.IsBigOTVS** 是 Mathlib 中的一个归纳类型，位于命名空间 `Asymptotics`。
形式化陈述：(𝕜 : Type u_1) →   {α : Type u_2} →     {E : Type u_3} →       {F : Type u
_4} →         [ENorm 𝕜] →           [TopologicalSpace E] →             [Topologi
calSpace F] → [Zero E] → [Zero F] → [SMul 𝕜 E] → [SMul 𝕜 F] → Filter α → (α → E)
 → (α → F) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f =O[𝕜; l] g` (`IsBigOTVS 𝕜 l f g`) is a generalization of `f =O[l] g` (`IsBigO
 l f g`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `𝕜`,
we say that $f = O(g)$ if for any neighborhood of zero `U` in the codomain of `f
`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) \le \operatorname{gauge}_{K, V} (g
(x))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.
-/
structure IsBigOTVS (l : Filter α) (f : α → E) (g : α → F) : Prop where
  exists_eventuallyLE : ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F),
    (egauge 𝕜 U <| f ·) ≤ᶠ[l] (egauge 𝕜 V <| g ·)

@[inherit_doc]
notation:100 f " =O[" 𝕜 "; " l "] " g:100 => IsBigOTVS 𝕜 l f g

/-- We say that `f =Θ[𝕜; l] g` (`IsThetaTVS 𝕜 l f g`), if `f =O[𝕜; l] g` and `g =O[𝕜; l] f`.
It is a generalization of `f =Θ[l] g` that works in topological `𝕜`-vector spaces. -/
/-
**Asymptotics.IsThetaTVS** 是 Mathlib 中的一个定义，位于命名空间 `Asymptotics`。
形式化陈述：IsThetaTVS (l : Filter α) (f : α -> E) (g : α -> F) : Prop
参数：l : Filter α；f : α -> E；g : α -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `f =Θ[𝕜; l] g` (`IsThetaTVS 𝕜 l f g`), if `f =O[𝕜; l] g` and `g =O[𝕜
; l] f`.
It is a generalization of `f =Θ[l] g` that works in topological `𝕜`-vector space
s.
-/
def IsThetaTVS (l : Filter α) (f : α → E) (g : α → F) : Prop :=
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

variable {f f₁ f₂ : α → E} {g g₁ g₂ : α → F} {l : Filter α}

/-
**Asymptotics.isLittleOTVS_iff_tendsto_div** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：isLittleOTVS_iff_tendsto_div : f =o[𝕜; l] g ↔ forall U in 𝓝 0, exists V in
 𝓝 0, Tendsto (fun x => egauge 𝕜 U (f x) / egauge 𝕜 V (g x)) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.nhds_coe`：nhds_coe {r : Real>=0} : 𝓝 (r : Real>=0∞) = (𝓝 r).map 
(↑)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `nhds_bot_basis_Iic`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α] [Densel
yOrdered…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ENNReal.image_coe_Iic`：image_coe_Iic (x : Real>=0) : (↑) '' Iic x = Iic 
(x : Real>=0∞)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleOTVS_iff_tendsto_div :
    f =o[𝕜; l] g ↔ ∀ U ∈ 𝓝 0, ∃ V ∈ 𝓝 0,
      Tendsto (fun x ↦ egauge 𝕜 U (f x) / egauge 𝕜 V (g x)) l (𝓝 0) := by
  simp only [isLittleOTVS_iff, ← ENNReal.coe_zero, ENNReal.nhds_coe, ← NNReal.bot_eq_zero,
    (nhds_bot_basis_Iic.map _).tendsto_right_iff]
  simp +contextual [ENNReal.div_le_iff_le_mul, pos_iff_ne_zero, EventuallyLE]

alias ⟨IsLittleOTVS.tendsto_div, IsLittleOTVS.of_tendsto_div⟩ := isLittleOTVS_iff_tendsto_div

/-- A version of `IsLittleOTVS.exists_eventuallyLE_mul`
where `ε` is quantified over `ℝ≥0∞` instead of `ℝ≥0`. -/
/-
**Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul_ennreal** 是 Mathlib 中的一个定理，位于
命名空间 `Asymptotics.IsLittleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f : α → E} {g : α → F} {l : Filter α},   f
 =o[𝕜; l] g →     ∀ {U : Set E},       U ∈ nhds 0 →         ∃ V ∈ nhds 0, ∀ (ε :
 ENNReal), ε ≠ 0 → (fun x => egauge 𝕜 U (f x)) ≤ᶠ[l] fun x => ε * egauge 𝕜 V (g 
x)
参数：ε : ENNReal；fun x => egauge 𝕜 U (f x)；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul`：∀ {𝕜 : Type u_1} {α : 
Type u_2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSp
ace E]   [inst_2 : TopologicalSpace F]…
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
A version of `IsLittleOTVS.exists_eventuallyLE_mul`
where `ε` is quantified over `ℝ≥0∞` instead of `ℝ≥0`.
-/
theorem IsLittleOTVS.exists_eventuallyLE_mul_ennreal (h : f =o[𝕜; l] g) {U : Set E} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ 0, (fun x ↦ egauge 𝕜 U (f x)) ≤ᶠ[l] (fun x ↦ ε * egauge 𝕜 V (g x)) := by
  obtain ⟨V, hV₀, hV⟩ := h.exists_eventuallyLE_mul U hU
  refine ⟨V, hV₀, fun ε hε ↦ ?_⟩
  cases ε with
  | top => exact (hV 1 one_ne_zero).trans <| .of_forall fun _ ↦ by dsimp; grw [← le_top]
  | coe ε => exact hV ε (mod_cast hε)
/-
**Asymptotics.isLittleOTVS_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[𝕜; l] g₁ 
↔ f₂ =o[𝕜; l] g₂
参数：hf : f₁ =ᶠ[l] f₂；hg : g₁ =ᶠ[l] g₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
-/
theorem isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =o[𝕜; l] g₁ ↔ f₂ =o[𝕜; l] g₂ := by
  simp only [isLittleOTVS_iff_tendsto_div]
  peel with U hU V hV
  exact tendsto_congr' (hf.comp₂ (egauge _ _ · / egauge _ _ ·) hg)

/-- A stronger version of `IsLittleOTVS.congr` that requires the functions only agree along the
filter. -/
/-
**Asymptotics.IsLittleOTVS.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittl
eOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter
 α},   f₁ =o[𝕜; l] g₁ → f₁ =ᶠ[l] f₂ → g₁ =ᶠ[l] g₂ → f₂ =o[𝕜; l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleOTVS_congr`：isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (h
g : g₁ =ᶠ[l] g₂) : f₁ =o[𝕜; l] g₁ ↔ f₂ =o[𝕜; l] g₂

--- 原说明 ---
A stronger version of `IsLittleOTVS.congr` that requires the functions only agre
e along the
filter.
-/
theorem IsLittleOTVS.congr' (h : f₁ =o[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =o[𝕜; l] g₂ :=
  (isLittleOTVS_congr hf hg).mp h
/-
**Asymptotics.IsLittleOTVS.congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
OTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter
 α},   f₁ =o[𝕜; l] g₁ → (∀ (x : α), f₁ x = f₂ x) → (∀ (x : α), g₁ x = g₂ x) → f₂
 =o[𝕜; l] g₂
参数：∀ (x : α), f₁ x = f₂ x；∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.congr'`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGro
up E] [inst_2 : Topol…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem IsLittleOTVS.congr (h : f₁ =o[𝕜; l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[𝕜; l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
/-
**Asymptotics.IsLittleOTVS.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f₁ f₂ : α → E} {g : α → F} {l : Filter α},
   f₁ =o[𝕜; l] g → (∀ (x : α), f₁ x = f₂ x) → f₂ =o[𝕜; l] g
参数：∀ (x : α), f₁ x = f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.congr`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGrou
p E] [inst_2 : Topol…
-/
theorem IsLittleOTVS.congr_left (h : f₁ =o[𝕜; l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[𝕜; l] g :=
  h.congr hf fun _ ↦ rfl
/-
**Asymptotics.IsLittleOTVS.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
LittleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f : α → E} {g₁ g₂ : α → F} {l : Filter α},
   f =o[𝕜; l] g₁ → (∀ (x : α), g₁ x = g₂ x) → f =o[𝕜; l] g₂
参数：∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.congr`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGrou
p E] [inst_2 : Topol…
-/
theorem IsLittleOTVS.congr_right (h : f =o[𝕜; l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[𝕜; l] g₂ :=
  h.congr (fun _ ↦ rfl) hg
/-
**Asymptotics.isBigOTVS_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[𝕜; l] g₁ ↔ f
₂ =O[𝕜; l] g₂
参数：hf : f₁ =ᶠ[l] f₂；hg : g₁ =ᶠ[l] g₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Filter.eventuallyLE_congr`：eventuallyLE_congr {f f' g g' : α -> β} (hf :
 f =ᶠ[l] f') (hg : g =ᶠ[l] g') : f <=ᶠ[l] g ↔ f' <=ᶠ[l] g'
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem isBigOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =O[𝕜; l] g₁ ↔ f₂ =O[𝕜; l] g₂ := by
  simp only [isBigOTVS_iff]
  peel with U hU V hV
  exact eventuallyLE_congr (hf.fun_comp (egauge 𝕜 U)) (hg.fun_comp (egauge 𝕜 V))

/-- A stronger version of `IsBigOTVS.congr` that requires the functions only agree along the
filter. -/
/-
**Asymptotics.IsBigOTVS.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`
。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter
 α},   f₁ =O[𝕜; l] g₁ → f₁ =ᶠ[l] f₂ → g₁ =ᶠ[l] g₂ → f₂ =O[𝕜; l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigOTVS_congr`：isBigOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁
 =ᶠ[l] g₂) : f₁ =O[𝕜; l] g₁ ↔ f₂ =O[𝕜; l] g₂

--- 原说明 ---
A stronger version of `IsBigOTVS.congr` that requires the functions only agree a
long the
filter.
-/
theorem IsBigOTVS.congr' (h : f₁ =O[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =O[𝕜; l] g₂ :=
  (isBigOTVS_congr hf hg).mp h
/-
**Asymptotics.IsBigOTVS.congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter
 α},   f₁ =O[𝕜; l] g₁ → (∀ (x : α), f₁ x = f₂ x) → (∀ (x : α), g₁ x = g₂ x) → f₂
 =O[𝕜; l] g₂
参数：∀ (x : α), f₁ x = f₂ x；∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.congr'`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup 
E] [inst_2 : Topol…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem IsBigOTVS.congr (h : f₁ =O[𝕜; l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[𝕜; l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
/-
**Asymptotics.IsBigOTVS.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
TVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f₁ f₂ : α → E} {g : α → F} {l : Filter α},
   f₁ =O[𝕜; l] g → (∀ (x : α), f₁ x = f₂ x) → f₂ =O[𝕜; l] g
参数：∀ (x : α), f₁ x = f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.congr`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E
] [inst_2 : Topol…
-/
theorem IsBigOTVS.congr_left (h : f₁ =O[𝕜; l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[𝕜; l] g :=
  h.congr hf fun _ ↦ rfl
/-
**Asymptotics.IsBigOTVS.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
OTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f : α → E} {g₁ g₂ : α → F} {l : Filter α},
   f =O[𝕜; l] g₁ → (∀ (x : α), g₁ x = g₂ x) → f =O[𝕜; l] g₂
参数：∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.congr`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E
] [inst_2 : Topol…
-/
theorem IsBigOTVS.congr_right (h : f =O[𝕜; l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[𝕜; l] g₂ :=
  h.congr (fun _ ↦ rfl) hg

end congr

variable {l l₁ l₂ : Filter α} {f : α → E} {g : α → F}

/-
**Asymptotics.IsBigOTVS.refl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : _roo
t_.Module 𝕜 E] (f : α → E) (l : Filter α), f =O[𝕜; l] f
参数：f : α → E；l : Filter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigOTVS_iff`：∀ (𝕜 : Type u_1) {α : Type u_2} {E : Type u_3
} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E]   [inst_2 : Topo
logicalSpace F]…
· 使用定理 `Filter.EventuallyLE.rfl`：∀ {α : Type u} {β : Type v} [inst : Preorder β]
 {l : Filter α} {f : α → β}, f ≤ᶠ[l] f
-/
protected theorem IsBigOTVS.refl (f : α → E) (l : Filter α) : f =O[𝕜; l] f := by
  rw [isBigOTVS_iff]
  exact fun U hU ↦ ⟨U, hU, EventuallyLE.rfl⟩
/-
**Asymptotics.IsBigOTVS.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : _roo
t_.Module 𝕜 E] {l : Filter α} {f : α → E}, f =O[𝕜; l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.refl`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_
4} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : Topo
logicalSpace E] …
-/
protected theorem IsBigOTVS.rfl : f =O[𝕜; l] f := .refl f l
/-
**Asymptotics.IsThetaTVS.refl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThetaTVS`
。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : _roo
t_.Module 𝕜 E] (f : α → E) (l : Filter α), f =Θ[𝕜; l] f
参数：f : α → E；l : Filter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.rfl`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : Topol
ogicalSpace E] …
-/
protected theorem IsThetaTVS.refl (f : α → E) (l : Filter α) : f =Θ[𝕜; l] f :=
  ⟨.rfl, .rfl⟩
/-
**Asymptotics.IsThetaTVS.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThetaTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : _roo
t_.Module 𝕜 E] {l : Filter α} {f : α → E}, f =Θ[𝕜; l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.refl`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : Top
ologicalSpace E] …
-/
protected theorem IsThetaTVS.rfl : f =Θ[𝕜; l] f := .refl f l
/-
**Asymptotics.IsLittleOTVS.isBigOTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F},   f
 =o[𝕜; l] g → f =O[𝕜; l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul`：∀ {𝕜 : Type u_1} {α : 
Type u_2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSp
ace E]   [inst_2 : TopologicalSpace F]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem IsLittleOTVS.isBigOTVS (h : f =o[𝕜; l] g) : f =O[𝕜; l] g := by
  refine ⟨fun U hU ↦ ?_⟩
  rcases h.1 U hU with ⟨V, hV₀, hV⟩
  use V, hV₀
  simpa using hV 1 one_ne_zero
/-
**Asymptotics.IsThetaTVS.isBigOTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThet
aTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F},   f
 =Θ[𝕜; l] g → f =O[𝕜; l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsThetaTVS.isBigOTVS (h : f =Θ[𝕜; l] g) : f =O[𝕜; l] g := h.left

@[symm]
/-
**Asymptotics.IsThetaTVS.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThetaTVS`
。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F},   f
 =Θ[𝕜; l] g → g =Θ[𝕜; l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem IsThetaTVS.symm (h : f =Θ[𝕜; l] g) : g =Θ[𝕜; l] f := And.symm h
/-
**Asymptotics.isThetaTVS_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isThetaTVS_comm : f =Θ[𝕜; l] g ↔ g =Θ[𝕜; l] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem isThetaTVS_comm : f =Θ[𝕜; l] g ↔ g =Θ[𝕜; l] f := and_comm

/-!
### Transitivity lemmas
-/

section Trans

variable {k : α → G}

@[trans]
/-
**Asymptotics.IsBigOTVS.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =O[𝕜; l] g → g =O[𝕜; l] k → f =O[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.exists_eventuallyLE`：∀ {𝕜 : Type u_1} {α : Type u_
2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E] 
  [inst_2 : TopologicalSpace F]…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsBigOTVS.trans (hfg : f =O[𝕜; l] g) (hgk : g =O[𝕜; l] k) : f =O[𝕜; l] k := by
  refine ⟨fun U hU₀ ↦ ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, ?_⟩
  filter_upwards [hV, hW] with x hx₁ hx₂ using hx₁.trans hx₂
/-
**Asymptotics.instTransIsBigOTVSIsBigOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics
`。
形式化陈述：instTransIsBigOTVSIsBigOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsBigOTVS
 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
-/
instance instTransIsBigOTVSIsBigOTVS :
    @Trans (α → E) (α → F) (α → G) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsBigOTVS.trans
/-
**Asymptotics.IsBigOTVS.trans_isThetaTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =O[𝕜; l] g → g =Θ[𝕜; l] k → f =O[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `Asymptotics.IsThetaTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
-/
theorem IsBigOTVS.trans_isThetaTVS (hfg : f =O[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) :
    f =O[𝕜; l] k :=
  hfg.trans hgk.isBigOTVS
/-
**Asymptotics.instTransIsBigOTVSIsThetaTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotic
s`。
形式化陈述：instTransIsBigOTVSIsThetaTVS : @Trans (α -> E) (α -> F) (α -> G) (IsBigOTV
S 𝕜 l) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isThetaTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} 
{E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜] 
  [inst_1 : AddCommGroup E] …
-/
instance instTransIsBigOTVSIsThetaTVS :
    @Trans (α → E) (α → F) (α → G) (IsBigOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsBigOTVS.trans_isThetaTVS
/-
**Asymptotics.IsThetaTVS.trans_isBigOTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsThetaTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =Θ[𝕜; l] g → g =O[𝕜; l] k → f =O[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `Asymptotics.IsThetaTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
-/
theorem IsThetaTVS.trans_isBigOTVS (hfg : f =Θ[𝕜; l] g) (hgk : g =O[𝕜; l] k) :
    f =O[𝕜; l] k :=
  hfg.isBigOTVS.trans hgk
/-
**Asymptotics.instTransIsThetaOTVSIsBigOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymptoti
cs`。
形式化陈述：instTransIsThetaOTVSIsBigOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsTheta
TVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.trans_isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} 
{E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜] 
  [inst_1 : AddCommGroup E] …
-/
instance instTransIsThetaOTVSIsBigOTVS :
    @Trans (α → E) (α → F) (α → G) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsThetaTVS.trans_isBigOTVS

@[trans]
/-
**Asymptotics.IsThetaTVS.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThetaTVS
`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =Θ[𝕜; l] g → g =Θ[𝕜; l] k → f =Θ[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsThetaTVS.trans (hfg : f =Θ[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) : f =Θ[𝕜; l] k :=
  ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩
/-
**Asymptotics.instTransIsThetaOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：instTransIsThetaOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsThetaTVS 𝕜 l) 
(IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 
: AddCommGroup E] …
-/
instance instTransIsThetaOTVS :
    @Trans (α → E) (α → F) (α → G) (IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) where
  trans := IsThetaTVS.trans
/-
**Asymptotics.IsLittleOTVS.trans_isBigOTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsLittleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =o[𝕜; l] g → g =O[𝕜; l] k → f =o[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul`：∀ {𝕜 : Type u_1} {α : 
Type u_2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSp
ace E]   [inst_2 : TopologicalSpace F]…
· 使用定理 `Asymptotics.IsBigOTVS.exists_eventuallyLE`：∀ {𝕜 : Type u_1} {α : Type u_
2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E] 
  [inst_2 : TopologicalSpace F]…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem IsLittleOTVS.trans_isBigOTVS (hfg : f =o[𝕜; l] g) (hgk : g =O[𝕜; l] k) :
    f =o[𝕜; l] k := by
  refine ⟨fun U hU₀ ↦ ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε ↦ ?_⟩
  filter_upwards [hV ε hε, hW] with x hx₁ hx₂ using hx₁.trans <| by gcongr
/-
**Asymptotics.instTransIsLittleOTVSIsBigOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymptot
ics`。
形式化陈述：instTransIsLittleOTVSIsBigOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsLitt
leOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.trans_isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
-/
instance instTransIsLittleOTVSIsBigOTVS :
    @Trans (α → E) (α → F) (α → G) (IsLittleOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans_isBigOTVS
/-
**Asymptotics.IsLittleOTVS.trans_isThetaTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsLittleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =o[𝕜; l] g → g =Θ[𝕜; l] k → f =o[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.trans_isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `Asymptotics.IsThetaTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
-/
theorem IsLittleOTVS.trans_isThetaTVS (hfg : f =o[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) :
    f =o[𝕜; l] k :=
  hfg.trans_isBigOTVS hgk.isBigOTVS
/-
**Asymptotics.instTransIsLittleOTVSIsThetaTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asympto
tics`。
形式化陈述：instTransIsLittleOTVSIsThetaTVS : @Trans (α -> E) (α -> F) (α -> G) (IsLit
tleOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.trans_isThetaTVS`：∀ {α : Type u_1} {𝕜 : Type u_
3} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 
𝕜]   [inst_1 : AddCommGroup E] …
-/
instance instTransIsLittleOTVSIsThetaTVS :
    @Trans (α → E) (α → F) (α → G) (IsLittleOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans_isThetaTVS
/-
**Asymptotics.IsBigOTVS.trans_isLittleOTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =O[𝕜; l] g → g =o[𝕜; l] k → f =o[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.exists_eventuallyLE`：∀ {𝕜 : Type u_1} {α : Type u_
2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E] 
  [inst_2 : TopologicalSpace F]…
· 使用定理 `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul`：∀ {𝕜 : Type u_1} {α : 
Type u_2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSp
ace E]   [inst_2 : TopologicalSpace F]…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsBigOTVS.trans_isLittleOTVS (hfg : f =O[𝕜; l] g) (hgk : g =o[𝕜; l] k) :
    f =o[𝕜; l] k := by
  refine ⟨fun U hU₀ ↦ ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε ↦ ?_⟩
  filter_upwards [hV, hW ε hε] with x hx₁ hx₂ using hx₁.trans hx₂
/-
**Asymptotics.instTransIsBigOTVSIsLittleOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymptot
ics`。
形式化陈述：instTransIsBigOTVSIsLittleOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsBigO
TVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
-/
instance instTransIsBigOTVSIsLittleOTVS :
    @Trans (α → E) (α → F) (α → G) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsBigOTVS.trans_isLittleOTVS
/-
**Asymptotics.IsThetaTVS.trans_isLittleOTVS** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsThetaTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =Θ[𝕜; l] g → g =o[𝕜; l] k → f =o[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `Asymptotics.IsThetaTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
-/
theorem IsThetaTVS.trans_isLittleOTVS (hfg : f =Θ[𝕜; l] g) (hgk : g =o[𝕜; l] k) :
    f =o[𝕜; l] k :=
  hfg.isBigOTVS.trans_isLittleOTVS hgk
/-
**Asymptotics.instTransIsThetaTVSIsLittleOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asympto
tics`。
形式化陈述：instTransIsThetaTVSIsLittleOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsThe
taTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsThetaTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_
3} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 
𝕜]   [inst_1 : AddCommGroup E] …
-/
instance instTransIsThetaTVSIsLittleOTVS :
    @Trans (α → E) (α → F) (α → G) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsThetaTVS.trans_isLittleOTVS

@[trans]
/-
**Asymptotics.IsLittleOTVS.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
OTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} {k : α → G},   f =o[𝕜; l] g → g =o[𝕜; l] k → f =o[𝕜; l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.trans_isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `Asymptotics.IsLittleOTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
theorem IsLittleOTVS.trans (hfg : f =o[𝕜; l] g) (hgk : g =o[𝕜; l] k) : f =o[𝕜; l] k :=
  hfg.trans_isBigOTVS hgk.isBigOTVS
/-
**Asymptotics.instTransIsLittleOTVSIsLittleOTVS** 是 Mathlib 中的一个实例，位于命名空间 `Asymp
totics`。
形式化陈述：instTransIsLittleOTVSIsLittleOTVS : @Trans (α -> E) (α -> F) (α -> G) (IsL
ittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_
1 : AddCommGroup E] …
-/
instance instTransIsLittleOTVSIsLittleOTVS :
    @Trans (α → E) (α → F) (α → G) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans

end Trans

/-
**Asymptotics._root_.Filter.HasBasis.isLittleOTVS_iff** 是 Mathlib 中的一个定理，位于命名空间 
`Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.HasBasis.isLittleOTVS_iff
    {ιE ιF : Sort*} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) :
    f =o[𝕜; l] g ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ ε * egauge 𝕜 (sF j) (g x) := by
  rw [isLittleOTVS_iff]
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε ↦ (h ε hε).mono fun x hx ↦ hx.trans ?_
    simp only
    gcongr
/-
**Asymptotics._root_.Filter.HasBasis.isBigOTVS_iff** 是 Mathlib 中的一个定理，位于命名空间 `As
ymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.HasBasis.isBigOTVS_iff
    {ιE ιF : Sort*} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) :
    f =O[𝕜; l] g ↔ ∀ i, pE i → ∃ j, pF j ∧
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ egauge 𝕜 (sF j) (g x) := by
  rw [isBigOTVS_iff]
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, hV.mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · exact fun s t hsub h ↦ h.mono fun x hx ↦ hx.trans <| egauge_anti 𝕜 hsub (g x)

/-- The definition of `IsBigOTVS` says that
for each neighborhood `U` of the origin in the codomain of `f`,
there exists a neighborhood `V` of the origin in the codomain of `g` such that
`egauge 𝕜 U (f x) ≤ egauge 𝕜 V (g x)` eventually along `l`.

This lemma shows that it suffices to make this inequality work up to a constant multiplier. -/
/-
**Asymptotics.IsBigOTVS.of_egauge_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F}   [C
ontinuousConstSMul 𝕜 F] {ι : Sort u_7} {p : ι → Prop} {U : ι → Set E},   (nhds 0
).HasBasis p U →     (∀ (i : ι), p i → ∃ C, ∃ V ∈ nhds 0, (fun x => egauge 𝕜 (U 
i) (f x)) ≤ᶠ[l] fun x => ↑C * egauge 𝕜 V (g x)) →       f =O[𝕜; l] g
参数：nhds 0；∀ (i : ι), p i → ∃ C, ∃ V ∈ nhds 0, (fun x => egauge 𝕜 (U i) (f x)) ≤ᶠ
[l] fun x => ↑C * egauge 𝕜 V (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isBigOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `NormedField.exists_lt_nnnorm`：exists_lt_nnnorm (r : Real>=0) : exists x 
: α, r < ‖x‖₊
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `egauge_smul_left`：egauge_smul_left (hc : c != 0) (s : Set E) (x : E) : e
gauge 𝕜 (c • s) x = egauge 𝕜 s x / ‖c‖ₑ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
The definition of `IsBigOTVS` says that
for each neighborhood `U` of the origin in the codomain of `f`,
there exists a neighborhood `V` of the origin in the codomain of `g` such that
`egauge 𝕜 U (f x) ≤ egauge 𝕜 V (g x)` eventually along `l`.

This lemma shows that it suffices to make this inequality work up to a constant 
multiplier.
-/
theorem IsBigOTVS.of_egauge_le_mul [ContinuousConstSMul 𝕜 F] {ι} {p : ι → Prop} {U : ι → Set E}
    (hb : (𝓝 0).HasBasis p U)
    (h : ∀ i, p i → ∃ C : ℝ≥0, ∃ V ∈ 𝓝 (0 : F),
      (egauge 𝕜 (U i) <| f ·) ≤ᶠ[l] (fun x ↦ C * egauge 𝕜 V (g x))) :
    f =O[𝕜; l] g := by
  rw [hb.isBigOTVS_iff (basis_sets _)]
  intro i hi
  rcases h i hi with ⟨C, V, hV₀, hV⟩
  rcases NormedField.exists_lt_nnnorm 𝕜 C with ⟨c, hc⟩
  have hc₀ : c ≠ 0 := by rintro rfl; simp at hc
  refine ⟨c⁻¹ • V, (set_smul_mem_nhds_zero_iff <| inv_ne_zero hc₀).mpr hV₀, ?_⟩
  refine hV.trans <| .of_forall fun x ↦ ?_
  simp only
  grw [hc]
  simp [egauge_smul_left, hc₀, enorm_eq_nnnorm, ENNReal.div_eq_inv_mul]
/-
**Asymptotics.isLittleOTVS_iff_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isLittleOTVS_iff_smallSets : f =o[𝕜; l] g ↔ forall U in 𝓝 0, forallᶠ V in 
(𝓝 0).smallSets, forall ε != (0 : Real>=0), forallᶠ x in l, egauge 𝕜 U (f x) <= 
ε * egauge 𝕜 V (g x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isLittleOTVS_iff`：∀ (𝕜 : Type u_1) {α : Type u_2} {E : Type 
u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E]   [inst_2 : T
opologicalSpace F]…
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `egauge_anti`：egauge_anti (h : s subseteq t) (x : E) : egauge 𝕜 t x <= eg
auge 𝕜 s x
-/
theorem isLittleOTVS_iff_smallSets :
    f =o[𝕜; l] g ↔ ∀ U ∈ 𝓝 0, ∀ᶠ V in (𝓝 0).smallSets, ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ ε * egauge 𝕜 V (g x) :=
  (isLittleOTVS_iff ..).trans <| forall₂_congr fun U hU ↦ .symm <|
    eventually_smallSets' fun V₁ V₂ hV hV₂ ε hε ↦ (hV₂ ε hε).mono fun x hx ↦ hx.trans <| by gcongr

alias ⟨IsLittleOTVS.eventually_smallSets, _⟩ := isLittleOTVS_iff_smallSets
/-
**Asymptotics.isBigOTVS_iff_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_iff_smallSets : f =O[𝕜; l] g ↔ forall U in 𝓝 0, forallᶠ V in (𝓝 
0).smallSets, forallᶠ x in l, egauge 𝕜 U (f x) <= egauge 𝕜 V (g x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigOTVS_iff`：∀ (𝕜 : Type u_1) {α : Type u_2} {E : Type u_3
} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E]   [inst_2 : Topo
logicalSpace F]…
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `egauge_anti`：egauge_anti (h : s subseteq t) (x : E) : egauge 𝕜 t x <= eg
auge 𝕜 s x
-/
theorem isBigOTVS_iff_smallSets :
    f =O[𝕜; l] g ↔ ∀ U ∈ 𝓝 0, ∀ᶠ V in (𝓝 0).smallSets,
      ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ egauge 𝕜 V (g x) :=
  (isBigOTVS_iff ..).trans <| forall₂_congr fun U hU ↦ .symm <|
    eventually_smallSets' fun V₁ V₂ hV hV₂ ↦ hV₂.mono fun x hx ↦ hx.trans <| by gcongr

alias ⟨IsBigOTVS.eventually_smallSets, _⟩ := isBigOTVS_iff_smallSets

@[simp]
/-
**Asymptotics.isLittleOTVS_map** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_map {k : β -> α} {l : Filter β} : f =o[𝕜; map k l] g ↔ (f ∘ k
) =o[𝕜; l] (g ∘ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleOTVS_map {k : β → α} {l : Filter β} :
    f =o[𝕜; map k l] g ↔ (f ∘ k) =o[𝕜; l] (g ∘ k) := by
  simp [isLittleOTVS_iff, EventuallyLE]

@[simp]
/-
**Asymptotics.isBigOTVS_map** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_map {k : β -> α} {l : Filter β} : f =O[𝕜; map k l] g ↔ (f ∘ k) =
O[𝕜; l] (g ∘ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOTVS_map {k : β → α} {l : Filter β} :
    f =O[𝕜; map k l] g ↔ (f ∘ k) =O[𝕜; l] (g ∘ k) := by
  simp [isBigOTVS_iff, EventuallyLE]
/-
**Asymptotics.IsLittleOTVS.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO
TVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l₁ l₂ : Filter α} {f : α → E} {g : α → F},
   f =o[𝕜; l₁] g → l₂ ≤ l₁ → f =o[𝕜; l₂] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul`：∀ {𝕜 : Type u_1} {α : 
Type u_2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSp
ace E]   [inst_2 : TopologicalSpace F]…
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
-/
lemma IsLittleOTVS.mono (hf : f =o[𝕜; l₁] g) (h : l₂ ≤ l₁) : f =o[𝕜; l₂] g :=
  ⟨fun U hU ↦ let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, fun ε hε ↦ (hV ε hε).filter_mono h⟩⟩
/-
**Asymptotics.IsBigOTVS.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l₁ l₂ : Filter α} {f : α → E} {g : α → F},
   f =O[𝕜; l₁] g → l₂ ≤ l₁ → f =O[𝕜; l₂] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.exists_eventuallyLE`：∀ {𝕜 : Type u_1} {α : Type u_
2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E] 
  [inst_2 : TopologicalSpace F]…
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
-/
lemma IsBigOTVS.mono (hf : f =O[𝕜; l₁] g) (h : l₂ ≤ l₁) : f =O[𝕜; l₂] g :=
  ⟨fun U hU ↦ let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, hV.filter_mono h⟩⟩
/-
**Asymptotics.IsLittleOTVS.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sLittleOTVS`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_
5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {
g : α → F} {k : β → α}   {lb : Filter β}, f =o[𝕜; l] g → Filter.Tendsto k lb l →
 (f ∘ k) =o[𝕜; lb] (g ∘ k)
参数：f ∘ k；g ∘ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleOTVS_map`：isLittleOTVS_map {k : β -> α} {l : Filter 
β} : f =o[𝕜; map k l] g ↔ (f ∘ k) =o[𝕜; l] (g ∘ k)
· 使用定理 `Asymptotics.IsLittleOTVS.mono`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
-/
lemma IsLittleOTVS.comp_tendsto {k : β → α} {lb : Filter β} (h : f =o[𝕜; l] g)
    (hk : Tendsto k lb l) : (f ∘ k) =o[𝕜; lb] (g ∘ k) :=
  isLittleOTVS_map.mp (h.mono hk)
/-
**Asymptotics.IsBigOTVS.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gOTVS`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_
5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {
g : α → F} {k : β → α}   {lb : Filter β}, f =O[𝕜; l] g → Filter.Tendsto k lb l →
 (f ∘ k) =O[𝕜; lb] (g ∘ k)
参数：f ∘ k；g ∘ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigOTVS_map`：isBigOTVS_map {k : β -> α} {l : Filter β} : f
 =O[𝕜; map k l] g ↔ (f ∘ k) =O[𝕜; l] (g ∘ k)
· 使用定理 `Asymptotics.IsBigOTVS.mono`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_
4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E]
 [inst_2 : Topol…
-/
lemma IsBigOTVS.comp_tendsto {k : β → α} {lb : Filter β} (h : f =O[𝕜; l] g)
    (hk : Tendsto k lb l) : (f ∘ k) =O[𝕜; lb] (g ∘ k) :=
  isBigOTVS_map.mp (h.mono hk)
/-
**Asymptotics.isLittleOTVS_sup** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_sup : f =o[𝕜; l₁ ⊔ l₂] g ↔ f =o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLittleOTVS_sup : f =o[𝕜; l₁ ⊔ l₂] g ↔ f =o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g := by
  simp only [isLittleOTVS_iff_smallSets, ← forall_and, ← eventually_and, eventually_sup]
/-
**Asymptotics.IsLittleOTVS.sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleOT
VS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l₁ l₂ : Filter α} {f : α → E} {g : α → F},
   f =o[𝕜; l₁] g → f =o[𝕜; l₂] g → f =o[𝕜; l₁ ⊔ l₂] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Asymptotics.isLittleOTVS_sup`：isLittleOTVS_sup : f =o[𝕜; l₁ ⊔ l₂] g ↔ f 
=o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g
-/
lemma IsLittleOTVS.sup (hf₁ : f =o[𝕜; l₁] g) (hf₂ : f =o[𝕜; l₂] g) : f =o[𝕜; l₁ ⊔ l₂] g :=
  isLittleOTVS_sup.mpr ⟨hf₁, hf₂⟩
/-
**Asymptotics._root_.ContinuousLinearMap.isBigOTVS_id** 是 Mathlib 中的一个引理，位于命名空间 
`Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.isBigOTVS_id {l : Filter E} (f : E →L[𝕜] F) : f =O[𝕜; l] id :=
  ⟨fun U hU ↦ ⟨f ⁻¹' U, (map_continuous f).tendsto' 0 0 (map_zero f) hU, .of_forall <|
    (mapsTo_preimage f U).egauge_le 𝕜 f⟩⟩
/-
**Asymptotics._root_.ContinuousLinearMap.isBigOTVS_comp** 是 Mathlib 中的一个引理，位于命名空
间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.isBigOTVS_comp (g : E →L[𝕜] F) : (g ∘ f) =O[𝕜; l] f :=
  g.isBigOTVS_id.comp_tendsto tendsto_top
/-
**Asymptotics._root_.ContinuousLinearMap.isBigOTVS_fun_comp** 是 Mathlib 中的一个引理，位
于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.isBigOTVS_fun_comp (g : E →L[𝕜] F) : (g <| f ·) =O[𝕜; l] f :=
  g.isBigOTVS_comp
/-
**Asymptotics._root_.LinearMap.isBigOTVS_rev_comp** 是 Mathlib 中的一个引理，位于命名空间 `Asy
mptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.isBigOTVS_rev_comp (g : E →ₗ[𝕜] F) (hg : comap g (𝓝 0) ≤ 𝓝 0) :
    f =O[𝕜; l] (g ∘ f) := by
  constructor
  intro U hU
  rcases mem_comap.1 (hg hU) with ⟨V, hV, hgV⟩
  use V, hV
  filter_upwards with a
  refine le_egauge_of_forall_ne_zero (mem_of_mem_nhds hV) fun c hc₀ hc ↦ ?_
  apply egauge_le_of_mem_smul
  grw [← hgV, ← (IsUnit.mk0 _ hc₀).preimage_smul_set]
  exact hc
/-
**Asymptotics._root_.ContinuousLinearMap.isThetaTVS_comp** 是 Mathlib 中的一个引理，位于命名
空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.isThetaTVS_comp (g : E →L[𝕜] F) (hg : Topology.IsInducing g) :
    (g ∘ f) =Θ[𝕜; l] f :=
  ⟨g.isBigOTVS_comp, g.isBigOTVS_rev_comp <| by simp [hg.nhds_eq_comap]⟩

@[simp]
/-
**Asymptotics.IsLittleOTVS.zero** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO
TVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] (g : α → F) (l : Filter α), 0 =o[𝕜; l] g
参数：g : α → F；l : Filter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `egauge_zero_right`：egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 
0
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用引理 `egauge_univ`：egauge_univ [(𝓝[!=] (0 : 𝕜)).NeBot] : egauge 𝕜 univ x = 0
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsLittleOTVS.zero (g : α → F) (l : Filter α) : (0 : α → E) =o[𝕜; l] g := by
  refine ⟨fun U hU ↦ ?_⟩
  use univ
  simp [egauge_zero_right _ (Filter.nonempty_of_mem hU), EventuallyLE]
/-
**Asymptotics.isLittleOTVS_insert** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_insert [TopologicalSpace α] {x : α} {s : Set α} (h : f x = 0)
 : f =o[𝕜; 𝓝[insert x s] x] g ↔ f =o[𝕜; (𝓝[s] x)] g
参数：h : f x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用引理 `Asymptotics.isLittleOTVS_sup`：isLittleOTVS_sup : f =o[𝕜; l₁ ⊔ l₂] g ↔ f 
=o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Asymptotics.IsLittleOTVS.congr'`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGro
up E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.zero`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLittleOTVS_insert [TopologicalSpace α] {x : α} {s : Set α} (h : f x = 0) :
    f =o[𝕜; 𝓝[insert x s] x] g ↔ f =o[𝕜; (𝓝[s] x)] g := by
  rw [nhdsWithin_insert, isLittleOTVS_sup, and_iff_right]
  exact .congr' (.zero g _) h.symm .rfl
/-
**Asymptotics.IsLittleOTVS.insert** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittl
eOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f : α → E} {g : α → F} [inst_7 : Topologic
alSpace α]   {x : α} {s : Set α}, f =o[𝕜; nhdsWithin x s] g → f x = 0 → f =o[𝕜; 
nhdsWithin x (insert x s)] g
参数：insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Asymptotics.isLittleOTVS_insert`：isLittleOTVS_insert [TopologicalSpace α
] {x : α} {s : Set α} (h : f x = 0) : f =o[𝕜; 𝓝[insert x s] x] g ↔ f =o[𝕜; (𝓝[s]
 x)] g
-/
lemma IsLittleOTVS.insert [TopologicalSpace α] {x : α} {s : Set α}
    (h : f =o[𝕜; 𝓝[s] x] g) (hf : f x = 0) :
    f =o[𝕜; 𝓝[insert x s] x] g :=
  (isLittleOTVS_insert hf).2 h

@[simp]
/-
**Asymptotics.IsLittleOTVS.bot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleOT
VS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {f : α → E} {g : α → F}, f =o[𝕜; ⊥] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `egauge_univ`：egauge_univ [(𝓝[!=] (0 : 𝕜)).NeBot] : egauge 𝕜 univ x = 0
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsLittleOTVS.bot : f =o[𝕜; ⊥] g :=
  ⟨fun u hU ↦ ⟨univ, by simp [EventuallyLE]⟩⟩
/-
**Asymptotics.IsLittleOTVS.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittl
eOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F]   {k : α → G}, f =o[
𝕜; l] k → g =o[𝕜; l] k → (fun x => (f x, g x)) =o[𝕜; l] k
参数：fun x => (f x, g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isLittleOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Filter.Eventually.exists_mem_of_smallSets`：∀ {α : Type u_1} {l : Filter 
α} {p : Set α → Prop}, (∀ᶠ (t : Set α) in l.smallSets, p t) → ∃ s ∈ l, p s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Asymptotics.IsLittleOTVS.eventually_smallSets`：∀ {α : Type u_1} {𝕜 : Typ
e u_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_
1 : AddCommGroup E] [inst_2 : Topol…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `egauge_prod_mk`：egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F]
 {U : Set E} {V : Set F} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F)
 : e…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsLittleOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G}
    (hf : f =o[𝕜; l] k) (hg : g =o[𝕜; l] k) : (fun x ↦ (f x, g x)) =o[𝕜; l] k := by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isLittleOTVS_iff
    (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, fun ε hε ↦ ?_⟩
  filter_upwards [hWf ε hε, hWg ε hε] with x hfx hgx
  simp [egauge_prod_mk, *]
/-
**Asymptotics.IsLittleOTVS.fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleOT
VS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E × F} {g : α → G}, f =o[𝕜; l] g → (fun x => (f x).1) =o[𝕜; l] g
参数：fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
protected theorem IsLittleOTVS.fst {f : α → E × F} {g : α → G} (h : f =o[𝕜; l] g) :
    (f · |>.fst) =o[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E F |>.isBigOTVS_comp |>.trans_isLittleOTVS h
/-
**Asymptotics.IsLittleOTVS.snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleOT
VS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E × F} {g : α → G}, f =o[𝕜; l] g → (fun x => (f x).2) =o[𝕜; l] g
参数：fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
protected theorem IsLittleOTVS.snd {f : α → E × F} {g : α → G} (h : f =o[𝕜; l] g) :
    (f · |>.snd) =o[𝕜; l] g :=
  ContinuousLinearMap.snd 𝕜 E F |>.isBigOTVS_comp |>.trans_isLittleOTVS h

@[simp]
/-
**Asymptotics.isLittleOTVS_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α 
-> G} : (fun x => (f x, g x)) =o[𝕜; l] k ↔ f =o[𝕜; l] k ∧ g =o[𝕜; l] k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.fst`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 
: AddCommGroup E] …
· 使用定理 `Asymptotics.IsLittleOTVS.snd`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 
: AddCommGroup E] …
· 使用定理 `Asymptotics.IsLittleOTVS.prodMk`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst
_1 : AddCommGroup E] …
-/
theorem isLittleOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G} :
    (fun x ↦ (f x, g x)) =o[𝕜; l] k ↔ f =o[𝕜; l] k ∧ g =o[𝕜; l] k :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.elim .prodMk⟩
/-
**Asymptotics.IsBigOTVS.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`
。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E} {g : α → F} [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F]   {k : α → G}, f =O[
𝕜; l] k → g =O[𝕜; l] k → (fun x => (f x, g x)) =O[𝕜; l] k
参数：fun x => (f x, g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isBigOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Filter.Eventually.exists_mem_of_smallSets`：∀ {α : Type u_1} {l : Filter 
α} {p : Set α → Prop}, (∀ᶠ (t : Set α) in l.smallSets, p t) → ∃ s ∈ l, p s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Asymptotics.IsBigOTVS.eventually_smallSets`：∀ {α : Type u_1} {𝕜 : Type u
_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] [inst_2 : Topol…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `egauge_prod_mk`：egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F]
 {U : Set E} {V : Set F} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F)
 : e…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsBigOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G}
    (hf : f =O[𝕜; l] k) (hg : g =O[𝕜; l] k) : (fun x ↦ (f x, g x)) =O[𝕜; l] k := by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isBigOTVS_iff (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, ?_⟩
  filter_upwards [hWf, hWg] with x hfx hgx
  simp [egauge_prod_mk, *]
/-
**Asymptotics.IsBigOTVS.fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E × F} {g : α → G}, f =O[𝕜; l] g → (fun x => (f x).1) =O[𝕜; l] g
参数：fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
protected theorem IsBigOTVS.fst {f : α → E × F} {g : α → G} (h : f =O[𝕜; l] g) :
    (f · |>.fst) =O[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E F |>.isBigOTVS_comp |>.trans h
/-
**Asymptotics.IsBigOTVS.snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : Topo
logicalSpace E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5
 : TopologicalSpace F] [inst_6 : _root_.Module 𝕜 F] [inst_7 : AddCommGroup G] [i
nst_8 : TopologicalSpace G]   [inst_9 : _root_.Module 𝕜 G] {l : Filter α} {f : α
 → E × F} {g : α → G}, f =O[𝕜; l] g → (fun x => (f x).2) =O[𝕜; l] g
参数：fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
protected theorem IsBigOTVS.snd {f : α → E × F} {g : α → G} (h : f =O[𝕜; l] g) :
    (f · |>.snd) =O[𝕜; l] g :=
  ContinuousLinearMap.snd 𝕜 E F |>.isBigOTVS_comp |>.trans h

@[simp]
/-
**Asymptotics.isBigOTVS_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α -> 
G} : (fun x => (f x, g x)) =O[𝕜; l] k ↔ f =O[𝕜; l] k ∧ g =O[𝕜; l] k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.fst`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : A
ddCommGroup E] …
· 使用定理 `Asymptotics.IsBigOTVS.snd`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : A
ddCommGroup E] …
· 使用定理 `Asymptotics.IsBigOTVS.prodMk`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 
: AddCommGroup E] …
-/
theorem isBigOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G} :
    (fun x ↦ (f x, g x)) =O[𝕜; l] k ↔ f =O[𝕜; l] k ∧ g =O[𝕜; l] k :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.elim .prodMk⟩

@[to_fun]
/-
**Asymptotics.IsLittleOTVS.add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleOT
VS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {f₁ 
f₂ : α → E}   {g : α → F} {l : Filter α}, f₁ =o[𝕜; l] g → f₂ =o[𝕜; l] g → (f₁ + 
f₂) =o[𝕜; l] g
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.prodMk`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst
_1 : AddCommGroup E] …
-/
theorem IsLittleOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α → E} {g : α → F} {l : Filter α}
    (h₁ : f₁ =o[𝕜; l] g) (h₂ : f₂ =o[𝕜; l] g) : (f₁ + f₂) =o[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E |>.isBigOTVS_comp
    |>.trans_isLittleOTVS <| h₁.prodMk h₂

@[to_fun]
/-
**Asymptotics.IsBigOTVS.add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {f₁ 
f₂ : α → E}   {g : α → F} {l : Filter α}, f₁ =O[𝕜; l] g → f₂ =O[𝕜; l] g → (f₁ + 
f₂) =O[𝕜; l] g
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsBigOTVS.prodMk`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 
: AddCommGroup E] …
-/
theorem IsBigOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α → E} {g : α → F} {l : Filter α}
    (h₁ : f₁ =O[𝕜; l] g) (h₂ : f₂ =O[𝕜; l] g) : (f₁ + f₂) =O[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E |>.isBigOTVS_comp
    |>.trans <| h₁.prodMk h₂
/-
**Asymptotics.IsLittleOTVS.triangle** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {f₁ 
f₂ f₃ : α → E}   {g : α → F} {l : Filter α}, (f₁ - f₂) =o[𝕜; l] g → (f₂ - f₃) =o
[𝕜; l] g → (f₁ - f₃) =o[𝕜; l] g
参数：f₁ - f₂；f₂ - f₃；f₁ - f₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `Asymptotics.IsLittleOTVS.add`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup 
E] [inst_2 : Topol…
-/
theorem IsLittleOTVS.triangle [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ f₃ : α → E} {g : α → F} {l : Filter α}
    (h₁ : (f₁ - f₂) =o[𝕜; l] g) (h₂ : (f₂ - f₃) =o[𝕜; l] g) : (f₁ - f₃) =o[𝕜; l] g := by
  simpa using h₁.add h₂
/-
**Asymptotics.IsBigOTVS.triangle** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTV
S`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {f₁ 
f₂ f₃ : α → E}   {g : α → F} {l : Filter α}, (f₁ - f₂) =O[𝕜; l] g → (f₂ - f₃) =O
[𝕜; l] g → (f₁ - f₃) =O[𝕜; l] g
参数：f₁ - f₂；f₂ - f₃；f₁ - f₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `Asymptotics.IsBigOTVS.add`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] 
[inst_2 : Topol…
-/
theorem IsBigOTVS.triangle [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ f₃ : α → E} {g : α → F} {l : Filter α}
    (h₁ : (f₁ - f₂) =O[𝕜; l] g) (h₂ : (f₂ - f₃) =O[𝕜; l] g) : (f₁ - f₃) =O[𝕜; l] g := by
  simpa using h₁.add h₂

section NegLeft

variable [ContinuousNeg E]

/-
**Asymptotics.IsBigOTVS.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTV
S`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F} [Con
tinuousNeg E],   f =O[𝕜; l] g → (-f) =O[𝕜; l] g
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
-/
theorem IsBigOTVS.neg_left (h : f =O[𝕜; l] g) : (-f) =O[𝕜; l] g :=
  .trans ((ContinuousLinearMap.mk (-.id (R := 𝕜)) continuous_neg).isBigOTVS_comp) h

@[simp]
/-
**Asymptotics.isBigOTVS_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_neg_left : (-f) =O[𝕜; l] g ↔ f =O[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Asymptotics.IsBigOTVS.neg_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGrou
p E] [inst_2 : Topol…
-/
theorem isBigOTVS_neg_left : (-f) =O[𝕜; l] g ↔ f =O[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_left, .neg_left⟩

@[simp]
/-
**Asymptotics.isBigOTVS_fun_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_fun_neg_left : (-f ·) =O[𝕜; l] g ↔ f =O[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOTVS_neg_left`：isBigOTVS_neg_left : (-f) =O[𝕜; l] g ↔ f
 =O[𝕜; l] g
-/
theorem isBigOTVS_fun_neg_left : (-f ·) =O[𝕜; l] g ↔ f =O[𝕜; l] g :=
  isBigOTVS_neg_left
/-
**Asymptotics.IsLittleOTVS.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F} [Con
tinuousNeg E],   f =o[𝕜; l] g → (-f) =o[𝕜; l] g
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `Asymptotics.IsBigOTVS.neg_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGrou
p E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsBigOTVS.rfl`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : Topol
ogicalSpace E] …
-/
theorem IsLittleOTVS.neg_left (h : f =o[𝕜; l] g) : (-f) =o[𝕜; l] g :=
  IsBigOTVS.rfl.neg_left.trans_isLittleOTVS h

@[simp]
/-
**Asymptotics.isLittleOTVS_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_neg_left : (-f) =o[𝕜; l] g ↔ f =o[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Asymptotics.IsLittleOTVS.neg_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : 
Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommG
roup E] [inst_2 : Topol…
-/
theorem isLittleOTVS_neg_left : (-f) =o[𝕜; l] g ↔ f =o[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_left, .neg_left⟩

@[simp]
/-
**Asymptotics.isLittleOTVS_fun_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_fun_neg_left : (-f ·) =o[𝕜; l] g ↔ f =o[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleOTVS_neg_left`：isLittleOTVS_neg_left : (-f) =o[𝕜; l]
 g ↔ f =o[𝕜; l] g
-/
theorem isLittleOTVS_fun_neg_left : (-f ·) =o[𝕜; l] g ↔ f =o[𝕜; l] g :=
  isLittleOTVS_neg_left

@[to_fun]
/-
**Asymptotics.IsLittleOTVS.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO
TVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {g : α → F} [ContinuousNeg E
]   {f₁ f₂ : α → E}, (f₁ - f₂) =o[𝕜; l] g → (f₂ - f₁) =o[𝕜; l] g
参数：f₁ - f₂；f₂ - f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Asymptotics.IsLittleOTVS.neg_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : 
Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommG
roup E] [inst_2 : Topol…
-/
protected theorem IsLittleOTVS.symm {f₁ f₂ : α → E} (h : (f₁ - f₂) =o[𝕜; l] g) :
    (f₂ - f₁) =o[𝕜; l] g := by
  simpa using h.neg_left
/-
**Asymptotics.isLittleOTVS_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_comm {f₁ f₂ : α -> E} : (f₁ - f₂) =o[𝕜; l] g ↔ (f₂ - f₁) =o[𝕜
; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.symm`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
-/
theorem isLittleOTVS_comm {f₁ f₂ : α → E} :
    (f₁ - f₂) =o[𝕜; l] g ↔ (f₂ - f₁) =o[𝕜; l] g :=
  ⟨.symm, .symm⟩
/-
**Asymptotics.isLittleOTVS_fun_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_fun_comm {f₁ f₂ : α -> E} : (fun a => f₁ a - f₂ a) =o[𝕜; l] g
 ↔ (fun a => f₂ a - f₁ a) =o[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleOTVS_comm`：isLittleOTVS_comm {f₁ f₂ : α -> E} : (f₁ 
- f₂) =o[𝕜; l] g ↔ (f₂ - f₁) =o[𝕜; l] g
-/
theorem isLittleOTVS_fun_comm {f₁ f₂ : α → E} :
    (fun a ↦ f₁ a - f₂ a) =o[𝕜; l] g ↔ (fun a ↦ f₂ a - f₁ a) =o[𝕜; l] g :=
  isLittleOTVS_comm

@[to_fun]
/-
**Asymptotics.IsBigOTVS.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {g : α → F} [ContinuousNeg E
]   {f₁ f₂ : α → E}, (f₁ - f₂) =O[𝕜; l] g → (f₂ - f₁) =O[𝕜; l] g
参数：f₁ - f₂；f₂ - f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Asymptotics.IsBigOTVS.neg_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGrou
p E] [inst_2 : Topol…
-/
protected theorem IsBigOTVS.symm {f₁ f₂ : α → E} (h : (f₁ - f₂) =O[𝕜; l] g) :
    (f₂ - f₁) =O[𝕜; l] g := by
  simpa using h.neg_left
/-
**Asymptotics.isBigOTVS_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_comm {f₁ f₂ : α -> E} : (f₁ - f₂) =O[𝕜; l] g ↔ (f₂ - f₁) =O[𝕜; l
] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.symm`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_
4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E]
 [inst_2 : Topol…
-/
theorem isBigOTVS_comm {f₁ f₂ : α → E} :
    (f₁ - f₂) =O[𝕜; l] g ↔ (f₂ - f₁) =O[𝕜; l] g :=
  ⟨.symm, .symm⟩
/-
**Asymptotics.isBigOTVS_fun_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_fun_comm {f₁ f₂ : α -> E} : (fun a => f₁ a - f₂ a) =O[𝕜; l] g ↔ 
(fun a => f₂ a - f₁ a) =O[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOTVS_comm`：isBigOTVS_comm {f₁ f₂ : α -> E} : (f₁ - f₂) 
=O[𝕜; l] g ↔ (f₂ - f₁) =O[𝕜; l] g
-/
theorem isBigOTVS_fun_comm {f₁ f₂ : α → E} :
    (fun a ↦ f₁ a - f₂ a) =O[𝕜; l] g ↔ (fun a ↦ f₂ a - f₁ a) =O[𝕜; l] g :=
  isBigOTVS_comm

end NegLeft

section NegRight

variable [ContinuousNeg F]

/-
**Asymptotics.IsBigOTVS.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOT
VS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F} [Con
tinuousNeg F],   f =O[𝕜; l] g → f =O[𝕜; l] (-g)
参数：-g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Asymptotics.IsBigOTVS.neg_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Typ
e u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGrou
p E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsBigOTVS.refl`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_
4} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : Topo
logicalSpace E] …
-/
theorem IsBigOTVS.neg_right (h : f =O[𝕜; l] g) : f =O[𝕜; l] (-g) :=
  h.trans <| by simpa using (IsBigOTVS.refl (-g) l).neg_left

@[simp]
/-
**Asymptotics.isBigOTVS_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_neg_right : f =O[𝕜; l] (-g) ↔ f =O[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Asymptotics.IsBigOTVS.neg_right`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGro
up E] [inst_2 : Topol…
-/
theorem isBigOTVS_neg_right : f =O[𝕜; l] (-g) ↔ f =O[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_right, .neg_right⟩

@[simp]
/-
**Asymptotics.isBigOTVS_fun_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_fun_neg_right : f =O[𝕜; l] (-g ·) ↔ f =O[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOTVS_neg_right`：isBigOTVS_neg_right : f =O[𝕜; l] (-g) ↔
 f =O[𝕜; l] g
-/
theorem isBigOTVS_fun_neg_right : f =O[𝕜; l] (-g ·) ↔ f =O[𝕜; l] g :=
  isBigOTVS_neg_right
/-
**Asymptotics.IsLittleOTVS.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F} [Con
tinuousNeg F],   f =o[𝕜; l] g → f =o[𝕜; l] (-g)
参数：-g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.trans_isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `Asymptotics.IsBigOTVS.neg_right`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGro
up E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsBigOTVS.rfl`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : Topol
ogicalSpace E] …
-/
theorem IsLittleOTVS.neg_right (h : f =o[𝕜; l] g) : f =o[𝕜; l] (-g) :=
  h.trans_isBigOTVS (.neg_right .rfl)

@[simp]
/-
**Asymptotics.isLittleOTVS_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_neg_right : f =o[𝕜; l] (-g) ↔ f =o[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Asymptotics.IsLittleOTVS.neg_right`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
theorem isLittleOTVS_neg_right : f =o[𝕜; l] (-g) ↔ f =o[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_right, .neg_right⟩

@[simp]
/-
**Asymptotics.isLittleOTVS_fun_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isLittleOTVS_fun_neg_right : f =o[𝕜; l] (-g ·) ↔ f =o[𝕜; l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleOTVS_neg_right`：isLittleOTVS_neg_right : f =o[𝕜; l] 
(-g) ↔ f =o[𝕜; l] g
-/
theorem isLittleOTVS_fun_neg_right : f =o[𝕜; l] (-g ·) ↔ f =o[𝕜; l] g :=
  isLittleOTVS_neg_right

end NegRight

/-
**Asymptotics.IsLittleOTVS.pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleOTV
S`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u_5} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : TopologicalSpace F] [inst_3 : _roo
t_.Module 𝕜 F] {l : Filter α} {g : α → F} {ι : Type u_7}   {E : ι → Type u_8} [i
nst_4 : (i : ι) → AddCommGroup (E i)] [inst_5 : (i : ι) → _root_.Module 𝕜 (E i)]
   [inst_6 : (i : ι) → TopologicalSpace (E i)] [∀ (i : ι), ContinuousSMul 𝕜 (E i
)] {f : (i : ι) → α → E i},   (∀ (i : ι), f i =o[𝕜; l] g) → (fun x i => f i x) =
o[𝕜; l] g
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；∀ (i : ι), f i =o[𝕜; l] g；fun x
 i => f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_pi`：hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i ->
 Set (α i)} {p : forall i, ι' i -> Prop} (h : forall i, (f i).HasBasis (p i) (s 
i)) : (p…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.isLittleOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.zero_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zero 
(M i)], 0 = fun x => 0
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsLittleOTVS.eventually_smallSets`：∀ {α : Type u_1} {𝕜 : Typ
e u_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_
1 : AddCommGroup E] [inst_2 : Topol…
· 使用定理 `Filter.Eventually.exists_mem_of_smallSets`：∀ {α : Type u_1} {l : Filter 
α} {p : Set α → Prop}, (∀ᶠ (t : Set α) in l.smallSets, p t) → ∃ s ∈ l, p s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `egauge_pi`：egauge_pi [(𝓝[!=] (0 : 𝕜)).NeBot] {I : Set ι} {U : forall i, 
Set (E i)} (hI : I.Finite) (hU : forall i in I, Balanced 𝕜 (U i)) (x : forall i…
-/
protected theorem IsLittleOTVS.pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : ∀ i, α → E i} (h : ∀ i, f i =o[𝕜; l] g) : (fun x i ↦ f i x) =o[𝕜; l] g := by
  have := hasBasis_pi fun i ↦ nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi, ← Pi.zero_def] at this
  simp only [this.isLittleOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi ↦ (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε ↦ ?_⟩
  refine (hIf.eventually_all.mpr (hV · · ε hε)).mono fun x hx ↦ ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]
/-
**Asymptotics.IsLittleOTVS.proj** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO
TVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u_5} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : TopologicalSpace F] [inst_3 : _roo
t_.Module 𝕜 F] {l : Filter α} {g : α → F} {ι : Type u_7}   {E : ι → Type u_8} [i
nst_4 : (i : ι) → AddCommGroup (E i)] [inst_5 : (i : ι) → _root_.Module 𝕜 (E i)]
   [inst_6 : (i : ι) → TopologicalSpace (E i)] {f : α → (i : ι) → E i},   f =o[𝕜
; l] g → ∀ (i : ι), (fun x => f x i) =o[𝕜; l] g
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；i : ι；fun x => f x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_fun_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} 
{E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Add
CommGroup E] [inst_2 : Topol…
-/
theorem IsLittleOTVS.proj {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] {f : α → ∀ i, E i}
    (h : f =o[𝕜; l] g) (i : ι) : (f · i) =o[𝕜; l] g :=
  ContinuousLinearMap.proj i |>.isBigOTVS_fun_comp |>.trans_isLittleOTVS h
/-
**Asymptotics.isLittleOTVS_pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)
] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] [forall i, Conti
nuousSMul 𝕜 (E i)] {f : α -> forall i, E i} : f =o[𝕜; l] g ↔ forall i, (f · i) =
o[𝕜; l] g
参数：E i；E i；E i；E i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.proj`：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type
 u_5} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : T
opologicalSpace F] …
· 使用定理 `Asymptotics.IsLittleOTVS.pi`：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u
_5} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : Top
ologicalSpace F] …
-/
theorem isLittleOTVS_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : α → ∀ i, E i} : f =o[𝕜; l] g ↔ ∀ i, (f · i) =o[𝕜; l] g :=
  ⟨.proj, .pi⟩
/-
**Asymptotics.IsBigOTVS.pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u_5} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : TopologicalSpace F] [inst_3 : _roo
t_.Module 𝕜 F] {l : Filter α} {g : α → F} {ι : Type u_7}   {E : ι → Type u_8} [i
nst_4 : (i : ι) → AddCommGroup (E i)] [inst_5 : (i : ι) → _root_.Module 𝕜 (E i)]
   [inst_6 : (i : ι) → TopologicalSpace (E i)] [∀ (i : ι), ContinuousSMul 𝕜 (E i
)] {f : (i : ι) → α → E i},   (∀ (i : ι), f i =O[𝕜; l] g) → (fun x i => f i x) =
O[𝕜; l] g
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；∀ (i : ι), f i =O[𝕜; l] g；fun x
 i => f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_pi`：hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i ->
 Set (α i)} {p : forall i, ι' i -> Prop} (h : forall i, (f i).HasBasis (p i) (s 
i)) : (p…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.isBigOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.zero_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zero 
(M i)], 0 = fun x => 0
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsBigOTVS.eventually_smallSets`：∀ {α : Type u_1} {𝕜 : Type u
_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] [inst_2 : Topol…
· 使用定理 `Filter.Eventually.exists_mem_of_smallSets`：∀ {α : Type u_1} {l : Filter 
α} {p : Set α → Prop}, (∀ᶠ (t : Set α) in l.smallSets, p t) → ∃ s ∈ l, p s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `egauge_pi`：egauge_pi [(𝓝[!=] (0 : 𝕜)).NeBot] {I : Set ι} {U : forall i, 
Set (E i)} (hI : I.Finite) (hU : forall i in I, Balanced 𝕜 (U i)) (x : forall i…
-/
protected theorem IsBigOTVS.pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : ∀ i, α → E i} (h : ∀ i, f i =O[𝕜; l] g) : (fun x i ↦ f i x) =O[𝕜; l] g := by
  have := hasBasis_pi fun i ↦ nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi, ← Pi.zero_def] at this
  simp only [this.isBigOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi ↦ (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  use V, hV₀
  refine (hIf.eventually_all.mpr hV).mono fun x hx ↦ ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]
/-
**Asymptotics.IsBigOTVS.proj** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u_5} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : TopologicalSpace F] [inst_3 : _roo
t_.Module 𝕜 F] {l : Filter α} {g : α → F} {ι : Type u_7}   {E : ι → Type u_8} [i
nst_4 : (i : ι) → AddCommGroup (E i)] [inst_5 : (i : ι) → _root_.Module 𝕜 (E i)]
   [inst_6 : (i : ι) → TopologicalSpace (E i)] {f : α → (i : ι) → E i},   f =O[𝕜
; l] g → ∀ (i : ι), (fun x => f x i) =O[𝕜; l] g
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；i : ι；fun x => f x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.trans`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 AddCommGroup E] …
· 使用定理 `ContinuousLinearMap.isBigOTVS_fun_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} 
{E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Add
CommGroup E] [inst_2 : Topol…
-/
theorem IsBigOTVS.proj {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] {f : α → ∀ i, E i}
    (h : f =O[𝕜; l] g) (i : ι) : (f · i) =O[𝕜; l] g :=
  ContinuousLinearMap.proj i |>.isBigOTVS_fun_comp |>.trans h
/-
**Asymptotics.isBigOTVS_pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)] [
forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] [forall i, Continuo
usSMul 𝕜 (E i)] {f : α -> forall i, E i} : f =O[𝕜; l] g ↔ forall i, (f · i) =O[𝕜
; l] g
参数：E i；E i；E i；E i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOTVS.proj`：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u_
5} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : Topo
logicalSpace F] …
· 使用定理 `Asymptotics.IsBigOTVS.pi`：∀ {α : Type u_1} {𝕜 : Type u_3} {F : Type u_5}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup F]   [inst_2 : Topolo
gicalSpace F] …
-/
theorem isBigOTVS_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : α → ∀ i, E i} : f =O[𝕜; l] g ↔ ∀ i, (f · i) =O[𝕜; l] g :=
  ⟨.proj, .pi⟩
/-
**Asymptotics.IsLittleOTVS.smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : TopologicalSpace E]
 [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommGroup F]   [inst_5 : TopologicalS
pace F] [inst_6 : _root_.Module 𝕜 F] {l : Filter α} {f : α → E} {g : α → F},   f
 =o[𝕜; l] g → ∀ (c : α → 𝕜), (fun x => c x • f x) =o[𝕜; l] fun x => c x • g x
参数：c : α → 𝕜；fun x => c x • f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `Mathlib.Tactic.Peel.and_imp_left_of_imp_imp`：and_imp_left_of_imp_imp {p 
q r : Prop} (h : r -> p -> q) : r ∧ p -> r ∧ q
· 使用定理 `Mathlib.Tactic.Peel.eventually_imp`：eventually_imp {α : Type*} {p q : α 
-> Prop} {f : Filter α} (hq : forall (x : α), p x -> q x) (hp : forallᶠ (x : α) 
in f, p x) : forallᶠ (x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `egauge_smul_right`：egauge_smul_right (h : c = 0 -> s.Nonempty) (x : E) :
 egauge 𝕜 s (c • x) = ‖c‖ₑ * egauge 𝕜 s x
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected lemma IsLittleOTVS.smul_left (h : f =o[𝕜; l] g) (c : α → 𝕜) :
    (fun x ↦ c x • f x) =o[𝕜; l] (fun x ↦ c x • g x) := by
  simp only [isLittleOTVS_iff] at *
  peel h with U hU V hV ε hε x hx
  simp only at *
  rw [egauge_smul_right, egauge_smul_right, mul_left_comm]
  · gcongr
  all_goals exact fun _ ↦ Filter.nonempty_of_mem ‹_›
/-
**Asymptotics.isLittleOTVS_one** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleOTVS_one [ContinuousSMul 𝕜 E] : f =o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto 
f l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.HasBasis.isLittleOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `Filter.Eventually.exists_gt`：∀ {α : Type u_1} [inst : TopologicalSpace α
] [inst_1 : Preorder α] {a : α} [(nhdsWithin a (Set.Ioi a)).NeBot]   {p : α → Pr
op}, (∀ᶠ (x : α) …
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Filter.Tendsto.eventually_lt_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ENNReal.continuous_div_const`：∀ (c : ENNReal), c ≠ 0 → Continuous fun x 
=> x / c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 68 条，此处仅展示前 30 条）
-/
lemma isLittleOTVS_one [ContinuousSMul 𝕜 E] : f =o[𝕜; l] (1 : α → 𝕜) ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro hf
    rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at hf
    rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
    rintro U ⟨hU, hUb⟩
    rcases hf U hU with ⟨r, hr₀, hr⟩
    lift r to ℝ≥0 using hr₀.le
    norm_cast at hr₀
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    obtain ⟨ε, hε₀, hε⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ (ε * ‖c‖₊ / r : ℝ≥0∞) < 1 := by
      apply Eventually.exists_gt
      refine Continuous.tendsto' ?_ _ _ (by simp) |>.eventually_lt_const zero_lt_one
      fun_prop (disch := intros; first | apply ENNReal.coe_ne_top | positivity)
    filter_upwards [hr ε hε₀.ne'] with x hx
    refine mem_of_egauge_lt_one hUb (hx.trans_lt ?_)
    calc
      (ε : ℝ≥0∞) * egauge 𝕜 (ball (0 : 𝕜) r) 1 ≤ (ε * ‖c‖₊ / r : ℝ≥0∞) := by
        rw [mul_div_assoc]
        gcongr
        simpa using! egauge_ball_le_of_one_lt_norm (r := r) (x := (1 : 𝕜)) hc (by simp)
      _ < 1 := ‹_›
  · simp only [isLittleOTVS_iff]
    intro hf U hU
    refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε ↦ ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε⟩
    replace hc₀ : c ≠ 0 := by simpa using! hc₀
    filter_upwards [hf ((set_smul_mem_nhds_zero_iff hc₀).2 hU)] with a ha
    calc
      egauge 𝕜 U (f a) ≤ ‖c‖₊ := egauge_le_of_mem_smul ha
      _ ≤ ε := mod_cast hcε.le
      _ ≤ ε * egauge 𝕜 (ball (0 : 𝕜) 1) 1 := by
        apply le_mul_of_one_le_right'
        simpa using! le_egauge_ball_one 𝕜 (1 : 𝕜)
/-
**Asymptotics.IsLittleOTVS.tendsto_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsLittleOTVS`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : _roo
t_.Module 𝕜 E] {l : Filter α} [ContinuousSMul 𝕜 E] {f : α → 𝕜}   {g : α → E}, g 
=o[𝕜; l] f → Filter.Tendsto (fun x => (f x)⁻¹ • g x) l (nhds 0)
参数：fun x => (f x)⁻¹ • g x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Asymptotics.isLittleOTVS_one`：isLittleOTVS_one [ContinuousSMul 𝕜 E] : f 
=o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto f l (𝓝 0)
· 使用定理 `Asymptotics.isLittleOTVS_iff`：∀ (𝕜 : Type u_1) {α : Type u_2} {E : Type 
u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSpace E]   [inst_2 : T
opologicalSpace F]…
· 使用定理 `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul`：∀ {𝕜 : Type u_1} {α : 
Type u_2} {E : Type u_3} {F : Type u_4} [inst : ENorm 𝕜] [inst_1 : TopologicalSp
ace E]   [inst_2 : TopologicalSpace F]…
· 使用定理 `Asymptotics.IsLittleOTVS.smul_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `egauge_zero_right`：egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 
0
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsLittleOTVS.tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α → 𝕜} {g : α → E}
    (h : g =o[𝕜; l] f) : Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  rw [← isLittleOTVS_one (𝕜 := 𝕜), isLittleOTVS_iff]
  intro U hU
  rcases (h.smul_left f⁻¹).1 U hU with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x hx ↦ hx.trans ?_⟩
  by_cases hx₀ : f x = 0 <;> simp [hx₀, egauge_zero_right _ (Filter.nonempty_of_mem hV₀)]
/-
**Asymptotics.isLittleOTVS_iff_tendsto_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 `Asymp
totics`。
形式化陈述：isLittleOTVS_iff_tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α -> 𝕜} {g : α
 -> E} {l : Filter α} (h₀ : forallᶠ x in l, f x = 0 -> g x = 0) : g =o[𝕜; l] f ↔
 Tendsto (fun x => (f x)⁻¹ • g x) l (𝓝 0)
参数：h₀ : forallᶠ x in l, f x = 0 -> g x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.tendsto_inv_smul`：∀ {α : Type u_1} {𝕜 : Type u_
3} {E : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]  
 [inst_2 : TopologicalSpace E] …
· 使用定理 `Asymptotics.IsLittleOTVS.congr'`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Ty
pe u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGro
up E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.smul_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Asymptotics.isLittleOTVS_one`：isLittleOTVS_one [ContinuousSMul 𝕜 E] : f 
=o[𝕜; l] (1 : α -> 𝕜) ↔ Tendsto f l (𝓝 0)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma isLittleOTVS_iff_tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α → 𝕜} {g : α → E} {l : Filter α}
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    g =o[𝕜; l] f ↔ Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h ↦ ?_⟩
  refine (((isLittleOTVS_one (𝕜 := 𝕜)).mpr h).smul_left f).congr' (h₀.mono fun x hx ↦ ?_) (by simp)
  by_cases h : f x = 0 <;> simp [h, hx]

variable (𝕜) in
/-- If `f` converges along `l` to a finite limit `x`, then `f =O[𝕜, l] 1`. -/
/-
**Asymptotics.Filter.Tendsto.isBigOTVS_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_3) {E : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : _roo
t_.Module 𝕜 E] {l : Filter α} {f : α → E} [ContinuousAdd E]   [ContinuousSMul 𝕜 
E] {x : E}, Filter.Tendsto f l (nhds x) → f =O[𝕜; l] fun x => 1
参数：𝕜 : Type u_3；nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.HasBasis.isBigOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `Filter.HasBasis.add_self`：∀ {ι : Type u_1} {M : Type u_3} [inst : Topolo
gicalSpace M] [inst_1 : AddZeroClass M] [ContinuousAdd M] {p : ι → Prop}   {s : 
ι → Set M}, (n…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Filter.Eventually.exists_gt`：∀ {α : Type u_1} [inst : TopologicalSpace α
] [inst_1 : Preorder α] {a : α} [(nhdsWithin a (Set.Ioi a)).NeBot]   {p : α → Pr
op}, (∀ᶠ (x : α) …
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_le_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x ≤ b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Tendsto.eventually_le_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NontriviallyNormedField.cobounded_neBot`：∀ (𝕜 : Type u_1) [inst : Nontri
viallyNormedField 𝕜], (Bornology.cobounded 𝕜).NeBot
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` converges along `l` to a finite limit `x`, then `f =O[𝕜, l] 1`.
-/
lemma Filter.Tendsto.isBigOTVS_one [ContinuousAdd E] [ContinuousSMul 𝕜 E] {x : E}
    (h : Tendsto f l (𝓝 x)) : f =O[𝕜; l] (fun _ ↦ 1 : α → 𝕜) := by
  replace h : Tendsto (f · - x) l (𝓝 0) := by
    simpa [sub_eq_add_neg] using h.add (tendsto_const_nhds (x := -x))
  rw [(nhds_basis_balanced 𝕜 E).add_self.isBigOTVS_iff nhds_basis_ball]
  rintro U ⟨hU₀, hUb⟩
  obtain ⟨r, hr₀, hr₁, hr⟩ : ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ (r : ℝ≥0∞) ≤ (egauge 𝕜 U x)⁻¹ := by
    apply Eventually.exists_gt
    refine .and (eventually_le_nhds one_pos) ?_
    refine (ENNReal.tendsto_coe.mpr tendsto_id).eventually_le_const ?_
    suffices ∃ c : 𝕜, x ∈ c • U by simpa [egauge_eq_top]
    simpa using (absorbent_nhds_zero (𝕜 := 𝕜) hU₀ x).exists
  use r, by positivity
  filter_upwards [h.eventually_mem hU₀] with a ha
  calc
    egauge 𝕜 (U + U) (f a) ≤ max (egauge 𝕜 U (f a - x)) (egauge 𝕜 U x) := by
      simpa using egauge_add_add_le hUb hUb (f a - x) x
    _ ≤ (r : ℝ≥0∞)⁻¹ := by
      apply max_le
      · refine (egauge_le_one _ ha).trans ?_
        simp [hr₁]
      · rwa [ENNReal.le_inv_iff_le_inv]
    _ ≤ egauge 𝕜 (ball (0 : 𝕜) _) 1 := by simpa using div_le_egauge_ball 𝕜 r (1 : 𝕜)

end TopologicalSpace

section NormedSpace

variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
variable {f : α → E} {g : α → F} {l : Filter α}

/-
**Asymptotics.isLittleOTVS_iff_isLittleO** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`
。
形式化陈述：isLittleOTVS_iff_isLittleO : f =o[𝕜; l] g ↔ f =o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isLittleOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `div_le_egauge_ball`：div_le_egauge_ball (r : Real>=0) (x : E) : ‖x‖ₑ / r 
<= egauge 𝕜 (ball 0 r) x
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用引理 `ENNReal.coe_div_le`：coe_div_le : ↑(p / r) <= (p / r : Real>=0∞)
· 使用引理 `egauge_ball_le_of_one_lt_norm`：egauge_ball_le_of_one_lt_norm (hc : 1 < ‖
c‖) (h₀ : r != 0 ∨ ‖x‖ != 0) : egauge 𝕜 (ball 0 r) x <= ‖c‖ₑ * ‖x‖ₑ / r
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
（共 69 条，此处仅展示前 30 条）
-/
lemma isLittleOTVS_iff_isLittleO : f =o[𝕜; l] g ↔ f =o[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ⟨1, one_pos, fun δ hδ ↦ ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to ℝ≥0 using hε.le; lift δ to ℝ≥0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : ℝ≥0∞) ≤ ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff₀' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : ℝ≥0∞) ≤ egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ ≤ ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ ≤ (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ ≤ 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ ≤ ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to ℝ≥0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) ≤ ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ ≤ ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ ≤ 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ ≤ δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one

alias ⟨isLittleOTVS.isLittleO, IsLittleO.isLittleOTVS⟩ := isLittleOTVS_iff_isLittleO
/-
**Asymptotics.isBigOTVS_iff_isBigO** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOTVS_iff_isBigO : f =O[𝕜; l] g ↔ f =O[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isBigOTVS_iff`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_egauge_ball_one`：le_egauge_ball_one (x : E) : ‖x‖ₑ <= egauge 𝕜 (ball 
0 1) x
· 使用引理 `egauge_ball_le_of_one_lt_norm`：egauge_ball_le_of_one_lt_norm (hc : 1 < ‖
c‖) (h₀ : r != 0 ∨ ‖x‖ != 0) : egauge 𝕜 (ball 0 r) x <= ‖c‖ₑ * ‖x‖ₑ / r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.mul_div_right_comm`：∀ {a b c : ENNReal}, a * b / c = a / c * b
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.isBigO_iff'`：isBigO_iff' {g : α -> E'''} : f =O[l] g ↔ exist
s c > 0, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 55 条，此处仅展示前 30 条）
-/
lemma isBigOTVS_iff_isBigO : f =O[𝕜; l] g ↔ f =O[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  constructor
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff]
    intro h
    rcases h 1 one_pos with ⟨r, hr₀, hr⟩
    lift r to ℝ≥0 using hr₀.le
    norm_cast at hr₀
    refine ⟨(‖c‖₊ / r : ℝ≥0), hr.mono fun x hx ↦ ?_⟩
    suffices ‖f x‖ₑ ≤ (‖c‖₊ / r : ℝ≥0) * ‖g x‖ₑ by
      simp only [enorm_eq_nnnorm, ← coe_nnnorm] at this ⊢
      exact mod_cast this
    calc
      ‖f x‖ₑ ≤ egauge 𝕜 (ball 0 1) (f x) := le_egauge_ball_one ..
      _ ≤ egauge 𝕜 (ball 0 r) (g x) := hx
      _ ≤ ‖c‖ₑ * ‖g x‖ₑ / ↑r :=
        egauge_ball_le_of_one_lt_norm hc <| .inl hr₀.ne'
      _ = (‖c‖₊ / r : ℝ≥0) * ‖g x‖ₑ := by
        simp [hr₀.ne', ENNReal.mul_div_right_comm, enorm_eq_nnnorm]
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff']
    have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
    rintro ⟨C, hC₀, hC⟩ r hr₀
    lift C to ℝ≥0 using hC₀.le; norm_cast at hC₀
    lift r to ℝ≥0 using hr₀.le; norm_cast at hr₀
    refine ⟨r / (C * ‖c‖₊), by positivity, hC.mono fun x hx ↦ ?_⟩
    calc
      egauge 𝕜 (ball 0 r) (f x) ≤ ‖c‖ₑ * ‖f x‖ₑ / r :=
        egauge_ball_le_of_one_lt_norm hc <| .inl hr₀.ne'
      _ ≤ ‖c‖ₑ * (C * ‖g x‖ₑ) / r := by
        gcongr
        simp only [enorm_eq_nnnorm, ← coe_nnnorm] at hx ⊢
        exact mod_cast hx
      _ = ‖g x‖ₑ / (r / (C * ‖c‖₊) : ℝ≥0) := by
        simp_all [pos_iff_ne_zero, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        ac_rfl
      _ ≤ _ := div_le_egauge_ball _ _ _

alias ⟨IsBigOTVS.isBigO, IsBigO.isBigOTVS⟩ := isBigOTVS_iff_isBigO

@[deprecated (since := "2026-02-03")]
alias isBigOTVS.isBigO := IsBigOTVS.isBigO
/-
**Asymptotics.isThetaTVS_iff_isTheta** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isThetaTVS_iff_isTheta : f =Θ[𝕜; l] g ↔ f =Θ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用引理 `Asymptotics.isBigOTVS_iff_isBigO`：isBigOTVS_iff_isBigO : f =O[𝕜; l] g ↔ 
f =O[l] g
-/
lemma isThetaTVS_iff_isTheta : f =Θ[𝕜; l] g ↔ f =Θ[l] g :=
  .and isBigOTVS_iff_isBigO isBigOTVS_iff_isBigO

alias ⟨IsThetaTVS.isTheta, IsTheta.isThetaTVS⟩ := isThetaTVS_iff_isTheta

end NormedSpace

end Asymptotics

