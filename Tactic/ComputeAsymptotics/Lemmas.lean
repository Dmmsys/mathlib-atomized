/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Conversion lemmas

The main procedure of the `compute_asymptotics` tactic is able to compute limits of functions at
`atTop` filter. This file contains lemmas we use to reduce other asymptotic goals to
the case `Tendsto f atTop l`.

## Main theorems

This file contains the following lemmas:
* `tendsto_nhdsGT_of_tendsto_atTop` for `Tendsto f (𝓝[>] c) l`
* `tendsto_nhdsLT_of_tendsto_atTop` for `Tendsto f (𝓝[<] c) l`
* `tendsto_nhdsNE_of_tendsto_atTop` for `Tendsto f (𝓝[≠] c) l`
* `isBigO_of_div_tendsto_atTop` and `isBigO_of_div_tendsto_atBot` for `f =O[l] g`

We also use lemmas from other files:
* `tendsto_comp_neg_atTop_iff` for `Tendsto f atBot l`
* `IsLittleO.of_tendsto_div_atBot` and `IsLittleO.of_tendsto_div_atTop` for `f =o[l] g`
* `isEquivalent_of_tendsto_one` for `f ∼ g`
-/

public section

open Filter Topology Asymptotics

namespace Tactic.ComputeAsymptotics

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {l : Filter α} (f : 𝕜 → α) (c : 𝕜)

/-
**Tactic.ComputeAsymptotics.tendsto_nhdsGT_of_tendsto_atTop** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics`。
形式化陈述：tendsto_nhdsGT_of_tendsto_atTop (h : Tendsto (fun x => f (c + x⁻¹)) atTop 
l) : Tendsto f (𝓝[>] c) l
参数：h : Tendsto (fun x => f (c + x⁻¹)) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `inv_atTop₀`：inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0
· 使用定理 `Filter.map_add_left_nhdsGT`：∀ {H : Type x} [inst : TopologicalSpace H] [
inst_1 : AddCommGroup H] [inst_2 : PartialOrder H] [IsOrderedAddMonoid H]   [Con
tinuousAdd H] {c…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
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
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem tendsto_nhdsGT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  simpa [← Function.comp_def, Tendsto, ← Filter.map_map] using h
/-
**Tactic.ComputeAsymptotics.tendsto_nhdsLT_of_tendsto_atTop** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics`。
形式化陈述：tendsto_nhdsLT_of_tendsto_atTop (h : Tendsto (fun x => f (c - x⁻¹)) atTop 
l) : Tendsto f (𝓝[<] c) l
参数：h : Tendsto (fun x => f (c - x⁻¹)) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `inv_atTop₀`：inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0
· 使用定理 `Filter.neg_nhdsGT`：∀ {H : Type x} [inst : TopologicalSpace H] [inst_1 : 
AddCommGroup H] [inst_2 : PartialOrder H] [IsOrderedAddMonoid H]   [ContinuousNe
g H] {a…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Filter.map_add_left_nhdsLT`：∀ {H : Type x} [inst : TopologicalSpace H] [
inst_1 : AddCommGroup H] [inst_2 : PartialOrder H] [IsOrderedAddMonoid H]   [Con
tinuousAdd H] {c…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tendsto_nhdsLT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] c) l := by
  convert_to Tendsto (f ∘ (fun x ↦ c + x) ∘ Neg.neg ∘ Inv.inv) atTop l at h
  · ext
    simp [AddGroupWithOne.sub_eq_add_neg]
  simpa [Tendsto, ← Filter.map_map] using h
/-
**Tactic.ComputeAsymptotics.tendsto_nhdsNE_of_tendsto_atTop** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics`。
形式化陈述：tendsto_nhdsNE_of_tendsto_atTop (h_neg : Tendsto (fun x => f (c - x⁻¹)) at
Top l) (h_pos : Tendsto (fun x => f (c + x⁻¹)) atTop l) : Tendsto f (𝓝[!=] c) l
参数：h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop l；h_pos : Tendsto (fun x => f (c
 + x⁻¹)) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_sup`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {m : 
α → β},   Filter.map m (f₁ ⊔ f₂) = Filter.map m f₁ ⊔ Filter.map m f₂
· 使用定理 `Tactic.ComputeAsymptotics.tendsto_nhdsLT_of_tendsto_atTop`：tendsto_nhdsL
T_of_tendsto_atTop (h : Tendsto (fun x => f (c - x⁻¹)) atTop l) : Tendsto f (𝓝[<
] c) l
· 使用定理 `Tactic.ComputeAsymptotics.tendsto_nhdsGT_of_tendsto_atTop`：tendsto_nhdsG
T_of_tendsto_atTop (h : Tendsto (fun x => f (c + x⁻¹)) atTop l) : Tendsto f (𝓝[>
] c) l
-/
theorem tendsto_nhdsNE_of_tendsto_atTop (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l)
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] c) l := by
  simpa [Tendsto, ← nhdsLT_sup_nhdsGT] using
    ⟨tendsto_nhdsLT_of_tendsto_atTop _ _ h_neg, tendsto_nhdsGT_of_tendsto_atTop _ _ h_pos⟩
/-
**Tactic.ComputeAsymptotics.tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics`。
形式化陈述：tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq [TopologicalSpace α] {a b : α} 
(h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop (𝓝 a)) (h_pos : Tendsto (fun x => 
f (c + x⁻¹)) atTop (𝓝 b)) (h_eq : a = b) : Tendsto f (𝓝[!=] c) (𝓝 a)
参数：h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop (𝓝 a)；h_pos : Tendsto (fun x => 
f (c + x⁻¹)) atTop (𝓝 b)；h_eq : a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.tendsto_nhdsNE_of_tendsto_atTop`：tendsto_nhdsN
E_of_tendsto_atTop (h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop l) (h_pos : Ten
dsto (fun x => f (c + x⁻¹)) atTop l) : Tendsto …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq [TopologicalSpace α] {a b : α}
    (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop (𝓝 a))
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop (𝓝 b)) (h_eq : a = b) :
    Tendsto f (𝓝[≠] c) (𝓝 a) := by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert! h_pos
/-
**Tactic.ComputeAsymptotics.isBigOWith_of_tendsto_top** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics`。
形式化陈述：isBigOWith_of_tendsto_top {C : Real} {f g : Real -> Real} {l : Filter Real
} (h : Tendsto (fun x => g x / f x) l atTop) (hC : 0 < C) : IsBigOWith C l f g
参数：h : Tendsto (fun x => g x / f x) l atTop；hC : 0 < C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `Asymptotics.IsLittleO.of_tendsto_div_atTop`：∀ {α : Type u_1} {𝕜 : Type u
_17} [inst : NormedField 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [
OrderTopology 𝕜] {l : Filter α} …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem isBigOWith_of_tendsto_top {C : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atTop h) hC
/-
**Tactic.ComputeAsymptotics.isBigOWith_of_tendsto_bot** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics`。
形式化陈述：isBigOWith_of_tendsto_bot {C : Real} {f g : Real -> Real} {l : Filter Real
} (h : Tendsto (fun x => g x / f x) l atBot) (hC : 0 < C) : IsBigOWith C l f g
参数：h : Tendsto (fun x => g x / f x) l atBot；hC : 0 < C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `Asymptotics.IsLittleO.of_tendsto_div_atBot`：∀ {α : Type u_1} {𝕜 : Type u
_17} [inst : NormedField 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [
OrderTopology 𝕜] {l : Filter α} …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem isBigOWith_of_tendsto_bot {C : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atBot h) hC
/-
**Tactic.ComputeAsymptotics.isBigO_of_div_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空
间 `Tactic.ComputeAsymptotics`。
形式化陈述：isBigO_of_div_tendsto_atTop {f g : Real -> Real} {l : Filter Real} (h : Te
ndsto (fun x => g x / f x) l atTop) : f =O[l] g
参数：h : Tendsto (fun x => g x / f x) l atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.IsLittleO.of_tendsto_div_atTop`：∀ {α : Type u_1} {𝕜 : Type u
_17} [inst : NormedField 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [
OrderTopology 𝕜] {l : Filter α} …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem isBigO_of_div_tendsto_atTop {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)
/-
**Tactic.ComputeAsymptotics.isBigO_of_div_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空
间 `Tactic.ComputeAsymptotics`。
形式化陈述：isBigO_of_div_tendsto_atBot {f g : Real -> Real} {l : Filter Real} (h : Te
ndsto (fun x => g x / f x) l atBot) : f =O[l] g
参数：h : Tendsto (fun x => g x / f x) l atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.IsLittleO.of_tendsto_div_atBot`：∀ {α : Type u_1} {𝕜 : Type u
_17} [inst : NormedField 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [
OrderTopology 𝕜] {l : Filter α} …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem isBigO_of_div_tendsto_atBot {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atBot) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

end Tactic.ComputeAsymptotics

