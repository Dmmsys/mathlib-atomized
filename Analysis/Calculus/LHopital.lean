/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hôpital's rule" for computing 0/0
indeterminate forms. The proof of `HasDerivAt.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`atTop` or `atBot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `HasDerivAt` form and a `deriv` form, which
is denoted by each statement being in either the `HasDerivAt` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/

public section


open Filter Set

open scoped Filter Topology Pointwise

variable {a b : ℝ} {l : Filter ℝ} {f f' g g' : ℝ → ℝ}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitly-provided interval.
-/


namespace HasDerivAt

/-
**HasDerivAt.lhopital_zero_right_on_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_right_on_Ioo (hab : a < b) (hff' : forall x in Ioo a b, HasD
erivAt f (f' x) x) (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hg' : fo
rall x in Ioo a b, g' x != 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g 
(𝓝[>] a) (𝓝 0)) (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) : Tendsto (fu
n x => f x / g x) (𝓝[>] a) l
参数：hab : a < b；hff' : forall x in Ioo a b, HasDerivAt f (f' x) x；hgg' : forall x
 in Ioo a b, HasDerivAt g (g' x) x；hg' : forall x in Ioo a b, g' x != 0；hfa : Te
ndsto f (𝓝[>] a) (𝓝 0)；hga : Tendsto g (𝓝[>] a) (𝓝 0)；hdiv : Tendsto (fun x => f
' x / g' x) (𝓝[>] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsLT`：nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a
 b] b = 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `exists_hasDerivAt_eq_zero'`：exists_hasDerivAt_eq_zero' (hab : a < b) (hf
a : Tendsto f (𝓝[>] a) (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : forall x 
in Ioo a b, HasD…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `exists_ratio_hasDerivAt_eq_ratio_slope'`：exists_ratio_hasDerivAt_eq_rati
o_slope' {lfa lga lfb lgb : Real} (hff' : forall x in Ioo a b, HasDerivAt f (f' 
x) x) (hgg' : forall x in Ioo…
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `tendsto_nhdsWithin_congr`：tendsto_nhdsWithin_congr {f g : α -> β} {s : S
et α} {a : α} {l : Filter β} (hfg : forall x in s, f x = g x) (hf : Tendsto f (𝓝
[s] a) l) : Te…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
（共 67 条，此处仅展示前 30 条）
-/
theorem lhopital_zero_right_on_Ioo (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have sub : ∀ x ∈ Ioo a b, Ioo a x ⊆ Ioo a b := fun x hx =>
    Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)
  have hg : ∀ x ∈ Ioo a b, g x ≠ 0 := by
    intro x hx h
    have : Tendsto g (𝓝[<] x) (𝓝 0) := by
      rw [← h, ← nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact ((hgg' x hx).continuousAt.continuousWithinAt.mono <| sub x hx).tendsto
    obtain ⟨y, hyx, hy⟩ : ∃ c ∈ Ioo a x, g' c = 0 :=
      exists_hasDerivAt_eq_zero' hx.1 hga this fun y hy => hgg' y <| sub x hx hy
    exact hg' y (sub x hx hyx) hy
  have : ∀ x ∈ Ioo a b, ∃ c ∈ Ioo a x, f x * g' c = g x * f' c := by
    intro x hx
    rw [← sub_zero (f x), ← sub_zero (g x)]
    exact exists_ratio_hasDerivAt_eq_ratio_slope' g g' hx.1 f f' (fun y hy => hgg' y <| sub x hx hy)
      (fun y hy => hff' y <| sub x hx hy) hga hfa
      (tendsto_nhdsWithin_of_tendsto_nhds (hgg' x hx).continuousAt.tendsto)
      (tendsto_nhdsWithin_of_tendsto_nhds (hff' x hx).continuousAt.tendsto)
  choose! c hc using this
  have : ∀ x ∈ Ioo a b, ((fun x' => f' x' / g' x') ∘ c) x = f x / g x := by grind
  have cmp : ∀ x ∈ Ioo a b, a < c x ∧ c x < x := fun x hx ↦ (hc x hx).1
  rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
  apply tendsto_nhdsWithin_congr this
  apply hdiv.comp
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_) ?_
  all_goals
    apply eventually_nhdsWithin_of_forall
    intro x hx
    have := cmp x hx
    simp
    linarith [this]
/-
**HasDerivAt.lhopital_zero_right_on_Ico** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_right_on_Ico (hab : a < b) (hff' : forall x in Ioo a b, HasD
erivAt f (f' x) x) (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hcf : Co
ntinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b)) (hg' : forall x in Ioo 
a b, g' x != 0) (hfa : f a = 0) (hga : g a = 0) (hdiv : Tendsto (fun x => f' x /
 g' x) (𝓝[>] a) l) : Tendsto (fun x => f x / g x) (𝓝[>] a) l
参数：hab : a < b；hff' : forall x in Ioo a b, HasDerivAt f (f' x) x；hgg' : forall x
 in Ioo a b, HasDerivAt g (g' x) x；hcf : ContinuousOn f (Ico a b)；hcg : Continuo
usOn g (Ico a b)；hg' : forall x in Ioo a b, g' x != 0；hfa : f a = 0；hga : g a = 
0；hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.lhopital_zero_right_on_Ioo`：lhopital_zero_right_on_Ioo (hab :
 a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in 
Ioo a b, HasDerivAt g (g' x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem lhopital_zero_right_on_Ico (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b))
    (hcg : ContinuousOn g (Ico a b)) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
/-
**HasDerivAt.lhopital_zero_left_on_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_left_on_Ioo (hab : a < b) (hff' : forall x in Ioo a b, HasDe
rivAt f (f' x) x) (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hg' : for
all x in Ioo a b, g' x != 0) (hfb : Tendsto f (𝓝[<] b) (𝓝 0)) (hgb : Tendsto g (
𝓝[<] b) (𝓝 0)) (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) : Tendsto (fun
 x => f x / g x) (𝓝[<] b) l
参数：hab : a < b；hff' : forall x in Ioo a b, HasDerivAt f (f' x) x；hgg' : forall x
 in Ioo a b, HasDerivAt g (g' x) x；hg' : forall x in Ioo a b, g' x != 0；hfb : Te
ndsto f (𝓝[<] b) (𝓝 0)；hgb : Tendsto g (𝓝[<] b) (𝓝 0)；hdiv : Tendsto (fun x => f
' x / g' x) (𝓝[<] b) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_neg`：hasDerivAt_neg : HasDerivAt Neg.neg (-1) x
· 使用定理 `HasDerivAt.lhopital_zero_right_on_Ioo`：lhopital_zero_right_on_Ioo (hab :
 a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in 
Ioo a b, HasDerivAt g (g' x…
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.neg_Ioo`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : PartialO
rder α] [IsOrderedAddMonoid α] (a b : α),   -Set.Ioo a b = Set.Ioo (-b) (-a)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_neg_nhdsGT_neg`：∀ {H : Type x} [inst : TopologicalSpace H] [inst
_1 : AddCommGroup H] [inst_2 : PartialOrder H] [IsOrderedAddMonoid H]   [Continu
ousNeg H] {a…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
· 使用定理 `tendsto_neg_nhdsLT`：∀ {H : Type x} [inst : TopologicalSpace H] [inst_1 :
 AddCommGroup H] [inst_2 : PartialOrder H] [IsOrderedAddMonoid H]   [ContinuousN
eg H] {a…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem lhopital_zero_left_on_Ioo (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfb : Tendsto f (𝓝[<] b) (𝓝 0)) (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Ioo] at hdnf hdng
  have := lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng (by grind)
    (hfb.comp tendsto_neg_nhdsGT_neg) (hgb.comp tendsto_neg_nhdsGT_neg)
    (by
      simp only [neg_div_neg_eq, mul_one, mul_neg]
      exact hdiv.comp tendsto_neg_nhdsGT_neg)
  have := this.comp tendsto_neg_nhdsLT
  unfold Function.comp at this
  simpa only [neg_neg]
/-
**HasDerivAt.lhopital_zero_left_on_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_left_on_Ioc (hab : a < b) (hff' : forall x in Ioo a b, HasDe
rivAt f (f' x) x) (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hcf : Con
tinuousOn f (Ioc a b)) (hcg : ContinuousOn g (Ioc a b)) (hg' : forall x in Ioo a
 b, g' x != 0) (hfb : f b = 0) (hgb : g b = 0) (hdiv : Tendsto (fun x => f' x / 
g' x) (𝓝[<] b) l) : Tendsto (fun x => f x / g x) (𝓝[<] b) l
参数：hab : a < b；hff' : forall x in Ioo a b, HasDerivAt f (f' x) x；hgg' : forall x
 in Ioo a b, HasDerivAt g (g' x) x；hcf : ContinuousOn f (Ioc a b)；hcg : Continuo
usOn g (Ioc a b)；hg' : forall x in Ioo a b, g' x != 0；hfb : f b = 0；hgb : g b = 
0；hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.lhopital_zero_left_on_Ioo`：lhopital_zero_left_on_Ioo (hab : a
 < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in Io
o a b, HasDerivAt g (g' x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsLT`：nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a
 b] b = 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
theorem lhopital_zero_left_on_Ioc (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b))
    (hcg : ContinuousOn g (Ioc a b)) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hfb : f b = 0) (hgb : g b = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
  · rw [← hgb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
/-
**HasDerivAt.lhopital_zero_atTop_on_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_atTop_on_Ioi (hff' : forall x in Ioi a, HasDerivAt f (f' x) 
x) (hgg' : forall x in Ioi a, HasDerivAt g (g' x) x) (hg' : forall x in Ioi a, g
' x != 0) (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0)) (hdiv 
: Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l
参数：hff' : forall x in Ioi a, HasDerivAt f (f' x) x；hgg' : forall x in Ioi a, Has
DerivAt g (g' x) x；hg' : forall x in Ioi a, g' x != 0；hftop : Tendsto f atTop (𝓝
 0)；hgtop : Tendsto g atTop (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `lt_one_add`：lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
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
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `lt_inv_comm₀`：lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_inv`：hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y 
=> y⁻¹) (-(x ^ 2)⁻¹) x
（共 57 条，此处仅展示前 30 条）
-/
theorem lhopital_zero_atTop_on_Ioi (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  obtain ⟨a', haa', ha'⟩ : ∃ a', a < a' ∧ 0 < a' := ⟨1 + max a 0,
    ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
      lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩
  have fact1 : ∀ x : ℝ, x ∈ Ioo 0 a'⁻¹ → x ≠ 0 := fun _ hx => (ne_of_lt hx.1).symm
  have fact2 (x) (hx : x ∈ Ioo 0 a'⁻¹) : a < x⁻¹ := lt_trans haa' ((lt_inv_comm₀ ha' hx.1).mpr hx.2)
  have hdnf : ∀ x ∈ Ioo 0 a'⁻¹, HasDerivAt (f ∘ Inv.inv) (f' x⁻¹ * -(x ^ 2)⁻¹) x := fun x hx =>
    comp x (hff' x⁻¹ <| fact2 x hx) (hasDerivAt_inv <| fact1 x hx)
  have hdng : ∀ x ∈ Ioo 0 a'⁻¹, HasDerivAt (g ∘ Inv.inv) (g' x⁻¹ * -(x ^ 2)⁻¹) x := fun x hx =>
    comp x (hgg' x⁻¹ <| fact2 x hx) (hasDerivAt_inv <| fact1 x hx)
  have := lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
    (by
      intro x hx
      refine mul_ne_zero ?_ (neg_ne_zero.mpr <| inv_ne_zero <| pow_ne_zero _ <| fact1 x hx)
      exact hg' _ (fact2 x hx))
    (hftop.comp tendsto_inv_nhdsGT_zero) (hgtop.comp tendsto_inv_nhdsGT_zero)
    (by
      refine (tendsto_congr' ?_).mp (hdiv.comp tendsto_inv_nhdsGT_zero)
      filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      simp only [Function.comp_def]
      rw [mul_div_mul_right]
      exact neg_ne_zero.mpr (by positivity))
  have := this.comp tendsto_inv_atTop_nhdsGT_zero
  unfold Function.comp at this
  simpa only [inv_inv]
/-
**HasDerivAt.lhopital_zero_atBot_on_Iio** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_atBot_on_Iio (hff' : forall x in Iio a, HasDerivAt f (f' x) 
x) (hgg' : forall x in Iio a, HasDerivAt g (g' x) x) (hg' : forall x in Iio a, g
' x != 0) (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0)) (hdiv 
: Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l
参数：hff' : forall x in Iio a, HasDerivAt f (f' x) x；hgg' : forall x in Iio a, Has
DerivAt g (g' x) x；hg' : forall x in Iio a, g' x != 0；hfbot : Tendsto f atBot (𝓝
 0)；hgbot : Tendsto g atBot (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) atBot l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_neg`：hasDerivAt_neg : HasDerivAt Neg.neg (-1) x
· 使用定理 `HasDerivAt.lhopital_zero_atTop_on_Ioi`：lhopital_zero_atTop_on_Ioi (hff' 
: forall x in Ioi a, HasDerivAt f (f' x) x) (hgg' : forall x in Ioi a, HasDerivA
t g (g' x) x) (hg' : forall…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.neg_Iio`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : PartialO
rder α] [IsOrderedAddMonoid α] (a : α),   -Set.Iio a = Set.Ioi (-a)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem lhopital_zero_atBot_on_Iio (hff' : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Iio a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Iio a, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Iio] at hdnf hdng
  have := lhopital_zero_atTop_on_Ioi hdnf hdng (by grind)
    (hfbot.comp tendsto_neg_atTop_atBot) (hgbot.comp tendsto_neg_atTop_atBot)
    (by simpa using! hdiv.comp tendsto_neg_atTop_atBot)
  have := this.comp tendsto_neg_atBot_atTop
  unfold Function.comp at this
  simpa only [neg_neg]

end HasDerivAt

namespace deriv

/-
**deriv.lhopital_zero_right_on_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_right_on_Ioo (hab : a < b) (hdf : DifferentiableOn Real f (I
oo a b)) (hg' : forall x in Ioo a b, deriv g x != 0) (hfa : Tendsto f (𝓝[>] a) (
𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (
deriv g) x) (𝓝[>] a) l) : Tendsto (fun x => f x / g x) (𝓝[>] a) l
参数：hab : a < b；hdf : DifferentiableOn Real f (Ioo a b)；hg' : forall x in Ioo a b
, deriv g x != 0；hfa : Tendsto f (𝓝[>] a) (𝓝 0)；hga : Tendsto g (𝓝[>] a) (𝓝 0)；h
div : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `HasDerivAt.lhopital_zero_right_on_Ioo`：lhopital_zero_right_on_Ioo (hab :
 a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in 
Ioo a b, HasDerivAt g (g' x…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem lhopital_zero_right_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_right_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfa hga hdiv
/-
**deriv.lhopital_zero_right_on_Ico** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_right_on_Ico (hab : a < b) (hdf : DifferentiableOn Real f (I
oo a b)) (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b)) (hg' 
: forall x in Ioo a b, (deriv g) x != 0) (hfa : f a = 0) (hga : g a = 0) (hdiv :
 Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) : Tendsto (fun x => f 
x / g x) (𝓝[>] a) l
参数：hab : a < b；hdf : DifferentiableOn Real f (Ioo a b)；hcf : ContinuousOn f (Ico
 a b)；hcg : ContinuousOn g (Ico a b)；hg' : forall x in Ioo a b, (deriv g) x != 0
；hfa : f a = 0；hga : g a = 0；hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x)
 (𝓝[>] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv.lhopital_zero_right_on_Ioo`：lhopital_zero_right_on_Ioo (hab : a < 
b) (hdf : DifferentiableOn Real f (Ioo a b)) (hg' : forall x in Ioo a b, deriv g
 x != 0) (hfa : Tendst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem lhopital_zero_right_on_Ico (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  refine lhopital_zero_right_on_Ioo hab hdf hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
/-
**deriv.lhopital_zero_left_on_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_left_on_Ioo (hab : a < b) (hdf : DifferentiableOn Real f (Io
o a b)) (hg' : forall x in Ioo a b, (deriv g) x != 0) (hfb : Tendsto f (𝓝[<] b) 
(𝓝 0)) (hgb : Tendsto g (𝓝[<] b) (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / 
(deriv g) x) (𝓝[<] b) l) : Tendsto (fun x => f x / g x) (𝓝[<] b) l
参数：hab : a < b；hdf : DifferentiableOn Real f (Ioo a b)；hg' : forall x in Ioo a b
, (deriv g) x != 0；hfb : Tendsto f (𝓝[<] b) (𝓝 0)；hgb : Tendsto g (𝓝[<] b) (𝓝 0)
；hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] b) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `HasDerivAt.lhopital_zero_left_on_Ioo`：lhopital_zero_left_on_Ioo (hab : a
 < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in Io
o a b, HasDerivAt g (g' x)…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem lhopital_zero_left_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfb hgb hdiv
/-
**deriv.lhopital_zero_atTop_on_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_atTop_on_Ioi (hdf : DifferentiableOn Real f (Ioi a)) (hg' : 
forall x in Ioi a, (deriv g) x != 0) (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Te
ndsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop 
l) : Tendsto (fun x => f x / g x) atTop l
参数：hdf : DifferentiableOn Real f (Ioi a)；hg' : forall x in Ioi a, (deriv g) x !=
 0；hftop : Tendsto f atTop (𝓝 0)；hgtop : Tendsto g atTop (𝓝 0)；hdiv : Tendsto (f
un x => (deriv f) x / (deriv g) x) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `HasDerivAt.lhopital_zero_atTop_on_Ioi`：lhopital_zero_atTop_on_Ioi (hff' 
: forall x in Ioi a, HasDerivAt f (f' x) x) (hgg' : forall x in Ioi a, HasDerivA
t g (g' x) x) (hg' : forall…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem lhopital_zero_atTop_on_Ioi (hdf : DifferentiableOn ℝ f (Ioi a))
    (hg' : ∀ x ∈ Ioi a, (deriv g) x ≠ 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  have hdf : ∀ x ∈ Ioi a, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioi_mem_nhds hx)
  have hdg : ∀ x ∈ Ioi a, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hftop hgtop hdiv
/-
**deriv.lhopital_zero_atBot_on_Iio** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_atBot_on_Iio (hdf : DifferentiableOn Real f (Iio a)) (hg' : 
forall x in Iio a, (deriv g) x != 0) (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Te
ndsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot 
l) : Tendsto (fun x => f x / g x) atBot l
参数：hdf : DifferentiableOn Real f (Iio a)；hg' : forall x in Iio a, (deriv g) x !=
 0；hfbot : Tendsto f atBot (𝓝 0)；hgbot : Tendsto g atBot (𝓝 0)；hdiv : Tendsto (f
un x => (deriv f) x / (deriv g) x) atBot l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `HasDerivAt.lhopital_zero_atBot_on_Iio`：lhopital_zero_atBot_on_Iio (hff' 
: forall x in Iio a, HasDerivAt f (f' x) x) (hgg' : forall x in Iio a, HasDerivA
t g (g' x) x) (hg' : forall…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem lhopital_zero_atBot_on_Iio (hdf : DifferentiableOn ℝ f (Iio a))
    (hg' : ∀ x ∈ Iio a, (deriv g) x ≠ 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  have hdf : ∀ x ∈ Iio a, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Iio_mem_nhds hx)
  have hdg : ∀ x ∈ Iio a, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atBot_on_Iio (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfbot hgbot hdiv

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/


namespace HasDerivAt

/-- L'Hôpital's rule for approaching a real from the right, `HasDerivAt` version -/
/-
**HasDerivAt.lhopital_zero_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_nhdsGT (hff' : forallᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x) (
hgg' : forallᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝[>] a, g
' x != 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0)) (hdi
v : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) : Tendsto (fun x => f x / g x) (𝓝
[>] a) l
参数：hff' : forallᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x；hgg' : forallᶠ x in 𝓝[>] a,
 HasDerivAt g (g' x) x；hg' : forallᶠ x in 𝓝[>] a, g' x != 0；hfa : Tendsto f (𝓝[>
] a) (𝓝 0)；hga : Tendsto g (𝓝[>] a) (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) 
(𝓝[>] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `mem_nhdsGT_iff_exists_Ioo_subset`：mem_nhdsGT_iff_exists_Ioo_subset [NoMa
xOrder α] {a : α} {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subsete
q s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `HasDerivAt.lhopital_zero_right_on_Ioo`：lhopital_zero_right_on_Ioo (hab :
 a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in 
Ioo a b, HasDerivAt g (g' x…

--- 原说明 ---
L'Hôpital's rule for approaching a real from the right, `HasDerivAt` version
-/
theorem lhopital_zero_nhdsGT (hff' : ∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[>] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ 𝓝[>] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨u, hau, hu⟩
  refine lhopital_zero_right_on_Ioo hau ?_ ?_ ?_ hfa hga hdiv <;> grind

/-- L'Hôpital's rule for approaching a real from the left, `HasDerivAt` version -/
/-
**HasDerivAt.lhopital_zero_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_nhdsLT (hff' : forallᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x) (
hgg' : forallᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝[<] a, g
' x != 0) (hfa : Tendsto f (𝓝[<] a) (𝓝 0)) (hga : Tendsto g (𝓝[<] a) (𝓝 0)) (hdi
v : Tendsto (fun x => f' x / g' x) (𝓝[<] a) l) : Tendsto (fun x => f x / g x) (𝓝
[<] a) l
参数：hff' : forallᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x；hgg' : forallᶠ x in 𝓝[<] a,
 HasDerivAt g (g' x) x；hg' : forallᶠ x in 𝓝[<] a, g' x != 0；hfa : Tendsto f (𝓝[<
] a) (𝓝 0)；hga : Tendsto g (𝓝[<] a) (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) 
(𝓝[<] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset`：mem_nhdsLT_iff_exists_Ioo_subset [NoMi
nOrder α] {a : α} {s : Set α} : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subsete
q s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `HasDerivAt.lhopital_zero_left_on_Ioo`：lhopital_zero_left_on_Ioo (hab : a
 < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in Io
o a b, HasDerivAt g (g' x)…

--- 原说明 ---
L'Hôpital's rule for approaching a real from the left, `HasDerivAt` version
-/
theorem lhopital_zero_nhdsLT (hff' : ∀ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[<] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[<] a) (𝓝 0)) (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ 𝓝[<] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨l, hal, hl⟩
  refine lhopital_zero_left_on_Ioo hal ?_ ?_ ?_ hfa hga hdiv <;> grind

/-- L'Hôpital's rule for approaching a real, `HasDerivAt` version. This
  does not require anything about the situation at `a` -/
/-
**HasDerivAt.lhopital_zero_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_nhdsNE (hff' : forallᶠ x in 𝓝[!=] a, HasDerivAt f (f' x) x) 
(hgg' : forallᶠ x in 𝓝[!=] a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝[!=] a
, g' x != 0) (hfa : Tendsto f (𝓝[!=] a) (𝓝 0)) (hga : Tendsto g (𝓝[!=] a) (𝓝 0))
 (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[!=] a) l) : Tendsto (fun x => f x / g
 x) (𝓝[!=] a) l
参数：hff' : forallᶠ x in 𝓝[!=] a, HasDerivAt f (f' x) x；hgg' : forallᶠ x in 𝓝[!=] 
a, HasDerivAt g (g' x) x；hg' : forallᶠ x in 𝓝[!=] a, g' x != 0；hfa : Tendsto f (
𝓝[!=] a) (𝓝 0)；hga : Tendsto g (𝓝[!=] a) (𝓝 0)；hdiv : Tendsto (fun x => f' x / g
' x) (𝓝[!=] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `HasDerivAt.lhopital_zero_nhdsLT`：lhopital_zero_nhdsLT (hff' : forallᶠ x 
in 𝓝[<] a, HasDerivAt f (f' x) x) (hgg' : forallᶠ x in 𝓝[<] a, HasDerivAt g (g' 
x) x) (hg' : forallᶠ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasDerivAt.lhopital_zero_nhdsGT`：lhopital_zero_nhdsGT (hff' : forallᶠ x 
in 𝓝[>] a, HasDerivAt f (f' x) x) (hgg' : forallᶠ x in 𝓝[>] a, HasDerivAt g (g' 
x) x) (hg' : forallᶠ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
L'Hôpital's rule for approaching a real, `HasDerivAt` version. This
  does not require anything about the situation at `a`
-/
theorem lhopital_zero_nhdsNE (hff' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[≠] a) (𝓝 0)) (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[≠] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  simp only [← Iio_union_Ioi, nhdsWithin_union, tendsto_sup, eventually_sup] at *
  exact ⟨lhopital_zero_nhdsLT hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
    lhopital_zero_nhdsGT hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

/-- L'Hôpital's rule for approaching a real from within a convex set, `HasDerivWithinAt` version.
  This does not require anything about the situation at `a` -/
/-
**HasDerivAt._root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex** 是 Mathlib
 中的一个定理，位于命名空间 `HasDerivAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
L'Hôpital's rule for approaching a real from within a convex set, `HasDerivWithi
nAt` version.
  This does not require anything about the situation at `a`
-/
theorem _root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hff' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (f' x) (s \ {a}) x)
    (hgg' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (g' x) (s \ {a}) x)
    (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x ↦ f' x / g' x) (𝓝[s \ {a}] a) l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[s \ {a}] a) l := .of_neBot_imp fun has => by
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  have h := hs.sdiff_singleton_eventually_mem_nhds a
  replace hff' := h.mp <| hff'.mono fun _ h ↦ h.hasDerivAt
  replace hgg' := h.mp <| hgg'.mono fun _ h ↦ h.hasDerivAt
  rcases eq_empty_or_nonempty (s ∩ Iio a) with hs_Iio | hs_Iio
    <;> rcases eq_empty_or_nonempty (s ∩ Ioi a) with hs_Ioi | hs_Ioi
  · simp [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left, hs_Iio, hs_Ioi]
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsGT has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsGT hff' hgg' hg' hfa hga hdiv
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsLT has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsLT hff' hgg' hg' hfa hga hdiv
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsNE has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `HasDerivAt` version -/
/-
**HasDerivAt.lhopital_zero_nhds** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_nhds (hff' : forallᶠ x in 𝓝 a, HasDerivAt f (f' x) x) (hgg' 
: forallᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝 a, g' x != 0) (
hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0)) (hdiv : Tendsto (fun 
x => f' x / g' x) (𝓝 a) l) : Tendsto (fun x => f x / g x) (𝓝[!=] a) l
参数：hff' : forallᶠ x in 𝓝 a, HasDerivAt f (f' x) x；hgg' : forallᶠ x in 𝓝 a, HasDe
rivAt g (g' x) x；hg' : forallᶠ x in 𝓝 a, g' x != 0；hfa : Tendsto f (𝓝 a) (𝓝 0)；h
ga : Tendsto g (𝓝 a) (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) (𝓝 a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.lhopital_zero_nhdsNE`：lhopital_zero_nhdsNE (hff' : forallᶠ x 
in 𝓝[!=] a, HasDerivAt f (f' x) x) (hgg' : forallᶠ x in 𝓝[!=] a, HasDerivAt g (g
' x) x) (hg' : forall…
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l

--- 原说明 ---
**L'Hôpital's rule** for approaching a real, `HasDerivAt` version
-/
theorem lhopital_zero_nhds (hff' : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝 a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝 a) l) : Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  apply @lhopital_zero_nhdsNE _ _ _ f' _ g' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

/-- L'Hôpital's rule for approaching +∞, `HasDerivAt` version -/
/-
**HasDerivAt.lhopital_zero_atTop** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_atTop (hff' : forallᶠ x in atTop, HasDerivAt f (f' x) x) (hg
g' : forallᶠ x in atTop, HasDerivAt g (g' x) x) (hg' : forallᶠ x in atTop, g' x 
!= 0) (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Te
ndsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l
参数：hff' : forallᶠ x in atTop, HasDerivAt f (f' x) x；hgg' : forallᶠ x in atTop, H
asDerivAt g (g' x) x；hg' : forallᶠ x in atTop, g' x != 0；hftop : Tendsto f atTop
 (𝓝 0)；hgtop : Tendsto g atTop (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) atTop
 l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HasDerivAt.lhopital_zero_atTop_on_Ioi`：lhopital_zero_atTop_on_Ioi (hff' 
: forall x in Ioi a, HasDerivAt f (f' x) x) (hgg' : forall x in Ioi a, HasDerivA
t g (g' x) x) (hg' : forall…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
L'Hôpital's rule for approaching +∞, `HasDerivAt` version
-/
theorem lhopital_zero_atTop (hff' : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atTop, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ atTop := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atTop_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Ioi l ⊆ s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atTop_on_Ioi ?_ ?_ (fun x hx ↦ hg' x (hl' hx).2) hftop hgtop hdiv <;> grind

/-- L'Hôpital's rule for approaching -∞, `HasDerivAt` version -/
/-
**HasDerivAt.lhopital_zero_atBot** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivAt`。
形式化陈述：lhopital_zero_atBot (hff' : forallᶠ x in atBot, HasDerivAt f (f' x) x) (hg
g' : forallᶠ x in atBot, HasDerivAt g (g' x) x) (hg' : forallᶠ x in atBot, g' x 
!= 0) (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Te
ndsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l
参数：hff' : forallᶠ x in atBot, HasDerivAt f (f' x) x；hgg' : forallᶠ x in atBot, H
asDerivAt g (g' x) x；hg' : forallᶠ x in atBot, g' x != 0；hfbot : Tendsto f atBot
 (𝓝 0)；hgbot : Tendsto g atBot (𝓝 0)；hdiv : Tendsto (fun x => f' x / g' x) atBot
 l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HasDerivAt.lhopital_zero_atBot_on_Iio`：lhopital_zero_atBot_on_Iio (hff' 
: forall x in Iio a, HasDerivAt f (f' x) x) (hgg' : forall x in Iio a, HasDerivA
t g (g' x) x) (hg' : forall…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
L'Hôpital's rule for approaching -∞, `HasDerivAt` version
-/
theorem lhopital_zero_atBot (hff' : ∀ᶠ x in atBot, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atBot, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atBot, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ atBot := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atBot_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Iio l ⊆ s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atBot_on_Iio ?_ ?_ (fun x hx ↦ hg' x (hl' hx).2) hfbot hgbot hdiv <;> grind

end HasDerivAt

namespace derivWithin

/-- **L'Hôpital's rule** for approaching a real from within a convex set, `derivWithin` version -/
/-
**derivWithin.lhopital_zero_nhdsWithin_convex** 是 Mathlib 中的一个定理，位于命名空间 `derivWi
thin`。
形式化陈述：lhopital_zero_nhdsWithin_convex {s : Set Real} (hs : Convex Real s) (hdf :
 forallᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt Real f (s \ {a}) x) (hg' : fo
rallᶠ x in 𝓝[s \ {a}] a, derivWithin g (s \ {a}) x != 0) (hfa : Tendsto f (𝓝[s \
 {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0)) (hdiv : Tendsto (fun x =>
 derivWithin f (s \ {a}) x / derivWithin g (s \ {a}) x) (𝓝[s \ {a}] a) l) : Tend
sto (fun x => f x / g x) (𝓝[s \ {a}] a) l
参数：hs : Convex Real s；hdf : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt Re
al f (s \ {a}) x；hg' : forallᶠ x in 𝓝[s \ {a}] a, derivWithin g (s \ {a}) x != 0
；hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)；hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0)；hdiv 
: Tendsto (fun x => derivWithin f (s \ {a}) x / derivWithin g (s \ {a}) x) (𝓝[s 
\ {a}] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `HasDerivWithinAt.lhopital_zero_nhdsWithin_convex`：∀ {a : ℝ} {l : Filter 
ℝ} {f f' g g' : ℝ → ℝ} {s : Set ℝ},   Convex ℝ s →     (∀ᶠ (x : ℝ) in nhdsWithin
 a (s \ {a}), HasDerivWithinAt f (f' x…

--- 原说明 ---
**L'Hôpital's rule** for approaching a real from within a convex set, `derivWith
in` version
-/
theorem lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hdf : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt ℝ f (s \ {a}) x)
    (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, derivWithin g (s \ {a}) x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => derivWithin f (s \ {a}) x / derivWithin g (s \ {a}) x)
      (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  have hdg : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt ℝ g (s \ {a}) x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (derivWithin_zero_of_not_differentiableWithinAt h))
  have hdf' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (derivWithin f (s \ {a}) x) (s \ {a}) x :=
    hdf.mp (Eventually.of_forall fun _ h ↦ h.hasDerivWithinAt)
  have hdg' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (derivWithin g (s \ {a}) x) (s \ {a}) x :=
    hdg.mp (Eventually.of_forall fun _ h => h.hasDerivWithinAt)
  exact HasDerivWithinAt.lhopital_zero_nhdsWithin_convex hs hdf' hdg' hg' hfa hga hdiv

end derivWithin

namespace deriv

/-- **L'Hôpital's rule** for approaching a real from within a convex set, `deriv` version -/
/-
**deriv.lhopital_zero_nhdsWithin_convex** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_nhdsWithin_convex {s : Set Real} (hs : Convex Real s) (hdf :
 forallᶠ x in 𝓝[s \ {a}] a, DifferentiableAt Real f x) (hg' : forallᶠ x in 𝓝[s \
 {a}] a, deriv g x != 0) (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g
 (𝓝[s \ {a}] a) (𝓝 0)) (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[s \ {
a}] a) l) : Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l
参数：hs : Convex Real s；hdf : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableAt Real f x
；hg' : forallᶠ x in 𝓝[s \ {a}] a, deriv g x != 0；hfa : Tendsto f (𝓝[s \ {a}] a) 
(𝓝 0)；hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0)；hdiv : Tendsto (fun x => deriv f x / 
deriv g x) (𝓝[s \ {a}] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin.lhopital_zero_nhdsWithin_convex`：lhopital_zero_nhdsWithin_co
nvex {s : Set Real} (hs : Convex Real s) (hdf : forallᶠ x in 𝓝[s \ {a}] a, Diffe
rentiableWithinAt Real f (s \ {a}…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Convex.sdiff_singleton_eventually_mem_nhds`：Convex.sdiff_singleton_event
ually_mem_nhds {s : Set 𝕜} (hs : Convex 𝕜 s) (a : 𝕜) : forallᶠ x in 𝓝[s \ {a}] a
, s \ {a} in 𝓝 x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…

--- 原说明 ---
**L'Hôpital's rule** for approaching a real from within a convex set, `deriv` ve
rsion
-/
theorem lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hdf : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableAt ℝ f x) (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, deriv g x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  refine derivWithin.lhopital_zero_nhdsWithin_convex hs
    (hdf.mono fun _ h ↦ h.differentiableWithinAt) (hg'.mp ?_) hfa hga
    (hdiv.congr' ?_)
  all_goals
    apply (hs.sdiff_singleton_eventually_mem_nhds a).mono
    intros
  · rwa [derivWithin_of_mem_nhds ‹_›]
  · simp only
    iterate 2 rw [derivWithin_of_mem_nhds ‹_›]

/-- **L'Hôpital's rule** for approaching a real from the right, `deriv` version -/
/-
**deriv.lhopital_zero_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_nhdsGT (hdf : forallᶠ x in 𝓝[>] a, DifferentiableAt Real f x
) (hg' : forallᶠ x in 𝓝[>] a, deriv g x != 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (
hga : Tendsto g (𝓝[>] a) (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g
) x) (𝓝[>] a) l) : Tendsto (fun x => f x / g x) (𝓝[>] a) l
参数：hdf : forallᶠ x in 𝓝[>] a, DifferentiableAt Real f x；hg' : forallᶠ x in 𝓝[>] 
a, deriv g x != 0；hfa : Tendsto f (𝓝[>] a) (𝓝 0)；hga : Tendsto g (𝓝[>] a) (𝓝 0)；
hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_sdiff_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ici a \ {a} = Set.Ioi a
· 使用定理 `deriv.lhopital_zero_nhdsWithin_convex`：lhopital_zero_nhdsWithin_convex {
s : Set Real} (hs : Convex Real s) (hdf : forallᶠ x in 𝓝[s \ {a}] a, Differentia
bleAt Real f x) (hg' : fora…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**L'Hôpital's rule** for approaching a real from the right, `deriv` version
-/
theorem lhopital_zero_nhdsGT (hdf : ∀ᶠ x in 𝓝[>] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[>] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  rw [← Ici_sdiff_left] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Ici a) hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real from the left, `deriv` version -/
/-
**deriv.lhopital_zero_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_nhdsLT (hdf : forallᶠ x in 𝓝[<] a, DifferentiableAt Real f x
) (hg' : forallᶠ x in 𝓝[<] a, deriv g x != 0) (hfa : Tendsto f (𝓝[<] a) (𝓝 0)) (
hga : Tendsto g (𝓝[<] a) (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g
) x) (𝓝[<] a) l) : Tendsto (fun x => f x / g x) (𝓝[<] a) l
参数：hdf : forallᶠ x in 𝓝[<] a, DifferentiableAt Real f x；hg' : forallᶠ x in 𝓝[<] 
a, deriv g x != 0；hfa : Tendsto f (𝓝[<] a) (𝓝 0)；hga : Tendsto g (𝓝[<] a) (𝓝 0)；
hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a
· 使用定理 `deriv.lhopital_zero_nhdsWithin_convex`：lhopital_zero_nhdsWithin_convex {
s : Set Real} (hs : Convex Real s) (hdf : forallᶠ x in 𝓝[s \ {a}] a, Differentia
bleAt Real f x) (hg' : fora…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**L'Hôpital's rule** for approaching a real from the left, `deriv` version
-/
theorem lhopital_zero_nhdsLT (hdf : ∀ᶠ x in 𝓝[<] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[<] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[<] a) (𝓝 0))
    (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  rw [← Iic_sdiff_right] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Iic a) hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
/-
**deriv.lhopital_zero_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_nhdsNE (hdf : forallᶠ x in 𝓝[!=] a, DifferentiableAt Real f 
x) (hg' : forallᶠ x in 𝓝[!=] a, deriv g x != 0) (hfa : Tendsto f (𝓝[!=] a) (𝓝 0)
) (hga : Tendsto g (𝓝[!=] a) (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (der
iv g) x) (𝓝[!=] a) l) : Tendsto (fun x => f x / g x) (𝓝[!=] a) l
参数：hdf : forallᶠ x in 𝓝[!=] a, DifferentiableAt Real f x；hg' : forallᶠ x in 𝓝[!=
] a, deriv g x != 0；hfa : Tendsto f (𝓝[!=] a) (𝓝 0)；hga : Tendsto g (𝓝[!=] a) (𝓝
 0)；hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[!=] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `deriv.lhopital_zero_nhdsWithin_convex`：lhopital_zero_nhdsWithin_convex {
s : Set Real} (hs : Convex Real s) (hdf : forallᶠ x in 𝓝[s \ {a}] a, Differentia
bleAt Real f x) (hg' : fora…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)

--- 原说明 ---
**L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a`
-/
theorem lhopital_zero_nhdsNE (hdf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[≠] a) (𝓝 0))
    (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[≠] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  rw [compl_eq_univ_sdiff] at *
  exact lhopital_zero_nhdsWithin_convex convex_univ hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version -/
/-
**deriv.lhopital_zero_nhds** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_nhds (hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x) (hg
' : forallᶠ x in 𝓝 a, deriv g x != 0) (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tends
to g (𝓝 a) (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l) 
: Tendsto (fun x => f x / g x) (𝓝[!=] a) l
参数：hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x；hg' : forallᶠ x in 𝓝 a, der
iv g x != 0；hfa : Tendsto f (𝓝 a) (𝓝 0)；hga : Tendsto g (𝓝 a) (𝓝 0)；hdiv : Tends
to (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv.lhopital_zero_nhdsNE`：lhopital_zero_nhdsNE (hdf : forallᶠ x in 𝓝[!
=] a, DifferentiableAt Real f x) (hg' : forallᶠ x in 𝓝[!=] a, deriv g x != 0) (h
fa : Tendsto f (…
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l

--- 原说明 ---
**L'Hôpital's rule** for approaching a real, `deriv` version
-/
theorem lhopital_zero_nhds (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝 a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  apply lhopital_zero_nhdsNE <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

/-- **L'Hôpital's rule** for approaching +∞, `deriv` version -/
/-
**deriv.lhopital_zero_atTop** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_atTop (hdf : forallᶠ x : Real in atTop, DifferentiableAt Rea
l f x) (hg' : forallᶠ x : Real in atTop, deriv g x != 0) (hftop : Tendsto f atTo
p (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x /
 (deriv g) x) atTop l) : Tendsto (fun x => f x / g x) atTop l
参数：hdf : forallᶠ x : Real in atTop, DifferentiableAt Real f x；hg' : forallᶠ x : 
Real in atTop, deriv g x != 0；hftop : Tendsto f atTop (𝓝 0)；hgtop : Tendsto g at
Top (𝓝 0)；hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `HasDerivAt.lhopital_zero_atTop`：lhopital_zero_atTop (hff' : forallᶠ x in
 atTop, HasDerivAt f (f' x) x) (hgg' : forallᶠ x in atTop, HasDerivAt g (g' x) x
) (hg' : forallᶠ x i…

--- 原说明 ---
**L'Hôpital's rule** for approaching +∞, `deriv` version
-/
theorem lhopital_zero_atTop (hdf : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x : ℝ in atTop, deriv g x ≠ 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  have hdg : ∀ᶠ x in atTop, DifferentiableAt ℝ g x := hg'.mp
    (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : ∀ᶠ x in atTop, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : ∀ᶠ x in atTop, HasDerivAt g (deriv g x) x :=
    hdg.mono fun _ => DifferentiableAt.hasDerivAt
  exact HasDerivAt.lhopital_zero_atTop hdf' hdg' hg' hftop hgtop hdiv

/-- **L'Hôpital's rule** for approaching -∞, `deriv` version -/
/-
**deriv.lhopital_zero_atBot** 是 Mathlib 中的一个定理，位于命名空间 `deriv`。
形式化陈述：lhopital_zero_atBot (hdf : forallᶠ x : Real in atBot, DifferentiableAt Rea
l f x) (hg' : forallᶠ x : Real in atBot, deriv g x != 0) (hfbot : Tendsto f atBo
t (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x /
 (deriv g) x) atBot l) : Tendsto (fun x => f x / g x) atBot l
参数：hdf : forallᶠ x : Real in atBot, DifferentiableAt Real f x；hg' : forallᶠ x : 
Real in atBot, deriv g x != 0；hfbot : Tendsto f atBot (𝓝 0)；hgbot : Tendsto g at
Bot (𝓝 0)；hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `HasDerivAt.lhopital_zero_atBot`：lhopital_zero_atBot (hff' : forallᶠ x in
 atBot, HasDerivAt f (f' x) x) (hgg' : forallᶠ x in atBot, HasDerivAt g (g' x) x
) (hg' : forallᶠ x i…

--- 原说明 ---
**L'Hôpital's rule** for approaching -∞, `deriv` version
-/
theorem lhopital_zero_atBot (hdf : ∀ᶠ x : ℝ in atBot, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x : ℝ in atBot, deriv g x ≠ 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  have hdg : ∀ᶠ x in atBot, DifferentiableAt ℝ g x :=
    hg'.mono fun _ hg' => by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h)
  have hdf' : ∀ᶠ x in atBot, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : ∀ᶠ x in atBot, HasDerivAt g (deriv g x) x :=
    hdg.mono fun _ => DifferentiableAt.hasDerivAt
  exact HasDerivAt.lhopital_zero_atBot hdf' hdg' hg' hfbot hgbot hdiv

end deriv

