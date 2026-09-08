/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Michael Stoll, Terence Tao
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Multiplicative inverse and iteration of real logarithm

We prove properties of the functions `x ↦ (log x)⁻¹` and `x ↦ log (log x)`.

## Main results

- `deriv_inv_log` gives a formula for the derivative of `x ↦ (log x)⁻¹` which holds for all values.
- `deriv_log_log` gives a formula for the derivative of `x ↦ log (log x)` which holds for all
  values.
-/

public section

namespace Real

open Filter Asymptotics Bornology Metric IsOrderBornology DifferentiableAt

/- ## Derivative of the inverse logarithm -/

/-
**Real.not_differentiableAt_inv_log_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_differentiableAt_inv_log_zero : ¬ DifferentiableAt Real (fun x => (log
 x)⁻¹) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `tendsto_nhdsWithin_mono_left`：tendsto_nhdsWithin_mono_left {f : α -> β} 
{a : α} {s t : Set α} {l : Filter β} (hst : s subseteq t) (h : Tendsto f (𝓝[t] a
) l) : Tendsto f (…
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用引理 `tendsto_log_mul_self_nhdsLT_zero`：tendsto_log_mul_self_nhdsLT_zero : Fil
ter.Tendsto (fun x => log x * x) (𝓝[<] 0) (𝓝 0)
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
## Derivative of the inverse logarithm
-/
lemma not_differentiableAt_inv_log_zero : ¬ DifferentiableAt ℝ (fun x ↦ (log x)⁻¹) 0 := by
  simp only [← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope_zero, zero_add, log_zero,
    inv_zero, sub_zero, smul_eq_mul, ← mul_inv, mul_comm _ (log _)]
  refine fun H ↦ (tendsto_nhdsWithin_mono_left (by grind : Set.Iio (0 : ℝ) ⊆ _) H).not_tendsto
    (by simp) (tendsto_inv_nhdsGT_zero.comp ?_)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_log_mul_self_nhdsLT_zero ?_
  simp only [← nhdsWithin_Ioo_eq_nhdsLT neg_one_lt_zero, Set.mem_Ioi]
  refine eventually_nhdsWithin_of_forall fun x ⟨hx₁, hx₂⟩ ↦ mul_pos_of_neg_of_neg ?_ hx₂
  apply log_neg_eq_log x ▸ log_neg <;> grind
/-
**Real.not_continuousAt_inv_log_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_continuousAt_inv_log_one : ¬ ContinuousAt (fun x => (log x)⁻¹) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Filter.tendsto_inv₀_nhdsNE_zero`：tendsto_inv₀_nhdsNE_zero : Tendsto Inv.
inv (𝓝[!=] 0) (cobounded α)
· 使用定理 `HasDerivAt.tendsto_nhdsNE`：HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f
' x) (hf' : f' != 0) : Tendsto f (𝓝[!=] x) (𝓝[!=] f x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Real.hasDerivAt_log`：hasDerivAt_log (hx : x != 0) : HasDerivAt log x⁻¹ x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用引理 `not_continuousAt_of_tendsto`：not_continuousAt_of_tendsto {f : X -> Y} {l
₁ : Filter X} {l₂ : Filter Y} {x : X} (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l
₁ <= 𝓝 x) (hl₂ : …
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)
-/
lemma not_continuousAt_inv_log_one : ¬ ContinuousAt (fun x ↦ (log x)⁻¹) 1 := by
  suffices Tendsto (fun x ↦ (log x)⁻¹) (nhdsWithin 1 {1}ᶜ) (cobounded ℝ) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
  exact tendsto_inv₀_nhdsNE_zero.comp <| log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero
/-
**Real.not_continuousAt_inv_log_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_continuousAt_inv_log_neg_one : ¬ ContinuousAt (fun x => (log x)⁻¹) (-1
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.not_continuousAt_inv_log_one`：not_continuousAt_inv_log_one : ¬ Cont
inuousAt (fun x => (log x)⁻¹) 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `continuousAt_neg`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : N
eg G] [ContinuousNeg G] {x : G}, ContinuousAt Neg.neg x
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma not_continuousAt_inv_log_neg_one : ¬ ContinuousAt (fun x ↦ (log x)⁻¹) (-1) :=
  fun H ↦ not_continuousAt_inv_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)
/-
**Real.deriv_inv_log_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_inv_log_apply {x : Real} : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / log
 x ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `Real.not_continuousAt_inv_log_neg_one`：not_continuousAt_inv_log_neg_one 
: ¬ ContinuousAt (fun x => (log x)⁻¹) (-1)
· 使用引理 `Real.not_continuousAt_inv_log_one`：not_continuousAt_inv_log_one : ¬ Cont
inuousAt (fun x => (log x)⁻¹) 1
· 使用引理 `Real.not_differentiableAt_inv_log_zero`：not_differentiableAt_inv_log_zer
o : ¬ DifferentiableAt Real (fun x => (log x)⁻¹) 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_inv''`：deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x
 != 0) : deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_log'`：deriv_log' : deriv log = Inv.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
（共 42 条，此处仅展示前 30 条）
-/
theorem deriv_inv_log_apply {x : ℝ} : deriv (fun x ↦ (log x)⁻¹) x = -x⁻¹ / log x ^ 2 := by
  have := mt (continuousAt (𝕜 := ℝ)) not_continuousAt_inv_log_neg_one
  have := mt (continuousAt (𝕜 := ℝ)) not_continuousAt_inv_log_one
  have := not_differentiableAt_inv_log_zero
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt ‹_›]; simp

@[simp]
/-
**Real.deriv_inv_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_inv_log : deriv (fun x => (log x)⁻¹) = fun x => -x⁻¹ / log x ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.deriv_inv_log_apply`：deriv_inv_log_apply {x : Real} : deriv (fun x 
=> (log x)⁻¹) x = -x⁻¹ / log x ^ 2
-/
theorem deriv_inv_log : deriv (fun x ↦ (log x)⁻¹) = fun x ↦ -x⁻¹ / log x ^ 2 :=
  funext fun _ ↦ deriv_inv_log_apply
/-
**Real.differentiableAt_inv_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_inv_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x
 != -1) : DifferentiableAt Real (fun x => (log x)⁻¹) x
参数：hx₀ : x != 0；hx₁ : x != 1；hx₂ : x != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.fun_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {R : Type u_…
· 使用定理 `DifferentiableAt.log`：DifferentiableAt.log (hf : DifferentiableAt Real f
 x) (hx : f x != 0) : DifferentiableAt Real (fun x => log (f x)) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
-/
theorem differentiableAt_inv_log {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hx₂ : x ≠ -1) :
    DifferentiableAt ℝ (fun x ↦ (log x)⁻¹) x := by
  fun_prop (disch := grind [log_ne_zero])
/-
**Real.hasDerivAt_inv_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_inv_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1
) : HasDerivAt (fun x => (log x)⁻¹) (-x⁻¹ / (log x ^ 2)) x
参数：hx₀ : x != 0；hx₁ : x != 1；hx₂ : x != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_inv_log`：deriv_inv_log : deriv (fun x => (log x)⁻¹) = fun x =
> -x⁻¹ / log x ^ 2
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Real.differentiableAt_inv_log`：differentiableAt_inv_log {x : Real} (hx₀ 
: x != 0) (hx₁ : x != 1) (hx₂ : x != -1) : DifferentiableAt Real (fun x => (log 
x)⁻¹) x
-/
theorem hasDerivAt_inv_log {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hx₂ : x ≠ -1) :
    HasDerivAt (fun x ↦ (log x)⁻¹) (-x⁻¹ / (log x ^ 2)) x := by
  simpa using (differentiableAt_inv_log hx₀ hx₁ hx₂).hasDerivAt
/-
**Real.differentiableOn_inv_log'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_inv_log' : DifferentiableOn Real (fun x => (log x)⁻¹) {-1
,0,1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.inv`：DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S)
 (hz : forall x in S, h x != 0) : DifferentiableOn 𝕜 (h⁻¹) S
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Real.differentiableOn_log`：differentiableOn_log : DifferentiableOn Real 
log {0}ᶜ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem differentiableOn_inv_log' : DifferentiableOn ℝ (fun x ↦ (log x)⁻¹) {-1,0,1}ᶜ :=
  (differentiableOn_log.mono (by grind)).inv (by simp; tauto)
/-
**Real.differentiableOn_inv_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_inv_log : DifferentiableOn Real (fun x => (log x)⁻¹) (.Io
i 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Real.differentiableOn_inv_log'`：differentiableOn_inv_log' : Differentiab
leOn Real (fun x => (log x)⁻¹) {-1,0,1}ᶜ
-/
theorem differentiableOn_inv_log : DifferentiableOn ℝ (fun x ↦ (log x)⁻¹) (.Ioi 1) :=
  differentiableOn_inv_log'.mono (by grind)
/-
**Real.inv_log_isLittleO_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inv_log_isLittleO_one : (fun x => (log x)⁻¹) =o[atTop] fun _ => (1 : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem inv_log_isLittleO_one : (fun x ↦ (log x)⁻¹) =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [isLittleO_one_iff]
  convert tendsto_log_atTop.inv_tendsto_atTop; simp

/- ## Derivative of the iterated logarithm -/

/-
**Real.not_continuousAt_log_log_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_continuousAt_log_log_zero : ¬ ContinuousAt (fun x => log (log x)) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用引理 `IsOrderBornology.atTop_le_cobounded`：IsOrderBornology.atTop_le_cobounded
 [NoMaxOrder α] : .atTop <= Bornology.cobounded α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
· 使用引理 `not_continuousAt_of_tendsto`：not_continuousAt_of_tendsto {f : X -> Y} {l
₁ : Filter X} {l₂ : Filter Y} {x : X} (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l
₁ <= 𝓝 x) (hl₂ : …
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)

--- 原说明 ---
## Derivative of the iterated logarithm
-/
lemma not_continuousAt_log_log_zero : ¬ ContinuousAt (fun x ↦ log (log x)) 0 := by
  suffices Tendsto (fun x ↦ log (log x)) (nhdsWithin 0 {0}ᶜ) (cobounded ℝ) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
  have : Tendsto log atBot atTop := by
    convert tendsto_log_atTop.comp tendsto_neg_atBot_atTop; ext; simp
  exact (this.mono_right atTop_le_cobounded).comp tendsto_log_nhdsNE_zero
/-
**Real.not_continuousAt_log_log_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_continuousAt_log_log_one : ¬ ContinuousAt (fun x => log (log x)) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
· 使用引理 `IsOrderBornology.atBot_le_cobounded`：IsOrderBornology.atBot_le_cobounded
 [NoMinOrder α] : .atBot <= Bornology.cobounded α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `HasDerivAt.tendsto_nhdsNE`：HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f
' x) (hf' : f' != 0) : Tendsto f (𝓝[!=] x) (𝓝[!=] f x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Real.hasDerivAt_log`：hasDerivAt_log (hx : x != 0) : HasDerivAt log x⁻¹ x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用引理 `not_continuousAt_of_tendsto`：not_continuousAt_of_tendsto {f : X -> Y} {l
₁ : Filter X} {l₂ : Filter Y} {x : X} (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l
₁ <= 𝓝 x) (hl₂ : …
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)
-/
lemma not_continuousAt_log_log_one : ¬ ContinuousAt (fun x ↦ log (log x)) 1 := by
  suffices Tendsto (fun x ↦ log (log x)) (nhdsWithin 1 {1}ᶜ) (cobounded ℝ) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
  exact (tendsto_log_nhdsNE_zero.mono_right atBot_le_cobounded).comp <| log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero
/-
**Real.not_continuousAt_log_log_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_continuousAt_log_log_neg_one : ¬ ContinuousAt (fun x => log (log x)) (
-1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.not_continuousAt_log_log_one`：not_continuousAt_log_log_one : ¬ Cont
inuousAt (fun x => log (log x)) 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `continuousAt_neg`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : N
eg G] [ContinuousNeg G] {x : G}, ContinuousAt Neg.neg x
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma not_continuousAt_log_log_neg_one : ¬ ContinuousAt (fun x ↦ log (log x)) (-1) :=
  fun H ↦ not_continuousAt_log_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)
/-
**Real.deriv_log_log_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_log_log_apply {x : Real} : deriv (fun x => log (log x)) x = x⁻¹ / lo
g x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.not_continuousAt_log_log_neg_one`：not_continuousAt_log_log_neg_one 
: ¬ ContinuousAt (fun x => log (log x)) (-1)
· 使用引理 `Real.not_continuousAt_log_log_zero`：not_continuousAt_log_log_zero : ¬ Co
ntinuousAt (fun x => log (log x)) 0
· 使用引理 `Real.not_continuousAt_log_log_one`：not_continuousAt_log_log_one : ¬ Cont
inuousAt (fun x => log (log x)) 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv.log`：deriv.log (hf : DifferentiableAt Real f x) (hx : f x != 0) : 
deriv (fun x => log (f x)) x = deriv f x / f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_log'`：deriv_log' : deriv log = Inv.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
（共 37 条，此处仅展示前 30 条）
-/
theorem deriv_log_log_apply {x : ℝ} : deriv (fun x ↦ log (log x)) x = x⁻¹ / log x := by
  have := not_continuousAt_log_log_neg_one
  have := not_continuousAt_log_log_zero
  have := not_continuousAt_log_log_one
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt (mt continuousAt ‹_›)]; simp

@[simp]
/-
**Real.deriv_log_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_log_log : deriv (fun x => log (log x)) = fun x => x⁻¹ / log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.deriv_log_log_apply`：deriv_log_log_apply {x : Real} : deriv (fun x 
=> log (log x)) x = x⁻¹ / log x
-/
theorem deriv_log_log : deriv (fun x ↦ log (log x)) = fun x ↦ x⁻¹ / log x :=
  funext fun _ ↦ deriv_log_log_apply
/-
**Real.differentiableAt_log_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_log_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x
 != -1) : DifferentiableAt Real (fun x => log (log x)) x
参数：hx₀ : x != 0；hx₁ : x != 1；hx₂ : x != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.log`：DifferentiableAt.log (hf : DifferentiableAt Real f
 x) (hx : f x != 0) : DifferentiableAt Real (fun x => log (f x)) x
· 使用定理 `Real.differentiableAt_log`：∀ {x : ℝ}, x ≠ 0 → DifferentiableAt ℝ Real.lo
g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem differentiableAt_log_log {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hx₂ : x ≠ -1) :
    DifferentiableAt ℝ (fun x ↦ log (log x)) x :=
  (differentiableAt_log (by grind)).log (by simp; grind)
/-
**Real.hasDerivAt_log_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_log_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1
) : HasDerivAt (fun x => log (log x)) (x⁻¹ / log x) x
参数：hx₀ : x != 0；hx₁ : x != 1；hx₂ : x != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_log_log`：deriv_log_log : deriv (fun x => log (log x)) = fun x
 => x⁻¹ / log x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Real.differentiableAt_log_log`：differentiableAt_log_log {x : Real} (hx₀ 
: x != 0) (hx₁ : x != 1) (hx₂ : x != -1) : DifferentiableAt Real (fun x => log (
log x)) x
-/
theorem hasDerivAt_log_log {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hx₂ : x ≠ -1) :
    HasDerivAt (fun x ↦ log (log x)) (x⁻¹ / log x) x := by
  simpa using (differentiableAt_log_log hx₀ hx₁ hx₂).hasDerivAt
/-
**Real.differentiableOn_log_log'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_log_log' : DifferentiableOn Real (fun x => log (log x)) {
-1,0,1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.log`：DifferentiableOn.log (hf : DifferentiableOn Real f
 s) (hx : forall x in s, f x != 0) : DifferentiableOn Real (fun x => log (f x)) 
s
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Real.differentiableOn_log`：differentiableOn_log : DifferentiableOn Real 
log {0}ᶜ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem differentiableOn_log_log' : DifferentiableOn ℝ (fun x ↦ log (log x)) {-1,0,1}ᶜ :=
  (differentiableOn_log.mono (by grind)).log (by simp; tauto)
/-
**Real.differentiableOn_log_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_log_log : DifferentiableOn Real (fun x => log (log x)) (.
Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Real.differentiableOn_log_log'`：differentiableOn_log_log' : Differentiab
leOn Real (fun x => log (log x)) {-1,0,1}ᶜ
-/
theorem differentiableOn_log_log : DifferentiableOn ℝ (fun x ↦ log (log x)) (.Ioi 1) :=
  differentiableOn_log_log'.mono (by grind)
/-
**Real.one_isLittleO_log_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_isLittleO_log_log : (fun _ => (1 : Real)) =o[atTop] fun x => log (log 
x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem one_isLittleO_log_log : (fun _ ↦ (1 : ℝ)) =o[atTop] fun x ↦ log (log x) := by
  simp only [isLittleO_one_left_iff, norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

