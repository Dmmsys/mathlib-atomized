/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Order.Archimedean.IndicatorCard
public import Mathlib.Probability.Martingale.Centering
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalStopping

/-!

# Generalized Borel-Cantelli lemma

This file proves Lévy's generalized Borel-Cantelli lemma which is a generalization of the
Borel-Cantelli lemmas. With this generalization, one can easily deduce the Borel-Cantelli lemmas
by choosing appropriate filtrations. This file also contains the one-sided martingale bound which
is required to prove the generalized Borel-Cantelli.

**Note**: the usual Borel-Cantelli lemmas are not in this file.
See `MeasureTheory.measure_limsup_atTop_eq_zero` for the first (which does not depend on
the results here), and `ProbabilityTheory.measure_limsup_eq_one` for the second (which does).

## Main results

- `MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto`: the one-sided martingale bound: given
  a submartingale `f` with uniformly bounded differences, the set for which `f` converges is almost
  everywhere equal to the set for which it is bounded.
- `MeasureTheory.ae_mem_limsup_atTop_iff`: Lévy's generalized Borel-Cantelli:
  given a filtration `ℱ` and a sequence of sets `s` such that `s n ∈ ℱ n` for all `n`,
  `limsup atTop s` is almost everywhere equal to the set for which `∑ ℙ[s (n + 1)∣ℱ n] = ∞`.

-/

@[expose] public section


open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {ι Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
/-!
### One-sided martingale bound
-/

/-- `leastGE f r` is the stopping time corresponding to the first time `f ≥ r`. -/
/-
**MeasureTheory.leastGE** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：leastGE [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β] (f : ι -> Ω -> β
) (r : β) : Ω -> WithTop ι
参数：f : ι -> Ω -> β；r : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`leastGE f r` is the stopping time corresponding to the first time `f ≥ r`.
-/
noncomputable def leastGE [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ici r) ⊥
/-
**MeasureTheory.StronglyAdapted.isStoppingTime_leastGE** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {β : Type u_3} {m0 : MeasurableSpace Ω} [i
nst : ConditionallyCompleteLinearOrderBot ι]   {ℱ : MeasureTheory.Filtration ι m
0} [WellFoundedLT ι] [Countable ι] [inst_3 : TopologicalSpace β]   [inst_4 : Pre
order β] [ClosedIciTopology β] [TopologicalSpace.PseudoMetrizableSpace β] [inst_
7 : MeasurableSpace β]   [BorelSpace β] {f : ι → Ω → β} (r : β),   MeasureTheory
.StronglyAdapted ℱ f → MeasureTheory.IsStoppingTime ℱ (MeasureTheory.leastGE f r
)
参数：r : β；MeasureTheory.leastGE f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Adapted.isStoppingTime_hittingAfter`：∀ {Ω : Type u_1} {β :
 Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : ConditionallyCompleteL
inearOrder ι]   [WellFoundedLT ι] [Coun…
· 使用定理 `MeasureTheory.StronglyAdapted.adapted`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   
{β : ι → Type u_3} [inst_1 …
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem StronglyAdapted.isStoppingTime_leastGE [ConditionallyCompleteLinearOrderBot ι]
    {ℱ : Filtration ι m0} [WellFoundedLT ι] [Countable ι] [TopologicalSpace β]
    [Preorder β] [ClosedIciTopology β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {f : ι → Ω → β} (r : β) (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (leastGE f r) :=
  hf.adapted.isStoppingTime_hittingAfter measurableSet_Ici

/-- The stopped process of `f` above `r` is the process that is equal to `f` until `leastGE f r`
(the first time `f` passes above `r`), and then is constant afterwards. -/
/-
**MeasureTheory.stoppedAbove** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedAbove [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β] (f : ι -
> Ω -> β) (r : β) : ι -> Ω -> β
参数：f : ι -> Ω -> β；r : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stopped process of `f` above `r` is the process that is equal to `f` until `
leastGE f r`
(the first time `f` passes above `r`), and then is constant afterwards.
-/
noncomputable def stoppedAbove [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : ι → Ω → β :=
  stoppedProcess f (leastGE f r)

variable {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
/-
**MeasureTheory.Submartingale.stoppedAbove** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Submartingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.Submartingale f ℱ μ → ∀ (r : ℝ), MeasureTheory.Submarting
ale (MeasureTheory.stoppedAbove f r) ℱ μ
参数：r : ℝ；MeasureTheory.stoppedAbove f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.stoppedProcess`：∀ {Ω : Type u_1} {m0 : Measu
rableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢 : MeasureTheory.Filtration ℕ m0} 
  {f : ℕ → Ω → ℝ} {τ : Ω → ℕ∞} […
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `MeasureTheory.StronglyAdapted.isStoppingTime_leastGE`：∀ {ι : Type u_1} {
Ω : Type u_2} {β : Type u_3} {m0 : MeasurableSpace Ω} [inst : ConditionallyCompl
eteLinearOrderBot ι]   {ℱ : MeasureTheory.…
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
-/
protected lemma Submartingale.stoppedAbove [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (r : ℝ) :
    Submartingale (stoppedAbove f r) ℱ μ :=
  hf.stoppedProcess (hf.stronglyAdapted.isStoppingTime_leastGE r)

variable {r : ℝ} {R : ℝ≥0}

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.stoppedAbove_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedAbove_le (hr : 0 <= r) (hf0 : f 0 = 0) (hbdd : forallᵐ ω ∂μ, forall
 i, |f (i + 1) ω - f i ω| <= R) (i : Nat) : forallᵐ ω ∂μ, stoppedAbove f r i ω <
= r + R
参数：hr : 0 <= r；hf0 : f 0 = 0；hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω
| <= R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedAbove.eq_1`：∀ {ι : Type u_1} {Ω : Type u_2} {β : Ty
pe u_3} [inst : LinearOrder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι]   [inst
_3 : Preorder β] (f :…
· 使用定理 `MeasureTheory.stoppedProcess.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : 
Type u_3} [inst : Nonempty ι] [inst_1 : LinearOrder ι] (u : ι → Ω → β)   (τ : Ω 
→ WithTop ι) (i : ι) (ω…
· 使用定理 `ENat.some_eq_natCast`：WithTop.some = Nat.cast
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.notMem_of_lt_hittingAfter`：notMem_of_lt_hittingAfter {k : 
ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n <= k) : u k ω ∉ s
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 46 条，此处仅展示前 30 条）
-/
theorem stoppedAbove_le (hr : 0 ≤ r) (hf0 : f 0 = 0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    ∀ᵐ ω ∂μ, stoppedAbove f r i ω ≤ r + R := by
  filter_upwards [hbdd] with ω hbddω
  rw [stoppedAbove, stoppedProcess, ENat.some_eq_natCast]
  by_cases h_zero : (min (i : ℕ∞) (leastGE f r ω)).untopA = 0
  · simp only [h_zero, hf0, Pi.zero_apply]
    positivity
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h_zero
  rw [hk, add_comm r, ← sub_le_iff_le_add]
  have := notMem_of_lt_hittingAfter (?_ : k < leastGE f r ω)
  · simp only [bot_eq_zero, zero_le, Set.mem_Ici, not_le, forall_const] at this
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _))
  · suffices (k : ℕ∞) < min (i : ℕ∞) (leastGE f r ω) from this.trans_le (min_le_right _ _)
    have h_top : min (i : ℕ∞) (leastGE f r ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    lift min (i : ℕ∞) (leastGE f r ω) to ℕ using h_top with p
    simp only [untopD_coe_enat, Nat.cast_lt, gt_iff_lt] at *
    lia
/-
**MeasureTheory.Submartingale.eLpNorm_stoppedAbove_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {r : ℝ} {R : NNReal} [Measur
eTheory.IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     0 ≤ r →   
    f 0 = 0 →         (∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →  
         ∀ (i : ℕ),             MeasureTheory.eLpNorm (MeasureTheory.stoppedAbov
e f r i) 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal (r + ↑R)
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；i : ℕ；MeasureTheory.stop
pedAbove f r i；r + ↑R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_one_le_of_le'`：eLpNorm_one_le_of_le' {r : Real} (h
fint : Integrable f μ) (hfint' : 0 <= ∫ x, f x ∂μ) (hf : forallᵐ ω ∂μ, f ω <= r)
 : eLpNorm f 1 μ <= 2 * μ…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.stoppedAbove`：∀ {Ω : Type u_2} {m0 : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℕ m0}   
{f : ℕ → Ω → ℝ} [MeasureTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `MeasureTheory.Submartingale.setIntegral_le`：setIntegral_le [PartialOrder
 E] [IsOrderedAddMonoid E] [IsOrderedModule Real E] [ClosedIciTopology E] [Sigma
FiniteFiltration μ ℱ] {f : ι -> …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.stoppedAbove_le`：stoppedAbove_le (hr : 0 <= r) (hf0 : f 0 
= 0) (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) (i : Nat) : for
allᵐ ω ∂μ, stoppedA…
-/
theorem Submartingale.eLpNorm_stoppedAbove_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hr : 0 ≤ r) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    eLpNorm (stoppedAbove f r i) 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal (r + R) := by
  refine eLpNorm_one_le_of_le' ((hf.stoppedAbove r).integrable _) ?_
    (stoppedAbove_le hr hf0 hbdd i)
  rw [← setIntegral_univ]
  refine le_trans ?_ ((hf.stoppedAbove r).setIntegral_le zero_le MeasurableSet.univ)
  simp [stoppedAbove, stoppedProcess, hf0]
/-
**MeasureTheory.Submartingale.eLpNorm_stoppedAbove_le'** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {r : ℝ} {R : NNReal} [Measur
eTheory.IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     0 ≤ r →   
    f 0 = 0 →         (∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →  
         ∀ (i : ℕ),             MeasureTheory.eLpNorm (MeasureTheory.stoppedAbov
e f r i) 1 μ ≤               ↑(2 * μ Set.univ * ENNReal.ofReal (r + ↑R)).toNNRea
l
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；i : ℕ；MeasureTheory.stop
pedAbove f r i；2 * μ Set.univ * ENNReal.ofReal (r + ↑R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Submartingale.eLpNorm_stoppedAbove_le`：∀ {Ω : Type u_2} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrati
on ℕ m0}   {f : ℕ → Ω → ℝ} {r : ℝ} {R : N…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem Submartingale.eLpNorm_stoppedAbove_le' [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hr : 0 ≤ r) (hf0 : f 0 = 0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    eLpNorm (stoppedAbove f r i) 1 μ
      ≤ ENNReal.toNNReal (2 * μ Set.univ * ENNReal.ofReal (r + R)) := by
  refine (hf.eLpNorm_stoppedAbove_le hr hf0 hbdd i).trans ?_
  simp [ENNReal.coe_toNNReal (measure_ne_top μ _), ENNReal.coe_toNNReal]

/-- This lemma is superseded by `Submartingale.bddAbove_iff_exists_tendsto`. -/
/-
**MeasureTheory.Submartingale.exists_tendsto_of_abs_bddAbove_aux** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     f 0 = 0 →       (∀
ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →         ∀ᵐ (ω : Ω) ∂μ, Bd
dAbove (Set.range fun n => f n ω) → ∃ c, Filter.Tendsto (fun n => f n ω) Filter.
atTop (nhds c)
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；ω : Ω；Set.range fun n =>
 f n ω；fun n => f n ω；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`：∀ {Ω : Type u_1} {
m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrat
ion ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Submartingale.stoppedAbove`：∀ {Ω : Type u_2} {m0 : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℕ m0}   
{f : ℕ → Ω → ℝ} [MeasureTheory…
· 使用定理 `MeasureTheory.Submartingale.eLpNorm_stoppedAbove_le'`：∀ {Ω : Type u_2} {
m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrat
ion ℕ m0}   {f : ℕ → Ω → ℝ} {r : ℝ} {R : N…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `BddAbove.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), BddAbove s = 
(upperBounds s).Nonempty
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `MeasureTheory.stoppedAbove.eq_1`：∀ {ι : Type u_1} {Ω : Type u_2} {β : Ty
pe u_3} [inst : LinearOrder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι]   [inst
_3 : Preorder β] (f :…
· 使用定理 `MeasureTheory.stoppedProcess.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : 
Type u_3} [inst : Nonempty ι] [inst_1 : LinearOrder ι] (u : ι → Ω → β)   (τ : Ω 
→ WithTop ι) (i : ι) (ω…
· 使用定理 `MeasureTheory.leastGE.eq_1`：∀ {ι : Type u_1} {Ω : Type u_2} {β : Type u_
3} [inst : Preorder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι]   [inst_3 : Pre
order β] (f : ι …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.hittingAfter_eq_top_iff`：hittingAfter_eq_top_iff : hitting
After u s n ω = ⊤ ↔ forall j, n <= j -> u j ω ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is superseded by `Submartingale.bddAbove_iff_exists_tendsto`.
-/
theorem Submartingale.exists_tendsto_of_abs_bddAbove_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) → ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  have ht : ∀ᵐ ω ∂μ, ∀ i : ℕ, ∃ c, Tendsto (fun n => stoppedAbove f i n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    exact fun i ↦ Submartingale.exists_ae_tendsto_of_bdd (hf.stoppedAbove i)
      (hf.eLpNorm_stoppedAbove_le' i.cast_nonneg hf0 hbdd)
  filter_upwards [ht] with ω hω hωb
  rw [BddAbove] at hωb
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some
  have hib : ∀ n, f n ω < i := by
    intro n
    exact lt_of_le_of_lt ((mem_upperBounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi
  have heq : ∀ n, stoppedAbove f i n ω = f n ω := by
    intro n
    rw [stoppedAbove, stoppedProcess, leastGE, hittingAfter_eq_top_iff.mpr]
    · simp only [le_top, inf_of_le_left]
      congr
    · simp [hib]
  simp only [← heq, hω i]
/-
**MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto_aux** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     f 0 = 0 →       (∀
ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →         ∀ᵐ (ω : Ω) ∂μ, Bd
dAbove (Set.range fun n => f n ω) ↔ ∃ c, Filter.Tendsto (fun n => f n ω) Filter.
atTop (nhds c)
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；ω : Ω；Set.range fun n =>
 f n ω；fun n => f n ω；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Submartingale.exists_tendsto_of_abs_bddAbove_aux`：∀ {Ω : T
ype u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheo
ry.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.bddAbove_range`：Filter.Tendsto.bddAbove_range [IsDirected
Order α] {u : Nat -> α} (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.range u)
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
-/
theorem Submartingale.bddAbove_iff_exists_tendsto_aux [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.exists_tendsto_of_abs_bddAbove_aux hf0 hbdd] with ω hω using
    ⟨hω, fun ⟨c, hc⟩ => hc.bddAbove_range⟩

/-- One-sided martingale bound: If `f` is a submartingale which has uniformly bounded differences,
then for almost every `ω`, `f n ω` is bounded above (in `n`) if and only if it converges. -/
/-
**MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     (∀ᵐ (ω : Ω) ∂μ, ∀ 
(i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, BddAbove (Set.range 
fun n => f n ω) ↔ ∃ c, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds c)
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；ω : Ω；Set.range fun n =>
 f n ω；fun n => f n ω；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Submartingale.sub_martingale`：sub_martingale [Preorder E] 
[AddLeftMono E] (hf : Submartingale f ℱ μ) (hg : Martingale g ℱ μ) : Submartinga
le (f - g) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.martingale_const_fun`：martingale_const_fun [OrderBot ι] (ℱ
 : Filtration ι m0) (μ : Measure Ω) [SigmaFiniteFiltration μ ℱ] {f : Ω -> E} (hf
 : StronglyMeasurable[ℱ …
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto_aux`：∀ {Ω : Type
 u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.
Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
One-sided martingale bound: If `f` is a submartingale which has uniformly bounde
d differences,
then for almost every `ω`, `f n ω` is bounded above (in `n`) if and only if it c
onverges.
-/
theorem Submartingale.bddAbove_iff_exists_tendsto [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  set g : ℕ → Ω → ℝ := fun n ω => f n ω - f 0 ω
  have hg : Submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.stronglyAdapted 0) (hf.integrable 0))
  have hg0 : g 0 = 0 := by
    ext ω
    simp only [g, sub_self, Pi.zero_apply]
  have hgbdd : ∀ᵐ ω ∂μ, ∀ i : ℕ, |g (i + 1) ω - g i ω| ≤ ↑R := by
    simpa only [g, sub_sub_sub_cancel_right]
  filter_upwards [hg.bddAbove_iff_exists_tendsto_aux hg0 hgbdd] with ω hω
  convert! hω using 1
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨b, hb⟩ := h <;>
    refine ⟨b + |f 0 ω|, fun y hy => ?_⟩ <;> obtain ⟨n, rfl⟩ := hy
    · simp_rw [g, sub_eq_add_neg]
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs _)
    · exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩))
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨c, hc⟩ := h
    · exact ⟨c - f 0 ω, hc.sub_const _⟩
    · refine ⟨c + f 0 ω, ?_⟩
      have := hc.add_const (f 0 ω)
      simpa only [g, sub_add_cancel]

/-!
### Lévy's generalization of the Borel-Cantelli lemma

Lévy's generalization of the Borel-Cantelli lemma states that: given a natural number indexed
filtration $(\mathcal{F}_n)$, and a sequence of sets $(s_n)$ such that for all
$n$, $s_n \in \mathcal{F}_n$, $limsup_n s_n$ is almost everywhere equal to the set for which
$\sum_n \mathbb{P}[s_n \mid \mathcal{F}_n] = \infty$.

The proof strategy follows by constructing a martingale satisfying the one-sided martingale bound.
In particular, we define
$$
  f_n := \sum_{k < n} \big(\mathbf{1}_{s_{k + 1}} - \mathbb{P}[s_{k + 1} \mid \mathcal{F}_k]\big).
$$
Then, as a martingale is both a sub- and a super-martingale, the set for which it is unbounded from
above must agree with the set for which it is unbounded from below almost everywhere. Thus, it
can only converge to $\pm \infty$ with probability 0. Thus, by considering
$$
  \limsup_n s_n = \{\sum_n \mathbf{1}_{s_n} = \infty\}
$$
almost everywhere, the result follows.
-/


/-
**MeasureTheory.Martingale.bddAbove_range_iff_bddBelow_range** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Martingale f ℱ μ →     (∀ᵐ (ω : Ω) ∂μ, ∀ (i 
: ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, BddAbove (Set.range fun
 n => f n ω) ↔ BddBelow (Set.range fun n => f n ω)
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；ω : Ω；Set.range fun n =>
 f n ω；Set.range fun n => f n ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto`：∀ {Ω : Type u_2
} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filt
ration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `MeasureTheory.Martingale.submartingale`：submartingale [Preorder E] (hf :
 Martingale f ℱ μ) : Submartingale f ℱ μ
· 使用定理 `MeasureTheory.Martingale.neg`：neg (hf : Martingale f ℱ μ) : Martingale (
-f) ℱ μ
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, a ≤ -b ↔ b ≤ -a
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x

--- 原说明 ---
### Lévy's generalization of the Borel-Cantelli lemma

Lévy's generalization of the Borel-Cantelli lemma states that: given a natural n
umber indexed
filtration $(\mathcal{F}_n)$, and a sequence of sets $(s_n)$ such that for all
$n$, $s_n \in \mathcal{F}_n$, $limsup_n s_n$ is almost everywhere equal to the s
et for which
$\sum_n \mathbb{P}[s_n \mid \mathcal{F}_n] = \infty$.

The proof strategy follows by constructing a martingale satisfying the one-sided
 martingale bound.
In particular, we define
$$
  f_n := \sum_{k < n} \big(\mathbf{1}_{s_{k + 1}} - \mathbb{P}[s_{k + 1} \mid \m
athcal{F}_k]\big).
$$
Then, as a martingale is both a sub- and a super-martingale, the set for which i
t is unbounded from
above must agree with the set for which it is unbounded from below almost everyw
here. Thus, it
can only converge to $\pm \infty$ with probability 0. Thus, by considering
$$
  \limsup_n s_n = \{\sum_n \mathbf{1}_{s_n} = \infty\}
$$
almost everywhere, the result follows.
-/
theorem Martingale.bddAbove_range_iff_bddBelow_range [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ BddBelow (Set.range fun n => f n ω) := by
  have hbdd' : ∀ᵐ ω ∂μ, ∀ i, |(-f) (i + 1) ω - (-f) i ω| ≤ R := by
    filter_upwards [hbdd] with ω hω i
    simp only [Pi.neg_apply]
    grind
  have hup := hf.submartingale.bddAbove_iff_exists_tendsto hbdd
  have hdown := hf.neg.submartingale.bddAbove_iff_exists_tendsto hbdd'
  filter_upwards [hup, hdown] with ω hω₁ hω₂
  have : (∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c)) ↔
      ∃ c, Tendsto (fun n => (-f) n ω) atTop (𝓝 c) := by
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨-c, hc.neg⟩
    · refine ⟨-c, ?_⟩
      convert! hc.neg
      simp only [neg_neg, Pi.neg_apply]
  rw [hω₁, this, ← hω₂]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨-c, fun ω hω => ?_⟩
  · rw [mem_upperBounds] at hc
    refine neg_le.2 (hc _ ?_)
    simpa only [Pi.neg_apply, Set.mem_range, neg_inj]
  · rw [mem_lowerBounds] at hc
    simp_rw [Set.mem_range, Pi.neg_apply, neg_eq_iff_eq_neg] at hω
    refine le_neg.1 (hc _ ?_)
    simpa only [Set.mem_range]
/-
**MeasureTheory.Martingale.ae_not_tendsto_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Martingale f ℱ μ →     (∀ᵐ (ω : Ω) ∂μ, ∀ (i 
: ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, ¬Filter.Tendsto (fun n 
=> f n ω) Filter.atTop Filter.atTop
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；ω : Ω；fun n => f n ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Martingale.bddAbove_range_iff_bddBelow_range`：∀ {Ω : Type 
u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.F
iltration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.not_bddAbove_of_tendsto_atTop`：not_bddAbove_of_tendsto_atTop [NoM
axOrder β] (h : Tendsto f l atTop) : ¬BddAbove (range f)
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.bddBelow_range_of_tendsto_atTop_atTop`：bddBelow_range_of_tendsto_
atTop_atTop [IsCodirectedOrder α] {u : Nat -> α} (hx : Tendsto u atTop atTop) : 
BddBelow (Set.range u)
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
-/
theorem Martingale.ae_not_tendsto_atTop_atTop [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atTop := by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddAbove_of_tendsto_atTop htop (hω.2 <| bddBelow_range_of_tendsto_atTop_atTop htop)
/-
**MeasureTheory.Martingale.ae_not_tendsto_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Martingale f ℱ μ →     (∀ᵐ (ω : Ω) ∂μ, ∀ (i 
: ℕ), |f (i + 1) ω - f i ω| ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, ¬Filter.Tendsto (fun n 
=> f n ω) Filter.atTop Filter.atBot
参数：∀ᵐ (ω : Ω) ∂μ, ∀ (i : ℕ), |f (i + 1) ω - f i ω| ≤ ↑R；ω : Ω；fun n => f n ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Martingale.bddAbove_range_iff_bddBelow_range`：∀ {Ω : Type 
u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.F
iltration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.not_bddBelow_of_tendsto_atBot`：∀ {α : Type u_3} {β : Type u_4} [i
nst : Preorder β] {l : Filter α} [l.NeBot] {f : α → β} [NoMinOrder β],   Filter.
Tendsto f l Filter.atBot →…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.bddAbove_range_of_tendsto_atTop_atBot`：bddAbove_range_of_tendsto_
atTop_atBot [IsDirectedOrder α] {u : Nat -> α} (hx : Tendsto u atTop atBot) : Bd
dAbove (Set.range u)
-/
theorem Martingale.ae_not_tendsto_atTop_atBot [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atBot := by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddBelow_of_tendsto_atBot htop (hω.1 <| bddAbove_range_of_tendsto_atTop_atBot htop)

namespace BorelCantelli

/-- Auxiliary definition required to prove Lévy's generalization of the Borel-Cantelli lemmas for
which we will take the martingale part. -/
/-
**MeasureTheory.BorelCantelli.process** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.B
orelCantelli`。
形式化陈述：process (s : Nat -> Set Ω) (n : Nat) : Ω -> Real
参数：s : Nat -> Set Ω；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition required to prove Lévy's generalization of the Borel-Cantel
li lemmas for
which we will take the martingale part.
-/
noncomputable def process (s : ℕ → Set Ω) (n : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range n, (s (k + 1)).indicator 1

variable {s : ℕ → Set Ω}
/-
**MeasureTheory.BorelCantelli.process_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.BorelCantelli`。
形式化陈述：process_zero : process s 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.BorelCantelli.process.eq_1`：∀ {Ω : Type u_2} (s : ℕ → Set 
Ω) (n : ℕ),   MeasureTheory.BorelCantelli.process s n = ∑ k ∈ Finset.range n, (s
 (k + 1)).indicator 1
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
-/
theorem process_zero : process s 0 = 0 := by rw [process, Finset.range_zero, Finset.sum_empty]
/-
**MeasureTheory.BorelCantelli.stronglyAdapted_process** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.BorelCantelli`。
形式化陈述：stronglyAdapted_process (hs : forall n, MeasurableSet[ℱ n] (s n)) : Strong
lyAdapted ℱ (process s)
参数：hs : forall n, MeasurableSet[ℱ n] (s n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.stronglyMeasurable_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : A
ddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measurabl
eSpace α} {ι : Type…
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
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_one`：stronglyMeasurable_one [One β] : S
tronglyMeasurable (1 : α -> β)
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
-/
theorem stronglyAdapted_process (hs : ∀ n, MeasurableSet[ℱ n] (s n)) :
    StronglyAdapted ℱ (process s) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hk =>
    stronglyMeasurable_one.indicator <| ℱ.mono (Finset.mem_range.1 hk) _ <| hs _
/-
**MeasureTheory.BorelCantelli.martingalePart_process_ae_eq** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.BorelCantelli`。
形式化陈述：martingalePart_process_ae_eq (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : 
Nat -> Set Ω) (n : Nat) : martingalePart (process s) ℱ μ n = ∑ k in Finset.range
 n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k])
参数：ℱ : Filtration Nat m0；μ : Measure Ω；s : Nat -> Set Ω；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.martingalePart_eq_sum`：martingalePart_eq_sum : martingaleP
art f ℱ μ = fun n => f 0 + ∑ i in Finset.range n, (f (i + 1) - f i - μ[f (i + 1)
 - f i | ℱ i])
· 使用定理 `MeasureTheory.BorelCantelli.process_zero`：process_zero : process s 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_range_succ_sub_sum`：∀ {M : Type u_4} (f : ℕ → M) {n : ℕ} [ins
t : AddCommGroup M],   ∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range n, f
 i = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem martingalePart_process_ae_eq (ℱ : Filtration ℕ m0) (μ : Measure Ω) (s : ℕ → Set Ω) (n : ℕ) :
    martingalePart (process s) ℱ μ n =
      ∑ k ∈ Finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k]) := by
  simp only [martingalePart_eq_sum, process_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [process, Finset.sum_range_succ_sub_sum]
/-
**MeasureTheory.BorelCantelli.predictablePart_process_ae_eq** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.BorelCantelli`。
形式化陈述：predictablePart_process_ae_eq (ℱ : Filtration Nat m0) (μ : Measure Ω) (s :
 Nat -> Set Ω) (n : Nat) : predictablePart (process s) ℱ μ n = ∑ k in Finset.ran
ge n, μ[(s (k + 1)).indicator (1 : Ω -> Real) | ℱ k]
参数：ℱ : Filtration Nat m0；μ : Measure Ω；s : Nat -> Set Ω；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.BorelCantelli.martingalePart_process_ae_eq`：martingalePart
_process_ae_eq (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : Nat -> Set Ω) (n : N
at) : martingalePart (process s) ℱ μ n = ∑ k i…
· 使用定理 `sub_right_injective`：∀ {G : Type u_3} [inst : AddGroup G] {b : G}, Funct
ion.Injective fun a => b - a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
-/
theorem predictablePart_process_ae_eq (ℱ : Filtration ℕ m0) (μ : Measure Ω) (s : ℕ → Set Ω)
    (n : ℕ) : predictablePart (process s) ℱ μ n =
    ∑ k ∈ Finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] := by
  have := martingalePart_process_ae_eq ℱ μ s n
  simp_rw [martingalePart, process, Finset.sum_sub_distrib] at this
  exact sub_right_injective this
/-
**MeasureTheory.BorelCantelli.process_difference_le** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.BorelCantelli`。
形式化陈述：process_difference_le (s : Nat -> Set Ω) (ω : Ω) (n : Nat) : |process s (n
 + 1) ω - process s n ω| <= (1 : Real>=0)
参数：s : Nat -> Set Ω；ω : Ω；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `MeasureTheory.BorelCantelli.process.eq_1`：∀ {Ω : Type u_2} (s : ℕ → Set 
Ω) (n : ℕ),   MeasureTheory.BorelCantelli.process s n = ∑ k ∈ Finset.range n, (s
 (k + 1)).indicator 1
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_range_succ_sub_sum`：∀ {M : Type u_4} (f : ℕ → M) {n : ℕ} [ins
t : AddCommGroup M],   ∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range n, f
 i = f n
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `Set.indicator_le'`：∀ {α : Type u_2} {M : Type u_3} [inst : LE M] [inst_1
 : Zero M] {s : Set α} {f g : α → M},   (∀ a ∈ s, f a ≤ g a) → (∀ a ∉ s, 0 ≤ g a
) → s.i…
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem process_difference_le (s : ℕ → Set Ω) (ω : Ω) (n : ℕ) :
    |process s (n + 1) ω - process s n ω| ≤ (1 : ℝ≥0) := by
  norm_cast
  rw [process, process, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_range_succ_sub_sum, ← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
  refine Set.indicator_le' (fun _ _ => ?_) (fun _ _ => zero_le_one) _
  rw [Pi.one_apply, norm_one]
/-
**MeasureTheory.BorelCantelli.integrable_process** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.BorelCantelli`。
形式化陈述：integrable_process (μ : Measure Ω) [IsFiniteMeasure μ] (hs : forall n, Mea
surableSet[ℱ n] (s n)) (n : Nat) : Integrable (process s n) μ
参数：μ : Measure Ω；hs : forall n, MeasurableSet[ℱ n] (s n)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
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
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem integrable_process (μ : Measure Ω) [IsFiniteMeasure μ] (hs : ∀ n, MeasurableSet[ℱ n] (s n))
    (n : ℕ) : Integrable (process s n) μ :=
  integrable_finsetSum' _ fun _ _ =>
    IntegrableOn.integrable_indicator (integrable_const 1) <| ℱ.le _ _ <| hs _

end BorelCantelli

open BorelCantelli

/-- An a.e. monotone strongly adapted process `f` with uniformly bounded differences converges to
`+∞` if and only if its predictable part also converges to `+∞`. -/
/-
**MeasureTheory.tendsto_sum_indicator_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tendsto_sum_indicator_atTop_iff [IsFiniteMeasure μ] (hfmono : forallᵐ ω ∂μ
, forall n, f n ω <= f (n + 1) ω) (hf : StronglyAdapted ℱ f) (hint : forall n, I
ntegrable (f n) μ) (hbdd : forallᵐ ω ∂μ, forall n, |f (n + 1) ω - f n ω| <= R) :
 forallᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop atTop ↔ Tendsto (fun n => predicta
blePart f ℱ μ n ω) atTop atTop
参数：hfmono : forallᵐ ω ∂μ, forall n, f n ω <= f (n + 1) ω；hf : StronglyAdapted ℱ 
f；hint : forall n, Integrable (f n) μ；hbdd : forallᵐ ω ∂μ, forall n, |f (n + 1) 
ω - f n ω| <= R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.martingalePart_bdd_difference`：martingalePart_bdd_differen
ce [CompleteSpace E] {R : Real} {f : Nat -> Ω -> E} (ℱ : Filtration Nat m0) (hbd
d : forallᵐ ω ∂μ, forall i, ‖f (i…
· 使用定理 `MeasureTheory.Martingale.ae_not_tendsto_atTop_atTop`：∀ {Ω : Type u_2} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrati
on ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `MeasureTheory.martingale_martingalePart`：martingale_martingalePart [Comp
leteSpace E] (hf : StronglyAdapted ℱ f) (hf_int : forall n, Integrable (f n) μ) 
[SigmaFiniteFiltration μ ℱ] :…
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `MeasureTheory.Martingale.ae_not_tendsto_atTop_atBot`：∀ {Ω : Type u_2} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrati
on ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `MeasureTheory.condExp_nonneg`：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ
] μ[f | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone'`：tendsto_atTop_atTop_of_monotone
' [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u) (H : ¬BddAbove (ran
ge u)) : Tendsto u atTop atTo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_mono_set_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : A
ddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} [AddLeftMono N],   (∀ (x : ι),
 0 ≤ f x) → Monoton…
· 使用定理 `Finset.range_mono`：range_mono : Monotone range
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
An a.e. monotone strongly adapted process `f` with uniformly bounded differences
 converges to
`+∞` if and only if its predictable part also converges to `+∞`.
-/
theorem tendsto_sum_indicator_atTop_iff [IsFiniteMeasure μ]
    (hfmono : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ f (n + 1) ω) (hf : StronglyAdapted ℱ f)
    (hint : ∀ n, Integrable (f n) μ) (hbdd : ∀ᵐ ω ∂μ, ∀ n, |f (n + 1) ω - f n ω| ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop atTop ↔
      Tendsto (fun n => predictablePart f ℱ μ n ω) atTop atTop := by
  simp only [← Real.norm_eq_abs] at hbdd
  have h₀ := martingalePart_bdd_difference ℱ hbdd
  simp only [Real.norm_eq_abs, ← NNReal.coe_ofNat, ← NNReal.coe_mul 2 R] at h₀
  have h₁ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atTop h₀
  have h₂ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atBot h₀
  have h₃ : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ (μ[f (n + 1) - f n | ℱ n]) ω := by
    refine ae_all_iff.2 fun n => condExp_nonneg ?_
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄
  constructor <;> intro ht
  · refine tendsto_atTop_atTop_of_monotone' ?_ ?_
    · intro n m hnm
      simp only [predictablePart, Finset.sum_apply]
      exact Finset.sum_mono_set_of_nonneg hω₃ (Finset.range_mono hnm)
    rintro ⟨b, hbdd⟩
    rw [← tendsto_neg_atBot_iff] at ht
    simp only [martingalePart, sub_eq_add_neg] at hω₁
    exact hω₁ (tendsto_atTop_add_right_of_le _ (-b) (tendsto_neg_atBot_iff.1 ht) fun n =>
      neg_le_neg (hbdd ⟨n, rfl⟩))
  · refine tendsto_atTop_atTop_of_monotone' (monotone_nat_of_le_succ hω₄) ?_
    rintro ⟨b, hbdd⟩
    exact hω₂ ((tendsto_atBot_add_left_of_ge _ b fun n =>
      hbdd ⟨n, rfl⟩) <| tendsto_neg_atBot_iff.2 ht)

open BorelCantelli
/-
**MeasureTheory.tendsto_sum_indicator_atTop_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：tendsto_sum_indicator_atTop_iff' [IsFiniteMeasure μ] {s : Nat -> Set Ω} (h
s : forall n, MeasurableSet[ℱ n] (s n)) : forallᵐ ω ∂μ, Tendsto (fun n => ∑ k in
 Finset.range n, (s (k + 1)).indicator (1 : Ω -> Real) ω) atTop atTop ↔ Tendsto 
(fun n => ∑ k in Finset.range n, (μ[(s (k + 1)).indicator (1 : Ω -> Real) | ℱ k]
) ω) atTop atTop
参数：hs : forall n, MeasurableSet[ℱ n] (s n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_sum_indicator_atTop_iff`：tendsto_sum_indicator_atT
op_iff [IsFiniteMeasure μ] (hfmono : forallᵐ ω ∂μ, forall n, f n ω <= f (n + 1) 
ω) (hf : StronglyAdapted ℱ f) (hint…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.BorelCantelli.process.eq_1`：∀ {Ω : Type u_2} (s : ℕ → Set 
Ω) (n : ℕ),   MeasureTheory.BorelCantelli.process s n = ∑ k ∈ Finset.range n, (s
 (k + 1)).indicator 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_range_succ_sub_sum`：∀ {M : Type u_4} (f : ℕ → M) {n : ℕ} [ins
t : AddCommGroup M],   ∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range n, f
 i = f n
· 使用定理 `Set.indicator_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder M
] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ a ∈ s, 0 ≤ f a) → ∀ (a : α), 0
 ≤ s.indic…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `MeasureTheory.BorelCantelli.stronglyAdapted_process`：stronglyAdapted_pro
cess (hs : forall n, MeasurableSet[ℱ n] (s n)) : StronglyAdapted ℱ (process s)
· 使用定理 `MeasureTheory.BorelCantelli.integrable_process`：integrable_process (μ : 
Measure Ω) [IsFiniteMeasure μ] (hs : forall n, MeasurableSet[ℱ n] (s n)) (n : Na
t) : Integrable (process s n) μ
· 使用定理 `MeasureTheory.BorelCantelli.process_difference_le`：process_difference_le
 (s : Nat -> Set Ω) (ω : Ω) (n : Nat) : |process s (n + 1) ω - process s n ω| <=
 (1 : Real>=0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.BorelCantelli.predictablePart_process_ae_eq`：predictablePa
rt_process_ae_eq (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : Nat -> Set Ω) (n :
 Nat) : predictablePart (process s) ℱ μ n = ∑ k…
-/
theorem tendsto_sum_indicator_atTop_iff' [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) : ∀ᵐ ω ∂μ,
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      (s (k + 1)).indicator (1 : Ω → ℝ) ω) atTop atTop ↔
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω) atTop atTop := by
  have := tendsto_sum_indicator_atTop_iff (Eventually.of_forall fun ω n => ?_)
    (stronglyAdapted_process hs) (integrable_process μ hs)
    (Eventually.of_forall <| process_difference_le s)
  swap
  · rw [process, process, ← sub_nonneg, Finset.sum_apply, Finset.sum_apply,
      Finset.sum_range_succ_sub_sum]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  simp_rw [process, predictablePart_process_ae_eq] at this
  simpa using this

/-- **Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets `s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `limsup s atTop` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`. -/
/-
**MeasureTheory.ae_mem_limsup_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：ae_mem_limsup_atTop_iff (μ : Measure Ω) [IsFiniteMeasure μ] {s : Nat -> Se
t Ω} (hs : forall n, MeasurableSet[ℱ n] (s n)) : forallᵐ ω ∂μ, ω in limsup s atT
op ↔ Tendsto (fun n => ∑ k in Finset.range n, (μ[(s (k + 1)).indicator (1 : Ω ->
 Real) | ℱ k]) ω) atTop atTop
参数：μ : Measure Ω；hs : forall n, MeasurableSet[ℱ n] (s n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.limsup_nat_add`：limsup_nat_add (f : Nat -> α) (k : Nat) : limsup 
(fun i => f (i + k)) atTop = limsup f atTop
· 使用引理 `Set.limsup_eq_tendsto_sum_indicator_atTop`：limsup_eq_tendsto_sum_indicat
or_atTop {α R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
 [AddLeftStrictMono R] [Archime…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.tendsto_sum_indicator_atTop_iff'`：tendsto_sum_indicator_at
Top_iff' [IsFiniteMeasure μ] {s : Nat -> Set Ω} (hs : forall n, MeasurableSet[ℱ 
n] (s n)) : forallᵐ ω ∂μ, Tendsto (f…

--- 原说明 ---
**Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets 
`s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `limsup s atTop
` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`.
-/
theorem ae_mem_limsup_atTop_iff (μ : Measure Ω) [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) : ∀ᵐ ω ∂μ, ω ∈ limsup s atTop ↔
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω) atTop atTop := by
  rw [← limsup_nat_add s 1,
    Set.limsup_eq_tendsto_sum_indicator_atTop (zero_lt_one (α := ℝ)) (fun n ↦ s (n + 1))]
  exact tendsto_sum_indicator_atTop_iff' hs

end MeasureTheory

