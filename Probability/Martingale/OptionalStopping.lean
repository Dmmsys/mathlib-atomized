/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic

/-! # Optional stopping theorem (fair game theorem)

The optional stopping theorem states that a strongly adapted integrable process `f` is a
submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`.

This file also contains Doob's maximal inequality: given a non-negative submartingale `f`, for all
`ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f * n ω = max_{k ≤ n}, f k ω`.

### Main results

* `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`: the optional stopping theorem.
* `MeasureTheory.Submartingale.stoppedProcess`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `MeasureTheory.maximal_ineq`: Doob's maximal inequality.

-/

public section


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {τ π : Ω → ℕ∞}

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stoppedValue f τ` is less than or equal to the expectation of `stoppedValue f π`.
This is the forward direction of the optional stopping theorem. -/
/-
**MeasureTheory.Submartingale.expected_stoppedValue_mono** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   {τ π : Ω → ℕ∞} {E : Type u_2} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E]   [inst_3 : Partial
Order E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]   [M
easureTheory.SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Submart
ingale f 𝒢 μ →     MeasureTheory.IsStoppingTime 𝒢 τ →       MeasureTheory.IsStop
pingTime 𝒢 π →         τ ≤ π →           ∀ {N : ℕ},             (∀ (ω : Ω), π ω 
≤ ↑N) →               ∫ (x : Ω), MeasureTheory.stoppedValue f τ x ∂μ ≤ ∫ (x : Ω)
, MeasureTheory.stoppedValue f π x ∂μ
参数：∀ (ω : Ω), π ω ≤ ↑N；x : Ω；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Submartingale.integrable_stoppedValue`：∀ {Ω : Type u_1} {E
 : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Norm
edAddCommGroup E]   [inst_1 : NormedSpace…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.stoppedValue_sub_eq_sum'`：stoppedValue_sub_eq_sum' [AddCom
mGroup β] (hle : τ <= π) {N : Nat} (hbdd : forall ω, π ω <= N) : stoppedValue u 
π - stoppedValue u τ = fun ω…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Submartingale.setIntegral_le`：setIntegral_le [PartialOrder
 E] [IsOrderedAddMonoid E] [IsOrderedModule Real E] [ClosedIciTopology E] [Sigma
FiniteFiltration μ ℱ] {f : ι -> …
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ 
π`, the
expectation of `stoppedValue f τ` is less than or equal to the expectation of `s
toppedValue f π`.
This is the forward direction of the optional stopping theorem.
-/
theorem Submartingale.expected_stoppedValue_mono {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) : μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := by
  rw [← sub_nonneg, ← integral_sub', stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have : ∀ i, MeasurableSet[𝒢 i] {ω : Ω | τ ω ≤ i ∧ i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert! (hπ i).compl using 1
      ext x
      simp; rfl
    rw [integral_finsetSum]
    · refine Finset.sum_nonneg fun i _ => ?_
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg]
      · exact hf.setIntegral_le (Nat.le_succ i) (this _)
      · exact (hf.integrable _).integrableOn
      · exact (hf.integrable _).integrableOn
    intro i _
    exact Integrable.indicator (Integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ _ (this _))
  · exact hf.integrable_stoppedValue hπ hbdd
  · exact hf.integrable_stoppedValue hτ fun ω => le_trans (hle ω) (hbdd ω)

set_option backward.isDefEq.respectTransparency false in
/-- The converse direction of the optional stopping theorem, i.e. a strongly adapted integrable
process `f` is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
/-
**MeasureTheory.submartingale_of_expected_stoppedValue_mono** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：submartingale_of_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢] (h
adp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf : forall τ 
π : Ω -> Nat∞, IsStoppingTime 𝒢 τ -> IsStoppingTime 𝒢 π -> τ <= π -> (exists N :
 Nat, forall ω, π ω <= N) -> μ[stoppedValue f τ] <= μ[stoppedValue f π]) : Subma
rtingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall τ 
π : Ω -> Nat∞, IsStoppingTime 𝒢 τ -> IsStoppingTime 𝒢 π -> τ <= π -> (exists N :
 Nat, forall ω, π ω <= N) -> μ[stoppedValue f τ] <= μ[stoppedValue f π]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.submartingale_of_setIntegral_le`：submartingale_of_setInteg
ral_le [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> Real} (hadp : StronglyAdapted 
ℱ f) (hint : forall i, Integrable (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.integral_piecewise`：integral_piecewise [DecidablePred (· i
n s)] (hs : MeasurableSet s) (hf : IntegrableOn f s μ) (hg : IntegrableOn g sᶜ μ
) : ∫ x, s.piecewise f…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.stoppedValue_piecewise_const`：stoppedValue_piecewise_const
 {ι' α : Type*} [Nonempty ι'] {i j : ι'} {f : ι' -> Ω -> α} : stoppedValue f (s.
piecewise (fun _ => i) fun _ => …
· 使用定理 `ENat.some_eq_natCast`：WithTop.some = Nat.cast
· 使用定理 `MeasureTheory.stoppedValue_const`：stoppedValue_const (u : ι -> Ω -> β) (
i : ι) : (stoppedValue u fun _ => i) = u i
· 使用定理 `MeasureTheory.isStoppingTime_piecewise_const`：isStoppingTime_piecewise_c
onst (hij : i <= j) (hs : MeasurableSet[𝒢 i] s) : IsStoppingTime 𝒢 (s.piecewise 
(fun _ => i) fun _ => j)
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The converse direction of the optional stopping theorem, i.e. a strongly adapted
 integrable
process `f` is a submartingale if for all bounded stopping times `τ` and `π` suc
h that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π
`.
-/
theorem submartingale_of_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π]) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  classical
  specialize hf (s.piecewise (fun _ => i) fun _ => j) _ (isStoppingTime_piecewise_const hij hs)
    (isStoppingTime_const 𝒢 j) ?_
    ⟨j, fun _ => le_rfl⟩
  · intro ω
    simp only [Set.piecewise, ENat.some_eq_natCast]
    split_ifs with hω
    · exact mod_cast hij
    · norm_cast
  · rwa [stoppedValue_const, ← ENat.some_eq_natCast, stoppedValue_piecewise_const,
      integral_piecewise (𝒢.le _ _ hs) (hint _).integrableOn (hint _).integrableOn, ←
      integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf

/-- **The optional stopping theorem** (fair game theorem): a strongly adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
/-
**MeasureTheory.submartingale_iff_expected_stoppedValue_mono** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：submartingale_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢] (
hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) : Submartingal
e f 𝒢 μ ↔ forall τ π : Ω -> Nat∞, IsStoppingTime 𝒢 τ -> IsStoppingTime 𝒢 π -> τ 
<= π -> (exists N : Nat, forall x, π x <= N) -> μ[stoppedValue f τ] <= μ[stopped
Value f π]
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.Submartingale.expected_stoppedValue_mono`：∀ {Ω : Type u_1}
 {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢 : MeasureTheory.Filtr
ation ℕ m0}   {τ π : Ω → ℕ∞} {E : Type u_2} …
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
· 使用定理 `MeasureTheory.submartingale_of_expected_stoppedValue_mono`：submartingale
_of_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢] (hadp : StronglyAdapt
ed 𝒢 f) (hint : forall i, Integrable (f i) μ) (…

--- 原说明 ---
**The optional stopping theorem** (fair game theorem): a strongly adapted integr
able process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` suc
h that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π
`.
-/
theorem submartingale_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

set_option backward.isDefEq.respectTransparency false in
/-- The stopped process of a submartingale with respect to a stopping time is a submartingale. -/
/-
**MeasureTheory.Submartingale.stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {τ : Ω → ℕ∞} [MeasureTheory.
SigmaFiniteFiltration μ 𝒢],   MeasureTheory.Submartingale f 𝒢 μ →     MeasureThe
ory.IsStoppingTime 𝒢 τ → MeasureTheory.Submartingale (MeasureTheory.stoppedProce
ss f τ) 𝒢 μ
参数：MeasureTheory.stoppedProcess f τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`：submartingal
e_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢] (hadp : StronglyAda
pted 𝒢 f) (hint : forall i, Integrable (f i) μ) …
· 使用定理 `MeasureTheory.StronglyAdapted.stoppedProcess_of_discrete`：∀ {Ω : Type u_
1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : TopologicalSpac
e β]   [TopologicalSpace.PseudoMetrizableSpace…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.Countable.to_separableSpace`：∀ {α : Type u} [t : Topolo
gicalSpace α] [Countable α], TopologicalSpace.SeparableSpace α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.integrable_stoppedValue`：∀ {Ω : Type u_1} {E
 : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Norm
edAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.stoppedValue_stoppedProcess`：stoppedValue_stoppedProcess :
 stoppedValue (stoppedProcess u τ) σ = fun ω => if σ ω != ⊤ then stoppedValue u 
(fun ω => min (σ ω) (τ ω)) ω el…
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The stopped process of a submartingale with respect to a stopping time is a subm
artingale.
-/
protected theorem Submartingale.stoppedProcess [SigmaFiniteFiltration μ 𝒢]
    (h : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) :
    Submartingale (stoppedProcess f τ) 𝒢 μ := by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (hσ_le_π ω)
    simp only [ne_eq, hσ_top, not_false_eq_true, ↓reduceIte, hπ_top, ge_iff_le]
    exact h.expected_stoppedValue_mono (hσ.min hτ) (hπ.min hτ)
      (fun ω => min_le_min (hσ_le_π ω) le_rfl) fun ω => (min_le_left _ _).trans (hπ_le_n ω)
  · exact StronglyAdapted.stoppedProcess_of_discrete h.stronglyAdapted hτ
  · exact fun i =>
      h.integrable_stoppedValue ((isStoppingTime_const _ i).min hτ) fun ω => min_le_left _ _

section Maximal

open Finset

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.smul_le_stoppedValue_hittingBtwn** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale
 f 𝒢 μ) {ε : Real>=0} (n : Nat) : ε • μ {ω | (ε : Real) <= (range (n + 1)).sup' 
nonempty_range_add_one fun k => f k ω} <= ENNReal.ofReal (∫ ω in {ω | (ε : Real)
 <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, stoppedValue f 
(fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω ∂μ)
参数：hsub : Submartingale f 𝒢 μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.stoppedValue_hittingBtwn_mem`：stoppedValue_hittingBtwn_mem
 [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι] {u : ι -> Ω -> β} {s : S
et β} {n m : ι} {ω : Ω} (h : exi…
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.setIntegral_ge_of_const_le_real`：setIntegral_ge_of_const_l
e_real {f : X -> Real} {c : Real} (hs : MeasurableSet s) (hμs : μ s != ∞) (hf : 
forall x in s, c <= f x) (hfint : I…
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Finset.measurable_range_sup''`：Finset.measurable_range_sup'' {f : Nat ->
 δ -> α} {n : Nat} (hf : forall k <= n, Measurable (f k)) : Measurable fun x => 
(range (n + 1)).sup…
· 使用定理 `ContinuousSup.measurableSup₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] {mγ : MeasurableSpace γ} [BorelSpace γ] [SecondCountableTopology γ]   [inst_3
 : Max γ] [Continu…
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `Measurable.le`：Measurable.le {α} {m m0 : MeasurableSpace α} {_ : Measura
bleSpace β} (hm : m <= m0) {f : α -> β} (hf : Measurable[m] f) : Measurable[m0] 
f
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Submartingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Submartingale.integrable_stoppedValue`：∀ {Ω : Type u_1} {E
 : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Norm
edAddCommGroup E]   [inst_1 : NormedSpace…
（共 53 条，此处仅展示前 30 条）
-/
theorem smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : ℝ≥0}
    (n : ℕ) : ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have : ∀ ω, ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) →
      (ε : ℝ) ≤ stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_ofPred_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ => (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this (Integrable.integrableOn (hsub.integrable_stoppedValue
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (mod_cast hittingBtwn_le)))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

set_option backward.isDefEq.respectTransparency false in
/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's Lp inequality
(which is a corollary of this lemma and will be proved in an upcoming PR). -/
/-
**MeasureTheory.maximal_ineq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0
 <= f) {ε : Real>=0} (n : Nat) : ε * μ {ω | (ε : Real) <= (range (n + 1)).sup' n
onempty_range_add_one fun k => f k ω} <= ENNReal.ofReal (∫ ω in {ω | (ε : Real) 
<= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, f n ω ∂μ)
参数：hsub : Submartingale f 𝒢 μ；hnonneg : 0 <= f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.smul_le_stoppedValue_hittingBtwn`：smul_le_stoppedValue_hit
tingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : Real>=0} (n : Nat
) : ε • μ {ω | (ε : Real) <= (range …
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `MeasureTheory.setIntegral_mono_on₀`：setIntegral_mono_on₀ (hs : NullMeasu
rableSet s μ) (h : forall x in s, f x <= g x) : ∫ x in s, f x ∂μ <= ∫ x in s, g 
x ∂μ
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
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.integrable_stoppedValue`：∀ {Ω : Type u_1} {E
 : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Norm
edAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`：∀ {Ω : Type u_1} {β : 
Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : ConditionallyCompleteLi
nearOrder ι]   [WellFoundedLT ι] [Coun…
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.StronglyAdapted.adapted`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   
{β : ι → Type u_3} [inst_1 …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
**Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `
ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n},
 f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's 
Lp inequality
(which is a corollary of this lemma and will be proved in an upcoming PR).
-/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0}
    (n : ℕ) : ε * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
        f n ω ∂μ) := by
  suffices ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) ≤
      ENNReal.ofReal (μ[f n]) by
    have hadd : ENNReal.ofReal (∫ ω, f n ω ∂μ) =
      ENNReal.ofReal
        (∫ ω in {ω | ε ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, f n ω ∂μ) +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ]
        convert! rfl
        ext ω
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      exacts [(hsub.integrable _).integrableOn, (hsub.integrable _).integrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this
  calc
    _ ≤ ENNReal.ofReal
          (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      gcongr with ω hω
      · exact smul_le_stoppedValue_hittingBtwn hsub n
      · exact (hsub.integrable n).integrableOn
      · refine Integrable.integrableOn ?_
        refine hsub.integrable_stoppedValue ?_ (fun ω ↦ mod_cast hittingBtwn_le ω)
        exact hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
      · exact nullMeasurableSet_lt (measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable aemeasurable_const
      rw [Set.mem_ofPred_eq] at hω
      have : hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω = n := by
        simp only [hittingBtwn, Set.mem_ofPred_eq, ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact False.elim
          ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp only [stoppedValue, this, ge_iff_le]
      refine le_of_eq ?_
      congr
    _ = ENNReal.ofReal
        (∫ ω, stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ (μ := μ)]
        convert! rfl
        ext ω
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ)
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω ↦ mod_cast hittingBtwn_le ω))
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω ↦ mod_cast hittingBtwn_le ω))
      exacts [integral_nonneg fun x => hnonneg _ _, integral_nonneg fun x => hnonneg _ _]
    _ ≤ ENNReal.ofReal (μ[f n]) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f n]
      refine hsub.expected_stoppedValue_mono
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (isStoppingTime_const _ _) (fun ω ↦ ?_) (fun _ => mod_cast le_rfl)
      simp [hittingBtwn_le]

end Maximal

end MeasureTheory

