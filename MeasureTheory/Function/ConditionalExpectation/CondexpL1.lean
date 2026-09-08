/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

The conditional expectation of an `L²` function is defined in
`MeasureTheory.Function.ConditionalExpectation.CondexpL2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).

## Main definitions

* `condExpL1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/

@[expose] public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α F F' G G' 𝕜 : Type*} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F']
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condExpInd (hm : m ≤ m0) (μ : Measure α) (s : Set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin


/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
/-
**MeasureTheory.condExpIndL1Fin** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1Fin (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableS
et s) (hμs : μ s != ∞) (x : G) : α ->₁[μ] G
参数：hm : m <= m0；μ.trim hm；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_condExpIndSMul`：integrable_condExpIndSMul (hm :
 m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞) (x :
 G) : Integrable (condExpIndS…

--- 原说明 ---
Conditional expectation of the indicator of a measurable set with finite measure
,
as a function in L1.
-/
def condExpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condExpIndSMul hm hs hμs x).toL1 _
/-
**MeasureTheory.condExpIndL1Fin_ae_eq_condExpIndSMul** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：condExpIndL1Fin_ae_eq_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim h
m)] (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : condExpIndL1Fin hm hs hμs 
x =ᵐ[μ] condExpIndSMul hm hs hμs x
参数：hm : m <= m0；μ.trim hm；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.integrable_condExpIndSMul`：integrable_condExpIndSMul (hm :
 m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞) (x :
 G) : Integrable (condExpIndS…
-/
theorem condExpIndL1Fin_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpIndL1Fin hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

-- Porting note: this lemma fills the hole in `refine' (MemLp.coeFn_toLp _) ...`
-- which is not automatically filled in Lean 4
/-
**MeasureTheory.q** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem q {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {x : G} :
    MemLp (condExpIndSMul hm hs hμs x) 1 μ := by
  rw [memLp_one_iff_integrable]; apply integrable_condExpIndSMul
/-
**MeasureTheory.condExpIndL1Fin_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G) : co
ndExpIndL1Fin hm hs hμs (x + y) = condExpIndL1Fin hm hs hμs x + condExpIndL1Fin 
hm hs hμs y
参数：hs : MeasurableSet s；hμs : μ s != ∞；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integrable_condExpIndSMul`：integrable_condExpIndSMul (hm :
 m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞) (x :
 G) : Integrable (condExpIndS…
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndSMul_add`：condExpIndSMul_add (hs : MeasurableSet
 s) (hμs : μ s != ∞) (x y : G) : condExpIndSMul hm hs hμs (x + y) = condExpIndSM
ul hm hs hμs x + condE…
-/
theorem condExpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condExpIndL1Fin hm hs hμs (x + y) =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm hs hμs y := by
  ext1
  unfold condExpIndL1Fin Integrable.toL1
  grw [Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp, MemLp.coeFn_toLp, condExpIndSMul_add,
    Lp.coeFn_add]
/-
**MeasureTheory.condExpIndL1Fin_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s != ∞) (c : Real) (x
 : G) : condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : Real；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.condExpIndL1Fin_ae_eq_condExpIndSMul`：condExpIndL1Fin_ae_e
q_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
 (hμs : μ s != ∞) (x : G) : condExpIndL1…
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndSMul_smul`：condExpIndSMul_smul [NormedSpace Real
 F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s) (hμs : μ s != ∞) (c : 𝕜) (x 
: F) : condExpIndSMul h…
-/
theorem condExpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]
/-
**MeasureTheory.condExpIndL1Fin_smul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1Fin_smul' [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (hs : 
MeasurableSet s) (hμs : μ s != ∞) (c : 𝕜) (x : F) : condExpIndL1Fin hm hs hμs (c
 • x) = c • condExpIndL1Fin hm hs hμs x
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : 𝕜；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.condExpIndL1Fin_ae_eq_condExpIndSMul`：condExpIndL1Fin_ae_e
q_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
 (hμs : μ s != ∞) (x : G) : condExpIndL1…
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndSMul_smul`：condExpIndSMul_smul [NormedSpace Real
 F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s) (hμs : μ s != ∞) (c : 𝕜) (x 
: F) : condExpIndSMul h…
-/
theorem condExpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]
/-
**MeasureTheory.norm_condExpIndL1Fin_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：norm_condExpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : 
‖condExpIndL1Fin hm hs hμs x‖ <= μ.real s * ‖x‖
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.norm_eq_integral_norm`：∀ {α : Type u_1} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {H : Type u_6} [inst : NormedAddCommGroup
 H]   (f : ↥(MeasureTheory.L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.ofReal_le_iff_le_toReal`：ofReal_le_iff_le_toReal {a : Real} {b :
 Real>=0∞} (hb : b != ∞) : ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`：ofReal_integral_n
orm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P} (hf : Int
egrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂…
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpIndL1Fin_ae_eq_condExpIndSMul`：condExpIndL1Fin_ae_e
q_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
 (hμs : μ s != ∞) (x : G) : condExpIndL1…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `MeasureTheory.lintegral_nnnorm_condExpIndSMul_le`：lintegral_nnnorm_condE
xpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) [Sig
maFinite (μ.trim hm)] : ∫⁻ a, ‖condExp…
-/
theorem norm_condExpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condExpIndL1Fin hm hs hμs x‖ ≤ μ.real s * ‖x‖ := by
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), measureReal_def,
    ← ENNReal.toReal_mul,
    ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_enorm]
  swap; · rw [← memLp_one_iff_integrable]; exact Lp.memLp _
  have h_eq :
    ∫⁻ a, ‖condExpIndL1Fin hm hs hμs x a‖ₑ ∂μ = ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x] with z hz
    rw [hz]
  rw [h_eq, ofReal_norm]
  exact lintegral_nnnorm_condExpIndSMul_le hm hs hμs x
/-
**MeasureTheory.condExpIndL1Fin_disjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：condExpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet 
t) (hμs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) (x : G) : condExpIndL1
Fin hm (hs.union ht) ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (EN
NReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x = condExpIndL1Fin hm hs hμs x + condExpI
ndL1Fin hm ht hμt x
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；hst :
 Disjoint s t；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.condExpIndL1Fin_ae_eq_condExpIndSMul`：condExpIndL1Fin_ae_e
q_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
 (hμs : μ s != ∞) (x : G) : condExpIndL1…
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndSMul.eq_1`：∀ {α : Type u_1} {G : Type u_5} [inst
 : NormedAddCommGroup G] {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   {s : Set α} [inst_1…
· 使用定理 `MeasureTheory.indicatorConstLp_disjoint_union`：indicatorConstLp_disjoint
_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s !=
 ∞) (hμt : μ t != ∞) (hst : Disjoin…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem condExpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm ht hμt x := by
  ext1
  grw [Lp.coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndL1Fin_ae_eq_condExpIndSMul]
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [map_add]
  push_cast
  rw [map_add]
  grw [Lp.coeFn_add]
  rfl

end CondexpIndL1Fin

section CondexpIndL1


open scoped Classical in
/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
/-
**MeasureTheory.condExpIndL1** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1 {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) (s 
: Set α) [SigmaFinite (μ.trim hm)] (x : G) : α ->₁[μ] G
参数：hm : m <= m0；μ : Measure α；s : Set α；μ.trim hm；x : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditional expectation of the indicator of a set, as a function in L1. Its valu
e for sets
which are not both measurable and of finite measure is not used: we set it to 0.
-/
def condExpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condExpIndL1Fin hm hs.1 hs.2 x else 0

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
/-
**MeasureTheory.condExpIndL1_of_measurableSet_of_measure_ne_top** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμ
s : μ s != ∞) (x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm hs hμs x
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condExpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm hs hμs x := by
  simp only [condExpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]
/-
**MeasureTheory.condExpIndL1_of_measure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：condExpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ
 s x = 0
参数：hμs : μ s = ∞；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem condExpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hμs, not_true, Ne, dif_neg, not_false_iff,
    and_false]
/-
**MeasureTheory.condExpIndL1_of_not_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：condExpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) : condEx
pIndL1 hm μ s x = 0
参数：hs : ¬MeasurableSet s；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condExpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hs, dif_neg, not_false_iff, false_and]
/-
**MeasureTheory.condExpIndL1_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1_add (x y : G) : condExpIndL1 hm μ s (x + y) = condExpIndL1 hm
 μ s x + condExpIndL1 hm μ s y
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndL1_of_measure_eq_top`：condExpIndL1_of_measure_eq
_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.condExpIndL1_of_measurableSet_of_measure_ne_top`：condExpIn
dL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s != ∞) (
x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm…
· 使用定理 `MeasureTheory.condExpIndL1Fin_add`：condExpIndL1Fin_add (hs : MeasurableS
et s) (hμs : μ s != ∞) (x y : G) : condExpIndL1Fin hm hs hμs (x + y) = condExpIn
dL1Fin hm hs hμs x + co…
· 使用定理 `MeasureTheory.condExpIndL1_of_not_measurableSet`：condExpIndL1_of_not_mea
surableSet (hs : ¬MeasurableSet s) (x : G) : condExpIndL1 hm μ s x = 0
-/
theorem condExpIndL1_add (x y : G) :
    condExpIndL1 hm μ s (x + y) = condExpIndL1 hm μ s x + condExpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_add hs hμs x y
/-
**MeasureTheory.condExpIndL1_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1_smul (c : Real) (x : G) : condExpIndL1 hm μ s (c • x) = c • c
ondExpIndL1 hm μ s x
参数：c : Real；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndL1_of_measure_eq_top`：condExpIndL1_of_measure_eq
_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.condExpIndL1_of_measurableSet_of_measure_ne_top`：condExpIn
dL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s != ∞) (
x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm…
· 使用定理 `MeasureTheory.condExpIndL1Fin_smul`：condExpIndL1Fin_smul (hs : Measurabl
eSet s) (hμs : μ s != ∞) (c : Real) (x : G) : condExpIndL1Fin hm hs hμs (c • x) 
= c • condExpIndL1Fin hm…
· 使用定理 `MeasureTheory.condExpIndL1_of_not_measurableSet`：condExpIndL1_of_not_mea
surableSet (hs : ¬MeasurableSet s) (x : G) : condExpIndL1 hm μ s x = 0
-/
theorem condExpIndL1_smul (c : ℝ) (x : G) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul hs hμs c x
/-
**MeasureTheory.condExpIndL1_smul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndL1_smul' [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (
x : F) : condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x
参数：c : 𝕜；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndL1_of_measure_eq_top`：condExpIndL1_of_measure_eq
_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.condExpIndL1_of_measurableSet_of_measure_ne_top`：condExpIn
dL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s != ∞) (
x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm…
· 使用定理 `MeasureTheory.condExpIndL1Fin_smul'`：condExpIndL1Fin_smul' [NormedSpace 
Real F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s) (hμs : μ s != ∞) (c : 𝕜)
 (x : F) : condExpIndL1Fi…
· 使用定理 `MeasureTheory.condExpIndL1_of_not_measurableSet`：condExpIndL1_of_not_mea
surableSet (hs : ¬MeasurableSet s) (x : G) : condExpIndL1 hm μ s x = 0
-/
theorem condExpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul' hs hμs c x
/-
**MeasureTheory.norm_condExpIndL1_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_condExpIndL1_le (x : G) : ‖condExpIndL1 hm μ s x‖ <= μ.real s * ‖x‖
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndL1_of_measure_eq_top`：condExpIndL1_of_measure_eq
_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0
· 使用定理 `MeasureTheory.Lp.norm_zero`：norm_zero : ‖(0 : Lp E p μ)‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.condExpIndL1_of_measurableSet_of_measure_ne_top`：condExpIn
dL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s != ∞) (
x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm…
· 使用定理 `MeasureTheory.norm_condExpIndL1Fin_le`：norm_condExpIndL1Fin_le (hs : Mea
surableSet s) (hμs : μ s != ∞) (x : G) : ‖condExpIndL1Fin hm hs hμs x‖ <= μ.real
 s * ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.condExpIndL1_of_not_measurableSet`：condExpIndL1_of_not_mea
surableSet (hs : ¬MeasurableSet s) (x : G) : condExpIndL1 hm μ s x = 0
-/
theorem norm_condExpIndL1_le (x : G) : ‖condExpIndL1 hm μ s x‖ ≤ μ.real s * ‖x‖ := by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condExpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    exact norm_condExpIndL1Fin_le hs hμs x
/-
**MeasureTheory.continuous_condExpIndL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：continuous_condExpIndL1 : Continuous fun x : G => condExpIndL1 hm μ s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_linear_of_bound`：continuous_of_linear_of_bound {f : E -> G
} (h_add : forall x y, f (x + y) = f x + f y) (h_smul : forall (c : 𝕜) (x), f (c
 • x) = c • f x) {C…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.condExpIndL1_add`：condExpIndL1_add (x y : G) : condExpIndL
1 hm μ s (x + y) = condExpIndL1 hm μ s x + condExpIndL1 hm μ s y
· 使用定理 `MeasureTheory.condExpIndL1_smul`：condExpIndL1_smul (c : Real) (x : G) : 
condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x
· 使用定理 `MeasureTheory.norm_condExpIndL1_le`：norm_condExpIndL1_le (x : G) : ‖cond
ExpIndL1 hm μ s x‖ <= μ.real s * ‖x‖
-/
theorem continuous_condExpIndL1 : Continuous fun x : G => condExpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condExpIndL1_add condExpIndL1_smul norm_condExpIndL1_le
/-
**MeasureTheory.condExpIndL1_disjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：condExpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) 
(hμs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) (x : G) : condExpIndL1 hm
 μ (s union t) x = condExpIndL1 hm μ s x + condExpIndL1 hm μ t x
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；hst :
 Disjoint s t；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndL1_of_measurableSet_of_measure_ne_top`：condExpIn
dL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s != ∞) (
x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm…
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.condExpIndL1Fin_disjoint_union`：condExpIndL1Fin_disjoint_u
nion (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t !
= ∞) (hst : Disjoint s t) (x : G) …
-/
theorem condExpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1 hm μ (s ∪ t) x = condExpIndL1 hm μ s x + condExpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x,
    condExpIndL1_of_measurableSet_of_measure_ne_top ht hμt x,
    condExpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condExpIndL1Fin_disjoint_union hs ht hμs hμt hst x

end CondexpIndL1

variable (G)

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
/-
**MeasureTheory.condExpInd** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpInd {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) [Sigm
aFinite (μ.trim hm)] (s : Set α) : G ->L[Real] α ->₁[μ] G where toFun
参数：hm : m <= m0；μ : Measure α；μ.trim hm；s : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.condExpIndL1_add`：condExpIndL1_add (x y : G) : condExpIndL
1 hm μ s (x + y) = condExpIndL1 hm μ s x + condExpIndL1 hm μ s y
· 使用定理 `MeasureTheory.condExpIndL1_smul`：condExpIndL1_smul (c : Real) (x : G) : 
condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x
· 使用定理 `MeasureTheory.continuous_condExpIndL1`：continuous_condExpIndL1 : Continu
ous fun x : G => condExpIndL1 hm μ s x

--- 原说明 ---
Conditional expectation of the indicator of a set, as a linear map from `G` to L
1.
-/
def condExpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G →L[ℝ] α →₁[μ] G where
  toFun := condExpIndL1 hm μ s
  map_add' := condExpIndL1_add
  map_smul' := condExpIndL1_smul
  cont := continuous_condExpIndL1

variable {G}
/-
**MeasureTheory.condExpInd_ae_eq_condExpIndSMul** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：condExpInd_ae_eq_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (
hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : condExpInd G hm μ s x =ᵐ[μ] con
dExpIndSMul hm hs hμs x
参数：hm : m <= m0；μ.trim hm；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExpIndL1Fin_ae_eq_condExpIndSMul`：condExpIndL1Fin_ae_e
q_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
 (hμs : μ s != ∞) (x : G) : condExpIndL1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
theorem condExpInd_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpInd G hm μ s x =ᵐ[μ] condExpIndSMul hm hs hμs x := by
  grw [← condExpIndL1Fin_ae_eq_condExpIndSMul]
  simp [condExpInd, condExpIndL1, hs, hμs]

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
/-
**MeasureTheory.aestronglyMeasurable_condExpInd** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：aestronglyMeasurable_condExpInd (hs : MeasurableSet s) (hμs : μ s != ∞) (x
 : G) : AEStronglyMeasurable[m] (condExpInd G hm μ s x) μ
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpIndSMul`：aestronglyMeasurable_
condExpIndSMul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : 
AEStronglyMeasurable[m] (condExpIndSMul…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpInd_ae_eq_condExpIndSMul`：condExpInd_ae_eq_condExpI
ndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ 
s != ∞) (x : G) : condExpInd G hm μ…
-/
theorem aestronglyMeasurable_condExpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable[m] (condExpInd G hm μ s x) μ :=
  (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm

@[simp]
/-
**MeasureTheory.condExpInd_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpInd_empty : condExpInd G hm μ ∅ = (0 : G ->L[Real] α ->₁[μ] G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.condExpInd_ae_eq_condExpIndSMul`：condExpInd_ae_eq_condExpI
ndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ 
s != ∞) (x : G) : condExpInd G hm μ…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `MeasureTheory.condExpIndSMul_empty`：condExpIndSMul_empty {x : G} : condE
xpIndSMul hm MeasurableSet.empty ((measure_empty (μ
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem condExpInd_empty : condExpInd G hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext x
  grw [condExpInd_ae_eq_condExpIndSMul hm MeasurableSet.empty (by simp), condExpIndSMul_empty,
    zero_apply, Lp.coeFn_zero, Lp.coeFn_zero]
/-
**MeasureTheory.condExpInd_smul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpInd_smul' [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (x 
: F) : condExpInd F hm μ s (c • x) = c • condExpInd F hm μ s x
参数：c : 𝕜；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExpIndL1_smul'`：condExpIndL1_smul' [NormedSpace Real F
] [SMulCommClass Real 𝕜 F] (c : 𝕜) (x : F) : condExpIndL1 hm μ s (c • x) = c • c
ondExpIndL1 hm μ s x
-/
theorem condExpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condExpInd F hm μ s (c • x) = c • condExpInd F hm μ s x :=
  condExpIndL1_smul' c x
/-
**MeasureTheory.norm_condExpInd_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：norm_condExpInd_apply_le (x : G) : ‖condExpInd G hm μ s x‖ <= μ.real s * ‖
x‖
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.norm_condExpIndL1_le`：norm_condExpIndL1_le (x : G) : ‖cond
ExpIndL1 hm μ s x‖ <= μ.real s * ‖x‖
-/
theorem norm_condExpInd_apply_le (x : G) : ‖condExpInd G hm μ s x‖ ≤ μ.real s * ‖x‖ :=
  norm_condExpIndL1_le x
/-
**MeasureTheory.norm_condExpInd_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_condExpInd_le : ‖(condExpInd G hm μ s : G ->L[Real] α ->₁[μ] G)‖ <= μ
.real s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.norm_condExpInd_apply_le`：norm_condExpInd_apply_le (x : G)
 : ‖condExpInd G hm μ s x‖ <= μ.real s * ‖x‖
-/
theorem norm_condExpInd_le : ‖(condExpInd G hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ μ.real s :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg norm_condExpInd_apply_le
/-
**MeasureTheory.condExpInd_disjoint_union_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：condExpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet
 t) (hμs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) (x : G) : condExpInd 
G hm μ (s union t) x = condExpInd G hm μ s x + condExpInd G hm μ t x
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；hst :
 Disjoint s t；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExpIndL1_disjoint_union`：condExpIndL1_disjoint_union (
hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t != ∞) (
hst : Disjoint s t) (x : G) : c…
-/
theorem condExpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpInd G hm μ (s ∪ t) x = condExpInd G hm μ s x + condExpInd G hm μ t x :=
  condExpIndL1_disjoint_union hs ht hμs hμt hst x
/-
**MeasureTheory.condExpInd_disjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：condExpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (h
μs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) : (condExpInd G hm μ (s uni
on t) : G ->L[Real] α ->₁[μ] G) = condExpInd G hm μ s + condExpInd G hm μ t
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；hst :
 Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `MeasureTheory.condExpInd_disjoint_union_apply`：condExpInd_disjoint_union
_apply (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t
 != ∞) (hst : Disjoint s t) (x : G)…
-/
theorem condExpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) : (condExpInd G hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) =
    condExpInd G hm μ s + condExpInd G hm μ t := by
  ext1 x; push_cast; exact condExpInd_disjoint_union_apply hs ht hμs hμt hst x

variable (G)
/-
**MeasureTheory.dominatedFinMeasAdditive_condExpInd** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：dominatedFinMeasAdditive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaF
inite (μ.trim hm)] : DominatedFinMeasAdditive μ (condExpInd G hm μ : Set α -> G 
->L[Real] α ->₁[μ] G) 1
参数：hm : m <= m0；μ : Measure α；μ.trim hm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.condExpInd_disjoint_union`：condExpInd_disjoint_union (hs :
 MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t != ∞) (hst 
: Disjoint s t) : (condExpInd…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.norm_condExpInd_le`：norm_condExpInd_le : ‖(condExpInd G hm
 μ s : G ->L[Real] α ->₁[μ] G)‖ <= μ.real s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem dominatedFinMeasAdditive_condExpInd (hm : m ≤ m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condExpInd G hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun _ _ => condExpInd_disjoint_union, fun _ _ _ => norm_condExpInd_le.trans (one_mul _).symm.le⟩

variable {G}
/-
**MeasureTheory.setIntegral_condExpInd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setIntegral_condExpInd (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (h
μs : μ s != ∞) (hμt : μ t != ∞) (x : G') : ∫ a in s, condExpInd G' hm μ t x a ∂μ
 = μ.real (t inter s) • x
参数：hs : MeasurableSet[m] s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；x 
: G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpInd_ae_eq_condExpIndSMul`：condExpInd_ae_eq_condExpI
ndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ 
s != ∞) (x : G) : condExpInd G hm μ…
· 使用定理 `MeasureTheory.setIntegral_condExpIndSMul`：setIntegral_condExpIndSMul (hs
 : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t != ∞) 
(x : G') : ∫ a in s, (condExpI…
-/
theorem setIntegral_condExpInd (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : ∫ a in s, condExpInd G' hm μ t x a ∂μ = μ.real (t ∩ s) • x :=
  calc
    ∫ a in s, condExpInd G' hm μ t x a ∂μ = ∫ a in s, condExpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpInd_ae_eq_condExpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = μ.real (t ∩ s) • x := setIntegral_condExpIndSMul hs ht hμs hμt x
/-
**MeasureTheory.condExpInd_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：condExpInd_of_measurable (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : G
) : condExpInd G hm μ s c = indicatorConstLp 1 (hm s hs) hμs c
参数：hs : MeasurableSet[m] s；hμs : μ s != ∞；c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.condExpInd_ae_eq_condExpIndSMul`：condExpInd_ae_eq_condExpI
ndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ 
s != ∞) (x : G) : condExpInd G hm μ…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.condExpIndSMul_ae_eq_smul`：condExpIndSMul_ae_eq_smul (hm :
 m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : condExpIndSMul hm hs
 hμs x =ᵐ[μ] fun a => (condEx…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL2_indicator_of_measurable`：condExpL2_indicator_of_
measurable (hm : m <= m0) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : E) : (
condExpL2 E 𝕜 hm (indicatorConstLp 2 …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem condExpInd_of_measurable (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condExpInd G hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  grw [indicatorConstLp_coeFn, condExpInd_ae_eq_condExpIndSMul hm (hm s hs) hμs,
    condExpIndSMul_ae_eq_smul]
  rw [condExpL2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  filter_upwards [@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)] with x hx
  rw [hx]
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]
/-
**MeasureTheory.condExpInd_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpInd_nonneg {E} [NormedAddCommGroup E] [PartialOrder E] [NormedSpace
 Real E] [IsOrderedModule Real E] (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E
) (hx : 0 <= x) : 0 <= condExpInd E hm μ s x
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : E；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.coeFn_le`：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <=
 g
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.EventuallyEq.trans_le`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f =ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `MeasureTheory.condExpIndSMul_nonneg`：condExpIndSMul_nonneg {E} [NormedAd
dCommGroup E] [PartialOrder E] [NormedSpace Real E] [IsOrderedModule Real E] [Si
gmaFinite (μ.trim hm)] (h…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExpInd_ae_eq_condExpIndSMul`：condExpInd_ae_eq_condExpI
ndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ 
s != ∞) (x : G) : condExpInd G hm μ…
-/
theorem condExpInd_nonneg {E} [NormedAddCommGroup E] [PartialOrder E] [NormedSpace ℝ E]
    [IsOrderedModule ℝ E] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    0 ≤ condExpInd E hm μ s x := by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condExpIndSMul_nonneg hs hμs x hx)

end CondexpInd

section CondexpL1


variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

section CondExpL1CLM

variable (F')

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
/-
**MeasureTheory.condExpL1CLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1CLM (hm : m <= m0) (μ : Measure α) [CompleteSpace ↑(Lp F' 1 μ)] [
SigmaFinite (μ.trim hm)] : (α ->₁[μ] F') ->L[Real] α ->₁[μ] F'
参数：hm : m <= m0；μ : Measure α；Lp F' 1 μ；μ.trim hm。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…

--- 原说明 ---
Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itsel
f.
-/
def condExpL1CLM (hm : m ≤ m0) (μ : Measure α) [CompleteSpace ↑(Lp F' 1 μ)]
    [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condExpInd F' hm μ)

variable {F'}
variable [CompleteSpace F']
/-
**MeasureTheory.condExpL1CLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1CLM_smul (c : 𝕜) (f : α ->₁[μ] F') : condExpL1CLM F' hm μ (c • f)
 = c • condExpL1CLM F' hm μ f
参数：c : 𝕜；f : α ->₁[μ] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_smul`：setToL1_smul (hT : DominatedFinMeasAdditi
ve μ T C) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜) (
f : α ->₁[μ] E) : s…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
· 使用定理 `MeasureTheory.condExpInd_smul'`：condExpInd_smul' [NormedSpace Real F] [S
MulCommClass Real 𝕜 F] (c : 𝕜) (x : F) : condExpInd F hm μ s (c • x) = c • condE
xpInd F hm μ s x
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem condExpL1CLM_smul (c : 𝕜) (f : α →₁[μ] F') :
    condExpL1CLM F' hm μ (c • f) = c • condExpL1CLM F' hm μ f := by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condExpInd F' hm μ) ?_ c f
  exact fun c s x => condExpInd_smul' c x
/-
**MeasureTheory.condExpL1CLM_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：condExpL1CLM_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s != ∞) (x :
 F') : (condExpL1CLM F' hm μ) (indicatorConstLp 1 hs hμs x) = condExpInd F' hm μ
 s x
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.L1.setToL1_indicatorConstLp`：setToL1_indicatorConstLp (hT 
: DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hμs : μ s 
!= ∞) (x : E) : setToL1 hT (ind…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1CLM_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condExpL1CLM F' hm μ) (indicatorConstLp 1 hs hμs x) = condExpInd F' hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condExpInd F' hm μ) hs hμs x
/-
**MeasureTheory.condExpL1CLM_indicatorConst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：condExpL1CLM_indicatorConst (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F
') : (condExpL1CLM F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condExpInd
 F' hm μ s x
参数：hs : MeasurableSet s；hμs : μ s != ∞；x : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.simpleFunc.coe_indicatorConst`：coe_indicatorConst {s : 
Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : (↑(indicatorConst p hs 
hμs c) : Lp E p μ) = indicatorConstL…
· 使用定理 `MeasureTheory.condExpL1CLM_indicatorConstLp`：condExpL1CLM_indicatorConst
Lp (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F') : (condExpL1CLM F' hm μ) (in
dicatorConstLp 1 hs hμs x) = cond…
-/
theorem condExpL1CLM_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condExpL1CLM F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condExpInd F' hm μ s x := by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condExpL1CLM_indicatorConstLp hs hμs x

/-- Auxiliary lemma used in the proof of `setIntegral_condExpL1CLM`. -/
/-
**MeasureTheory.setIntegral_condExpL1CLM_of_measure_ne_top** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：setIntegral_condExpL1CLM_of_measure_ne_top (f : α ->₁[μ] F') (hs : Measura
bleSet[m] s) (hμs : μ s != ∞) : ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s
, f x ∂μ
参数：f : α ->₁[μ] F'；hs : MeasurableSet[m] s；hμs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.induction`：∀ {α : Type u_1} {E : Type u_4} [inst : Meas
urableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheor
y.Measure α} [_i…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.condExpL1CLM_indicatorConst`：condExpL1CLM_indicatorConst (
hs : MeasurableSet s) (hμs : μ s != ∞) (x : F') : (condExpL1CLM F' hm μ) ↑(simpl
eFunc.indicatorConst 1 hs hμs x…
· 使用定理 `MeasureTheory.Lp.simpleFunc.coe_indicatorConst`：coe_indicatorConst {s : 
Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : (↑(indicatorConst p hs 
hμs c) : Lp E p μ) = indicatorConstL…
· 使用定理 `MeasureTheory.setIntegral_indicatorConstLp`：setIntegral_indicatorConstLp
 [CompleteSpace E] {p : Real>=0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) 
(hμt : μ t != ∞) (e : E) : ∫ x i…
· 使用定理 `MeasureTheory.setIntegral_condExpInd`：setIntegral_condExpInd (hs : Measu
rableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : μ t != ∞) (x : G')
 : ∫ a in s, condExpInd G'…
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.continuous_setIntegral`：continuous_setIntegral [NormedSpac
e Real E] (s : Set X) : Continuous fun f : X ->₁[μ] E => ∫ x in s, f x ∂μ
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…

--- 原说明 ---
Auxiliary lemma used in the proof of `setIntegral_condExpL1CLM`.
-/
theorem setIntegral_condExpL1CLM_of_measure_ne_top (f : α →₁[μ] F') (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condExpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst, setIntegral_indicatorConstLp (hm _ hs)]
    exact setIntegral_condExpInd hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp _ hf hg
    simp_rw [(condExpL1CLM F' hm μ).map_add]
    rw [setIntegral_congr_ae (hm s hs) ((Lp.coeFn_add (condExpL1CLM F' hm μ (hf_Lp.toLp f))
      (condExpL1CLM F' hm μ (hg_Lp.toLp g))).mono fun x hx _ => hx)]
    rw [setIntegral_congr_ae (hm s hs)
      ((Lp.coeFn_add (hf_Lp.toLp f) (hg_Lp.toLp g)).mono fun x hx _ => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn,
      integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn, hf,
      hg]
  · exact (continuous_setIntegral s).comp (condExpL1CLM F' hm μ).continuous
  · exact continuous_setIntegral s

/-- The integral of the conditional expectation `condExpL1CLM` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `setIntegral_condExp`, the similar statement for
`condExp`. -/
/-
**MeasureTheory.setIntegral_condExpL1CLM** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setIntegral_condExpL1CLM (f : α ->₁[μ] F') (hs : MeasurableSet[m] s) : ∫ x
 in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ
参数：f : α ->₁[μ] F'；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.setIntegral_condExpL1CLM_of_measure_ne_top`：setIntegral_co
ndExpL1CLM_of_measure_ne_top (f : α ->₁[μ] F') (hs : MeasurableSet[m] s) (hμs : 
μ s != ∞) : ∫ x in s, condExpL1CLM F' hm μ f x…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.tendsto_setIntegral_of_monotone`：tendsto_setIntegral_of_mo
notone {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι
 -> Set X} (hsm : forall i, Measura…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of the conditional expectation `condExpL1CLM` over an `m`-measurabl
e set is equal
to the integral of `f` on that set. See also `setIntegral_condExp`, the similar 
statement for
`condExp`.
-/
theorem setIntegral_condExpL1CLM (f : α →₁[μ] F') (hs : MeasurableSet[m] s) :
    ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  let S := spanningSets (μ.trim hm)
  have hS_meas : ∀ i, MeasurableSet[m] (S i) := measurableSet_spanningSets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_iUnion, iUnion_spanningSets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine fun i => (measure_mono Set.inter_subset_left).trans_lt ?_
    have hS_finite_trim := measure_spanningSets_lt_top (μ.trim hm) i
    rwa [trim_measurableSet_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanningSets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i ∩ s, condExpL1CLM F' hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      setIntegral_condExpL1CLM_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left : Tendsto (fun i => ∫ x in S i ∩ s, condExpL1CLM F' hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condExpL1CLM F' hm μ f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
      (L1.integrable_coeFn (condExpL1CLM F' hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right
/-
**MeasureTheory.aestronglyMeasurable_condExpL1CLM** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：aestronglyMeasurable_condExpL1CLM (f : α ->₁[μ] F') : AEStronglyMeasurable
[m] (condExpL1CLM F' hm μ f) μ
参数：f : α ->₁[μ] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.induction`：∀ {α : Type u_1} {E : Type u_4} [inst : Meas
urableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheor
y.Measure α} [_i…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL1CLM_indicatorConst`：condExpL1CLM_indicatorConst (
hs : MeasurableSet s) (hμs : μ s != ∞) (x : F') : (condExpL1CLM F' hm μ) ↑(simpl
eFunc.indicatorConst 1 hs hμs x…
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpInd`：aestronglyMeasurable_cond
ExpInd (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : AEStronglyMeasurable[m]
 (condExpInd G hm μ s x) μ
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `MeasureTheory.isClosed_aestronglyMeasurable`：isClosed_aestronglyMeasurab
le [Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0) : IsClosed {f : Lp F p μ | A
EStronglyMeasurable[m] f μ}
-/
theorem aestronglyMeasurable_condExpL1CLM (f : α →₁[μ] F') :
    AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condExpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable_condExpInd hs hμs.ne c
  · intro f g hf hg _ hfm hgm
    rw [(condExpL1CLM F' hm μ).map_add]
    exact (hfm.add hgm).congr (coeFn_add ..).symm
  · have : {f : Lp F' 1 μ | AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ} =
        condExpL1CLM F' hm μ ⁻¹' {f | AEStronglyMeasurable[m] f μ} := rfl
    rw [this]
    refine IsClosed.preimage (condExpL1CLM F' hm μ).continuous ?_
    exact isClosed_aestronglyMeasurable hm
/-
**MeasureTheory.condExpL1CLM_lpMeas** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1CLM_lpMeas (f : lpMeas F' Real m 1 μ) : condExpL1CLM F' hm μ (f :
 α ->₁[μ] F') = ↑f
参数：f : lpMeas F' Real m 1 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Lp.induction`：∀ {α : Type u_1} {E : Type u_4} [inst : Meas
urableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheor
y.Measure α} [_i…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Lp.simpleFunc.coe_indicatorConst`：coe_indicatorConst {s : 
Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : (↑(indicatorConst p hs 
hμs c) : Lp E p μ) = indicatorConstL…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.lpMeasToLpTrimLie_symm_indicator`：lpMeasToLpTrimLie_symm_i
ndicator [one_le_p : Fact (1 <= p)] [NormedSpace Real F] {hm : m <= m0} {s : Set
 α} {μ : Measure α} (hs : Measurable…
· 使用定理 `MeasureTheory.condExpL1CLM_indicatorConstLp`：condExpL1CLM_indicatorConst
Lp (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F') : (condExpL1CLM F' hm μ) (in
dicatorConstLp 1 hs hμs x) = cond…
· 使用定理 `MeasureTheory.condExpInd_of_measurable`：condExpInd_of_measurable (hs : M
easurableSet[m] s) (hμs : μ s != ∞) (c : G) : condExpInd G hm μ s c = indicatorC
onstLp 1 (hm s hs) hμs c
· 使用定理 `LinearIsometryEquiv.map_add`：map_add (x y : E) : e (x + y) = e x + e y
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
theorem condExpL1CLM_lpMeas (f : lpMeas F' ℝ m 1 μ) :
    condExpL1CLM F' hm μ (f : α →₁[μ] F') = ↑f := by
  let g := lpMeasToLpTrimLie F' ℝ 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α →₁[μ.trim hm] F' =>
    condExpL1CLM F' hm μ ((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
    ↑((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g)) ?_ ?_ ?_ g
  · intro c s hs hμs
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator hs hμs.ne c,
      condExpL1CLM_indicatorConstLp]
    exact condExpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
  · intro f g hf hg _ hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
  · refine isClosed_eq ?_ ?_
    · refine (condExpL1CLM F' hm μ).continuous.comp (continuous_induced_dom.comp ?_)
      exact LinearIsometryEquiv.continuous _
    · refine continuous_induced_dom.comp ?_
      exact LinearIsometryEquiv.continuous _
/-
**MeasureTheory.condExpL1CLM_of_aestronglyMeasurable'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：condExpL1CLM_of_aestronglyMeasurable' (f : α ->₁[μ] F') (hfm : AEStronglyM
easurable[m] f μ) : condExpL1CLM F' hm μ f = f
参数：f : α ->₁[μ] F'；hfm : AEStronglyMeasurable[m] f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.condExpL1CLM_lpMeas`：condExpL1CLM_lpMeas (f : lpMeas F' Re
al m 1 μ) : condExpL1CLM F' hm μ (f : α ->₁[μ] F') = ↑f
-/
theorem condExpL1CLM_of_aestronglyMeasurable' (f : α →₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ) :
    condExpL1CLM F' hm μ f = f :=
  condExpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)

end CondExpL1CLM

set_option linter.overlappingInstances false in
/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condExp` should be used instead in most cases. -/
/-
**MeasureTheory.condExpL1** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1 (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α 
-> F') : α ->₁[μ] F'
参数：hm : m <= m0；μ : Measure α；μ.trim hm；f : α -> F'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…

--- 原说明 ---
Conditional expectation of a function, in L1. Its value is 0 if the function is 
not
integrable. The function-valued `condExp` should be used instead in most cases.
-/
def condExpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condExpInd F' hm μ) (dominatedFinMeasAdditive_condExpInd F' hm μ) f
/-
**MeasureTheory.condExpL1_undef** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_undef (hf : ¬Integrable f μ) : condExpL1 hm μ f = 0
参数：hf : ¬Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_undef (hf : ¬Integrable f μ) : condExpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditive_condExpInd F' hm μ) hf
/-
**MeasureTheory.condExpL1_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_eq [CompleteSpace F'] (hf : Integrable f μ) : condExpL1 hm μ f =
 condExpL1CLM F' hm μ (hf.toL1 f)
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_eq [CompleteSpace F']
    (hf : Integrable f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f) :=
  setToFun_eq (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

@[simp]
/-
**MeasureTheory.condExpL1_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_zero : condExpL1 hm μ (0 : α -> F') = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_zero`：setToFun_zero (hT : DominatedFinMeasAdditiv
e μ T C) : setToFun μ T hT (0 : α -> E) = 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_zero : condExpL1 hm μ (0 : α → F') = 0 :=
  setToFun_zero _

@[simp]
/-
**MeasureTheory.condExpL1_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：condExpL1_measure_zero (hm : m <= m0) : condExpL1 hm (0 : Measure α) f = 0
参数：hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_measure_zero`：setToFun_measure_zero (hT : Dominat
edFinMeasAdditive μ T C) (h : μ = 0) : setToFun μ T hT f = 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_measure_zero (hm : m ≤ m0) : condExpL1 hm (0 : Measure α) f = 0 :=
  setToFun_measure_zero _ rfl
/-
**MeasureTheory.condExpL1_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_congr_ae (hm : m <= m0) (h : f =ᵐ[μ] g) : condExpL1 hm μ f = con
dExpL1 hm μ g
参数：hm : m <= m0；h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_congr_ae (hm : m ≤ m0) (h : f =ᵐ[μ] g) :
    condExpL1 hm μ f = condExpL1 hm μ g :=
  setToFun_congr_ae _ h
/-
**MeasureTheory.aestronglyMeasurable_condExpL1** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：aestronglyMeasurable_condExpL1 {f : α -> F'} : AEStronglyMeasurable[m] (co
ndExpL1 hm μ f) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.condExpL1_congr_ae`：condExpL1_congr_ae (hm : m <= m0) (h :
 f =ᵐ[μ] g) : condExpL1 hm μ f = condExpL1 hm μ g
· 使用定理 `MeasureTheory.condExpL1_zero`：condExpL1_zero : condExpL1 hm μ (0 : α -> 
F') = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.Lp.ext_iff`：∀ {α : Type u_1} {E : Type u_4} {m : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f g : ↥…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用引理 `MeasureTheory.completeSpace_of_completeSpace_Lp`：completeSpace_of_comple
teSpace_Lp [hp : Fact (1 <= p)] [CompleteSpace (Lp E p μ)] [Nontrivial (Lp E p μ
)] : CompleteSpace E
· 使用定理 `MeasureTheory.condExpL1_eq`：condExpL1_eq [CompleteSpace F'] (hf : Integr
able f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f)
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1CLM`：aestronglyMeasurable_co
ndExpL1CLM (f : α ->₁[μ] F') : AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) 
μ
· 使用定理 `MeasureTheory.condExpL1_undef`：condExpL1_undef (hf : ¬Integrable f μ) : 
condExpL1 hm μ f = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem aestronglyMeasurable_condExpL1 {f : α → F'} :
    AEStronglyMeasurable[m] (condExpL1 hm μ f) μ := by
  by_cases hF' : CompleteSpace (Lp F' 1 μ); swap
  · simp only [condExpL1, setToFun, hF', ↓reduceDIte, ZeroMemClass.coe_zero]
    apply stronglyMeasurable_zero.aestronglyMeasurable.congr
    exact (coeFn_zero _ 1 _).symm
  by_cases hf : Integrable f μ; swap
  · rw [condExpL1_undef hf]
    exact stronglyMeasurable_zero.aestronglyMeasurable.congr (coeFn_zero ..).symm
  by_cases hf' : f =ᵐ[μ] 0
  · apply stronglyMeasurable_zero.aestronglyMeasurable.congr
    simp only [condExpL1_congr_ae hm hf', condExpL1_zero, ZeroMemClass.coe_zero]
    exact (coeFn_zero _ 1 _).symm
  have : CompleteSpace F' := by
    have : Nontrivial (Lp F' 1 μ) := by
      apply nontrivial_of_ne (hf.toL1 f) 0
      grw [ne_eq, Lp.ext_iff, Integrable.coeFn_toL1, coeFn_zero]
      exact hf'
    exact completeSpace_of_completeSpace_Lp F' 1 μ
  rw [condExpL1_eq hf]
  exact aestronglyMeasurable_condExpL1CLM _
/-
**MeasureTheory.integrable_condExpL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_condExpL1 (f : α -> F') : Integrable (condExpL1 hm μ f) μ
参数：f : α -> F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
-/
theorem integrable_condExpL1 (f : α → F') : Integrable (condExpL1 hm μ f) μ :=
  L1.integrable_coeFn _

/-- The integral of the conditional expectation `condExpL1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `setIntegral_condExp`, the similar statement for
`condExp`. -/
/-
**MeasureTheory.setIntegral_condExpL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_condExpL1 [CompleteSpace F'] (hf : Integrable f μ) (hs : Measu
rableSet[m] s) : ∫ x in s, condExpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ
参数：hf : Integrable f μ；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.condExpL1_eq`：condExpL1_eq [CompleteSpace F'] (hf : Integr
able f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f)
· 使用定理 `MeasureTheory.setIntegral_condExpL1CLM`：setIntegral_condExpL1CLM (f : α 
->₁[μ] F') (hs : MeasurableSet[m] s) : ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫
 x in s, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f

--- 原说明 ---
The integral of the conditional expectation `condExpL1` over an `m`-measurable s
et is equal to
the integral of `f` on that set. See also `setIntegral_condExp`, the similar sta
tement for
`condExp`.
-/
theorem setIntegral_condExpL1 [CompleteSpace F'] (hf : Integrable f μ) (hs : MeasurableSet[m] s) :
    ∫ x in s, condExpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  simp_rw [condExpL1_eq hf]
  rw [setIntegral_condExpL1CLM (hf.toL1 f) hs]
  exact setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)
/-
**MeasureTheory.condExpL1_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_add (hf : Integrable f μ) (hg : Integrable g μ) : condExpL1 hm μ
 (f + g) = condExpL1 hm μ f + condExpL1 hm μ g
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_add`：setToFun_add (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f + g) = s
etToFun μ T hT f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condExpL1 hm μ (f + g) = condExpL1 hm μ f + condExpL1 hm μ g :=
  setToFun_add _ hf hg
/-
**MeasureTheory.condExpL1_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_neg (f : α -> F') : condExpL1 hm μ (-f) = -condExpL1 hm μ f
参数：f : α -> F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_neg`：setToFun_neg (hT : DominatedFinMeasAdditive 
μ T C) (f : α -> E) : setToFun μ T hT (-f) = -setToFun μ T hT f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_neg (f : α → F') : condExpL1 hm μ (-f) = -condExpL1 hm μ f :=
  setToFun_neg _ f
/-
**MeasureTheory.condExpL1_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_smul (c : 𝕜) (f : α -> F') : condExpL1 hm μ (c • f) = c • condEx
pL1 hm μ f
参数：c : 𝕜；f : α -> F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_smul`：setToFun_smul [NormedDivisionRing 𝕜] [Modul
e 𝕜 E] [NormSMulClass 𝕜 E] [Module 𝕜 F] [NormSMulClass 𝕜 F] (hT : DominatedFinMe
asAdditive μ T C)…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
· 使用定理 `MeasureTheory.condExpInd_smul'`：condExpInd_smul' [NormedSpace Real F] [S
MulCommClass Real 𝕜 F] (c : 𝕜) (x : F) : condExpInd F hm μ s (c • x) = c • condE
xpInd F hm μ s x
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem condExpL1_smul (c : 𝕜) (f : α → F') : condExpL1 hm μ (c • f) = c • condExpL1 hm μ f := by
  refine setToFun_smul _ ?_ c f
  exact fun c _ x => condExpInd_smul' c x
/-
**MeasureTheory.condExpL1_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) : condExpL1 hm μ
 (f - g) = condExpL1 hm μ f - condExpL1 hm μ g
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_sub`：setToFun_sub (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f - g) = s
etToFun μ T hT f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condExpL1 hm μ (f - g) = condExpL1 hm μ f - condExpL1 hm μ g :=
  setToFun_sub _ hf hg
/-
**MeasureTheory.condExpL1_of_aestronglyMeasurable'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：condExpL1_of_aestronglyMeasurable' [CompleteSpace F'] (hfm : AEStronglyMea
surable[m] f μ) (hfi : Integrable f μ) : condExpL1 hm μ f =ᵐ[μ] f
参数：hfm : AEStronglyMeasurable[m] f μ；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL1_eq`：condExpL1_eq [CompleteSpace F'] (hf : Integr
able f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExpL1CLM_of_aestronglyMeasurable'`：condExpL1CLM_of_aes
tronglyMeasurable' (f : α ->₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ) : condE
xpL1CLM F' hm μ f = f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem condExpL1_of_aestronglyMeasurable' [CompleteSpace F'] (hfm : AEStronglyMeasurable[m] f μ)
    (hfi : Integrable f μ) : condExpL1 hm μ f =ᵐ[μ] f := by
  rw [condExpL1_eq hfi]
  refine EventuallyEq.trans ?_ (Integrable.coeFn_toL1 hfi)
  rw [condExpL1CLM_of_aestronglyMeasurable']
  exact hfm.congr hfi.coeFn_toL1.symm
/-
**MeasureTheory.condExpL1_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL1_mono {E} [NormedAddCommGroup E] [PartialOrder E] [ClosedIciTopol
ogy E] [IsOrderedAddMonoid E] [NormedSpace Real E] [IsOrderedModule Real E] {f g
 : α -> E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g) : cond
ExpL1 hm μ f <=ᵐ[μ] condExpL1 hm μ g
参数：hf : Integrable f μ；hg : Integrable g μ；hfg : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.coeFn_le`：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <=
 g
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.condExpInd_nonneg`：condExpInd_nonneg {E} [NormedAddCommGro
up E] [PartialOrder E] [NormedSpace Real E] [IsOrderedModule Real E] (hs : Measu
rableSet s) (hμs : μ …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.setToFun_mono`：setToFun_mono [ClosedIciTopology G''] [IsOr
deredAddMonoid G'] {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFin
MeasAdditive μ T …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `MeasureTheory.Lp.instOrderClosedTopologySubtypeAEEqFunMemAddSubgroupOfCl
osedIciTopology`：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {μ : Me
asureTheory.Measure α} {p : ENNReal}   [inst : NormedAddCommGroup E] [inst_1 …
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
-/
theorem condExpL1_mono {E}
    [NormedAddCommGroup E] [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [NormedSpace ℝ E] [IsOrderedModule ℝ E] {f g : α → E} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condExpL1 hm μ f ≤ᵐ[μ] condExpL1 hm μ g := by
  rw [coeFn_le]
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condExpInd E hm μ s x :=
    fun s hs hμs x hx => condExpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condExpInd E hm μ) h_nonneg hf hg hfg

end CondexpL1

end MeasureTheory

