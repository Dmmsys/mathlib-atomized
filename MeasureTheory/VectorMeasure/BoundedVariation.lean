/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

import Mathlib.MeasureTheory.VectorMeasure.AddContent

/-!
# Vector valued Stieltjes measure associated to a bounded variation function

Let `α` be a dense linear order with compact segments (e.g. `ℝ` or `ℝ≥0`), and `f : α → E` a
bounded variation function taking values in a complete additive normed group.
We associate to `f` a vector measure, called `BoundedVariationOn.vectorMeasure`. It gives
mass `f.rightLim b - f.leftLim a` to the interval `[a, b]` (with similar formulas for
other types of intervals).

For the construction, we define first an additive content on the set semiring of open-closed
intervals `(a, b]`, mapping this interval to `f.rightLim b - f.rightLim a`. To extend this content
to the whole sigma-algebra, by general extension theorems, it is enough to show that it is
dominated by a finite measure. For this, we can use the Stieltjes measure associated to the
variation of `f.rightLim`. The extension we get is not exactly the desired vector measure, as we
need to tweak things if there is a bot element `a`: the previous vector measure gives to `{a}` the
mass `0` instead of the desired `f.rightLim a - f a`, so we add a Dirac mass to correct this defect.
-/

@[expose] public section

open Filter Set MeasureTheory MeasurableSpace MeasureTheory
open scoped symmDiff Topology NNReal ENNReal

variable {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [CompactIccSpace α] [hα : MeasurableSpace α] [BorelSpace α]
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {f : α → E} {a b : α}

namespace BoundedVariationOn

/-- The Stieltjes function associated to a bounded variation function. It is given by
the variation of the function `f.rightLim` from a fixed base point.
Using right limits ensures the right continuity, which is used to construct Stieltjes measures. -/
/-
**BoundedVariationOn.stieltjesFunctionRightLim** 是 Mathlib 中的一个定义，位于命名空间 `Bounde
dVariationOn`。
形式化陈述：{α : Type u_1} →   [inst : LinearOrder α] →     [inst_1 : TopologicalSpace
 α] →       [OrderTopology α] →         {E : Type u_2} →           [inst_3 : Nor
medAddCommGroup E] →             [CompleteSpace E] → {f : α → E} → BoundedVariat
ionOn f Set.univ → α → StieltjesFunction α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Stieltjes function associated to a bounded variation function. It is given b
y
the variation of the function `f.rightLim` from a fixed base point.
Using right limits ensures the right continuity, which is used to construct Stie
ltjes measures.
-/
@[simps] noncomputable def stieltjesFunctionRightLim
    (hf : BoundedVariationOn f univ) (x₀ : α) : StieltjesFunction α where
  toFun x := variationOnFromTo f.rightLim univ x₀ x
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn hf.rightLim.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x := hf.continuousWithinAt_variationOnFromTo_rightLim_Ici

open scoped Classical in
/-- Auxiliary measure used to construct the vector measure associated to a bounded variation
function. This is *not* the total variation of this measure in general, as we need to adjust things
when there is a bot element by adding a Dirac mass there. -/
/-
**BoundedVariationOn.measureAux** 是 Mathlib 中的一个定义，位于命名空间 `BoundedVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary measure used to construct the vector measure associated to a bounded v
ariation
function. This is *not* the total variation of this measure in general, as we ne
ed to adjust things
when there is a bot element by adding a Dirac mass there.
-/
private noncomputable def measureAux (hf : BoundedVariationOn f univ) : Measure α :=
  if h : Nonempty α then (hf.stieltjesFunctionRightLim h.some).measure else 0
/-
**BoundedVariationOn.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance (hf : BoundedVariationOn f univ) : IsFiniteMeasure hf.measureAux := by
  by_cases h : Nonempty α; swap
  · simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
    infer_instance
  simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
    (C := (eVariationOn f.rightLim univ).toReal) _ (fun x ↦ ?_)
  exact variationOnFromTo.abs_le_eVariationOn hf.rightLim

/-- Given a bounded variation function `f`, we can construct a vector measure giving
mass `f.rightLim v - f.rightLim a` to each open-closed interval `(a, b]`. This is *not* the
measure associated to `f` in general, as we may need to adjust things at the bot element if
there is one. -/
/-
**BoundedVariationOn.exists_vectorMeasure_le_measureAux** 是 Mathlib 中的一个引理，位于命名空
间 `BoundedVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a bounded variation function `f`, we can construct a vector measure giving
mass `f.rightLim v - f.rightLim a` to each open-closed interval `(a, b]`. This i
s *not* the
measure associated to `f` in general, as we may need to adjust things at the bot
 element if
there is one.
-/
private lemma exists_vectorMeasure_le_measureAux (hf : BoundedVariationOn f univ) :
    ∃ m : VectorMeasure α E, (∀ u v, u ≤ v → m (Set.Ioc u v) = f.rightLim v - f.rightLim u) ∧
      m botSet = 0 ∧ ∀ s, ‖m s‖ₑ ≤ hf.measureAux s := by
  /- We will apply the general extension theorem
  `VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`. For this, we
  need to check that the additive content is bounded by the measure `measureAux`. -/
  rcases isEmpty_or_nonempty α with h'α | h'α
  · exact ⟨0, by simp⟩
  let m := AddContent.onIoc f.rightLim
  have A : ∀ s ∈ {s | ∃ u v, u ≤ v ∧ s = Ioc u v}, ‖m s‖ₑ ≤ hf.measureAux s := by
    rintro s ⟨u, v, huv, rfl⟩
    rw [AddContent.onIoc_apply huv]
    simp only [BoundedVariationOn.measureAux, h'α, ↓reduceDIte, StieltjesFunction.measure_Ioc,
      BoundedVariationOn.stieltjesFunctionRightLim_apply]
    rw [← variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn
      (mem_univ h'α.some) (mem_univ u) (mem_univ v)]
    simp only [add_sub_cancel_left, variationOnFromTo, huv, ↓reduceIte, univ_inter]
    rw [ENNReal.ofReal_toReal]; swap
    · exact ((eVariationOn.mono _ (subset_univ _)).trans_lt hf.rightLim.lt_top).ne
    rw [← edist_eq_enorm_sub]
    exact eVariationOn.edist_le _ (by grind) (by grind)
  have B : hα = generateFrom {s | ∃ u v, u ≤ v ∧ s = Ioc u v} := by
    borelize α
    convert! borel_eq_generateFrom_Ioc_le α using 2
    grind only
  rcases VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    IsSetSemiring.Ioc A B with ⟨m', hm', h'm'⟩
  refine ⟨m', fun u v huv ↦ ?_, ?_, h'm'⟩
  · rw [hm']
    · exact AddContent.onIoc_apply huv
    · exact ⟨u, v, huv, rfl⟩
  · apply enorm_eq_zero.1
    apply le_bot_iff.1
    exact (h'm' _).trans (by simp [measureAux, h'α])

open scoped Classical in
/-- The vector measure associated to a bounded variation function `f`, giving mass
`f.rightLim b - f.leftLim a` to closed intervals `[a, b]`, and similarly for other intervals. -/
/-
**BoundedVariationOn.vectorMeasure** 是 Mathlib 中的一个定义，位于命名空间 `BoundedVariationOn
`。
形式化陈述：{α : Type u_1} →   [inst : LinearOrder α] →     [DenselyOrdered α] →      
 [inst_2 : TopologicalSpace α] →         [OrderTopology α] →           [SecondCo
untableTopology α] →             [CompactIccSpace α] →               [hα : Measu
rableSpace α] →                 [BorelSpace α] →                   {E : Type u_2
} →                     [inst_7 : NormedAddCommGroup E] →                       
[CompleteSpace E] → {f : α → E} → BoundedVariationOn f Set.univ → MeasureTheory.
VectorMeasure α E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.BoundedVariation.0.BoundedV
ariationOn.exists_vectorMeasure_le_measureAux`：∀ {α : Type u_1} [inst : LinearOr
der α] [inst_1 : DenselyOrdered α] [inst_2 : TopologicalSpace α]   [inst_3 : Ord
erTopology α] [inst_4 : Sec…

--- 原说明 ---
The vector measure associated to a bounded variation function `f`, giving mass
`f.rightLim b - f.leftLim a` to closed intervals `[a, b]`, and similarly for oth
er intervals.
-/
@[no_expose] noncomputable def vectorMeasure (hf : BoundedVariationOn f univ) : VectorMeasure α E :=
  hf.exists_vectorMeasure_le_measureAux.choose +
  (if h : ∃ x, IsBot x then VectorMeasure.dirac h.choose (f.rightLim h.choose - f h.choose) else 0)
/-
**BoundedVariationOn.vectorMeasure_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Ioc (hf : BoundedVariationOn f univ) (h : a <= b) : hf.vecto
rMeasure (Ioc a b) = f.rightLim b - f.rightLim a
参数：hf : BoundedVariationOn f univ；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.BoundedVariation.0.BoundedV
ariationOn.exists_vectorMeasure_le_measureAux`：∀ {α : Type u_1} [inst : LinearOr
der α] [inst_1 : DenselyOrdered α] [inst_2 : TopologicalSpace α]   [inst_3 : Ord
erTopology α] [inst_4 : Sec…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_notMem`：∀ {β : Type u_2} {M :
 Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Meas
urableSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma vectorMeasure_Ioc (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Ioc a b) = f.rightLim b - f.rightLim a := by
  classical
  have A : hf.exists_vectorMeasure_le_measureAux.choose (Ioc a b) =
      f.rightLim b - f.rightLim a :=
    hf.exists_vectorMeasure_le_measureAux.choose_spec.1 a b h
  have B : (if hx : ∃ (x : α), IsBot x then VectorMeasure.dirac hx.choose
      (f.rightLim hx.choose - f hx.choose) else 0) (Ioc a b) = 0 := by
    by_cases hx : ∃ (x : α), IsBot x
    · simp only [hx, ↓reduceDIte]
      rw [VectorMeasure.dirac_apply_of_notMem]
      simp only [mem_Ioc, not_and_or, not_lt, not_le]
      exact Or.inl (hx.choose_spec _)
    · simp [hx]
  simp [vectorMeasure, A, B]
/-
**BoundedVariationOn.vectorMeasure_singleton** 是 Mathlib 中的一个引理，位于命名空间 `BoundedV
ariationOn`。
形式化陈述：vectorMeasure_singleton (hf : BoundedVariationOn f univ) : hf.vectorMeasur
e {a} = f.rightLim a - f.leftLim a
参数：hf : BoundedVariationOn f univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_isBot`：∀ (α : Type u_1) [inst : PartialOrder α], {x | I
sBot x}.Subsingleton
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.BoundedVariation.0.BoundedV
ariationOn.exists_vectorMeasure_le_measureAux`：∀ {α : Type u_1} [inst : LinearOr
der α] [inst_1 : DenselyOrdered α] [inst_2 : TopologicalSpace α]   [inst_3 : Ord
erTopology α] [inst_4 : Sec…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `botSet_eq_singleton_of_isBot`：botSet_eq_singleton_of_isBot {x : R} (hx :
 IsBot x) : botSet = {x}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_mem`：∀ {β : Type u_2} {M : Ty
pe u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Measura
bleSpace β]   {x : β} {v : M} {s : S…
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `leftLim_eq_of_isBot`：leftLim_eq_of_isBot {f : α -> β} {a : α} (ha : IsBo
t a) : leftLim f a = f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 69 条，此处仅展示前 30 条）
-/
lemma vectorMeasure_singleton (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure {a} = f.rightLim a - f.leftLim a := by
  by_cases ha : IsBot a
  · have h : ∃ x, IsBot x := ⟨a, ha⟩
    have heqa : h.choose = a := subsingleton_isBot _ h.choose_spec ha
    have A : hf.exists_vectorMeasure_le_measureAux.choose {a} = 0 := by
      rw [← botSet_eq_singleton_of_isBot ha]
      exact hf.exists_vectorMeasure_le_measureAux.choose_spec.2.1
    simp only [vectorMeasure, h, ↓reduceDIte, add_apply, A, zero_add]
    rw [VectorMeasure.dirac_apply_of_mem (MeasurableSet.singleton a)]
    · simpa only [heqa, sub_right_inj] using (leftLim_eq_of_isBot ha).symm
    · simp [heqa]
  obtain ⟨b, hb⟩ : ∃ b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
      ∃ u : ℕ → α, StrictMono u ∧ (∀ n : ℕ, u n ∈ Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : ∀ (i : ℕ), u i < x ∧ x ≤ a := by simpa using hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n ↦ hf.vectorMeasure (Ioc (u n) a)) atTop (𝓝 (hf.vectorMeasure {a})) := by
    rw [A]
    apply VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat ?_ (fun n ↦ measurableSet_Ioc)
    exact fun m n hmn ↦ Ioc_subset_Ioc_left (u_mono.monotone hmn)
  have L2 : Tendsto (fun n ↦ hf.vectorMeasure (Ioc (u n) a)) atTop
      (𝓝 (f.rightLim a - f.leftLim a)) := by
    simp_rw [hf.vectorMeasure_Ioc (u_lt_a _).le]
    apply tendsto_const_nhds.sub
    have : Tendsto u atTop (𝓝[<] a) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      u_lim (Eventually.of_forall u_lt_a)
    convert! (hf.rightLim.tendsto_leftLim a).comp this using 2
    have : (𝓝[<] a).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨b, hb⟩]
      exact self_mem_Iic
    exact (leftLim_rightLim (hf.tendsto_leftLim _)).symm
  exact tendsto_nhds_unique L1 L2
/-
**BoundedVariationOn.vectorMeasure_Icc** 是 Mathlib 中的一个引理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Icc (hf : BoundedVariationOn f univ) (h : a <= b) : hf.vecto
rMeasure (Icc a b) = f.rightLim b - f.leftLim a
参数：hf : BoundedVariationOn f univ；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Ioc_eq_Icc`：Icc_union_Ioc_eq_Icc (h₁ : a <= b) (h₂ : b <= 
c) : Icc a b union Ioc b c = Icc a c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用引理 `BoundedVariationOn.vectorMeasure_singleton`：vectorMeasure_singleton (hf 
: BoundedVariationOn f univ) : hf.vectorMeasure {a} = f.rightLim a - f.leftLim a
· 使用引理 `BoundedVariationOn.vectorMeasure_Ioc`：vectorMeasure_Ioc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Ioc a b) = f.rightLim b - f.ri
ghtLim a
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vectorMeasure_Icc (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Icc a b) = f.rightLim b - f.leftLim a := by
  rw [← Icc_union_Ioc_eq_Icc le_rfl h, VectorMeasure.of_union (by simp)
    measurableSet_Icc measurableSet_Ioc, Icc_self, hf.vectorMeasure_singleton,
    hf.vectorMeasure_Ioc h]
  simp
/-
**BoundedVariationOn.vectorMeasure_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Ioo (hf : BoundedVariationOn f univ) (h : a < b) : hf.vector
Measure (Ioo a b) = f.leftLim b - f.rightLim a
参数：hf : BoundedVariationOn f univ；h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BoundedVariationOn.vectorMeasure_Ioc`：vectorMeasure_Ioc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Ioc a b) = f.rightLim b - f.ri
ghtLim a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedVariationOn.vectorMeasure_Icc`：vectorMeasure_Icc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Icc a b) = f.rightLim b - f.le
ftLim a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_union_Icc_eq_Ioc`：Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b <= c
) : Ioo a b union Icc b c = Ioc a c
-/
theorem vectorMeasure_Ioo (hf : BoundedVariationOn f univ) (h : a < b) :
    hf.vectorMeasure (Ioo a b) = f.leftLim b - f.rightLim a := by
  have := hf.vectorMeasure_Ioc h.le
  rw [← Ioo_union_Icc_eq_Ioc h le_rfl, VectorMeasure.of_union (by simp) measurableSet_Ioo
    measurableSet_Icc, hf.vectorMeasure_Icc le_rfl] at this
  grind
/-
**BoundedVariationOn.vectorMeasure_Ico** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Ico (hf : BoundedVariationOn f univ) (h : a <= b) : hf.vecto
rMeasure (Ico a b) = f.leftLim b - f.leftLim a
参数：hf : BoundedVariationOn f univ；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Ioo_eq_Ico`：Icc_union_Ioo_eq_Ico (h₁ : a <= b) (h₂ : b < c
) : Icc a b union Ioo b c = Ico a c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用引理 `BoundedVariationOn.vectorMeasure_Icc`：vectorMeasure_Icc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Icc a b) = f.rightLim b - f.le
ftLim a
· 使用定理 `BoundedVariationOn.vectorMeasure_Ioo`：vectorMeasure_Ioo (hf : BoundedVar
iationOn f univ) (h : a < b) : hf.vectorMeasure (Ioo a b) = f.leftLim b - f.righ
tLim a
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.BoundedVariation.0.BoundedV
ariationOn.vectorMeasure_Ico._abel_1_2`：∀ {α : Type u_2} [inst : LinearOrder α] 
{E : Type u_1} [inst_1 : NormedAddCommGroup E] {f : α → E} {a b : α},   Function
.rightLim f a - Func…
-/
theorem vectorMeasure_Ico (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Ico a b) = f.leftLim b - f.leftLim a := by
  rcases h.eq_or_lt with rfl | h'
  · simp
  rw [← Icc_union_Ioo_eq_Ico le_rfl h', VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioo, hf.vectorMeasure_Icc le_rfl, hf.vectorMeasure_Ioo h']
  abel
/-
**BoundedVariationOn.vectorMeasure_Ici** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Ici (hf : BoundedVariationOn f univ) (a : α) : hf.vectorMeas
ure (Ici a) = limUnder atTop f - f.leftLim a
参数：hf : BoundedVariationOn f univ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `BoundedVariationOn.tendsto_atTop_limUnder`：∀ {α : Type u_1} [inst : Line
arOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] [CompleteSpace E]   [h
E : Nonempty E] {f : α → E},   …
· 使用定理 `Filter.exists_seq_monotone_tendsto_atTop_atTop`：exists_seq_monotone_tend
sto_atTop_atTop (α : Type*) [Preorder α] [Nonempty α] [IsDirectedOrder α] [(atTo
p : Filter α).IsCountablyGenerated] …
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat`：tend
sto_vectorMeasure_iUnion_atTop_nat {s : Nat -> Set α} (hm : Monotone s) (hs : fo
rall i, MeasurableSet (s i)) : Tendsto (fun n => v (s n)…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `BoundedVariationOn.vectorMeasure_Icc`：vectorMeasure_Icc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Icc a b) = f.rightLim b - f.le
ftLim a
（共 40 条，此处仅展示前 30 条）
-/
theorem vectorMeasure_Ici (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Ici a) = limUnder atTop f - f.leftLim a := by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atTop (𝓝 (limUnder atTop f)) := hf.tendsto_atTop_limUnder
  obtain ⟨u, u_mono, hu⟩ : ∃ u, Monotone u ∧ Tendsto u atTop atTop :=
    Filter.exists_seq_monotone_tendsto_atTop_atTop α
  have A : Tendsto (fun n ↦ hf.vectorMeasure (Icc a (u n))) atTop
      (𝓝 (hf.vectorMeasure (Ici a))) := by
    have : Ici a = ⋃ n, Icc a (u n) := by
      apply le_antisymm ?_ (by simp [Icc_subset_Ici_self])
      intro x (hx : a ≤ x)
      simpa [hx] using (hu.eventually (Ici_mem_atTop x)).exists
    rw [this]
    exact hf.vectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat (s := fun n ↦ Icc a (u n))
      (fun i j hij x hx ↦ by grind [Monotone]) (fun i ↦ measurableSet_Icc)
  have B : Tendsto (fun n ↦ hf.vectorMeasure (Icc a (u n))) atTop
      (𝓝 (limUnder atTop f - f.leftLim a)) := by
    have : (fun n ↦ f.rightLim (u n) - f.leftLim a) =ᶠ[atTop]
        (fun n ↦ hf.vectorMeasure (Icc a (u n))) := by
      have : ∀ᶠ n in atTop, a ≤ u n := by
        simp only [tendsto_atTop, eventually_atTop] at hu
        simp [hu]
      filter_upwards [this] with n hn using by rw [hf.vectorMeasure_Icc hn]
    apply Tendsto.congr' this
    apply Tendsto.sub ?_ tendsto_const_nhds
    exact (tendsto_rightLim_atTop_of_tendsto hlim).comp hu
  exact tendsto_nhds_unique A B
/-
**BoundedVariationOn.vectorMeasure_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Ioi (hf : BoundedVariationOn f univ) (a : α) : hf.vectorMeas
ure (Ioi a) = limUnder atTop f - f.rightLim a
参数：hf : BoundedVariationOn f univ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `BoundedVariationOn.vectorMeasure_Ici`：vectorMeasure_Ici (hf : BoundedVar
iationOn f univ) (a : α) : hf.vectorMeasure (Ici a) = limUnder atTop f - f.leftL
im a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedVariationOn.vectorMeasure_Icc`：vectorMeasure_Icc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Icc a b) = f.rightLim b - f.le
ftLim a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Ioi_eq_Ici`：Icc_union_Ioi_eq_Ici (h : a <= b) : Icc a b un
ion Ioi b = Ici a
-/
theorem vectorMeasure_Ioi (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Ioi a) = limUnder atTop f - f.rightLim a := by
  have := hf.vectorMeasure_Ici a
  rw [← Icc_union_Ioi_eq_Ici le_rfl, VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioi, hf.vectorMeasure_Icc le_rfl] at this
  grind
/-
**BoundedVariationOn.vectorMeasure_Iic** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Iic (hf : BoundedVariationOn f univ) (a : α) : hf.vectorMeas
ure (Iic a) = f.rightLim a - limUnder atBot f
参数：hf : BoundedVariationOn f univ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `BoundedVariationOn.tendsto_atBot_limUnder`：∀ {α : Type u_1} [inst : Line
arOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] [CompleteSpace E]   [h
E : Nonempty E] {f : α → E},   …
· 使用定理 `Filter.exists_seq_antitone_tendsto_atTop_atBot`：exists_seq_antitone_tend
sto_atTop_atBot (α : Type*) [Preorder α] [Nonempty α] [IsCodirectedOrder α] [(at
Bot : Filter α).IsCountablyGenerated…
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instIsCountablyGenerated_atBot`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : LinearOrder α] [OrderTopology α]   [TopologicalSpace.SeparableSpace
 α], Filter.atBot.Is…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat`：tend
sto_vectorMeasure_iUnion_atTop_nat {s : Nat -> Set α} (hm : Monotone s) (hs : fo
rall i, MeasurableSet (s i)) : Tendsto (fun n => v (s n)…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `BoundedVariationOn.vectorMeasure_Icc`：vectorMeasure_Icc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Icc a b) = f.rightLim b - f.le
ftLim a
（共 40 条，此处仅展示前 30 条）
-/
theorem vectorMeasure_Iic (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Iic a) = f.rightLim a - limUnder atBot f := by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atBot (𝓝 (limUnder atBot f)) := hf.tendsto_atBot_limUnder
  obtain ⟨u, u_anti, hu⟩ : ∃ u, Antitone u ∧ Tendsto u atTop atBot :=
    Filter.exists_seq_antitone_tendsto_atTop_atBot α
  have A : Tendsto (fun n ↦ hf.vectorMeasure (Icc (u n) a)) atTop
      (𝓝 (hf.vectorMeasure (Iic a))) := by
    have : Iic a = ⋃ n, Icc (u n) a := by
      apply le_antisymm ?_ (by simp [Icc_subset_Iic_self])
      intro x (hx : x ≤ a)
      simpa [hx] using (hu.eventually (Iic_mem_atBot x)).exists
    rw [this]
    exact hf.vectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat (s := fun n ↦ Icc (u n) a)
      (fun i j hij x hx ↦ by grind [Antitone]) (fun i ↦ measurableSet_Icc)
  have B : Tendsto (fun n ↦ hf.vectorMeasure (Icc (u n) a)) atTop
      (𝓝 (f.rightLim a - limUnder atBot f)) := by
    have : (fun n ↦ f.rightLim a - f.leftLim (u n)) =ᶠ[atTop]
        (fun n ↦ hf.vectorMeasure (Icc (u n) a)) := by
      have : ∀ᶠ n in atTop, u n ≤ a := by
        simp only [tendsto_atBot, eventually_atTop] at hu
        simp [hu]
      filter_upwards [this] with n hn using by rw [hf.vectorMeasure_Icc hn]
    apply Tendsto.congr' this
    apply Tendsto.sub tendsto_const_nhds
    exact (tendsto_leftLim_atBot_of_tendsto hf.tendsto_atBot_limUnder).comp hu
  exact tendsto_nhds_unique A B
/-
**BoundedVariationOn.vectorMeasure_Iio** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariati
onOn`。
形式化陈述：vectorMeasure_Iio (hf : BoundedVariationOn f univ) (a : α) : hf.vectorMeas
ure (Iio a) = f.leftLim a - limUnder atBot f
参数：hf : BoundedVariationOn f univ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `BoundedVariationOn.vectorMeasure_Iic`：vectorMeasure_Iic (hf : BoundedVar
iationOn f univ) (a : α) : hf.vectorMeasure (Iic a) = f.rightLim a - limUnder at
Bot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedVariationOn.vectorMeasure_Icc`：vectorMeasure_Icc (hf : BoundedVar
iationOn f univ) (h : a <= b) : hf.vectorMeasure (Icc a b) = f.rightLim b - f.le
ftLim a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `measurableSet_Iio`：measurableSet_Iio [ClosedIciTopology α] : MeasurableS
et (Iio a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Icc_eq_Iic`：Iio_union_Icc_eq_Iic (h : a <= b) : Iio a unio
n Icc a b = Iic b
-/
theorem vectorMeasure_Iio (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Iio a) = f.leftLim a - limUnder atBot f := by
  have := hf.vectorMeasure_Iic a
  rw [← Iio_union_Icc_eq_Iic le_rfl, VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Icc, hf.vectorMeasure_Icc le_rfl] at this
  grind
/-
**BoundedVariationOn.vectorMeasure_univ** 是 Mathlib 中的一个定理，位于命名空间 `BoundedVariat
ionOn`。
形式化陈述：vectorMeasure_univ (hf : BoundedVariationOn f univ) : hf.vectorMeasure uni
v = limUnder atTop f - limUnder atBot f
参数：hf : BoundedVariationOn f univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `Filter.limUnder.congr_simp`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 {α : Type u_3} [inst_1 : Nonempty X] (f f_1 : Filter α),   f = f_1 → ∀ (g g_1 :
 α → X), g = g_1…
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Ici`：Iio_union_Ici : Iio a union Ici a = univ
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `measurableSet_Iio`：measurableSet_Iio [ClosedIciTopology α] : MeasurableS
et (Iio a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BoundedVariationOn.vectorMeasure_Iio`：vectorMeasure_Iio (hf : BoundedVar
iationOn f univ) (a : α) : hf.vectorMeasure (Iio a) = f.leftLim a - limUnder atB
ot f
· 使用定理 `BoundedVariationOn.vectorMeasure_Ici`：vectorMeasure_Ici (hf : BoundedVar
iationOn f univ) (a : α) : hf.vectorMeasure (Ici a) = limUnder atTop f - f.leftL
im a
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.BoundedVariation.0.BoundedV
ariationOn.vectorMeasure_univ._abel_1_2`：∀ {α : Type u_2} [inst : LinearOrder α]
 {E : Type u_1} [inst_1 : NormedAddCommGroup E] {f : α → E} (hα : Nonempty α),  
 Function.leftLim f h…
-/
theorem vectorMeasure_univ (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure univ = limUnder atTop f - limUnder atBot f := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_empty_of_isEmpty, filter_eq_bot_of_isEmpty]
  rw [← Iio_union_Ici (a := hα.some), VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Ici, hf.vectorMeasure_Iio, hf.vectorMeasure_Ici]
  abel

end BoundedVariationOn

