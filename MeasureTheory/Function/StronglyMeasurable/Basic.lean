/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`FinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

We provide a solid API for strongly measurable functions, as a basis for the Bochner integral.

## Main definitions

* `StronglyMeasurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`.
* `FinStronglyMeasurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

@[expose] public section

-- Guard against import creep
assert_not_exists InnerProductSpace

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `StronglyMeasurable` if it is the limit of simple functions. -/
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：StronglyMeasurable [MeasurableSpace α] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is `StronglyMeasurable` if it is the limit of simple functions.
-/
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @StronglyMeasurable ..])
  (by fun_prop (disch := measurability))

/-- The notation for StronglyMeasurable giving the measurable space instance explicitly. -/
scoped notation "StronglyMeasurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

/-- A function is `FinStronglyMeasurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
/-
**MeasureTheory.FinStronglyMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：FinStronglyMeasurable [Zero β] {_ : MeasurableSpace α} (f : α -> β) (μ : M
easure α
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is `FinStronglyMeasurable` with respect to a measure if it is the lim
it of simple
  functions with support with finite measure.
-/
def FinStronglyMeasurable [Zero β]
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/

section StronglyMeasurable
variable {_ : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : ℕ → α} {m : ℕ}

variable [TopologicalSpace β]

@[fun_prop]
/-
**MeasureTheory.SimpleFunc.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : MeasurableSpace α} [inst : Topologica
lSpace β] (f : MeasureTheory.SimpleFunc α β),   MeasureTheory.StronglyMeasurable
 ⇑f
参数：f : MeasureTheory.SimpleFunc α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem SimpleFunc.stronglyMeasurable (f : α →ₛ β) : StronglyMeasurable f :=
  ⟨fun _ => f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]
/-
**MeasureTheory.StronglyMeasurable.of_subsingleton_dom** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : MeasurableSpace α} {f : α → β} [inst 
: TopologicalSpace β] [Subsingleton α],   MeasureTheory.StronglyMeasurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Subsingleton.measurableSingletonClass`：∀ {α : Type u_1} [inst : Measurab
leSpace α] [Subsingleton α], MeasurableSingletonClass α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma StronglyMeasurable.of_subsingleton_dom [Subsingleton α] : StronglyMeasurable f :=
  ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]
/-
**MeasureTheory.StronglyMeasurable.of_subsingleton_cod** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : MeasurableSpace α} {f : α → β} [inst 
: TopologicalSpace β] [Subsingleton β],   MeasureTheory.StronglyMeasurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma StronglyMeasurable.of_subsingleton_cod [Subsingleton β] : StronglyMeasurable f := by
  let f_sf : α →ₛ β := ⟨f, fun x => ?_, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun _ => f_sf, fun x => tendsto_const_nhds⟩
  · simp [Set.preimage, eq_iff_true_of_subsingleton]

@[fun_prop]
/-
**MeasureTheory.stronglyMeasurable_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：stronglyMeasurable_const {b : β} : StronglyMeasurable fun _ : α => b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem stronglyMeasurable_const {b : β} : StronglyMeasurable fun _ : α => b :=
  ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩

@[to_additive]
/-
**MeasureTheory.stronglyMeasurable_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：stronglyMeasurable_one [One β] : StronglyMeasurable (1 : α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem stronglyMeasurable_one [One β] : StronglyMeasurable (1 : α → β) := stronglyMeasurable_const

/-- A version of `stronglyMeasurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
/-
**MeasureTheory.stronglyMeasurable_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：stronglyMeasurable_const' (hf : forall x y, f x = f y) : StronglyMeasurabl
e f
参数：hf : forall x y, f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b

--- 原说明 ---
A version of `stronglyMeasurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types.
-/
theorem stronglyMeasurable_const' (hf : ∀ x y, f x = f y) : StronglyMeasurable f := by
  nontriviality α
  inhabit α
  convert! stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default

variable [MeasurableSingletonClass α]

section aux
omit [TopologicalSpace β]

/-- Auxiliary definition for `StronglyMeasurable.of_discrete`. -/
/-
**MeasureTheory.simpleFuncAux** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `StronglyMeasurable.of_discrete`.
-/
private noncomputable def simpleFuncAux (f : α → β) (g : ℕ → α) : ℕ → SimpleFunc α β
  | 0 => .const _ (f (g 0))
  | n + 1 => .piecewise {g n} (.singleton _) (.const _ <| f (g n)) (simpleFuncAux f g n)
/-
**MeasureTheory.simpleFuncAux_eq_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma simpleFuncAux_eq_of_lt : ∀ n > m, simpleFuncAux f g n (g m) = f (g m)
  | _, .refl => by simp [simpleFuncAux]
  | _, Nat.le.step (m := n) hmn => by
    obtain hnm | hnm := eq_or_ne (g n) (g m) <;>
      simp [simpleFuncAux, Set.piecewise_eq_of_notMem, hnm.symm, simpleFuncAux_eq_of_lt _ hmn]
/-
**MeasureTheory.simpleFuncAux_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma simpleFuncAux_eventuallyEq : ∀ᶠ n in atTop, simpleFuncAux f g n (g m) = f (g m) :=
  eventually_atTop.2 ⟨_, simpleFuncAux_eq_of_lt⟩

end aux

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : MeasurableSpace α} {f : α → β} [inst 
: TopologicalSpace β]   [MeasurableSingletonClass α] [Countable α], MeasureTheor
y.StronglyMeasurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `_private.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic.0.Measu
reTheory.simpleFuncAux_eventuallyEq`：∀ {α : Type u_1} {β : Type u_2} {x : Measur
ableSpace α} {f : α → β} {g : ℕ → α} {m : ℕ}   [inst : MeasurableSingletonClass 
α], ∀ᶠ (n : ℕ) in…
-/
lemma StronglyMeasurable.of_discrete [Countable α] : StronglyMeasurable f := by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  exact ⟨simpleFuncAux f g, hg.forall.2 fun m ↦
    tendsto_nhds_of_eventually_eq simpleFuncAux_eventuallyEq⟩

end StronglyMeasurable

namespace StronglyMeasurable

variable {f g : α → β}

section BasicPropertiesInAnyTopologicalSpace

variable [TopologicalSpace β]

/-- A sequence of simple functions such that
`∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x))`.
That property is given by `stronglyMeasurable.tendsto_approx`. -/
/-
**MeasureTheory.StronglyMeasurable.approx** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.StronglyMeasurable`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {f : α → β} →       [inst : Topolo
gicalSpace β] →         {x : MeasurableSpace α} → MeasureTheory.StronglyMeasurab
le f → ℕ → MeasureTheory.SimpleFunc α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of simple functions such that
`∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x))`.
That property is given by `stronglyMeasurable.tendsto_approx`.
-/
protected noncomputable def approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ℕ → α →ₛ β :=
  hf.choose
/-
**MeasureTheory.StronglyMeasurable.tendsto_approx** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : TopologicalSpace β] {x
 : MeasurableSpace α}   (hf : MeasureTheory.StronglyMeasurable f) (x_1 : α),   F
ilter.Tendsto (fun n => (hf.approx n) x_1) Filter.atTop (nhds (f x_1))
参数：hf : MeasureTheory.StronglyMeasurable f；x_1 : α；fun n => (hf.approx n) x_1；nh
ds (f x_1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem tendsto_approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec

/-- Similar to `stronglyMeasurable.approx`, but enforces that the norm of every function in the
sequence is less than `c` everywhere. If `‖f x‖ ≤ c` this sequence of simple functions verifies
`Tendsto (fun n => hf.approxBounded n x) atTop (𝓝 (f x))`. -/
/-
**MeasureTheory.StronglyMeasurable.approxBounded** 是 Mathlib 中的一个定义，位于命名空间 `Meas
ureTheory.StronglyMeasurable`。
形式化陈述：approxBounded {_ : MeasurableSpace α} [Norm β] [SMul Real β] (hf : Strongl
yMeasurable f) (c : Real) : Nat -> SimpleFunc α β
参数：hf : StronglyMeasurable f；c : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Similar to `stronglyMeasurable.approx`, but enforces that the norm of every func
tion in the
sequence is less than `c` everywhere. If `‖f x‖ ≤ c` this sequence of simple fun
ctions verifies
`Tendsto (fun n => hf.approxBounded n x) atTop (𝓝 (f x))`.
-/
noncomputable def approxBounded {_ : MeasurableSpace α} [Norm β] [SMul ℝ β]
    (hf : StronglyMeasurable f) (c : ℝ) : ℕ → SimpleFunc α β := fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x
/-
**MeasureTheory.StronglyMeasurable.tendsto_approxBounded_of_norm_le** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：tendsto_approxBounded_of_norm_le {β} {f : α -> β} [NormedAddCommGroup β] [
NormedSpace Real β] {m : MeasurableSpace α} (hf : StronglyMeasurable[m] f) {c : 
Real} {x : α} (hfx : ‖f x‖ <= c) : Tendsto (fun n => hf.approxBounded c n x) atT
op (𝓝 (f x))
参数：hf : StronglyMeasurable[m] f；hfx : ‖f x‖ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `squeeze_zero_norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] {f : α → E} {a : α → ℝ} {t₀ : Filter α},   (∀ (n : α), ‖f n‖ ≤ a n) → F
ilter.T…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `min_eq_left_iff`：min_eq_left_iff : min a b = a ↔ a <= b
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
（共 42 条，此处仅展示前 30 条）
-/
theorem tendsto_approxBounded_of_norm_le {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} (hf : StronglyMeasurable[m] f) {c : ℝ} {x : α} (hfx : ‖f x‖ ≤ c) :
    Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  have h_tendsto := hf.tendsto_approx x
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  by_cases hfx0 : ‖f x‖ = 0
  · rw [norm_eq_zero] at hfx0
    rw [hfx0] at h_tendsto ⊢
    have h_tendsto_norm : Tendsto (fun n => ‖hf.approx n x‖) atTop (𝓝 0) := by
      convert! h_tendsto.norm
      rw [norm_zero]
    refine squeeze_zero_norm (fun n => ?_) h_tendsto_norm
    calc
      ‖min 1 (c / ‖hf.approx n x‖) • hf.approx n x‖ =
          ‖min 1 (c / ‖hf.approx n x‖)‖ * ‖hf.approx n x‖ :=
        norm_smul _ _
      _ ≤ ‖(1 : ℝ)‖ * ‖hf.approx n x‖ := by
        gcongr
        rw [norm_one, Real.norm_of_nonneg]
        · exact min_le_left _ _
        · exact le_min zero_le_one (div_nonneg ((norm_nonneg _).trans hfx) (norm_nonneg _))
      _ = ‖hf.approx n x‖ := by rw [norm_one, one_mul]
  rw [← one_smul ℝ (f x)]
  refine Tendsto.smul ?_ h_tendsto
  have : min 1 (c / ‖f x‖) = 1 := by
    rw [min_eq_left_iff, one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfx0))]
    exact hfx
  nth_rw 2 [this.symm]
  refine Tendsto.min tendsto_const_nhds ?_
  exact Tendsto.div tendsto_const_nhds h_tendsto.norm hfx0
/-
**MeasureTheory.StronglyMeasurable.tendsto_approxBounded_ae** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：tendsto_approxBounded_ae {β} {f : α -> β} [NormedAddCommGroup β] [NormedSp
ace Real β] {m m0 : MeasurableSpace α} {μ : Measure α} (hf : StronglyMeasurable[
m] f) {c : Real} (hf_bound : forallᵐ x ∂μ, ‖f x‖ <= c) : forallᵐ x ∂μ, Tendsto (
fun n => hf.approxBounded c n x) atTop (𝓝 (f x))
参数：hf : StronglyMeasurable[m] f；hf_bound : forallᵐ x ∂μ, ‖f x‖ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approxBounded_of_norm_le`：tends
to_approxBounded_of_norm_le {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace
 Real β] {m : MeasurableSpace α} (hf : StronglyMeasurab…
-/
theorem tendsto_approxBounded_ae {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hf : StronglyMeasurable[m] f) {c : ℝ}
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ∀ᵐ x ∂μ, Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  filter_upwards [hf_bound] with x hfx using tendsto_approxBounded_of_norm_le hf hfx
/-
**MeasureTheory.StronglyMeasurable.norm_approxBounded_le** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：norm_approxBounded_le {β} {f : α -> β} [SeminormedAddCommGroup β] [NormedS
pace Real β] {m : MeasurableSpace α} {c : Real} (hf : StronglyMeasurable[m] f) (
hc : 0 <= c) (n : Nat) (x : α) : ‖hf.approxBounded c n x‖ <= c
参数：hf : StronglyMeasurable[m] f；hc : 0 <= c；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）
-/
theorem norm_approxBounded_le {β} {f : α → β} [SeminormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} {c : ℝ} (hf : StronglyMeasurable[m] f) (hc : 0 ≤ c) (n : ℕ) (x : α) :
    ‖hf.approxBounded c n x‖ ≤ c := by
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  refine (norm_smul_le _ _).trans ?_
  by_cases h0 : ‖hf.approx n x‖ = 0
  · simp only [h0, _root_.div_zero, min_eq_right, zero_le_one, norm_zero, mul_zero]
    exact hc
  rcases le_total ‖hf.approx n x‖ c with h | h
  · rw [min_eq_left _]
    · simpa only [norm_one, one_mul] using h
    · rwa [one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
  · rw [min_eq_right _]
    · rw [norm_div, norm_norm, mul_comm, mul_div, div_eq_mul_inv, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ h0, one_mul, Real.norm_of_nonneg hc]
    · rwa [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_bot_iff** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.stronglyMeasurable_bot_iff [Nonempty β] [T2Space β] :
    StronglyMeasurable[⊥] f ↔ ∃ c, f = fun _ => c := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_iff_true_of_subsingleton]
  refine ⟨fun hf => ?_, fun hf_eq => ?_⟩
  · refine ⟨f hα.some, ?_⟩
    let fs := hf.approx
    have h_fs_tendsto : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)) := hf.tendsto_approx
    have : ∀ n, ∃ c, ∀ x, fs n x = c := fun n => SimpleFunc.simpleFunc_bot (fs n)
    let cs n := (this n).choose
    have h_cs_eq : ∀ n, ⇑(fs n) = fun _ => cs n := fun n => funext (this n).choose_spec
    conv at h_fs_tendsto => enter [x, 1, n]; rw [h_cs_eq]
    have h_tendsto : Tendsto cs atTop (𝓝 (f hα.some)) := h_fs_tendsto hα.some
    ext1 x
    exact tendsto_nhds_unique (h_fs_tendsto x) h_tendsto
  · obtain ⟨c, rfl⟩ := hf_eq
    exact stronglyMeasurable_const

end BasicPropertiesInAnyTopologicalSpace

/-
**MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β] {m 
: MeasurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable f) {t : Set α
} (ht : MeasurableSet t) (hft_zero : forall x in tᶜ, f x = 0) (htμ : SigmaFinite
 (μ.restrict t)) : FinStronglyMeasurable f μ
参数：hf_meas : StronglyMeasurable f；ht : MeasurableSet t；hft_zero : forall x in tᶜ
, f x = 0；htμ : SigmaFinite (μ.restrict t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.restrict_apply`：restrict_apply (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) (a) : restrict f s a = indicator s f a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.support_eq`：support_eq [MeasurableSpace α] [Zer
o β] (f : α ->ₛ β) : support f = ⋃ y in {y in f.range | y != 0}, f ⁻¹' {y}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `MeasureTheory.SimpleFunc.restrict_preimage_singleton`：restrict_preimage_
singleton (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β} (hr : r != 0)
 : restrict f s ⁻¹' {r} = s inter f ⁻¹' {r…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 45 条，此处仅展示前 30 条）
-/
theorem finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β]
    {m : MeasurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable f) {t : Set α}
    (ht : MeasurableSet t) (hft_zero : ∀ x ∈ tᶜ, f x = 0) (htμ : SigmaFinite (μ.restrict t)) :
    FinStronglyMeasurable f μ := by
  have : SigmaFinite (μ.restrict t) := htμ
  let S := spanningSets (μ.restrict t)
  have hS_meas : ∀ n, MeasurableSet (S n) := measurableSet_spanningSets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := SimpleFunc.restrict (f_approx n) (S n ∩ t)
  have h_fs_t_compl : ∀ n, ∀ x, x ∉ t → fs n x = 0 := by
    intro n x hxt
    rw [SimpleFunc.restrict_apply _ ((hS_meas n).inter ht)]
    refine Set.indicator_of_notMem ?_ _
    simp [hxt]
  refine ⟨fs, ?_, fun x => ?_⟩
  · simp_rw [SimpleFunc.support_eq, ← Finset.mem_coe]
    classical
    refine fun n => measure_biUnion_lt_top {y ∈ (fs n).range | y ≠ 0}.finite_toSet fun y hy => ?_
    rw [SimpleFunc.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · let : (y : β) → Decidable (y = 0) := fun y => Classical.propDecidable _
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      exact hy.2
    refine (measure_mono Set.inter_subset_left).trans_lt ?_
    have h_lt_top := measure_spanningSets_lt_top (μ.restrict t) n
    rwa [Measure.restrict_apply' ht] at h_lt_top
  · by_cases hxt : x ∈ t
    swap
    · rw [funext fun n => h_fs_t_compl n x hxt, hft_zero x hxt]
      exact tendsto_const_nhds
    have h : Tendsto (fun n => (f_approx n) x) atTop (𝓝 (f x)) := hf_meas.tendsto_approx x
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x := by
      obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t := by
        rsuffices ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m
        · exact ⟨n, fun m hnm => Set.mem_inter (hn m hnm) hxt⟩
        rsuffices ⟨n, hn⟩ : ∃ n, x ∈ S n
        · exact ⟨n, fun m hnm => monotone_spanningSets (μ.restrict t) hnm hn⟩
        rw [← Set.mem_iUnion, iUnion_spanningSets (μ.restrict t)]
        trivial
      refine ⟨n, fun m hnm => ?_⟩
      simp_rw [fs, SimpleFunc.restrict_apply _ ((hS_meas m).inter ht),
        Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_atTop'] at h ⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rw [hn₁ m ((le_max_left _ _).trans hm)]
    exact hn₂ m ((le_max_right _ _).trans hm)

/-- If the measure is sigma-finite, all strongly measurable functions are
  `FinStronglyMeasurable`. -/
@[aesop 5% apply (rule_sets := [Measurable])]
/-
**MeasureTheory.StronglyMeasurable.finStronglyMeasurable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : TopologicalSpace β] [i
nst_1 : Zero β] {m0 : MeasurableSpace α},   MeasureTheory.StronglyMeasurable f →
     ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ], MeasureTheor
y.FinStronglyMeasurable f μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinit
e`：finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β] {m : M
easurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ

--- 原说明 ---
If the measure is sigma-finite, all strongly measurable functions are
  `FinStronglyMeasurable`.
-/
protected theorem finStronglyMeasurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] : FinStronglyMeasurable f μ :=
  hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [Measure.restrict_univ])

/-- A strongly measurable function is measurable. -/
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.measurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : MeasurableSpace α} [inst 
: TopologicalSpace β]   [TopologicalSpace.PseudoMetrizableSpace β] [inst_2 : Mea
surableSpace β] [BorelSpace β],   MeasureTheory.StronglyMeasurable f → Measurabl
e f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_tendsto_metrizable`：measurable_of_tendsto_metrizable {f : 
Nat -> α -> β} {g : α -> β} (hf : forall i, Measurable (f i)) (lim : Tendsto f a
tTop (𝓝 g)) : Measurab…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …

--- 原说明 ---
A strongly measurable function is measurable.
-/
protected theorem measurable {_ : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : StronglyMeasurable f) : Measurable f :=
  measurable_of_tendsto_metrizable (fun n => (hf.approx n).measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)

/-- A strongly measurable function is almost everywhere measurable. -/
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : MeasurableSpace α} [inst 
: TopologicalSpace β]   [TopologicalSpace.PseudoMetrizableSpace β] [inst_2 : Mea
surableSpace β] [BorelSpace β] {μ : MeasureTheory.Measure α},   MeasureTheory.St
ronglyMeasurable f → AEMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…

--- 原说明 ---
A strongly measurable function is almost everywhere measurable.
-/
protected theorem aemeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {μ : Measure α}
    (hf : StronglyMeasurable f) : AEMeasurable f μ :=
  hf.measurable.aemeasurable
/-
**MeasureTheory.StronglyMeasurable._root_.Continuous.comp_stronglyMeasurable** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.comp_stronglyMeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [TopologicalSpace γ] {g : β → γ} {f : α → β} (hg : Continuous g) (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => g (f x) :=
  ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.tendsto _).comp (hf.tendsto_approx x)⟩

@[to_additive]
nonrec theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) := by
  borelize β
  exact measurableSet_mulSupport hf.measurable
/-
**MeasureTheory.StronglyMeasurable.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m m' : MeasurableSpace α} [in
st : TopologicalSpace β],   MeasureTheory.StronglyMeasurable f → m' ≤ m → Measur
eTheory.StronglyMeasurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber'`：∀ {α : Type u} [inst : Me
asurableSpace α] {β : Type v} (self : MeasureTheory.SimpleFunc α β) (x : β),   M
easurableSet (self.toFun ⁻¹' {x})
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable[m'] f) (h_mono : m' ≤ m) : StronglyMeasurable[m] f := by
  let f_approx : ℕ → @SimpleFunc α m β := fun n =>
    @SimpleFunc.mk α m β
      (hf.approx n)
      (fun x => h_mono _ (SimpleFunc.measurableSet_fiber' _ x))
      (SimpleFunc.finite_range (hf.approx n))
  exact ⟨f_approx, hf.tendsto_approx⟩

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} [in
st : TopologicalSpace β]   [inst_1 : TopologicalSpace γ] {f : α → β × γ},   Meas
ureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun x => (f x)
.1
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
protected theorem fst {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β × γ} (hf : StronglyMeasurable f) : StronglyMeasurable fun x ↦ (f x).1 :=
  continuous_fst.comp_stronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} [in
st : TopologicalSpace β]   [inst_1 : TopologicalSpace γ] {f : α → β × γ},   Meas
ureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun x => (f x)
.2
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
protected theorem snd {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β × γ} (hf : StronglyMeasurable f) : StronglyMeasurable fun x ↦ (f x).2 :=
  continuous_snd.comp_stronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} [in
st : TopologicalSpace β]   [inst_1 : TopologicalSpace γ] {f : α → β} {g : α → γ}
,   MeasureTheory.StronglyMeasurable f →     MeasureTheory.StronglyMeasurable g 
→ MeasureTheory.StronglyMeasurable fun x => (f x, g x)
参数：f x, g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem prodMk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β} {g : α → γ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => (f x, g x) := by
  refine ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => ?_⟩
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_approx x) (hg.tendsto_approx x)

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.comp_measurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.StronglyMeasurable`。
形式化陈述：comp_measurable [TopologicalSpace β] {_ : MeasurableSpace α} {_ : Measurab
leSpace γ} {f : α -> β} {g : γ -> α} (hf : StronglyMeasurable f) (hg : Measurabl
e g) : StronglyMeasurable (f ∘ g)
参数：hf : StronglyMeasurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
theorem comp_measurable [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → β} {g : γ → α} (hf : StronglyMeasurable f) (hg : Measurable g) :
    StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩
/-
**MeasureTheory.StronglyMeasurable.of_uncurry_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.StronglyMeasurable`。
形式化陈述：of_uncurry_left [TopologicalSpace β] {_ : MeasurableSpace α} {_ : Measurab
leSpace γ} {f : α -> γ -> β} (hf : StronglyMeasurable (uncurry f)) {x : α} : Str
onglyMeasurable (f x)
参数：hf : StronglyMeasurable (uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
theorem of_uncurry_left [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prodMk_left
/-
**MeasureTheory.StronglyMeasurable.of_uncurry_right** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.StronglyMeasurable`。
形式化陈述：of_uncurry_right [TopologicalSpace β] {_ : MeasurableSpace α} {_ : Measura
bleSpace γ} {f : α -> γ -> β} (hf : StronglyMeasurable (uncurry f)) {y : γ} : St
ronglyMeasurable fun x => f x y
参数：hf : StronglyMeasurable (uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem of_uncurry_right [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {y : γ} :
    StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prodMk_right
/-
**MeasureTheory.StronglyMeasurable.prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : MeasurableSpace α} {x_
1 : MeasurableSpace β}   [inst : TopologicalSpace γ] {f : β × α → γ},   MeasureT
heory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun z => f z.swap
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
protected theorem prod_swap {_ : MeasurableSpace α} {_ : MeasurableSpace β} [TopologicalSpace γ]
    {f : β × α → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.swap) :=
  hf.comp_measurable measurable_swap
/-
**MeasureTheory.StronglyMeasurable.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : MeasurableSpace α} [mβ
 : MeasurableSpace β]   [inst : TopologicalSpace γ] {f : α → γ},   MeasureTheory
.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun z => f z.1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
protected theorem comp_fst {_ : MeasurableSpace α} [mβ : MeasurableSpace β] [TopologicalSpace γ]
    {f : α → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.1) :=
  hf.comp_measurable measurable_fst
/-
**MeasureTheory.StronglyMeasurable.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [mα : MeasurableSpace α] {x
 : MeasurableSpace β}   [inst : TopologicalSpace γ] {f : β → γ},   MeasureTheory
.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun z => f z.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
protected theorem comp_snd [mα : MeasurableSpace α] {_ : MeasurableSpace β} [TopologicalSpace γ]
    {f : β → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.2) :=
  hf.comp_measurable measurable_snd

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.StronglyMeasurable.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {mα : MeasurableSpace α} [in
st : TopologicalSpace β] [inst_1 : Mul β]   [ContinuousMul β],   MeasureTheory.S
tronglyMeasurable f → MeasureTheory.StronglyMeasurable g → MeasureTheory.Strongl
yMeasurable (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) : 
StronglyMeasurable fun x => f x * c
参数：hf : StronglyMeasurable f；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Mul β
]   [ContinuousMul β],   M…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul stronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) : 
StronglyMeasurable fun x => c * f x
参数：hf : StronglyMeasurable f；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Mul β
]   [ContinuousMul β],   M…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  stronglyMeasurable_const.mul hf

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]
/-
**MeasureTheory.StronglyMeasurable.pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {mα : MeasurableSpace α} [inst
 : TopologicalSpace β] [inst_1 : Monoid β]   [ContinuousMul β], MeasureTheory.St
ronglyMeasurable f → ∀ (n : ℕ), MeasureTheory.StronglyMeasurable (f ^ n)
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.pow`：Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : 
M} (hf : Tendsto f l (𝓝 x)) (n : Nat) : Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem pow [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : ℕ) :
    StronglyMeasurable (f ^ n) :=
  ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.StronglyMeasurable.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {mα : MeasurableSpace α} [inst
 : TopologicalSpace β] [inst_1 : Inv β]   [ContinuousInv β], MeasureTheory.Stron
glyMeasurable f → MeasureTheory.StronglyMeasurable f⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem inv [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f) :
    StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {mα : MeasurableSpace α} [inst
 : TopologicalSpace β] [inst_1 : Inv β]   [ContinuousInv β], MeasureTheory.Stron
glyMeasurable f → MeasureTheory.StronglyMeasurable f⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem inv₀ [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : StronglyMeasurable f) : StronglyMeasurable f⁻¹ := by
  borelize β
  refine ⟨fun n => ((hf.approx n).restrict {x | f x ≠ 0})⁻¹, fun x => ?_⟩
  have : MeasurableSet {x | f x ≠ 0} := ((MeasurableSet.singleton 0).preimage hf.measurable).compl
  by_cases h : f x = 0
  · simp_all only [ne_eq, measurableSet_setOfPred, SimpleFunc.coe_inv, SimpleFunc.coe_restrict,
      Pi.inv_apply, mem_ofPred_eq, not_true_eq_false, not_false_eq_true, indicator_of_notMem,
      _root_.inv_zero]
    exact tendsto_const_nhds
  · simp_all only [ne_eq, measurableSet_setOfPred, SimpleFunc.coe_inv, SimpleFunc.coe_restrict,
      Pi.inv_apply, mem_ofPred_eq, not_false_eq_true, indicator_of_mem]
    apply (hf.tendsto_approx x).inv₀ h

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
/-
**MeasureTheory.StronglyMeasurable.div'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {mα : MeasurableSpace α} [in
st : TopologicalSpace β] [inst_1 : Div β]   [ContinuousDiv β],   MeasureTheory.S
tronglyMeasurable f → MeasureTheory.StronglyMeasurable g → MeasureTheory.Strongl
yMeasurable (f / g)
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem div' [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：div [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpac
e β] (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : StronglyMeasurabl
e (f / g)
参数：hf : StronglyMeasurable f；hg : StronglyMeasurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
theorem div₀ [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) (h₀ : ∀ (x : α), g x ≠ 0) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n,
    fun x => (hf.tendsto_approx x).div (hg.tendsto_approx x) (h₀ x)⟩

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：div [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpac
e β] (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : StronglyMeasurabl
e (f / g)
参数：hf : StronglyMeasurable f；hg : StronglyMeasurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
theorem div [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f / g) := by
  borelize β
  refine ⟨fun n => hf.approx n / (hg.approx n).restrict {x | g x ≠ 0}, fun x => ?_⟩
  have : MeasurableSet {x | g x ≠ 0} := ((MeasurableSet.singleton 0).preimage hg.measurable).compl
  by_cases h : g x = 0
  · simp_all only [ne_eq, SimpleFunc.coe_div, SimpleFunc.coe_restrict, Pi.div_apply, mem_ofPred_eq,
      not_true_eq_false, not_false_eq_true, indicator_of_notMem, _root_.div_zero]
    exact tendsto_const_nhds
  · simp_all only [ne_eq, SimpleFunc.coe_div, SimpleFunc.coe_restrict,
      Pi.div_apply, mem_ofPred_eq, not_false_eq_true, indicator_of_mem]
    exact (hf.tendsto_approx x).div (hg.tendsto_approx x) h

@[to_additive]
/-
**MeasureTheory.StronglyMeasurable.mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.StronglyMeasurable`。
形式化陈述：mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurabl
e f) : StronglyMeasurable (f * g) ↔ StronglyMeasurable g
参数：hf : StronglyMeasurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Mul β
]   [ContinuousMul β],   M…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.StronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Inv β] 
  [ContinuousInv β], Measu…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (f * g) ↔ StronglyMeasurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
/-
**MeasureTheory.StronglyMeasurable.mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.StronglyMeasurable`。
形式化陈述：mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable
 f) : StronglyMeasurable (g * f) ↔ StronglyMeasurable g
参数：hf : StronglyMeasurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mul_iff_right`：mul_iff_right [CommGroup
 β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) : StronglyMeasurable (f *
 g) ↔ StronglyMeasurable g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (g * f) ↔ StronglyMeasurable g :=
  mul_comm g f ▸ mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.StronglyMeasurable.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : Topologic
alSpace β] {𝕜 : Type u_5}   [inst_1 : TopologicalSpace 𝕜] [inst_2 : SMul 𝕜 β] [C
ontinuousSMul 𝕜 β] {f : α → 𝕜} {g : α → β},   MeasureTheory.StronglyMeasurable f
 → MeasureTheory.StronglyMeasurable g → MeasureTheory.StronglyMeasurable (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
-/
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f • g) :=
  continuous_smul.comp_stronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**MeasureTheory.StronglyMeasurable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {mα : MeasurableSpace α} [inst
 : TopologicalSpace β] {𝕜 : Type u_5}   [inst_1 : SMul 𝕜 β] [ContinuousConstSMul
 𝕜 β],   MeasureTheory.StronglyMeasurable f → ∀ (c : 𝕜), MeasureTheory.StronglyM
easurable (c • f)
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := StronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := StronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : Topologic
alSpace β] {𝕜 : Type u_5}   [inst_1 : TopologicalSpace 𝕜] [inst_2 : SMul 𝕜 β] [C
ontinuousSMul 𝕜 β] {f : α → 𝕜},   MeasureTheory.StronglyMeasurable f → ∀ (c : β)
, MeasureTheory.StronglyMeasurable fun x => f x • c
参数：c : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_stronglyMeasurable (hf.prodMk stronglyMeasurable_const)

/-- Pointwise star on functions induced from continuous star preserves strong measurability. -/
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.star** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {R : Type u_5} [inst : MeasurableSpace α] [inst_1 : Star 
R] [inst_2 : TopologicalSpace R]   [ContinuousStar R] (f : α → R), MeasureTheory
.StronglyMeasurable f → MeasureTheory.StronglyMeasurable (star f)
参数：f : α → R；star f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.star`：Filter.Tendsto.star {f : α -> R} {l : Filter α} {y 
: R} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => star (f x)) l (𝓝 (star y))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …

--- 原说明 ---
Pointwise star on functions induced from continuous star preserves strong measur
ability.
-/
protected theorem star {R : Type*} [MeasurableSpace α] [Star R] [TopologicalSpace R]
    [ContinuousStar R] (f : α → R) (hf : StronglyMeasurable f) : StronglyMeasurable (star f) :=
  ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩

/-- In a normed vector space, the addition of a measurable function and a strongly measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the addition of two measurable functions. -/
/-
**MeasureTheory.StronglyMeasurable._root_.Measurable.add_stronglyMeasurable** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a normed vector space, the addition of a measurable function and a strongly m
easurable
function is measurable. Note that this is not true without further second-counta
bility assumptions
for the addition of two measurable functions.
-/
theorem _root_.Measurable.add_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddCancelMonoid E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g + f) := by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x ↦ g x + φ n x) atTop (𝓝 (g + f)) :=
    tendsto_pi_nhds.2 (fun x ↦ tendsto_const_nhds.add (hφ x))
  apply measurable_of_tendsto_metrizable (fun n ↦ ?_) this
  exact hg.add_simpleFunc _

/-- In a normed vector space, the subtraction of a measurable function and a strongly measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the subtraction of two measurable functions. -/
/-
**MeasureTheory.StronglyMeasurable._root_.Measurable.sub_stronglyMeasurable** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a normed vector space, the subtraction of a measurable function and a strongl
y measurable
function is measurable. Note that this is not true without further second-counta
bility assumptions
for the subtraction of two measurable functions.
-/
theorem _root_.Measurable.sub_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddGroup E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [ContinuousNeg E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g - f) := by
  rw [sub_eq_add_neg]
  exact hg.add_stronglyMeasurable hf.neg

/-- In a normed vector space, the addition of a strongly measurable function and a measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the addition of two measurable functions. -/
/-
**MeasureTheory.StronglyMeasurable._root_.Measurable.stronglyMeasurable_add** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a normed vector space, the addition of a strongly measurable function and a m
easurable
function is measurable. Note that this is not true without further second-counta
bility assumptions
for the addition of two measurable functions.
-/
theorem _root_.Measurable.stronglyMeasurable_add
    {α E : Type*} {_ : MeasurableSpace α} [AddCancelMonoid E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (f + g) := by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x ↦ φ n x + g x) atTop (𝓝 (f + g)) :=
    tendsto_pi_nhds.2 (fun x ↦ (hφ x).add tendsto_const_nhds)
  apply measurable_of_tendsto_metrizable (fun n ↦ ?_) this
  exact hg.simpleFunc_add _

end Arithmetic

section MulAction

variable {M G G₀ : Type*}
variable [TopologicalSpace β]
variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]
variable [Group G] [MulAction G β] [ContinuousConstSMul G β]
variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_const_smul_iff** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.stronglyMeasurable_const_smul_iff {m : MeasurableSpace α} (c : G) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

nonrec theorem _root_.IsUnit.stronglyMeasurable_const_smul_iff {_ : MeasurableSpace α} {c : M}
    (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ stronglyMeasurable_const_smul_iff u
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_const_smul_iff** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.stronglyMeasurable_const_smul_iff₀ {_ : MeasurableSpace α} {c : G₀} (hc : c ≠ 0) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff

end MulAction

section Order

variable [MeasurableSpace α] [TopologicalSpace β]

open Filter

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} [inst : MeasurableSpace α] [
inst_1 : TopologicalSpace β] [inst_2 : Max β]   [ContinuousSup β],   MeasureTheo
ry.StronglyMeasurable f → MeasureTheory.StronglyMeasurable g → MeasureTheory.Str
onglyMeasurable (f ⊔ g)
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.sup_nhds`：sup_nhds [Max L] [ContinuousSup L] (hf : Tendst
o f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y
))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem sup [Max β] [ContinuousSup β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊔ g) :=
  ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} [inst : MeasurableSpace α] [
inst_1 : TopologicalSpace β] [inst_2 : Min β]   [ContinuousInf β],   MeasureTheo
ry.StronglyMeasurable f → MeasureTheory.StronglyMeasurable g → MeasureTheory.Str
onglyMeasurable (f ⊓ g)
参数：f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.inf_nhds`：inf_nhds [Min L] [ContinuousInf L] (hf : Tendst
o f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y
))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
-/
protected theorem inf [Min β] [ContinuousInf β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊓ g) :=
  ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.oneLePart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : MeasurableSpace α] [in
st_1 : TopologicalSpace β] [inst_2 : Group β]   [inst_3 : Lattice β] [Continuous
Sup β],   MeasureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable 
fun x => (f x)⁺ᵐ
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace β] [inst_2 : M
ax β]   [ContinuousSup β],…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
protected theorem oneLePart [Group β] [Lattice β] [ContinuousSup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x ↦ oneLePart (f x) :=
  hf.sup stronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable.leOnePart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : MeasurableSpace α] [in
st_1 : TopologicalSpace β] [inst_2 : Group β]   [inst_3 : Lattice β] [Continuous
Sup β] [ContinuousInv β],   MeasureTheory.StronglyMeasurable f → MeasureTheory.S
tronglyMeasurable fun x => (f x)⁻ᵐ
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace β] [inst_2 : M
ax β]   [ContinuousSup β],…
· 使用定理 `MeasureTheory.StronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Inv β] 
  [ContinuousInv β], Measu…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
protected theorem leOnePart [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x ↦ leOnePart (f x) :=
  hf.inv.sup stronglyMeasurable_const

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable._root_.List.stronglyMeasurable_prod** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.stronglyMeasurable_prod (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  induction l with
  | nil => exact stronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable._root_.List.stronglyMeasurable_fun_prod** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.stronglyMeasurable_fun_prod (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}


@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable._root_.Multiset.stronglyMeasurable_prod** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Multiset.stronglyMeasurable_prod (l : Multiset (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable._root_.Multiset.stronglyMeasurable_fun_prod**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Multiset.stronglyMeasurable_fun_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable._root_.Finset.stronglyMeasurable_prod** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.stronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.StronglyMeasurable._root_.Finset.stronglyMeasurable_fun_prod** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.stronglyMeasurable_fun_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i ∈ s, f i a := by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod hf

variable {n : MeasurableSpace β} in
/-- Compositional version of `Finset.stronglyMeasurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Finset.stronglyMeasurable_sum` for use by `fun_prop`. -/]
/-
**MeasureTheory.StronglyMeasurable.Finset.stronglyMeasurable_prod_apply** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable.Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : CommMonoid M] [inst
_1 : TopologicalSpace M] [ContinuousMul M]   {m : MeasurableSpace α} {n : Measur
ableSpace β} {ι : Type u_6} {f : ι → α → β → M} {g : α → β} {s : Finset ι},   (∀
 i ∈ s, MeasureTheory.StronglyMeasurable ↿(f i)) →     Measurable g → MeasureThe
ory.StronglyMeasurable fun a => (∏ i ∈ s, f i a) (g a)
参数：∀ i ∈ s, MeasureTheory.StronglyMeasurable ↿(f i)；∏ i ∈ s, f i a；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.stronglyMeasurable_fun_prod`：∀ {α : Type u_1} {M : Type u_5} [ins
t : CommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousMul M]   {m : Measura
bleSpace α} {ι : Type u_…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma Finset.stronglyMeasurable_prod_apply {ι : Type*} {f : ι → α → β → M} {g : α → β}
    {s : Finset ι} (hf : ∀ i ∈ s, StronglyMeasurable ↿(f i)) (hg : Measurable g) :
    StronglyMeasurable fun a ↦ (∏ i ∈ s, f i a) (g a) := by
  simp only [Finset.prod_apply]; fun_prop

end CommMonoid

/-- The range of a strongly measurable function is separable. -/
/-
**MeasureTheory.StronglyMeasurable.isSeparable_range** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : MeasurableSpace α} [inst 
: TopologicalSpace β],   MeasureTheory.StronglyMeasurable f → TopologicalSpace.I
sSeparable (Set.range f)
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用定理 `TopologicalSpace.IsSeparable.iUnion`：∀ {α : Type u} [t : TopologicalSpac
e α] {ι : Sort u_2} [Countable ι] {s : ι → Set α},   (∀ (i : ι), TopologicalSpac
e.IsSeparable (s i)) → To…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.Finite.isSeparable`：∀ {α : Type u} [t : TopologicalSpace α] {s : Set
 α}, s.Finite → TopologicalSpace.IsSeparable s
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite
· 使用定理 `TopologicalSpace.IsSeparable.mono`：∀ {α : Type u} [t : TopologicalSpace 
α] {s u : Set α},   TopologicalSpace.IsSeparable s → u ⊆ s → TopologicalSpace.Is
Separable u
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The range of a strongly measurable function is separable.
-/
protected theorem isSeparable_range {m : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable f) : TopologicalSpace.IsSeparable (range f) := by
  have : IsSeparable (closure (⋃ n, range (hf.approx n))) :=
    .closure <| .iUnion fun n => (hf.approx n).finite_range.isSeparable
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  filter_upwards with n
  apply mem_iUnion_of_mem n
  exact mem_range_self _
/-
**MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：separableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalS
pace β] [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b : β} : Separabl
eSpace (range f union {b} : Set β)
参数：hf : StronglyMeasurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsSeparable.separableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X},   Topo
logicalSpace.IsSeparable s → Topo…
· 使用定理 `TopologicalSpace.IsSeparable.union`：∀ {α : Type u} [t : TopologicalSpace
 α] {s u : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le u → TopologicalSpace.…
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用定理 `Set.Finite.isSeparable`：∀ {α : Type u} [t : TopologicalSpace α] {s : Set
 α}, s.Finite → TopologicalSpace.IsSeparable s
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem separableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b : β} :
    SeparableSpace (range f ∪ {b} : Set β) :=
  letI := pseudoMetrizableSpacePseudoMetric β
  (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace

section SecondCountableStronglyMeasurable

variable {mα : MeasurableSpace α} [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable._root_.Measurable.stronglyMeasurable** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a space with second countable topology, measurable implies strongly measurabl
e.
-/
theorem _root_.Measurable.stronglyMeasurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (hf : Measurable f) :
    StronglyMeasurable f := by
  let := pseudoMetrizableSpacePseudoMetric β
  nontriviality β; inhabit β
  exact ⟨SimpleFunc.approxOn f hf Set.univ default (Set.mem_univ _), fun x ↦
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ _) (by simp)⟩

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_iff_measurable** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a space with second countable topology, strongly measurable and measurable ar
e equivalent.
-/
theorem _root_.stronglyMeasurable_iff_measurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [BorelSpace β] [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_id** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.stronglyMeasurable_id [TopologicalSpace α] [PseudoMetrizableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] : StronglyMeasurable (id : α → α) :=
  measurable_id.stronglyMeasurable

end SecondCountableStronglyMeasurable

/-- A function is strongly measurable if and only if it is measurable and has separable
range. -/
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_iff_measurable_sepa
rable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is strongly measurable if and only if it is measurable and has separa
ble
range.
-/
theorem _root_.stronglyMeasurable_iff_measurable_separable {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] :
    StronglyMeasurable f ↔ Measurable f ∧ IsSeparable (range f) := by
  refine ⟨fun H ↦ ⟨H.measurable, H.isSeparable_range⟩, fun ⟨Hm, Hsep⟩  ↦ ?_⟩
  have := Hsep.secondCountableTopology
  have Hm' : StronglyMeasurable (rangeFactorization f) := Hm.subtype_mk.stronglyMeasurable
  exact continuous_subtype_val.comp_stronglyMeasurable Hm'

/-- A continuous function is strongly measurable when either the source space or the target space
is second-countable. -/
/-
**MeasureTheory.StronglyMeasurable._root_.Continuous.stronglyMeasurable** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function is strongly measurable when either the source space or the
 target space
is second-countable.
-/
theorem _root_.Continuous.stronglyMeasurable [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α → β} (hf : Continuous f) :
    StronglyMeasurable f := by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine ⟨hf.measurable, ?_⟩
    exact isSeparable_range hf
  · exact hf.measurable.stronglyMeasurable

/-- A continuous function whose support is contained in a compact set is strongly measurable. -/
@[to_additive /-- A continuous function whose support is contained in a compact set is strongly
measurable. -/]
/-
**MeasureTheory.StronglyMeasurable._root_.Continuous.stronglyMeasurable_of_mulSu
pport_subset_isCompact** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurab
le`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [One β] {f : α → β} (hf : Continuous f) {k : Set α}
    (hk : IsCompact k) (h'f : mulSupport f ⊆ k) : StronglyMeasurable f := by
  borelize β
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨hf.measurable, (isCompact_range_of_mulSupport_subset_isCompact hf hk h'f).isSeparable⟩

/-- A continuous function with compact support is strongly measurable. -/
@[to_additive /-- A continuous function with compact support is strongly measurable. -/]
/-
**MeasureTheory.StronglyMeasurable._root_.Continuous.stronglyMeasurable_of_hasCo
mpactMulSupport** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function with compact support is strongly measurable.
-/
theorem _root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [One β] {f : α → β} (hf : Continuous f)
    (h'f : HasCompactMulSupport f) : StronglyMeasurable f :=
  hf.stronglyMeasurable_of_mulSupport_subset_isCompact h'f (subset_mulTSupport f)

/-- A continuous function with compact support on a product space is strongly measurable for the
product sigma-algebra. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
/-
**MeasureTheory.StronglyMeasurable._root_.HasCompactSupport.stronglyMeasurable_o
f_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function with compact support on a product space is strongly measur
able for the
product sigma-algebra. The subtlety is that we do not assume that the spaces are
 separable, so the
product of the Borel sigma algebras might not contain all open sets, but still i
t contains enough
of them to approximate compactly supported continuous functions.
-/
lemma _root_.HasCompactSupport.stronglyMeasurable_of_prod {X Y : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [TopologicalSpace α] [PseudoMetrizableSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    StronglyMeasurable f := by
  borelize α
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨h'f.measurable_of_prod hf, ?_⟩
  let : PseudoMetricSpace α := pseudoMetrizableSpacePseudoMetric α
  exact IsCompact.isSeparable (s := range f) (h'f.isCompact_range hf)

/-- If `g` is a topological embedding, then `f` is strongly measurable iff `g ∘ f` is. -/
/-
**MeasureTheory.StronglyMeasurable._root_.Embedding.comp_stronglyMeasurable_iff*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a topological embedding, then `f` is strongly measurable iff `g ∘ f` i
s.
-/
theorem _root_.Embedding.comp_stronglyMeasurable_iff {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [TopologicalSpace γ] [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β}
    (hg : IsEmbedding g) : (StronglyMeasurable fun x => g (f x)) ↔ StronglyMeasurable f := by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_stronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by
          rw [rangeFactorization_surjective.range_eq]
          exact isClosed_univ }
    have : Measurable (G ∘ f) := Measurable.subtype_mk H.measurable
    exact hG.measurableEmbedding.measurable_comp_iff.1 this
  · have : IsSeparable (g ⁻¹' range (g ∘ f)) := hg.isSeparable_preimage H.isSeparable_range
    rwa [range_comp, hg.injective.preimage_image] at this

/-- A sequential limit of strongly measurable functions is strongly measurable. -/
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_of_tendsto** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequential limit of strongly measurable functions is strongly measurable.
-/
theorem _root_.stronglyMeasurable_of_tendsto {ι : Type*} {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} (hf : ∀ i, StronglyMeasurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    StronglyMeasurable g := by
  borelize β
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).measurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (closure (⋃ i, range (f (v i)))) :=
      .closure <| .iUnion fun i => (hf (v i)).isSeparable_range
    apply this.mono
    rintro _ ⟨x, rfl⟩
    rw [tendsto_pi_nhds] at lim
    apply mem_closure_of_tendsto ((lim x).comp hv)
    filter_upwards with n
    apply mem_iUnion_of_mem n
    exact mem_range_self _
/-
**MeasureTheory.StronglyMeasurable.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {m : MeasurableSpace α} [ins
t : TopologicalSpace β] {s : Set α}   {x : DecidablePred fun x => x ∈ s},   Meas
urableSet s →     MeasureTheory.StronglyMeasurable f →       MeasureTheory.Stron
glyMeasurable g → MeasureTheory.StronglyMeasurable (s.piecewise f g)
参数：s.piecewise f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected theorem piecewise {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
    {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (Set.piecewise s f g) := by
  refine ⟨fun n => SimpleFunc.piecewise s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x ∈ s
  · simpa [@Set.piecewise_eq_of_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hf.tendsto_approx x
  · simpa [@Set.piecewise_eq_of_notMem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hg.tendsto_approx x

/-- this is slightly different from `StronglyMeasurable.piecewise`. It can be used to show
`StronglyMeasurable (ite (x=0) 0 1)` by
`exact StronglyMeasurable.ite (measurableSet_singleton 0) stronglyMeasurable_const
stronglyMeasurable_const`, but replacing `StronglyMeasurable.ite` by
`StronglyMeasurable.piecewise` in that example proof does not work. -/
/-
**MeasureTheory.StronglyMeasurable.ite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {x : MeasurableSpace α} [ins
t : TopologicalSpace β] {p : α → Prop}   {x_1 : DecidablePred p},   MeasurableSe
t {a | p a} →     MeasureTheory.StronglyMeasurable f →       MeasureTheory.Stron
glyMeasurable g → MeasureTheory.StronglyMeasurable fun x => if p x then f x else
 g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.piecewise`：∀ {α : Type u_1} {β : Type u
_2} {f g : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β] {s : Set α
}   {x : DecidablePred fun x => …

--- 原说明 ---
this is slightly different from `StronglyMeasurable.piecewise`. It can be used t
o show
`StronglyMeasurable (ite (x=0) 0 1)` by
`exact StronglyMeasurable.ite (measurableSet_singleton 0) stronglyMeasurable_con
st
stronglyMeasurable_const`, but replacing `StronglyMeasurable.ite` by
`StronglyMeasurable.piecewise` in that example proof does not work.
-/
protected theorem ite {_ : MeasurableSpace α} [TopologicalSpace β] {p : α → Prop}
    {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a }) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun x => ite (p x) (f x) (g x) :=
  StronglyMeasurable.piecewise hp hf hg
/-
**MeasureTheory.StronglyMeasurable.dite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {m : MeasurableSpace α} [inst 
: TopologicalSpace β]   [inst_1 : (x : α) → Decidable (x ∈ s)] {f : ↑s → β},   M
easureTheory.StronglyMeasurable f →     ∀ {g : ↑sᶜ → β},       MeasureTheory.Str
onglyMeasurable g →         MeasurableSet s → MeasureTheory.StronglyMeasurable f
un x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩
参数：x : α；x ∈ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.dite_toFun`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] (s : Set α) (hs : MeasurableSet s)   (f : MeasureTheory.
SimpleFunc (↑s) β) (g : M…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
protected theorem dite {s : Set α} {m : MeasurableSpace α} [TopologicalSpace β]
    [(x : α) → Decidable (x ∈ s)] {f : ↑s → β} (hf : StronglyMeasurable f)
    {g : ↑sᶜ → β} (hg : StronglyMeasurable g) (hs : MeasurableSet s) :
    StronglyMeasurable fun x ↦ if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ := by
  refine ⟨fun n ↦ SimpleFunc.dite s hs (hf.approx n) (hg.approx n), fun x ↦ ?_⟩
  by_cases hx : x ∈ s
  · simpa [hx] using hf.tendsto_approx ⟨x, hx⟩
  · simpa [hx] using hg.tendsto_approx ⟨x, hx⟩

/-- If a function is continuous outside of a countable set, then it is strongly measurable. -/
/-
**MeasureTheory.StronglyMeasurable._root_.ContinuousOn.stronglyMeasurable_of_cou
ntable_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function is continuous outside of a countable set, then it is strongly meas
urable.
-/
theorem _root_.ContinuousOn.stronglyMeasurable_of_countable_compl [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α → β} {s : Set α} (hf : ContinuousOn f s)
    (hs : (sᶜ).Countable) : StronglyMeasurable f := by
  classical
  have h's : MeasurableSet s := by simpa using hs.measurableSet.compl
  have : f = fun x ↦ if hx : x ∈ s then f (⟨x, hx⟩ : s) else f (⟨x, hx⟩ : (sᶜ : Set α)) := by simp
  rw [this]
  apply StronglyMeasurable.dite (f := fun x ↦ f x) (g := fun x ↦ f x) ?_ ?_ h's
  · have : SecondCountableTopologyEither s β := by cases h.out <;> infer_instance
    exact (continuousOn_iff_continuous_domRestrict.1 hf).stronglyMeasurable
  · have := hs.to_subtype
    exact MeasureTheory.StronglyMeasurable.of_discrete

/-- If a function is continuous outside of a countable set, then it is strongly measurable. -/
/-
**MeasureTheory.StronglyMeasurable.of_countable_not_continuousAt** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：of_countable_not_continuousAt [MeasurableSpace α] [TopologicalSpace α] [Op
ensMeasurableSpace α] [MeasurableSingletonClass α] [TopologicalSpace β] [PseudoM
etrizableSpace β] [h : SecondCountableTopologyEither α β] {f : α -> β} (hf : Set
.Countable {x | ¬ ContinuousAt f x}) : StronglyMeasurable f
参数：hf : Set.Countable {x | ¬ ContinuousAt f x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousOn.stronglyMeasurable_of_countable_compl`：∀ {α : Type u_1} {β 
: Type u_2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasu
rableSpace α]   [MeasurableSingletonClas…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a function is continuous outside of a countable set, then it is strongly meas
urable.
-/
theorem of_countable_not_continuousAt [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α → β}
    (hf : Set.Countable {x | ¬ ContinuousAt f x}) : StronglyMeasurable f := by
  have : ContinuousOn f {x | ContinuousAt f x} := fun x hx ↦ hx.continuousWithinAt
  apply this.stronglyMeasurable_of_countable_compl
  convert hf
  grind

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable._root_.MeasurableEmbedding.stronglyMeasurable
_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.stronglyMeasurable_extend {f : α → β} {g : α → γ} {g' : γ → β}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hg' : StronglyMeasurable g') :
    StronglyMeasurable (Function.extend g f g') := by
  refine ⟨fun n => SimpleFunc.extend (hf.approx n) g hg (hg'.approx n), ?_⟩
  intro x
  by_cases hx : ∃ y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [SimpleFunc.extend_apply, hg.injective, Injective.extend_apply] using
      hf.tendsto_approx y
  · simpa only [hx, SimpleFunc.extend_apply', not_false_iff, extend_apply'] using
      hg'.tendsto_approx x
/-
**MeasureTheory.StronglyMeasurable._root_.MeasurableEmbedding.exists_stronglyMea
surable_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.exists_stronglyMeasurable_extend {f : α → β} {g : α → γ}
    {_ : MeasurableSpace α} {_ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hne : γ → Nonempty β) :
    ∃ f' : γ → β, StronglyMeasurable f' ∧ f' ∘ g = f :=
  ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun _ => hg.injective.extend_apply _ _ _⟩
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_of_stronglyMeasurab
le_union_cover** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.stronglyMeasurable_of_stronglyMeasurable_union_cover {m : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ ⊆ s ∪ t) (hc : StronglyMeasurable fun a : s => f a)
    (hd : StronglyMeasurable fun a : t => f a) : StronglyMeasurable f := by
  nontriviality β; inhabit β
  suffices Function.extend Subtype.val (fun x : s ↦ f x)
      (Function.extend (↑) (fun x : t ↦ f x) fun _ ↦ default) = f from
    this ▸ (MeasurableEmbedding.subtype_coe hs).stronglyMeasurable_extend hc <|
      (MeasurableEmbedding.subtype_coe ht).stronglyMeasurable_extend hd stronglyMeasurable_const
  ext x
  by_cases hxs : x ∈ s
  · lift x to s using hxs
    simp
  · lift x to t using (h trivial).resolve_left hxs
    rw [extend_apply', Subtype.coe_injective.extend_apply]
    exact fun ⟨y, hy⟩ ↦ hxs <| hy ▸ y.2
/-
**MeasureTheory.StronglyMeasurable._root_.stronglyMeasurable_of_restrict_of_rest
rict_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.stronglyMeasurable_of_restrict_of_restrict_compl {_ : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : StronglyMeasurable (s.domRestrict f)) (h₂ : StronglyMeasurable (sᶜ.domRestrict f)) :
    StronglyMeasurable f :=
  stronglyMeasurable_of_stronglyMeasurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁
    h₂

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : MeasurableSpace α} [inst 
: TopologicalSpace β] [inst_1 : Zero β],   MeasureTheory.StronglyMeasurable f → 
∀ {s : Set α}, MeasurableSet s → MeasureTheory.StronglyMeasurable (s.indicator f
)
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.piecewise`：∀ {α : Type u_1} {β : Type u
_2} {f g : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β] {s : Set α
}   {x : DecidablePred fun x => …
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
protected theorem indicator {_ : MeasurableSpace α} [TopologicalSpace β] [Zero β]
    (hf : StronglyMeasurable f) {s : Set α} (hs : MeasurableSet s) :
    StronglyMeasurable (s.indicator f) :=
  hf.piecewise hs stronglyMeasurable_const

/-- To prove that a property holds for any strongly measurable function, it is enough to show
that it holds for constant indicator functions of measurable sets and that it is closed under
addition and pointwise limit.

To use in an induction proof, the syntax is
`induction f, hf using StronglyMeasurable.induction with`. -/
/-
**MeasureTheory.StronglyMeasurable.induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.StronglyMeasurable`。
形式化陈述：induction [MeasurableSpace α] [AddZeroClass β] [TopologicalSpace β] {P : (
f : α -> β) -> StronglyMeasurable f -> Prop} (ind : forall c ⦃s : Set α⦄ (hs : M
easurableSet s), P (s.indicator fun _ => c) (stronglyMeasurable_const.indicator 
hs)) (add : forall ⦃f g : α -> β⦄ (hf : StronglyMeasurable f) (hg : StronglyMeas
urable g) (hfg : StronglyMeasurable (f + g)), Disjoint f.support g.support -> P 
f hf -> P g hg -> P (f + g) hfg) (lim : forall ⦃f : Nat -> α -> β⦄ ⦃g : α -> β⦄ 
(hf : forall n, StronglyMe
参数：f : α -> β；ind : forall c ⦃s : Set α⦄ (hs : MeasurableSet s), P (s.indicator 
fun _ => c) (stronglyMeasurable_const.indicator hs)；add : forall ⦃f g : α -> β⦄ 
(hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (hfg : StronglyMeasurabl
e (f + g)), Disjoint f.support g.support -> P f hf -> P g hg -> P (f + g) hfg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …

--- 原说明 ---
To prove that a property holds for any strongly measurable function, it is enoug
h to show
that it holds for constant indicator functions of measurable sets and that it is
 closed under
addition and pointwise limit.

To use in an induction proof, the syntax is
`induction f, hf using StronglyMeasurable.induction with`.
-/
theorem induction [MeasurableSpace α] [AddZeroClass β] [TopologicalSpace β]
    {P : (f : α → β) → StronglyMeasurable f → Prop}
    (ind : ∀ c ⦃s : Set α⦄ (hs : MeasurableSet s),
      P (s.indicator fun _ ↦ c) (stronglyMeasurable_const.indicator hs))
    (add : ∀ ⦃f g : α → β⦄ (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hfg : StronglyMeasurable (f + g)), Disjoint f.support g.support →
      P f hf → P g hg → P (f + g) hfg)
    (lim : ∀ ⦃f : ℕ → α → β⦄ ⦃g : α → β⦄ (hf : ∀ n, StronglyMeasurable (f n))
      (hg : StronglyMeasurable g), (∀ n, P (f n) (hf n)) →
      (∀ x, Tendsto (f · x) atTop (𝓝 (g x))) → P g hg)
    (f : α → β) (hf : StronglyMeasurable f) : P f hf := by
  let s := hf.approx
  refine lim (fun n ↦ (s n).stronglyMeasurable) hf (fun n ↦ ?_) hf.tendsto_approx
  induction s n using SimpleFunc.induction with
  | const c hs => exact ind c hs
  | @add f g h_supp hf hg =>
    exact add f.stronglyMeasurable g.stronglyMeasurable (f + g).stronglyMeasurable h_supp hf hg

open scoped Classical in
/-- To prove that a property holds for any strongly measurable function, it is enough to show
that it holds for constant functions and that it is closed under piecewise combination of functions
and pointwise limits.

To use in an induction proof, the syntax is
`induction f, hf using StronglyMeasurable.induction' with`. -/
/-
**MeasureTheory.StronglyMeasurable.induction'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.StronglyMeasurable`。
形式化陈述：induction' [MeasurableSpace α] [Nonempty β] [TopologicalSpace β] {P : (f :
 α -> β) -> StronglyMeasurable f -> Prop} (const : forall (c), P (fun _ => c) st
ronglyMeasurable_const) (pcw : forall ⦃f g : α -> β⦄ {s} (hf : StronglyMeasurabl
e f) (hg : StronglyMeasurable g) (hs : MeasurableSet s), P f hf -> P g hg -> P (
s.piecewise f g) (hf.piecewise hs hg)) (lim : forall ⦃f : Nat -> α -> β⦄ ⦃g : α 
-> β⦄ (hf : forall n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g), (fo
rall n, P (f n) (hf n)) ->
参数：f : α -> β；const : forall (c), P (fun _ => c) stronglyMeasurable_const；pcw : 
forall ⦃f g : α -> β⦄ {s} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g
) (hs : MeasurableSet s), P f hf -> P g hg -> P (s.piecewise f g) (hf.piecewise 
hs hg)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.StronglyMeasurable.piecewise`：∀ {α : Type u_1} {β : Type u
_2} {f g : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β] {s : Set α
}   {x : DecidablePred fun x => …
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.SimpleFunc.induction'`：∀ {α : Type u_5} {γ : Type u_6} [in
st : MeasurableSpace α] [Nonempty γ] {P : MeasureTheory.SimpleFunc α γ → Prop}, 
  (∀ (c : γ), P (MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …

--- 原说明 ---
To prove that a property holds for any strongly measurable function, it is enoug
h to show
that it holds for constant functions and that it is closed under piecewise combi
nation of functions
and pointwise limits.

To use in an induction proof, the syntax is
`induction f, hf using StronglyMeasurable.induction' with`.
-/
theorem induction' [MeasurableSpace α] [Nonempty β] [TopologicalSpace β]
    {P : (f : α → β) → StronglyMeasurable f → Prop}
    (const : ∀ (c), P (fun _ ↦ c) stronglyMeasurable_const)
    (pcw : ∀ ⦃f g : α → β⦄ {s} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hs : MeasurableSet s), P f hf → P g hg → P (s.piecewise f g) (hf.piecewise hs hg))
    (lim : ∀ ⦃f : ℕ → α → β⦄ ⦃g : α → β⦄ (hf : ∀ n, StronglyMeasurable (f n))
      (hg : StronglyMeasurable g), (∀ n, P (f n) (hf n)) →
      (∀ x, Tendsto (f · x) atTop (𝓝 (g x))) → P g hg)
    (f : α → β) (hf : StronglyMeasurable f) : P f hf := by
  let s := hf.approx
  refine lim (fun n ↦ (s n).stronglyMeasurable) hf (fun n ↦ ?_) hf.tendsto_approx
  induction s n with
  | const c => exact const c
  | @pcw f g s hs Pf Pg =>
    simp_rw [SimpleFunc.coe_piecewise]
    exact pcw f.stronglyMeasurable g.stronglyMeasurable hs Pf Pg

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.dist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {β : Type u_5} [inst : PseudoMetr
icSpace β] {f g : α → β},   MeasureTheory.StronglyMeasurable f →     MeasureTheo
ry.StronglyMeasurable g → MeasureTheory.StronglyMeasurable fun x => dist (f x) (
g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
-/
protected theorem dist {_ : MeasurableSpace α} {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.edist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {β : Type u_5} [inst : PseudoEMet
ricSpace β] {f g : α → β},   MeasureTheory.StronglyMeasurable f →     MeasureThe
ory.StronglyMeasurable g → MeasureTheory.StronglyMeasurable fun x => edist (f x)
 (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
-/
protected theorem edist {_ : MeasurableSpace α} {β : Type*} [PseudoEMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => edist (f x) (g x) :=
  continuous_edist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {β : Type u_5} [inst : Seminormed
AddCommGroup β] {f : α → β},   MeasureTheory.StronglyMeasurable f → MeasureTheor
y.StronglyMeasurable fun x => ‖f x‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
-/
protected theorem norm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖ :=
  continuous_norm.comp_stronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {β : Type u_5} [inst : Seminormed
AddCommGroup β] {f : α → β},   MeasureTheory.StronglyMeasurable f → MeasureTheor
y.StronglyMeasurable fun x => ‖f x‖₊
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_nnnorm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Conti
nuous fun a => ‖a‖₊
-/
protected theorem nnnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖₊ :=
  continuous_nnnorm.comp_stronglyMeasurable hf

/-- The `enorm` of a strongly measurable function is measurable.

Unlike `StrongMeasurable.norm` and `StronglyMeasurable.nnnorm`, this lemma proves measurability,
**not** strong measurability. This is an intentional decision: for functions taking values in
ℝ≥0∞, measurability is much more useful than strong measurability. -/
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {ε : Type u_5} [inst : Topologica
lSpace ε] [inst_1 : ContinuousENorm ε]   {f : α → ε}, MeasureTheory.StronglyMeas
urable f → Measurable fun x => ‖f x‖ₑ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ

--- 原说明 ---
The `enorm` of a strongly measurable function is measurable.

Unlike `StrongMeasurable.norm` and `StronglyMeasurable.nnnorm`, this lemma prove
s measurability,
**not** strong measurability. This is an intentional decision: for functions tak
ing values in
ℝ≥0∞, measurability is much more useful than strong measurability.
-/
protected theorem enorm {_ : MeasurableSpace α} {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α → ε} (hf : StronglyMeasurable f) : Measurable (‖f ·‖ₑ) :=
  (continuous_enorm.comp_stronglyMeasurable hf).measurable

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {f : α → ℝ},   MeasureTheory.Stro
nglyMeasurable f → MeasureTheory.StronglyMeasurable fun x => (f x).toNNReal
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
-/
protected theorem real_toNNReal {_ : MeasurableSpace α} {f : α → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNNReal :=
  continuous_real_toNNReal.comp_stronglyMeasurable hf

section PseudoMetrizableSpace
variable {E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α → E}
  [TopologicalSpace E] [Preorder E] [OrderClosedTopology E] [PseudoMetrizableSpace E]

/-
**MeasureTheory.StronglyMeasurable.measurableSet_le** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.StronglyMeasurable`。
形式化陈述：measurableSet_le (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m
] g) : MeasurableSet[m] {a | f a <= g a}
参数：hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_le_prod`：isClosed_le_prod : IsClosed { p : α × α | p.1 <= p.2 }
-/
lemma measurableSet_le (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a ≤ g a} := by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_le_prod.measurableSet
/-
**MeasureTheory.StronglyMeasurable.measurableSet_lt** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.StronglyMeasurable`。
形式化陈述：measurableSet_lt (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m
] g) : MeasurableSet[m] {a | f a < g a}
参数：hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
lemma measurableSet_lt (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a < g a} := by
  simpa only [lt_iff_le_not_ge] using! (hf.measurableSet_le hg).inter (hg.measurableSet_le hf).compl
/-
**MeasureTheory.StronglyMeasurable.ae_le_trim_of_stronglyMeasurable** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：ae_le_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m
] f) (hg : StronglyMeasurable[m] g) (hfg : f <=ᵐ[μ] g) : f <=ᵐ[μ.trim hm] g
参数：hm : m <= m₀；hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g；hfg : 
f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
-/
lemma ae_le_trim_of_stronglyMeasurable (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (hfg : f ≤ᵐ[μ] g) : f ≤ᵐ[μ.trim hm] g := by
  rwa [EventuallyLE, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_le hg).compl
/-
**MeasureTheory.StronglyMeasurable.ae_le_trim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.StronglyMeasurable`。
形式化陈述：ae_le_trim_iff (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : Strongl
yMeasurable[m] g) : f <=ᵐ[μ.trim hm] g ↔ f <=ᵐ[μ] g
参数：hm : m <= m₀；hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_le_of_ae_le_trim`：ae_le_of_ae_le_trim {E} [LE E] {hm : 
m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_le_trim_of_stronglyMeasurable`：ae_le
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f <=ᵐ[μ] g) : f <=ᵐ[μ.t…
-/
lemma ae_le_trim_iff (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f ≤ᵐ[μ.trim hm] g ↔ f ≤ᵐ[μ] g :=
  ⟨ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable hm hf hg⟩

end PseudoMetrizableSpace

section MetrizableSpace
variable {E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α → E}
  [TopologicalSpace E] [MetrizableSpace E]

/-
**MeasureTheory.StronglyMeasurable.measurableSet_eq_fun** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：measurableSet_eq_fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurab
le[m] g) : MeasurableSet[m] {a | f a = g a}
参数：hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
-/
lemma measurableSet_eq_fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a = g a} := by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_diagonal.measurableSet
/-
**MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：ae_eq_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m
] f) (hg : StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.trim hm] g
参数：hm : m <= m₀；hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g；hfg : 
f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_eq_fun`：measurableSet_eq_
fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSe
t[m] {a | f a = g a}
-/
lemma ae_eq_trim_of_stronglyMeasurable (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.trim hm] g := by
  rwa [EventuallyEq, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_eq_fun hg).compl
/-
**MeasureTheory.StronglyMeasurable.ae_eq_trim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.StronglyMeasurable`。
形式化陈述：ae_eq_trim_iff (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : Strongl
yMeasurable[m] g) : f =ᵐ[μ.trim hm] g ↔ f =ᵐ[μ] g
参数：hm : m <= m₀；hf : StronglyMeasurable[m] f；hg : StronglyMeasurable[m] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
-/
lemma ae_eq_trim_iff (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f =ᵐ[μ.trim hm] g ↔ f =ᵐ[μ] g :=
  ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable hm hf hg⟩

end MetrizableSpace

/-
**MeasureTheory.StronglyMeasurable.stronglyMeasurable_in_set** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：stronglyMeasurable_in_set {m : MeasurableSpace α} [TopologicalSpace β] [Ze
ro β] {s : Set α} {f : α -> β} (hs : MeasurableSet s) (hf : StronglyMeasurable f
) (hf_zero : forall x, x ∉ s -> f x = 0) : exists fs : Nat -> α ->ₛ β, (forall x
, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧ forall x ∉ s, forall n, fs n x = 
0
参数：hs : MeasurableSet s；hf : StronglyMeasurable f；hf_zero : forall x, x ∉ s -> f
 x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stronglyMeasurable_in_set {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α}
    {f : α → β} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hf_zero : ∀ x, x ∉ s → f x = 0) :
    ∃ fs : ℕ → α →ₛ β,
      (∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧ ∀ x ∉ s, ∀ n, fs n x = 0 := by
  refine ⟨fun n => (hf.approx n).restrict s, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ s
    · simpa [SimpleFunc.coe_restrict, hs, hx] using hf.tendsto_approx x
    · simpa [SimpleFunc.coe_restrict, hs, hx, hf_zero x hx] using tendsto_const_nhds
  · intro x hx n
    simp [SimpleFunc.coe_restrict, hs, hx]

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` supported
on `s` is `m`-strongly-measurable, then `f` is also `m₂`-strongly-measurable. -/
/-
**MeasureTheory.StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：stronglyMeasurable_of_measurableSpace_le_on {α E} {m m₂ : MeasurableSpace 
α} [TopologicalSpace E] [Zero E] {s : Set α} {f : α -> E} (hs_m : MeasurableSet[
m] s) (hs : forall t, MeasurableSet[m] (s inter t) -> MeasurableSet[m₂] (s inter
 t)) (hf : StronglyMeasurable[m] f) (hf_zero : forall x ∉ s, f x = 0) : Strongly
Measurable[m₂] f
参数：hs_m : MeasurableSet[m] s；hs : forall t, MeasurableSet[m] (s inter t) -> Meas
urableSet[m₂] (s inter t)；hf : StronglyMeasurable[m] f；hf_zero : forall x ∉ s, f
 x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `stronglyMeasurable_of_restrict_of_restrict_compl`：∀ {α : Type u_1} {β : 
Type u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] {f : α → β} {s : S
et α},   MeasurableSet s →     Measure…
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
· 使用定理 `MeasureTheory.stronglyMeasurable_const'`：stronglyMeasurable_const' (hf :
 forall x y, f x = f y) : StronglyMeasurable f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If the restriction to a set `s` of a σ-algebra `m` is included in the restrictio
n to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a fu
nction `f` supported
on `s` is `m`-strongly-measurable, then `f` is also `m₂`-strongly-measurable.
-/
theorem stronglyMeasurable_of_measurableSpace_le_on {α E} {m m₂ : MeasurableSpace α}
    [TopologicalSpace E] [Zero E] {s : Set α} {f : α → E} (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) → MeasurableSet[m₂] (s ∩ t))
    (hf : StronglyMeasurable[m] f) (hf_zero : ∀ x ∉ s, f x = 0) :
    StronglyMeasurable[m₂] f := by
  have hs_m₂ : MeasurableSet[m₂] s := by
    have : MeasurableSet (s ∩ univ) := hs univ (by simpa)
    simpa
  have h_sub : m.comap ((↑) : s → α) ≤ m₂.comap ((↑) : s → α) := by
    intro _ ht
    rcases ht with ⟨u, hu, rfl⟩
    exact ⟨s ∩ u, hs u (hs_m.inter hu), by simp⟩
  refine stronglyMeasurable_of_restrict_of_restrict_compl hs_m₂ ?_ ?_
  · exact (hf.comp_measurable (comap_measurable _)).mono h_sub
  · exact stronglyMeasurable_const' fun x y ↦ by simp [hf_zero _ x.2, hf_zero _ y.2]

/-- If a function `f` is strongly measurable w.r.t. a sub-σ-algebra `m` and the measure is σ-finite
on `m`, then there exists spanning measurable sets with finite measure on which `f` has bounded
norm. In particular, `f` is integrable on each of those sets. -/
/-
**MeasureTheory.StronglyMeasurable.exists_spanning_measurableSet_norm_le** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : M
easurableSpace α} (hm : m <= m0) (hf : StronglyMeasurable[m] f) (μ : Measure α) 
[SigmaFinite (μ.trim hm)] : exists s : Nat -> Set α, (forall n, MeasurableSet[m]
 (s n) ∧ μ (s n) < ∞ ∧ forall x in s n, ‖f x‖ <= n) ∧ ⋃ i, s i = Set.univ
参数：hm : m <= m0；hf : StronglyMeasurable[m] f；μ : Measure α；μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_spanning_measurableSet_le`：exists_spanning_measurableSet_le {f : 
α -> Real>=0} (hf : Measurable f) (μ : Measure α) [SigmaFinite μ] : exists s : N
at -> Set α, (forall n…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.nnnorm`：∀ {α : Type u_1} {x : Measurabl
eSpace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   Measur
eTheory.StronglyMeasurable f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n

--- 原说明 ---
If a function `f` is strongly measurable w.r.t. a sub-σ-algebra `m` and the meas
ure is σ-finite
on `m`, then there exists spanning measurable sets with finite measure on which 
`f` has bounded
norm. In particular, `f` is integrable on each of those sets.
-/
theorem exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) (hf : StronglyMeasurable[m] f) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    ∃ s : ℕ → Set α,
      (∀ n, MeasurableSet[m] (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, ‖f x‖ ≤ n) ∧
      ⋃ i, s i = Set.univ := by
  obtain ⟨s, hs, hs_univ⟩ :=
    @exists_spanning_measurableSet_le _ m _ hf.nnnorm.measurable (μ.trim hm) _
  refine ⟨s, fun n ↦ ⟨(hs n).1, (le_trim hm).trans_lt (hs n).2.1, fun x hx ↦ ?_⟩, hs_univ⟩
  have hx_nnnorm : ‖f x‖₊ ≤ n := (hs n).2.2 x hx
  rw [← coe_nnnorm]
  norm_cast

end StronglyMeasurable

/-! ## Finitely strongly measurable functions -/


/-
**MeasureTheory.finStronglyMeasurable_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：finStronglyMeasurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [
Zero β] [TopologicalSpace β] : FinStronglyMeasurable (0 : α -> β) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], 
Function.support 0 = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
## Finitely strongly measurable functions
-/
theorem finStronglyMeasurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
    [TopologicalSpace β] : FinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, by
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero, measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

section sequence

variable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)

/-- A sequence of simple functions such that `∀ x, Tendsto (fun n ↦ hf.approx n x) atTop (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`FinStronglyMeasurable.tendsto_approx` and `FinStronglyMeasurable.fin_support_approx`. -/
/-
**MeasureTheory.FinStronglyMeasurable.approx** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.FinStronglyMeasurable`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {m0 : MeasurableSpace α} →       {
μ : MeasureTheory.Measure α} →         {f : α → β} →           [inst : Zero β] →
             [inst_1 : TopologicalSpace β] → MeasureTheory.FinStronglyMeasurable
 f μ → ℕ → MeasureTheory.SimpleFunc α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of simple functions such that `∀ x, Tendsto (fun n ↦ hf.approx n x) a
tTop (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`FinStronglyMeasurable.tendsto_approx` and `FinStronglyMeasurable.fin_support_ap
prox`.
-/
protected noncomputable def approx : ℕ → α →ₛ β :=
  hf.choose
/-
**MeasureTheory.FinStronglyMeasurable.fin_support_approx** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : α → β} [inst : Zero β]   [inst_1 : TopologicalSpace β] (hf : M
easureTheory.FinStronglyMeasurable f μ) (n : ℕ),   μ (Function.support ⇑(hf.appr
ox n)) < ⊤
参数：hf : MeasureTheory.FinStronglyMeasurable f μ；n : ℕ；Function.support ⇑(hf.appr
ox n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ :=
  hf.choose_spec.1
/-
**MeasureTheory.FinStronglyMeasurable.tendsto_approx** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : α → β} [inst : Zero β]   [inst_1 : TopologicalSpace β] (hf : M
easureTheory.FinStronglyMeasurable f μ) (x : α),   Filter.Tendsto (fun n => (hf.
approx n) x) Filter.atTop (nhds (f x))
参数：hf : MeasureTheory.FinStronglyMeasurable f μ；x : α；fun n => (hf.approx n) x；n
hds (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem tendsto_approx : ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec.2

end sequence

/-- A finitely strongly measurable function is strongly measurable. -/
@[fun_prop]
/-
**MeasureTheory.FinStronglyMeasurable.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : α → β} [inst : Zero β]   [inst_1 : TopologicalSpace β], Measur
eTheory.FinStronglyMeasurable f μ → MeasureTheory.StronglyMeasurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…

--- 原说明 ---
A finitely strongly measurable function is strongly measurable.
-/
protected theorem stronglyMeasurable [Zero β] [TopologicalSpace β]
    (hf : FinStronglyMeasurable f μ) : StronglyMeasurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩
/-
**MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.FinStronglyMeasurable`。
形式化陈述：exists_set_sigmaFinite [Zero β] [TopologicalSpace β] [T2Space β] (hf : Fin
StronglyMeasurable f μ) : exists t, MeasurableSet t ∧ (forall x in tᶜ, f x = 0) 
∧ SigmaFinite (μ.restrict t)
参数：hf : FinStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_support`：measurableSet_support [M
easurableSpace α] (f : α ->ₛ β) : MeasurableSet (support f)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `trivial`：True
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_iUnion`：union_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s union ⋃ i, t i) = ⋃ i, s union t i
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
-/
theorem exists_set_sigmaFinite [Zero β] [TopologicalSpace β] [T2Space β]
    (hf : FinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : ∀ n, MeasurableSet (T n) := fun n => SimpleFunc.measurableSet_support (fs n)
  let t := ⋃ n, T n
  refine ⟨t, MeasurableSet.iUnion hT_meas, ?_, ?_⟩
  · have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0 := by
      intro n x hxt
      rw [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hxt
      simpa [T] using hxt n
    refine fun x hxt => tendsto_nhds_unique (h_approx x) ?_
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
  · refine ⟨⟨⟨fun n => tᶜ ∪ T n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply' (MeasurableSet.iUnion hT_meas), Set.union_inter_distrib_right,
        Set.compl_inter_self t, Set.empty_union]
      exact (measure_mono Set.inter_subset_left).trans_lt (hT_lt_top n)
    · rw [← Set.union_iUnion tᶜ T]
      exact Set.compl_union_self _

/-- A finitely strongly measurable function is measurable. -/
/-
**MeasureTheory.FinStronglyMeasurable.measurable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : α → β} [inst : Zero β]   [inst_1 : TopologicalSpace β] [Topolo
gicalSpace.PseudoMetrizableSpace β] [inst_3 : MeasurableSpace β] [BorelSpace β],
   MeasureTheory.FinStronglyMeasurable f μ → Measurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.stronglyMeasurable`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…

--- 原说明 ---
A finitely strongly measurable function is measurable.
-/
protected theorem measurable [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : FinStronglyMeasurable f μ) : Measurable f :=
  hf.stronglyMeasurable.measurable

section Arithmetic

variable [TopologicalSpace β]

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.FinStronglyMeasurable.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f g : α → β}   [inst : TopologicalSpace β] [inst_1 : MulZeroClass 
β] [ContinuousMul β],   MeasureTheory.FinStronglyMeasurable f μ →     MeasureThe
ory.FinStronglyMeasurable g μ → MeasureTheory.FinStronglyMeasurable (f * g) μ
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Function.support_mul_subset_left`：support_mul_subset_left (f g : ι -> M₀
) : support (fun x => f x * g x) subseteq support f
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ := by
  refine
    ⟨fun n => hf.approx n * hg.approx n, ?_, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.FinStronglyMeasurable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f g : α → β}   [inst : TopologicalSpace β] [inst_1 : AddZeroClass 
β] [ContinuousAdd β],   MeasureTheory.FinStronglyMeasurable f μ →     MeasureThe
ory.FinStronglyMeasurable g μ → MeasureTheory.FinStronglyMeasurable (f + g) μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_add`：∀ {α : Type u_1} {M : Type u_2} [inst : AddZeroCla
ss M] (f g : α → M),   (Function.support fun x => f x + g x) ⊆ Function.support 
f ∪ Functi…
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

@[measurability]
/-
**MeasureTheory.FinStronglyMeasurable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : α → β}   [inst : TopologicalSpace β] [inst_1 : SubtractionMono
id β] [ContinuousNeg β],   MeasureTheory.FinStronglyMeasurable f μ → MeasureTheo
ry.FinStronglyMeasurable (-f) μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_fun_neg`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtra
ctionMonoid G] (f : α → G),   (Function.support fun x => -f x) = Function.suppor
t f
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem neg [SubtractionMonoid β] [ContinuousNeg β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ := by
  refine ⟨fun n ↦ -hf.approx n, fun n ↦ ?_, fun x ↦ (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x ↦ -(hf.approx n) x) < ∞ by convert! this
  rw [Function.support_fun_neg (hf.approx n)]
  exact hf.fin_support_approx n

@[measurability]
/-
**MeasureTheory.FinStronglyMeasurable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f g : α → β}   [inst : TopologicalSpace β] [inst_1 : SubtractionMo
noid β] [ContinuousSub β],   MeasureTheory.FinStronglyMeasurable f μ →     Measu
reTheory.FinStronglyMeasurable g μ → MeasureTheory.FinStronglyMeasurable (f - g)
 μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_sub`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f g : α → G),   (Function.support fun x => f x - g x) ⊆ Function.sup
port f ∪ F…
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

@[measurability]
/-
**MeasureTheory.FinStronglyMeasurable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : α → β}   [inst : TopologicalSpace β] {𝕜 : Type u_5} [inst_1 : 
TopologicalSpace 𝕜] [inst_2 : Zero β]   [inst_3 : SMulZeroClass 𝕜 β] [Continuous
SMul 𝕜 β],   MeasureTheory.FinStronglyMeasurable f μ → ∀ (c : 𝕜), MeasureTheory.
FinStronglyMeasurable (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_smul`：coe_smul [SMul K β] (c : K) (f : α ->
ₛ β) : ⇑(c • f) = c • ⇑f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Function.support_const_smul_subset`：support_const_smul_subset [Zero M] [
SMulZeroClass R M] (a : R) (f : α -> M) : support (a • f) subseteq support f
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousSMul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) :
    FinStronglyMeasurable (c • f) μ := by
  refine ⟨fun n => c • hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [SimpleFunc.coe_smul]
  exact (measure_mono (support_const_smul_subset c _)).trans_lt (hf.fin_support_approx n)

end Arithmetic

section Order

variable [TopologicalSpace β] [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.FinStronglyMeasurable.sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f g : α → β}   [inst : TopologicalSpace β] [inst_1 : Zero β] [inst
_2 : SemilatticeSup β] [ContinuousSup β],   MeasureTheory.FinStronglyMeasurable 
f μ →     MeasureTheory.FinStronglyMeasurable g μ → MeasureTheory.FinStronglyMea
surable (f ⊔ g) μ
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_sup`：∀ {α : Type u_2} {M : Type u_3} [inst : Zero M] [i
nst_1 : SemilatticeSup M] (f g : α → M),   (Function.support fun x => f x ⊔ g x)
 ⊆ Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_union_lt_top_iff`：measure_union_lt_top_iff : μ (s 
union t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用引理 `Filter.Tendsto.sup_nhds`：sup_nhds [Max L] [ContinuousSup L] (hf : Tendst
o f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y
))
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊔ g) μ := by
  refine
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_sup _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.FinStronglyMeasurable.inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.FinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f g : α → β}   [inst : TopologicalSpace β] [inst_1 : Zero β] [inst
_2 : SemilatticeInf β] [ContinuousInf β],   MeasureTheory.FinStronglyMeasurable 
f μ →     MeasureTheory.FinStronglyMeasurable g μ → MeasureTheory.FinStronglyMea
surable (f ⊓ g) μ
参数：f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_inf`：∀ {α : Type u_2} {M : Type u_3} [inst : Zero M] [i
nst_1 : SemilatticeInf M] (f g : α → M),   (Function.support fun x => f x ⊓ g x)
 ⊆ Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_union_lt_top_iff`：measure_union_lt_top_iff : μ (s 
union t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞
· 使用定理 `MeasureTheory.FinStronglyMeasurable.fin_support_approx`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用引理 `Filter.Tendsto.inf_nhds`：inf_nhds [Min L] [ContinuousInf L] (hf : Tendst
o f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y
))
· 使用定理 `MeasureTheory.FinStronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [
inst : Zero β]   [inst_1 : TopologicalSp…
-/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊓ g) μ := by
  refine
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_inf _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

end Order

end FinStronglyMeasurable

/-
**MeasureTheory.finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigm
aFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite {α
 β} {f : α -> β} [TopologicalSpace β] [T2Space β] [Zero β] {_ : MeasurableSpace 
α} {μ : Measure α} : FinStronglyMeasurable f μ ↔ StronglyMeasurable f ∧ exists t
, MeasurableSet t ∧ (forall x in tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinStronglyMeasurable.stronglyMeasurable`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite`：exists_set_s
igmaFinite [Zero β] [TopologicalSpace β] [T2Space β] (hf : FinStronglyMeasurable
 f μ) : exists t, MeasurableSet t ∧ (forall x in…
· 使用定理 `MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinit
e`：finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β] {m : M
easurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite {α β} {f : α → β}
    [TopologicalSpace β] [T2Space β] [Zero β] {_ : MeasurableSpace α} {μ : Measure α} :
    FinStronglyMeasurable f μ ↔
      StronglyMeasurable f ∧
        ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) :=
  ⟨fun hf => ⟨hf.stronglyMeasurable, hf.exists_set_sigmaFinite⟩, fun hf =>
    hf.1.finStronglyMeasurable_of_set_sigmaFinite hf.2.choose_spec.1 hf.2.choose_spec.2.1
      hf.2.choose_spec.2.2⟩

section SecondCountableTopology

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `FinStronglyMeasurable`
  and `Measurable` are equivalent. -/
/-
**MeasureTheory.finStronglyMeasurable_iff_measurable** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：finStronglyMeasurable_iff_measurable {_m0 : MeasurableSpace α} (μ : Measur
e α) [SigmaFinite μ] : FinStronglyMeasurable f μ ↔ Measurable f
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FinStronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [inst
 : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.finStronglyMeasurable`：∀ {α : Type u_1}
 {β : Type u_2} {f : α → β} [inst : TopologicalSpace β] [inst_1 : Zero β] {m0 : 
MeasurableSpace α},   MeasureTheory.Strongly…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α

--- 原说明 ---
In a space with second countable topology and a sigma-finite measure, `FinStrong
lyMeasurable`
  and `Measurable` are equivalent.
-/
theorem finStronglyMeasurable_iff_measurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : FinStronglyMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => (Measurable.stronglyMeasurable h).finStronglyMeasurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure, a measurable function
is `FinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
/-
**MeasureTheory.finStronglyMeasurable_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：finStronglyMeasurable_of_measurable {_m0 : MeasurableSpace α} (μ : Measure
 α) [SigmaFinite μ] (hf : Measurable f) : FinStronglyMeasurable f μ
参数：μ : Measure α；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.finStronglyMeasurable_iff_measurable`：finStronglyMeasurabl
e_iff_measurable {_m0 : MeasurableSpace α} (μ : Measure α) [SigmaFinite μ] : Fin
StronglyMeasurable f μ ↔ Measurable f

--- 原说明 ---
In a space with second countable topology and a sigma-finite measure, a measurab
le function
is `FinStronglyMeasurable`.
-/
theorem finStronglyMeasurable_of_measurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : Measurable f) : FinStronglyMeasurable f μ :=
  (finStronglyMeasurable_iff_measurable μ).mpr hf

end SecondCountableTopology

/-
**MeasureTheory.measurable_uncurry_of_continuous_of_measurable** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_uncurry_of_continuous_of_measurable {α β ι : Type*} [Topologica
lSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι] [O
pensMeasurableSpace ι] {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetr
izableSpace β] [BorelSpace β] {m : MeasurableSpace α} {u : ι -> α -> β} (hu_cont
 : forall x, Continuous fun i => u i x) (h : forall i, Measurable (u i)) : Measu
rable (Function.uncurry u)
参数：hu_cont : forall x, Continuous fun i => u i x；h : forall i, Measurable (u i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `stronglyMeasurable_id`：∀ {α : Type u_1} {mα : MeasurableSpace α} [inst :
 TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]   [OpensMeasurab
leSpace α] …
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `measurable_of_tendsto_metrizable`：measurable_of_tendsto_metrizable {f : 
Nat -> α -> β} {g : α -> β} (hf : forall i, Measurable (f i)) (lim : Tendsto f a
tTop (𝓝 g)) : Measurab…
· 使用定理 `measurable_swap_iff`：measurable_swap_iff {_ : MeasurableSpace γ} {f : α 
× β -> γ} : Measurable (f ∘ Prod.swap) ↔ Measurable f
· 使用定理 `measurable_from_prod_countable_left`：measurable_from_prod_countable_left
 [Countable β] [MeasurableSingletonClass β] {f : α × β -> γ} (hf : forall y, Mea
surable fun x => f (x, y)…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `MeasureTheory.SimpleFunc.mem_range_self`：mem_range_self (f : α ->ₛ β) (x
 : α) : f x in f.range
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem measurable_uncurry_of_continuous_of_measurable {α β ι : Type*} [TopologicalSpace ι]
    [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι] [OpensMeasurableSpace ι]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
    {m : MeasurableSpace α} {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x)
    (h : ∀ i, Measurable (u i)) : Measurable (Function.uncurry u) := by
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → SimpleFunc ι ι, ∀ j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι → ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine measurable_of_tendsto_metrizable (fun n => ?_) h_tendsto
  have h_meas : Measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    have :
      (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
        (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
      rfl
    rw [this, @measurable_swap_iff α (↥(t_sf n).range) β m]
    exact measurable_from_prod_countable_left fun j => h j
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine h_meas.comp (Measurable.prodMk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk
/-
**MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Ty
pe*} [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountab
leTopology ι] [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpa
ce β] [MeasurableSpace α] {u : ι -> α -> β} (hu_cont : forall x, Continuous fun 
i => u i x) (h : forall i, StronglyMeasurable (u i)) : StronglyMeasurable (Funct
ion.uncurry u)
参数：hu_cont : forall x, Continuous fun i => u i x；h : forall i, StronglyMeasurabl
e (u i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `stronglyMeasurable_id`：∀ {α : Type u_1} {mα : MeasurableSpace α} [inst :
 TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]   [OpensMeasurab
leSpace α] …
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approx`：∀ {α : Type u_1} {β : T
ype u_2} {f : α → β} [inst : TopologicalSpace β] {x : MeasurableSpace α}   (hf :
 MeasureTheory.StronglyMeasurable f) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable_separable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `measurable_swap_iff`：measurable_swap_iff {_ : MeasurableSpace γ} {f : α 
× β -> γ} : Measurable (f ∘ Prod.swap) ↔ Measurable f
· 使用定理 `measurable_from_prod_countable_left`：measurable_from_prod_countable_left
 [Countable β] [MeasurableSingletonClass β] {f : α × β -> γ} (hf : forall y, Mea
surable fun x => f (x, y)…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.IsSeparable.iUnion`：∀ {α : Type u} [t : TopologicalSpac
e α] {ι : Sort u_2} [Countable ι] {s : ι → Set α},   (∀ (i : ι), TopologicalSpac
e.IsSeparable (s i)) → To…
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
（共 41 条，此处仅展示前 30 条）
-/
theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Type*}
    [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace α]
    {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x) (h : ∀ i, StronglyMeasurable (u i)) :
    StronglyMeasurable (Function.uncurry u) := by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → SimpleFunc ι ι, ∀ j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι → ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine stronglyMeasurable_of_tendsto _ (fun n => ?_) h_tendsto
  have h_str_meas : StronglyMeasurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
    · have :
        (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
          (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
        rfl
      rw [this, measurable_swap_iff]
      exact measurable_from_prod_countable_left fun j => (h j).measurable
    · have : IsSeparable (⋃ i : (t_sf n).range, range (u i)) :=
        .iUnion fun i => (h i).isSeparable_range
      apply this.mono
      rintro _ ⟨⟨i, x⟩, rfl⟩
      simp only [mem_iUnion, mem_range]
      exact ⟨i, x, rfl⟩
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine h_str_meas.comp_measurable (Measurable.prodMk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk

end MeasureTheory

