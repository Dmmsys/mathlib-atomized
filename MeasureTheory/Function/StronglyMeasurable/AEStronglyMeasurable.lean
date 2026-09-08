/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be almost everywhere strongly measurable if `f` is almost everywhere
equal to a strongly measurable function, i.e. the sequential limit of simple functions.
It is said to be almost everywhere finitely strongly measurable with respect to a measure `μ`
if the supports of those simple functions have finite measure.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

## Main definitions
* `AEStronglyMeasurable f μ`: `f` is almost everywhere equal to a `StronglyMeasurable` function.
* `AEFinStronglyMeasurable f μ`: `f` is almost everywhere equal to a `FinStronglyMeasurable`
  function.

* `AEFinStronglyMeasurable.sigmaFiniteSet`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `AEFinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `AEStronglyMeasurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions.

One can specify the sigma-algebra according to which simple functions are taken using the
`AEStronglyMeasurable[m]` notation in the `MeasureTheory` scope. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：AEStronglyMeasurable [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f :
 α -> β) (μ : Measure[m₀] α
参数：f : α -> β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A function is `AEStronglyMeasurable` with respect to a measure `μ` if it is almo
st everywhere
equal to the limit of a sequence of simple functions.

One can specify the sigma-algebra according to which simple functions are taken 
using the
`AEStronglyMeasurable[m]` notation in the `MeasureTheory` scope.
-/
def AEStronglyMeasurable [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f : α → β)
    (μ : Measure[m₀] α := by volume_tac) : Prop :=
  ∃ g : α → β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEStronglyMeasurable ..])
  (by fun_prop (disch := measurability))

/-- A function is `m`-`AEStronglyMeasurable` with respect to a measure `μ` if it is almost
everywhere equal to the limit of a sequence of `m`-simple functions. -/
scoped notation "AEStronglyMeasurable[" m "]" => @MeasureTheory.AEStronglyMeasurable _ _ _ m

/-- A function is `AEFinStronglyMeasurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
/-
**MeasureTheory.AEFinStronglyMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
`。
形式化陈述：AEFinStronglyMeasurable [Zero β] {_ : MeasurableSpace α} (f : α -> β) (μ :
 Measure α
参数：f : α -> β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A function is `AEFinStronglyMeasurable` with respect to a measure if it is almos
t everywhere
equal to the limit of a sequence of simple functions with support with finite me
asure.
-/
def AEFinStronglyMeasurable
    [Zero β] {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

end Definitions

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

/-
**MeasureTheory.FinStronglyMeasurable.aefinStronglyMeasurable** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.FinStronglyMeasurable`。
形式化陈述：aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMea
surable f μ) : AEFinStronglyMeasurable f μ
参数：hf : FinStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩

end FinStronglyMeasurable

/-
**MeasureTheory.aefinStronglyMeasurable_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：aefinStronglyMeasurable_zero {α β} {_ : MeasurableSpace α} (μ : Measure α)
 [Zero β] [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α -> β) μ
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.finStronglyMeasurable_zero`：finStronglyMeasurable_zero {α 
β} {m : MeasurableSpace α} {μ : Measure α} [Zero β] [TopologicalSpace β] : FinSt
ronglyMeasurable (0 : α -> β) …
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem aefinStronglyMeasurable_zero {α β} {_ : MeasurableSpace α} (μ : Measure α) [Zero β]
    [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩

/-! ## Almost everywhere strongly measurable functions -/

section AEStronglyMeasurable
variable [TopologicalSpace β] [TopologicalSpace γ] {m m₀ : MeasurableSpace α} {μ ν : Measure[m₀] α}
  {f g : α → β}

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β}, MeasureTheory.Strongly
Measurable f → MeasureTheory.AEStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
protected theorem StronglyMeasurable.aestronglyMeasurable (hf : StronglyMeasurable[m] f) :
    AEStronglyMeasurable[m] f μ := ⟨f, hf, EventuallyEq.refl _ _⟩

@[fun_prop]
/-
**MeasureTheory.aestronglyMeasurable_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：aestronglyMeasurable_const {b : β} : AEStronglyMeasurable[m] (fun _ : α =>
 b) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem aestronglyMeasurable_const {b : β} : AEStronglyMeasurable[m] (fun _ : α => b) μ :=
  stronglyMeasurable_const.aestronglyMeasurable

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.aestronglyMeasurable_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：aestronglyMeasurable_one [One β] : AEStronglyMeasurable[m] (1 : α -> β) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_one`：stronglyMeasurable_one [One β] : S
tronglyMeasurable (1 : α -> β)
-/
theorem aestronglyMeasurable_one [One β] : AEStronglyMeasurable[m] (1 : α → β) μ :=
  stronglyMeasurable_one.aestronglyMeasurable

@[simp, nontriviality]
/-
**MeasureTheory.AEStronglyMeasurable.of_subsingleton_dom** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [Subsingleton α], Measu
reTheory.AEStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.of_subsingleton_dom`：∀ {α : Type u_1} {
β : Type u_2} {x : MeasurableSpace α} {f : α → β} [inst : TopologicalSpace β] [S
ubsingleton α],   MeasureTheory.StronglyMe…
-/
lemma AEStronglyMeasurable.of_subsingleton_dom [Subsingleton α] : AEStronglyMeasurable[m] f μ :=
  StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable

@[simp, nontriviality]
/-
**MeasureTheory.AEStronglyMeasurable.of_subsingleton_cod** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [Subsingleton β], Measu
reTheory.AEStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.of_subsingleton_cod`：∀ {α : Type u_1} {
β : Type u_2} {x : MeasurableSpace α} {f : α → β} [inst : TopologicalSpace β] [S
ubsingleton β],   MeasureTheory.StronglyMe…
-/
lemma AEStronglyMeasurable.of_subsingleton_cod [Subsingleton β] : AEStronglyMeasurable[m] f μ :=
  StronglyMeasurable.of_subsingleton_cod.aestronglyMeasurable

@[fun_prop, simp]
/-
**MeasureTheory.aestronglyMeasurable_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：aestronglyMeasurable_zero_measure (f : α -> β) : AEStronglyMeasurable[m] f
 (0 : Measure[m₀] α)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem aestronglyMeasurable_zero_measure (f : α → β) :
    AEStronglyMeasurable[m] f (0 : Measure[m₀] α) := by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩

@[fun_prop]
/-
**MeasureTheory.SimpleFunc.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   (f : MeasureTheory.SimpleFunc α β), M
easureTheory.AEStronglyMeasurable (⇑f) μ
参数：f : MeasureTheory.SimpleFunc α β；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
-/
theorem SimpleFunc.aestronglyMeasurable (f : α →ₛ β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

/-- In a pseudometrizable space, if a measure `μ` is supported on
a separable set then the identity function is `AEStronglyMeasurable` with respect to `μ`. -/
/-
**MeasureTheory.aestronglyMeasurable_id_of_isSeparable** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：aestronglyMeasurable_id_of_isSeparable [TopologicalSpace α] [TopologicalSp
ace.PseudoMetrizableSpace α] [OpensMeasurableSpace α] {s : Set α} (h1 : Topologi
calSpace.IsSeparable s) (h2 : μ sᶜ = 0) : AEStronglyMeasurable id μ
参数：h1 : TopologicalSpace.IsSeparable s；h2 : μ sᶜ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.IsSeparable.secondCountableTopology`：∀ {X : Type u_2} [
inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X
},   TopologicalSpace.IsSeparable s → Seco…
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用定理 `Continuous.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasurableSpace α]   [inst
_3 : TopologicalSpa…
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Function.extend_val_apply`：∀ {β : Sort u_2} {γ : Sort u_3} {p : β → Prop
} {g : { x // p x } → γ} {j : β → γ} {b : β} (hb : p b),   Function.extend Subty
pe.val g j b = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableEmbedding.stronglyMeasurable_extend`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {f : α → β} {g : α → γ} {g' : γ → β} {mα : MeasurableSpace
 α}   {mγ : MeasurableSpace γ} [ins…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
In a pseudometrizable space, if a measure `μ` is supported on
a separable set then the identity function is `AEStronglyMeasurable` with respec
t to `μ`.
-/
lemma aestronglyMeasurable_id_of_isSeparable [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (h1 : TopologicalSpace.IsSeparable s) (h2 : μ sᶜ = 0) :
    AEStronglyMeasurable id μ := by
  nontriviality α
  obtain ⟨a, -⟩ := exists_pair_ne α
  classical
  refine ⟨(closure s).piecewise id (fun _ ↦ a), ?_,
    Filter.mem_of_superset h2 (fun x hx ↦ by simp [subset_closure hx])⟩
  have h : StronglyMeasurable ((↑) : closure s → α) := by
    have := h1.closure.secondCountableTopology
    exact continuous_subtype_val.stronglyMeasurable
  have : (closure s).piecewise id (fun _ ↦ a) =
      ((↑) : closure s → α).extend ((↑) : closure s → α) (fun _ ↦ a) := by
    ext x
    by_cases hx : x ∈ closure s
    · simp [Function.extend_val_apply, hx]
    · simp [hx]
  rw [this]
  exact (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet).stronglyMeasurable_extend
    h stronglyMeasurable_const

namespace AEStronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.of_discrete** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：of_discrete [Countable α] [MeasurableSingletonClass α] : AEStronglyMeasura
ble f μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.of_discrete`：∀ {α : Type u_1} {β : Type
 u_2} {x : MeasurableSpace α} {f : α → β} [inst : TopologicalSpace β]   [Measura
bleSingletonClass α] [Countable α]…
-/
lemma of_discrete [Countable α] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ :=
  StronglyMeasurable.of_discrete.aestronglyMeasurable

section Mk

/-- A `StronglyMeasurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`stronglyMeasurable_mk` and `ae_eq_mk`. -/
/-
**MeasureTheory.AEStronglyMeasurable.mk** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.AEStronglyMeasurable`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace β] →     
  {m m₀ : MeasurableSpace α} →         {μ : MeasureTheory.Measure α} → (f : α → 
β) → MeasureTheory.AEStronglyMeasurable f μ → α → β
参数：f : α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A `StronglyMeasurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`stronglyMeasurable_mk` and `ae_eq_mk`.
-/
protected noncomputable def mk (f : α → β) (hf : AEStronglyMeasurable[m] f μ) : α → β :=
  hf.choose

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：stronglyMeasurable_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasura
ble[m] (hf.mk f)
参数：hf : AEStronglyMeasurable[m] f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma stronglyMeasurable_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f) :=
  hf.choose_spec.1

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.measurable_mk** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AEStronglyMeasurable`。
形式化陈述：measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
 (hf : AEStronglyMeasurable[m] f μ) : Measurable[m] (hf.mk f)
参数：hf : AEStronglyMeasurable[m] f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
-/
theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : AEStronglyMeasurable[m] f μ) : Measurable[m] (hf.mk f) :=
  hf.stronglyMeasurable_mk.measurable
/-
**MeasureTheory.AEStronglyMeasurable.ae_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEStronglyMeasurable`。
形式化陈述：ae_eq_mk (hf : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] hf.mk f
参数：hf : AEStronglyMeasurable[m] f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem ae_eq_mk (hf : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_5} [inst : MeasurableSpace β]   [inst_1 : TopologicalSpace β] [Topolog
icalSpace.PseudoMetrizableSpace β] [BorelSpace β] {f : α → β},   MeasureTheory.A
EStronglyMeasurable f μ → AEMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem aemeasurable {β} [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

/-
**MeasureTheory.AEStronglyMeasurable.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEStronglyMeasurable`。
形式化陈述：congr (hf : AEStronglyMeasurable[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasu
rable[m] g μ
参数：hf : AEStronglyMeasurable[m] f μ；h : f =ᵐ[μ] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem congr (hf : AEStronglyMeasurable[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_congr** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_congr (h : f =ᵐ[μ] g) :
    AEStronglyMeasurable[m] f μ ↔ AEStronglyMeasurable[m] g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩
/-
**MeasureTheory.AEStronglyMeasurable.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.AEStronglyMeasurable`。
形式化陈述：mono_measure {ν : Measure α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= 
μ) : AEStronglyMeasurable[m] f ν
参数：hf : AEStronglyMeasurable[m] f μ；h : ν <= μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem mono_measure {ν : Measure α} (hf : AEStronglyMeasurable[m] f μ) (h : ν ≤ μ) :
    AEStronglyMeasurable[m] f ν :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩
/-
**MeasureTheory.AEStronglyMeasurable.mono_ac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ ν : MeasureTheory.Measure α}   {f : α → β},   ν.AbsolutelyContin
uous μ → MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.AEStronglyMeasur
able f ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
-/
protected lemma mono_ac (h : ν ≪ μ) (hμ : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] f ν := let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩
/-
**MeasureTheory.AEStronglyMeasurable.mono_set** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEStronglyMeasurable`。
形式化陈述：mono_set {s t} (h : s subseteq t) (ht : AEStronglyMeasurable[m] f (μ.restr
ict t)) : AEStronglyMeasurable[m] f (μ.restrict s)
参数：h : s subseteq t；ht : AEStronglyMeasurable[m] f (μ.restrict t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mono_set {s t} (h : s ⊆ t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) :
    AEStronglyMeasurable[m] f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)
/-
**MeasureTheory.AEStronglyMeasurable.mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.AEStronglyMeasurable`。
形式化陈述：mono {m'} (hm : m <= m') (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMe
asurable[m'] f μ
参数：hm : m <= m'；hf : AEStronglyMeasurable[m] f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
-/
lemma mono {m'} (hm : m ≤ m') (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m'] f μ :=
  let ⟨f', hf'_meas, hff'⟩ := hf; ⟨f', hf'_meas.mono hm, hff'⟩
/-
**MeasureTheory.AEStronglyMeasurable.of_trim** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.AEStronglyMeasurable`。
形式化陈述：of_trim {m₀' : MeasurableSpace α} (hm₀ : m₀' <= m₀) (hf : AEStronglyMeasur
able[m] f (μ.trim hm₀)) : AEStronglyMeasurable[m] f μ
参数：hm₀ : m₀' <= m₀；hf : AEStronglyMeasurable[m] f (μ.trim hm₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
-/
lemma of_trim {m₀' : MeasurableSpace α} (hm₀ : m₀' ≤ m₀)
    (hf : AEStronglyMeasurable[m] f (μ.trim hm₀)) : AEStronglyMeasurable[m] f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β},   MeasureTheory.AEStro
nglyMeasurable f μ → ∀ {s : Set α}, MeasureTheory.AEStronglyMeasurable f (μ.rest
rict s)
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
protected theorem restrict (hfm : AEStronglyMeasurable[m] f μ) {s} :
    AEStronglyMeasurable[m] f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self
/-
**MeasureTheory.AEStronglyMeasurable.ae_mem_imp_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEStronglyMeasurable`。
形式化陈述：ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable[m] f (μ.restrict s)) : fora
llᵐ x ∂μ, x in s -> f x = h.mk f x
参数：h : AEStronglyMeasurable[m] f (μ.restrict s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable[m] f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Continuous.comp_aestronglyMeasurable
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of a continuous function and an ae strongly measurable function 
is ae strongly
measurable.
-/
theorem _root_.Continuous.comp_aestronglyMeasurable {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Continuous.aestronglyMeasurable** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function from `α` to `β` is ae strongly measurable when one of the 
two spaces is
second countable.
-/
theorem _root_.Continuous.aestronglyMeasurable [TopologicalSpace α] [OpensMeasurableSpace α]
    [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] (hf : Continuous f) :
    AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace β]
 [inst_1 : TopologicalSpace γ]   {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α} {f : α → β × γ},   MeasureTheory.AEStronglyMeasurable f μ → MeasureThe
ory.AEStronglyMeasurable (fun x => (f x).1) μ
参数：fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
protected theorem fst {f : α → β × γ} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x ↦ (f x).1) μ :=
  continuous_fst.comp_aestronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace β]
 [inst_1 : TopologicalSpace γ]   {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α} {f : α → β × γ},   MeasureTheory.AEStronglyMeasurable f μ → MeasureThe
ory.AEStronglyMeasurable (fun x => (f x).2) μ
参数：fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
protected theorem snd {f : α → β × γ} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x ↦ (f x).2) μ :=
  continuous_snd.comp_aestronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace β]
 [inst_1 : TopologicalSpace γ]   {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α} {f : α → β} {g : α → γ},   MeasureTheory.AEStronglyMeasurable f μ →   
  MeasureTheory.AEStronglyMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f
un x => (f x, g x)) μ
参数：fun x => (f x, g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} {l 
: Filter α} {f f' : α → β},   f =ᶠ[l] f' → ∀ {g g' : α → γ}, g =ᶠ[l] g' → (fun x
 => (f x, g x)) …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem prodMk {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prodMk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

/-- The composition of a continuous function of two variables and two ae strongly measurable
functions is ae strongly measurable. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.Continuous.comp_aestronglyMeasurable
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of a continuous function of two variables and two ae strongly me
asurable
functions is ae strongly measurable.
-/
theorem _root_.Continuous.comp_aestronglyMeasurable₂
    {β' : Type*} [TopologicalSpace β']
    {g : β → β' → γ} {f : α → β} {f' : α → β'} (hg : Continuous g.uncurry)
    (hf : AEStronglyMeasurable[m] f μ) (h'f : AEStronglyMeasurable[m] f' μ) :
    AEStronglyMeasurable[m] (fun x => g (f x) (f' x)) μ :=
  hg.comp_aestronglyMeasurable (hf.prodMk h'f)

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Measurable.aestronglyMeasurable** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a space with second countable topology, measurable implies ae strongly measur
able.
-/
theorem _root_.Measurable.aestronglyMeasurable
    [MeasurableSpace β] [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable[m] f) : AEStronglyMeasurable[m] f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
/-
**MeasureTheory.AEStronglyMeasurable.of_measurableSpace_le_on** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：of_measurableSpace_le_on {m' m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [
Zero β] (hm : m <= m₀) {s : Set α} (hs_m : MeasurableSet[m] s) (hs : forall t, M
easurableSet[m] (s inter t) -> MeasurableSet[m'] (s inter t)) (hf : AEStronglyMe
asurable[m] f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) : AEStronglyMeasurable[m'] f 
μ
参数：hm : m <= m₀；hs_m : MeasurableSet[m] s；hs : forall t, MeasurableSet[m] (s int
er t) -> MeasurableSet[m'] (s inter t)；hf : AEStronglyMeasurable[m] f μ；hf_zero 
: f =ᵐ[μ.restrict sᶜ] 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `indicator_ae_eq_of_restrict_compl_ae_eq_zero`：indicator_ae_eq_of_restric
t_compl_ae_eq_zero (hs : MeasurableSet s) (hf : f =ᵐ[μ.restrict sᶜ] 0) : s.indic
ator f =ᵐ[μ] f
· 使用定理 `MeasureTheory.StronglyMeasurable.stronglyMeasurable_of_measurableSpace_l
e_on`：stronglyMeasurable_of_measurableSpace_le_on {α E} {m m₂ : MeasurableSpace 
α} [TopologicalSpace E] [Zero E] {s : Set α} {f : α -> E} (hs_m : …
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…

--- 原说明 ---
If the restriction to a set `s` of a σ-algebra `m` is included in the restrictio
n to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a fu
nction `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable.
-/
lemma of_measurableSpace_le_on {m' m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [Zero β]
    (hm : m ≤ m₀) {s : Set α} (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) → MeasurableSet[m'] (s ∩ t))
    (hf : AEStronglyMeasurable[m] f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
    AEStronglyMeasurable[m'] f μ := by
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
    refine Filter.EventuallyEq.trans ?_ <|
      indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs, hx]
    · simp [hxs]
  suffices StronglyMeasurable[m'] (s.indicator (hf.mk f)) from
    this.aestronglyMeasurable.congr h_ind_eq
  exact (hf.stronglyMeasurable_mk.indicator hs_m).stronglyMeasurable_of_measurableSpace_le_on hs_m
    hs fun x hxs => Set.indicator_of_notMem hxs _

section Arithmetic

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.AEStronglyMeasurable.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f g : α → β} [inst_1 : Mul β] [Con
tinuousMul β],   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTheory.AESt
ronglyMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f * g) μ
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Mul β
]   [ContinuousMul β],   M…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f * g) μ :=
  ⟨hf.mk f * hg.mk g, by fun_prop, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Mul β] [Conti
nuousMul β],   MeasureTheory.AEStronglyMeasurable f μ → ∀ (c : β), MeasureTheory
.AEStronglyMeasurable (fun x => f x * c) μ
参数：c : β；fun x => f x * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => f x * c) μ :=
  hf.mul aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Mul β] [Conti
nuousMul β],   MeasureTheory.AEStronglyMeasurable f μ → ∀ (c : β), MeasureTheory
.AEStronglyMeasurable (fun x => c * f x) μ
参数：c : β；fun x => c * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => c * f x) μ :=
  aestronglyMeasurable_const.mul hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.AEStronglyMeasurable.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Inv β] [Conti
nuousInv β],   MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.AEStrongly
Measurable f⁻¹ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Inv β] 
  [ContinuousInv β], Measu…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.inv`：∀ {α : Type u} {β : Type v} [inst : Inv β] {f g
 : α → β} {l : Filter α}, f =ᶠ[l] g → f⁻¹ =ᶠ[l] g⁻¹
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem inv [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Inv β] [Conti
nuousInv β],   MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.AEStrongly
Measurable f⁻¹ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Inv β] 
  [ContinuousInv β], Measu…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.inv`：∀ {α : Type u} {β : Type v} [inst : Inv β] {f g
 : α → β} {l : Filter α}, f =ᶠ[l] g → f⁻¹ =ᶠ[l] g⁻¹
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem inv₀ [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv₀, hf.ae_eq_mk.inv⟩

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.AEStronglyMeasurable.div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f g : α → β} [inst_1 : Group β] [I
sTopologicalGroup β],   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTheo
ry.AEStronglyMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f / g) μ
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.div'`：∀ {α : Type u_1} {β : Type u_2} {
f g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Div 
β]   [ContinuousDiv β],   M…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.div`：∀ {α : Type u} {β : Type v} [inst : Div β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f / f' =ᶠ[l] g / g'
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem div [Group β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div' hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f g : α → β} [inst_1 : Group β] [I
sTopologicalGroup β],   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTheo
ry.AEStronglyMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f / g) μ
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.div'`：∀ {α : Type u_1} {β : Type u_2} {
f g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Div 
β]   [ContinuousDiv β],   M…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.div`：∀ {α : Type u} {β : Type v} [inst : Div β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f / f' =ᶠ[l] g / g'
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem div₀ [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]
/-
**MeasureTheory.AEStronglyMeasurable.mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AEStronglyMeasurable`。
形式化陈述：mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasura
ble[m] f μ) : AEStronglyMeasurable[m] (f * g) μ ↔ AEStronglyMeasurable[m] g μ
参数：hf : AEStronglyMeasurable[m] f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
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
theorem mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (f * g) μ ↔ AEStronglyMeasurable[m] g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
/-
**MeasureTheory.AEStronglyMeasurable.mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.AEStronglyMeasurable`。
形式化陈述：mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurab
le[m] f μ) : AEStronglyMeasurable[m] (g * f) μ ↔ AEStronglyMeasurable[m] g μ
参数：hf : AEStronglyMeasurable[m] f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_iff_right`：mul_iff_right [CommGro
up β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeas
urable[m] (f * g) μ ↔ AEStronglyMeasur…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (g * f) μ ↔ AEStronglyMeasurable[m] g μ :=
  mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**MeasureTheory.AEStronglyMeasurable.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {𝕜 : Type u_5} [inst_1 : Topologica
lSpace 𝕜] [inst_2 : SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜} {g : α → β},   Me
asureTheory.AEStronglyMeasurable f μ →     MeasureTheory.AEStronglyMeasurable g 
μ → MeasureTheory.AEStronglyMeasurable (f • g) μ
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
-/
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (f • g) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]
/-
**MeasureTheory.AEStronglyMeasurable.pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Monoid β] [Co
ntinuousMul β],   MeasureTheory.AEStronglyMeasurable f μ → ∀ (n : ℕ), MeasureThe
ory.AEStronglyMeasurable (f ^ n) μ
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.pow`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Monoid 
β]   [ContinuousMul β], Me…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.pow_const`：∀ {α : Type u} {β : Type v} {γ : Type u_2
} [inst : Pow β γ] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), f ^ c 
=ᶠ[l] g ^ c
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem pow [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (n : ℕ) :
    AEStronglyMeasurable[m] (f ^ n) μ :=
  ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**MeasureTheory.AEStronglyMeasurable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} {𝕜 : Type u_5} [inst_1 
: SMul 𝕜 β] [ContinuousConstSMul 𝕜 β],   MeasureTheory.AEStronglyMeasurable f μ 
→ ∀ (c : 𝕜), MeasureTheory.AEStronglyMeasurable (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type 
u_5}   [inst_1 : SMul 𝕜 β] [Conti…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable[m] f μ) (c : 𝕜) : AEStronglyMeasurable[m] (c • f) μ :=
  ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := AEStronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := AEStronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m m₀ : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {𝕜 : Type u_5} [inst_1 : Topologica
lSpace 𝕜] [inst_2 : SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜},   MeasureTheory.
AEStronglyMeasurable f μ → ∀ (c : β), MeasureTheory.AEStronglyMeasurable (fun x 
=> f x • c) μ
参数：c : β；fun x => f x • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : AEStronglyMeasurable[m] f μ) (c : β) : AEStronglyMeasurable[m] (fun x => f x • c) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prodMk aestronglyMeasurable_const)

end Arithmetic

section Star

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.star** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {R
 : Type u_5} [inst : TopologicalSpace R]   [inst_1 : Star R] [ContinuousStar R] 
{f : α → R},   MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.AEStrongly
Measurable (star f) μ
参数：star f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.star`：∀ {α : Type u_1} {R : Type u_5} [
inst : MeasurableSpace α] [inst_1 : Star R] [inst_2 : TopologicalSpace R]   [Con
tinuousStar R] (f : α → R),…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.star`：∀ {α : Type u} {R : Type u_2} [inst : Star R] 
{f g : α → R} {l : Filter α}, f =ᶠ[l] g → star f =ᶠ[l] star g
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem star {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R] {f : α → R}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (star f) μ :=
  ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩

end Star

section Order

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   {f g : α → β} [inst_1 : SemilatticeSu
p β] [ContinuousSup β],   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTh
eory.AEStronglyMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f ⊔ g) μ
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace β] [inst_2 : M
ax β]   [ContinuousSup β],…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.sup`：∀ {α : Type u} {β : Type v} [inst : Max β] {l :
 Filter α} {f f' g g' : α → β},   f =ᶠ[l] f' → g =ᶠ[l] g' → f ⊔ g =ᶠ[l] f' ⊔ g'
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   {f g : α → β} [inst_1 : SemilatticeIn
f β] [ContinuousInf β],   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTh
eory.AEStronglyMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f ⊓ g) μ
参数：f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.inf`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace β] [inst_2 : M
in β]   [ContinuousInf β],…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.inf`：∀ {α : Type u} {β : Type v} [inst : Min β] {l :
 Filter α} {f f' g g' : α → β},   f =ᶠ[l] f' → g =ᶠ[l] g' → f ⊓ g =ᶠ[l] f' ⊓ g'
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.oneLePart** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Group β] [inst_
2 : Lattice β] [ContinuousSup β],   MeasureTheory.AEStronglyMeasurable f μ → Mea
sureTheory.AEStronglyMeasurable (fun x => (f x)⁺ᵐ) μ
参数：fun x => (f x)⁺ᵐ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure 
α}   {f g : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
protected theorem oneLePart [Group β] [Lattice β] [ContinuousSup β]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ oneLePart (f x)) μ :=
  hf.sup aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable.leOnePart** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Group β] [inst_
2 : Lattice β] [ContinuousSup β] [ContinuousInv β],   MeasureTheory.AEStronglyMe
asurable f μ → MeasureTheory.AEStronglyMeasurable (fun x => (f x)⁻ᵐ) μ
参数：fun x => (f x)⁻ᵐ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure 
α}   {f g : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
protected theorem leOnePart [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ leOnePart (f x)) μ :=
  hf.inv.sup aestronglyMeasurable_const

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable._root_.List.aestronglyMeasurable_prod** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.aestronglyMeasurable_prod (l : List (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  induction l with
  | nil => exact aestronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable._root_.List.aestronglyMeasurable_fun_prod**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.aestronglyMeasurable_fun_prod
    (l : List (α → M)) (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Multiset.aestronglyMeasurable_prod**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Multiset.aestronglyMeasurable_prod (l : Multiset (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Multiset.aestronglyMeasurable_fun_pr
od** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Multiset.aestronglyMeasurable_fun_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Finset.aestronglyMeasurable_prod** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.aestronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏ i ∈ s, f i) μ :=
  Multiset.aestronglyMeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.AEStronglyMeasurable._root_.Finset.aestronglyMeasurable_fun_prod
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.aestronglyMeasurable_fun_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∏ i ∈ s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod hf

end CommMonoid

section SecondCountableAEStronglyMeasurable

variable [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable._root_.AEMeasurable.aestronglyMeasurable** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a space with second countable topology, measurable implies strongly measurabl
e.
-/
theorem _root_.AEMeasurable.aestronglyMeasurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AEMeasurable f μ) : AEStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_id** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_id {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {_ : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AEStronglyMeasurable (id : α → α) μ :=
  aemeasurable_id.aestronglyMeasurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_iff_aemeasurabl
e** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a space with second countable topology, strongly measurable and measurable ar
e equivalent.
-/
theorem _root_.aestronglyMeasurable_iff_aemeasurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩

end SecondCountableAEStronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.dist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_5} [inst : PseudoMetricSpace β]   {f g : α → β},   MeasureTheory.AEStr
onglyMeasurable f μ →     MeasureTheory.AEStronglyMeasurable g μ → MeasureTheory
.AEStronglyMeasurable (fun x => dist (f x) (g x)) μ
参数：fun x => dist (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
-/
protected theorem dist {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_5} [inst : SeminormedAddCommGroup β]   {f : α → β}, MeasureTheory.AESt
ronglyMeasurable f μ → MeasureTheory.AEStronglyMeasurable (fun x => ‖f x‖) μ
参数：fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
-/
protected theorem norm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖) μ :=
  continuous_norm.comp_aestronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_5} [inst : SeminormedAddCommGroup β]   {f : α → β}, MeasureTheory.AESt
ronglyMeasurable f μ → MeasureTheory.AEStronglyMeasurable (fun x => ‖f x‖₊) μ
参数：fun x => ‖f x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_nnnorm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Conti
nuous fun a => ‖a‖₊
-/
protected theorem nnnorm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖₊) μ :=
  continuous_nnnorm.comp_aestronglyMeasurable hf

/-- The `enorm` of a strongly a.e. measurable function is a.e. measurable.

Note that unlike `AEStronglyMeasurable.norm` and `AEStronglyMeasurable.nnnorm`, this lemma proves
a.e. measurability, **not** a.e. strong measurability. This is an intentional decision:
for functions taking values in `ℝ≥0∞`, a.e. measurability is much more useful than
a.e. strong measurability. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_5} [inst : TopologicalSpace β]   [inst_1 : ContinuousENorm β] {f : α →
 β}, MeasureTheory.AEStronglyMeasurable f μ → AEMeasurable (fun x => ‖f x‖ₑ) μ
参数：fun x => ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ

--- 原说明 ---
The `enorm` of a strongly a.e. measurable function is a.e. measurable.

Note that unlike `AEStronglyMeasurable.norm` and `AEStronglyMeasurable.nnnorm`, 
this lemma proves
a.e. measurability, **not** a.e. strong measurability. This is an intentional de
cision:
for functions taking values in `ℝ≥0∞`, a.e. measurability is much more useful th
an
a.e. strong measurability.
-/
protected theorem enorm {β : Type*} [TopologicalSpace β] [ContinuousENorm β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (‖f ·‖ₑ) μ :=
  (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable

/-- Given a.e. strongly measurable functions `f` and `g`, `edist f g` is measurable.

Note that this lemma proves a.e. measurability, **not** a.e. strong measurability.
This is an intentional decision: for functions taking values in ℝ≥0∞,
a.e. measurability is much more useful than a.e. strong measurability. -/
@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.edist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_5} [inst : PseudoMetricSpace β]   {f g : α → β},   MeasureTheory.AEStr
onglyMeasurable f μ →     MeasureTheory.AEStronglyMeasurable g μ → AEMeasurable 
(fun a => edist (f a) (g a)) μ
参数：fun a => edist (f a) (g a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…

--- 原说明 ---
Given a.e. strongly measurable functions `f` and `g`, `edist f g` is measurable.

Note that this lemma proves a.e. measurability, **not** a.e. strong measurabilit
y.
This is an intentional decision: for functions taking values in ℝ≥0∞,
a.e. measurability is much more useful than a.e. strong measurability.
-/
protected theorem edist {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_aestronglyMeasurable (hf.prodMk hg)).aemeasurable

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 : α → ℝ},   MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.AEStronglyMe
asurable (fun x => (f x).toNNReal) μ
参数：fun x => (f x).toNNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
-/
protected theorem real_toNNReal {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_indicator_iff**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_indicator_iff**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_indicator_iff₀
    [Zero β] {s : Set α} (hs : NullMeasurableSet s μ) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  rw [← aestronglyMeasurable_congr (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    aestronglyMeasurable_indicator_iff (measurableSet_toMeasurable ..),
    restrict_congr_set hs.toMeasurable_ae_eq]

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Zero β],   Meas
ureTheory.AEStronglyMeasurable f μ →     ∀ {s : Set α}, MeasurableSet s → Measur
eTheory.AEStronglyMeasurable (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aestronglyMeasurable_indicator_iff`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {f : α → β} [inst_1 : Z…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
-/
protected theorem indicator [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : MeasurableSet s) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace β] {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α}   {f : α → β} [inst_1 : Zero β],   Meas
ureTheory.AEStronglyMeasurable f μ →     ∀ {s : Set α}, MeasurableSet s → Measur
eTheory.AEStronglyMeasurable (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aestronglyMeasurable_indicator_iff`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {f : α → β} [inst_1 : Z…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
-/
protected theorem indicator₀ [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : NullMeasurableSet s μ) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff₀ hs).2 hfm.restrict
/-
**MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_eq_fun** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g
 : α -> E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) : Nul
lMeasurableSet { x | f x = g x } μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_eq_fun`：measurableSet_eq_
fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSe
t[m] {a | f a = g a}
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]

@[to_additive]
/-
**MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_mulSupport** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：nullMeasurableSet_mulSupport {E} [TopologicalSpace E] [MetrizableSpace E] 
[One E] {f : α -> E} (hf : AEStronglyMeasurable f μ) : NullMeasurableSet (mulSup
port f) μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_eq_fun`：nullMeasura
bleSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α -> E} (hf : 
AEStronglyMeasurable f μ) (hg : AEStronglyMeasura…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
lemma nullMeasurableSet_mulSupport {E} [TopologicalSpace E] [MetrizableSpace E] [One E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) : NullMeasurableSet (mulSupport f) μ :=
  (hf.nullMeasurableSet_eq_fun stronglyMeasurable_const.aestronglyMeasurable).compl
/-
**MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_lt** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：nullMeasurableSet_lt [Preorder β] [OrderClosedTopology β] [PseudoMetrizabl
eSpace β] {f g : α -> β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasura
ble g μ) : NullMeasurableSet { a | f a < g a } μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_lt`：measurableSet_lt (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a < g a}
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nullMeasurableSet_lt [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a < g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_lt hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x < hg.mk g x) = (f x < g x)
  simp only [hfx, hgx]
/-
**MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizabl
eSpace β] {f g : α -> β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasura
ble g μ) : NullMeasurableSet { a | f a <= g a } μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x ≤ hg.mk g x) = (f x ≤ g x)
  simp only [hfx, hgx]
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_of_aestronglyMe
asurable_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim {α} {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) {f : α → β} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    AEStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩
/-
**MeasureTheory.AEStronglyMeasurable.comp_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：comp_aemeasurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace
 α} {f : γ -> α} {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ))
 (hf : AEMeasurable f μ) : AEStronglyMeasurable (g ∘ f) μ
参数：hg : AEStronglyMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem comp_aemeasurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩
/-
**MeasureTheory.AEStronglyMeasurable.comp_measurable** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.AEStronglyMeasurable`。
形式化陈述：comp_measurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α
} {f : γ -> α} {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (
hf : Measurable f) : AEStronglyMeasurable (g ∘ f) μ
参数：hg : AEStronglyMeasurable g (Measure.map f μ)；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_aemeasurable`：comp_aemeasurable 
{γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Me
asure γ} (hg : AEStronglyMeasurable g (Mea…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem comp_measurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable
/-
**MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：comp_quasiMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : Measu
rableSpace α} {f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasu
rable g ν) (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ
参数：hg : AEStronglyMeasurable g ν；hf : QuasiMeasurePreserving f μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem comp_quasiMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
    {f : γ → α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono_ac hf.absolutelyContinuous).comp_measurable hf.measurable
/-
**MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：isSeparable_ae_range (hf : AEStronglyMeasurable f μ) : exists t : Set β, I
sSeparable t ∧ forallᵐ x ∂μ, f x in t
参数：hf : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isSeparable_ae_range (hf : AEStronglyMeasurable f μ) :
    ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, ?_⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]

/-- If `μ : Measure α` and `f : α → β` is `AEStronglyMeasurable` where `β` is a pseudometrizable
space and a Borel space, then the identity is a.e.-strongly measurable w.r.t. `μ.map f`. -/
/-
**MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_id_map** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：aestronglyMeasurable_id_map {mβ : MeasurableSpace β} [TopologicalSpace.Pse
udoMetrizableSpace β] [BorelSpace β] {f : α -> β} (hf : AEStronglyMeasurable f μ
) : AEStronglyMeasurable id (μ.map f)
参数：hf : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range`：isSeparable_ae_
range (hf : AEStronglyMeasurable f μ) : exists t : Set β, IsSeparable t ∧ forall
ᵐ x ∂μ, f x in t
· 使用引理 `MeasureTheory.aestronglyMeasurable_id_of_isSeparable`：aestronglyMeasurab
le_id_of_isSeparable [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpac
e α] [OpensMeasurableSpace α] {s : Set α} …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If `μ : Measure α` and `f : α → β` is `AEStronglyMeasurable` where `β` is a pseu
dometrizable
space and a Borel space, then the identity is a.e.-strongly measurable w.r.t. `μ
.map f`.
-/
lemma aestronglyMeasurable_id_map {mβ : MeasurableSpace β}
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β]
    {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable id (μ.map f) := by
  obtain ⟨t, ht1, ht2⟩ := hf.isSeparable_ae_range
  refine aestronglyMeasurable_id_of_isSeparable ht1.closure ?_
  refine ae_map_iff hf.aemeasurable isClosed_closure.measurableSet |>.2 ?_
  filter_upwards [ht2] with ω hω using subset_closure hω

/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_iff_aemeasurabl
e_separable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is almost everywhere strongly measurable if and only if it is almost 
everywhere
measurable, and up to a zero measure set its range is contained in a separable s
et.
-/
theorem _root_.aestronglyMeasurable_iff_aemeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      AEMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, ?_⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, g_meas, gt, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine ⟨g, ?_, fg⟩
    exact stronglyMeasurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono gt⟩
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_iff_nullMeasura
ble_separable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_iff_nullMeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      NullMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t :=
  aestronglyMeasurable_iff_aemeasurable_separable.trans <| and_congr_left fun ⟨_, hsep, h⟩ ↦
    have := hsep.secondCountableTopology
    ⟨AEMeasurable.nullMeasurable, fun hf ↦ hf.aemeasurable_of_aerange h⟩
/-
**MeasureTheory.AEStronglyMeasurable._root_.MeasurableEmbedding.aestronglyMeasur
able_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.aestronglyMeasurable_map_iff {γ : Type*}
    {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    (hf : MeasurableEmbedding f) {g : α → β} :
    AEStronglyMeasurable g (Measure.map f μ) ↔ AEStronglyMeasurable (g ∘ f) μ := by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩
/-
**MeasureTheory.AEStronglyMeasurable._root_.Topology.IsEmbedding.aestronglyMeasu
rable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Topology.IsEmbedding.aestronglyMeasurable_comp_iff [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β} (hg : IsEmbedding g) :
    AEStronglyMeasurable (fun x => g (f x)) μ ↔ AEStronglyMeasurable f μ := by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by rw [rangeFactorization_surjective.range_eq]; exact isClosed_univ }
    have : AEMeasurable (G ∘ f) μ := AEMeasurable.subtype_mk H.aemeasurable
    exact hG.measurableEmbedding.aemeasurable_comp_iff.1 this
  · rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.isSeparable_preimage ht, h't⟩

/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_of_tendsto_ae**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An almost everywhere sequential limit of almost everywhere strongly measurable f
unctions is
almost everywhere strongly measurable.
-/
theorem _root_.aestronglyMeasurable_of_tendsto_ae {ι : Type*} [PseudoMetrizableSpace β]
    (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι → α → β} {g : α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    AEStronglyMeasurable g μ := by
  borelize β
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : ∀ n : ℕ, ∃ t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t ∈ ae μ := fun n =>
      (aestronglyMeasurable_iff_aemeasurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
    refine ⟨closure (⋃ i, t i), .closure <| .iUnion t_sep, ?_⟩
    filter_upwards [ae_all_iff.2 ht, lim] with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    filter_upwards with n using mem_iUnion_of_mem n (hx n)

/-- If a sequence of almost everywhere strongly measurable functions converges almost everywhere,
one can select a strongly measurable function as the almost everywhere limit. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.exists_stronglyMeasurable_limit_of_t
endsto_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a sequence of almost everywhere strongly measurable functions converges almos
t everywhere,
one can select a strongly measurable function as the almost everywhere limit.
-/
theorem _root_.exists_stronglyMeasurable_limit_of_tendsto_ae [PseudoMetrizableSpace β]
    {f : ℕ → α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) atTop (𝓝 l)) :
    ∃ f_lim : α → β, StronglyMeasurable f_lim ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) := by
  borelize β
  obtain ⟨g, _, hg⟩ :
    ∃ g : α → β, Measurable g ∧ ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).aemeasurable) h_ae_tendsto
  have Hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hg
  refine ⟨Hg.mk g, Hg.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x
  rwa [h'x] at hx

/-- If `f` is almost everywhere strongly measurable and its range is almost everywhere contained
in a nonempty measurable set `s`, then there is a strongly measurable representative `g` of `f`
whose range is contained in `s`. -/
/-
**MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_range_subset** 是 
Mathlib 中的一个引理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：exists_stronglyMeasurable_range_subset {α β : Type*} [TopologicalSpace β] 
[PseudoMetrizableSpace β] [mb : MeasurableSpace β] [BorelSpace β] [m : Measurabl
eSpace α] {μ : Measure α} {f : α -> β} (hf : AEStronglyMeasurable f μ) {s : Set 
β} (hs : MeasurableSet s) (h_nonempty : s.Nonempty) (h_mem : forallᵐ x ∂μ, f x i
n s) : exists g : α -> β, StronglyMeasurable g ∧ (forall x, g x in s) ∧ f =ᵐ[μ] 
g
参数：hf : AEStronglyMeasurable f μ；hs : MeasurableSet s；h_nonempty : s.Nonempty；h_
mem : forallᵐ x ∂μ, f x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.piecewise`：∀ {α : Type u_1} {β : Type u
_2} {f g : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β] {s : Set α
}   {x : DecidablePred fun x => …
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_piecewise`：range_piecewise (f g : α -> β) : range (s.piecewise
 f g) = f '' s union g '' sᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i

--- 原说明 ---
If `f` is almost everywhere strongly measurable and its range is almost everywhe
re contained
in a nonempty measurable set `s`, then there is a strongly measurable representa
tive `g` of `f`
whose range is contained in `s`.
-/
lemma exists_stronglyMeasurable_range_subset {α β : Type*}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [mb : MeasurableSpace β] [BorelSpace β]
    [m : MeasurableSpace α] {μ : Measure α} {f : α → β} (hf : AEStronglyMeasurable f μ)
    {s : Set β} (hs : MeasurableSet s) (h_nonempty : s.Nonempty) (h_mem : ∀ᵐ x ∂μ, f x ∈ s) :
    ∃ g : α → β, StronglyMeasurable g ∧ (∀ x, g x ∈ s) ∧ f =ᵐ[μ] g := by
  obtain ⟨f', hf', hff'⟩ := hf
  classical
  refine ⟨(f' ⁻¹' s).piecewise f' (fun _ ↦ h_nonempty.some), ?meas, ?subset, ?ae_eq⟩
  case meas => exact hf'.piecewise (hf'.measurable hs) stronglyMeasurable_const
  case subset =>
    rw [← Set.range_subset_iff]
    simpa [Set.range_piecewise] using! fun _ _ ↦ h_nonempty.some_mem
  case ae_eq =>
    apply hff'.trans
    filter_upwards [h_mem, hff'] with x hx hx'
    exact Eq.symm <| (f' ⁻¹' s).piecewise_eq_of_mem f' _ (by simpa [hx'] using! hx)
/-
**MeasureTheory.AEStronglyMeasurable.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：piecewise {s : Set α} [DecidablePred (· in s)] (hs : MeasurableSet s) (hf 
: AEStronglyMeasurable f (μ.restrict s)) (hg : AEStronglyMeasurable g (μ.restric
t sᶜ)) : AEStronglyMeasurable (s.piecewise f g) μ
参数：· in s；hs : MeasurableSet s；hf : AEStronglyMeasurable f (μ.restrict s)；hg : A
EStronglyMeasurable g (μ.restrict sᶜ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.piecewise`：∀ {α : Type u_1} {β : Type u
_2} {f g : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β] {s : Set α
}   {x : DecidablePred fun x => …
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem piecewise {s : Set α} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hg : AEStronglyMeasurable g (μ.restrict sᶜ)) :
    AEStronglyMeasurable (s.piecewise f g) μ := by
  refine ⟨s.piecewise (hf.mk f) (hg.mk g),
    StronglyMeasurable.piecewise hs hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk, ?_⟩
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' hs] at h
    rw [ae_restrict_iff' hs]
    filter_upwards [h] with x hx
    intro hx_mem
    simp only [hx_mem, Set.piecewise_eq_of_mem, hx hx_mem]
  · have h := hg.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at h
    rw [ae_restrict_iff' hs.compl]
    filter_upwards [h] with x hx
    intro hx_mem
    rw [Set.mem_compl_iff] at hx_mem
    simp only [hx_mem, not_false_eq_true, Set.piecewise_eq_of_notMem, hx hx_mem]

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.sum_measure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι -> Me
asure α} (h : forall i, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (
Measure.sum μ)
参数：h : forall i, AEStronglyMeasurable f (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `AEMeasurable.sum_measure`：sum_measure [Countable ι] {μ : ι -> Measure α}
 (h : forall i, AEMeasurable f (μ i)) : AEMeasurable f (sum μ)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsSeparable.iUnion`：∀ {α : Type u} [t : TopologicalSpac
e α] {ι : Sort u_2} [Countable ι] {s : ι → Set α},   (∀ (i : ι), TopologicalSpac
e.IsSeparable (s i)) → To…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.ae_sum_eq`：ae_sum_eq [Countable ι] (μ : ι -> Measu
re α) : ae (sum μ) = ⨆ i, ae (μ i)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι → Measure α}
    (h : ∀ i, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (Measure.sum μ) := by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, ?_⟩
  have A : ∀ i : ι, ∃ t : Set β, IsSeparable t ∧ f ⁻¹' t ∈ ae (μ i) := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine ⟨⋃ i, t i, .iUnion t_sep, ?_⟩
  simp only [Measure.ae_sum_eq, mem_iUnion, eventually_iSup]
  intro i
  filter_upwards [ht i] with x hx
  exact ⟨i, hx⟩

@[simp]
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_sum_measure_iff
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_sum_measure_iff [PseudoMetrizableSpace β]
    {_m : MeasurableSpace α} {μ : ι → Measure α} :
    AEStronglyMeasurable f (sum μ) ↔ ∀ i, AEStronglyMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_add_measure_iff
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AEStronglyMeasurable f (μ + ν) ↔ AEStronglyMeasurable f μ ∧ AEStronglyMeasurable f ν := by
  rw [← sum_cond, aestronglyMeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α -> β} (hμ : A
EStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) : AEStronglyMeasurable 
f (μ + ν)
参数：hμ : AEStronglyMeasurable f μ；hν : AEStronglyMeasurable f ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aestronglyMeasurable_add_measure_iff`：∀ {α : Type u_1} {β : Type u_2} [i
nst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}
   {f : α → β} [Topologica…
-/
theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α → β}
    (hμ : AEStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable f (μ + ν) :=
  aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [Countable ι] [inst : Topol
ogicalSpace β] {m₀ : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {f : α →
 β} [TopologicalSpace.PseudoMetrizableSpace β] {s : ι → Set α},   (∀ (i : ι), Me
asureTheory.AEStronglyMeasurable f (μ.restrict (s i))) →     MeasureTheory.AEStr
onglyMeasurable f (μ.restrict (⋃ i, s i))
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable f (μ.restrict (s i))；μ.restrict
 (⋃ i, s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sum_measure`：sum_measure [PseudoMetri
zableSpace β] {m : MeasurableSpace α} {μ : ι -> Measure α} (h : forall i, AEStro
nglyMeasurable f (μ i)) : AEStrongly…
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_le`：restrict_iUnion_le [Countable 
ι] {s : ι -> Set α} : μ.restrict (⋃ i, s i) <= sum fun i => μ.restrict (s i)
-/
protected theorem iUnion [PseudoMetrizableSpace β] {s : ι → Set α}
    (h : ∀ i, AEStronglyMeasurable f (μ.restrict (s i))) :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le

@[simp]
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_iUnion_iff** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_iUnion_iff [PseudoMetrizableSpace β] {s : ι → Set α} :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔
      ∀ i, AEStronglyMeasurable f (μ.restrict (s i)) :=
  ⟨fun h _ => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩

@[simp]
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_union_iff** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AEStronglyMeasurable f (μ.restrict (s ∪ t)) ↔
      AEStronglyMeasurable f (μ.restrict s) ∧ AEStronglyMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]
/-
**MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f
 : α -> β} {a b : α} : AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔ AEStron
glyMeasurable f (μ.restrict <| Ioc a b) ∧ AEStronglyMeasurable f (μ.restrict <| 
Ioc b a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `aestronglyMeasurable_union_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : 
TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f 
: α → β} [Topologica…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f : α → β}
    {a b : α} :
    AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔
      AEStronglyMeasurable f (μ.restrict <| Ioc a b) ∧
        AEStronglyMeasurable f (μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union, aestronglyMeasurable_union_iff]

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.AEStronglyMeasurable`。
形式化陈述：smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>
=0∞] (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ)
参数：h : AEStronglyMeasurable f μ；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩

section MulAction

variable {M G G₀ : Type*}
variable [Monoid M] [MulAction M β]
variable [Group G] [MulAction G β]
variable [GroupWithZero G₀] [MulAction G₀ β]

/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_const_smul_iff*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_const_smul_iff [ContinuousConstSMul G β] (c : G) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

/-- Multiplying by an a.e. strongly measurable scalar *function* with values in a group preserves
a.e. strong measurability. This is the varying-scalar analogue of
`aestronglyMeasurable_const_smul_iff`. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_smul_iff** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying by an a.e. strongly measurable scalar *function* with values in a gr
oup preserves
a.e. strong measurability. This is the varying-scalar analogue of
`aestronglyMeasurable_const_smul_iff`.
-/
theorem _root_.aestronglyMeasurable_smul_iff [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G β] {c : α → G} (hc : AEStronglyMeasurable c μ) :
    AEStronglyMeasurable (fun x => c x • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => (hc.fun_inv.fun_smul h).congr (by simp), fun h => hc.fun_smul h⟩

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff [ContinuousConstSMul M β] {c : M}
    (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aestronglyMeasurable_const_smul_iff u
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_const_smul_iff*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.aestronglyMeasurable_const_smul_iff₀ [ContinuousConstSMul G₀ β] {c : G₀}
    (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff

/-- Multiplying by an almost-everywhere nonzero scalar *function* preserves a.e. strong
measurability. This is the varying-scalar analogue of `aestronglyMeasurable_const_smul_iff₀`. -/
/-
**MeasureTheory.AEStronglyMeasurable._root_.aestronglyMeasurable_smul_iff** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying by an almost-everywhere nonzero scalar *function* preserves a.e. str
ong
measurability. This is the varying-scalar analogue of `aestronglyMeasurable_cons
t_smul_iff₀`.
-/
theorem _root_.aestronglyMeasurable_smul_iff₀ [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MetrizableSpace G₀] [ContinuousSMul G₀ β] {c : α → G₀}
    (hc : AEStronglyMeasurable c μ) (hc0 : ∀ᵐ x ∂μ, c x ≠ 0) :
    AEStronglyMeasurable (fun x => c x • f x) μ ↔ AEStronglyMeasurable f μ := by
  refine ⟨fun h => (hc.fun_inv₀.fun_smul h).congr ?_, fun h => hc.fun_smul h⟩
  filter_upwards [hc0] with x hx
  simp [hx]

end MulAction

end AEStronglyMeasurable
end AEStronglyMeasurable

/-! ## Almost everywhere finitely strongly measurable functions -/


namespace AEFinStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α → β}

section Mk

variable [Zero β]

/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
/-
**MeasureTheory.AEFinStronglyMeasurable.mk** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.AEFinStronglyMeasurable`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {m : MeasurableSpace α} →       {μ
 : MeasureTheory.Measure α} →         [inst : TopologicalSpace β] →           [i
nst_1 : Zero β] → (f : α → β) → MeasureTheory.AEFinStronglyMeasurable f μ → α → 
β
参数：f : α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`.
-/
protected noncomputable def mk (f : α → β) (hf : AEFinStronglyMeasurable f μ) : α → β :=
  hf.choose
/-
**MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyM
easurable (hf.mk f) μ
参数：hf : AEFinStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) :
    FinStronglyMeasurable (hf.mk f) μ :=
  hf.choose_spec.1
/-
**MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEFinStronglyMeasurable`。
形式化陈述：ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
参数：hf : AEFinStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[fun_prop]
/-
**MeasureTheory.AEFinStronglyMeasurable.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_5} [inst : Zero β]   [inst_1 : MeasurableSpace β] [inst_2 : Topological
Space β] [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β]   {f : α → β}
, MeasureTheory.AEFinStronglyMeasurable f μ → AEMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β} [inst
 : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem aemeasurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEFinStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

section Arithmetic

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.AEFinStronglyMeasurable.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f g : α → β} [inst_1 : MulZeroClass β
] [ContinuousMul β],   MeasureTheory.AEFinStronglyMeasurable f μ →     MeasureTh
eory.AEFinStronglyMeasurable g μ → MeasureTheory.AEFinStronglyMeasurable (f * g)
 μ
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → β}   [inst : 
TopologicalSpace β] [inst_1 :…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.AEFinStronglyMeasurable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f g : α → β} [inst_1 : AddZeroClass β
] [ContinuousAdd β],   MeasureTheory.AEFinStronglyMeasurable f μ →     MeasureTh
eory.AEFinStronglyMeasurable g μ → MeasureTheory.AEFinStronglyMeasurable (f + g)
 μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → β}   [inst : 
TopologicalSpace β] [inst_1 :…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩

@[measurability]
/-
**MeasureTheory.AEFinStronglyMeasurable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f : α → β} [inst_1 : SubtractionMonoi
d β] [ContinuousNeg β],   MeasureTheory.AEFinStronglyMeasurable f μ → MeasureThe
ory.AEFinStronglyMeasurable (-f) μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β}   [inst : To
pologicalSpace β] [inst_1 : S…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.neg`：∀ {α : Type u} {β : Type v} [inst : Neg β] {f g
 : α → β} {l : Filter α}, f =ᶠ[l] g → -f =ᶠ[l] -g
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem neg [SubtractionMonoid β] [ContinuousNeg β] (hf : AEFinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩

@[measurability]
/-
**MeasureTheory.AEFinStronglyMeasurable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f g : α → β} [inst_1 : SubtractionMon
oid β] [ContinuousSub β],   MeasureTheory.AEFinStronglyMeasurable f μ →     Meas
ureTheory.AEFinStronglyMeasurable g μ → MeasureTheory.AEFinStronglyMeasurable (f
 - g) μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → β}   [inst : 
TopologicalSpace β] [inst_1 :…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩

@[measurability]
/-
**MeasureTheory.AEFinStronglyMeasurable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f : α → β} {𝕜 : Type u_5} [inst_1 : T
opologicalSpace 𝕜] [inst_2 : Zero β] [inst_3 : SMulZeroClass 𝕜 β]   [ContinuousS
Mul 𝕜 β],   MeasureTheory.AEFinStronglyMeasurable f μ → ∀ (c : 𝕜), MeasureTheory
.AEFinStronglyMeasurable (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → β}   [in
st : TopologicalSpace β] {𝕜 : Type u…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousSMul 𝕜 β] (hf : AEFinStronglyMeasurable f μ) (c : 𝕜) :
    AEFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end Arithmetic

section Order

variable [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.AEFinStronglyMeasurable.sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f g : α → β} [inst_1 : Zero β] [inst_
2 : SemilatticeSup β] [ContinuousSup β],   MeasureTheory.AEFinStronglyMeasurable
 f μ →     MeasureTheory.AEFinStronglyMeasurable g μ → MeasureTheory.AEFinStrong
lyMeasurable (f ⊔ g) μ
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → β}   [inst : 
TopologicalSpace β] [inst_1 :…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.sup`：∀ {α : Type u} {β : Type v} [inst : Max β] {l :
 Filter α} {f f' g g' : α → β},   f =ᶠ[l] f' → g =ᶠ[l] g' → f ⊔ g =ᶠ[l] f' ⊔ g'
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
/-
**MeasureTheory.AEFinStronglyMeasurable.inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f g : α → β} [inst_1 : Zero β] [inst_
2 : SemilatticeInf β] [ContinuousInf β],   MeasureTheory.AEFinStronglyMeasurable
 f μ →     MeasureTheory.AEFinStronglyMeasurable g μ → MeasureTheory.AEFinStrong
lyMeasurable (f ⊓ g) μ
参数：f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.inf`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → β}   [inst : 
TopologicalSpace β] [inst_1 :…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk`：finStron
glyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.
mk f) μ
· 使用定理 `Filter.EventuallyEq.inf`：∀ {α : Type u} {β : Type v} [inst : Min β] {l :
 Filter α} {f f' g g' : α → β},   f =ᶠ[l] f' → g =ᶠ[l] g' → f ⊓ g =ᶠ[l] f' ⊓ g'
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEFinStro
nglyMeasurable f μ) : f =ᵐ[μ] hf.mk f
-/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

variable [Zero β] [T2Space β]

/-
**MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) : exists t, Meas
urableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t)
参数：hf : AEFinStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite`：exists_set_s
igmaFinite [Zero β] [TopologicalSpace β] [T2Space β] (hf : FinStronglyMeasurable
 f μ) : exists t, MeasurableSet t ∧ (forall x in…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine ⟨t, ht, ?_, htμ⟩
  refine EventuallyEq.trans (ae_restrict_of_ae hfg) ?_
  rw [EventuallyEq, ae_restrict_iff' ht.compl]
  exact Eventually.of_forall hgt_zero

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet** 是 Mathlib 中的一个定义，位于命名空间
 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α
参数：hf : AEFinStronglyMeasurable f μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite`：exists_set
_sigmaFinite (hf : AEFinStronglyMeasurable f μ) : exists t, MeasurableSet t ∧ f 
=ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t)
-/
noncomputable def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.choose
/-
**MeasureTheory.AEFinStronglyMeasurable.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace β]   {f : α → β} [inst_1 : Zero β] [inst_2 
: T2Space β] (hf : MeasureTheory.AEFinStronglyMeasurable f μ),   MeasurableSet h
f.sigmaFiniteSet
参数：hf : MeasureTheory.AEFinStronglyMeasurable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite`：exists_set
_sigmaFinite (hf : AEFinStronglyMeasurable f μ) : exists t, MeasurableSet t ∧ f 
=ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem measurableSet (hf : AEFinStronglyMeasurable f μ) :
    MeasurableSet hf.sigmaFiniteSet :=
  hf.exists_set_sigmaFinite.choose_spec.1
/-
**MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ.restrict hf.s
igmaFiniteSetᶜ] 0
参数：hf : AEFinStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite`：exists_set
_sigmaFinite (hf : AEFinStronglyMeasurable f μ) : exists t, MeasurableSet t ∧ f 
=ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) :
    f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0 :=
  hf.exists_set_sigmaFinite.choose_spec.2.1
/-
**MeasureTheory.AEFinStronglyMeasurable.sigmaFinite_restrict** 是 Mathlib 中的一个实例，
位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) : SigmaFinite (μ.r
estrict hf.sigmaFiniteSet)
参数：hf : AEFinStronglyMeasurable f μ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite`：exists_set
_sigmaFinite (hf : AEFinStronglyMeasurable f μ) : exists t, MeasurableSet t ∧ f 
=ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
instance sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) :
    SigmaFinite (μ.restrict hf.sigmaFiniteSet) :=
  hf.exists_set_sigmaFinite.choose_spec.2.2

end AEFinStronglyMeasurable

section SecondCountableTopology

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure,
  `AEFinStronglyMeasurable` and `AEMeasurable` are equivalent. -/
/-
**MeasureTheory.aefinStronglyMeasurable_iff_aemeasurable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：aefinStronglyMeasurable_iff_aemeasurable {_m0 : MeasurableSpace α} (μ : Me
asure α) [SigmaFinite μ] : AEFinStronglyMeasurable f μ ↔ AEMeasurable f μ
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
In a space with second countable topology and a sigma-finite measure,
  `AEFinStronglyMeasurable` and `AEMeasurable` are equivalent.
-/
theorem aefinStronglyMeasurable_iff_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : AEFinStronglyMeasurable f μ ↔ AEMeasurable f μ := by
  simp_rw [AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable]

/-- In a space with second countable topology and a sigma-finite measure,
  an `AEMeasurable` function is `AEFinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
/-
**MeasureTheory.aefinStronglyMeasurable_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：aefinStronglyMeasurable_of_aemeasurable {_m0 : MeasurableSpace α} (μ : Mea
sure α) [SigmaFinite μ] (hf : AEMeasurable f μ) : AEFinStronglyMeasurable f μ
参数：μ : Measure α；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.aefinStronglyMeasurable_iff_aemeasurable`：aefinStronglyMea
surable_iff_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α) [SigmaFinite 
μ] : AEFinStronglyMeasurable f μ ↔ AEMeasura…

--- 原说明 ---
In a space with second countable topology and a sigma-finite measure,
  an `AEMeasurable` function is `AEFinStronglyMeasurable`.
-/
theorem aefinStronglyMeasurable_of_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : AEMeasurable f μ) : AEFinStronglyMeasurable f μ :=
  (aefinStronglyMeasurable_iff_aemeasurable μ).mpr hf

end SecondCountableTopology

end MeasureTheory

