/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.WithTop

/-!
# Borel measurable space on `WithTop`

For `ι` a linear order with the order topology, we define the Borel measurable space on `WithTop ι`.
We then prove that the natural inclusion `ι → WithTop ι` is measurable, and that the function
`WithTop.untopA : WithTop ι → ι` (which sends `⊤` to an arbitrary element of `ι`) is measurable.

## Main statements

* `measurable_of_measurable_comp_coe`: if `f : WithTop ι → α` is such that `f ∘ coe` is measurable,
  then `f` is measurable.
* `Measurable.withTop_coe`: the function `fun x : ι ↦ (x : WithTop ι)` is measurable.
* `Measurable.untopD`: for `d : ι`, the function `WithTop.untopD d : WithTop ι → ι` is measurable.
* `Measurable.untopA`: the function `WithTop.untopA : WithTop ι → ι` is measurable.

-/

@[expose] public section


namespace WithTop

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MeasurableSpace (WithTop ι) := borel _
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BorelSpace (WithTop ι) := ⟨rfl⟩

variable [MeasurableSpace ι] [BorelSpace ι]

/-- Measurable equivalence between the non-top elements of `WithTop ι` and `ι`. -/
noncomputable
/-
**WithTop.MeasurableEquiv.neTopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithTop.Measurab
leEquiv`。
形式化陈述：{ι : Type u_1} →   [inst : LinearOrder ι] →     [inst_1 : TopologicalSpace
 ι] →       [inst_2 : OrderTopology ι] → [inst_3 : MeasurableSpace ι] → [BorelSp
ace ι] → ↑{r | r ≠ ⊤} ≃ᵐ ι
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MeasurableEquiv.neTopEquiv : { r : WithTop ι | r ≠ ⊤ } ≃ᵐ ι :=
  (WithTop.neTopHomeomorph ι).toMeasurableEquiv
/-
**WithTop.measurable_of_measurable_comp_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：measurable_of_measurable_comp_coe {α : Type*} {mα : MeasurableSpace α} {f 
: WithTop ι -> α} (h : Measurable fun p : ι => f p) : Measurable f
参数：h : Measurable fun p : ι => f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_measurable_on_compl_singleton`：measurable_of_measurable_on
_compl_singleton [MeasurableSingletonClass α] {f : α -> β} (a : α) (hf : Measura
ble ({ x | x != a }.domRestrict f…
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasurableEquiv.measurable_comp_iff`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {f : β…
-/
lemma measurable_of_measurable_comp_coe {α : Type*} {mα : MeasurableSpace α}
    {f : WithTop ι → α} (h : Measurable fun p : ι ↦ f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_singleton ⊤
    (MeasurableEquiv.neTopEquiv.symm.measurable_comp_iff.1 h)
/-
**WithTop.measurable_untopD** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：measurable_untopD (d : ι) : Measurable (untopD d)
参数：d : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.measurable_of_measurable_comp_coe`：measurable_of_measurable_comp
_coe {α : Type*} {mα : MeasurableSpace α} {f : WithTop ι -> α} (h : Measurable f
un p : ι => f p) : Measurable f
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma measurable_untopD (d : ι) : Measurable (untopD d) :=
  measurable_of_measurable_comp_coe measurable_id
/-
**WithTop.measurable_untopA** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：measurable_untopA [Nonempty ι] : Measurable (WithTop.untopA (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.measurable_untopD`：measurable_untopD (d : ι) : Measurable (untop
D d)
-/
lemma measurable_untopA [Nonempty ι] : Measurable (WithTop.untopA (α := ι)) :=
  measurable_untopD _
/-
**WithTop.measurable_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：measurable_coe : Measurable (fun x : ι => (x : WithTop ι))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用引理 `WithTop.continuous_coe`：continuous_coe : Continuous ((↑) : ι -> WithTop 
ι)
-/
lemma measurable_coe : Measurable (fun x : ι ↦ (x : WithTop ι)) := continuous_coe.measurable

@[fun_prop]
/-
**WithTop._root_.Measurable.withTop_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Measurable.withTop_coe {α} {mα : MeasurableSpace α} {f : α → ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x : WithTop ι)) :=
  measurable_coe.comp hf

@[fun_prop]
/-
**WithTop._root_.Measurable.untopD** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Measurable.untopD {α} {mα : MeasurableSpace α} (d : ι)
    {f : α → WithTop ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x).untopD d) := (measurable_untopD d).comp hf

@[fun_prop]
/-
**WithTop._root_.Measurable.untopA** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Measurable.untopA {α} {mα : MeasurableSpace α} [Nonempty ι]
    {f : α → WithTop ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x).untopA) := hf.untopD _

/-- Measurable equivalence between `WithTop ι` and `ι ⊕ Unit`. -/
/-
**WithTop.measurableEquivSum** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：measurableEquivSum : WithTop ι ≃ᵐ ι oplus Unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measurable equivalence between `WithTop ι` and `ι ⊕ Unit`.
-/
def measurableEquivSum : WithTop ι ≃ᵐ ι ⊕ Unit :=
  { Equiv.optionEquivSumPUnit ι with
    measurable_toFun := measurable_of_measurable_comp_coe measurable_inl
    measurable_invFun := measurable_fun_sum measurable_coe (@measurable_const _ Unit _ _ ⊤) }

end WithTop

