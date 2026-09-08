/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.Order.Filter.EventuallyConst

/-!
# Measure-preserving maps

We say that `f : α → β` is a measure-preserving map w.r.t. measures `μ : Measure α` and
`ν : Measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`MeasureTheory.MeasurePreserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure-preserving map, measure
-/

public section

open MeasureTheory.Measure Function Set
open scoped ENNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace MeasureTheory

variable {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}

/-- `f` is a measure-preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
/-
**MeasureTheory.MeasurePreserving** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
形式化陈述：MeasurePreserving (f : α -> β) (μa : Measure α
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is a measure-preserving map w.r.t. measures `μa` and `μb` if `f` is measurab
le
and `map f μa = μb`.
-/
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by volume_tac) (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected map_eq : map f μa = μb
/-
**MeasureTheory._root_.Measurable.measurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Measurable.measurePreserving
    {f : α → β} (h : Measurable f) (μa : Measure α) : MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩

namespace MeasurePreserving

/-
**MeasureTheory.MeasurePreserving.id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asurePreserving`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α),
 MeasureTheory.MeasurePreserving id μ μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩
/-
**MeasureTheory.MeasurePreserving.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f
 : α → β}, MeasureTheory.MeasurePreserving f μa μb → AEMeasurable f μa
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
-/
protected theorem aemeasurable {f : α → β} (hf : MeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable
/-
**MeasureTheory.MeasurePreserving.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f
 f' : α → β},   MeasureTheory.MeasurePreserving f μa μb → Measurable f' → f =ᵐ[μ
a] f' → MeasureTheory.MeasurePreserving f' μa μb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem congr {f f' : α → β} (hf : MeasurePreserving f μa μb) (hf' : Measurable f')
    (h : f =ᵐ[μa] f') : MeasurePreserving f' μa μb := by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.map_eq

@[nontriviality]
/-
**MeasureTheory.MeasurePreserving.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.MeasurePreserving`。
形式化陈述：of_isEmpty [IsEmpty β] (f : α -> β) (μa : Measure α) (μb : Measure β) : Me
asurePreserving f μa μb
参数：f : α -> β；μa : Measure α；μb : Measure β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_subsingleton_codomain`：measurable_of_subsingleton_codomain
 [Subsingleton β] (f : α -> β) : Measurable f
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem of_isEmpty [IsEmpty β] (f : α → β) (μa : Measure α) (μb : Measure β) :
    MeasurePreserving f μa μb :=
  ⟨measurable_of_subsingleton_codomain _, Subsingleton.elim _ _⟩
/-
**MeasureTheory.MeasurePreserving.symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
MeasurePreserving`。
形式化陈述：symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving
 e μa μb) : MeasurePreserving e.symm μb μa
参数：e : α ≃ᵐ β；h : MeasurePreserving e μa μb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.measurable, by
    rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩
/-
**MeasureTheory.MeasurePreserving.restrict_preimage** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.MeasurePreserving`。
形式化陈述：restrict_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β
} (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restr
ict s)
参数：hf : MeasurePreserving f μa μb；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.restrict_map`：restrict_map {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restric
t <| f ⁻¹' s).map f
-/
theorem restrict_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩
/-
**MeasureTheory.MeasurePreserving.restrict_preimage_emb** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.MeasurePreserving`。
形式化陈述：restrict_preimage_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : 
MeasurableEmbedding f) (s : Set β) : MeasurePreserving f (μa.restrict (f ⁻¹' s))
 (μb.restrict s)
参数：hf : MeasurePreserving f μa μb；h₂ : MeasurableEmbedding f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasurableEmbedding.restrict_map`：restrict_map (μ : Measure α) (s : Set 
β) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f
-/
theorem restrict_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩
/-
**MeasureTheory.MeasurePreserving.restrict_image_emb** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.MeasurePreserving`。
形式化陈述：restrict_image_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : Mea
surableEmbedding f) (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restri
ct (f '' s))
参数：hf : MeasurePreserving f μa μb；h₂ : MeasurableEmbedding f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_preimage_emb`：restrict_preimage
_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) 
(s : Set β) : MeasurePreserving f (μa.restr…
-/
theorem restrict_image_emb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
    (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [Set.preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)
/-
**MeasureTheory.MeasurePreserving.aemeasurable_comp_iff** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.MeasurePreserving`。
形式化陈述：aemeasurable_comp_iff {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : 
MeasurableEmbedding f) {g : β -> γ} : AEMeasurable (g ∘ f) μa ↔ AEMeasurable g μ
b
参数：hf : MeasurePreserving f μa μb；h₂ : MeasurableEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasurableEmbedding.aemeasurable_map_iff`：MeasurableEmbedding.aemeasurab
le_map_iff {g : β -> γ} (hf : MeasurableEmbedding f) : AEMeasurable g (μ.map f) 
↔ AEMeasurable (g ∘ f) μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aemeasurable_comp_iff {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β → γ} : AEMeasurable (g ∘ f) μa ↔ AEMeasurable g μb := by
  rw [← hf.map_eq, h₂.aemeasurable_map_iff]
/-
**MeasureTheory.MeasurePreserving.quasiMeasurePreserving** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f
 : α → β},   MeasureTheory.MeasurePreserving f μa μb → MeasureTheory.Measure.Qua
siMeasurePreserving f μa μb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem quasiMeasurePreserving {f : α → β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.absolutelyContinuous⟩
/-
**MeasureTheory.MeasurePreserving.comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μa : MeasureTheory.
Measure α} {μb : MeasureTheory.Measure β}   {μc : MeasureTheory.Measure γ} {g : 
β → γ} {f : α → β},   MeasureTheory.MeasurePreserving g μb μc →     MeasureTheor
y.MeasurePreserving f μa μb → MeasureTheory.MeasurePreserving (g ∘ f) μa μc
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
    (hf : MeasurePreserving f μa μb) : MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩
/-
**MeasureTheory.MeasurePreserving.map_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μa : MeasureTheory.
Measure α} {μc : MeasureTheory.Measure γ} {f : α → β} {g : β → γ},   MeasureTheo
ry.MeasurePreserving (g ∘ f) μa μc →     Measurable g → Measurable f → MeasureTh
eory.MeasurePreserving g (MeasureTheory.Measure.map f μa) μc
参数：g ∘ f；MeasureTheory.Measure.map f μa。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem map_of_comp {f : α → β} {g : β → γ} (hgf : MeasurePreserving (g ∘ f) μa μc)
    (hg : Measurable g) (hf : Measurable f) :
    MeasurePreserving g (μa.map f) μc :=
  ⟨hg, (map_map hg hf).trans hgf.map_eq⟩
/-
**MeasureTheory.MeasurePreserving.of_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f
 : α → β} {ga : α → α} {gb : β → β},   MeasureTheory.MeasurePreserving f μa μb →
     MeasureTheory.MeasurePreserving ga μa μa →       Function.Semiconj f ga gb 
→ Measurable gb → MeasureTheory.MeasurePreserving gb μb μb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_of_comp`：∀ {α : Type u_1} {β : Type 
u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [i
nst_2 : MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem of_semiconj {f : α → β} {ga : α → α} {gb : β → β}
    (hfm : MeasurePreserving f μa μb) (hga : MeasurePreserving ga μa μa) (hf : Semiconj f ga gb)
    (hgb : Measurable gb) : MeasurePreserving gb μb μb := by
  have := hf.comp_eq ▸ hfm.comp hga |>.map_of_comp hgb hfm.measurable
  rwa [hfm.map_eq] at this

/-- An alias of `MeasureTheory.MeasurePreserving.comp` with a convenient defeq and argument order
for `MeasurableEquiv` -/
/-
**MeasureTheory.MeasurePreserving.trans** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {e : α ≃ᵐ β} {e' : β
 ≃ᵐ γ} {μa : MeasureTheory.Measure α} {μb : MeasureTheory.Measure β}   {μc : Mea
sureTheory.Measure γ},   MeasureTheory.MeasurePreserving (⇑e) μa μb →     Measur
eTheory.MeasurePreserving (⇑e') μb μc → MeasureTheory.MeasurePreserving (⇑(e.tra
ns e')) μa μc
参数：⇑e；⇑e'；⇑(e.trans e')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …

--- 原说明 ---
An alias of `MeasureTheory.MeasurePreserving.comp` with a convenient defeq and a
rgument order
for `MeasurableEquiv`
-/
protected theorem trans {e : α ≃ᵐ β} {e' : β ≃ᵐ γ}
    {μa : Measure α} {μb : Measure β} {μc : Measure γ}
    (h : MeasurePreserving e μa μb) (h' : MeasurePreserving e' μb μc) :
    MeasurePreserving (e.trans e') μa μc :=
  h'.comp h
/-
**MeasureTheory.MeasurePreserving.comp_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μa : MeasureTheory.
Measure α} {μb : MeasureTheory.Measure β}   {μc : MeasureTheory.Measure γ} {g : 
α → β} {e : β ≃ᵐ γ},   MeasureTheory.MeasurePreserving (⇑e) μb μc →     (Measure
Theory.MeasurePreserving (⇑e ∘ g) μa μc ↔ MeasureTheory.MeasurePreserving g μa μ
b)
参数：⇑e；MeasureTheory.MeasurePreserving (⇑e ∘ g) μa μc ↔ MeasureTheory.MeasurePres
erving g μa μb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
-/
protected theorem comp_left_iff {g : α → β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc) :
    MeasurePreserving (e ∘ g) μa μc ↔ MeasurePreserving g μa μb := by
  refine ⟨fun hg => ?_, fun hg => h.comp hg⟩
  convert! (MeasurePreserving.symm e h).comp hg
  simp [← Function.comp_assoc e.symm e g]
/-
**MeasureTheory.MeasurePreserving.comp_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μa : MeasureTheory.
Measure α} {μb : MeasureTheory.Measure β}   {μc : MeasureTheory.Measure γ} {g : 
α → β} {e : γ ≃ᵐ α},   MeasureTheory.MeasurePreserving (⇑e) μc μa →     (Measure
Theory.MeasurePreserving (g ∘ ⇑e) μc μb ↔ MeasureTheory.MeasurePreserving g μa μ
b)
参数：⇑e；MeasureTheory.MeasurePreserving (g ∘ ⇑e) μc μb ↔ MeasureTheory.MeasurePres
erving g μa μb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.self_comp_symm`：self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm
 = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
-/
protected theorem comp_right_iff {g : α → β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa) :
    MeasurePreserving (g ∘ e) μc μb ↔ MeasurePreserving g μa μb := by
  refine ⟨fun hg => ?_, fun hg => hg.comp h⟩
  convert! hg.comp (MeasurePreserving.symm e h)
  simp [Function.comp_assoc g e e.symm]
/-
**MeasureTheory.MeasurePreserving.sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f
 : α → β},   MeasureTheory.MeasurePreserving f μa μb → ∀ [MeasureTheory.SigmaFin
ite μb], MeasureTheory.SigmaFinite μa
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFinite.of_map`：∀ {α : Type u_1} {β : Type u_2} {m0 : 
MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α)   {f
 : α → β},   AEMeasura…
· 使用定理 `MeasureTheory.MeasurePreserving.aemeasurable`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : MeasureTheor
y.Measure α}   {μb : MeasureTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem sigmaFinite {f : α → β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] :
    SigmaFinite μa :=
  SigmaFinite.of_map μa hf.aemeasurable (by rwa [hf.map_eq])
/-
**MeasureTheory.MeasurePreserving.sfinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f
 : α → β},   MeasureTheory.MeasurePreserving f μa μb → ∀ [MeasureTheory.SFinite 
μa], MeasureTheory.SFinite μb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
-/
protected theorem sfinite {f : α → β} (hf : MeasurePreserving f μa μb) [SFinite μa] :
    SFinite μb := by
  rw [← hf.map_eq]
  infer_instance
/-
**MeasureTheory.MeasurePreserving.measure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.MeasurePreserving`。
形式化陈述：measure_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
 (hs : NullMeasurableSet s μb) : μa (f ⁻¹' s) = μb s
参数：hf : MeasurePreserving f μa μb；hs : NullMeasurableSet s μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用引理 `MeasureTheory.Measure.map_apply₀`：map_apply₀ {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹
' s)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
-/
theorem measure_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq] at hs ⊢
  rw [map_apply₀ hf.1.aemeasurable hs]
/-
**MeasureTheory.MeasurePreserving.measureReal_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.MeasurePreserving`。
形式化陈述：measureReal_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Se
t β} (hs : NullMeasurableSet s μb) : μa.real (f ⁻¹' s) = μb.real s
参数：hf : MeasurePreserving f μa μb；hs : NullMeasurableSet s μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) : μa.real (f ⁻¹' s) = μb.real s := by
  simp [measureReal_def, measure_preimage hf hs]
/-
**MeasureTheory.MeasurePreserving.measure_preimage_emb** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.MeasurePreserving`。
形式化陈述：measure_preimage_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (hfe : 
MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s
参数：hf : MeasurePreserving f μa μb；hfe : MeasurableEmbedding f；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
-/
theorem measure_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (hfe : MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, hfe.map_apply]
/-
**MeasureTheory.MeasurePreserving.measure_preimage_equiv** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：measure_preimage_equiv {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : 
Set β) : μa (f ⁻¹' s) = μb s
参数：hf : MeasurePreserving f μa μb；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage_emb`：measure_preimage_e
mb {f : α -> β} (hf : MeasurePreserving f μa μb) (hfe : MeasurableEmbedding f) (
s : Set β) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem measure_preimage_equiv {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set β) :
    μa (f ⁻¹' s) = μb s :=
  measure_preimage_emb hf f.measurableEmbedding s
/-
**MeasureTheory.MeasurePreserving.measure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.MeasurePreserving`。
形式化陈述：measure_preimage_le {f : α -> β} (hf : MeasurePreserving f μa μb) (s : Set
 β) : μa (f ⁻¹' s) <= μb s
参数：hf : MeasurePreserving f μa μb；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.le_map_apply`：le_map_apply {f : α -> β} (hf : AEMe
asurable f μ) (s : Set β) : μ (f ⁻¹' s) <= μ.map f s
· 使用定理 `MeasureTheory.MeasurePreserving.aemeasurable`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : MeasureTheor
y.Measure α}   {μb : MeasureTheory…
-/
theorem measure_preimage_le {f : α → β} (hf : MeasurePreserving f μa μb) (s : Set β) :
    μa (f ⁻¹' s) ≤ μb s := by
  rw [← hf.map_eq]
  exact le_map_apply hf.aemeasurable _
/-
**MeasureTheory.MeasurePreserving.preimage_null** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.MeasurePreserving`。
形式化陈述：preimage_null {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (h
s : μb s = 0) : μa (f ⁻¹' s) = 0
参数：hf : MeasurePreserving f μa μb；hs : μb s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null`：preimage_nul
l (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s
) = 0
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem preimage_null {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : μb s = 0) : μa (f ⁻¹' s) = 0 :=
  hf.quasiMeasurePreserving.preimage_null hs
/-
**MeasureTheory.MeasurePreserving.aeconst_comp** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MeasurePreserving`。
形式化陈述：aeconst_comp [MeasurableSingletonClass γ] {f : α -> β} (hf : MeasurePreser
ving f μa μb) {g : β -> γ} (hg : NullMeasurable g μb) : Filter.EventuallyConst (
g ∘ f) (ae μa) ↔ Filter.EventuallyConst g (ae μb)
参数：hf : MeasurePreserving f μa μb；hg : NullMeasurable g μb。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `Set.Subsingleton.measurableSet`：Set.Subsingleton.measurableSet {s : Set 
α} (hs : s.Subsingleton) : MeasurableSet s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem aeconst_comp [MeasurableSingletonClass γ] {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : β → γ} (hg : NullMeasurable g μb) :
    Filter.EventuallyConst (g ∘ f) (ae μa) ↔ Filter.EventuallyConst g (ae μb) :=
  exists_congr fun s ↦ and_congr_left fun hs ↦ by
    simp only [Filter.mem_map, mem_ae_iff, ← hf.measure_preimage (hg hs.measurableSet).compl,
      preimage_comp, preimage_compl]
/-
**MeasureTheory.MeasurePreserving.aeconst_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.MeasurePreserving`。
形式化陈述：aeconst_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
 (hs : NullMeasurableSet s μb) : Filter.EventuallyConst (f ⁻¹' s) (ae μa) ↔ Filt
er.EventuallyConst s (ae μb)
参数：hf : MeasurePreserving f μa μb；hs : NullMeasurableSet s μb。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.aeconst_comp`：aeconst_comp [MeasurableSi
ngletonClass γ] {f : α -> β} (hf : MeasurePreserving f μa μb) {g : β -> γ} (hg :
 NullMeasurable g μb) : Filter.Eve…
· 使用定理 `MeasurableSet.mem`：∀ {α : Type u_1} {s : Set α} [inst : MeasurableSpace 
α], MeasurableSet s → Measurable fun x => x ∈ s
-/
theorem aeconst_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) :
    Filter.EventuallyConst (f ⁻¹' s) (ae μa) ↔ Filter.EventuallyConst s (ae μb) :=
  aeconst_comp hf hs.mem
/-
**MeasureTheory.MeasurePreserving.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.MeasurePreserving`。
形式化陈述：add_measure {f μa' μb'} (hf : MeasurePreserving f μa μb) (hf' : MeasurePre
serving f μa' μb') : MeasurePreserving f (μa + μa') (μb + μb') where measurable
参数：hf : MeasurePreserving f μa μb；hf' : MeasurePreserving f μa' μb'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_add`：∀ {α : Type u_1} {β : Type u_2} {mα : Mea
surableSpace α} {mβ : MeasurableSpace β} (μ ν : MeasureTheory.Measure α)   {f : 
α → β},   Measurabl…
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
theorem add_measure {f μa' μb'} (hf : MeasurePreserving f μa μb)
    (hf' : MeasurePreserving f μa' μb') : MeasurePreserving f (μa + μa') (μb + μb') where
  measurable := hf.measurable
  map_eq := by rw [Measure.map_add _ _ hf.measurable, hf.map_eq, hf'.map_eq]
/-
**MeasureTheory.MeasurePreserving.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MeasurePreserving`。
形式化陈述：smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>
=0∞] {f : α -> β} (hf : MeasurePreserving f μa μb) (c : R) : MeasurePreserving f
 (c • μa) (c • μb) where measurable
参数：hf : MeasurePreserving f μa μb；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] {f : α → β}
    (hf : MeasurePreserving f μa μb) (c : R) : MeasurePreserving f (c • μa) (c • μb) where
  measurable := hf.measurable
  map_eq := by rw [Measure.map_smul, hf.map_eq]

variable {μ : Measure α} {f : α → α} {s : Set α}
/-
**MeasureTheory.MeasurePreserving.iterate** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
{f : α → α},   MeasureTheory.MeasurePreserving f μ μ → ∀ (n : ℕ), MeasureTheory.
MeasurePreserving f^[n] μ μ
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem iterate (hf : MeasurePreserving f μ μ) :
    ∀ n, MeasurePreserving f^[n] μ μ
  | 0 => .id μ
  | n + 1 => (MeasurePreserving.iterate hf n).comp hf

open scoped symmDiff in
/-
**MeasureTheory.MeasurePreserving.measure_symmDiff_preimage_iterate_le** 是 Mathl
ib 中的一个引理，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：measure_symmDiff_preimage_iterate_le (hf : MeasurePreserving f μ μ) (hs : 
NullMeasurableSet s μ) (n : Nat) : μ (s ∆ (f^[n] ⁻¹' s)) <= n • μ (s ∆ (f ⁻¹' s)
)
参数：hf : MeasurePreserving f μ μ；hs : NullMeasurableSet s μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `MeasureTheory.measure_symmDiff_le`：measure_symmDiff_le (s t u : Set α) :
 μ (s ∆ u) <= μ (s ∆ t) + μ (t ∆ u)
· 使用定理 `MeasureTheory.NullMeasurableSet.symmDiff`：∀ {α : Type u_2} {m0 : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {s₁ s₂ : Set α},   MeasureTheory.NullM
easurableSet s₁ μ →     Measur…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.preimage_symmDiff`：preimage_symmDiff {f : α -> β} (s t : Set β) : f 
⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t)
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasureTheory.MeasurePreserving.iterate`：∀ {α : Type u_1} [inst : Measur
ableSpace α] {μ : MeasureTheory.Measure α} {f : α → α},   MeasureTheory.MeasureP
reserving f μ μ → ∀ (n : ℕ), …
-/
lemma measure_symmDiff_preimage_iterate_le
    (hf : MeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) (n : ℕ) :
    μ (s ∆ (f^[n] ⁻¹' s)) ≤ n • μ (s ∆ (f ⁻¹' s)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul]
    grw [← ih, measure_symmDiff_le s (f^[n] ⁻¹' s) (f^[n + 1] ⁻¹' s)]
    replace hs : NullMeasurableSet (s ∆ (f ⁻¹' s)) μ :=
      hs.symmDiff <| hs.preimage hf.quasiMeasurePreserving
    rw [iterate_succ', preimage_comp, ← preimage_symmDiff, (hf.iterate n).measure_preimage hs]

/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
/-
**MeasureTheory.MeasurePreserving.exists_mem_iterate_mem_of_measure_univ_lt_mul_
measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：exists_mem_iterate_mem_of_measure_univ_lt_mul_measure (hf : MeasurePreserv
ing f μ μ) (hs : NullMeasurableSet s μ) {n : Nat} (hvol : μ (Set.univ : Set α) <
 n * μ s) : exists x in s, exists m in Set.Ioo 0 n, f^[m] x in s
参数：hf : MeasurePreserving f μ μ；hs : NullMeasurableSet s μ；hvol : μ (Set.univ : 
Set α) < n * μ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.MeasurePreserving.iterate`：∀ {α : Type u_1} [inst : Measur
ableSpace α] {μ : MeasureTheory.Measure α} {f : α → α},   MeasureTheory.MeasureP
reserving f μ μ → ∀ (n : ℕ), …
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`：exis
ts_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Me
asure α) {s : Finset ι} {t : ι -> Set α} (h : forall i i…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`.
-/
theorem exists_mem_iterate_mem_of_measure_univ_lt_mul_measure (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) {n : ℕ} (hvol : μ (Set.univ : Set α) < n * μ s) :
    ∃ x ∈ s, ∃ m ∈ Set.Ioo 0 n, f^[m] x ∈ s := by
  have A : ∀ m, NullMeasurableSet (f^[m] ⁻¹' s) μ := fun m ↦
    hs.preimage (hf.iterate m).quasiMeasurePreserving
  have B : ∀ m, μ (f^[m] ⁻¹' s) = μ s := fun m ↦ (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < ∑ m ∈ Finset.range n, μ (f^[m] ⁻¹' s) := by simpa [B]
  obtain ⟨i, hi, j, hj, hij, x, hxi : f^[i] x ∈ s, hxj : f^[j] x ∈ s⟩ :
      ∃ i < n, ∃ j < n, i ≠ j ∧ (f^[i] ⁻¹' s ∩ f^[j] ⁻¹' s).Nonempty := by
    simpa using exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (fun m _ ↦ A m) this
  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hxj hxi (hij.lt_or_gt.resolve_left hlt)
  refine ⟨f^[i] x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, ?_⟩
  rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]

/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `MeasureTheory.MeasurePreserving.conservative` and theorems about
`MeasureTheory.Conservative`. -/
/-
**MeasureTheory.MeasurePreserving.exists_mem_iterate_mem** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：exists_mem_iterate_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ) 
(hs : NullMeasurableSet s μ) (hs' : μ s != 0) : exists x in s, exists m != 0, f^
[m] x in s
参数：hf : MeasurePreserving f μ μ；hs : NullMeasurableSet s μ；hs' : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_nat_mul_gt`：exists_nat_mul_gt (ha : a != 0) (hb : b != ∞)
 : exists n : Nat, b < n * a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.MeasurePreserving.exists_mem_iterate_mem_of_measure_univ_l
t_mul_measure`：exists_mem_iterate_mem_of_measure_univ_lt_mul_measure (hf : Measu
rePreserving f μ μ) (hs : NullMeasurableSet s μ) {n : Nat} (hvol : μ (Set.u…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at le
ast one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` c
omes back to `s`
infinitely many times, see `MeasureTheory.MeasurePreserving.conservative` and th
eorems about
`MeasureTheory.Conservative`.
-/
theorem exists_mem_iterate_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : μ s ≠ 0) : ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s := by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (Set.univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩

end MeasurePreserving

/-
**MeasureTheory.measurePreserving_subtype_coe** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：measurePreserving_subtype_coe {s : Set α} (hs : MeasurableSet s) : Measure
Preserving (Subtype.val : s -> α) (μa.comap Subtype.val) (μa.restrict s) where m
easurable
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
-/
lemma measurePreserving_subtype_coe {s : Set α} (hs : MeasurableSet s) :
    MeasurePreserving (Subtype.val : s → α) (μa.comap Subtype.val) (μa.restrict s) where
  measurable := measurable_subtype_coe
  map_eq := map_comap_subtype_coe hs _

namespace MeasurableEquiv

/-
**MeasureTheory.MeasurableEquiv.measurePreserving_symm** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.MeasurableEquiv`。
形式化陈述：measurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) : MeasurePreserving e.
symm (map e μ) μ
参数：μ : Measure α；e : α ≃ᵐ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Measurable.measurePreserving`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measurable f → ∀ (μ
a : MeasureTheory.…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
-/
theorem measurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    MeasurePreserving e.symm (map e μ) μ :=
  (e.measurable.measurePreserving μ).symm _

end MeasurableEquiv

end MeasureTheory

