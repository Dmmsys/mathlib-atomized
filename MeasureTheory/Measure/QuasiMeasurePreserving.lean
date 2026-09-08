/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Quasi-Measure-Preserving Functions

A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`.
That last condition can also be written `μa.map f ≪ μb` (the map of `μa` by `f` is
absolutely continuous with respect to `μb`).

## Main definitions

* `MeasureTheory.Measure.QuasiMeasurePreserving f μa μb`: `f` is quasi-measure-preserving with
  respect to `μa` and `μb`.

-/

public section

variable {α β γ δ : Type*}

namespace MeasureTheory

open Set Function ENNReal
open Filter hiding map

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

/-- A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
@[fun_prop]
/-
**MeasureTheory.Measure.QuasiMeasurePreserving** 是 Mathlib 中的一个结构，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α -> β) (μa : Measure
 α
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular)
 w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`.
-/
structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α → β)
  (μa : Measure α := by volume_tac)
  (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected absolutelyContinuous : μa.map f ≪ μb

attribute [fun_prop] QuasiMeasurePreserving.measurable

namespace QuasiMeasurePreserving

@[fun_prop]
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.id** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {_m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α), 
  MeasureTheory.Measure.QuasiMeasurePreserving id μ μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
protected theorem id {_m0 : MeasurableSpace α} (μ : Measure α) : QuasiMeasurePreserving id μ μ :=
  ⟨measurable_id, map_id.absolutelyContinuous⟩

variable {μa μa' : Measure α} {μb μb' : Measure β} {μc : Measure γ} {f : α → β}
/-
**MeasureTheory.Measure.QuasiMeasurePreserving._root_.Measurable.quasiMeasurePre
serving** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Measurable.quasiMeasurePreserving
    {_m0 : MeasurableSpace α} (hf : Measurable f) (μ : Measure α) :
    QuasiMeasurePreserving f μ (μ.map f) :=
  ⟨hf, AbsolutelyContinuous.rfl⟩
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.mono_left** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：mono_left (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) : QuasiMeas
urePreserving f μa' μb
参数：h : QuasiMeasurePreserving f μa μb；ha : μa' ≪ μa。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem mono_left (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) :
    QuasiMeasurePreserving f μa' μb :=
  ⟨h.1, (ha.map h.1).trans h.2⟩
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.mono_right** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：mono_right (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') : QuasiMea
surePreserving f μa μb'
参数：h : QuasiMeasurePreserving f μa μb；ha : μb ≪ μb'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem mono_right (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') :
    QuasiMeasurePreserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩

@[gcongr, mono]
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.mono** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) 
: QuasiMeasurePreserving f μa' μb'
参数：ha : μa' ≪ μa；hb : μb ≪ μb'；h : QuasiMeasurePreserving f μa μb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono_right`：mono_right (h :
 QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') : QuasiMeasurePreserving f μa μ
b'
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono_left`：mono_left (h : Q
uasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) : QuasiMeasurePreserving f μa' μb
-/
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa' μb' :=
  (h.mono_left ha).mono_right hb

@[fun_prop]
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.comp** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} {μa : MeasureTheory.Measure α}
 {μb : MeasureTheory.Measure β} {μc : MeasureTheory.Measure γ}   {g : β → γ} {f 
: α → β},   MeasureTheory.Measure.QuasiMeasurePreserving g μb μc →     MeasureTh
eory.Measure.QuasiMeasurePreserving f μa μb → MeasureTheory.Measure.QuasiMeasure
Preserving (g ∘ f) μa μc
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
    (hf : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.iterate** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {
f : α → α},   MeasureTheory.Measure.QuasiMeasurePreserving f μa μa →     ∀ (n : 
ℕ), MeasureTheory.Measure.QuasiMeasurePreserving f^[n] μa μa
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem iterate {f : α → α} (hf : QuasiMeasurePreserving f μa μa) :
    ∀ n, QuasiMeasurePreserving f^[n] μa μa
  | 0 => QuasiMeasurePreserving.id μa
  | n + 1 => (hf.iterate n).comp hf
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f : α →
 β}, MeasureTheory.Measure.QuasiMeasurePreserving f μa μb → AEMeasurable f μa
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
-/
protected theorem aemeasurable (hf : QuasiMeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.congr** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Measure β} {f : α →
 β},   MeasureTheory.Measure.QuasiMeasurePreserving f μa μb →     ∀ {f' : α → β}
, Measurable f' → f =ᵐ[μa] f' → MeasureTheory.Measure.QuasiMeasurePreserving f' 
μa μb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
protected theorem congr (hf : QuasiMeasurePreserving f μa μb) {f' : α → β} (hf' : Measurable f')
    (h : f =ᵐ[μa] f') : QuasiMeasurePreserving f' μa μb := by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.absolutelyContinuous
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.smul_measure** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>
=0∞] (hf : QuasiMeasurePreserving f μa μb) (c : R) : QuasiMeasurePreserving f (c
 • μa) (c • μb)
参数：hf : QuasiMeasurePreserving f μa μb；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul`：∀ {α : Type u_1} {R : T
ype u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : SMul R
 ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : QuasiMeasurePreserving f μa μb) (c : R) : QuasiMeasurePreserving f (c • μa) (c • μb) :=
  ⟨hf.1, by rw [Measure.map_smul]; exact hf.2.smul c⟩
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.ae_map_le** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：ae_map_le (h : QuasiMeasurePreserving f μa μb) : ae (μa.map f) <= ae μb
参数：h : QuasiMeasurePreserving f μa μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem ae_map_le (h : QuasiMeasurePreserving f μa μb) : ae (μa.map f) ≤ ae μb :=
  h.2.ae_le
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.tendsto_ae** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb
)
参数：h : QuasiMeasurePreserving f μa μb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.tendsto_ae_map`：tendsto_ae_map {f : α -> β} (hf : 
AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f))
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : Measu
reTheory.Measure α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae_map_le`：ae_map_le (h : Q
uasiMeasurePreserving f μa μb) : ae (μa.map f) <= ae μb
-/
theorem tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb) :=
  (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.ae** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：ae (h : QuasiMeasurePreserving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μ
b, p x) : forallᵐ x ∂μa, p (f x)
参数：h : QuasiMeasurePreserving f μa μb；hg : forallᵐ x ∂μb, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.tendsto_ae`：tendsto_ae (h :
 QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb)
-/
theorem ae (h : QuasiMeasurePreserving f μa μb) {p : β → Prop} (hg : ∀ᵐ x ∂μb, p x) :
    ∀ᵐ x ∂μa, p (f x) :=
  h.tendsto_ae hg

@[gcongr]
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：ae_eq (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β -> δ} (hg : g₁ =ᵐ[μb
] g₂) : g₁ ∘ f =ᵐ[μa] g₂ ∘ f
参数：h : QuasiMeasurePreserving f μa μb；hg : g₁ =ᵐ[μb] g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae`：ae (h : QuasiMeasurePre
serving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μb, p x) : forallᵐ x ∂μa, p (f
 x)
-/
theorem ae_eq (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) :
    g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
  h.ae hg
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：preimage_null (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s 
= 0) : μa (f ⁻¹' s) = 0
参数：h : QuasiMeasurePreserving f μa μb；hs : μb s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.preimage_null_of_map_null`：preimage_null_of_map_nu
ll {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs : μ.map f s = 0) : μ (f 
⁻¹' s) = 0
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : Measu
reTheory.Measure α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem preimage_null (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) :
    μa (f ⁻¹' s) = 0 :=
  preimage_null_of_map_null h.aemeasurable (h.2 hs)
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.preimage_mono_ae** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : 
s <=ᵐ[μb] t) : f ⁻¹' s <=ᵐ[μa] f ⁻¹' t
参数：hf : QuasiMeasurePreserving f μa μb；h : s <=ᵐ[μb] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.Measure.tendsto_ae_map`：tendsto_ae_map {f : α -> β} (hf : 
AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f))
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : Measu
reTheory.Measure α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae_map_le`：ae_map_le (h : Q
uasiMeasurePreserving f μa μb) : ae (μa.map f) <= ae μb
-/
theorem preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s ≤ᵐ[μb] t) :
    f ⁻¹' s ≤ᵐ[μa] f ⁻¹' t :=
  eventually_map.mp <|
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s 
=ᵐ[μb] t) : f ⁻¹' s =ᵐ[μa] f ⁻¹' t
参数：hf : QuasiMeasurePreserving f μa μb；h : s =ᵐ[μb] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_mono_ae`：preimage_
mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s <=ᵐ[μb] t) : 
f ⁻¹' s <=ᵐ[μa] f ⁻¹' t
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) :
    f ⁻¹' s =ᵐ[μa] f ⁻¹' t :=
  EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)

/-- The preimage of a null measurable set under a (quasi-)measure-preserving map is a null
measurable set. -/
/-
**MeasureTheory.Measure.QuasiMeasurePreserving._root_.MeasureTheory.NullMeasurab
leSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePres
erving`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a null measurable set under a (quasi-)measure-preserving map is 
a null
measurable set.
-/
theorem _root_.MeasureTheory.NullMeasurableSet.preimage {s : Set β} (hs : NullMeasurableSet s μb)
    (hf : QuasiMeasurePreserving f μa μb) : NullMeasurableSet (f ⁻¹' s) μa :=
  let ⟨t, htm, hst⟩ := hs
  ⟨f ⁻¹' t, hf.measurable htm, hf.preimage_ae_eq hst⟩
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：preimage_iterate_ae_eq {s : Set α} {f : α -> α} (hf : QuasiMeasurePreservi
ng f μ μ) (k : Nat) (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s
参数：hf : QuasiMeasurePreserving f μ μ；k : Nat；hs : f ⁻¹' s =ᵐ[μ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq`：preimage_ae
_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) : f ⁻¹'
 s =ᵐ[μa] f ⁻¹' t
-/
theorem preimage_iterate_ae_eq {s : Set α} {f : α → α} (hf : QuasiMeasurePreserving f μ μ) (k : ℕ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ, preimage_comp]
    exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.image_zpow_ae_eq** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ 
μ) (he' : QuasiMeasurePreserving e.symm μ μ) (k : Int) (hs : e '' s =ᵐ[μ] s) : (
⇑(e ^ k)) '' s =ᵐ[μ] s
参数：he : QuasiMeasurePreserving e μ μ；he' : QuasiMeasurePreserving e.symm μ μ；k :
 Int；hs : e '' s =ᵐ[μ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq`：pre
image_iterate_ae_eq {s : Set α} {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
 (k : Nat) (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用引理 `Equiv.Perm.iterate_eq_pow`：iterate_eq_pow (f : Perm α) (n : Nat) : f^[n]
 = ⇑(f ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq`：preimage_ae
_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) : f ⁻¹'
 s =ᵐ[μa] f ⁻¹' t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
    (he' : QuasiMeasurePreserving e.symm μ μ) (k : ℤ) (hs : e '' s =ᵐ[μ] s) :
    (⇑(e ^ k)) '' s =ᵐ[μ] s := by
  rw [Equiv.image_eq_preimage_symm]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage_symm] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert! he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he

-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/issues/10941
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.limsup_preimage_iterate_ae_eq** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：limsup_preimage_iterate_ae_eq {f : α -> α} (hf : QuasiMeasurePreserving f 
μ μ) (hs : f ⁻¹' s =ᵐ[μ] s) : limsup (α
参数：hf : QuasiMeasurePreserving f μ μ；hs : f ⁻¹' s =ᵐ[μ] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.limsup_ae_eq_of_forall_ae_eq`：limsup_ae_eq_of_forall_ae_eq
 (s : Nat -> Set α) {t : Set α} (h : forall n, s n =ᵐ[μ] t) : limsup (α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.preimage_iterate_eq`：preimage_iterate_eq {f : α -> α} {n : Nat} : Se
t.preimage f^[n] = (Set.preimage f)^[n]
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq`：pre
image_iterate_ae_eq {s : Set α} {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
 (k : Nat) (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s
-/
theorem limsup_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : limsup (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n ↦ by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/issues/10941
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.liminf_preimage_iterate_ae_eq** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：liminf_preimage_iterate_ae_eq {f : α -> α} (hf : QuasiMeasurePreserving f 
μ μ) (hs : f ⁻¹' s =ᵐ[μ] s) : liminf (α
参数：hf : QuasiMeasurePreserving f μ μ；hs : f ⁻¹' s =ᵐ[μ] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.liminf_ae_eq_of_forall_ae_eq`：liminf_ae_eq_of_forall_ae_eq
 (s : Nat -> Set α) {t : Set α} (h : forall n, s n =ᵐ[μ] t) : liminf (α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.preimage_iterate_eq`：preimage_iterate_eq {f : α -> α} {n : Nat} : Se
t.preimage f^[n] = (Set.preimage f)^[n]
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq`：pre
image_iterate_ae_eq {s : Set α} {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
 (k : Nat) (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s
-/
theorem liminf_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : liminf (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  liminf_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n ↦ by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

/-- For a quasi-measure-preserving self-map `f`, if a null measurable set `s` is a.e. invariant,
then it is a.e. equal to a measurable invariant set.
-/
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：exists_preimage_eq_of_preimage_ae {f : α -> α} (h : QuasiMeasurePreserving
 f μ μ) (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s =ᵐ[μ] s) : exists t : Set α,
 MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t
参数：h : QuasiMeasurePreserving f μ μ；hs : NullMeasurableSet s μ；hs' : f ⁻¹' s =ᵐ[
μ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSet.measurableSet_limsup`：measurableSet_limsup {s : Nat -> Set
 α} (hs : forall n, MeasurableSet <| s n) : MeasurableSet Filter.limsup s Filter
.atTop
· 使用定理 `Measurable.iterate`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → α}
, Measurable f → ∀ (n : ℕ), Measurable f^[n]
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq`：preimage_ae
_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) : f ⁻¹'
 s =ᵐ[μa] f ⁻¹' t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.limsup_ae_eq_of_forall_ae_eq`：limsup_ae_eq_of_forall_ae_eq
 (s : Nat -> Set α) {t : Set α} (h : forall n, s n =ᵐ[μ] t) : limsup (α
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq`：pre
image_iterate_ae_eq {s : Set α} {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
 (k : Nat) (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.preimage_iterate_eq`：preimage_iterate_eq {f : α -> α} {n : Nat} : Se
t.preimage f^[n] = (Set.preimage f)^[n]
· 使用定理 `CompleteLatticeHom.apply_limsup_iterate`：∀ {α : Type u_1} [inst : Comple
teLattice α] (f : CompleteLatticeHom α α) (a : α),   f (Filter.limsup (fun n => 
(⇑f)^[n] a) Filter.atTop) = F…

--- 原说明 ---
For a quasi-measure-preserving self-map `f`, if a null measurable set `s` is a.e
. invariant,
then it is a.e. equal to a measurable invariant set.
-/
theorem exists_preimage_eq_of_preimage_ae {f : α → α} (h : QuasiMeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set α, MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t := by
  obtain ⟨t, htm, ht⟩ := hs
  refine ⟨limsup (f^[·] ⁻¹' t) atTop, ?_, ?_, ?_⟩
  · exact .measurableSet_limsup fun n ↦ h.measurable.iterate n htm
  · have : f ⁻¹' t =ᵐ[μ] t := (h.preimage_ae_eq ht.symm).trans (hs'.trans ht)
    exact limsup_ae_eq_of_forall_ae_eq _ fun n ↦ .trans (h.preimage_iterate_ae_eq _ this) ht.symm
  · simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) t

open scoped Pointwise

@[to_additive]
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：smul_ae_eq_of_ae_eq {G α : Type*} [Group G] [MulAction G α] {_ : Measurabl
eSpace α} {s t : Set α} {μ : Measure α} (g : G) (h_qmp : QuasiMeasurePreserving 
(g⁻¹ • · : α -> α) μ μ) (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : S
et α)
参数：g : G；h_qmp : QuasiMeasurePreserving (g⁻¹ • · : α -> α) μ μ；h_ae_eq : s =ᵐ[μ]
 t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq`：ae_eq (h : QuasiMeas
urePreserving f μa μb) {g₁ g₂ : β -> δ} (hg : g₁ =ᵐ[μb] g₂) : g₁ ∘ f =ᵐ[μa] g₂ ∘
 f
-/
theorem smul_ae_eq_of_ae_eq {G α : Type*} [Group G] [MulAction G α] {_ : MeasurableSpace α}
    {s t : Set α} {μ : Measure α} (g : G)
    (h_qmp : QuasiMeasurePreserving (g⁻¹ • · : α → α) μ μ)
    (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : Set α) := by
  simpa only [← preimage_smul_inv] using! h_qmp.ae_eq h_ae_eq

end QuasiMeasurePreserving

section Pointwise

open scoped Pointwise

@[to_additive]
/-
**MeasureTheory.Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_one** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：pairwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [M
ulAction G α] {_ : MeasurableSpace α} {μ : Measure α} {s : Set α} (h_ae_disjoint
 : forall g != (1 : G), AEDisjoint μ (g • s) s) (h_qmp : forall g : G, QuasiMeas
urePreserving (g • ·) μ μ) : Pairwise (AEDisjoint μ on fun g : G => g • s)
参数：h_ae_disjoint : forall g != (1 : G), AEDisjoint μ (g • s) s；h_qmp : forall g 
: G, QuasiMeasurePreserving (g • ·) μ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {f : α -> β} (hf 
: Bijective f) {s t} : f ⁻¹' s = t ↔ s = f '' t
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null`：preimage_nul
l (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s
) = 0
-/
theorem pairwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulAction G α]
    {_ : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (h_ae_disjoint : ∀ g ≠ (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • ·) μ μ) :
    Pairwise (AEDisjoint μ on fun g : G => g • s) := by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g ≠ 1 := by
    rw [Ne, inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s ∩ s) = g₁ • s ∩ g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹), image_smul, smul_set_inter, smul_smul,
      smul_smul, inv_mul_cancel, one_smul]
  change μ (g₁ • s ∩ g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)

end Pointwise

end Measure

open Measure

/-
**MeasureTheory.NullMeasurable.comp_quasiMeasurePreserving** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.NullMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} {μ : MeasureTheory.Measure α} 
{ν : MeasureTheory.Measure β} {f : α → β} {g : β → γ},   MeasureTheory.NullMeasu
rable g ν →     MeasureTheory.Measure.QuasiMeasurePreserving f μ ν → MeasureTheo
ry.NullMeasurable (g ∘ f) μ
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
-/
theorem NullMeasurable.comp_quasiMeasurePreserving {ν : Measure β}
    {f : α → β} {g : β → γ} (hg : NullMeasurable g ν) (hf : QuasiMeasurePreserving f μ ν) :
    NullMeasurable (g ∘ f) μ := fun _s hs ↦ (hg hs).preimage hf
/-
**MeasureTheory.NullMeasurableSet.mono_ac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{s : Set α},   MeasureTheory.NullMeasurableSet s μ → ν.AbsolutelyContinuous μ → 
MeasureTheory.NullMeasurableSet s ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono_left`：mono_left (h : Q
uasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) : QuasiMeasurePreserving f μa' μb
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
-/
theorem NullMeasurableSet.mono_ac (h : NullMeasurableSet s μ) (hle : ν ≪ μ) :
    NullMeasurableSet s ν :=
  h.preimage <| (QuasiMeasurePreserving.id μ).mono_left hle
/-
**MeasureTheory.NullMeasurableSet.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
NullMeasurableSet`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{s : Set α},   MeasureTheory.NullMeasurableSet s μ → ν ≤ μ → MeasureTheory.NullM
easurableSet s ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
-/
theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν ≤ μ) : NullMeasurableSet s ν :=
  h.mono_ac hle.absolutelyContinuous
/-
**MeasureTheory.NullMeasurableSet.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set α},   MeasureTheory.NullMeasurableSet s μ → ∀ (c : ENNReal), MeasureTheor
y.NullMeasurableSet s (c • μ)
参数：c : ENNReal；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
lemma NullMeasurableSet.smul_measure (h : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    NullMeasurableSet s (c • μ) :=
  h.mono_ac (Measure.AbsolutelyContinuous.rfl.smul_left c)
/-
**MeasureTheory.nullMeasurableSet_smul_measure_iff** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：nullMeasurableSet_smul_measure_iff {c : Real>=0∞} (hc : c != 0) : NullMeas
urableSet s (c • μ) ↔ NullMeasurableSet s μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `MeasureTheory.NullMeasurableSet.smul_measure`：∀ {α : Type u_1} {mα : Mea
surableSpace α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullM
easurableSet s μ → ∀ (c : ENNReal)…
-/
lemma nullMeasurableSet_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    NullMeasurableSet s (c • μ) ↔ NullMeasurableSet s μ :=
  ⟨fun h ↦ h.mono_ac (Measure.absolutelyContinuous_smul hc), fun h ↦ h.smul_measure c⟩
/-
**MeasureTheory.AEDisjoint.preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AED
isjoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} {f : α → β
} {s t : Set β},   MeasureTheory.AEDisjoint ν s t →     MeasureTheory.Measure.Qu
asiMeasurePreserving f μ ν → MeasureTheory.AEDisjoint μ (f ⁻¹' s) (f ⁻¹' t)
参数：f ⁻¹' s；f ⁻¹' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null`：preimage_nul
l (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s
) = 0
-/
theorem AEDisjoint.preimage {ν : Measure β} {f : α → β} {s t : Set β} (ht : AEDisjoint ν s t)
    (hf : QuasiMeasurePreserving f μ ν) : AEDisjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
  hf.preimage_null ht

end MeasureTheory

open MeasureTheory

namespace MeasurableEquiv

variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-
**MeasurableEquiv.quasiMeasurePreserving_symm** 是 Mathlib 中的一个定理，位于命名空间 `Measura
bleEquiv`。
形式化陈述：quasiMeasurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) : Measure.QuasiMe
asurePreserving e.symm (μ.map e) μ
参数：μ : Measure α；e : α ≃ᵐ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.refl`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α), μ.AbsolutelyContinuous μ
-/
theorem quasiMeasurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    Measure.QuasiMeasurePreserving e.symm (μ.map e) μ :=
  ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩

end MeasurableEquiv

