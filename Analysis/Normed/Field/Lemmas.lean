/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.MetricSpace.DilationEquiv
import Mathlib.Analysis.Normed.MulAction

/-!
# Normed fields

In this file we continue building the theory of normed division rings and fields.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `discreteTopology_or_nontriviallyNormedField`
* `discreteTopology_of_bddAbove_range_norm`

-/

@[expose] public section

-- Guard against import creep.
assert_not_exists RestrictScalars

variable {α β ι : Type*}

open Filter Bornology Metric
open scoped Topology NNReal Pointwise Uniformity

section NormedDivisionRing

variable [NormedDivisionRing α]

/-- Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
/-
**DilationEquiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DilationEquiv.mulLeft (a : α) (ha : a != 0) : α ≃ᵈ α where __
参数：a : α；ha : a != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α

--- 原说明 ---
Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring.
-/
def DilationEquiv.mulLeft (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  __ := Dilation.mulLeft a ha
  toEquiv := Equiv.mulLeft₀ a ha

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
/-
**DilationEquiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DilationEquiv.mulRight (a : α) (ha : a != 0) : α ≃ᵈ α where __
参数：a : α；ha : a != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α

--- 原说明 ---
Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring.
-/
def DilationEquiv.mulRight (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  __ := Dilation.mulRight a ha
  toEquiv := Equiv.mulRight₀ a ha

namespace Filter

@[simp]
/-
**Filter.map_mul_left_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：map_mul_left_cobounded {a : α} (ha : a != 0) : map (a * ·) (cobounded α) =
 cobounded α
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DilationEquiv.map_cobounded`：map_cobounded (e : F) : map e (cobounded X)
 = cobounded Y
· 使用定理 `DilationEquiv.instDilationEquivClass`：∀ {X : Type u_1} {Y : Type u_2} [i
nst : PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y],   DilationEquivClas
s (X ≃ᵈ Y) X Y
-/
lemma map_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
/-
**Filter.map_mul_right_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：map_mul_right_cobounded {a : α} (ha : a != 0) : map (· * a) (cobounded α) 
= cobounded α
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DilationEquiv.map_cobounded`：map_cobounded (e : F) : map e (cobounded X)
 = cobounded Y
· 使用定理 `DilationEquiv.instDilationEquivClass`：∀ {X : Type u_1} {Y : Type u_2} [i
nst : PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y],   DilationEquivClas
s (X ≃ᵈ Y) X Y
-/
lemma map_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. -/
/-
**Filter.tendsto_mul_left_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_left_cobounded {a : α} (ha : a != 0) : Tendsto (a * ·) (coboun
ded α) (cobounded α)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Filter.map_mul_left_cobounded`：map_mul_left_cobounded {a : α} (ha : a !=
 0) : map (a * ·) (cobounded α) = cobounded α

--- 原说明 ---
Multiplication on the left by a nonzero element of a normed division ring tends 
to infinity at
infinity.
-/
theorem tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. -/
/-
**Filter.tendsto_mul_right_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_right_cobounded {a : α} (ha : a != 0) : Tendsto (· * a) (cobou
nded α) (cobounded α)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Filter.map_mul_right_cobounded`：map_mul_right_cobounded {a : α} (ha : a 
!= 0) : map (· * a) (cobounded α) = cobounded α

--- 原说明 ---
Multiplication on the right by a nonzero element of a normed division ring tends
 to infinity at
infinity.
-/
theorem tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (· * a) (cobounded α) (cobounded α) :=
  (map_mul_right_cobounded ha).le

@[simp]
/-
**Filter.inv_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[≠] 0 := by
  rw [← comap_norm_atTop, ← Filter.comap_inv, ← comap_norm_nhdsGT_zero, ← inv_atTop₀,
    ← Filter.comap_inv]
  simp only [comap_comap, Function.comp_def, norm_inv]

@[simp]
/-
**Filter.inv_nhdsNE_zero** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：inv_nhdsNE_zero : (𝓝[!=] (0 : α))⁻¹ = cobounded α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.inv_cobounded₀`：inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[!=] 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_nhdsNE_zero : (𝓝[≠] (0 : α))⁻¹ = cobounded α := by
  rw [← inv_cobounded₀, inv_inv]
/-
**Filter.tendsto_inv** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tendsto_inv₀_cobounded' : Tendsto Inv.inv (cobounded α) (𝓝[≠] 0) :=
  inv_cobounded₀.le
/-
**Filter.tendsto_inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded α) (𝓝 0) :=
  tendsto_inv₀_cobounded'.mono_right inf_le_left
/-
**Filter.tendsto_inv** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded α) :=
  inv_nhdsNE_zero.le

end Filter

/-- If `s` is a set disjoint from `𝓝 0`, then `fun x ↦ x⁻¹` is uniformly continuous on `s`. -/
/-
**uniformContinuousOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a set disjoint from `𝓝 0`, then `fun x ↦ x⁻¹` is uniformly continuous 
on `s`.
-/
theorem uniformContinuousOn_inv₀ {s : Set α} (hs : sᶜ ∈ 𝓝 0) :
    UniformContinuousOn Inv.inv s := by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hs with ⟨r, hr₀, hr⟩
  simp only [Set.subset_compl_comm (t := s), Set.compl_ofPred, not_lt] at hr
  have hs₀ : ∀ x ∈ s, x ≠ 0 := fun x hx ↦ norm_pos_iff.mp <| hr₀.trans_le (hr hx)
  refine ⟨ε * r ^ 2, by positivity, fun x hx y hy hxy ↦ ?_⟩
  calc
    dist x⁻¹ y⁻¹ = ‖x‖⁻¹ * dist y x * ‖y‖⁻¹ := by
      simp [dist_eq_norm, inv_sub_inv' (hs₀ x hx) (hs₀ y hy)]
    _ ≤ r⁻¹ * (ε * r ^ 2) * r⁻¹ := by
      rw [dist_comm]
      gcongr <;> exact hr ‹_›
    _ = ε := by field_simp

@[to_fun]
/-
**UniformContinuousOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformContinuousOn.inv₀ {X : Type*} [UniformSpace X] {f : X → α} {s : Set X}
    (hf : UniformContinuousOn f s) (hf₀ : (f '' s)ᶜ ∈ 𝓝 0) :
    UniformContinuousOn f⁻¹ s :=
  uniformContinuousOn_inv₀ hf₀ |>.comp hf (Set.mapsTo_image f s)

@[to_fun]
/-
**UniformContinuous.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.inv [UniformSpace β] {f : β -> α} (hf : UniformContinuou
s f) : UniformContinuous fun x => (f x)⁻¹
参数：hf : UniformContinuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.div`：UniformContinuous.div [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem UniformContinuous.inv₀ {X : Type*} [UniformSpace X] {f : X → α}
    (hf : UniformContinuous f) (hf₀ : (Set.range f)ᶜ ∈ 𝓝 0) :
    UniformContinuous f⁻¹ := by
  simp only [← uniformContinuousOn_univ, ← Set.image_univ] at *
  exact hf.inv₀ hf₀

@[to_fun]
/-
**TendstoLocallyUniformlyOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.inv (hf : TendstoLocallyUniformlyOn F f l s) : T
endstoLocallyUniformlyOn F⁻¹ f⁻¹ l s
参数：hf : TendstoLocallyUniformlyOn F f l s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformlyOn`：UniformContinuous.comp
_tendstoLocallyUniformlyOn (hg : UniformContinuous g) (hf : TendstoLocallyUnifor
mlyOn F f p s) : TendstoLocallyUniform…
· 使用定理 `uniformContinuous_inv`：uniformContinuous_inv : UniformContinuous fun x :
 α => x⁻¹
-/
theorem TendstoLocallyUniformlyOn.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ∀ x ∈ s, Disjoint (map f (𝓝[s] x)) (𝓝 0)) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases basis_sets _ |>.map _ |>.disjoint_iff nhds_basis_ball
    |>.mp (hf x hx) with ⟨U, hUx, r, hr₀, hr⟩
  refine Tendsto.comp (uniformContinuousOn_inv₀ (s := (closedBall (0 : α) (r / 2))ᶜ)
    (by simp [closedBall_mem_nhds, hr₀])) <| tendsto_inf.mpr ⟨hF x hx, tendsto_principal.mpr ?_⟩
  filter_upwards [hF x hx (dist_mem_uniformity (half_pos hr₀)), tendsto_snd hUx] with y hy₁ hy₂
  have : r ≤ ‖f y.2‖ := by simp_all [Set.disjoint_left]
  have : r / 2 < ‖F y.1 y.2‖ := by
    simp [dist_eq_norm_sub] at hy₁
    linarith [hy₁, norm_sub_norm_le (f y.2) (F y.1 y.2)]
  simp_all [(half_lt_self hr₀).trans_le]

@[to_fun]
/-
**TendstoLocallyUniformly.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.inv (hf : TendstoLocallyUniformly F f l) : Tendsto
LocallyUniformly F⁻¹ f⁻¹ l
参数：hf : TendstoLocallyUniformly F f l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformly`：UniformContinuous.comp_t
endstoLocallyUniformly (hg : UniformContinuous g) (hf : TendstoLocallyUniformly 
F f p) : TendstoLocallyUniformly (g …
· 使用定理 `uniformContinuous_inv`：uniformContinuous_inv : UniformContinuous fun x :
 α => x⁻¹
-/
theorem TendstoLocallyUniformly.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : ∀ x, Disjoint (map f (𝓝 x)) (𝓝 0)) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.inv₀_of_disjoint
  simpa

@[to_fun]
/-
**TendstoLocallyUniformlyOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.inv (hf : TendstoLocallyUniformlyOn F f l s) : T
endstoLocallyUniformlyOn F⁻¹ f⁻¹ l s
参数：hf : TendstoLocallyUniformlyOn F f l s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformlyOn`：UniformContinuous.comp
_tendstoLocallyUniformlyOn (hg : UniformContinuous g) (hf : TendstoLocallyUnifor
mlyOn F f p s) : TendstoLocallyUniform…
· 使用定理 `uniformContinuous_inv`：uniformContinuous_inv : UniformContinuous fun x :
 α => x⁻¹
-/
theorem TendstoLocallyUniformlyOn.inv₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ContinuousOn f s) (hf₀ : ∀ x ∈ s, f x ≠ 0) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s :=
  hF.inv₀_of_disjoint fun x hx ↦ disjoint_nhds_nhds.2 (hf₀ x hx) |>.mono_left (hf x hx)

@[to_fun]
/-
**TendstoLocallyUniformly.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.inv (hf : TendstoLocallyUniformly F f l) : Tendsto
LocallyUniformly F⁻¹ f⁻¹ l
参数：hf : TendstoLocallyUniformly F f l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformly`：UniformContinuous.comp_t
endstoLocallyUniformly (hg : UniformContinuous g) (hf : TendstoLocallyUniformly 
F f p) : TendstoLocallyUniformly (g …
· 使用定理 `uniformContinuous_inv`：uniformContinuous_inv : UniformContinuous fun x :
 α => x⁻¹
-/
theorem TendstoLocallyUniformly.inv₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : Continuous f) (hf₀ : ∀ x, f x ≠ 0) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l :=
  hF.inv₀_of_disjoint fun x ↦ disjoint_nhds_nhds.2 (hf₀ x) |>.mono_left (hf.tendsto x)

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedDivisionRing.to_continuousInv₀ : ContinuousInv₀ α where
  continuousAt_inv₀ x hx := by
    refine uniformContinuousOn_inv₀ (s := (Metric.closedBall x (‖x‖ / 2))) ?_
      |>.continuousOn |>.continuousAt ?_
    · refine Metric.isClosed_closedBall.isOpen_compl.mem_nhds ?_
      simpa
    · apply Metric.closedBall_mem_nhds
      simpa

@[to_fun]
/-
**TendstoLocallyUniformlyOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.div (hf : TendstoLocallyUniformlyOn F f l s) (hg
 : TendstoLocallyUniformlyOn G g l s) : TendstoLocallyUniformlyOn (F / G) (f / g
) l s
参数：hf : TendstoLocallyUniformlyOn F f l s；hg : TendstoLocallyUniformlyOn G g l s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformlyOn`：UniformContinuous.comp
_tendstoLocallyUniformlyOn (hg : UniformContinuous g) (hf : TendstoLocallyUnifor
mlyOn F f p s) : TendstoLocallyUniform…
· 使用定理 `uniformContinuous_div`：uniformContinuous_div : UniformContinuous fun p :
 α × α => p.1 / p.2
· 使用定理 `TendstoLocallyUniformlyOn.prodMk`：TendstoLocallyUniformlyOn.prodMk [Unif
ormSpace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformlyOn F f p
 s) (hG : TendstoLocal…
-/
theorem TendstoLocallyUniformlyOn.div₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F G : ι → X → α} {f g : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hg₀ : ∀ x ∈ s, g x ≠ 0) :
    TendstoLocallyUniformlyOn (F / G) (f / g) l s := by
  simp only [div_eq_mul_inv]
  exact hF.mul₀ (hG.inv₀ hg hg₀) hf <| hg.inv₀ hg₀

@[to_fun]
/-
**TendstoLocallyUniformly.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.div (hf : TendstoLocallyUniformly F f l) (hg : Ten
dstoLocallyUniformly G g l) : TendstoLocallyUniformly (F / G) (f / g) l
参数：hf : TendstoLocallyUniformly F f l；hg : TendstoLocallyUniformly G g l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformly`：UniformContinuous.comp_t
endstoLocallyUniformly (hg : UniformContinuous g) (hf : TendstoLocallyUniformly 
F f p) : TendstoLocallyUniformly (g …
· 使用定理 `uniformContinuous_div`：uniformContinuous_div : UniformContinuous fun p :
 α × α => p.1 / p.2
· 使用定理 `TendstoLocallyUniformly.prodMk`：TendstoLocallyUniformly.prodMk [UniformS
pace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformly F f p) (hG 
: TendstoLocallyUnif…
-/
theorem TendstoLocallyUniformly.div₀ {X ι : Type*} [TopologicalSpace X]
    {F G : ι → X → α} {f g : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) (hg₀ : ∀ x, g x ≠ 0) :
    TendstoLocallyUniformly (F / G) (f / g) l := by
  simp only [div_eq_mul_inv]
  exact hF.mul₀ (hG.inv₀ hg hg₀) hf <| hg.inv₀ hg₀

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed division ring is a topological division ring.
-/
instance (priority := 100) NormedDivisionRing.to_isTopologicalDivisionRing :
    IsTopologicalDivisionRing α where
/-
**tendsto_norm_inv_nhdsNE_zero_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_norm_inv_nhdsNE_zero_atTop : Tendsto (fun x : α => ‖x⁻¹‖) (𝓝[!=] 0
) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_norm_cobounded_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto norm (Bornology.cobounded E) Filter.atTop
· 使用引理 `Filter.tendsto_inv₀_nhdsNE_zero`：tendsto_inv₀_nhdsNE_zero : Tendsto Inv.
inv (𝓝[!=] 0) (cobounded α)
-/
lemma tendsto_norm_inv_nhdsNE_zero_atTop : Tendsto (fun x : α ↦ ‖x⁻¹‖) (𝓝[≠] 0) atTop :=
  tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero
/-
**tendsto_zpow_nhdsNE_zero_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_zpow_nhdsNE_zero_cobounded {m : Int} (hm : m < 0) : Tendsto (· ^ m
) (𝓝[!=] 0) (cobounded α)
参数：hm : m < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_surjective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Surj
ective Neg.neg
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_pow_cobounded_cobounded`：tendsto_pow_cobounded_cobounded [NormOn
eClass α] [NormMulClass α] {m : Nat} (hm : m != 0) : Tendsto (· ^ m) (cobounded 
α) (cobounded α)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Filter.tendsto_inv₀_nhdsNE_zero`：tendsto_inv₀_nhdsNE_zero : Tendsto Inv.
inv (𝓝[!=] 0) (cobounded α)
-/
lemma tendsto_zpow_nhdsNE_zero_cobounded {m : ℤ} (hm : m < 0) :
    Tendsto (· ^ m) (𝓝[≠] 0) (cobounded α) := by
  obtain ⟨m, rfl⟩ := neg_surjective m
  lift m to ℕ using by lia
  simpa [Function.comp_def] using
    (tendsto_pow_cobounded_cobounded (by lia)).comp tendsto_inv₀_nhdsNE_zero

end NormedDivisionRing

namespace NormedField

/-- A normed field is either nontrivially normed or has a discrete topology.
In the discrete topology case, all the norms are 1, by `norm_eq_one_iff_ne_zero_of_discrete`.
The nontrivially normed field instance is provided by a subtype with a proof that the
forgetful inheritance to the existing `NormedField` instance is definitionally true.
This allows one to have the new `NontriviallyNormedField` instance without data clashes. -/
/-
**NormedField.discreteTopology_or_nontriviallyNormedField** 是 Mathlib 中的一个引理，位于命
名空间 `NormedField`。
形式化陈述：discreteTopology_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜
] : DiscreteTopology 𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜 // h'.toNorme
dField = h})
参数：𝕜 : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A normed field is either nontrivially normed or has a discrete topology.
In the discrete topology case, all the norms are 1, by `norm_eq_one_iff_ne_zero_
of_discrete`.
The nontrivially normed field instance is provided by a subtype with a proof tha
t the
forgetful inheritance to the existing `NormedField` instance is definitionally t
rue.
This allows one to have the new `NontriviallyNormedField` instance without data 
clashes.
-/
lemma discreteTopology_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] :
    DiscreteTopology 𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜 // h'.toNormedField = h}) := by
  by_cases H : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    refine H.imp ?_
    -- contextual to reuse the `a ≠ 0` hypothesis in the proof of `a ≠ 0 ∧ ‖a‖ ≠ 1`
    simp +contextual [ne_of_lt]
/-
**NormedField.discreteTopology_of_bddAbove_range_norm** 是 Mathlib 中的一个引理，位于命名空间 
`NormedField`。
形式化陈述：discreteTopology_of_bddAbove_range_norm {𝕜 : Type*} [NormedField 𝕜] (h : B
ddAbove (Set.range fun k : 𝕜 => ‖k‖)) : DiscreteTopology 𝕜
参数：h : BddAbove (Set.range fun k : 𝕜 => ‖k‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `NormedField.discreteTopology_or_nontriviallyNormedField`：discreteTopolog
y_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] : DiscreteTopology 
𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜…
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma discreteTopology_of_bddAbove_range_norm {𝕜 : Type*} [NormedField 𝕜]
    (h : BddAbove (Set.range fun k : 𝕜 ↦ ‖k‖)) :
    DiscreteTopology 𝕜 := by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_ge (h (Set.mem_range_self k))

section Densely

variable (α) [DenselyNormedField α]

/-
**NormedField.denseRange_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：denseRange_nnnorm : DenseRange (nnnorm : α -> Real>=0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_of_exists_between`：dense_of_exists_between [Nontrivial α] {s : Set
 α} (h : forall ⦃a b⦄, a < b -> exists c in s, c in Ioo a b) : Dense s
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NormedField.exists_lt_nnnorm_lt`：exists_lt_nnnorm_lt {r₁ r₂ : Real>=0} (
h : r₁ < r₂) : exists x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂
-/
theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

end Densely

section NontriviallyNormedField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℤ} {x : 𝕜}

@[simp]
/-
**NormedField.continuousAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：∀ {𝕜 : Type u_4} [inst : NontriviallyNormedField 𝕜] {n : ℤ} {x : 𝕜}, Conti
nuousAt (fun x => x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n
参数：fun x => x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)
· 使用引理 `tendsto_zpow_nhdsNE_zero_cobounded`：tendsto_zpow_nhdsNE_zero_cobounded {
m : Int} (hm : m < 0) : Tendsto (· ^ m) (𝓝[!=] 0) (cobounded α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousAt_zpow₀`：continuousAt_zpow₀ (x : G₀) (m : Int) (h : x != 0 ∨ 
0 <= m) : ContinuousAt (fun x => x ^ m) x
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
-/
protected lemma continuousAt_zpow : ContinuousAt (fun x ↦ x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n := by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).not_tendsto (Metric.disjoint_nhds_cobounded _)
    (tendsto_zpow_nhdsNE_zero_cobounded hm)

@[simp]
/-
**NormedField.continuousAt_inv** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：∀ {𝕜 : Type u_4} [inst : NontriviallyNormedField 𝕜] {x : 𝕜}, ContinuousAt 
Inv.inv x ↔ x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `NormedField.continuousAt_zpow`：∀ {𝕜 : Type u_4} [inst : NontriviallyNorm
edField 𝕜] {n : ℤ} {x : 𝕜}, ContinuousAt (fun x => x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n
-/
protected lemma continuousAt_inv : ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa using NormedField.continuousAt_zpow (n := -1) (x := x)

end NontriviallyNormedField
end NormedField

/-
**Rat.instNormedField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instNormedField : NormedField Rat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedAddCommGroup 
E] (x y : E), dist x y = ‖-x + y‖
-/
instance Rat.instNormedField : NormedField ℚ where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul a b := by simp only [norm, Rat.cast_mul, abs_mul]
/-
**Rat.instDenselyNormedField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instDenselyNormedField : DenselyNormedField Rat where lt_norm_lt r₁ r₂
 h₀ hr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Rat.instDenselyNormedField : DenselyNormedField ℚ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

section Complete

/-
**NormedField.completeSpace_iff_isComplete_closedBall** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：NormedField.completeSpace_iff_isComplete_closedBall {K : Type*} [NormedFie
ld K] : CompleteSpace K ↔ IsComplete (Metric.closedBall 0 1 : Set K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用引理 `NormedField.discreteTopology_or_nontriviallyNormedField`：discreteTopolog
y_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] : DiscreteTopology 
𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_univ`：completeSpace_iff_isComplete_univ : C
ompleteSpace α ↔ IsComplete (univ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NormedDivisionRing.unitClosedBall_eq_univ_of_discrete`：unitClosedBall_eq
_univ_of_discrete : (Metric.closedBall 0 1 : Set 𝕜) = Set.univ
· 使用定理 `Metric.complete_of_cauchySeq_tendsto`：Metric.complete_of_cauchySeq_tends
to : (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Co
mpleteSpace α
· 使用定理 `CauchySeq.norm_bddAbove`：∀ {G : Type u_4} [inst : SeminormedAddGroup G] 
{u : ℕ → G}, CauchySeq u → BddAbove (Set.range fun n => ‖u n‖)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `UniformContinuous.comp_cauchySeq`：UniformContinuous.comp_cauchySeq {γ} [
UniformSpace β] [Preorder γ] {f : α -> β} (hf : UniformContinuous f) {u : γ -> α
} (hu : CauchySeq u) :…
· 使用定理 `uniformContinuous_div_const'`：uniformContinuous_div_const' {R : Type*} [
DivisionRing R] [UniformSpace R] [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) : U
niformContinuous f…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
（共 47 条，此处仅展示前 30 条）
-/
lemma NormedField.completeSpace_iff_isComplete_closedBall {K : Type*} [NormedField K] :
    CompleteSpace K ↔ IsComplete (Metric.closedBall 0 1 : Set K) := by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨k, hk⟩ := hu.norm_bddAbove
  have kpos : 0 ≤ k := (_root_.norm_nonneg (u 0)).trans (hk (by simp))
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K k
  have hu' : CauchySeq ((· / x) ∘ u) := (uniformContinuous_div_const' x).comp_cauchySeq hu
  have hb : ∀ n, ((· / x) ∘ u) n ∈ Metric.closedBall 0 1 := by
    intro
    simp only [Function.comp_apply, Metric.mem_closedBall, dist_zero_right, norm_div]
    rw [div_le_one (kpos.trans_lt hx)]
    exact hx.le.trans' (hk (by simp))
  obtain ⟨a, -, ha'⟩ := cauchySeq_tendsto_of_isComplete h hb hu'
  refine ⟨a * x, (((continuous_mul_const x).tendsto a).comp ha').congr ?_⟩
  have hx' : x ≠ 0 := by
    contrapose! hx
    simp [hx, kpos]
  simp [div_mul_cancel₀ _ hx']

end Complete

