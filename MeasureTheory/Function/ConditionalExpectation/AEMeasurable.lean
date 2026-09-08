/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-! # Functions a.e. measurable with respect to a sub-σ-algebra

A function `f` verifies `AEStronglyMeasurable[m] f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `AEStronglyMeasurable`, but the
`MeasurableSpace` structures used for the measurability statement and for the measure are
different.

We define `lpMeas F 𝕜 m p μ`, the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-strongly
measurable function.

## Main statements

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of `lpMeas`.

`Lp.induction_stronglyMeasurable` (see also `MemLp.induction_stronglyMeasurable`):
To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped ENNReal MeasureTheory

namespace MeasureTheory

/-
**MeasureTheory.ae_eq_trim_iff_of_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：ae_eq_trim_iff_of_aestronglyMeasurable {α β} [TopologicalSpace β] [Metriza
bleSpace β] {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α -> β} (hm : m <=
 m0) (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : h
fm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g
参数：hm : m <= m0；hfm : AEStronglyMeasurable[m] f μ；hgm : AEStronglyMeasurable[m] 
g μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_iff`：ae_eq_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f =ᵐ[μ.tr
im hm] g ↔ f =ᵐ[μ] g
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem ae_eq_trim_iff_of_aestronglyMeasurable {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) :
    hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (hfm.stronglyMeasurable_mk.ae_eq_trim_iff hm hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩
/-
**MeasureTheory.AEStronglyMeasurable.comp_ae_measurable'** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace β]
 {mα : MeasurableSpace α}   {x : MeasurableSpace γ} {f : α → β} {μ : MeasureTheo
ry.Measure γ} {g : γ → α},   MeasureTheory.AEStronglyMeasurable f (MeasureTheory
.Measure.map g μ) →     AEMeasurable g μ → MeasureTheory.AEStronglyMeasurable (f
 ∘ g) μ
参数：MeasureTheory.Measure.map g μ；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_iff_comap_le`：measurable_iff_comap_le {m₁ : MeasurableSpace α
} {m₂ : MeasurableSpace β} {f : α -> β} : Measurable f ↔ m₂.comap f <= m₁
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem AEStronglyMeasurable.comp_ae_measurable' {α β γ : Type*} [TopologicalSpace β]
    {mα : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α → β} {μ : Measure γ} {g : γ → α}
    (hf : AEStronglyMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    AEStronglyMeasurable[mα.comap g] (f ∘ g) μ :=
  ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩

variable {α F 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section LpMeas

/-! ## The subset `lpMeas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `lpMeasSubgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
/-
**MeasureTheory.lpMeasSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : Real>=0∞) 
(μ : Measure α) : AddSubgroup (Lp F p μ) where carrier
参数：m : MeasurableSpace α；p : Real>=0∞；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lpMeasSubgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` 
verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function.
-/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    AddSubgroup (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' {f} hf := AEStronglyMeasurable.congr hf.neg (Lp.coeFn_neg f).symm

variable (𝕜)

/-- `lpMeas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
/-
**MeasureTheory.lpMeas** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : Real>=0∞) (μ : Mea
sure α) : Submodule 𝕜 (Lp F p μ) where carrier
参数：m : MeasurableSpace α；p : Real>=0∞；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lpMeas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verify
ing
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function.
-/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    Submodule 𝕜 (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm

variable {F 𝕜}
/-
**MeasureTheory.mem_lpMeasSubgroup_iff_aestronglyMeasurable** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：mem_lpMeasSubgroup_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ 
: Measure α} {f : Lp F p μ} : f in lpMeasSubgroup F m p μ ↔ AEStronglyMeasurable
[m] f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.mem_carrier`：∀ {G : Type u_1} [inst : AddGroup G] {s : AddSu
bgroup G} {x : G}, x ∈ s.carrier ↔ x ∈ s
· 使用定理 `MeasureTheory.lpMeasSubgroup.eq_1`：∀ {α : Type u_1} (F : Type u_2) [inst
 : NormedAddCommGroup F] (m : MeasurableSpace α) [inst_1 : MeasurableSpace α]   
(p : ENNReal) (μ : Meas…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_lpMeasSubgroup_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeasSubgroup F m p μ ↔ AEStronglyMeasurable[m] f μ := by
  rw [← AddSubgroup.mem_carrier, lpMeasSubgroup, Set.mem_ofPred_eq]
/-
**MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：mem_lpMeas_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measur
e α} {f : Lp F p μ} : f in lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable[m] f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_carrier`：mem_carrier : x in p.carrier ↔ x in (p : Set M)
· 使用定理 `MeasureTheory.lpMeas.eq_1`：∀ {α : Type u_1} (F : Type u_2) (𝕜 : Type u_3
) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 (m : Measurabl…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_lpMeas_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable[m] f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, lpMeas, Set.mem_ofPred_eq]
/-
**MeasureTheory.lpMeas.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.lpMeas`。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {m x : Measura
bleSpace α} {μ : MeasureTheory.Measure α}   (f : ↥(MeasureTheory.lpMeas F 𝕜 m p 
μ)), MeasureTheory.AEStronglyMeasurable (↑↑↑f) μ
参数：f : ↥(MeasureTheory.lpMeas F 𝕜 m p μ)；↑↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable`：mem_lpMeas_iff_aestro
nglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : Lp F p μ} : f in 
lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable…
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
-/
theorem lpMeas.aestronglyMeasurable {m _ : MeasurableSpace α} {μ : Measure α}
    (f : lpMeas F 𝕜 m p μ) : AEStronglyMeasurable[m] (f : α → F) μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mp f.mem
/-
**MeasureTheory.mem_lpMeas_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ) : 
f in lpMeas F 𝕜 m0 p μ
参数：μ : Measure α；f : Lp F p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable`：mem_lpMeas_iff_aestro
nglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : Lp F p μ} : f in 
lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
-/
theorem mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ) :
    f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mpr (Lp.aestronglyMeasurable f)
/-
**MeasureTheory.mem_lpMeas_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m <= m0) {μ :
 Measure α} {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s != ∞) {c : F} : ind
icatorConstLp p (hm s hs) hμs c in lpMeas F 𝕜 m p μ
参数：hm : m <= m0；hs : MeasurableSet[m] s；hμs : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
-/
theorem mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α}
    {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) {c : F} :
    indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun _ : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩

section CompleteSubspace

/-! ## The subspace `lpMeas` is complete.

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`lpMeasSubgroup` (and `lpMeas`). -/


variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `lpMeasSubgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `AEMeasurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
/-
**MeasureTheory.memLp_trim_of_mem_lpMeasSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：memLp_trim_of_mem_lpMeasSubgroup (hm : m <= m0) (f : Lp F p μ) (hf_meas : 
f in lpMeasSubgroup F m p μ) : MemLp (mem_lpMeasSubgroup_iff_aestronglyMeasurabl
e.mp hf_meas).choose p (μ.trim hm)
参数：hm : m <= m0；f : Lp F p μ；hf_meas : f in lpMeasSubgroup F m p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_lpMeasSubgroup_iff_aestronglyMeasurable`：mem_lpMeasSub
group_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : L
p F p μ} : f in lpMeasSubgroup F m p μ ↔ AEStro…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_trim`：eLpNorm_trim (hm : m <= m0) {f : α -> ε} (hf
 : StronglyMeasurable[m] f) : eLpNorm f p (μ.trim hm) = eLpNorm f p μ
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.Lp.eLpNorm_lt_top`：eLpNorm_lt_top (f : Lp E p μ) : eLpNorm
 f p μ < ∞

--- 原说明 ---
If `f` belongs to `lpMeasSubgroup F m p μ`, then the measurable function it is a
lmost
everywhere equal to (given by `AEMeasurable.mk`) belongs to `ℒp` for the measure
 `μ.trim hm`.
-/
theorem memLp_trim_of_mem_lpMeasSubgroup (hm : m ≤ m0) (f : Lp F p μ)
    (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    MemLp (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp hf_meas).choose p (μ.trim hm) := by
  have hf : AEStronglyMeasurable[m] f μ :=
    mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp hf_meas
  change MemLp (hf.mk f) p (μ.trim hm)
  refine ⟨hf.stronglyMeasurable_mk.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_trim hm hf.stronglyMeasurable_mk, eLpNorm_congr_ae hf.ae_eq_mk.symm]
  exact Lp.eLpNorm_lt_top f

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`lpMeasSubgroup F m p μ`. -/
/-
**MeasureTheory.mem_lpMeasSubgroup_toLp_of_trim** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：mem_lpMeasSubgroup_toLp_of_trim (hm : m <= m0) (f : Lp F p (μ.trim hm)) : 
(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f in lpMeasSubgroup F m p μ
参数：hm : m <= m0；f : Lp F p (μ.trim hm)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.memLp_of_memLp_trim`：memLp_of_memLp_trim (hm : m <= m0) {f
 : α -> ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_lpMeasSubgroup_iff_aestronglyMeasurable`：mem_lpMeasSub
group_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : L
p F p μ} : f in lpMeasSubgroup F m p μ ↔ AEStro…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_trim`：of_trim {m₀' : MeasurableSpa
ce α} (hm₀ : m₀' <= m₀) (hf : AEStronglyMeasurable[m] f (μ.trim hm₀)) : AEStrong
lyMeasurable[m] f μ
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f

--- 原说明 ---
If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgr
oup
`lpMeasSubgroup F m p μ`.
-/
theorem mem_lpMeasSubgroup_toLp_of_trim (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    (memLp_of_memLp_trim hm (Lp.memLp f)).toLp f ∈ lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := memLp_of_memLp_trim hm (Lp.memLp f)
  rw [mem_lpMeasSubgroup_iff_aestronglyMeasurable]
  refine AEStronglyMeasurable.congr ?_ (MemLp.coeFn_toLp hf_mem_ℒp).symm
  exact (Lp.aestronglyMeasurable f).of_trim hm

variable (F p μ)

/-- Map from `lpMeasSubgroup` to `Lp F p (μ.trim hm)`. -/
/-
**MeasureTheory.lpMeasSubgroupToLpTrim** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`
。
形式化陈述：lpMeasSubgroupToLpTrim (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : Lp F 
p (μ.trim hm)
参数：hm : m <= m0；f : lpMeasSubgroup F m p μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Map from `lpMeasSubgroup` to `Lp F p (μ.trim hm)`.
-/
noncomputable def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    Lp F p (μ.trim hm) :=
  MemLp.toLp (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

variable (𝕜) in
/-- Map from `lpMeas` to `Lp F p (μ.trim hm)`. -/
/-
**MeasureTheory.lpMeasToLpTrim** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lpMeasToLpTrim (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) : Lp F p (μ.trim hm)
参数：hm : m <= m0；f : lpMeas F 𝕜 m p μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Map from `lpMeas` to `Lp F p (μ.trim hm)`.
-/
noncomputable def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
  MemLp.toLp (mem_lpMeas_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

/-- Map from `Lp F p (μ.trim hm)` to `lpMeasSubgroup`, inverse of
`lpMeasSubgroupToLpTrim`. -/
/-
**MeasureTheory.lpTrimToLpMeasSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`
。
形式化陈述：lpTrimToLpMeasSubgroup (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpMeasSub
group F m p μ
参数：hm : m <= m0；f : Lp F p (μ.trim hm)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mem_lpMeasSubgroup_toLp_of_trim`：mem_lpMeasSubgroup_toLp_o
f_trim (hm : m <= m0) (f : Lp F p (μ.trim hm)) : (memLp_of_memLp_trim hm (Lp.mem
Lp f)).toLp f in lpMeasSubgroup F m…

--- 原说明 ---
Map from `Lp F p (μ.trim hm)` to `lpMeasSubgroup`, inverse of
`lpMeasSubgroupToLpTrim`.
-/
noncomputable def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpMeasSubgroup F m p μ :=
  ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

variable (𝕜) in
/-- Map from `Lp F p (μ.trim hm)` to `lpMeas`, inverse of `Lp_meas_to_Lp_trim`. -/
/-
**MeasureTheory.lpTrimToLpMeas** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lpTrimToLpMeas (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ
参数：hm : m <= m0；f : Lp F p (μ.trim hm)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mem_lpMeasSubgroup_toLp_of_trim`：mem_lpMeasSubgroup_toLp_o
f_trim (hm : m <= m0) (f : Lp F p (μ.trim hm)) : (memLp_of_memLp_trim hm (Lp.mem
Lp f)).toLp f in lpMeasSubgroup F m…

--- 原说明 ---
Map from `Lp F p (μ.trim hm)` to `lpMeas`, inverse of `Lp_meas_to_Lp_trim`.
-/
noncomputable def lpTrimToLpMeas (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

variable {F p μ}
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lpMeasSubgroupToLpTrim_ae_eq (hm : m <= m0) (f : lpMeasSubgroup F m p μ) :
 lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f
参数：hm : m <= m0；f : lpMeasSubgroup F m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_lpMeasSubgroup_iff_aestronglyMeasurable`：mem_lpMeasSub
group_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : L
p F p μ} : f in lpMeasSubgroup F m p μ ↔ AEStro…
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `MeasureTheory.memLp_trim_of_mem_lpMeasSubgroup`：memLp_trim_of_mem_lpMeas
Subgroup (hm : m <= m0) (f : Lp F p μ) (hf_meas : f in lpMeasSubgroup F m p μ) :
 MemLp (mem_lpMeasSubgroup_iff_aestr…
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem lpMeasSubgroupToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm
/-
**MeasureTheory.lpTrimToLpMeasSubgroup_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lpTrimToLpMeasSubgroup_ae_eq (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpT
rimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f
参数：hm : m <= m0；f : Lp F p (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `MeasureTheory.memLp_of_memLp_trim`：memLp_of_memLp_trim (hm : m <= m0) {f
 : α -> ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem lpTrimToLpMeasSubgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))
/-
**MeasureTheory.lpMeasToLpTrim_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lpMeasToLpTrim_ae_eq (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) : lpMeasToLpTri
m F 𝕜 p μ hm f =ᵐ[μ] f
参数：hm : m <= m0；f : lpMeas F 𝕜 m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_lpMeasSubgroup_iff_aestronglyMeasurable`：mem_lpMeasSub
group_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : L
p F p μ} : f in lpMeasSubgroup F m p μ ↔ AEStro…
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `MeasureTheory.memLp_trim_of_mem_lpMeasSubgroup`：memLp_trim_of_mem_lpMeas
Subgroup (hm : m <= m0) (f : Lp F p μ) (hf_meas : f in lpMeasSubgroup F m p μ) :
 MemLp (mem_lpMeasSubgroup_iff_aestr…
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem lpMeasToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm
/-
**MeasureTheory.lpTrimToLpMeas_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lpTrimToLpMeas_ae_eq (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpTrimToLpM
eas F 𝕜 p μ hm f =ᵐ[μ] f
参数：hm : m <= m0；f : Lp F p (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `MeasureTheory.memLp_of_memLp_trim`：memLp_of_memLp_trim (hm : m <= m0) {f
 : α -> ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem lpTrimToLpMeas_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

/-- `lpTrimToLpMeasSubgroup` is a right inverse of `lpMeasSubgroupToLpTrim`. -/
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：lpMeasSubgroupToLpTrim_right_inv (hm : m <= m0) : Function.RightInverse (l
pTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm)
参数：hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq`：lpMeasSubgroupToLpTrim_ae_eq
 (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm f
 =ᵐ[μ] f
· 使用定理 `MeasureTheory.lpTrimToLpMeasSubgroup_ae_eq`：lpTrimToLpMeasSubgroup_ae_eq
 (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[
μ] f

--- 原说明 ---
`lpTrimToLpMeasSubgroup` is a right inverse of `lpMeasSubgroupToLpTrim`.
-/
theorem lpMeasSubgroupToLpTrim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine
    (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)

/-- `lpTrimToLpMeasSubgroup` is a left inverse of `lpMeasSubgroupToLpTrim`. -/
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：lpMeasSubgroupToLpTrim_left_inv (hm : m <= m0) : Function.LeftInverse (lpT
rimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm)
参数：hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lpTrimToLpMeasSubgroup_ae_eq`：lpTrimToLpMeasSubgroup_ae_eq
 (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[
μ] f
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq`：lpMeasSubgroupToLpTrim_ae_eq
 (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm f
 =ᵐ[μ] f

--- 原说明 ---
`lpTrimToLpMeasSubgroup` is a left inverse of `lpMeasSubgroupToLpTrim`.
-/
theorem lpMeasSubgroupToLpTrim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lpMeasSubgroupToLpTrim_add (hm : m <= m0) (f g : lpMeasSubgroup F m p μ) :
 lpMeasSubgroupToLpTrim F p μ hm (f + g) = lpMeasSubgroupToLpTrim F p μ hm f + l
pMeasSubgroupToLpTrim F p μ hm g
参数：hm : m <= m0；f g : lpMeasSubgroup F m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
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
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `MeasureTheory.StronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Add β
]   [ContinuousAdd β],   M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq`：lpMeasSubgroupToLpTrim_ae_eq
 (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm f
 =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
-/
theorem lpMeasSubgroupToLpTrim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) =
      lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g := by
  ext1
  grw [Lp.coeFn_add]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).add (Lp.stronglyMeasurable _)
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq,
    ← Lp.coeFn_add]
  rfl
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lpMeasSubgroupToLpTrim_neg (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : l
pMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f
参数：hm : m <= m0；f : lpMeasSubgroup F m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
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
· 使用定理 `MeasureTheory.Lp.coeFn_neg`：coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `MeasureTheory.StronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Neg β] 
  [ContinuousNeg β], Measu…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq`：lpMeasSubgroupToLpTrim_ae_eq
 (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm f
 =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.neg`：∀ {α : Type u} {β : Type v} [inst : Neg β] {f g
 : α → β} {l : Filter α}, f =ᶠ[l] g → -f =ᶠ[l] -g
-/
theorem lpMeasSubgroupToLpTrim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  grw [Lp.coeFn_neg]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _).neg
    ?_
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, ← Lp.coeFn_neg]
  rfl
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lpMeasSubgroupToLpTrim_sub (hm : m <= m0) (f g : lpMeasSubgroup F m p μ) :
 lpMeasSubgroupToLpTrim F p μ hm (f - g) = lpMeasSubgroupToLpTrim F p μ hm f - l
pMeasSubgroupToLpTrim F p μ hm g
参数：hm : m <= m0；f g : lpMeasSubgroup F m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_add`：lpMeasSubgroupToLpTrim_add (hm
 : m <= m0) (f g : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm (f 
+ g) = lpMeasSubgroupToLpTrim …
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_neg`：lpMeasSubgroupToLpTrim_neg (hm
 : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm (-f) 
= -lpMeasSubgroupToLpTrim F p …
-/
theorem lpMeasSubgroupToLpTrim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) =
      lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, lpMeasSubgroupToLpTrim_add,
    lpMeasSubgroupToLpTrim_neg]
/-
**MeasureTheory.lpMeasToLpTrim_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lpMeasToLpTrim_smul (hm : m <= m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) : lpMeas
ToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f
参数：hm : m <= m0；c : 𝕜；f : lpMeas F 𝕜 m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
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
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `MeasureTheory.StronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type 
u_5}   [inst_1 : SMul 𝕜 β] [Conti…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.lpMeasToLpTrim_ae_eq`：lpMeasToLpTrim_ae_eq (hm : m <= m0) 
(f : lpMeas F 𝕜 m p μ) : lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
-/
theorem lpMeasToLpTrim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  grw [Lp.coeFn_smul]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).const_smul c
  grw [lpMeasToLpTrim_ae_eq]
  push_cast
  grw [Lp.coeFn_smul, lpMeasToLpTrim_ae_eq]

/-- `lpMeasSubgroupToLpTrim` preserves the norm. -/
/-
**MeasureTheory.lpMeasSubgroupToLpTrim_norm_map** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 <= p)] (hm : m <= m0) (f : l
pMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖
参数：1 <= p；hm : m <= m0；f : lpMeasSubgroup F m p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_trim`：eLpNorm_trim (hm : m <= m0) {f : α -> ε} (hf
 : StronglyMeasurable[m] f) : eLpNorm f p (μ.trim hm) = eLpNorm f p μ
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq`：lpMeasSubgroupToLpTrim_ae_eq
 (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm f
 =ᵐ[μ] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`lpMeasSubgroupToLpTrim` preserves the norm.
-/
theorem lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0)
    (f : lpMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_trim hm (Lp.stronglyMeasurable _),
    eLpNorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _), ← Lp.norm_def]
  congr
/-
**MeasureTheory.isometry_lpMeasSubgroupToLpTrim** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 <= p)] (hm : m <= m0) : Isom
etry (lpMeasSubgroupToLpTrim F p μ hm)
参数：1 <= p；hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_sub`：lpMeasSubgroupToLpTrim_sub (hm
 : m <= m0) (f g : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm (f 
- g) = lpMeasSubgroupToLpTrim …
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_norm_map`：lpMeasSubgroupToLpTrim_no
rm_map [hp : Fact (1 <= p)] (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : ‖lpMea
sSubgroupToLpTrim F p μ hm f‖ = ‖f‖
-/
theorem isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, ← lpMeasSubgroupToLpTrim_sub, lpMeasSubgroupToLpTrim_norm_map,
      dist_eq_norm]

variable (F p μ)

/-- `lpMeasSubgroup` and `Lp F p (μ.trim hm)` are isometric. -/
/-
**MeasureTheory.lpMeasSubgroupToLpTrimIso** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lpMeasSubgroupToLpTrimIso [Fact (1 <= p)] (hm : m <= m0) : lpMeasSubgroup 
F m p μ ≃ᵢ Lp F p (μ.trim hm) where toFun
参数：1 <= p；hm : m <= m0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_left_inv`：lpMeasSubgroupToLpTrim_le
ft_inv (hm : m <= m0) : Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (
lpMeasSubgroupToLpTrim F p μ hm)
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_right_inv`：lpMeasSubgroupToLpTrim_r
ight_inv (hm : m <= m0) : Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm
) (lpMeasSubgroupToLpTrim F p μ hm)
· 使用定理 `MeasureTheory.isometry_lpMeasSubgroupToLpTrim`：isometry_lpMeasSubgroupTo
LpTrim [hp : Fact (1 <= p)] (hm : m <= m0) : Isometry (lpMeasSubgroupToLpTrim F 
p μ hm)

--- 原说明 ---
`lpMeasSubgroup` and `Lp F p (μ.trim hm)` are isometric.
-/
noncomputable def lpMeasSubgroupToLpTrimIso [Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeasSubgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm

variable (𝕜)

/-- `lpMeasSubgroup` and `lpMeas` are isometric. -/
/-
**MeasureTheory.lpMeasSubgroupToLpMeasIso** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lpMeasSubgroupToLpMeasIso [Fact (1 <= p)] : lpMeasSubgroup F m p μ ≃ᵢ lpMe
as F 𝕜 m p μ
参数：1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lpMeasSubgroup` and `lpMeas` are isometric.
-/
noncomputable def lpMeasSubgroupToLpMeasIso [Fact (1 ≤ p)] :
    lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  IsometryEquiv.refl (lpMeasSubgroup F m p μ)

/-- `lpMeas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
/-
**MeasureTheory.lpMeasToLpTrimLie** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lpMeasToLpTrimLie [Fact (1 <= p)] (hm : m <= m0) : lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜]
 Lp F p (μ.trim hm) where toFun
参数：1 <= p；hm : m <= m0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_add`：lpMeasSubgroupToLpTrim_add (hm
 : m <= m0) (f g : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm (f 
+ g) = lpMeasSubgroupToLpTrim …
· 使用定理 `MeasureTheory.lpMeasToLpTrim_smul`：lpMeasToLpTrim_smul (hm : m <= m0) (c
 : 𝕜) (f : lpMeas F 𝕜 m p μ) : lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToL
pTrim F 𝕜 p μ hm f
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_left_inv`：lpMeasSubgroupToLpTrim_le
ft_inv (hm : m <= m0) : Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (
lpMeasSubgroupToLpTrim F p μ hm)
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_right_inv`：lpMeasSubgroupToLpTrim_r
ight_inv (hm : m <= m0) : Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm
) (lpMeasSubgroupToLpTrim F p μ hm)
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_norm_map`：lpMeasSubgroupToLpTrim_no
rm_map [hp : Fact (1 <= p)] (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : ‖lpMea
sSubgroupToLpTrim F p μ hm f‖ = ‖f‖

--- 原说明 ---
`lpMeas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence.
-/
noncomputable def lpMeasToLpTrimLie [Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] Lp F p (μ.trim hm) where
  toFun := lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  map_add' := lpMeasSubgroupToLpTrim_add hm
  map_smul' := lpMeasToLpTrim_smul hm
  norm_map' := lpMeasSubgroupToLpTrim_norm_map hm

variable {F 𝕜 p μ}
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeasSubgroup F m p μ) := by
  rw [(lpMeasSubgroupToLpTrimIso F p μ hm.elim).completeSpace_iff]; infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeas F 𝕜 m p μ) := by
  rw [(lpMeasSubgroupToLpMeasIso F 𝕜 p μ).symm.completeSpace_iff]; infer_instance
/-
**MeasureTheory.isComplete_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：isComplete_aestronglyMeasurable [hp : Fact (1 <= p)] [CompleteSpace F] (hm
 : m <= m0) : IsComplete {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
参数：1 <= p；hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `completeSpace_coe_iff_isComplete`：completeSpace_coe_iff_isComplete {s : 
Set α} : CompleteSpace s ↔ IsComplete s
· 使用定理 `MeasureTheory.instCompleteSpaceSubtypeAEEqFunMemAddSubgroupLpLpMeasSubgr
oupOfFactLeMeasurableSpace`：∀ {α : Type u_1} {F : Type u_2} {p : ENNReal} [inst 
: NormedAddCommGroup F] {m m0 : MeasurableSpace α}   {μ : MeasureTheory.Measure 
α} [hm :…
-/
theorem isComplete_aestronglyMeasurable [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsComplete {f : Lp F p μ | AEStronglyMeasurable[m] f μ} := by
  rw [← completeSpace_coe_iff_isComplete]
  have : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance
/-
**MeasureTheory.isClosed_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：isClosed_aestronglyMeasurable [Fact (1 <= p)] [CompleteSpace F] (hm : m <=
 m0) : IsClosed {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
参数：1 <= p；hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.isClosed`：IsComplete.isClosed [UniformSpace α] [T0Space α] {s
 : Set α} (h : IsComplete s) : IsClosed s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.isComplete_aestronglyMeasurable`：isComplete_aestronglyMeas
urable [hp : Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0) : IsComplete {f : L
p F p μ | AEStronglyMeasurable[m] f…
-/
theorem isClosed_aestronglyMeasurable [Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed {f : Lp F p μ | AEStronglyMeasurable[m] f μ} :=
  IsComplete.isClosed (isComplete_aestronglyMeasurable hm)

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
/-
**MeasureTheory.lpMeas.ae_fin_strongly_measurable'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.lpMeas`。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {m m0 : Measur
ableSpace α} {μ : MeasureTheory.Measure α} (hm : m ≤ m0)   (f : ↥(MeasureTheory.
lpMeas F 𝕜 m p μ)),   p ≠ 0 → p ≠ ⊤ → ∃ g, MeasureTheory.FinStronglyMeasurable g
 (μ.trim hm) ∧ ↑↑↑f =ᵐ[μ] g
参数：hm : m ≤ m0；f : ↥(MeasureTheory.lpMeas F 𝕜 m p μ)；μ.trim hm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.finStronglyMeasurable`：∀ {α : Type u_1} {G : Type u_2} 
{p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : N
ormedAddCommGroup G] (f : ↥(…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq`：lpMeasSubgroupToLpTrim_ae_eq
 (hm : m <= m0) (f : lpMeasSubgroup F m p μ) : lpMeasSubgroupToLpTrim F p μ hm f
 =ᵐ[μ] f

--- 原说明 ---
We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`.
-/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) :
    ∃ g, FinStronglyMeasurable g (μ.trim hm) ∧ f.1 =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩

/-- When applying the inverse of `lpMeasToLpTrimLie` (which takes a function in the Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indicator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-algebra. -/
/-
**MeasureTheory.lpMeasToLpTrimLie_symm_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：lpMeasToLpTrimLie_symm_indicator [one_le_p : Fact (1 <= p)] [NormedSpace R
eal F] {hm : m <= m0} {s : Set α} {μ : Measure α} (hs : MeasurableSet[m] s) (hμs
 : μ.trim hm s != ∞) (c : F) : ((lpMeasToLpTrimLie F Real p μ hm).symm (indicato
rConstLp p hs hμs c) : Lp F p μ) = indicatorConstLp p (hm s hs) ((le_trim hm).tr
ans_lt hμs.lt_top).ne c
参数：1 <= p；hs : MeasurableSet[m] s；hμs : μ.trim hm s != ∞；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.lpTrimToLpMeas_ae_eq`：lpTrimToLpMeas_ae_eq (hm : m <= m0) 
(f : Lp F p (μ.trim hm)) : lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
When applying the inverse of `lpMeasToLpTrimLie` (which takes a function in the 
Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indi
cator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-al
gebra.
-/
theorem lpMeasToLpTrimLie_symm_indicator [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] {hm : m ≤ m0}
    {s : Set α} {μ : Measure α} (hs : MeasurableSet[m] s) (hμs : μ.trim hm s ≠ ∞) (c : F) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (indicatorConstLp p hs hμs c) : Lp F p μ) =
      indicatorConstLp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).ne c := by
  ext1
  change
    lpTrimToLpMeas F ℝ p μ hm (indicatorConstLp p hs hμs c) =ᵐ[μ]
      (indicatorConstLp p _ _ c : α → F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim indicatorConstLp_coeFn, indicatorConstLp_coeFn]
/-
**MeasureTheory.lpMeasToLpTrimLie_symm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 <= p)] [NormedSpace Real F
] (hm : m <= m0) (f : α -> F) (hf : MemLp f p (μ.trim hm)) : ((lpMeasToLpTrimLie
 F Real p μ hm).symm (hf.toLp f) : Lp F p μ) = (memLp_of_memLp_trim hm hf).toLp 
f
参数：1 <= p；hm : m <= m0；f : α -> F；hf : MemLp f p (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.memLp_of_memLp_trim`：memLp_of_memLp_trim (hm : m <= m0) {f
 : α -> ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.lpTrimToLpMeas_ae_eq`：lpTrimToLpMeas_ae_eq (hm : m <= m0) 
(f : Lp F p (μ.trim hm)) : lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] (hm : m ≤ m0)
    (f : α → F) (hf : MemLp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (hf.toLp f) : Lp F p μ) =
      (memLp_of_memLp_trim hm hf).toLp f := by
  ext1
  change lpTrimToLpMeas F ℝ p μ hm (MemLp.toLp f hf) =ᵐ[μ] (MemLp.toLp f _ : α → F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp hf), MemLp.coeFn_toLp]

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 ≤ p)] [NormedSpace ℝ F]

/-- Auxiliary lemma for `Lp.induction_stronglyMeasurable`. -/
@[elab_as_elim]
/-
**MeasureTheory.Lp.induction_stronglyMeasurable_aux** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {p : ENNReal} [inst : NormedAddCommGroup F
] {m m0 : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [inst_1 : Fact (1 ≤
 p)] [inst_2 : NormedSpace ℝ F] (hm : m ≤ m0),   p ≠ ⊤ →     ∀ (P : ↥(MeasureThe
ory.Lp F p μ) → Prop),       (∀ (c : F) {s : Set α} (hs : MeasurableSet s) (hμs 
: μ s < ⊤),           P ↑(MeasureTheory.Lp.simpleFunc.indicatorConst p ⋯ ⋯ c)) →
         (∀ ⦃f g : α → F⦄ (hf : MeasureTheory.MemLp f p μ) (hg : MeasureTheory.M
emLp g p μ),             MeasureTheory.AEStronglyMeasurable f μ →               
MeasureTheory.AEStronglyMeasurable g μ →                 Disjoint (Function.supp
ort f) (Function.support g) →                   P (MeasureTheory.MemLp.toLp f hf
) →                     P (MeasureTheory.MemLp.toLp g hg) →                     
  P (MeasureTheory.MemLp.toLp f hf + MeasureTheory.MemLp.toLp g hg)) →          
 IsClosed {f | P ↑f} → ∀ (f : ↥(MeasureTheory.Lp F p μ)), MeasureTheory.AEStrong
lyMeasurable (↑↑f) μ → P f
参数：1 ≤ p；hm : m ≤ m0；P : ↥(MeasureTheory.Lp F p μ) → Prop；∀ (c : F) {s : Set α} 
(hs : MeasurableSet s) (hμs : μ s < ⊤),           P ↑(MeasureTheory.Lp.simpleFun
c.indicatorConst p ⋯ ⋯ c)；∀ ⦃f g : α → F⦄ (hf : MeasureTheory.MemLp f p μ) (hg :
 MeasureTheory.MemLp g p μ),             MeasureTheory.AEStronglyMeasurable f μ 
→               MeasureTheory.AEStronglyMeasurable g μ →                 Disjoin
t (Function.support f) (Function.support g) →                   P (MeasureTheory
.MemLp.toLp f hf) →                     P (MeasureTheory.MemLp.toLp g hg) →     
                  P (MeasureTheory.MemLp.toLp f hf + MeasureTheory.MemLp.toLp g 
hg)；f : ↥(MeasureTheory.Lp F p μ)；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
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
· 使用定理 `LinearIsometryEquiv.map_add`：map_add (x y : E) : e (x + y) = e x + e y
· 使用定理 `MeasureTheory.memLp_of_memLp_trim`：memLp_of_memLp_trim (hm : m <= m0) {f
 : α -> ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ
· 使用定理 `MeasureTheory.lpMeasToLpTrimLie_symm_toLp`：lpMeasToLpTrimLie_symm_toLp [
one_le_p : Fact (1 <= p)] [NormedSpace Real F] (hm : m <= m0) (f : α -> F) (hf :
 MemLp f p (μ.trim hm)) : ((lpM…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_trim`：of_trim {m₀' : MeasurableSpa
ce α} (hm₀ : m₀' <= m₀) (hf : AEStronglyMeasurable[m] f (μ.trim hm₀)) : AEStrong
lyMeasurable[m] f μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …

--- 原说明 ---
Auxiliary lemma for `Lp.induction_stronglyMeasurable`.
-/
theorem Lp.induction_stronglyMeasurable_aux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind : ∀ (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : ∀ ⦃f g⦄, ∀ hf : MemLp f p μ, ∀ hg : MemLp g p μ, AEStronglyMeasurable[m] f μ →
      AEStronglyMeasurable[m] g μ → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AEStronglyMeasurable[m] f μ → P f := by
  intro f hf
  let f' := (⟨f, hf⟩ : lpMeas F ℝ m p μ)
  let g := lpMeasToLpTrimLie F ℝ p μ hm f'
  have hfg : f' = (lpMeasToLpTrimLie F ℝ p μ hm).symm g := by
    simp only [f', g, LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine
    @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top
      (fun g => P ((lpMeasToLpTrimLie F ℝ p μ hm).symm g)) ?_ ?_ ?_ g
  · intro b t ht hμt
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator ht hμt.ne b]
    have hμt' : μ t < ∞ := (le_trim hm).trans_lt hμt
    specialize h_ind b ht hμt'
    rwa [Lp.simpleFunc.coe_indicatorConst] at h_ind
  · intro f g hf hg h_disj hfP hgP
    rw [LinearIsometryEquiv.map_add]
    push_cast
    have h_eq :
      ∀ (f : α → F) (hf : MemLp f p (μ.trim hm)),
        ((lpMeasToLpTrimLie F ℝ p μ hm).symm (MemLp.toLp f hf) : Lp F p μ) =
          (memLp_of_memLp_trim hm hf).toLp f :=
      lpMeasToLpTrimLie_symm_toLp hm
    rw [h_eq f hf] at hfP ⊢
    rw [h_eq g hg] at hgP ⊢
    exact h_add (memLp_of_memLp_trim hm hf) (memLp_of_memLp_trim hm hg)
      (hf.aestronglyMeasurable.of_trim hm) (hg.aestronglyMeasurable.of_trim hm) h_disj hfP hgP
  · change IsClosed ((lpMeasToLpTrimLie F ℝ p μ hm).symm ⁻¹' {g : lpMeas F ℝ m p μ | P ↑g})
    exact IsClosed.preimage (LinearIsometryEquiv.continuous _) h_closed

set_option backward.isDefEq.respectTransparency false in
/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_elim]
/-
**MeasureTheory.Lp.induction_stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {p : ENNReal} [inst : NormedAddCommGroup F
] {m m0 : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [inst_1 : Fact (1 ≤
 p)] [inst_2 : NormedSpace ℝ F] (hm : m ≤ m0),   p ≠ ⊤ →     ∀ (P : ↥(MeasureThe
ory.Lp F p μ) → Prop),       (∀ (c : F) {s : Set α} (hs : MeasurableSet s) (hμs 
: μ s < ⊤),           P ↑(MeasureTheory.Lp.simpleFunc.indicatorConst p ⋯ ⋯ c)) →
         (∀ ⦃f g : α → F⦄ (hf : MeasureTheory.MemLp f p μ) (hg : MeasureTheory.M
emLp g p μ),             MeasureTheory.StronglyMeasurable f →               Meas
ureTheory.StronglyMeasurable g →                 Disjoint (Function.support f) (
Function.support g) →                   P (MeasureTheory.MemLp.toLp f hf) →     
                P (MeasureTheory.MemLp.toLp g hg) →                       P (Mea
sureTheory.MemLp.toLp f hf + MeasureTheory.MemLp.toLp g hg)) →           IsClose
d {f | P ↑f} → ∀ (f : ↥(MeasureTheory.Lp F p μ)), MeasureTheory.AEStronglyMeasur
able (↑↑f) μ → P f
参数：1 ≤ p；hm : m ≤ m0；P : ↥(MeasureTheory.Lp F p μ) → Prop；∀ (c : F) {s : Set α} 
(hs : MeasurableSet s) (hμs : μ s < ⊤),           P ↑(MeasureTheory.Lp.simpleFun
c.indicatorConst p ⋯ ⋯ c)；∀ ⦃f g : α → F⦄ (hf : MeasureTheory.MemLp f p μ) (hg :
 MeasureTheory.MemLp g p μ),             MeasureTheory.StronglyMeasurable f →   
            MeasureTheory.StronglyMeasurable g →                 Disjoint (Funct
ion.support f) (Function.support g) →                   P (MeasureTheory.MemLp.t
oLp f hf) →                     P (MeasureTheory.MemLp.toLp g hg) →             
          P (MeasureTheory.MemLp.toLp f hf + MeasureTheory.MemLp.toLp g hg)；f : 
↥(MeasureTheory.Lp F p μ)；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.StronglyMeasurable.measurableSet_support`：∀ {α : Type u_1}
 {β : Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : Zero β] [inst_1 : To
pologicalSpace β]   [TopologicalSpace.Metriz…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.support`：∀ {α : Type u_1} {β : Type u_2} [inst : Zer
o β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → Function.support f =ᶠ[l] Functi
on.support g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Filter.EventuallyEq.diff`：∀ {α : Type u} {s t s' t' : Set α} {l : Filter
 α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s \ s' =ᶠ[l] t \ t'
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `indicator_ae_eq_of_ae_eq_set`：indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ
] t) : s.indicator f =ᵐ[μ] t.indicator f
· 使用定理 `Set.indicator_support`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
f : α → M}, (Function.support f).indicator f = f
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.support_indicator_subset`：∀ {α : Type u_1} {M : Type u_3} [inst : Ze
ro M] {s : Set α} {f : α → M}, Function.support (s.indicator f) ⊆ s
· 使用定理 `disjoint_sdiff_sdiff`：disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x)
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
To prove something for an `Lp` function a.e. strongly measurable with respect to
 a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measu
rable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the prop
erty holds is
  closed.
-/
theorem Lp.induction_stronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind : ∀ (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : ∀ ⦃f g⦄, ∀ hf : MemLp f p μ, ∀ hg : MemLp g p μ, StronglyMeasurable[m] f →
      StronglyMeasurable[m] g → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AEStronglyMeasurable[m] f μ → P f := by
  intro f hf
  suffices h_add_ae :
    ∀ ⦃f g⦄, ∀ hf : MemLp f p μ, ∀ hg : MemLp g p μ, AEStronglyMeasurable[m] f μ →
      AEStronglyMeasurable[m] g μ → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g) from
    Lp.induction_stronglyMeasurable_aux hm hp_ne_top _ h_ind h_add_ae h_closed f hf
  intro f g hf hg hfm hgm h_disj hPf hPg
  let s_f : Set α := Function.support (hfm.mk f)
  have hs_f : MeasurableSet[m] s_f := hfm.stronglyMeasurable_mk.measurableSet_support
  have hs_f_eq : s_f =ᵐ[μ] Function.support f := hfm.ae_eq_mk.symm.support
  let s_g : Set α := Function.support (hgm.mk g)
  have hs_g : MeasurableSet[m] s_g := hgm.stronglyMeasurable_mk.measurableSet_support
  have hs_g_eq : s_g =ᵐ[μ] Function.support g := hgm.ae_eq_mk.symm.support
  have h_inter_empty : (s_f ∩ s_g : Set α) =ᵐ[μ] (∅ : Set α) := by
    refine (hs_f_eq.inter hs_g_eq).trans ?_
    suffices Function.support f ∩ Function.support g = ∅ by rw [this]
    exact Set.disjoint_iff_inter_eq_empty.mp h_disj
  let f' := (s_f \ s_g).indicator (hfm.mk f)
  have hff' : f =ᵐ[μ] f' := by
    have : s_f \ s_g =ᵐ[μ] s_f := by
      rw [← Set.sdiff_inter_self_eq_sdiff, Set.inter_comm]
      refine ((ae_eq_refl s_f).diff h_inter_empty).trans ?_
      rw [Set.sdiff_empty]
    refine ((indicator_ae_eq_of_ae_eq_set this).trans ?_).symm
    rw [Set.indicator_support]
    exact hfm.ae_eq_mk.symm
  have hf'_meas : StronglyMeasurable[m] f' := hfm.stronglyMeasurable_mk.indicator (hs_f.diff hs_g)
  have hf'_Lp : MemLp f' p μ := hf.ae_eq hff'
  let g' := (s_g \ s_f).indicator (hgm.mk g)
  have hgg' : g =ᵐ[μ] g' := by
    have : s_g \ s_f =ᵐ[μ] s_g := by
      rw [← Set.sdiff_inter_self_eq_sdiff]
      refine ((ae_eq_refl s_g).diff h_inter_empty).trans ?_
      rw [Set.sdiff_empty]
    refine ((indicator_ae_eq_of_ae_eq_set this).trans ?_).symm
    rw [Set.indicator_support]
    exact hgm.ae_eq_mk.symm
  have hg'_meas : StronglyMeasurable[m] g' := hgm.stronglyMeasurable_mk.indicator (hs_g.diff hs_f)
  have hg'_Lp : MemLp g' p μ := hg.ae_eq hgg'
  have h_disj : Disjoint (Function.support f') (Function.support g') :=
    haveI : Disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff
    this.mono Set.support_indicator_subset Set.support_indicator_subset
  rw [← MemLp.toLp_congr hf'_Lp hf hff'.symm] at hPf ⊢
  rw [← MemLp.toLp_congr hg'_Lp hg hgg'.symm] at hPg ⊢
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg

/-- To prove something for an arbitrary `MemLp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_elim]
/-
**MeasureTheory.MemLp.induction_stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {F : Type u_2} {p : ENNReal} [inst : NormedAddCommGroup F
] {m m0 : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [inst_1 : Fact (1 ≤
 p)] [inst_2 : NormedSpace ℝ F],   m ≤ m0 →     p ≠ ⊤ →       ∀ (P : (α → F) → P
rop),         (∀ (c : F) ⦃s : Set α⦄, MeasurableSet s → μ s < ⊤ → P (s.indicator
 fun x => c)) →           (∀ ⦃f g : α → F⦄,               Disjoint (Function.sup
port f) (Function.support g) →                 MeasureTheory.MemLp f p μ →      
             MeasureTheory.MemLp g p μ →                     MeasureTheory.Stron
glyMeasurable f → MeasureTheory.StronglyMeasurable g → P f → P g → P (f + g)) → 
            IsClosed {f | P ↑↑↑f} →               (∀ ⦃f g : α → F⦄, f =ᵐ[μ] g → 
MeasureTheory.MemLp f p μ → P f → P g) →                 ∀ ⦃f : α → F⦄, MeasureT
heory.MemLp f p μ → MeasureTheory.AEStronglyMeasurable f μ → P f
参数：1 ≤ p；P : (α → F) → Prop；∀ (c : F) ⦃s : Set α⦄, MeasurableSet s → μ s < ⊤ → P
 (s.indicator fun x => c)；∀ ⦃f g : α → F⦄,               Disjoint (Function.supp
ort f) (Function.support g) →                 MeasureTheory.MemLp f p μ →       
            MeasureTheory.MemLp g p μ →                     MeasureTheory.Strong
lyMeasurable f → MeasureTheory.StronglyMeasurable g → P f → P g → P (f + g)；∀ ⦃f
 g : α → F⦄, f =ᵐ[μ] g → MeasureTheory.MemLp f p μ → P f → P g。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.Lp.induction_stronglyMeasurable`：∀ {α : Type u_1} {F : Typ
e u_2} {p : ENNReal} [inst : NormedAddCommGroup F] {m m0 : MeasurableSpace α}   
{μ : MeasureTheory.Measure α} [inst…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.simpleFunc.coe_indicatorConst`：coe_indicatorConst {s : 
Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : (↑(indicatorConst p hs 
hμs c) : Lp E p μ) = indicatorConstL…
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用引理 `MeasureTheory.memLp_indicator_const`：memLp_indicator_const (p : Real>=0∞
) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s != ∞) : MemLp (s.indicator 
fun _ => c) p μ
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G

--- 原说明 ---
To prove something for an arbitrary `MemLp` function a.e. strongly measurable wi
th respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measu
rable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for whic
h the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
theorem MemLp.induction_stronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : (α → F) → Prop)
    (h_ind : ∀ (c : F) ⦃s⦄, MeasurableSet[m] s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add : ∀ ⦃f g : α → F⦄, Disjoint (Function.support f) (Function.support g) →
      MemLp f p μ → MemLp g p μ → StronglyMeasurable[m] f → StronglyMeasurable[m] g →
        P f → P g → P (f + g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f})
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → MemLp f p μ → P f → P g) :
    ∀ ⦃f : α → F⦄, MemLp f p μ → AEStronglyMeasurable[m] f μ → P f := by
  intro f hf hfm
  let f_Lp := hf.toLp f
  have hfm_Lp : AEStronglyMeasurable[m] f_Lp μ := hfm.congr hf.coeFn_toLp.symm
  refine h_ae hf.coeFn_toLp (Lp.memLp _) ?_
  change P f_Lp
  refine Lp.induction_stronglyMeasurable hm hp_ne_top (fun f => P f) ?_ ?_ h_closed f_Lp hfm_Lp
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine h_ae indicatorConstLp_coeFn.symm ?_ (h_ind c hs hμs)
    exact memLp_indicator_const p (hm s hs) c (Or.inr hμs.ne)
  · intro f g hf_mem hg_mem hfm hgm h_disj hfP hgP
    have hfP' : P f := h_ae hf_mem.coeFn_toLp (Lp.memLp _) hfP
    have hgP' : P g := h_ae hg_mem.coeFn_toLp (Lp.memLp _) hgP
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP'
    refine h_ae ?_ (hf_mem.add hg_mem) h_add
    exact (hf_mem.coeFn_toLp.symm.add hg_mem.coeFn_toLp.symm).trans (Lp.coeFn_add _ _).symm

end Induction

end MeasureTheory

