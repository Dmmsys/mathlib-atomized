/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Defs

/-!
# Basic kernels

This file contains basic results about kernels in general and definitions of some particular
kernels.

## Main definitions

* `ProbabilityTheory.Kernel.deterministic (f : α → β) (hf : Measurable f)`:
  kernel `a ↦ Measure.dirac (f a)`.
* `ProbabilityTheory.Kernel.id`: the identity kernel, deterministic kernel for
  the identity function.
* `ProbabilityTheory.Kernel.copy α`: the deterministic kernel that maps `x : α` to
  the Dirac measure at `(x, x) : α × α`.
* `ProbabilityTheory.Kernel.discard α`: the Markov kernel to the type `PUnit`.
* `ProbabilityTheory.Kernel.swap α β`: the deterministic kernel that maps `(x, y)` to
  the Dirac measure at `(y, x)`.
* `ProbabilityTheory.Kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `ProbabilityTheory.Kernel.restrict κ (hs : MeasurableSet s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(κ.restrict hs a) = ∫⁻ b in s, f b ∂(κ a)`
* `ProbabilityTheory.Kernel.comapRight`: Kernel with value `(κ a).comap f`,
  for a measurable embedding `f`. That is, for a measurable set `t : Set β`,
  `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`
* `ProbabilityTheory.Kernel.piecewise (hs : MeasurableSet s) κ η`: the kernel equal to `κ`
  on the measurable set `s` and to `η` on its complement.

## Main statements

-/

@[expose] public section

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}

namespace Kernel

section Deterministic

/--
Definition of `deterministic` / `deterministic` 的定义

English:
definition deterministic
  signature: (f : α -> β) (hf : Measurable f)
  body: Measure.dirac (f a)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)

中文:
定义 deterministic
  签名: (f : α -> β) (hf : 可测 f)
  定义体: Measure.dirac (f a)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)

Depends on / 依赖: Measure, Measure.dirac
-/
noncomputable def deterministic (f : α -> β) (hf : Measurable f) : Kernel α β where
  toFun a := Measure.dirac (f a)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)

/--
theorem `deterministic_apply` / 定理 `deterministic_apply`

English:
theorem deterministic_apply
  given: {f : α -> β} (hf : Measurable f) (a : α)
  proof: rfl

中文:
定理 deterministic_apply
  条件: {f : α -> β} (hf : 可测 f) (a : α)
  证明: rfl
-/
theorem deterministic_apply {f : α -> β} (hf : Measurable f) (a : α) :
    deterministic f hf a = Measure.dirac (f a) :=
  rfl

/--
theorem `deterministic_apply'` / 定理 `deterministic_apply'`

English:
theorem deterministic_apply'
  statement: {f : α -> β} (hf : Measurable f) (a : α) {s : Set β}
  proof: by
  rw [deterministic]
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]

中文:
定理 deterministic_apply'
  结论: {f : α -> β} (hf : 可测 f) (a : α) {s : 集合 β}
  证明: by
  rw [deterministic]
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]

Depends on / 依赖: Measure, Measure.dirac, Measure.dirac_apply, deterministic, dirac_apply, indicator, s.indicator, simp_rw
-/
theorem deterministic_apply' {f : α -> β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a) := by
  rw [deterministic]
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]

/--
theorem `deterministic_congr` / 定理 `deterministic_congr`

English:
theorem deterministic_congr
  given: {f g : α -> β} {hf : Measurable f} (h : f = g)
  proof: by
  grind

中文:
定理 deterministic_congr
  条件: {f g : α -> β} {hf : 可测 f} (h : f = g)
  证明: by
  grind
-/
theorem deterministic_congr {f g : α -> β} {hf : Measurable f} (h : f = g) :
    deterministic f hf = deterministic g (h ▸ hf) := by
  grind

/--
Instance `isMarkovKernel_deterministic` / 实例 `isMarkovKernel_deterministic`

English:
instance isMarkovKernel_deterministic
  signature: {f : α -> β} (hf : Measurable f)
  body: ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩

中文:
实例 isMarkovKernel_deterministic
  签名: {f : α -> β} (hf : 可测 f)
  定义体: ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩

Depends on / 依赖: deterministic_apply, infer_instance
-/
instance isMarkovKernel_deterministic {f : α -> β} (hf : Measurable f) :
    IsMarkovKernel (deterministic f hf) :=
  ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩

/--
theorem `lintegral_deterministic'` / 定理 `lintegral_deterministic'`

English:
theorem lintegral_deterministic'
  statement: {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [lintegral_dirac' _ hf]

@[simp]

中文:
定理 lintegral_deterministic'
  结论: {f : β -> 实数>=0∞} {g : α -> β} {a : α} (hg : 可测 g)
  证明: by
  rw [deterministic_apply]; rw [lintegral_dirac' _ hf]

@[simp]

Depends on / 依赖: deterministic_apply, lintegral_dirac
-/
theorem lintegral_deterministic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
    (hf : Measurable f) : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply]; rw [lintegral_dirac' _ hf]

@[simp]
/--
theorem `lintegral_deterministic` / 定理 `lintegral_deterministic`

English:
theorem lintegral_deterministic
  statement: {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [lintegral_dirac (g a) f]

中文:
定理 lintegral_deterministic
  结论: {f : β -> 实数>=0∞} {g : α -> β} {a : α} (hg : 可测 g)
  证明: by
  rw [deterministic_apply]; rw [lintegral_dirac (g a) f]

Depends on / 依赖: deterministic_apply, lintegral_dirac
-/
theorem lintegral_deterministic {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply]; rw [lintegral_dirac (g a) f]

/--
theorem `setLIntegral_deterministic'` / 定理 `setLIntegral_deterministic'`

English:
theorem setLIntegral_deterministic'
  statement: {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [setLIntegral_dirac' hf hs]

@[simp]

中文:
定理 setL整数egral_deterministic'
  结论: {f : β -> 实数>=0∞} {g : α -> β} {a : α} (hg : 可测 g)
  证明: by
  rw [deterministic_apply]; rw [setLIntegral_dirac' hf hs]

@[simp]

Depends on / 依赖: deterministic_apply, setLIntegral_dirac
-/
theorem setLIntegral_deterministic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a in s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a in s then f (g a) else 0 := by
  rw [deterministic_apply]; rw [setLIntegral_dirac' hf hs]

@[simp]
/--
theorem `setLIntegral_deterministic` / 定理 `setLIntegral_deterministic`

English:
theorem setLIntegral_deterministic
  statement: {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [setLIntegral_dirac f s]

中文:
定理 setL整数egral_deterministic
  结论: {f : β -> 实数>=0∞} {g : α -> β} {a : α} (hg : 可测 g)
  证明: by
  rw [deterministic_apply]; rw [setLIntegral_dirac f s]

Depends on / 依赖: deterministic_apply, setLIntegral_dirac
-/
theorem setLIntegral_deterministic {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a in s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a in s then f (g a) else 0 := by
  rw [deterministic_apply]; rw [setLIntegral_dirac f s]

end Deterministic

section Id

/-- The identity kernel, that maps `x : α` to the Dirac measure at `x`. -/
protected noncomputable
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Kernel α α
  body: Kernel.deterministic id measurable_id

中文:
定义 id
  签名: : 核 α α
  定义体: Kernel.deterministic id measurable_id

Depends on / 依赖: Kernel, Kernel.deterministic, deterministic, measurable_id
-/
def id : Kernel α α := Kernel.deterministic id measurable_id

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel (Kernel.id : Kernel α α)
  body: by rw [Kernel.id]; infer_instance

中文:
实例 :
  签名: 是MarkovKernel (核.id : 核 α α)
  定义体: by rw [Kernel.id]; infer_instance

Depends on / 依赖: Kernel, Kernel.id, infer_instance
-/
instance : IsMarkovKernel (Kernel.id : Kernel α α) := by rw [Kernel.id]; infer_instance

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (a : α)
  statement: Kernel.id a = Measure.dirac a
  proof: by
  rw [Kernel.id]; rw [deterministic_apply]; rw [id_def]

中文:
引理 id_apply
  条件: (a : α)
  结论: 核.id a = 测度.dirac a
  证明: by
  rw [Kernel.id]; rw [deterministic_apply]; rw [id_def]

Depends on / 依赖: Kernel, Kernel.id, deterministic_apply, id_def
-/
lemma id_apply (a : α) : Kernel.id a = Measure.dirac a := by
  rw [Kernel.id]; rw [deterministic_apply]; rw [id_def]

/--
lemma `lintegral_id'` / 引理 `lintegral_id'`

English:
lemma lintegral_id'
  given: {f : α -> Real>=0∞} (hf : Measurable f) (a : α)
  proof: by
  rw [id_apply]; rw [lintegral_dirac' _ hf]

中文:
引理 lintegral_id'
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (a : α)
  证明: by
  rw [id_apply]; rw [lintegral_dirac' _ hf]

Depends on / 依赖: id_apply, lintegral_dirac
-/
lemma lintegral_id' {f : α -> Real>=0∞} (hf : Measurable f) (a : α) :
    ∫⁻ a, f a ∂(@Kernel.id α mα a) = f a := by
  rw [id_apply]; rw [lintegral_dirac' _ hf]

/--
lemma `lintegral_id` / 引理 `lintegral_id`

English:
lemma lintegral_id
  given: [MeasurableSingletonClass α] {f : α -> Real>=0∞} (a : α)
  proof: by
  rw [id_apply]; rw [lintegral_dirac]

中文:
引理 lintegral_id
  条件: [MeasurableSingleton类 α] {f : α -> 实数>=0∞} (a : α)
  证明: by
  rw [id_apply]; rw [lintegral_dirac]

Depends on / 依赖: id_apply, lintegral_dirac
-/
lemma lintegral_id [MeasurableSingletonClass α] {f : α -> Real>=0∞} (a : α) :
    ∫⁻ a, f a ∂(@Kernel.id α mα a) = f a := by
  rw [id_apply]; rw [lintegral_dirac]

end Id

section Copy

/-- The deterministic kernel that maps `x : α` to the Dirac measure at `(x, x) : α × α`. -/
noncomputable
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (α : Type*) [MeasurableSpace α]
  body: Kernel.deterministic Function.diag (measurable_id.prod measurable_id)

中文:
定义 copy
  签名: (α : 类型) [可测空间 α]
  定义体: Kernel.deterministic Function.diag (measurable_id.prod measurable_id)

Depends on / 依赖: Function, Function.diag, Kernel, Kernel.deterministic, deterministic, measurable_id, measurable_id.prod
-/
def copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α) :=
  Kernel.deterministic Function.diag (measurable_id.prod measurable_id)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel (copy α)
  body: by rw [copy]; infer_instance

中文:
实例 :
  签名: 是MarkovKernel (copy α)
  定义体: by rw [copy]; infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsMarkovKernel (copy α) := by rw [copy]; infer_instance

/--
lemma `copy_apply` / 引理 `copy_apply`

English:
lemma copy_apply
  given: (a : α)
  statement: copy α a = Measure.dirac (a, a)
  proof: by simp [copy, deterministic_apply]

中文:
引理 copy_apply
  条件: (a : α)
  结论: copy α a = 测度.dirac (a, a)
  证明: by simp [copy, deterministic_apply]

Depends on / 依赖: deterministic_apply
-/
lemma copy_apply (a : α) : copy α a = Measure.dirac (a, a) := by simp [copy, deterministic_apply]

end Copy

section Discard

/-- The Markov kernel to the `PUnit` type. -/
noncomputable
/--
Definition of `discard` / `discard` 的定义

English:
definition discard
  signature: (α : Type*) [MeasurableSpace α]
  body: Kernel.deterministic (fun _ => PUnit.unit) measurable_const

中文:
定义 discard
  签名: (α : 类型) [可测空间 α]
  定义体: Kernel.deterministic (fun _ => PUnit.unit) measurable_const

Depends on / 依赖: Kernel, Kernel.deterministic, PUnit.unit, deterministic, measurable_const
-/
def discard (α : Type*) [MeasurableSpace α] : Kernel α PUnit :=
  Kernel.deterministic (fun _ => PUnit.unit) measurable_const

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel (discard α)
  body: by rw [discard]; infer_instance

@[simp]

中文:
实例 :
  签名: 是MarkovKernel (discard α)
  定义体: by rw [discard]; infer_instance

@[simp]

Depends on / 依赖: discard, infer_instance
-/
instance : IsMarkovKernel (discard α) := by rw [discard]; infer_instance

@[simp]
/--
lemma `discard_apply` / 引理 `discard_apply`

English:
lemma discard_apply
  given: (a : α)
  statement: discard α a = Measure.dirac PUnit.unit
  proof: deterministic_apply _ _

中文:
引理 discard_apply
  条件: (a : α)
  结论: discard α a = 测度.dirac 命题单元.unit
  证明: deterministic_apply _ _

Depends on / 依赖: deterministic_apply
-/
lemma discard_apply (a : α) : discard α a = Measure.dirac PUnit.unit := deterministic_apply _ _

end Discard

section Swap

/-- The deterministic kernel that maps `(x, y)` to the Dirac measure at `(y, x)`. -/
noncomputable
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  body: Kernel.deterministic Prod.swap measurable_swap

中文:
定义 swap
  签名: (α β : 类型) [可测空间 α] [可测空间 β]
  定义体: Kernel.deterministic Prod.swap measurable_swap

Depends on / 依赖: Kernel, Kernel.deterministic, Prod.swap, deterministic, measurable_swap
-/
def swap (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Kernel (α × β) (β × α) :=
  Kernel.deterministic Prod.swap measurable_swap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel (swap α β)
  body: by rw [swap]; infer_instance

中文:
实例 :
  签名: 是MarkovKernel (swap α β)
  定义体: by rw [swap]; infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsMarkovKernel (swap α β) := by rw [swap]; infer_instance

/--
lemma `swap_apply` / 引理 `swap_apply`

English:
lemma swap_apply
  given: (ab : α × β)
  statement: swap α β ab = Measure.dirac ab.swap
  proof: by
  rw [swap]; rw [deterministic_apply]

中文:
引理 swap_apply
  条件: (ab : α × β)
  结论: swap α β ab = 测度.dirac ab.swap
  证明: by
  rw [swap]; rw [deterministic_apply]

Depends on / 依赖: deterministic_apply
-/
lemma swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap := by
  rw [swap]; rw [deterministic_apply]

/--
lemma `swap_apply'` / 引理 `swap_apply'`

English:
lemma swap_apply'
  given: (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s)
  proof: by
  rw [swap_apply]; rw [Measure.dirac_apply' _ hs]

中文:
引理 swap_apply'
  条件: (ab : α × β) {s : 集合 (β × α)} (hs : 可测集 s)
  证明: by
  rw [swap_apply]; rw [Measure.dirac_apply' _ hs]

Depends on / 依赖: Measure, Measure.dirac_apply, dirac_apply, swap_apply
-/
lemma swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) :
    swap α β ab s = s.indicator 1 ab.swap := by
  rw [swap_apply]; rw [Measure.dirac_apply' _ hs]

end Swap

section Const

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β)
  body: μβ
  measurable' := measurable_const

@[simp]

中文:
定义 const
  签名: (α : 类型) {β : 类型} [可测空间 α] {_ : 可测空间 β} (μβ : 测度 β)
  定义体: μβ
  measurable' := measurable_const

@[simp]
-/
def const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β) :
    Kernel α β where
  toFun _ := μβ
  measurable' := measurable_const

@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (μβ : Measure β) (a : α)
  statement: const α μβ a = μβ
  proof: rfl

@[simp]

中文:
定理 const_apply
  条件: (μβ : 测度 β) (a : α)
  结论: const α μβ a = μβ
  证明: rfl

@[simp]
-/
theorem const_apply (μβ : Measure β) (a : α) : const α μβ a = μβ :=
  rfl

@[simp]
/--
lemma `const_zero` / 引理 `const_zero`

English:
lemma const_zero
  statement: const α (0 : Measure β) = 0
  proof: by
  ext x s _; simp [const_apply]

中文:
引理 const_zero
  结论: const α (0 : 测度 β) = 0
  证明: by
  ext x s _; simp [const_apply]

Depends on / 依赖: const_apply
-/
lemma const_zero : const α (0 : Measure β) = 0 := by
  ext x s _; simp [const_apply]

/--
lemma `const_add` / 引理 `const_add`

English:
lemma const_add
  given: (β : Type*) [MeasurableSpace β] (μ ν : Measure α)
  proof: by ext; simp

中文:
引理 const_add
  条件: (β : 类型) [可测空间 β] (μ ν : 测度 α)
  证明: by ext; simp
-/
lemma const_add (β : Type*) [MeasurableSpace β] (μ ν : Measure α) :
    const β (μ + ν) = const β μ + const β ν := by ext; simp

/--
lemma `sum_const` / 引理 `sum_const`

English:
lemma sum_const
  given: [Countable ι] (μ : ι -> Measure β)
  proof: rfl

中文:
引理 sum_const
  条件: [可数 ι] (μ : ι -> 测度 β)
  证明: rfl
-/
lemma sum_const [Countable ι] (μ : ι -> Measure β) :
    Kernel.sum (fun n => const α (μ n)) = const α (Measure.sum μ) := rfl

/--
Instance `const.instIsFiniteKernel` / 实例 `const.instIsFiniteKernel`

English:
instance const.instIsFiniteKernel
  signature: {μβ : Measure β} [IsFiniteMeasure μβ]
  body: ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩

中文:
实例 const.instIsFiniteKernel
  签名: {μβ : 测度 β} [是有限测度 μβ]
  定义体: ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩

Depends on / 依赖: Set.univ, le_rfl, measure_lt_top
-/
instance const.instIsFiniteKernel {μβ : Measure β} [IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩

/--
Instance `const.instIsSFiniteKernel` / 实例 `const.instIsSFiniteKernel`

English:
instance const.instIsSFiniteKernel
  signature: {μβ : Measure β} [SFinite μβ]
  body: ⟨fun n => const α (sfiniteSeq μβ n), fun n => inferInstance, by rw [sum_const, sum_sfiniteSeq]⟩

中文:
实例 const.instIsSFiniteKernel
  签名: {μβ : 测度 β} [SFinite μβ]
  定义体: ⟨fun n => const α (sfiniteSeq μβ n), fun n => inferInstance, by rw [sum_const, sum_sfiniteSeq]⟩

Depends on / 依赖: sfiniteSeq, sum_const, sum_sfiniteSeq
-/
instance const.instIsSFiniteKernel {μβ : Measure β} [SFinite μβ] :
    IsSFiniteKernel (const α μβ) :=
  ⟨fun n => const α (sfiniteSeq μβ n), fun n => inferInstance, by rw [sum_const, sum_sfiniteSeq]⟩

/--
Instance `const.instIsMarkovKernel` / 实例 `const.instIsMarkovKernel`

English:
instance const.instIsMarkovKernel
  signature: {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ]
  body: ⟨fun _ => hμβ⟩

中文:
实例 const.instIsMarkovKernel
  签名: {μβ : 测度 β} [hμβ : 是概率测度 μβ]
  定义体: ⟨fun _ => hμβ⟩
-/
instance const.instIsMarkovKernel {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun _ => hμβ⟩

/--
Instance `const.instIsZeroOrMarkovKernel` / 实例 `const.instIsZeroOrMarkovKernel`

English:
instance const.instIsZeroOrMarkovKernel
  signature: {μβ : Measure β} [hμβ : IsZeroOrProbabilityMeasure μβ]
  body: by
  rcases eq_zero_or_isProbabilityMeasure μβ with rfl | h
  · simp only [const_zero]
    infer_instance
  · infer_instance

中文:
实例 const.instIsZeroOrMarkovKernel
  签名: {μβ : 测度 β} [hμβ : 是ZeroOrProbabilityMeasure μβ]
  定义体: by
  rcases eq_zero_or_isProbabilityMeasure μβ with rfl | h
  · simp only [const_zero]
    infer_instance
  · infer_instance

Depends on / 依赖: const_zero, eq_zero_or_isProbabilityMeasure, infer_instance
-/
instance const.instIsZeroOrMarkovKernel {μβ : Measure β} [hμβ : IsZeroOrProbabilityMeasure μβ] :
    IsZeroOrMarkovKernel (const α μβ) := by
  rcases eq_zero_or_isProbabilityMeasure μβ with rfl | h
  · simp only [const_zero]
    infer_instance
  · infer_instance

/--
lemma `isSFiniteKernel_const` / 引理 `isSFiniteKernel_const`

English:
lemma isSFiniteKernel_const
  given: [Nonempty α] {μβ : Measure β}
  proof: ⟨fun h => h.sFinite (Classical.arbitrary α), fun _ => inferInstance⟩

中文:
引理 isSFiniteKernel_const
  条件: [非空 α] {μβ : 测度 β}
  证明: ⟨fun h => h.sFinite (Classical.arbitrary α), fun _ => inferInstance⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, h.sFinite, sFinite
-/
lemma isSFiniteKernel_const [Nonempty α] {μβ : Measure β} :
    IsSFiniteKernel (const α μβ) ↔ SFinite μβ :=
  ⟨fun h => h.sFinite (Classical.arbitrary α), fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: β] : Nonempty {κ
  body: nonempty_subtype.2 ⟨Kernel.const _ (Measure.dirac Classical.ofNonempty), inferInstance⟩

@[simp]

中文:
实例 [非空
  签名: β] : 非空 {κ
  定义体: nonempty_subtype.2 ⟨Kernel.const _ (Measure.dirac Classical.ofNonempty), inferInstance⟩

@[simp]

Depends on / 依赖: Classical, Classical.ofNonempty, Kernel, Kernel.const, Measure, Measure.dirac, nonempty_subtype, ofNonempty
-/
instance [Nonempty β] : Nonempty {κ : Kernel α β // IsMarkovKernel κ} :=
  nonempty_subtype.2 ⟨Kernel.const _ (Measure.dirac Classical.ofNonempty), inferInstance⟩

@[simp]
/--
theorem `lintegral_const` / 定理 `lintegral_const`

English:
theorem lintegral_const
  given: {f : β -> Real>=0∞} {μ : Measure β} {a : α}
  proof: by rw [const_apply]

@[simp]

中文:
定理 lintegral_const
  条件: {f : β -> 实数>=0∞} {μ : 测度 β} {a : α}
  证明: by rw [const_apply]

@[simp]

Depends on / 依赖: const_apply
-/
theorem lintegral_const {f : β -> Real>=0∞} {μ : Measure β} {a : α} :
    ∫⁻ x, f x ∂const α μ a = ∫⁻ x, f x ∂μ := by rw [const_apply]

@[simp]
/--
theorem `setLIntegral_const` / 定理 `setLIntegral_const`

English:
theorem setLIntegral_const
  given: {f : β -> Real>=0∞} {μ : Measure β} {a : α} {s : Set β}
  proof: by rw [const_apply]

中文:
定理 setL整数egral_const
  条件: {f : β -> 实数>=0∞} {μ : 测度 β} {a : α} {s : 集合 β}
  证明: by rw [const_apply]

Depends on / 依赖: const_apply
-/
theorem setLIntegral_const {f : β -> Real>=0∞} {μ : Measure β} {a : α} {s : Set β} :
    ∫⁻ x in s, f x ∂const α μ a = ∫⁻ x in s, f x ∂μ := by rw [const_apply]

/--
lemma `discard_eq_const` / 引理 `discard_eq_const`

English:
lemma discard_eq_const
  statement: discard α = const α (Measure.dirac PUnit.unit)
  proof: rfl

中文:
引理 discard_eq_const
  结论: discard α = const α (测度.dirac 命题单元.unit)
  证明: rfl
-/
lemma discard_eq_const : discard α = const α (Measure.dirac PUnit.unit) := rfl

end Const

/--
Definition of `ofFunOfCountable` / `ofFunOfCountable` 的定义

English:
definition ofFunOfCountable
  signature: [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
  body: f
  measurable' := measurable_of_countable f

中文:
定义 ofFunOfCountable
  签名: [可测空间 α] {_ : 可测空间 β} [可数 α]
  定义体: f
  measurable' := measurable_of_countable f
-/
def ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
    [MeasurableSingletonClass α] (f : α -> Measure β) : Kernel α β where
  toFun := f
  measurable' := measurable_of_countable f

section Restrict

variable {s t : Set β}

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def restrict (κ : Kernel α β) (hs : MeasurableSet s)
  body: (κ a).restrict s
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp_rw [Measure.restrict_apply ht]
    exact Kernel.measurable_coe κ (ht.inter hs)

中文:
定义 noncomputable
  签名: def restrict (κ : 核 α β) (hs : 可测集 s)
  定义体: (κ a).restrict s
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp_rw [Measure.restrict_apply ht]
    exact Kernel.measurable_coe κ (ht.inter hs)
-/
protected noncomputable def restrict (κ : Kernel α β) (hs : MeasurableSet s) : Kernel α β where
  toFun a := (κ a).restrict s
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp_rw [Measure.restrict_apply ht]
    exact Kernel.measurable_coe κ (ht.inter hs)

/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: (κ : Kernel α β) (hs : MeasurableSet s) (a : α)
  proof: rfl

中文:
定理 restrict_apply
  条件: (κ : 核 α β) (hs : 可测集 s) (a : α)
  证明: rfl
-/
theorem restrict_apply (κ : Kernel α β) (hs : MeasurableSet s) (a : α) :
    κ.restrict hs a = (κ a).restrict s :=
  rfl

/--
theorem `restrict_apply'` / 定理 `restrict_apply'`

English:
theorem restrict_apply'
  given: (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t)
  proof: by
  rw [restrict_apply κ hs a]; rw [Measure.restrict_apply ht]

中文:
定理 restrict_apply'
  条件: (κ : 核 α β) (hs : 可测集 s) (a : α) (ht : 可测集 t)
  证明: by
  rw [restrict_apply κ hs a]; rw [Measure.restrict_apply ht]

Depends on / 依赖: Measure, Measure.restrict_apply, restrict_apply
-/
theorem restrict_apply' (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) :
    κ.restrict hs a t = (κ a) (t inter s) := by
  rw [restrict_apply κ hs a]; rw [Measure.restrict_apply ht]

/--
theorem `restrict_const` / 定理 `restrict_const`

English:
theorem restrict_const
  given: {μ : Measure β} (hs : MeasurableSet s)
  proof: by
  ext a
  simp [Kernel.restrict_apply, Kernel.const_apply]

@[simp]

中文:
定理 restrict_const
  条件: {μ : 测度 β} (hs : 可测集 s)
  证明: by
  ext a
  simp [Kernel.restrict_apply, Kernel.const_apply]

@[simp]

Depends on / 依赖: Kernel, Kernel.const_apply, Kernel.restrict_apply, const_apply, restrict_apply
-/
theorem restrict_const {μ : Measure β} (hs : MeasurableSet s) :
    (Kernel.const α μ).restrict hs = Kernel.const α (μ.restrict s) := by
  ext a
  simp [Kernel.restrict_apply, Kernel.const_apply]

@[simp]
/--
theorem `restrict_univ` / 定理 `restrict_univ`

English:
theorem restrict_univ
  statement: κ.restrict MeasurableSet.univ = κ
  proof: by
  ext1 a
  rw [Kernel.restrict_apply]; rw [Measure.restrict_univ]

@[simp]

中文:
定理 restrict_univ
  结论: κ.restrict 可测集.univ = κ
  证明: by
  ext1 a
  rw [Kernel.restrict_apply]; rw [Measure.restrict_univ]

@[simp]

Depends on / 依赖: Kernel, Kernel.restrict_apply, Measure, Measure.restrict_univ, restrict_apply, restrict_univ
-/
theorem restrict_univ : κ.restrict MeasurableSet.univ = κ := by
  ext1 a
  rw [Kernel.restrict_apply]; rw [Measure.restrict_univ]

@[simp]
/--
theorem `lintegral_restrict` / 定理 `lintegral_restrict`

English:
theorem lintegral_restrict
  given: (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β -> Real>=0∞)
  proof: by rw [restrict_apply]

@[simp]

中文:
定理 lintegral_restrict
  条件: (κ : 核 α β) (hs : 可测集 s) (a : α) (f : β -> 实数>=0∞)
  证明: by rw [restrict_apply]

@[simp]

Depends on / 依赖: restrict_apply
-/
theorem lintegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β -> Real>=0∞) :
    ∫⁻ b, f b ∂κ.restrict hs a = ∫⁻ b in s, f b ∂κ a := by rw [restrict_apply]

@[simp]
/--
theorem `setLIntegral_restrict` / 定理 `setLIntegral_restrict`

English:
theorem setLIntegral_restrict
  statement: (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β -> Real>=0∞)
  proof: by
  rw [restrict_apply]; rw [Measure.restrict_restrict' hs]

中文:
定理 setL整数egral_restrict
  结论: (κ : 核 α β) (hs : 可测集 s) (a : α) (f : β -> 实数>=0∞)
  证明: by
  rw [restrict_apply]; rw [Measure.restrict_restrict' hs]

Depends on / 依赖: Measure, Measure.restrict_restrict, restrict_apply, restrict_restrict
-/
theorem setLIntegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β -> Real>=0∞)
    (t : Set β) : ∫⁻ b in t, f b ∂κ.restrict hs a = ∫⁻ b in t inter s, f b ∂κ a := by
  rw [restrict_apply]; rw [Measure.restrict_restrict' hs]


/--
Instance `IsFiniteKernel.restrict` / 实例 `IsFiniteKernel.restrict`

English:
instance IsFiniteKernel.restrict
  signature: (κ : Kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s)
  body: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _

中文:
实例 是FiniteKernel.restrict
  签名: (κ : 核 α β) [是FiniteKernel κ] (hs : 可测集 s)
  定义体: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, bound_lt_top, measure_le_bound, restrict_apply
-/
instance IsFiniteKernel.restrict (κ : Kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (κ.restrict hs) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _

/--
Instance `IsSFiniteKernel.restrict` / 实例 `IsSFiniteKernel.restrict`

English:
instance IsSFiniteKernel.restrict
  signature: (κ : Kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s)
  body: by
  refine ⟨⟨fun n => Kernel.restrict (seq κ n) hs, inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← Measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]

中文:
实例 是SFiniteKernel.restrict
  签名: (κ : 核 α β) [是SFiniteKernel κ] (hs : 可测集 s)
  定义体: by
  refine ⟨⟨fun n => Kernel.restrict (seq κ n) hs, inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← Measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]

Depends on / 依赖: Kernel, Kernel.restrict, Measure, Measure.restrict_sum, kernel_sum_seq, restrict, restrict_apply, restrict_sum, simp_rw, sum_apply
-/
instance IsSFiniteKernel.restrict (κ : Kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    IsSFiniteKernel (κ.restrict hs) := by
  refine ⟨⟨fun n => Kernel.restrict (seq κ n) hs, inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← Measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]

end Restrict

section ComapRight

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : γ -> β}

/--
Definition of `comapRight` / `comapRight` 的定义

English:
definition comapRight
  signature: (κ : Kernel α β) (hf : MeasurableEmbedding f)
  body: (κ a).comap f
  measurable' := by
    refine Measure.measurable_measure.mpr fun t ht => ?_
    have : (fun a => Measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [Measure.comap_apply _ hf.injective _ _ ht]
      exact fun s' hs' => hf.measurableSet_image.mpr hs'
    rw [th

中文:
定义 comapRight
  签名: (κ : 核 α β) (hf : 可测嵌入 f)
  定义体: (κ a).comap f
  measurable' := by
    refine Measure.measurable_measure.mpr fun t ht => ?_
    have : (fun a => Measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [Measure.comap_apply _ hf.injective _ _ ht]
      exact fun s' hs' => hf.measurableSet_image.mpr hs'
    rw [th
-/
noncomputable def comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f) : Kernel α γ where
  toFun a := (κ a).comap f
  measurable' := by
    refine Measure.measurable_measure.mpr fun t ht => ?_
    have : (fun a => Measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [Measure.comap_apply _ hf.injective _ _ ht]
      exact fun s' hs' => hf.measurableSet_image.mpr hs'
    rw [this]
    exact Kernel.measurable_coe _ (hf.measurableSet_image.mpr ht)

/--
theorem `comapRight_apply` / 定理 `comapRight_apply`

English:
theorem comapRight_apply
  given: (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α)
  proof: rfl

中文:
定理 comapRight_apply
  条件: (κ : 核 α β) (hf : 可测嵌入 f) (a : α)
  证明: rfl
-/
theorem comapRight_apply (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) :
    comapRight κ hf a = Measure.comap f (κ a) :=
  rfl

/--
theorem `comapRight_apply'` / 定理 `comapRight_apply'`

English:
theorem comapRight_apply'
  statement: (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ}
  proof: by
  rw [comapRight_apply]; rw [Measure.comap_apply _ hf.injective (fun s => hf.measurableSet_image.mpr) _ ht]

@[simp]

中文:
定理 comapRight_apply'
  结论: (κ : 核 α β) (hf : 可测嵌入 f) (a : α) {t : 集合 γ}
  证明: by
  rw [comapRight_apply]; rw [Measure.comap_apply _ hf.injective (fun s => hf.measurableSet_image.mpr) _ ht]

@[simp]

Depends on / 依赖: Measure, Measure.comap_apply, comapRight_apply, comap_apply, hf.injective, hf.measurableSet_image.mpr, injective, measurableSet_image
-/
theorem comapRight_apply' (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ}
    (ht : MeasurableSet t) : comapRight κ hf a t = κ a (f '' t) := by
  rw [comapRight_apply]; rw [Measure.comap_apply _ hf.injective (fun s => hf.measurableSet_image.mpr) _ ht]

@[simp]
/--
lemma `comapRight_id` / 引理 `comapRight_id`

English:
lemma comapRight_id
  given: (κ : Kernel α β)
  statement: comapRight κ MeasurableEmbedding.id = κ
  proof: by
  ext _ _ hs; rw [comapRight_apply' _ _ _ hs]; simp

中文:
引理 comapRight_id
  条件: (κ : 核 α β)
  结论: comapRight κ 可测嵌入.id = κ
  证明: by
  ext _ _ hs; rw [comapRight_apply' _ _ _ hs]; simp

Depends on / 依赖: comapRight_apply
-/
lemma comapRight_id (κ : Kernel α β) : comapRight κ MeasurableEmbedding.id = κ := by
  ext _ _ hs; rw [comapRight_apply' _ _ _ hs]; simp

/--
theorem `IsMarkovKernel.comapRight` / 定理 `IsMarkovKernel.comapRight`

English:
theorem IsMarkovKernel.comapRight
  statement: (κ : Kernel α β) (hf : MeasurableEmbedding f)
  proof: by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [comapRight_apply' κ hf a MeasurableSet.univ]
  simp only [Set.image_univ]
  exact hκ a

中文:
定理 是MarkovKernel.comapRight
  结论: (κ : 核 α β) (hf : 可测嵌入 f)
  证明: by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [comapRight_apply' κ hf a MeasurableSet.univ]
  simp only [Set.image_univ]
  exact hκ a

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.image_univ, comapRight_apply, image_univ
-/
theorem IsMarkovKernel.comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f)
    (hκ : forall a, κ a (Set.range f) = 1) : IsMarkovKernel (comapRight κ hf) := by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [comapRight_apply' κ hf a MeasurableSet.univ]
  simp only [Set.image_univ]
  exact hκ a

/--
Instance `IsFiniteKernel.comapRight` / 实例 `IsFiniteKernel.comapRight`

English:
instance IsFiniteKernel.comapRight
  signature: (κ : Kernel α β) [IsFiniteKernel κ]
  body: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comapRight_apply' κ hf a .univ]
  exact measure_le_bound κ a _

中文:
实例 是FiniteKernel.comapRight
  签名: (κ : 核 α β) [是FiniteKernel κ]
  定义体: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comapRight_apply' κ hf a .univ]
  exact measure_le_bound κ a _

Depends on / 依赖: bound_lt_top, comapRight_apply, measure_le_bound
-/
instance IsFiniteKernel.comapRight (κ : Kernel α β) [IsFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsFiniteKernel (comapRight κ hf) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comapRight_apply' κ hf a .univ]
  exact measure_le_bound κ a _

/--
Instance `IsSFiniteKernel.comapRight` / 实例 `IsSFiniteKernel.comapRight`

English:
instance IsSFiniteKernel.comapRight
  signature: (κ : Kernel α β) [IsSFiniteKernel κ]
  body: by
  refine ⟨⟨fun n => comapRight (seq κ n) hf, inferInstance, ?_⟩⟩
  ext1 a
  rw [sum_apply]
  simp_rw [comapRight_apply _ hf]
  have :
    (Measure.sum fun n => Measure.comap f (seq κ n a)) =
      Measure.comap f (Measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [Measure.comap_apply _ h

中文:
实例 是SFiniteKernel.comapRight
  签名: (κ : 核 α β) [是SFiniteKernel κ]
  定义体: by
  refine ⟨⟨fun n => comapRight (seq κ n) hf, inferInstance, ?_⟩⟩
  ext1 a
  rw [sum_apply]
  simp_rw [comapRight_apply _ hf]
  have :
    (Measure.sum fun n => Measure.comap f (seq κ n a)) =
      Measure.comap f (Measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [Measure.comap_apply _ h
-/
protected instance IsSFiniteKernel.comapRight (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsSFiniteKernel (comapRight κ hf) := by
  refine ⟨⟨fun n => comapRight (seq κ n) hf, inferInstance, ?_⟩⟩
  ext1 a
  rw [sum_apply]
  simp_rw [comapRight_apply _ hf]
  have :
    (Measure.sum fun n => Measure.comap f (seq κ n a)) =
      Measure.comap f (Measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht]; rw [Measure.sum_apply _ ht]; rw [Measure.sum_apply _ (hf.measurableSet_image.mpr ht)]
    congr with n : 1
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht]
  rw [this]; rw [measure_sum_seq]

end ComapRight

section Piecewise

variable {η : Kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· in s)]

/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: (hs : MeasurableSet s) (κ η : Kernel α β)
  body: if a in s then κ a else η a
  measurable' := κ.measurable.piecewise hs η.measurable

中文:
定义 piecewise
  签名: (hs : 可测集 s) (κ η : 核 α β)
  定义体: if a in s then κ a else η a
  measurable' := κ.measurable.piecewise hs η.measurable
-/
def piecewise (hs : MeasurableSet s) (κ η : Kernel α β) : Kernel α β where
  toFun a := if a in s then κ a else η a
  measurable' := κ.measurable.piecewise hs η.measurable

/--
theorem `piecewise_apply` / 定理 `piecewise_apply`

English:
theorem piecewise_apply
  given: (a : α)
  statement: piecewise hs κ η a = if a in s then κ a else η a
  proof: rfl

中文:
定理 piecewise_apply
  条件: (a : α)
  结论: piecewise hs κ η a = if a in s then κ a else η a
  证明: rfl
-/
theorem piecewise_apply (a : α) : piecewise hs κ η a = if a in s then κ a else η a :=
  rfl

/--
theorem `piecewise_apply'` / 定理 `piecewise_apply'`

English:
theorem piecewise_apply'
  given: (a : α) (t : Set β)
  proof: by
  rw [piecewise_apply]; split_ifs <;> rfl

中文:
定理 piecewise_apply'
  条件: (a : α) (t : 集合 β)
  证明: by
  rw [piecewise_apply]; split_ifs <;> rfl

Depends on / 依赖: piecewise_apply, split_ifs
-/
theorem piecewise_apply' (a : α) (t : Set β) :
    piecewise hs κ η a t = if a in s then κ a t else η a t := by
  rw [piecewise_apply]; split_ifs <;> rfl

/--
Instance `IsMarkovKernel.piecewise` / 实例 `IsMarkovKernel.piecewise`

English:
instance IsMarkovKernel.piecewise
  signature: [IsMarkovKernel κ] [IsMarkovKernel η]
  body: by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [piecewise_apply']; rw [measure_univ]; rw [measure_univ]; rw [ite_self]

中文:
实例 是MarkovKernel.piecewise
  签名: [是MarkovKernel κ] [是MarkovKernel η]
  定义体: by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [piecewise_apply']; rw [measure_univ]; rw [measure_univ]; rw [ite_self]

Depends on / 依赖: ite_self, measure_univ, piecewise_apply
-/
instance IsMarkovKernel.piecewise [IsMarkovKernel κ] [IsMarkovKernel η] :
    IsMarkovKernel (piecewise hs κ η) := by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [piecewise_apply']; rw [measure_univ]; rw [measure_univ]; rw [ite_self]

/--
Instance `IsFiniteKernel.piecewise` / 实例 `IsFiniteKernel.piecewise`

English:
instance IsFiniteKernel.piecewise
  signature: [IsFiniteKernel κ] [IsFiniteKernel η]
  body: by
  refine ⟨⟨max κ.bound η.bound, max_lt κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  rw [piecewise_apply']
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))

中文:
实例 是FiniteKernel.piecewise
  签名: [是FiniteKernel κ] [是FiniteKernel η]
  定义体: by
  refine ⟨⟨max κ.bound η.bound, max_lt κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  rw [piecewise_apply']
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))

Depends on / 依赖: bound_lt_top, ite_le_sup, max_lt, measure_le_bound, piecewise_apply, sup_le_sup
-/
instance IsFiniteKernel.piecewise [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (piecewise hs κ η) := by
  refine ⟨⟨max κ.bound η.bound, max_lt κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  rw [piecewise_apply']
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))

/--
Instance `IsSFiniteKernel.piecewise` / 实例 `IsSFiniteKernel.piecewise`

English:
instance IsSFiniteKernel.piecewise
  signature: [IsSFiniteKernel κ] [IsSFiniteKernel η]
  body: by
  refine ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, Kernel.piecewise_apply]
  split_ifs <;> exact (measure_sum_seq _ a).symm

中文:
实例 是SFiniteKernel.piecewise
  签名: [是SFiniteKernel κ] [是SFiniteKernel η]
  定义体: by
  refine ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, Kernel.piecewise_apply]
  split_ifs <;> exact (measure_sum_seq _ a).symm
-/
protected instance IsSFiniteKernel.piecewise [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (piecewise hs κ η) := by
  refine ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, Kernel.piecewise_apply]
  split_ifs <;> exact (measure_sum_seq _ a).symm

/--
theorem `lintegral_piecewise` / 定理 `lintegral_piecewise`

English:
theorem lintegral_piecewise
  given: (a : α) (g : β -> Real>=0∞)
  proof: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

中文:
定理 lintegral_piecewise
  条件: (a : α) (g : β -> 实数>=0∞)
  证明: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

Depends on / 依赖: piecewise_apply, simp_rw, split_ifs
-/
theorem lintegral_piecewise (a : α) (g : β -> Real>=0∞) :
    ∫⁻ b, g b ∂piecewise hs κ η a = if a in s then ∫⁻ b, g b ∂κ a else ∫⁻ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

/--
theorem `setLIntegral_piecewise` / 定理 `setLIntegral_piecewise`

English:
theorem setLIntegral_piecewise
  given: (a : α) (g : β -> Real>=0∞) (t : Set β)
  proof: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

中文:
定理 setL整数egral_piecewise
  条件: (a : α) (g : β -> 实数>=0∞) (t : 集合 β)
  证明: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

Depends on / 依赖: piecewise_apply, simp_rw, split_ifs
-/
theorem setLIntegral_piecewise (a : α) (g : β -> Real>=0∞) (t : Set β) :
    ∫⁻ b in t, g b ∂piecewise hs κ η a =
      if a in s then ∫⁻ b in t, g b ∂κ a else ∫⁻ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

end Piecewise

/--
lemma `exists_ae_eq_isMarkovKernel` / 引理 `exists_ae_eq_isMarkovKernel`

English:
lemma exists_ae_eq_isMarkovKernel
  statement: {μ : Measure α}
  proof: by
  classical
  obtain ⟨s, s_meas, μs, hs⟩ : exists s, MeasurableSet s ∧ μ s = 0
      ∧ forall a ∉ s, IsProbabilityMeasure (κ a) := by
    refine ⟨toMeasurable μ {a | ¬ IsProbabilityMeasure (κ a)}, measurableSet_toMeasurable _ _,
      by simpa [measure_toMeasurable] using! h, ?_⟩
    intro a ha
 

中文:
引理 存在_ae_eq_isMarkovKernel
  结论: {μ : 测度 α}
  证明: by
  classical
  obtain ⟨s, s_meas, μs, hs⟩ : exists s, MeasurableSet s ∧ μ s = 0
      ∧ forall a ∉ s, IsProbabilityMeasure (κ a) := by
    refine ⟨toMeasurable μ {a | ¬ IsProbabilityMeasure (κ a)}, measurableSet_toMeasurable _ _,
      by simpa [measure_toMeasurable] using! h, ?_⟩
    intro a ha
 

Depends on / 依赖: IsProbabilityMeasure, Kernel, Kernel.const, Kernel.piecewise, MeasurableSet, Nonempty, classical, contrapose, measurableSet_toMeasurable, measure_toMeasurable, measure_univ_le_add_compl, piecewise, s_meas, subset_toMeasurable, toMeasurable
-/
lemma exists_ae_eq_isMarkovKernel {μ : Measure α}
    (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ != 0) :
    exists (η : Kernel α β), (κ =ᵐ[μ] η) ∧ IsMarkovKernel η := by
  classical
  obtain ⟨s, s_meas, μs, hs⟩ : exists s, MeasurableSet s ∧ μ s = 0
      ∧ forall a ∉ s, IsProbabilityMeasure (κ a) := by
    refine ⟨toMeasurable μ {a | ¬ IsProbabilityMeasure (κ a)}, measurableSet_toMeasurable _ _,
      by simpa [measure_toMeasurable] using! h, ?_⟩
    intro a ha
    contrapose ha
    exact subset_toMeasurable _ _ ha
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := by
    contrapose! h'; simpa [μs, h'] using! measure_univ_le_add_compl s (μ := μ)
  refine ⟨Kernel.piecewise s_meas (Kernel.const _ (κ a)) κ, ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 μs] with b hb
    simp [hb, piecewise]
  · refine ⟨fun b => ?_⟩
    by_cases hb : b in s
    · simpa [hb, piecewise] using! hs _ ha
    · simpa [hb, piecewise] using! hs _ hb

section Bool

variable {μ ν : Measure α}

/--
Definition of `boolKernel` / `boolKernel` 的定义

English:
definition boolKernel
  signature: (μ ν : Measure α)
  body: fun b => if b then ν else μ
  measurable' := .of_discrete

中文:
定义 boolKernel
  签名: (μ ν : 测度 α)
  定义体: fun b => if b then ν else μ
  measurable' := .of_discrete
-/
def boolKernel (μ ν : Measure α) : Kernel Bool α where
  toFun := fun b => if b then ν else μ
  measurable' := .of_discrete

/--
lemma `boolKernel_false` / 引理 `boolKernel_false`

English:
lemma boolKernel_false
  statement: boolKernel μ ν false = μ
  proof: rfl

中文:
引理 boolKernel_false
  结论: boolKernel μ ν false = μ
  证明: rfl
-/
lemma boolKernel_false : boolKernel μ ν false = μ := rfl

/--
lemma `boolKernel_true` / 引理 `boolKernel_true`

English:
lemma boolKernel_true
  statement: boolKernel μ ν true = ν
  proof: rfl

中文:
引理 boolKernel_true
  结论: boolKernel μ ν true = ν
  证明: rfl
-/
lemma boolKernel_true : boolKernel μ ν true = ν := rfl

/--
lemma `boolKernel_apply` / 引理 `boolKernel_apply`

English:
lemma boolKernel_apply
  given: (b : Bool)
  statement: boolKernel μ ν b = if b then ν else μ
  proof: rfl

中文:
引理 boolKernel_apply
  条件: (b : 布尔值)
  结论: boolKernel μ ν b = if b then ν else μ
  证明: rfl
-/
@[simp] lemma boolKernel_apply (b : Bool) : boolKernel μ ν b = if b then ν else μ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ] [IsFiniteMeasure ν] : IsFiniteKernel (boolKernel μ ν)
  body: ⟨max (μ .univ) (ν .univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
    fun b => by cases b <;> simp⟩

中文:
实例 [是有限测度
  签名: μ] [是有限测度 ν] : 是FiniteKernel (boolKernel μ ν)
  定义体: ⟨max (μ .univ) (ν .univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
    fun b => by cases b <;> simp⟩

Depends on / 依赖: max_lt, measure_lt_top
-/
instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteKernel (boolKernel μ ν) :=
  ⟨max (μ .univ) (ν .univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
    fun b => by cases b <;> simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsProbabilityMeasure
  signature: μ] [IsProbabilityMeasure ν] : IsMarkovKernel (boolKernel μ ν) where
  body: by
    cases b
      <;> simp only [boolKernel_apply, Bool.false_eq_true, ↓reduceIte]
      <;> infer_instance

中文:
实例 [是概率测度
  签名: μ] [是概率测度 ν] : 是MarkovKernel (boolKernel μ ν) where
  定义体: by
    cases b
      <;> simp only [boolKernel_apply, Bool.false_eq_true, ↓reduceIte]
      <;> infer_instance

Depends on / 依赖: Bool.false_eq_true, boolKernel_apply, false_eq_true, infer_instance, reduceIte
-/
instance [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsMarkovKernel (boolKernel μ ν) where
  isProbabilityMeasure b := by
    cases b
      <;> simp only [boolKernel_apply, Bool.false_eq_true, ↓reduceIte]
      <;> infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] [SFinite ν] : IsSFiniteKernel (boolKernel μ ν) where
  body: by
    refine ⟨fun n => boolKernel (sfiniteSeq μ n) (sfiniteSeq ν n), fun n => inferInstance, ?_⟩
    ext b
    rw [Kernel.sum_apply]
    cases b <;> simp [sum_sfiniteSeq]

中文:
实例 [SFinite
  签名: μ] [SFinite ν] : 是SFiniteKernel (boolKernel μ ν) where
  定义体: by
    refine ⟨fun n => boolKernel (sfiniteSeq μ n) (sfiniteSeq ν n), fun n => inferInstance, ?_⟩
    ext b
    rw [Kernel.sum_apply]
    cases b <;> simp [sum_sfiniteSeq]

Depends on / 依赖: Kernel, Kernel.sum_apply, boolKernel, sfiniteSeq, sum_apply, sum_sfiniteSeq
-/
instance [SFinite μ] [SFinite ν] : IsSFiniteKernel (boolKernel μ ν) where
  tsum_finite := by
    refine ⟨fun n => boolKernel (sfiniteSeq μ n) (sfiniteSeq ν n), fun n => inferInstance, ?_⟩
    ext b
    rw [Kernel.sum_apply]
    cases b <;> simp [sum_sfiniteSeq]

/--
lemma `eq_boolKernel` / 引理 `eq_boolKernel`

English:
lemma eq_boolKernel
  given: (κ : Kernel Bool α)
  statement: κ = boolKernel (κ false) (κ true)
  proof: by
  ext (_ | _) <;> simp

中文:
引理 eq_boolKernel
  条件: (κ : 核 布尔值 α)
  结论: κ = boolKernel (κ false) (κ true)
  证明: by
  ext (_ | _) <;> simp
-/
lemma eq_boolKernel (κ : Kernel Bool α) : κ = boolKernel (κ false) (κ true) := by
  ext (_ | _) <;> simp

end Bool

end Kernel
end ProbabilityTheory
