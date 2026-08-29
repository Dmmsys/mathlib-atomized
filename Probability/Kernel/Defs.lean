/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → MeasureTheory.Measure β`, where the measurable space instance on `measure β` is the one defined
in `MeasureTheory.Measure.instMeasurableSpace`. That is, a kernel `κ` verifies that for all
measurable sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `ProbabilityTheory.Kernel α β`: kernels from `α` to `β`.
* `ProbabilityTheory.IsMarkovKernel κ`: a kernel from `α` to `β` is said to be a Markov kernel
  if for all `a : α`, `k a` is a probability measure.
* `ProbabilityTheory.IsZeroOrMarkovKernel κ`: a kernel from `α` to `β` which is zero or
  a Markov kernel.
* `ProbabilityTheory.IsFiniteKernel κ`: a kernel from `α` to `β` is said to be finite if there
  exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
  particular that all measures in the image of `κ` are finite, but is stronger since it requires a
  uniform bound. This stronger condition is necessary to ensure that the composition of two finite
  kernels is finite.
* `ProbabilityTheory.IsSFiniteKernel κ`: a kernel is called s-finite if it is a countable
  sum of finite kernels.

## Main statements

* `ProbabilityTheory.Kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/

@[expose] public section

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

/--
Definition of `Kernel` / `Kernel` 的定义

English:
structure Kernel
  parameters: (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  axioms and operations (2):
    - toFun : α -> Measure β
    - measurable' : Measurable toFun

中文:
结构 核
  参数: (α β : 类型) [可测空间 α] [可测空间 β]
  公理与运算 (2 个):
    - toFun : α -> 测度 β
    - measurable' : 可测 toFun
-/
structure Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- The underlying function of a kernel.

  Do not use this function directly. Instead use the coercion coming from the `DFunLike`
  instance. -/
  toFun : α -> Measure β
  /-- A kernel is a measurable map.

  Do not use this lemma directly. Use `Kernel.measurable` instead. -/
  measurable' : Measurable toFun

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Kernel[" mα "] " α:arg β:arg => @Kernel α β mα _

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain and codomain. -/
scoped notation "Kernel[" mα ", " mβ "] " α:arg β:arg => @Kernel α β mα mβ

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Kernel α β) α (Measure β) where
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

@[fun_prop]

中文:
实例 instFunLike
  签名: : 函数状 (核 α β) α (测度 β) where
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr

@[fun_prop]
-/
instance instFunLike : FunLike (Kernel α β) α (Measure β) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[fun_prop]
/--
lemma `measurable` / 引理 `measurable`

English:
lemma measurable
  given: (κ : Kernel α β)
  statement: Measurable κ
  proof: κ.measurable'

中文:
引理 measurable
  条件: (κ : 核 α β)
  结论: 可测 κ
  证明: κ.measurable'

Depends on / 依赖: measurable
-/
lemma measurable (κ : Kernel α β) : Measurable κ := κ.measurable'

/--
lemma `aemeasurable` / 引理 `aemeasurable`

English:
lemma aemeasurable
  given: (κ : Kernel α β) {μ : Measure α}
  statement: AEMeasurable κ μ
  proof: κ.measurable.aemeasurable

中文:
引理 aemeasurable
  条件: (κ : 核 α β) {μ : 测度 α}
  结论: 几乎处处可测 κ μ
  证明: κ.measurable.aemeasurable

Depends on / 依赖: aemeasurable, measurable, measurable.aemeasurable
-/
lemma aemeasurable (κ : Kernel α β) {μ : Measure α} : AEMeasurable κ μ := κ.measurable.aemeasurable

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : α -> Measure β) (hf)
  statement: mk f hf = f
  proof: rfl

initialize_simps_projections Kernel (toFun -> apply)

中文:
引理 coe_mk
  条件: (f : α -> 测度 β) (hf)
  结论: mk f hf = f
  证明: rfl

initialize_simps_projections Kernel (toFun -> apply)
-/
@[simp, norm_cast] lemma coe_mk (f : α -> Measure β) (hf) : mk f hf = f := rfl

initialize_simps_projections Kernel (toFun -> apply)

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (Kernel α β) where zero
  body: ⟨0, measurable_zero⟩

中文:
实例 instZero
  签名: : 零 (核 α β) where zero
  定义体: ⟨0, measurable_zero⟩

Depends on / 依赖: measurable_zero
-/
instance instZero : Zero (Kernel α β) where zero := ⟨0, measurable_zero⟩
/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (Kernel α β) where add κ η
  body: ⟨κ + η, κ.2.add η.2⟩

中文:
实例 instAdd
  签名: : 加法 (核 α β) where add κ η
  定义体: ⟨κ + η, κ.2.add η.2⟩
-/
noncomputable instance instAdd : Add (Kernel α β) where add κ η := ⟨κ + η, κ.2.add η.2⟩
/--
Instance `instSMulNat` / 实例 `instSMulNat`

English:
instance instSMulNat
  signature: : SMul Nat (Kernel α β) where
  body: ⟨n • κ, (measurable_const (a := n)).smul κ.2⟩

中文:
实例 instSMul自然数
  签名: : 标量乘法 自然数 (核 α β) where
  定义体: ⟨n • κ, (measurable_const (a := n)).smul κ.2⟩

Depends on / 依赖: measurable_const
-/
noncomputable instance instSMulNat : SMul Nat (Kernel α β) where
  smul n κ := ⟨n • κ, (measurable_const (a := n)).smul κ.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (Kernel α β) α (Measure β)
  body: rfl

中文:
实例 :
  签名: 是ZeroApply (核 α β) α (测度 β)
  定义体: rfl
-/
instance : IsZeroApply (Kernel α β) α (Measure β) where
  zero_apply _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (Kernel α β) α (Measure β)
  body: rfl

中文:
实例 :
  签名: 是加法Apply (核 α β) α (测度 β)
  定义体: rfl
-/
instance : IsAddApply (Kernel α β) α (Measure β) where
  add_apply _ _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply Nat (Kernel α β) α (Measure β)
  body: rfl

@[deprecated (since := "2026-06-30")] alias coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-06-30")] alias coe_add := FunLike.coe_add
@[deprecated (since := "2026-06-30")] alias coe_nsmul := FunLike.coe_smul

@[deprecated (since := "2026-06-30")] protected alias zero_apply := zero_app

中文:
实例 :
  签名: 是SMulApply 自然数 (核 α β) α (测度 β)
  定义体: rfl

@[deprecated (since := "2026-06-30")] alias coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-06-30")] alias coe_add := FunLike.coe_add
@[deprecated (since := "2026-06-30")] alias coe_nsmul := FunLike.coe_smul

@[deprecated (since := "2026-06-30")] protected alias zero_apply := zero_app
-/
instance : IsSMulApply Nat (Kernel α β) α (Measure β) where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-30")] alias coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-06-30")] alias coe_add := FunLike.coe_add
@[deprecated (since := "2026-06-30")] alias coe_nsmul := FunLike.coe_smul

@[deprecated (since := "2026-06-30")] protected alias zero_apply := zero_apply
@[deprecated (since := "2026-06-30")] protected alias add_apply := add_apply
@[deprecated (since := "2026-06-30")] protected alias nsmul_apply := smul_apply

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (Kernel α β)
  body: fast_instance% FunLike.addCommMonoid

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (核 α β)
  定义体: fast_instance% FunLike.addCommMonoid

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
noncomputable instance instAddCommMonoid : AddCommMonoid (Kernel α β) :=
  fast_instance% FunLike.addCommMonoid

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Kernel α β)
  body: .lift _ DFunLike.coe_injective

中文:
实例 instPartialOrder
  签名: : 偏序 (核 α β)
  定义体: .lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
instance instPartialOrder : PartialOrder (Kernel α β) := .lift _ DFunLike.coe_injective

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    AddLeftMono (Kernel α β) :=
  ⟨fun _ _ _ hμ a => add_le_add_right (hμ a) _⟩

noncomputable
/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  body: 0
  bot_le κ a := by simp only [zero_apply, Measure.zero_le]

@[deprecated (since := "2026-06-30")] alias coeAddHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-30")] alias coeAddHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-30")] alias coe_finsetSum 

中文:
实例 instOrderBot
  签名: {α β : 类型} [可测空间 α] [可测空间 β]
  定义体: 0
  bot_le κ a := by simp only [zero_apply, Measure.zero_le]

@[deprecated (since := "2026-06-30")] alias coeAddHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-30")] alias coeAddHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-30")] alias coe_finsetSum 
-/
instance instOrderBot {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    OrderBot (Kernel α β) where
  bot := 0
  bot_le κ a := by simp only [zero_apply, Measure.zero_le]

@[deprecated (since := "2026-06-30")] alias coeAddHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-30")] alias coeAddHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-30")] alias coe_finsetSum := FunLike.coe_sum

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := FunLike.coe_sum

@[deprecated (since := "2026-06-30")] alias finsetSum_apply := sum_apply

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := sum_apply

/--
theorem `finsetSum_apply'` / 定理 `finsetSum_apply'`

English:
theorem finsetSum_apply'
  given: (I : Finset ι) (κ : ι -> Kernel α β) (a : α) (s : Set β)
  proof: by rw [sum_apply, Measure.finsetSum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply' := finsetSum_apply'

中文:
定理 finsetSum_apply'
  条件: (I : 有限集 ι) (κ : ι -> 核 α β) (a : α) (s : 集合 β)
  证明: by rw [sum_apply, Measure.finsetSum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply' := finsetSum_apply'

Depends on / 依赖: Measure, Measure.finsetSum_apply, finsetSum_apply, sum_apply
-/
theorem finsetSum_apply' (I : Finset ι) (κ : ι -> Kernel α β) (a : α) (s : Set β) :
    (∑ i in I, κ i) a s = ∑ i in I, κ i a s := by rw [sum_apply, Measure.finsetSum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply' := finsetSum_apply'

end Kernel

/--
Definition of `IsMarkovKernel` / `IsMarkovKernel` 的定义

English:
class IsMarkovKernel
  parameters: (κ : Kernel α β)
  axioms and operations (1):
    - isProbabilityMeasure : forall a, IsProbabilityMeasure (κ a)

中文:
类 是MarkovKernel
  参数: (κ : 核 α β)
  公理与运算 (1 个):
    - isProbabilityMeasure : 对任意 a, 是概率测度 (κ a)
-/
class IsMarkovKernel (κ : Kernel α β) : Prop where
  isProbabilityMeasure : forall a, IsProbabilityMeasure (κ a)

/--
Definition of `IsZeroOrMarkovKernel` / `IsZeroOrMarkovKernel` 的定义

English:
class IsZeroOrMarkovKernel
  parameters: (κ : Kernel α β)
  axioms and operations (1):
    - eq_zero_or_isMarkovKernel' : κ = 0 ∨ IsMarkovKernel κ

中文:
类 是ZeroOrMarkovKernel
  参数: (κ : 核 α β)
  公理与运算 (1 个):
    - eq_zero_or_isMarkovKernel' : κ = 0 ∨ 是MarkovKernel κ
-/
class IsZeroOrMarkovKernel (κ : Kernel α β) : Prop where
  eq_zero_or_isMarkovKernel' : κ = 0 ∨ IsMarkovKernel κ

/--
Definition of `IsFiniteKernel` / `IsFiniteKernel` 的定义

English:
class IsFiniteKernel
  parameters: (κ : Kernel α β)
  axioms and operations (1):
    - exists_univ_le : exists C : Real>=0∞, C < ∞ ∧ forall a, κ a Set.univ <= C

中文:
类 是FiniteKernel
  参数: (κ : 核 α β)
  公理与运算 (1 个):
    - exists_univ_le : 存在 C : 实数>=0∞, C < ∞ ∧ 对任意 a, κ a 集合.univ <= C
-/
class IsFiniteKernel (κ : Kernel α β) : Prop where
  exists_univ_le : exists C : Real>=0∞, C < ∞ ∧ forall a, κ a Set.univ <= C

/--
theorem `eq_zero_or_isMarkovKernel` / 定理 `eq_zero_or_isMarkovKernel`

English:
theorem eq_zero_or_isMarkovKernel
  proof: h.eq_zero_or_isMarkovKernel'

中文:
定理 eq_zero_or_isMarkovKernel
  证明: h.eq_zero_or_isMarkovKernel'

Depends on / 依赖: eq_zero_or_isMarkovKernel, h.eq_zero_or_isMarkovKernel
-/
theorem eq_zero_or_isMarkovKernel
    (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] :
    κ = 0 ∨ IsMarkovKernel κ :=
  h.eq_zero_or_isMarkovKernel'

/--
Definition of `Kernel.bound` / `Kernel.bound` 的定义

English:
definition Kernel.bound
  signature: (κ : Kernel α β)
  body: ⨆ a, κ a Set.univ

中文:
定义 核.bound
  签名: (κ : 核 α β)
  定义体: ⨆ a, κ a Set.univ

Depends on / 依赖: Set.univ
-/
noncomputable def Kernel.bound (κ : Kernel α β) : Real>=0∞ :=
  ⨆ a, κ a Set.univ

namespace Kernel

/--
theorem `bound_lt_top` / 定理 `bound_lt_top`

English:
theorem bound_lt_top
  given: (κ : Kernel α β) [h : IsFiniteKernel κ]
  statement: κ.bound < ∞
  proof: by
  obtain ⟨C, hC, hle⟩ := h.exists_univ_le
  refine lt_of_le_of_lt ?_ hC
  simp [bound, hle]

中文:
定理 bound_lt_top
  条件: (κ : 核 α β) [h : 是FiniteKernel κ]
  结论: κ.bound < ∞
  证明: by
  obtain ⟨C, hC, hle⟩ := h.exists_univ_le
  refine lt_of_le_of_lt ?_ hC
  simp [bound, hle]

Depends on / 依赖: exists_univ_le, h.exists_univ_le, lt_of_le_of_lt
-/
theorem bound_lt_top (κ : Kernel α β) [h : IsFiniteKernel κ] : κ.bound < ∞ := by
  obtain ⟨C, hC, hle⟩ := h.exists_univ_le
  refine lt_of_le_of_lt ?_ hC
  simp [bound, hle]

/--
theorem `bound_ne_top` / 定理 `bound_ne_top`

English:
theorem bound_ne_top
  given: (κ : Kernel α β) [IsFiniteKernel κ]
  proof: κ.bound_lt_top.ne

中文:
定理 bound_ne_top
  条件: (κ : 核 α β) [是FiniteKernel κ]
  证明: κ.bound_lt_top.ne

Depends on / 依赖: bound_lt_top, bound_lt_top.ne
-/
theorem bound_ne_top (κ : Kernel α β) [IsFiniteKernel κ] :
    κ.bound != ∞ := κ.bound_lt_top.ne

/--
theorem `measure_le_bound` / 定理 `measure_le_bound`

English:
theorem measure_le_bound
  given: (κ : Kernel α β) (a : α) (s : Set β)
  proof: (measure_mono (Set.subset_univ s)).trans le_iSup (f := fun a => κ a .univ) a

@[simp]

中文:
定理 measure_le_bound
  条件: (κ : 核 α β) (a : α) (s : 集合 β)
  证明: (measure_mono (Set.subset_univ s)).trans le_iSup (f := fun a => κ a .univ) a

@[simp]

Depends on / 依赖: Set.subset_univ, le_iSup, measure_mono, subset_univ
-/
theorem measure_le_bound (κ : Kernel α β) (a : α) (s : Set β) :
    κ a s <= κ.bound :=
(measure_mono (Set.subset_univ s)).trans le_iSup (f := fun a => κ a .univ) a

@[simp]
/--
lemma `bound_eq_zero_of_isEmpty` / 引理 `bound_eq_zero_of_isEmpty`

English:
lemma bound_eq_zero_of_isEmpty
  given: [IsEmpty α] (κ : Kernel α β)
  proof: by simp [bound]

@[simp]

中文:
引理 bound_eq_zero_of_isEmpty
  条件: [是空 α] (κ : 核 α β)
  证明: by simp [bound]

@[simp]
-/
lemma bound_eq_zero_of_isEmpty [IsEmpty α] (κ : Kernel α β) :
    κ.bound = 0 := by simp [bound]

@[simp]
/--
lemma `bound_eq_zero_of_isEmpty'` / 引理 `bound_eq_zero_of_isEmpty'`

English:
lemma bound_eq_zero_of_isEmpty'
  given: [IsEmpty β] (κ : Kernel α β)
  proof: by simp [bound, Subsingleton.elim _ (0 : Measure β)]

@[simp]

中文:
引理 bound_eq_zero_of_isEmpty'
  条件: [是空 β] (κ : 核 α β)
  证明: by simp [bound, Subsingleton.elim _ (0 : Measure β)]

@[simp]

Depends on / 依赖: Measure, Subsingleton, Subsingleton.elim
-/
lemma bound_eq_zero_of_isEmpty' [IsEmpty β] (κ : Kernel α β) :
    κ.bound = 0 := by simp [bound, Subsingleton.elim _ (0 : Measure β)]

@[simp]
/--
lemma `bound_zero` / 引理 `bound_zero`

English:
lemma bound_zero
  statement: bound (0 : Kernel α β) = 0
  proof: by
  simp [bound]

中文:
引理 bound_zero
  结论: bound (0 : 核 α β) = 0
  证明: by
  simp [bound]
-/
lemma bound_zero : bound (0 : Kernel α β) = 0 := by
  simp [bound]

end Kernel

/--
Instance `isFiniteKernel_zero` / 实例 `isFiniteKernel_zero`

English:
instance isFiniteKernel_zero
  signature: (α β : Type*) {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  body: ⟨⟨0, ENNReal.coe_lt_top, fun _ => by simp⟩⟩

中文:
实例 isFiniteKernel_zero
  签名: (α β : 类型) {_ : 可测空间 α} {_ : 可测空间 β}
  定义体: ⟨⟨0, ENNReal.coe_lt_top, fun _ => by simp⟩⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, coe_lt_top
-/
instance isFiniteKernel_zero (α β : Type*) {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    IsFiniteKernel (0 : Kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun _ => by simp⟩⟩

/--
Instance `IsFiniteKernel.add` / 实例 `IsFiniteKernel.add`

English:
instance IsFiniteKernel.add
  signature: (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
  body: by
  refine ⟨⟨κ.bound + η.bound, ENNReal.add_lt_top.mpr ⟨κ.bound_lt_top, η.bound_lt_top⟩, fun a => ?_⟩⟩
  exact add_le_add (Kernel.measure_le_bound _ _ _) (Kernel.measure_le_bound _ _ _)

中文:
实例 是FiniteKernel.add
  签名: (κ η : 核 α β) [是FiniteKernel κ] [是FiniteKernel η]
  定义体: by
  refine ⟨⟨κ.bound + η.bound, ENNReal.add_lt_top.mpr ⟨κ.bound_lt_top, η.bound_lt_top⟩, fun a => ?_⟩⟩
  exact add_le_add (Kernel.measure_le_bound _ _ _) (Kernel.measure_le_bound _ _ _)

Depends on / 依赖: ENNReal, ENNReal.add_lt_top.mpr, Kernel, Kernel.measure_le_bound, add_le_add, add_lt_top, bound_lt_top, measure_le_bound
-/
instance IsFiniteKernel.add (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) := by
  refine ⟨⟨κ.bound + η.bound, ENNReal.add_lt_top.mpr ⟨κ.bound_lt_top, η.bound_lt_top⟩, fun a => ?_⟩⟩
  exact add_le_add (Kernel.measure_le_bound _ _ _) (Kernel.measure_le_bound _ _ _)

/--
lemma `isFiniteKernel_of_le` / 引理 `isFiniteKernel_of_le`

English:
lemma isFiniteKernel_of_le
  given: {κ ν : Kernel α β} [hν : IsFiniteKernel ν] (hκν : κ <= ν)
  proof: ⟨ν.bound, ν.bound_lt_top, fun a => (hκν _ _).trans (ν.measure_le_bound a Set.univ)⟩

中文:
引理 isFiniteKernel_of_le
  条件: {κ ν : 核 α β} [hν : 是FiniteKernel ν] (hκν : κ <= ν)
  证明: ⟨ν.bound, ν.bound_lt_top, fun a => (hκν _ _).trans (ν.measure_le_bound a Set.univ)⟩

Depends on / 依赖: Set.univ, bound_lt_top, measure_le_bound
-/
lemma isFiniteKernel_of_le {κ ν : Kernel α β} [hν : IsFiniteKernel ν] (hκν : κ <= ν) :
    IsFiniteKernel κ :=
  ⟨ν.bound, ν.bound_lt_top, fun a => (hκν _ _).trans (ν.measure_le_bound a Set.univ)⟩

variable {κ η : Kernel α β}

/--
Instance `IsMarkovKernel.is_probability_measure'` / 实例 `IsMarkovKernel.is_probability_measure'`

English:
instance IsMarkovKernel.is_probability_measure'
  signature: [IsMarkovKernel κ] (a : α)
  body: IsMarkovKernel.isProbabilityMeasure a

中文:
实例 是MarkovKernel.is_probability_measure'
  签名: [是MarkovKernel κ] (a : α)
  定义体: IsMarkovKernel.isProbabilityMeasure a

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.isProbabilityMeasure, isProbabilityMeasure
-/
instance IsMarkovKernel.is_probability_measure' [IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroOrMarkovKernel (0 : Kernel α β)
  body: ⟨Or.inl rfl⟩

中文:
实例 :
  签名: 是ZeroOrMarkovKernel (0 : 核 α β)
  定义体: ⟨Or.inl rfl⟩

Depends on / 依赖: Or.inl
-/
instance : IsZeroOrMarkovKernel (0 : Kernel α β) := ⟨Or.inl rfl⟩

instance (priority := 100) IsMarkovKernel.IsZeroOrMarkovKernel [h : IsMarkovKernel κ] :
    IsZeroOrMarkovKernel κ := ⟨Or.inr h⟩

instance (priority := 100) IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure
    [IsZeroOrMarkovKernel κ] (a : α) : IsZeroOrProbabilityMeasure (κ a) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h'
  · simp only [zero_apply]
    infer_instance
  · infer_instance

/--
Instance `IsFiniteKernel.isFiniteMeasure` / 实例 `IsFiniteKernel.isFiniteMeasure`

English:
instance IsFiniteKernel.isFiniteMeasure
  signature: [IsFiniteKernel κ] (a : α)
  body: ⟨(κ.measure_le_bound a Set.univ).trans_lt κ.bound_lt_top⟩

中文:
实例 是FiniteKernel.isFiniteMeasure
  签名: [是FiniteKernel κ] (a : α)
  定义体: ⟨(κ.measure_le_bound a Set.univ).trans_lt κ.bound_lt_top⟩

Depends on / 依赖: Set.univ, bound_lt_top, measure_le_bound, trans_lt
-/
instance IsFiniteKernel.isFiniteMeasure [IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(κ.measure_le_bound a Set.univ).trans_lt κ.bound_lt_top⟩

instance (priority := 100) IsZeroOrMarkovKernel.isFiniteKernel [h : IsZeroOrMarkovKernel κ] :
    IsFiniteKernel κ := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | _h'
  · infer_instance
  · exact ⟨⟨1, ENNReal.one_lt_top, fun _ => prob_le_one⟩⟩

namespace Kernel

@[simp]
/--
lemma `bound_eq_one` / 引理 `bound_eq_one`

English:
lemma bound_eq_one
  given: [Nonempty α] (κ : Kernel α β) [IsMarkovKernel κ]
  proof: by simp [bound]

@[simp]

中文:
引理 bound_eq_one
  条件: [非空 α] (κ : 核 α β) [是MarkovKernel κ]
  证明: by simp [bound]

@[simp]
-/
lemma bound_eq_one [Nonempty α] (κ : Kernel α β) [IsMarkovKernel κ] :
    κ.bound = 1 := by simp [bound]

@[simp]
/--
lemma `bound_le_one` / 引理 `bound_le_one`

English:
lemma bound_le_one
  given: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  proof: by
  rcases isEmpty_or_nonempty α
  · simp
  · rcases eq_zero_or_isMarkovKernel κ with rfl | _ <;> simp

@[ext]

中文:
引理 bound_le_one
  条件: (κ : 核 α β) [是ZeroOrMarkovKernel κ]
  证明: by
  rcases isEmpty_or_nonempty α
  · simp
  · rcases eq_zero_or_isMarkovKernel κ with rfl | _ <;> simp

@[ext]

Depends on / 依赖: eq_zero_or_isMarkovKernel, isEmpty_or_nonempty
-/
lemma bound_le_one (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    κ.bound <= 1 := by
  rcases isEmpty_or_nonempty α
  · simp
  · rcases eq_zero_or_isMarkovKernel κ with rfl | _ <;> simp

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall a, κ a = η a)
  statement: κ = η
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: (h : 对任意 a, κ a = η a)
  结论: κ = η
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall a, κ a = η a) : κ = η := DFunLike.ext _ _ h

/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  statement: κ = η ↔ forall a s, MeasurableSet s -> κ a s = η a s
  proof: by
  simp_rw [Kernel.ext_iff, Measure.ext_iff]

中文:
定理 ext_iff'
  结论: κ = η ↔ 对任意 a s, 可测集 s -> κ a s = η a s
  证明: by
  simp_rw [Kernel.ext_iff, Measure.ext_iff]

Depends on / 依赖: Kernel, Kernel.ext_iff, Measure, Measure.ext_iff, ext_iff, simp_rw
-/
theorem ext_iff' : κ = η ↔ forall a s, MeasurableSet s -> κ a s = η a s := by
  simp_rw [Kernel.ext_iff, Measure.ext_iff]

/--
theorem `ext_fun` / 定理 `ext_fun`

English:
theorem ext_fun
  given: (h : forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a)
  proof: by
  ext a s hs
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]

中文:
定理 ext_fun
  条件: (h : 对任意 a f, 可测 f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a)
  证明: by
  ext a s hs
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]

Depends on / 依赖: Measurable, Measurable.indicator, indicator, lintegral_indicator_const, measurable_const, one_mul, s.indicator, simp_rw, specialize
-/
theorem ext_fun (h : forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext a s hs
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]

/--
theorem `ext_fun_iff` / 定理 `ext_fun_iff`

English:
theorem ext_fun_iff
  statement: κ = η ↔ forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a
  proof: ⟨fun h a f _ => by rw [h], ext_fun⟩

中文:
定理 ext_fun_iff
  结论: κ = η ↔ 对任意 a f, 可测 f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a
  证明: ⟨fun h a f _ => by rw [h], ext_fun⟩

Depends on / 依赖: ext_fun
-/
theorem ext_fun_iff : κ = η ↔ forall a f, Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a :=
  ⟨fun h a f _ => by rw [h], ext_fun⟩

section IsEmptyNonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: β] : Subsingleton (Kernel α β) where
  body: by ext a s; simp [Set.eq_empty_of_isEmpty s]

中文:
实例 [是空
  签名: β] : 子单例 (核 α β) where
  定义体: by ext a s; simp [Set.eq_empty_of_isEmpty s]

Depends on / 依赖: Set.eq_empty_of_isEmpty, eq_empty_of_isEmpty
-/
instance [IsEmpty β] : Subsingleton (Kernel α β) where
  allEq κ η := by ext a s; simp [Set.eq_empty_of_isEmpty s]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] (κ
  body: by simp

中文:
实例 [是空
  签名: α] (κ
  定义体: by simp
-/
instance [IsEmpty α] (κ : Kernel α β) : IsMarkovKernel κ where
  isProbabilityMeasure := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: β] (κ
  body: by
    left
    ext a s
    simp [Set.eq_empty_of_isEmpty s]

中文:
实例 [是空
  签名: β] (κ
  定义体: by
    left
    ext a s
    simp [Set.eq_empty_of_isEmpty s]

Depends on / 依赖: Set.eq_empty_of_isEmpty, eq_empty_of_isEmpty
-/
instance [IsEmpty β] (κ : Kernel α β) : IsZeroOrMarkovKernel κ where
  eq_zero_or_isMarkovKernel' := by
    left
    ext a s
    simp [Set.eq_empty_of_isEmpty s]

/--
lemma `not_isMarkovKernel_zero` / 引理 `not_isMarkovKernel_zero`

English:
lemma not_isMarkovKernel_zero
  given: [Nonempty α]
  statement: ¬ IsMarkovKernel (0 : Kernel α β)
  proof: by
  by_contra h
  let x : α := Nonempty.some inferInstance
  have h1 : (0 : Measure β) .univ = 1 := (h.isProbabilityMeasure x).measure_univ
  simp at h1

中文:
引理 not_isMarkovKernel_zero
  条件: [非空 α]
  结论: ¬ 是MarkovKernel (0 : 核 α β)
  证明: by
  by_contra h
  let x : α := Nonempty.some inferInstance
  have h1 : (0 : Measure β) .univ = 1 := (h.isProbabilityMeasure x).measure_univ
  simp at h1

Depends on / 依赖: Measure, Nonempty, Nonempty.some, h.isProbabilityMeasure, isProbabilityMeasure, measure_univ
-/
lemma not_isMarkovKernel_zero [Nonempty α] : ¬ IsMarkovKernel (0 : Kernel α β) := by
  by_contra h
  let x : α := Nonempty.some inferInstance
  have h1 : (0 : Measure β) .univ = 1 := (h.isProbabilityMeasure x).measure_univ
  simp at h1

end IsEmptyNonempty

/--
theorem `measurable_coe` / 定理 `measurable_coe`

English:
theorem measurable_coe
  given: (κ : Kernel α β) {s : Set β} (hs : MeasurableSet s)
  proof: (Measure.measurable_coe hs).comp κ.measurable

中文:
定理 measurable_coe
  条件: (κ : 核 α β) {s : 集合 β} (hs : 可测集 s)
  证明: (Measure.measurable_coe hs).comp κ.measurable
-/
protected theorem measurable_coe (κ : Kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp κ.measurable

/--
lemma `apply_congr_of_mem_measurableAtom` / 引理 `apply_congr_of_mem_measurableAtom`

English:
lemma apply_congr_of_mem_measurableAtom
  given: (κ : Kernel α β) {y' y : α} (hy' : y' in measurableAtom y)
  proof: by
  ext s hs
  exact mem_of_mem_measurableAtom hy' (κ.measurable_coe hs (measurableSet_singleton (κ y s))) rfl

中文:
引理 apply_congr_of_mem_measurableAtom
  条件: (κ : 核 α β) {y' y : α} (hy' : y' in measurableAtom y)
  证明: by
  ext s hs
  exact mem_of_mem_measurableAtom hy' (κ.measurable_coe hs (measurableSet_singleton (κ y s))) rfl

Depends on / 依赖: measurableSet_singleton, measurable_coe, mem_of_mem_measurableAtom
-/
lemma apply_congr_of_mem_measurableAtom (κ : Kernel α β) {y' y : α} (hy' : y' in measurableAtom y) :
    κ y' = κ y := by
  ext s hs
  exact mem_of_mem_measurableAtom hy' (κ.measurable_coe hs (measurableSet_singleton (κ y s))) rfl

/--
lemma `eq_zero_of_isEmpty_left` / 引理 `eq_zero_of_isEmpty_left`

English:
lemma eq_zero_of_isEmpty_left
  given: (κ : Kernel α β) [h : IsEmpty α]
  statement: κ = 0
  proof: by
  ext a
  exact h.elim a

中文:
引理 eq_zero_of_isEmpty_left
  条件: (κ : 核 α β) [h : 是空 α]
  结论: κ = 0
  证明: by
  ext a
  exact h.elim a

Depends on / 依赖: h.elim
-/
lemma eq_zero_of_isEmpty_left (κ : Kernel α β) [h : IsEmpty α] : κ = 0 := by
  ext a
  exact h.elim a

/--
lemma `eq_zero_of_isEmpty_right` / 引理 `eq_zero_of_isEmpty_right`

English:
lemma eq_zero_of_isEmpty_right
  given: (κ : Kernel α β) [IsEmpty β]
  statement: κ = 0
  proof: by
  ext a
  simp [Measure.eq_zero_of_isEmpty (κ a)]

中文:
引理 eq_zero_of_isEmpty_right
  条件: (κ : 核 α β) [是空 β]
  结论: κ = 0
  证明: by
  ext a
  simp [Measure.eq_zero_of_isEmpty (κ a)]

Depends on / 依赖: Measure, Measure.eq_zero_of_isEmpty, eq_zero_of_isEmpty
-/
lemma eq_zero_of_isEmpty_right (κ : Kernel α β) [IsEmpty β] : κ = 0 := by
  ext a
  simp [Measure.eq_zero_of_isEmpty (κ a)]

section Sum

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def sum [Countable ι] (κ : ι -> Kernel α β)
  body: Measure.sum fun n => κ n a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sum_apply _ hs]
    exact Measurable.tsum fun n => Kernel.measurable_coe (κ n) hs

中文:
定义 noncomputable
  签名: def 求和 [可数 ι] (κ : ι -> 核 α β)
  定义体: Measure.sum fun n => κ n a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sum_apply _ hs]
    exact Measurable.tsum fun n => Kernel.measurable_coe (κ n) hs
-/
protected noncomputable def sum [Countable ι] (κ : ι -> Kernel α β) : Kernel α β where
  toFun a := Measure.sum fun n => κ n a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sum_apply _ hs]
    exact Measurable.tsum fun n => Kernel.measurable_coe (κ n) hs

/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: [Countable ι] (κ : ι -> Kernel α β) (a : α)
  proof: rfl

中文:
定理 sum_apply
  条件: [可数 ι] (κ : ι -> 核 α β) (a : α)
  证明: rfl
-/
theorem sum_apply [Countable ι] (κ : ι -> Kernel α β) (a : α) :
    Kernel.sum κ a = Measure.sum fun n => κ n a :=
  rfl

/--
theorem `sum_apply'` / 定理 `sum_apply'`

English:
theorem sum_apply'
  given: [Countable ι] (κ : ι -> Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s)
  proof: by rw [sum_apply κ a, Measure.sum_apply _ hs]

@[simp]

中文:
定理 sum_apply'
  条件: [可数 ι] (κ : ι -> 核 α β) (a : α) {s : 集合 β} (hs : 可测集 s)
  证明: by rw [sum_apply κ a, Measure.sum_apply _ hs]

@[simp]

Depends on / 依赖: Measure, Measure.sum_apply, sum_apply
-/
theorem sum_apply' [Countable ι] (κ : ι -> Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) :
    Kernel.sum κ a s = ∑' n, κ n a s := by rw [sum_apply κ a, Measure.sum_apply _ hs]

@[simp]
/--
theorem `sum_zero` / 定理 `sum_zero`

English:
theorem sum_zero
  given: [Countable ι]
  statement: (Kernel.sum fun _ : ι => (0 : Kernel α β)) = 0
  proof: by
  ext a s hs
  rw [sum_apply' _ a hs]
  simp only [zero_apply, Measure.coe_zero, Pi.zero_apply, tsum_zero]

中文:
定理 sum_zero
  条件: [可数 ι]
  结论: (核.求和 fun _ : ι => (0 : 核 α β)) = 0
  证明: by
  ext a s hs
  rw [sum_apply' _ a hs]
  simp only [zero_apply, Measure.coe_zero, Pi.zero_apply, tsum_zero]

Depends on / 依赖: Measure, Measure.coe_zero, Pi.zero_apply, coe_zero, sum_apply, tsum_zero, zero_apply
-/
theorem sum_zero [Countable ι] : (Kernel.sum fun _ : ι => (0 : Kernel α β)) = 0 := by
  ext a s hs
  rw [sum_apply' _ a hs]
  simp only [zero_apply, Measure.coe_zero, Pi.zero_apply, tsum_zero]

/--
theorem `sum_comm` / 定理 `sum_comm`

English:
theorem sum_comm
  given: [Countable ι] (κ : ι -> ι -> Kernel α β)
  proof: by
  ext a s; simp_rw [sum_apply]; rw [Measure.sum_comm]

@[simp]

中文:
定理 sum_comm
  条件: [可数 ι] (κ : ι -> ι -> 核 α β)
  证明: by
  ext a s; simp_rw [sum_apply]; rw [Measure.sum_comm]

@[simp]

Depends on / 依赖: Measure, Measure.sum_comm, simp_rw, sum_apply, sum_comm
-/
theorem sum_comm [Countable ι] (κ : ι -> ι -> Kernel α β) :
    (Kernel.sum fun n => Kernel.sum (κ n)) = Kernel.sum fun m => Kernel.sum fun n => κ n m := by
  ext a s; simp_rw [sum_apply]; rw [Measure.sum_comm]

@[simp]
/--
theorem `sum_fintype` / 定理 `sum_fintype`

English:
theorem sum_fintype
  given: [Fintype ι] (κ : ι -> Kernel α β)
  statement: Kernel.sum κ = ∑ i, κ i
  proof: by
  ext a s hs
  simp only [sum_apply' κ a hs, finsetSum_apply' _ κ a s, tsum_fintype]

中文:
定理 sum_fintype
  条件: [有限类型 ι] (κ : ι -> 核 α β)
  结论: 核.求和 κ = ∑ i, κ i
  证明: by
  ext a s hs
  simp only [sum_apply' κ a hs, finsetSum_apply' _ κ a s, tsum_fintype]

Depends on / 依赖: finsetSum_apply, sum_apply, tsum_fintype
-/
theorem sum_fintype [Fintype ι] (κ : ι -> Kernel α β) : Kernel.sum κ = ∑ i, κ i := by
  ext a s hs
  simp only [sum_apply' κ a hs, finsetSum_apply' _ κ a s, tsum_fintype]

/--
theorem `sum_add` / 定理 `sum_add`

English:
theorem sum_add
  given: [Countable ι] (κ η : ι -> Kernel α β)
  proof: by
  ext a s hs
  simp only [add_apply, sum_apply, Measure.sum_apply _ hs, Pi.add_apply,
    Measure.coe_add, ENNReal.summable.tsum_add ENNReal.summable]

中文:
定理 sum_add
  条件: [可数 ι] (κ η : ι -> 核 α β)
  证明: by
  ext a s hs
  simp only [add_apply, sum_apply, Measure.sum_apply _ hs, Pi.add_apply,
    Measure.coe_add, ENNReal.summable.tsum_add ENNReal.summable]

Depends on / 依赖: ENNReal, ENNReal.summable, ENNReal.summable.tsum_add, Measure, Measure.coe_add, Measure.sum_apply, Pi.add_apply, add_apply, coe_add, sum_apply, summable, tsum_add
-/
theorem sum_add [Countable ι] (κ η : ι -> Kernel α β) :
    (Kernel.sum fun n => κ n + η n) = Kernel.sum κ + Kernel.sum η := by
  ext a s hs
  simp only [add_apply, sum_apply, Measure.sum_apply _ hs, Pi.add_apply,
    Measure.coe_add, ENNReal.summable.tsum_add ENNReal.summable]

end Sum

section SFinite

/--
Definition of `_root_.ProbabilityTheory.IsSFiniteKernel` / `_root_.ProbabilityTheory.IsSFiniteKernel` 的定义

English:
class _root_.ProbabilityTheory.IsSFiniteKernel
  parameters: (κ : Kernel α β)
  axioms and operations (1):
    - tsum_finite : exists κs : Nat -> Kernel α β, (forall n, IsFiniteKernel (κs n)) ∧ κ = Kernel.sum κs

中文:
类 _root_.ProbabilityTheory.是SFiniteKernel
  参数: (κ : 核 α β)
  公理与运算 (1 个):
    - tsum_finite : 存在 κs : 自然数 -> 核 α β, (对任意 n, 是FiniteKernel (κs n)) ∧ κ = 核.求和 κs
-/
class _root_.ProbabilityTheory.IsSFiniteKernel (κ : Kernel α β) : Prop where
  tsum_finite : exists κs : Nat -> Kernel α β, (forall n, IsFiniteKernel (κs n)) ∧ κ = Kernel.sum κs

instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] :
    IsSFiniteKernel κ :=
  ⟨⟨fun n => if n = 0 then κ else 0, fun n => by
      simp only; split_ifs
      · exact h
      · infer_instance, by
      ext a s hs
      rw [Kernel.sum_apply' _ _ hs]
      have : (fun i => ((ite (i = 0) κ 0) a) s) = fun i => ite (i = 0) (κ a s) 0 := by
        ext1 i; split_ifs <;> rfl
      rw [this]; rw [tsum_ite_eq]⟩⟩

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (κ : Kernel α β) [h : IsSFiniteKernel κ]
  body: h.tsum_finite.choose

中文:
定义 seq
  签名: (κ : 核 α β) [h : 是SFiniteKernel κ]
  定义体: h.tsum_finite.choose

Depends on / 依赖: h.tsum_finite.choose, tsum_finite
-/
noncomputable def seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : Nat -> Kernel α β :=
  h.tsum_finite.choose

/--
theorem `kernel_sum_seq` / 定理 `kernel_sum_seq`

English:
theorem kernel_sum_seq
  given: (κ : Kernel α β) [h : IsSFiniteKernel κ]
  statement: Kernel.sum (seq κ) = κ
  proof: h.tsum_finite.choose_spec.2.symm

中文:
定理 kernel_sum_seq
  条件: (κ : 核 α β) [h : 是SFiniteKernel κ]
  结论: 核.求和 (seq κ) = κ
  证明: h.tsum_finite.choose_spec.2.symm

Depends on / 依赖: choose_spec, h.tsum_finite.choose_spec, tsum_finite
-/
theorem kernel_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ :=
  h.tsum_finite.choose_spec.2.symm

/--
theorem `measure_sum_seq` / 定理 `measure_sum_seq`

English:
theorem measure_sum_seq
  given: (κ : Kernel α β) [h : IsSFiniteKernel κ] (a : α)
  proof: by rw [← Kernel.sum_apply, kernel_sum_seq κ]

中文:
定理 measure_sum_seq
  条件: (κ : 核 α β) [h : 是SFiniteKernel κ] (a : α)
  证明: by rw [← Kernel.sum_apply, kernel_sum_seq κ]

Depends on / 依赖: Finite, Kernel, Kernel.sum_apply, Module, Module.Finite, QuasiFinite, kernel_sum_seq, sum_apply
-/
theorem measure_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (a : α) :
    (Measure.sum fun n => seq κ n a) = κ a := by rw [← Kernel.sum_apply, kernel_sum_seq κ]

/--
Instance `isFiniteKernel_seq` / 实例 `isFiniteKernel_seq`

English:
instance isFiniteKernel_seq
  signature: (κ : Kernel α β) [h : IsSFiniteKernel κ] (n : Nat)
  body: h.tsum_finite.choose_spec.1 n

中文:
实例 isFiniteKernel_seq
  签名: (κ : 核 α β) [h : 是SFiniteKernel κ] (n : 自然数)
  定义体: h.tsum_finite.choose_spec.1 n

Depends on / 依赖: choose_spec, h.tsum_finite.choose_spec, tsum_finite
-/
instance isFiniteKernel_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (n : Nat) :
    IsFiniteKernel (Kernel.seq κ n) :=
  h.tsum_finite.choose_spec.1 n

/--
Instance `_root_.ProbabilityTheory.IsSFiniteKernel.sFinite` / 实例 `_root_.ProbabilityTheory.IsSFiniteKernel.sFinite`

English:
instance _root_.ProbabilityTheory.IsSFiniteKernel.sFinite
  signature: [IsSFiniteKernel κ] (a : α)
  body: ⟨⟨fun n => seq κ n a, inferInstance, (measure_sum_seq κ a).symm⟩⟩

中文:
实例 _root_.ProbabilityTheory.是SFiniteKernel.sFinite
  签名: [是SFiniteKernel κ] (a : α)
  定义体: ⟨⟨fun n => seq κ n a, inferInstance, (measure_sum_seq κ a).symm⟩⟩

Depends on / 依赖: measure_sum_seq
-/
instance _root_.ProbabilityTheory.IsSFiniteKernel.sFinite [IsSFiniteKernel κ] (a : α) :
    SFinite (κ a) :=
  ⟨⟨fun n => seq κ n a, inferInstance, (measure_sum_seq κ a).symm⟩⟩

/--
Instance `IsSFiniteKernel.add` / 实例 `IsSFiniteKernel.add`

English:
instance IsSFiniteKernel.add
  signature: (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η]
  body: by
  refine ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, ?_⟩⟩
  rw [sum_add]; rw [kernel_sum_seq κ]; rw [kernel_sum_seq η]

中文:
实例 是SFiniteKernel.add
  签名: (κ η : 核 α β) [是SFiniteKernel κ] [是SFiniteKernel η]
  定义体: by
  refine ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, ?_⟩⟩
  rw [sum_add]; rw [kernel_sum_seq κ]; rw [kernel_sum_seq η]

Depends on / 依赖: kernel_sum_seq, sum_add
-/
instance IsSFiniteKernel.add (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (κ + η) := by
  refine ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, ?_⟩⟩
  rw [sum_add]; rw [kernel_sum_seq κ]; rw [kernel_sum_seq η]

/--
theorem `IsSFiniteKernel.finsetSum` / 定理 `IsSFiniteKernel.finsetSum`

English:
theorem IsSFiniteKernel.finsetSum
  statement: {κs : ι -> Kernel α β} (I : Finset ι)
  proof: by
  classical
  induction I using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i I hi_notMem_I h_ind =>
    rw [Finset.sum_insert hi_notMem_I]
    have : IsSFiniteKernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : IsSFiniteKernel (∑ x in I, κs x) :=


中文:
定理 是SFiniteKernel.finsetSum
  结论: {κs : ι -> 核 α β} (I : 有限集 ι)
  证明: by
  classical
  induction I using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i I hi_notMem_I h_ind =>
    rw [Finset.sum_insert hi_notMem_I]
    have : IsSFiniteKernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : IsSFiniteKernel (∑ x in I, κs x) :=


Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_empty, Finset.sum_insert, IsSFiniteKernel, IsSFiniteKernel.add, classical, h_ind, hi_notMem_I, infer_instance, insert, mem_insert_of_mem, mem_insert_self, sum_empty, sum_insert
-/
theorem IsSFiniteKernel.finsetSum {κs : ι -> Kernel α β} (I : Finset ι)
    (h : forall i in I, IsSFiniteKernel (κs i)) : IsSFiniteKernel (∑ i in I, κs i) := by
  classical
  induction I using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i I hi_notMem_I h_ind =>
    rw [Finset.sum_insert hi_notMem_I]
    have : IsSFiniteKernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : IsSFiniteKernel (∑ x in I, κs x) :=
      h_ind fun i hiI => h i (Finset.mem_insert_of_mem hiI)
    exact IsSFiniteKernel.add _ _

@[deprecated (since := "2026-04-08")] alias IsSFiniteKernel.finset_sum := IsSFiniteKernel.finsetSum

/--
theorem `isSFiniteKernel_sum_of_denumerable` / 定理 `isSFiniteKernel_sum_of_denumerable`

English:
theorem isSFiniteKernel_sum_of_denumerable
  statement: [Denumerable ι] {κs : ι -> Kernel α β}
  proof: by
  let e : Nat ≃ ι × Nat := (Denumerable.eqv (ι × Nat)).symm
  refine ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, ?_⟩⟩
  have hκ_eq : Kernel.sum κs = Kernel.sum fun n => Kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext a s hs
  rw [hκ_eq]
  simp_rw [Kernel.sum_apply' _ _ hs

中文:
定理 isSFiniteKernel_sum_of_denumerable
  结论: [可枚举 ι] {κs : ι -> 核 α β}
  证明: by
  let e : Nat ≃ ι × Nat := (Denumerable.eqv (ι × Nat)).symm
  refine ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, ?_⟩⟩
  have hκ_eq : Kernel.sum κs = Kernel.sum fun n => Kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext a s hs
  rw [hκ_eq]
  simp_rw [Kernel.sum_apply' _ _ hs

Depends on / 依赖: Denumerable, Denumerable.eqv, ENNReal, ENNReal.summable.tsum_prod, Kernel, Kernel.sum, Kernel.sum_apply, e.tsum_eq, im.fst, im.snd, kernel_sum_seq, simp_rw, sum_apply, summable, tsum_eq, tsum_prod
-/
theorem isSFiniteKernel_sum_of_denumerable [Denumerable ι] {κs : ι -> Kernel α β}
    (hκs : forall n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (Kernel.sum κs) := by
  let e : Nat ≃ ι × Nat := (Denumerable.eqv (ι × Nat)).symm
  refine ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, ?_⟩⟩
  have hκ_eq : Kernel.sum κs = Kernel.sum fun n => Kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext a s hs
  rw [hκ_eq]
  simp_rw [Kernel.sum_apply' _ _ hs]
  change (∑' i, ∑' m, seq (κs i) m a s) = ∑' n, (fun im : ι × Nat => seq (κs im.fst) im.snd a s) (e n)
  rw [e.tsum_eq (fun im : ι × Nat => seq (κs im.fst) im.snd a s)]; rw [ENNReal.summable.tsum_prod' fun _ => ENNReal.summable]

/--
Instance `isSFiniteKernel_sum` / 实例 `isSFiniteKernel_sum`

English:
instance isSFiniteKernel_sum
  signature: [Countable ι] {κs : ι -> Kernel α β}
  body: by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact IsSFiniteKernel.finsetSum Finset.univ fun i _ => hκs i
  cases nonempty_denumerable ι
  exact isSFiniteKernel_sum_of_denumerable hκs

中文:
实例 isSFiniteKernel_sum
  签名: [可数 ι] {κs : ι -> 核 α β}
  定义体: by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact IsSFiniteKernel.finsetSum Finset.univ fun i _ => hκs i
  cases nonempty_denumerable ι
  exact isSFiniteKernel_sum_of_denumerable hκs

Depends on / 依赖: Finset, Finset.univ, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, IsSFiniteKernel, IsSFiniteKernel.finsetSum, Quotient, finsetSum, fintypeOrInfinite, isSFiniteKernel_sum_of_denumerable, mk_surjective, nonempty_denumerable, of_surjective_algHom, sum_fintype
-/
instance isSFiniteKernel_sum [Countable ι] {κs : ι -> Kernel α β}
    [hκs : forall n, IsSFiniteKernel (κs n)] : IsSFiniteKernel (Kernel.sum κs) := by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact IsSFiniteKernel.finsetSum Finset.univ fun i _ => hκs i
  cases nonempty_denumerable ι
  exact isSFiniteKernel_sum_of_denumerable hκs

end SFinite
end Kernel
end ProbabilityTheory
