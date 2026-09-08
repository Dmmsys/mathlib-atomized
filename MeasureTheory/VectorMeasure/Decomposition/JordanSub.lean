/-
Copyright (c) 2025 Loic Simon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loic Simon
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Jordan decomposition from signed measure subtraction

This file develops the Jordan decomposition of the signed measure `μ - ν` for finite measures `μ`
and `ν`, expressing it as the pair `(μ - ν, ν - μ)` of mutually singular finite measures.

The key tool is the Hahn decomposition theorem, which yields a measurable partition of the space
where `μ ≤ ν` and `ν ≤ μ`, and the measure difference behaves like a signed measure difference.

## Main results

* `toJordanDecomposition_toSignedMeasure_sub`:
  The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is given by
  `(μ - ν, ν - μ)`. It relies on the following intermediate results.
* `mutually_singular_measure_sub`:
  The measures `μ - ν` and `ν - μ` are mutually singular.
* `sub_toSignedMeasure_eq_toSignedMeasure_sub`:
  The signed measure `μ.toSignedMeasure - ν.toSignedMeasure` equals
  `(μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

noncomputable section

variable {X : Type*} {mX : MeasurableSpace X}
variable {s : Set X}
variable {μ ν : Measure X}

/-
**MeasureTheory.Measure.sub_apply_eq_zero_of_isHahnDecomposition** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：sub_apply_eq_zero_of_isHahnDecomposition (hs : IsHahnDecomposition μ ν s) 
: (μ - ν) s = 0
参数：hs : IsHahnDecomposition μ ν s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict`：restrict_su
b_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - ν).restrict s = μ
.restrict s - ν.restrict s
· 使用定理 `MeasureTheory.IsHahnDecomposition.measurableSet`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.
IsHahnDecomposition μ ν s → Measurabl…
· 使用定理 `MeasureTheory.Measure.sub_eq_zero_of_le`：sub_eq_zero_of_le (h : μ <= ν) 
: μ - ν = 0
· 使用定理 `MeasureTheory.IsHahnDecomposition.le_on`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.IsHahnDe
composition μ ν s → μ.restric…
-/
lemma sub_apply_eq_zero_of_isHahnDecomposition
    (hs : IsHahnDecomposition μ ν s) : (μ - ν) s = 0 := by
  rw [← restrict_eq_zero, restrict_sub_eq_restrict_sub_restrict hs.measurableSet]
  exact sub_eq_zero_of_le hs.le_on

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
/-
**MeasureTheory.Measure.mutually_singular_measure_sub** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：mutually_singular_measure_sub : (μ - ν).MutuallySingular (ν - μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.exists_isHahnDecomposition`：exists_isHahnDecomposition (μ 
ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : exists s : Set α, IsHah
nDecomposition μ ν s
· 使用定理 `MeasureTheory.IsHahnDecomposition.measurableSet`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.
IsHahnDecomposition μ ν s → Measurabl…
· 使用引理 `MeasureTheory.Measure.sub_apply_eq_zero_of_isHahnDecomposition`：sub_appl
y_eq_zero_of_isHahnDecomposition (hs : IsHahnDecomposition μ ν s) : (μ - ν) s = 
0
· 使用定理 `MeasureTheory.IsHahnDecomposition.compl`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.IsHahnDe
composition μ ν s → MeasureTh…
-/
theorem mutually_singular_measure_sub :
    (μ - ν).MutuallySingular (ν - μ) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  exact ⟨s, hs.measurableSet,
    sub_apply_eq_zero_of_isHahnDecomposition hs,
    sub_apply_eq_zero_of_isHahnDecomposition hs.compl⟩
/-
**MeasureTheory.Measure.toSignedMeasure_restrict_sub** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：toSignedMeasure_restrict_sub (hs : IsHahnDecomposition μ ν s) : ((ν - μ).r
estrict s).toSignedMeasure = ν.toSignedMeasure.restrict s - μ.toSignedMeasure.re
strict s
参数：hs : IsHahnDecomposition μ ν s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsHahnDecomposition.measurableSet`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.
IsHahnDecomposition μ ν s → Measurabl…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasu
re`：toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s) 
: μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_add`：toSignedMeasure_add (μ ν : Me
asure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : (μ + ν).toSignedMeasure = μ.t
oSignedMeasure + ν.toSignedMeas…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict`：restrict_su
b_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - ν).restrict s = μ
.restrict s - ν.restrict s
· 使用定理 `MeasureTheory.Measure.sub_add_cancel_of_le`：sub_add_cancel_of_le [IsFini
teMeasure ν] (h₁ : ν <= μ) : μ - ν + ν = μ
· 使用定理 `MeasureTheory.IsHahnDecomposition.le_on`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.IsHahnDe
composition μ ν s → μ.restric…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure.congr_simp`：∀ {α : Type u_1} {m : 
MeasurableSpace α} (μ μ_1 : MeasureTheory.Measure α) (e_μ : μ = μ_1)   [hμ : Mea
sureTheory.IsFiniteMeasure μ], μ.toSig…
-/
lemma toSignedMeasure_restrict_sub (hs : IsHahnDecomposition μ ν s) :
    ((ν - μ).restrict s).toSignedMeasure =
      ν.toSignedMeasure.restrict s - μ.toSignedMeasure.restrict s := by
  have hmeas := hs.measurableSet
  rw [eq_sub_iff_add_eq, toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas,
    ← toSignedMeasure_add]
  simp only [restrict_sub_eq_restrict_sub_restrict, hmeas, sub_add_cancel_of_le hs.le_on]
  exact (toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas).symm
/-
**MeasureTheory.Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：sub_toSignedMeasure_eq_toSignedMeasure_sub : μ.toSignedMeasure - ν.toSigne
dMeasure = (μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `MeasureTheory.exists_isHahnDecomposition`：exists_isHahnDecomposition (μ 
ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : exists s : Set α, IsHah
nDecomposition μ ν s
· 使用定理 `MeasureTheory.IsHahnDecomposition.compl`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.IsHahnDe
composition μ ν s → MeasureTh…
· 使用引理 `MeasureTheory.Measure.toSignedMeasure_restrict_sub`：toSignedMeasure_rest
rict_sub (hs : IsHahnDecomposition μ ν s) : ((ν - μ).restrict s).toSignedMeasure
 = ν.toSignedMeasure.restrict s - μ.toSi…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_congr`：toSignedMeasure_congr {μ ν 
: Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν) : μ.toSignedMea
sure = ν.toSignedMeasure
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用引理 `MeasureTheory.Measure.sub_apply_eq_zero_of_isHahnDecomposition`：sub_appl
y_eq_zero_of_isHahnDecomposition (hs : IsHahnDecomposition μ ν s) : (μ - ν) s = 
0
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.VectorMeasure.restrict_add_restrict_compl`：restrict_add_re
strict_compl (hi : MeasurableSet i) : v.restrict i + v.restrict iᶜ = v
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.IsHahnDecomposition.measurableSet`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.
IsHahnDecomposition μ ν s → Measurabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_zero`：toSignedMeasure_zero : (0 : 
Measure α).toSignedMeasure = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasu
re`：toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s) 
: μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub.0.M
easureTheory.Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub._abel_1_1`：∀ {X 
: Type u_1} {mX : MeasurableSpace X} {μ ν : MeasureTheory.Measure X} [inst : Mea
sureTheory.IsFiniteMeasure μ]   [inst_1 : MeasureTheory…
-/
theorem sub_toSignedMeasure_eq_toSignedMeasure_sub :
    μ.toSignedMeasure - ν.toSignedMeasure =
      (μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsc := hs.compl
  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc
  have h₁' := toSignedMeasure_congr <| restrict_eq_zero.mpr <|
    sub_apply_eq_zero_of_isHahnDecomposition hs
  have h₂' := toSignedMeasure_congr <| restrict_eq_zero.mpr <|
  sub_apply_eq_zero_of_isHahnDecomposition hsc
  have partition₁ := VectorMeasure.restrict_add_restrict_compl (v := (μ - ν).toSignedMeasure)
    hs.measurableSet
  have partition₂ := VectorMeasure.restrict_add_restrict_compl (v := (ν - μ).toSignedMeasure)
    hs.measurableSet
  rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hs.measurableSet,
    toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hs.measurableSet.compl]
    at partition₁ partition₂
  rw [h₁', h₂] at partition₁
  rw [h₁, h₂'] at partition₂
  simp only [toSignedMeasure_zero, zero_add] at partition₁ partition₂
  rw [← VectorMeasure.restrict_add_restrict_compl (v := μ.toSignedMeasure) hs.measurableSet,
    ← VectorMeasure.restrict_add_restrict_compl (v := ν.toSignedMeasure) hs.measurableSet,
    ← partition₁, ← partition₂]
  abel

/-- The Jordan decomposition associated to the pair of mutually singular measures `μ - ν`
and `ν - μ`. -/
/-
**MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub** 是 Mathlib 中的一个
定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：jordanDecompositionOfToSignedMeasureSub (μ ν : Measure X) [IsFiniteMeasure
 μ] [IsFiniteMeasure ν] : JordanDecomposition X where posPart
参数：μ ν : Measure X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.mutually_singular_measure_sub`：mutually_singular_m
easure_sub : (μ - ν).MutuallySingular (ν - μ)

--- 原说明 ---
The Jordan decomposition associated to the pair of mutually singular measures `μ
 - ν`
and `ν - μ`.
-/
def jordanDecompositionOfToSignedMeasureSub
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : JordanDecomposition X where
  posPart := μ - ν
  negPart := ν - μ
  mutuallySingular := mutually_singular_measure_sub
/-
**MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：jordanDecompositionOfToSignedMeasureSub_posPart : (jordanDecompositionOfTo
SignedMeasureSub μ ν).posPart = μ - ν
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jordanDecompositionOfToSignedMeasureSub_posPart :
    (jordanDecompositionOfToSignedMeasureSub μ ν).posPart = μ - ν := rfl
/-
**MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_negPart** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：jordanDecompositionOfToSignedMeasureSub_negPart : (jordanDecompositionOfTo
SignedMeasureSub μ ν).negPart = ν - μ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jordanDecompositionOfToSignedMeasureSub_negPart :
    (jordanDecompositionOfToSignedMeasureSub μ ν).negPart = ν - μ := rfl
/-
**MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_toSignedMeasure*
* 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：jordanDecompositionOfToSignedMeasureSub_toSignedMeasure : (jordanDecomposi
tionOfToSignedMeasureSub μ ν).toSignedMeasure = μ.toSignedMeasure - ν.toSignedMe
asure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jordanDecompositionOfToSignedMeasureSub_toSignedMeasure :
    (jordanDecompositionOfToSignedMeasureSub μ ν).toSignedMeasure =
    μ.toSignedMeasure - ν.toSignedMeasure := by
  simp_rw [JordanDecomposition.toSignedMeasure, jordanDecompositionOfToSignedMeasureSub_posPart,
    jordanDecompositionOfToSignedMeasureSub_negPart, ← sub_toSignedMeasure_eq_toSignedMeasure_sub]

/-- The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is `(μ - ν, ν - μ)`. -/
@[simp]
/-
**MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toJordanDecomposition_toSignedMeasure_sub : (μ.toSignedMeasure - ν.toSigne
dMeasure).toJordanDecomposition = jordanDecompositionOfToSignedMeasureSub μ ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_injective`：toSignedMea
sure_injective : Injective @JordanDecomposition.toSignedMeasure α _
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用引理 `MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_toSignedMe
asure`：jordanDecompositionOfToSignedMeasureSub_toSignedMeasure : (jordanDecompos
itionOfToSignedMeasureSub μ ν).toSignedMeasure = μ.toSignedMeasure …

--- 原说明 ---
The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is `(μ - ν, 
ν - μ)`.
-/
theorem toJordanDecomposition_toSignedMeasure_sub :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition =
      jordanDecompositionOfToSignedMeasureSub μ ν := by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition,
    jordanDecompositionOfToSignedMeasureSub_toSignedMeasure]

end

end MeasureTheory.Measure

