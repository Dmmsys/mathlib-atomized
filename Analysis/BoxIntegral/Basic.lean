/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Filter
public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.Analysis.Oscillation
public import Mathlib.Data.Bool.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Integrals of Riemann, Henstock-Kurzweil, and McShane

In this file we define the integral of a function over a box in `ℝⁿ`. The same definition works for
Riemann, Henstock-Kurzweil, and McShane integrals.

As usual, we represent `ℝⁿ` as the type of functions `ι → ℝ` for some finite type `ι`. A rectangular
box `(l, u]` in `ℝⁿ` is defined to be the set `{x : ι → ℝ | ∀ i, l i < x i ∧ x i ≤ u i}`, see
`BoxIntegral.Box`.

Let `vol` be a box-additive function on boxes in `ℝⁿ` with codomain `E →L[ℝ] F`. Given a function
`f : ℝⁿ → E`, a box `I` and a tagged partition `π` of this box, the *integral sum* of `f` over `π`
with respect to the volume `vol` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. Here
`π.tag J` is the point (tag) in `ℝⁿ` associated with the box `J`.

The integral is defined as the limit of integral sums along a filter. Different filters correspond
to different integration theories. In order to avoid code duplication, all our definitions and
theorems take an argument `l : BoxIntegral.IntegrationParams`. This is a type that holds three
Boolean values, and encodes eight filters including those corresponding to Riemann,
Henstock-Kurzweil, and McShane integrals.

Following the design of infinite sums (see `hasSum` and `tsum`), we define a predicate
`BoxIntegral.HasIntegral` and a function `BoxIntegral.integral` that returns a vector satisfying
the predicate or zero if the function is not integrable.

Then we prove some basic properties of box integrals (linearity, a formula for the integral of a
constant). We also prove a version of the Henstock-Sacks inequality (see
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`), prove
integrability of continuous functions, and provide a criterion for integrability w.r.t. a
non-Riemann filter (e.g., Henstock-Kurzweil and McShane).

## Notation

- `ℝⁿ`: local notation for `ι → ℝ`

## Tags

integral
-/

@[expose] public section

open scoped Topology NNReal Filter Uniformity BoxIntegral

open Set Finset Function Filter Metric BoxIntegral.IntegrationParams

noncomputable section

namespace BoxIntegral

universe u v w

variable {ι : Type u} {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {I J : Box ι} {π : TaggedPrepartition I}

open TaggedPrepartition

local notation "ℝⁿ" => ι → ℝ

/-!
### Integral sum and its basic properties
-/

/-- The integral sum of `f : ℝⁿ → E` over a tagged prepartition `π` w.r.t. box-additive volume `vol`
with codomain `E →L[ℝ] F` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. -/
/-
**BoxIntegral.integralSum** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepa
rtition I) : F
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartition I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The integral sum of `f : ℝⁿ → E` over a tagged prepartition `π` w.r.t. box-addit
ive volume `vol`
with codomain `E →L[ℝ] F` is the sum of `vol J (f (π.tag J))` over all boxes of 
`π`.
-/
def integralSum (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) : F :=
  ∑ J ∈ π.boxes, vol J (f (π.tag J))
/-
**BoxIntegral.integralSum_congr** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_congr {f₁ f₂ : Realⁿ -> E} {vol₁ vol₂ : ι ->ᵇᵃ E ->L[Real] F} 
(hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ π.boxes) : integralSum f₁ vol₁ π 
= integralSum f₂ vol₂ π
参数：hf : EqOn f₁ f₂ I.Icc；hvol : EqOn vol₁ vol₂ π.boxes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `BoxIntegral.TaggedPrepartition.tag_mem_Icc`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (self : BoxIntegral.TaggedPrepartition I) (J : BoxIntegral.Box ι), 
  self.tag J ∈ BoxIntegral.Box.I…
-/
theorem integralSum_congr {f₁ f₂ : ℝⁿ → E} {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F}
    (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ π.boxes) :
    integralSum f₁ vol₁ π = integralSum f₂ vol₂ π := by
  unfold integralSum
  refine Finset.sum_congr rfl (fun J hJ ↦ ?_)
  congr 1
  · exact hvol hJ
  exact hf (π.tag_mem_Icc J)
/-
**BoxIntegral.integralSum_biUnionTagged** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_biUnionTagged (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π
 : Prepartition I) (πi : forall J, TaggedPrepartition J) : integralSum f vol (π.
biUnionTagged πi) = ∑ J in π.boxes, integralSum f vol (πi J)
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : Prepartition I；πi : forall J, T
aggedPrepartition J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.sum_biUnion_boxes`：sum_biUnion_boxes {M : Type*
} [AddCommMonoid M] (π : Prepartition I) (πi : forall J, Prepartition J) (f : Bo
x ι -> M) : (∑ J in π.boxes.biUn…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.tag_biUnionTagged`：tag_biUnionTagged (π : Prepa
rtition I) {πi : forall J, TaggedPrepartition J} (hJ : J in π) {J'} (hJ' : J' in
 πi J) : (π.biUnionTagged πi).ta…
-/
theorem integralSum_biUnionTagged (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    integralSum f vol (π.biUnionTagged πi) = ∑ J ∈ π.boxes, integralSum f vol (πi J) := by
  refine (π.sum_biUnion_boxes _ _).trans <| sum_congr rfl fun J hJ => sum_congr rfl fun J' hJ' => ?_
  rw [π.tag_biUnionTagged hJ hJ']
/-
**BoxIntegral.integralSum_biUnion_partition** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al`。
形式化陈述：integralSum_biUnion_partition (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F
) (π : TaggedPrepartition I) (πi : forall J, Prepartition J) (hπi : forall J in 
π, (πi J).IsPartition) : integralSum f vol (π.biUnionPrepartition πi) = integral
Sum f vol π
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartition I；πi : foral
l J, Prepartition J；hπi : forall J in π, (πi J).IsPartition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.sum_biUnion_boxes`：sum_biUnion_boxes {M : Type*
} [AddCommMonoid M] (π : Prepartition I) (πi : forall J, Prepartition J) (f : Bo
x ι -> M) : (∑ J in π.boxes.biUn…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex_of_mem`：biUnionIndex_of_mem (hJ : 
J in π) {J'} (hJ' : J' in πi J) : π.biUnionIndex πi J' = J
· 使用定理 `BoxIntegral.BoxAdditiveMap.sum_partition_boxes`：sum_partition_boxes (f :
 ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I} (h : π.IsPartition) : ∑ J in
 π.boxes, f J = f I
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem integralSum_biUnion_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) (hπi : ∀ J ∈ π, (πi J).IsPartition) :
    integralSum f vol (π.biUnionPrepartition πi) = integralSum f vol π := by
  refine (π.sum_biUnion_boxes _ _).trans (sum_congr rfl fun J hJ => ?_)
  calc
    (∑ J' ∈ (πi J).boxes, vol J' (f (π.tag <| π.toPrepartition.biUnionIndex πi J'))) =
        ∑ J' ∈ (πi J).boxes, vol J' (f (π.tag J)) :=
      sum_congr rfl fun J' hJ' => by rw [Prepartition.biUnionIndex_of_mem _ hJ hJ']
    _ = vol J (f (π.tag J)) :=
      (vol.map ⟨⟨fun g : E →L[ℝ] F => g (f (π.tag J)), rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes
        le_top (hπi J hJ)
/-
**BoxIntegral.integralSum_inf_partition** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_inf_partition (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π
 : TaggedPrepartition I) {π' : Prepartition I} (h : π'.IsPartition) : integralSu
m f vol (π.infPrepartition π') = integralSum f vol π
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartition I；h : π'.IsP
artition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.integralSum_biUnion_partition`：integralSum_biUnion_partition
 (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I) (πi : 
forall J, Prepartition J) (hπi …
· 使用定理 `BoxIntegral.Prepartition.IsPartition.restrict`：∀ {ι : Type u_1} {I J : B
oxIntegral.Box ι} {π : BoxIntegral.Prepartition I},   π.IsPartition → J ≤ I → (π
.restrict J).IsPartition
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
-/
theorem integralSum_inf_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I)
    {π' : Prepartition I} (h : π'.IsPartition) :
    integralSum f vol (π.infPrepartition π') = integralSum f vol π :=
  integralSum_biUnion_partition f vol π _ fun _J hJ => h.restrict (Prepartition.le_of_mem _ hJ)

open scoped Classical in
/-
**BoxIntegral.integralSum_fiberwise** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_fiberwise {α} (g : Box ι -> α) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ 
E ->L[Real] F) (π : TaggedPrepartition I) : (∑ y in π.boxes.image g, integralSum
 f vol (π.filter (g · = y))) = integralSum f vol π
参数：g : Box ι -> α；f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartiti
on I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.Prepartition.sum_fiberwise`：sum_fiberwise {α M} [AddCommMono
id M] (π : Prepartition I) (f : Box ι -> α) (g : Box ι -> M) : (∑ y in π.boxes.i
mage f, ∑ J in (π.filter fun…
-/
theorem integralSum_fiberwise {α} (g : Box ι → α) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    (∑ y ∈ π.boxes.image g, integralSum f vol (π.filter (g · = y))) = integralSum f vol π :=
  π.sum_fiberwise g fun J => vol J (f <| π.tag J)
/-
**BoxIntegral.integralSum_sub_partitions** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`
。
形式化陈述：integralSum_sub_partitions (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) {
π₁ π₂ : TaggedPrepartition I} (h₁ : π₁.IsPartition) (h₂ : π₂.IsPartition) : inte
gralSum f vol π₁ - integralSum f vol π₂ = ∑ J in (π₁.toPrepartition ⊓ π₂.toPrepa
rtition).boxes, (vol J (f <| (π₁.infPrepartition π₂.toPrepartition).tag J) - vol
 J (f <| (π₂.infPrepartition π₁.toPrepartition).tag J))
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；h₁ : π₁.IsPartition；h₂ : π₂.IsParti
tion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.integralSum_inf_partition`：integralSum_inf_partition (f : Re
alⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I) {π' : Preparti
tion I} (h : π'.IsPartition…
· 使用定理 `BoxIntegral.integralSum.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [inst_3 …
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralSum_sub_partitions (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    {π₁ π₂ : TaggedPrepartition I} (h₁ : π₁.IsPartition) (h₂ : π₂.IsPartition) :
    integralSum f vol π₁ - integralSum f vol π₂ =
      ∑ J ∈ (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes,
        (vol J (f <| (π₁.infPrepartition π₂.toPrepartition).tag J) -
          vol J (f <| (π₂.infPrepartition π₁.toPrepartition).tag J)) := by
  rw [← integralSum_inf_partition f vol π₁ h₂, ← integralSum_inf_partition f vol π₂ h₁,
    integralSum, integralSum, Finset.sum_sub_distrib]
  simp only [infPrepartition_toPrepartition, inf_comm]

@[simp]
/-
**BoxIntegral.integralSum_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_disjUnion (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) {π₁ π₂
 : TaggedPrepartition I} (h : Disjoint π₁.iUnion π₂.iUnion) : integralSum f vol 
(π₁.disjUnion π₂ h) = integralSum f vol π₁ + integralSum f vol π₂
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.sum_disj_union_boxes`：sum_disj_union_boxes {M :
 Type*} [AddCommMonoid M] (h : Disjoint π₁.iUnion π₂.iUnion) (f : Box ι -> M) : 
∑ J in π₁.boxes union π₂.boxes, f J…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left`：disjUnion_tag_
of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁) : (π₁.disjUnion π₂
 h).tag J = π₁.tag J
· 使用定理 `BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right`：disjUnion_tag
_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₂) : (π₁.disjUnion 
π₂ h).tag J = π₂.tag J
-/
theorem integralSum_disjUnion (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) {π₁ π₂ : TaggedPrepartition I}
    (h : Disjoint π₁.iUnion π₂.iUnion) :
    integralSum f vol (π₁.disjUnion π₂ h) = integralSum f vol π₁ + integralSum f vol π₂ := by
  refine (Prepartition.sum_disj_union_boxes h _).trans
      (congr_arg₂ (· + ·) (sum_congr rfl fun J hJ => ?_) (sum_congr rfl fun J hJ => ?_))
  · rw [disjUnion_tag_of_mem_left _ hJ]
  · rw [disjUnion_tag_of_mem_right _ hJ]

@[simp]
/-
**BoxIntegral.integralSum_add** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_add (f g : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : Tagge
dPrepartition I) : integralSum (f + g) vol π = integralSum f vol π + integralSum
 g vol π
参数：f g : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralSum_add (f g : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) :
    integralSum (f + g) vol π = integralSum f vol π + integralSum g vol π := by
  simp only [integralSum, Pi.add_apply, (vol _).map_add, Finset.sum_add_distrib]

@[simp]
/-
**BoxIntegral.integralSum_neg** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_neg (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedP
repartition I) : integralSum (-f) vol π = -integralSum f vol π
参数：f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearMap.map_neg`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralSum_neg (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) :
    integralSum (-f) vol π = -integralSum f vol π := by
  simp only [integralSum, Pi.neg_apply, (vol _).map_neg, Finset.sum_neg_distrib]

@[simp]
/-
**BoxIntegral.integralSum_smul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integralSum_smul (c : Real) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) 
(π : TaggedPrepartition I) : integralSum (c • f) vol π = c • integralSum f vol π
参数：c : Real；f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；π : TaggedPrepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralSum_smul (c : ℝ) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) :
    integralSum (c • f) vol π = c • integralSum f vol π := by
  simp only [integralSum, Finset.smul_sum, Pi.smul_apply, map_smul]

variable [Fintype ι]

/-!
### Basic integrability theory
-/

/-- The predicate `HasIntegral I l f vol y` says that `y` is the integral of `f` over `I` along `l`
w.r.t. volume `vol`. This means that integral sums of `f` tend to `𝓝 y` along
`BoxIntegral.IntegrationParams.toFilteriUnion I ⊤`. -/
/-
**BoxIntegral.HasIntegral** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral`。
形式化陈述：HasIntegral (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι 
->ᵇᵃ E ->L[Real] F) (y : F) : Prop
参数：I : Box ι；l : IntegrationParams；f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F；y :
 F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate `HasIntegral I l f vol y` says that `y` is the integral of `f` ove
r `I` along `l`
w.r.t. volume `vol`. This means that integral sums of `f` tend to `𝓝 y` along
`BoxIntegral.IntegrationParams.toFilteriUnion I ⊤`.
-/
def HasIntegral (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (y : F) :
    Prop :=
  Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y)

/-- A function is integrable if there exists a vector that satisfies the `HasIntegral`
predicate. -/
/-
**BoxIntegral.Integrable** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral`。
形式化陈述：Integrable (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι -
>ᵇᵃ E ->L[Real] F)
参数：I : Box ι；l : IntegrationParams；f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is integrable if there exists a vector that satisfies the `HasIntegra
l`
predicate.
-/
def Integrable (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  ∃ y, HasIntegral I l f vol y

open scoped Classical in
/-- The integral of a function `f` over a box `I` along a filter `l` w.r.t. a volume `vol`.
Returns zero on non-integrable functions. -/
/-
**BoxIntegral.integral** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral`。
形式化陈述：integral (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇ
ᵃ E ->L[Real] F)
参数：I : Box ι；l : IntegrationParams；f : Realⁿ -> E；vol : ι ->ᵇᵃ E ->L[Real] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The integral of a function `f` over a box `I` along a filter `l` w.r.t. a volume
 `vol`.
Returns zero on non-integrable functions.
-/
def integral (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  if h : Integrable I l f vol then h.choose else 0
/-
**BoxIntegral.hasIntegral_congr** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegral_congr (I : Box ι) (l : IntegrationParams) {f₁ f₂ : Realⁿ -> E}
 {vol₁ vol₂ : ι ->ᵇᵃ E ->L[Real] F} (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vo
l₂ (Set.Iic I)) (y : F) : HasIntegral I l f₁ vol₁ y ↔ HasIntegral I l f₂ vol₂ y
参数：I : Box ι；l : IntegrationParams；hf : EqOn f₁ f₂ I.Icc；hvol : EqOn vol₁ vol₂ (
Set.Iic I)；y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.tendsto_congr`：tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂
 : Filter β} (h : forall x, f₁ x = f₂ x) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `BoxIntegral.integralSum_congr`：integralSum_congr {f₁ f₂ : Realⁿ -> E} {v
ol₁ vol₂ : ι ->ᵇᵃ E ->L[Real] F} (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ 
π.boxes) : integral…
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `BoxIntegral.Prepartition.le_of_mem'`：∀ {ι : Type u_1} {I : BoxIntegral.B
ox ι} (self : BoxIntegral.Prepartition I), ∀ J ∈ self.boxes, J ≤ I
-/
theorem hasIntegral_congr (I : Box ι) (l : IntegrationParams) {f₁ f₂ : ℝⁿ → E}
    {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F}
    (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ (Set.Iic I)) (y : F) :
    HasIntegral I l f₁ vol₁ y ↔ HasIntegral I l f₂ vol₂ y := by
  unfold HasIntegral
  refine Filter.tendsto_congr (fun π ↦ integralSum_congr hf (hvol.mono ?_))
  intro J hJ
  simp [π.le_of_mem' J hJ]

-- Porting note: using the above notation ℝⁿ here causes the theorem below to be silently ignored
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Lean.204.20doesn't.20add.20lemma.20to.20the.20environment/near/363764522
-- and https://github.com/leanprover/lean4/issues/2257
variable {l : IntegrationParams} {f g : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {y y' : F}

/-- Reinterpret `BoxIntegral.HasIntegral` as `Filter.Tendsto`, e.g., dot-notation theorems
that are shadowed in the `BoxIntegral.HasIntegral` namespace. -/
/-
**BoxIntegral.HasIntegral.tendsto** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasInte
gral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y 
: F},   BoxIntegral.HasIntegral I l f vol y →     Filter.Tendsto (BoxIntegral.in
tegralSum f vol) (BoxIntegral.IntegrationParams.toFilteriUnion I ⊤) (nhds y)
参数：ι → ℝ；E →L[ℝ] F；BoxIntegral.integralSum f vol；BoxIntegral.IntegrationParams.t
oFilteriUnion I ⊤；nhds y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Reinterpret `BoxIntegral.HasIntegral` as `Filter.Tendsto`, e.g., dot-notation th
eorems
that are shadowed in the `BoxIntegral.HasIntegral` namespace.
-/
theorem HasIntegral.tendsto (h : HasIntegral I l f vol y) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y) :=
  h

/-- The `ε`-`δ` definition of `BoxIntegral.HasIntegral`. -/
/-
**BoxIntegral.hasIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegral_iff : HasIntegral I l f vol y ↔ forall ε > (0 : Real), exists 
r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c, l.RCond (r c)) ∧ forall c π, 
l.MemBaseSet I c (r c) π -> IsPartition π -> dist (integralSum f vol π) y <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion_top`：hasBasis_toFi
lteriUnion_top (l : IntegrationParams) (I : Box ι) : (l.toFilteriUnion I ⊤).HasB
asis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 …
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The `ε`-`δ` definition of `BoxIntegral.HasIntegral`.
-/
theorem hasIntegral_iff : HasIntegral I l f vol y ↔
    ∀ ε > (0 : ℝ), ∃ r : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ), (∀ c, l.RCond (r c)) ∧
      ∀ c π, l.MemBaseSet I c (r c) π → IsPartition π → dist (integralSum f vol π) y ≤ ε :=
  ((l.hasBasis_toFilteriUnion_top I).tendsto_iff nhds_basis_closedBall).trans <| by
    simp [@forall_comm ℝ≥0 (TaggedPrepartition I)]

/-- Quite often it is more natural to prove an estimate of the form `a * ε`, not `ε` in the RHS of
`BoxIntegral.hasIntegral_iff`, so we provide this auxiliary lemma. -/
/-
**BoxIntegral.HasIntegral.of_mul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasInteg
ral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y 
: F}   (a : ℝ),   (∀ (ε : ℝ),       0 < ε →         ∃ r,           (∀ (c : NNRea
l), l.RCond (r c)) ∧             ∀ (c : NNReal) (π : BoxIntegral.TaggedPrepartit
ion I),               l.MemBaseSet I c (r c) π → π.IsPartition → dist (BoxIntegr
al.integralSum f vol π) y ≤ a * ε) →     BoxIntegral.HasIntegral I l f vol y
参数：ι → ℝ；E →L[ℝ] F；a : ℝ；∀ (ε : ℝ),       0 < ε →         ∃ r,           (∀ (c :
 NNReal), l.RCond (r c)) ∧             ∀ (c : NNReal) (π : BoxIntegral.TaggedPre
partition I),               l.MemBaseSet I c (r c) π → π.IsPartition → dist (Box
Integral.integralSum f vol π) y ≤ a * ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.hasIntegral_iff`：hasIntegral_iff : HasIntegral I l f vol y ↔
 forall ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c
, l.RCond (r c)) …
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Quite often it is more natural to prove an estimate of the form `a * ε`, not `ε`
 in the RHS of
`BoxIntegral.hasIntegral_iff`, so we provide this auxiliary lemma.
-/
theorem HasIntegral.of_mul (a : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ), (∀ c, l.RCond (r c)) ∧ ∀ c π,
      l.MemBaseSet I c (r c) π → IsPartition π → dist (integralSum f vol π) y ≤ a * ε) :
    HasIntegral I l f vol y := by
  refine hasIntegral_iff.2 fun ε hε => ?_
  rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩
  rcases h ε' hε' with ⟨r, hr, H⟩
  exact ⟨r, hr, fun c π hπ hπp => (H c π hπ hπp).trans ha.le⟩
/-
**BoxIntegral.integrable_iff_cauchy** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integrable_iff_cauchy [CompleteSpace F] : Integrable I l f vol ↔ Cauchy ((
l.toFilteriUnion I ⊤).map (integralSum f vol))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `cauchy_map_iff_exists_tendsto`：cauchy_map_iff_exists_tendsto [CompleteSp
ace α] {l : Filter β} {f : β -> α} [NeBot l] : Cauchy (l.map f) ↔ exists x, Tend
sto f l (𝓝 x)
-/
theorem integrable_iff_cauchy [CompleteSpace F] :
    Integrable I l f vol ↔ Cauchy ((l.toFilteriUnion I ⊤).map (integralSum f vol)) :=
  cauchy_map_iff_exists_tendsto.symm

/-- In a complete space, a function is integrable if and only if its integral sums form a Cauchy
net. Here we restate this fact in terms of `∀ ε > 0, ∃ r, ...`. -/
/-
**BoxIntegral.integrable_iff_cauchy_basis** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
`。
形式化陈述：integrable_iff_cauchy_basis [CompleteSpace F] : Integrable I l f vol ↔ for
all ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c, l.
RCond (r c)) ∧ forall c₁ c₂ π₁ π₂, l.MemBaseSet I c₁ (r c₁) π₁ -> π₁.IsPartition
 -> l.MemBaseSet I c₂ (r c₂) π₂ -> π₂.IsPartition -> dist (integralSum f vol π₁)
 (integralSum f vol π₂) <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.integrable_iff_cauchy`：integrable_iff_cauchy [CompleteSpace 
F] : Integrable I l f vol ↔ Cauchy ((l.toFilteriUnion I ⊤).map (integralSum f vo
l))
· 使用定理 `cauchy_map_iff'`：cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β ->
 α} : Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α
)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion_top`：hasBasis_toFi
lteriUnion_top (l : IntegrationParams) (I : Box ι) : (l.toFilteriUnion I ⊤).HasB
asis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 …
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a complete space, a function is integrable if and only if its integral sums f
orm a Cauchy
net. Here we restate this fact in terms of `∀ ε > 0, ∃ r, ...`.
-/
theorem integrable_iff_cauchy_basis [CompleteSpace F] : Integrable I l f vol ↔
    ∀ ε > (0 : ℝ), ∃ r : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ), (∀ c, l.RCond (r c)) ∧
      ∀ c₁ c₂ π₁ π₂, l.MemBaseSet I c₁ (r c₁) π₁ → π₁.IsPartition → l.MemBaseSet I c₂ (r c₂) π₂ →
        π₂.IsPartition → dist (integralSum f vol π₁) (integralSum f vol π₂) ≤ ε := by
  rw [integrable_iff_cauchy, cauchy_map_iff',
    (l.hasBasis_toFilteriUnion_top _).prod_self.tendsto_iff uniformity_basis_dist_le]
  refine forall₂_congr fun ε _ => exists_congr fun r => ?_
  simp only [Prod.forall, exists_imp, prodMk_mem_set_prod_eq, and_imp, mem_ofPred_eq]
  exact
    and_congr Iff.rfl
      ⟨fun H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂ => H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂,
        fun H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂ => H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂⟩
/-
**BoxIntegral.HasIntegral.mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasIntegra
l`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {f : (ι → ℝ) → E} {vol : Box
Integral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y : F} {l₁ l₂ : BoxIntegral.Integratio
nParams},   BoxIntegral.HasIntegral I l₁ f vol y → l₂ ≤ l₁ → BoxIntegral.HasInte
gral I l₂ f vol y
参数：ι → ℝ；E →L[ℝ] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `BoxIntegral.IntegrationParams.toFilteriUnion_mono`：toFilteriUnion_mono (
I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂) (π₀ : Prepartition I) : l₁
.toFilteriUnion I π₀ <= l₂.toFilteriUni…
-/
theorem HasIntegral.mono {l₁ l₂ : IntegrationParams} (h : HasIntegral I l₁ f vol y) (hl : l₂ ≤ l₁) :
    HasIntegral I l₂ f vol y :=
  h.mono_left <| IntegrationParams.toFilteriUnion_mono _ hl _
/-
**BoxIntegral.Integrable.hasIntegral** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Inte
grable`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤},   
BoxIntegral.Integrable I l f vol → BoxIntegral.HasIntegral I l f vol (BoxIntegra
l.integral I l f vol)
参数：ι → ℝ；E →L[ℝ] F；BoxIntegral.integral I l f vol。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.integral.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGr
oup F] [inst_3 …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem Integrable.hasIntegral (h : Integrable I l f vol) :
    HasIntegral I l f vol (integral I l f vol) := by
  rw [integral, dif_pos h]
  exact Classical.choose_spec h
/-
**BoxIntegral.Integrable.mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`
。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤}   {
l' : BoxIntegral.IntegrationParams}, BoxIntegral.Integrable I l f vol → l' ≤ l →
 BoxIntegral.Integrable I l' f vol
参数：ι → ℝ；E →L[ℝ] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.mono`：∀ {ι : Type u} {E : Type v} {F : Type w} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem Integrable.mono {l'} (h : Integrable I l f vol) (hle : l' ≤ l) : Integrable I l' f vol :=
  ⟨_, h.hasIntegral.mono hle⟩
/-
**BoxIntegral.HasIntegral.unique** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasInteg
ral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y 
y' : F},   BoxIntegral.HasIntegral I l f vol y → BoxIntegral.HasIntegral I l f v
ol y' → y = y'
参数：ι → ℝ；E →L[ℝ] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem HasIntegral.unique (h : HasIntegral I l f vol y) (h' : HasIntegral I l f vol y') : y = y' :=
  tendsto_nhds_unique h h'
/-
**BoxIntegral.HasIntegral.integrable** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasI
ntegral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y 
: F},   BoxIntegral.HasIntegral I l f vol y → BoxIntegral.Integrable I l f vol
参数：ι → ℝ；E →L[ℝ] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem HasIntegral.integrable (h : HasIntegral I l f vol y) : Integrable I l f vol :=
  ⟨_, h⟩
/-
**BoxIntegral.HasIntegral.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Has
Integral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y 
: F},   BoxIntegral.HasIntegral I l f vol y → BoxIntegral.integral I l f vol = y
参数：ι → ℝ；E →L[ℝ] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.unique`：∀ {ι : Type u} {E : Type v} {F : Type w}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddC
ommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.integrable`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem HasIntegral.integral_eq (h : HasIntegral I l f vol y) : integral I l f vol = y :=
  h.integrable.hasIntegral.unique h

nonrec theorem HasIntegral.add (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f + g) vol (y + y') := by
  simpa only [HasIntegral, ← integralSum_add] using h.add h'
/-
**BoxIntegral.Integrable.add** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f g : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤}, 
  BoxIntegral.Integrable I l f vol → BoxIntegral.Integrable I l g vol → BoxInteg
ral.Integrable I l (f + g) vol
参数：ι → ℝ；E →L[ℝ] F；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integrable`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.add`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem Integrable.add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    Integrable I l (f + g) vol :=
  (hf.hasIntegral.add hg.hasIntegral).integrable
/-
**BoxIntegral.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_add (hf : Integrable I l f vol) (hg : Integrable I l g vol) : int
egral I l (f + g) vol = integral I l f vol + integral I l g vol
参数：hf : Integrable I l f vol；hg : Integrable I l g vol。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.add`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem integral_add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
  (hf.hasIntegral.add hg.hasIntegral).integral_eq

nonrec theorem HasIntegral.neg (hf : HasIntegral I l f vol y) : HasIntegral I l (-f) vol (-y) := by
  simpa only [HasIntegral, ← integralSum_neg] using hf.neg
/-
**BoxIntegral.Integrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤},   
BoxIntegral.Integrable I l f vol → BoxIntegral.Integrable I l (-f) vol
参数：ι → ℝ；E →L[ℝ] F；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integrable`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.neg`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem Integrable.neg (hf : Integrable I l f vol) : Integrable I l (-f) vol :=
  hf.hasIntegral.neg.integrable
/-
**BoxIntegral.Integrable.of_neg** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrabl
e`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤},   
BoxIntegral.Integrable I l (-f) vol → BoxIntegral.Integrable I l f vol
参数：ι → ℝ；E →L[ℝ] F；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.Integrable.neg`：∀ {ι : Type u} {E : Type v} {F : Type w} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommG
roup F] [inst_3 …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem Integrable.of_neg (hf : Integrable I l (-f) vol) : Integrable I l f vol :=
  neg_neg f ▸ hf.neg

@[simp]
/-
**BoxIntegral.integrable_neg** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integrable_neg : Integrable I l (-f) vol ↔ Integrable I l f vol
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.Integrable.of_neg`：∀ {ι : Type u} {E : Type v} {F : Type w} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCo
mmGroup F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.neg`：∀ {ι : Type u} {E : Type v} {F : Type w} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommG
roup F] [inst_3 …
-/
theorem integrable_neg : Integrable I l (-f) vol ↔ Integrable I l f vol :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩

@[simp]
/-
**BoxIntegral.integral_neg** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_neg : integral I l (-f) vol = -integral I l f vol
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.neg`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.integral.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGr
oup F] [inst_3 …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `BoxIntegral.Integrable.of_neg`：∀ {ι : Type u} {E : Type v} {F : Type w} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCo
mmGroup F] [inst_3 …
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem integral_neg : integral I l (-f) vol = -integral I l f vol := by
  classical
  exact if h : Integrable I l f vol then h.hasIntegral.neg.integral_eq
  else by rw [integral, integral, dif_neg h, dif_neg (mt Integrable.of_neg h), neg_zero]
/-
**BoxIntegral.HasIntegral.sub** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasIntegral
`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f g : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {
y y' : F},   BoxIntegral.HasIntegral I l f vol y →     BoxIntegral.HasIntegral I
 l g vol y' → BoxIntegral.HasIntegral I l (f - g) vol (y - y')
参数：ι → ℝ；E →L[ℝ] F；f - g；y - y'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `BoxIntegral.HasIntegral.add`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.neg`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
-/
theorem HasIntegral.sub (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f - g) vol (y - y') := by simpa only [sub_eq_add_neg] using h.add h'.neg
/-
**BoxIntegral.Integrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f g : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤}, 
  BoxIntegral.Integrable I l f vol → BoxIntegral.Integrable I l g vol → BoxInteg
ral.Integrable I l (f - g) vol
参数：ι → ℝ；E →L[ℝ] F；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integrable`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.sub`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem Integrable.sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    Integrable I l (f - g) vol :=
  (hf.hasIntegral.sub hg.hasIntegral).integrable
/-
**BoxIntegral.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) : int
egral I l (f - g) vol = integral I l f vol - integral I l g vol
参数：hf : Integrable I l f vol；hg : Integrable I l g vol。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.sub`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem integral_sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
  (hf.hasIntegral.sub hg.hasIntegral).integral_eq
/-
**BoxIntegral.hasIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegral_const (c : E) : HasIntegral I l (fun _ => c) vol (vol I c)
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `BoxIntegral.IntegrationParams.eventually_isPartition`：eventually_isParti
tion (l : IntegrationParams) (I : Box ι) : forallᶠ π in l.toFilteriUnion I ⊤, Ta
ggedPrepartition.IsPartition π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.BoxAdditiveMap.sum_partition_boxes`：sum_partition_boxes (f :
 ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I} (h : π.IsPartition) : ∑ J in
 π.boxes, f J = f I
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem hasIntegral_const (c : E) : HasIntegral I l (fun _ => c) vol (vol I c) :=
  tendsto_const_nhds.congr' <| (l.eventually_isPartition I).mono fun _π hπ => Eq.symm <|
    (vol.map ⟨⟨fun g : E →L[ℝ] F ↦ g c, rfl⟩, fun _ _ ↦ rfl⟩).sum_partition_boxes le_top hπ

@[simp]
/-
**BoxIntegral.integral_const** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_const (c : E) : integral I l (fun _ => c) vol = vol I c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.hasIntegral_const`：hasIntegral_const (c : E) : HasIntegral I
 l (fun _ => c) vol (vol I c)
-/
theorem integral_const (c : E) : integral I l (fun _ => c) vol = vol I c :=
  (hasIntegral_const c).integral_eq
/-
**BoxIntegral.integrable_const** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integrable_const (c : E) : Integrable I l (fun _ => c) vol
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.hasIntegral_const`：hasIntegral_const (c : E) : HasIntegral I
 l (fun _ => c) vol (vol I c)
-/
theorem integrable_const (c : E) : Integrable I l (fun _ => c) vol :=
  ⟨_, hasIntegral_const c⟩
/-
**BoxIntegral.hasIntegral_zero** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegral_zero : HasIntegral I l (fun _ => (0 : E)) vol 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `BoxIntegral.hasIntegral_const`：hasIntegral_const (c : E) : HasIntegral I
 l (fun _ => c) vol (vol I c)
-/
theorem hasIntegral_zero : HasIntegral I l (fun _ => (0 : E)) vol 0 := by
  simpa only [← (vol I).map_zero] using hasIntegral_const (0 : E)
/-
**BoxIntegral.integrable_zero** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integrable_zero : Integrable I l (fun _ => (0 : E)) vol
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.hasIntegral_zero`：hasIntegral_zero : HasIntegral I l (fun _ 
=> (0 : E)) vol 0
-/
theorem integrable_zero : Integrable I l (fun _ => (0 : E)) vol :=
  ⟨0, hasIntegral_zero⟩
/-
**BoxIntegral.integral_zero** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_zero : integral I l (fun _ => (0 : E)) vol = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.hasIntegral_zero`：hasIntegral_zero : HasIntegral I l (fun _ 
=> (0 : E)) vol 0
-/
theorem integral_zero : integral I l (fun _ => (0 : E)) vol = 0 :=
  hasIntegral_zero.integral_eq
/-
**BoxIntegral.HasIntegral.sum** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasIntegral
`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {α : Type u_1} {s : F
inset α}   {f : α → (ι → ℝ) → E} {g : α → F},   (∀ i ∈ s, BoxIntegral.HasIntegra
l I l (f i) vol (g i)) →     BoxIntegral.HasIntegral I l (fun x => ∑ i ∈ s, f i 
x) vol (∑ i ∈ s, g i)
参数：E →L[ℝ] F；ι → ℝ；∀ i ∈ s, BoxIntegral.HasIntegral I l (f i) vol (g i)；fun x =>
 ∑ i ∈ s, f i x；∑ i ∈ s, g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `BoxIntegral.HasIntegral.add`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasIntegral.sum {α : Type*} {s : Finset α} {f : α → ℝⁿ → E} {g : α → F}
    (h : ∀ i ∈ s, HasIntegral I l (f i) vol (g i)) :
    HasIntegral I l (fun x => ∑ i ∈ s, f i x) vol (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hasIntegral_zero]
  | insert a s ha ihs =>
    simp only [Finset.sum_insert ha]; rw [Finset.forall_mem_insert] at h
    exact h.1.add (ihs h.2)
/-
**BoxIntegral.HasIntegral.smul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasIntegra
l`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y 
: F},   BoxIntegral.HasIntegral I l f vol y → ∀ (c : ℝ), BoxIntegral.HasIntegral
 I l (c • f) vol (c • y)
参数：ι → ℝ；E →L[ℝ] F；c : ℝ；c • f；c • y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem HasIntegral.smul (hf : HasIntegral I l f vol y) (c : ℝ) :
    HasIntegral I l (c • f) vol (c • y) := by
  simpa only [HasIntegral, ← integralSum_smul] using
    (tendsto_const_nhds : Tendsto _ _ (𝓝 c)).smul hf
/-
**BoxIntegral.Integrable.smul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`
。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤},   
BoxIntegral.Integrable I l f vol → ∀ (c : ℝ), BoxIntegral.Integrable I l (c • f)
 vol
参数：ι → ℝ；E →L[ℝ] F；c : ℝ；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.integrable`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.smul`：∀ {ι : Type u} {E : Type v} {F : Type w} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
-/
theorem Integrable.smul (hf : Integrable I l f vol) (c : ℝ) : Integrable I l (c • f) vol :=
  (hf.hasIntegral.smul c).integrable
/-
**BoxIntegral.Integrable.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrab
le`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {c 
: ℝ},   BoxIntegral.Integrable I l (c • f) vol → c ≠ 0 → BoxIntegral.Integrable 
I l f vol
参数：ι → ℝ；E →L[ℝ] F；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `BoxIntegral.Integrable.smul`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
-/
theorem Integrable.of_smul {c : ℝ} (hf : Integrable I l (c • f) vol) (hc : c ≠ 0) :
    Integrable I l f vol := by
  simpa [inv_smul_smul₀ hc] using hf.smul c⁻¹

@[simp]
/-
**BoxIntegral.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_smul (c : Real) : integral I l (fun x => c • f x) vol = c • integ
ral I l f vol
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `BoxIntegral.integral_zero`：integral_zero : integral I l (fun _ => (0 : E
)) vol = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.smul`：∀ {ι : Type u} {E : Type v} {F : Type w} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [inst_3 …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `BoxIntegral.Integrable.of_smul`：∀ {ι : Type u} {E : Type v} {F : Type w}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddC
ommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.integral.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGr
oup F] [inst_3 …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem integral_smul (c : ℝ) : integral I l (fun x => c • f x) vol = c • integral I l f vol := by
  rcases eq_or_ne c 0 with (rfl | hc); · simp only [zero_smul, integral_zero]
  by_cases hf : Integrable I l f vol
  · exact (hf.hasIntegral.smul c).integral_eq
  · have : ¬Integrable I l (fun x => c • f x) vol := mt (fun h => h.of_smul hc) hf
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero]

open MeasureTheory

/-- The integral of a nonnegative function w.r.t. a volume generated by a locally-finite measure is
nonnegative. -/
/-
**BoxIntegral.integral_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：integral_nonneg {g : Realⁿ -> Real} (hg : forall x in Box.Icc I, 0 <= g x)
 (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] : 0 <= integral I l g μ.toBoxAdd
itive.toSMul
参数：hg : forall x in Box.Icc I, 0 <= g x；μ : Measure Realⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `BoxIntegral.TaggedPrepartition.tag_mem_Icc`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (self : BoxIntegral.TaggedPrepartition I) (J : BoxIntegral.Box ι), 
  self.tag J ∈ BoxIntegral.Box.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.integral.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGr
oup F] [inst_3 …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The integral of a nonnegative function w.r.t. a volume generated by a locally-fi
nite measure is
nonnegative.
-/
theorem integral_nonneg {g : ℝⁿ → ℝ} (hg : ∀ x ∈ Box.Icc I, 0 ≤ g x) (μ : Measure ℝⁿ)
    [IsLocallyFiniteMeasure μ] : 0 ≤ integral I l g μ.toBoxAdditive.toSMul := by
  by_cases hgi : Integrable I l g μ.toBoxAdditive.toSMul
  · refine ge_of_tendsto' hgi.hasIntegral fun π => sum_nonneg fun J _ => ?_
    exact mul_nonneg ENNReal.toReal_nonneg (hg _ <| π.tag_mem_Icc _)
  · rw [integral, dif_neg hgi]

/-- If `‖f x‖ ≤ g x` on `[l, u]` and `g` is integrable, then the norm of the integral of `f` is less
than or equal to the integral of `g`. -/
/-
**BoxIntegral.norm_integral_le_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
`。
形式化陈述：norm_integral_le_of_norm_le {g : Realⁿ -> Real} (hle : forall x in Box.Icc
 I, ‖f x‖ <= g x) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] (hg : Integrabl
e I l g μ.toBoxAdditive.toSMul) : ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ 
<= integral I l g μ.toBoxAdditive.toSMul
参数：hle : forall x in Box.Icc I, ‖f x‖ <= g x；μ : Measure Realⁿ；hg : Integrable I
 l g μ.toBoxAdditive.toSMul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `norm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] (s : Finset ι) {f : ι → E} {n : ι → ℝ},   (∀ b ∈ s, ‖f b‖ ≤ n b) → 
‖∑ b ∈ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.toBoxAdditive_apply`：∀ {ι : Type u_1} [inst : Fini
te ι] (μ : MeasureTheory.Measure (ι → ℝ)) [inst_1 : MeasureTheory.IsLocallyFinit
eMeasure μ]   (J : BoxIntegral.…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `BoxIntegral.TaggedPrepartition.tag_mem_Icc`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (self : BoxIntegral.TaggedPrepartition I) (J : BoxIntegral.Box ι), 
  self.tag J ∈ BoxIntegral.Box.I…
· 使用定理 `BoxIntegral.integral.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGr
oup F] [inst_3 …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `BoxIntegral.integral_nonneg`：integral_nonneg {g : Realⁿ -> Real} (hg : f
orall x in Box.Icc I, 0 <= g x) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] :
 0 <= integral I …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If `‖f x‖ ≤ g x` on `[l, u]` and `g` is integrable, then the norm of the integra
l of `f` is less
than or equal to the integral of `g`.
-/
theorem norm_integral_le_of_norm_le {g : ℝⁿ → ℝ} (hle : ∀ x ∈ Box.Icc I, ‖f x‖ ≤ g x)
    (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ] (hg : Integrable I l g μ.toBoxAdditive.toSMul) :
    ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ ≤ integral I l g μ.toBoxAdditive.toSMul := by
  by_cases hfi : Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul
  · refine le_of_tendsto_of_tendsto' hfi.hasIntegral.norm hg.hasIntegral fun π => ?_
    refine norm_sum_le_of_le _ fun J _ => ?_
    simp only [BoxAdditiveMap.toSMul_apply, norm_smul, smul_eq_mul, Real.norm_eq_abs,
      μ.toBoxAdditive_apply, abs_of_nonneg measureReal_nonneg]
    gcongr
    exact hle _ <| π.tag_mem_Icc _
  · rw [integral, dif_neg hfi, norm_zero]
    exact integral_nonneg (fun x hx => (norm_nonneg _).trans (hle x hx)) μ
/-
**BoxIntegral.norm_integral_le_of_le_const** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l`。
形式化陈述：norm_integral_le_of_le_const {c : Real} (hc : forall x in Box.Icc I, ‖f x‖
 <= c) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] : ‖(integral I l f μ.toBox
Additive.toSMul : E)‖ <= μ.real I * c
参数：hc : forall x in Box.Icc I, ‖f x‖ <= c；μ : Measure Realⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.integral_const`：integral_const (c : E) : integral I l (fun _
 => c) vol = vol I c
· 使用定理 `BoxIntegral.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {g 
: Realⁿ -> Real} (hle : forall x in Box.Icc I, ‖f x‖ <= g x) (μ : Measure Realⁿ)
 [IsLocallyFiniteMeasure μ] (…
· 使用定理 `BoxIntegral.integrable_const`：integrable_const (c : E) : Integrable I l 
(fun _ => c) vol
-/
theorem norm_integral_le_of_le_const {c : ℝ}
    (hc : ∀ x ∈ Box.Icc I, ‖f x‖ ≤ c) (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ] :
    ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ ≤ μ.real I * c := by
  simpa only [integral_const] using! norm_integral_le_of_norm_le hc μ (integrable_const c)

/-!
### Henstock-Sacks inequality and integrability on subboxes

Henstock-Sacks inequality for Henstock-Kurzweil integral says the following. Let `f` be a function
integrable on a box `I`; let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged partition of
`I` subordinate to `r`, the integral sum over this partition is `ε`-close to the integral. Then for
any tagged prepartition (i.e. a finite collections of pairwise disjoint subboxes of `I` with tagged
points) `π`, the integral sum over `π` differs from the integral of `f` over the part of `I` covered
by `π` by at most `ε`. The actual statement in the library is a bit more complicated to make it work
for any `BoxIntegral.IntegrationParams`. We formalize several versions of this inequality in
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet`,
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`, and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet`.

Instead of using predicate assumptions on `r`, we define
`BoxIntegral.Integrable.convergenceR (h : integrable I l f vol) (ε : ℝ) (c : ℝ≥0) : ℝⁿ → (0, ∞)`
to be a function `r` such that

- if `l.bRiemann`, then `r` is a constant;
- if `ε > 0`, then for any tagged partition `π` of `I` subordinate to `r` (more precisely,
  satisfying the predicate `l.mem_base_set I c r`), the integral sum of `f` over `π` differs from
  the integral of `f` over `I` by at most `ε`.

The proof is mostly based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

-/
namespace Integrable

/-- If `ε > 0`, then `BoxIntegral.Integrable.convergenceR` is a function `r : ℝ≥0 → ℝⁿ → (0, ∞)`
such that for every `c : ℝ≥0`, for every tagged partition `π` subordinate to `r` (and satisfying
additional distortion estimates if `BoxIntegral.IntegrationParams.bDistortion l = true`), the
corresponding integral sum is `ε`-close to the integral.

If `BoxIntegral.IntegrationParams.bRiemann = true`, then `r c x` does not depend on `x`. If
`ε ≤ 0`, then we use `r c x = 1`. -/
/-
**BoxIntegral.Integrable.convergenceR** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Int
egrable`。
形式化陈述：convergenceR (h : Integrable I l f vol) (ε : Real) : Real>=0 -> Realⁿ -> I
oi (0 : Real)
参数：h : Integrable I l f vol；ε : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ε > 0`, then `BoxIntegral.Integrable.convergenceR` is a function `r : ℝ≥0 → 
ℝⁿ → (0, ∞)`
such that for every `c : ℝ≥0`, for every tagged partition `π` subordinate to `r`
 (and satisfying
additional distortion estimates if `BoxIntegral.IntegrationParams.bDistortion l 
= true`), the
corresponding integral sum is `ε`-close to the integral.

If `BoxIntegral.IntegrationParams.bRiemann = true`, then `r c x` does not depend
 on `x`. If
`ε ≤ 0`, then we use `r c x = 1`.
-/
def convergenceR (h : Integrable I l f vol) (ε : ℝ) : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ) :=
  if hε : 0 < ε then (hasIntegral_iff.1 h.hasIntegral ε hε).choose
  else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩

variable {c c₁ c₂ : ℝ≥0} {ε ε₁ ε₂ : ℝ} {π₁ π₂ : TaggedPrepartition I}
/-
**BoxIntegral.Integrable.convergenceR_cond** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Integrable`。
形式化陈述：convergenceR_cond (h : Integrable I l f vol) (ε : Real) (c : Real>=0) : l.
RCond (h.convergenceR ε c)
参数：h : Integrable I l f vol；ε : Real；c : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Integrable.convergenceR.eq_1`：∀ {ι : Type u} {E : Type v} {F
 : Type w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : 
NormedAddCommGroup F] [inst_3 …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.hasIntegral_iff`：hasIntegral_iff : HasIntegral I l f vol y ↔
 forall ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c
, l.RCond (r c)) …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem convergenceR_cond (h : Integrable I l f vol) (ε : ℝ) (c : ℝ≥0) :
    l.RCond (h.convergenceR ε c) := by
  rw [convergenceR]; split_ifs with h₀
  exacts [(hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.1 _, fun _ x => rfl]
/-
**BoxIntegral.Integrable.dist_integralSum_integral_le_of_memBaseSet** 是 Mathlib 
中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：dist_integralSum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h₀ 
: 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) (hπp : π.IsPartition) : 
dist (integralSum f vol π) (integral I l f vol) <= ε
参数：h : Integrable I l f vol；h₀ : 0 < ε；hπ : l.MemBaseSet I c (h.convergenceR ε c
) π；hπp : π.IsPartition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.hasIntegral_iff`：hasIntegral_iff : HasIntegral I l f vol y ↔
 forall ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c
, l.RCond (r c)) …
· 使用定理 `BoxIntegral.Integrable.hasIntegral`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `BoxIntegral.Integrable.convergenceR.eq_1`：∀ {ι : Type u} {E : Type v} {F
 : Type w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : 
NormedAddCommGroup F] [inst_3 …
-/
theorem dist_integralSum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h₀ : 0 < ε)
    (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) (hπp : π.IsPartition) :
    dist (integralSum f vol π) (integral I l f vol) ≤ ε := by
  rw [convergenceR, dif_pos h₀] at hπ
  exact (hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.2 c _ hπ hπp

/-- **Henstock-Sacks inequality**. Let `r₁ r₂ : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `rₖ`, `k=1,2`, the integral sum of `f` over this partition differs
from the integral of `f` by at most `εₖ`. Then for any two tagged *prepartition* `π₁ π₂` subordinate
to `r₁` and `r₂` respectively and covering the same part of `I`, the integral sums of `f` over these
prepartitions differ from each other by at most `ε₁ + ε₂`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption on `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion.

See also `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet`.
-/
/-
**BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.Integrable`。
形式化陈述：dist_integralSum_le_of_memBaseSet (h : Integrable I l f vol) (hpos₁ : 0 < 
ε₁) (hpos₂ : 0 < ε₂) (h₁ : l.MemBaseSet I c₁ (h.convergenceR ε₁ c₁) π₁) (h₂ : l.
MemBaseSet I c₂ (h.convergenceR ε₂ c₂) π₂) (HU : π₁.iUnion = π₂.iUnion) : dist (
integralSum f vol π₁) (integralSum f vol π₂) <= ε₁ + ε₂
参数：h : Integrable I l f vol；hpos₁ : 0 < ε₁；hpos₂ : 0 < ε₂；h₁ : l.MemBaseSet I c₁
 (h.convergenceR ε₁ c₁) π₁；h₂ : l.MemBaseSet I c₂ (h.convergenceR ε₂ c₂) π₂；HU :
 π₁.iUnion = π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.exists_common_compl`：∀ {ι : Typ
e u_1} [inst : Fintype ι] {I : BoxIntegral.Box ι} {c₁ c₂ : NNReal} {l : BoxInteg
ral.IntegrationParams}   {r₁ r₂ : (ι → ℝ) → ↑(Set.…
· 使用定理 `Std.instMinEqOrOfLawfulOrderLeftLeaningMin`：∀ {α : Type u} [inst : LE α]
 [inst_1 : Min α] [Std.LawfulOrderLeftLeaningMin α], Std.MinEqOr α
· 使用定理 `Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf`：∀ {α :
 Type u} [inst : LE α] [inst_1 : Min α] [Std.IsLinearOrder α] [Std.LawfulOrderIn
f α],   Std.LawfulOrderLeftLeaningMin α
· 使用定理 `instIsLinearOrder_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], Std.
IsLinearOrder α
· 使用定理 `instLawfulOrderInf_mathlib`：∀ {α : Type u} [inst : LinearOrder α], Std.L
awfulOrderInf α
· 使用定理 `BoxIntegral.Integrable.dist_integralSum_integral_le_of_memBaseSet`：dist_
integralSum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h₀ : 0 < ε) (h
π : l.MemBaseSet I c (h.convergenceR ε c) π) (hπp : π.I…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.unionComplToSubordinate`：∀ {ι :
 Type u_1} [inst : Fintype ι] {I : BoxIntegral.Box ι} {c : NNReal} {l : BoxInteg
ral.IntegrationParams}   {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi …
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinate`：isPa
rtition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I
) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.integralSum_disjUnion`：integralSum_disjUnion (f : Realⁿ -> E
) (vol : ι ->ᵇᵃ E ->L[Real] F) {π₁ π₂ : TaggedPrepartition I} (h : Disjoint π₁.i
Union π₂.iUnion) : inte…
· 使用定理 `dist_add_right`：∀ {M : Type u} [inst : Add M] [inst_1 : PseudoMetricSpac
e M] [IsIsometricVAdd Mᵃᵒᵖ M] (a b c : M),   dist (a + c) (b + c) = dist a b
· 使用定理 `NormedAddGroup.to_isIsometricVAdd_right`：∀ {E : Type u_2} [inst : Semino
rmedAddCommGroup E], IsIsometricVAdd Eᵃᵒᵖ E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
**Henstock-Sacks inequality**. Let `r₁ r₂ : ℝⁿ → (0, ∞)` be a function such that
 for any tagged
*partition* of `I` subordinate to `rₖ`, `k=1,2`, the integral sum of `f` over th
is partition differs
from the integral of `f` by at most `εₖ`. Then for any two tagged *prepartition*
 `π₁ π₂` subordinate
to `r₁` and `r₂` respectively and covering the same part of `I`, the integral su
ms of `f` over these
prepartitions differ from each other by at most `ε₁ + ε₂`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption o
n `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`
” to
  account for additional requirements like being a Henstock partition or having 
a bounded
  distortion.

See also `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_
of_iUnion_eq` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet`.
-/
theorem dist_integralSum_le_of_memBaseSet (h : Integrable I l f vol) (hpos₁ : 0 < ε₁)
    (hpos₂ : 0 < ε₂) (h₁ : l.MemBaseSet I c₁ (h.convergenceR ε₁ c₁) π₁)
    (h₂ : l.MemBaseSet I c₂ (h.convergenceR ε₂ c₂) π₂) (HU : π₁.iUnion = π₂.iUnion) :
    dist (integralSum f vol π₁) (integralSum f vol π₂) ≤ ε₁ + ε₂ := by
  rcases h₁.exists_common_compl h₂ HU with ⟨π, hπU, hπc₁, hπc₂⟩
  set r : ℝⁿ → Ioi (0 : ℝ) := fun x => min (h.convergenceR ε₁ c₁ x) (h.convergenceR ε₂ c₂ x)
  set πr := π.toSubordinate r
  have H₁ :
    dist (integralSum f vol (π₁.unionComplToSubordinate π hπU r)) (integral I l f vol) ≤ ε₁ :=
    h.dist_integralSum_integral_le_of_memBaseSet hpos₁
      (h₁.unionComplToSubordinate (fun _ _ => min_le_left _ _) hπU hπc₁)
      (isPartition_unionComplToSubordinate _ _ _ _)
  rw [HU] at hπU
  have H₂ :
    dist (integralSum f vol (π₂.unionComplToSubordinate π hπU r)) (integral I l f vol) ≤ ε₂ :=
    h.dist_integralSum_integral_le_of_memBaseSet hpos₂
      (h₂.unionComplToSubordinate (fun _ _ => min_le_right _ _) hπU hπc₂)
      (isPartition_unionComplToSubordinate _ _ _ _)
  simpa [unionComplToSubordinate] using (dist_triangle_right _ _ _).trans (add_le_add H₁ H₂)

/-- If `f` is integrable on `I` along `l`, then for two sufficiently fine tagged prepartitions
(in the sense of the filter `BoxIntegral.IntegrationParams.toFilter l I`) such that they cover
the same part of `I`, the integral sums of `f` over `π₁` and `π₂` are very close to each other. -/
/-
**BoxIntegral.Integrable.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_un
iformity** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity (h : Integ
rable I l f vol) : Tendsto (fun π : TaggedPrepartition I × TaggedPrepartition I 
=> (integralSum f vol π.1, integralSum f vol π.2)) ((l.toFilter I ×ˢ l.toFilter 
I) ⊓ 𝓟 {π | π.1.iUnion = π.2.iUnion}) (𝓤 F)
参数：h : Integrable I l f vol。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilter`：hasBasis_toFilter (l : 
IntegrationParams) (I : Box ι) : (l.toFilter I).HasBasis (fun r : Real>=0 -> (ι 
-> Real) -> Ioi (0 : Real) => forall …
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `BoxIntegral.Integrable.convergenceR_cond`：convergenceR_cond (h : Integra
ble I l f vol) (ε : Real) (c : Real>=0) : l.RCond (h.convergenceR ε c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet`：dist_integralS
um_le_of_memBaseSet (h : Integrable I l f vol) (hpos₁ : 0 < ε₁) (hpos₂ : 0 < ε₂)
 (h₁ : l.MemBaseSet I c₁ (h.convergenceR ε₁ c₁…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
If `f` is integrable on `I` along `l`, then for two sufficiently fine tagged pre
partitions
(in the sense of the filter `BoxIntegral.IntegrationParams.toFilter l I`) such t
hat they cover
the same part of `I`, the integral sums of `f` over `π₁` and `π₂` are very close
 to each other.
-/
theorem tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity (h : Integrable I l f vol) :
    Tendsto (fun π : TaggedPrepartition I × TaggedPrepartition I =>
      (integralSum f vol π.1, integralSum f vol π.2))
        ((l.toFilter I ×ˢ l.toFilter I) ⊓ 𝓟 {π | π.1.iUnion = π.2.iUnion}) (𝓤 F) := by
  refine (((l.hasBasis_toFilter I).prod_self.inf_principal _).tendsto_iff
    uniformity_basis_dist_le).2 fun ε ε0 => ?_
  replace ε0 := half_pos ε0
  use h.convergenceR (ε / 2), h.convergenceR_cond (ε / 2); rintro ⟨π₁, π₂⟩ ⟨⟨h₁, h₂⟩, hU⟩
  rw [← add_halves ε]
  exact h.dist_integralSum_le_of_memBaseSet ε0 ε0 h₁.choose_spec h₂.choose_spec hU

/-- If `f` is integrable on a box `I` along `l`, then for any fixed subset `s` of `I` that can be
represented as a finite union of boxes, the integral sums of `f` over tagged prepartitions that
cover exactly `s` form a Cauchy “sequence” along `l`. -/
/-
**BoxIntegral.Integrable.cauchy_map_integralSum_toFilteriUnion** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：cauchy_map_integralSum_toFilteriUnion (h : Integrable I l f vol) (π₀ : Pre
partition I) : Cauchy ((l.toFilteriUnion I π₀).map (integralSum f vol))
参数：h : Integrable I l f vol；π₀ : Prepartition I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.IntegrationParams.toFilter_inf_iUnion_eq`：toFilter_inf_iUnio
n_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) : l.toFilter I ⊓ 
𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilte…
· 使用定理 `Filter.prod_inf_prod`：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β
} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `BoxIntegral.Integrable.tendsto_integralSum_toFilter_prod_self_inf_iUnion
_eq_uniformity`：tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity 
(h : Integrable I l f vol) : Tendsto (fun π : TaggedPrepartition I × TaggedP…
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` is integrable on a box `I` along `l`, then for any fixed subset `s` of `I
` that can be
represented as a finite union of boxes, the integral sums of `f` over tagged pre
partitions that
cover exactly `s` form a Cauchy “sequence” along `l`.
-/
theorem cauchy_map_integralSum_toFilteriUnion (h : Integrable I l f vol) (π₀ : Prepartition I) :
    Cauchy ((l.toFilteriUnion I π₀).map (integralSum f vol)) := by
  refine ⟨inferInstance, ?_⟩
  rw [prod_map_map_eq, ← toFilter_inf_iUnion_eq, ← prod_inf_prod, prod_principal_principal]
  exact h.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity.mono_left
    (inf_le_inf_left _ <| principal_mono.2 fun π h => h.1.trans h.2.symm)

variable [CompleteSpace F]
/-
**BoxIntegral.Integrable.to_subbox_aux** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.In
tegrable`。
形式化陈述：to_subbox_aux (h : Integrable I l f vol) (hJ : J <= I) : exists y : F, Has
Integral J l f vol y ∧ Tendsto (integralSum f vol) (l.toFilteriUnion I (Preparti
tion.single I J hJ)) (𝓝 y)
参数：h : Integrable I l f vol；hJ : J <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `BoxIntegral.IntegrationParams.tendsto_embedBox_toFilteriUnion_top`：tends
to_embedBox_toFilteriUnion_top (l : IntegrationParams) (h : I <= J) : Tendsto (T
aggedPrepartition.embedBox I J h) (l.toFilteriUnion I ⊤…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchy_map_iff_exists_tendsto`：cauchy_map_iff_exists_tendsto [CompleteSp
ace α] {l : Filter β} {f : β -> α} [NeBot l] : Cauchy (l.map f) ↔ exists x, Tend
sto f l (𝓝 x)
· 使用定理 `BoxIntegral.Integrable.cauchy_map_integralSum_toFilteriUnion`：cauchy_map
_integralSum_toFilteriUnion (h : Integrable I l f vol) (π₀ : Prepartition I) : C
auchy ((l.toFilteriUnion I π₀).map (integralSum f …
-/
theorem to_subbox_aux (h : Integrable I l f vol) (hJ : J ≤ I) :
    ∃ y : F, HasIntegral J l f vol y ∧
      Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single I J hJ)) (𝓝 y) := by
  refine (cauchy_map_iff_exists_tendsto.1
    (h.cauchy_map_integralSum_toFilteriUnion (.single I J hJ))).imp fun y hy ↦ ⟨?_, hy⟩
  convert!
    hy.comp
      (l.tendsto_embedBox_toFilteriUnion_top hJ) -- faster than `exact` here
         -- faster than `exact` here

/-- If `f` is integrable on a box `I`, then it is integrable on any subbox of `I`. -/
/-
**BoxIntegral.Integrable.to_subbox** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integr
able`。
形式化陈述：to_subbox (h : Integrable I l f vol) (hJ : J <= I) : Integrable J l f vol
参数：h : Integrable I l f vol；hJ : J <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Integrable.to_subbox_aux`：to_subbox_aux (h : Integrable I l 
f vol) (hJ : J <= I) : exists y : F, HasIntegral J l f vol y ∧ Tendsto (integral
Sum f vol) (l.toFilteriUni…

--- 原说明 ---
If `f` is integrable on a box `I`, then it is integrable on any subbox of `I`.
-/
theorem to_subbox (h : Integrable I l f vol) (hJ : J ≤ I) : Integrable J l f vol :=
  (h.to_subbox_aux hJ).imp fun _ => And.left

/-- If `f` is integrable on a box `I`, then integral sums of `f` over tagged prepartitions
that cover exactly a subbox `J ≤ I` tend to the integral of `f` over `J` along `l`. -/
/-
**BoxIntegral.Integrable.tendsto_integralSum_toFilteriUnion_single** 是 Mathlib 中
的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：tendsto_integralSum_toFilteriUnion_single (h : Integrable I l f vol) (hJ :
 J <= I) : Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single 
I J hJ)) (𝓝 <| integral J l f vol)
参数：h : Integrable I l f vol；hJ : J <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.Integrable.to_subbox_aux`：to_subbox_aux (h : Integrable I l 
f vol) (hJ : J <= I) : exists y : F, HasIntegral J l f vol y ∧ Tendsto (integral
Sum f vol) (l.toFilteriUni…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …

--- 原说明 ---
If `f` is integrable on a box `I`, then integral sums of `f` over tagged prepart
itions
that cover exactly a subbox `J ≤ I` tend to the integral of `f` over `J` along `
l`.
-/
theorem tendsto_integralSum_toFilteriUnion_single (h : Integrable I l f vol) (hJ : J ≤ I) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single I J hJ))
      (𝓝 <| integral J l f vol) :=
  let ⟨_y, h₁, h₂⟩ := h.to_subbox_aux hJ
  h₁.integral_eq.symm ▸ h₂

/-- **Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partition differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordinate to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption on `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion;
- takes an extra argument `π₀ : prepartition I` and an assumption `π.Union = π₀.Union` instead of
  using `π.to_prepartition`.
-/
/-
**BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnio
n_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq (h : Integrabl
e I l f vol) (h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) {π₀ : P
repartition I} (hU : π.iUnion = π₀.iUnion) : dist (integralSum f vol π) (∑ J in 
π₀.boxes, integral J l f vol) <= ε
参数：h : Integrable I l f vol；h0 : 0 < ε；hπ : l.MemBaseSet I c (h.convergenceR ε c
) π；hU : π.iUnion = π₀.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `BoxIntegral.Integrable.to_subbox`：to_subbox (h : Integrable I l f vol) (
hJ : J <= I) : Integrable J l f vol
· 使用定理 `Std.instMinEqOrOfLawfulOrderLeftLeaningMin`：∀ {α : Type u} [inst : LE α]
 [inst_1 : Min α] [Std.LawfulOrderLeftLeaningMin α], Std.MinEqOr α
· 使用定理 `Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf`：∀ {α :
 Type u} [inst : LE α] [inst_1 : Min α] [Std.IsLinearOrder α] [Std.LawfulOrderIn
f α],   Std.LawfulOrderLeftLeaningMin α
· 使用定理 `instIsLinearOrder_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], Std.
IsLinearOrder α
· 使用定理 `instLawfulOrderInf_mathlib`：∀ {α : Type u} [inst : LinearOrder α], Std.L
awfulOrderInf α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `BoxIntegral.IntegrationParams.exists_memBaseSet_isPartition`：exists_memB
aseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.distortion <= c) 
(r : (ι -> Real) -> Ioi (0 : Real)) : exists π, l…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.mono`：∀ {ι : Type u_1} [inst : 
Fintype ι] (I : BoxIntegral.Box ι) {c₁ c₂ : NNReal} {l₁ l₂ : BoxIntegral.Integra
tionParams}   {r₁ r₂ : (ι → ℝ) → ↑(…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `BoxIntegral.Integrable.dist_integralSum_integral_le_of_memBaseSet`：dist_
integralSum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h₀ : 0 < ε) (h
π : l.MemBaseSet I c (h.convergenceR ε c) π) (hπp : π.I…
· 使用定理 `BoxIntegral.IntegrationParams.biUnionTagged_memBaseSet`：biUnionTagged_me
mBaseSet {π : Prepartition I} {πi : forall J, TaggedPrepartition J} (h : forall 
J in π, l.MemBaseSet J c r (πi J)) (hp : for…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 99 条，此处仅展示前 30 条）

--- 原说明 ---
**Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for
 any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partiti
on differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordina
te to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over
 the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption o
n `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`
” to
  account for additional requirements like being a Henstock partition or having 
a bounded
  distortion;
- takes an extra argument `π₀ : prepartition I` and an assumption `π.Union = π₀.
Union` instead of
  using `π.to_prepartition`.
-/
theorem dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq (h : Integrable I l f vol)
    (h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) {π₀ : Prepartition I}
    (hU : π.iUnion = π₀.iUnion) :
    dist (integralSum f vol π) (∑ J ∈ π₀.boxes, integral J l f vol) ≤ ε := by
  -- Let us prove that the distance is less than or equal to `ε + δ` for all positive `δ`.
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  -- First we choose some constants.
  set δ' : ℝ := δ / (#π₀.boxes + 1)
  have H0 : 0 < (#π₀.boxes + 1 : ℝ) := Nat.cast_add_one_pos _
  have δ'0 : 0 < δ' := div_pos δ0 H0
  set C := max π₀.distortion π₀.compl.distortion
  /- Next we choose a tagged partition of each `J ∈ π₀` such that the integral sum of `f` over this
    partition is `δ'`-close to the integral of `f` over `J`. -/
  have : ∀ J ∈ π₀, ∃ πi : TaggedPrepartition J,
      πi.IsPartition ∧ dist (integralSum f vol πi) (integral J l f vol) ≤ δ' ∧
        l.MemBaseSet J C (h.convergenceR δ' C) πi := by
    intro J hJ
    have Hle : J ≤ I := π₀.le_of_mem hJ
    have HJi : Integrable J l f vol := h.to_subbox Hle
    set r := fun x => min (h.convergenceR δ' C x) (HJi.convergenceR δ' C x)
    have hJd : J.distortion ≤ C := le_trans (Finset.le_sup hJ) (le_max_left _ _)
    rcases l.exists_memBaseSet_isPartition J hJd r with ⟨πJ, hC, hp⟩
    have hC₁ : l.MemBaseSet J C (HJi.convergenceR δ' C) πJ := by
      refine hC.mono J le_rfl le_rfl fun x _ => ?_; exact min_le_right _ _
    have hC₂ : l.MemBaseSet J C (h.convergenceR δ' C) πJ := by
      refine hC.mono J le_rfl le_rfl fun x _ => ?_; exact min_le_left _ _
    exact ⟨πJ, hp, HJi.dist_integralSum_integral_le_of_memBaseSet δ'0 hC₁ hp, hC₂⟩
  /- Now we combine these tagged partitions into a tagged prepartition of `I` that covers the
    same part of `I` as `π₀` and apply `BoxIntegral.dist_integralSum_le_of_memBaseSet` to
    `π` and this prepartition. -/
  choose! πi hπip hπiδ' hπiC using this
  have : l.MemBaseSet I C (h.convergenceR δ' C) (π₀.biUnionTagged πi) :=
    biUnionTagged_memBaseSet hπiC hπip fun _ => le_max_right _ _
  have hU' : π.iUnion = (π₀.biUnionTagged πi).iUnion :=
    hU.trans (Prepartition.iUnion_biUnion_partition _ hπip).symm
  have := h.dist_integralSum_le_of_memBaseSet h0 δ'0 hπ this hU'
  rw [integralSum_biUnionTagged] at this
  calc
    dist (integralSum f vol π) (∑ J ∈ π₀.boxes, integral J l f vol) ≤
        dist (integralSum f vol π) (∑ J ∈ π₀.boxes, integralSum f vol (πi J)) +
          dist (∑ J ∈ π₀.boxes, integralSum f vol (πi J)) (∑ J ∈ π₀.boxes, integral J l f vol) :=
      dist_triangle _ _ _
    _ ≤ ε + δ' + ∑ _J ∈ π₀.boxes, δ' := add_le_add this (dist_sum_sum_le_of_le _ hπiδ')
    _ = ε + δ := by simp [field, δ']; ring

/-- **Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partition differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordinate to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption on `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion;
-/
/-
**BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet** 是 Math
lib 中的一个定理，位于命名空间 `BoxIntegral.Integrable`。
形式化陈述：dist_integralSum_sum_integral_le_of_memBaseSet (h : Integrable I l f vol) 
(h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) : dist (integralSum 
f vol π) (∑ J in π.boxes, integral J l f vol) <= ε
参数：h : Integrable I l f vol；h0 : 0 < ε；hπ : l.MemBaseSet I c (h.convergenceR ε c
) π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of
_iUnion_eq`：dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq (h : Int
egrable I l f vol) (h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε…

--- 原说明 ---
**Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for
 any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partiti
on differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordina
te to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over
 the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption o
n `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`
” to
  account for additional requirements like being a Henstock partition or having 
a bounded
  distortion;
-/
theorem dist_integralSum_sum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h0 : 0 < ε)
    (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) :
    dist (integralSum f vol π) (∑ J ∈ π.boxes, integral J l f vol) ≤ ε :=
  h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq h0 hπ rfl

/-- Integral sum of `f` over a tagged prepartition `π` such that `π.Union = π₀.Union` tends to the
sum of integrals of `f` over the boxes of `π₀`. -/
/-
**BoxIntegral.Integrable.tendsto_integralSum_sum_integral** 是 Mathlib 中的一个定理，位于命
名空间 `BoxIntegral.Integrable`。
形式化陈述：tendsto_integralSum_sum_integral (h : Integrable I l f vol) (π₀ : Preparti
tion I) : Tendsto (integralSum f vol) (l.toFilteriUnion I π₀) (𝓝 <| ∑ J in π₀.bo
xes, integral J l f vol)
参数：h : Integrable I l f vol；π₀ : Prepartition I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion`：hasBasis_toFilter
iUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) : (l.toFilteriU
nion I π₀).HasBasis (fun r : Real>=0 -> (ι …
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `BoxIntegral.Integrable.convergenceR_cond`：convergenceR_cond (h : Integra
ble I l f vol) (ε : Real) (c : Real>=0) : l.RCond (h.convergenceR ε c)
· 使用定理 `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of
_iUnion_eq`：dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq (h : Int
egrable I l f vol) (h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε…

--- 原说明 ---
Integral sum of `f` over a tagged prepartition `π` such that `π.Union = π₀.Union
` tends to the
sum of integrals of `f` over the boxes of `π₀`.
-/
theorem tendsto_integralSum_sum_integral (h : Integrable I l f vol) (π₀ : Prepartition I) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I π₀)
      (𝓝 <| ∑ J ∈ π₀.boxes, integral J l f vol) := by
  refine ((l.hasBasis_toFilteriUnion I π₀).tendsto_iff nhds_basis_closedBall).2 fun ε ε0 => ?_
  refine ⟨h.convergenceR ε, h.convergenceR_cond ε, ?_⟩
  simp only [mem_ofPred_eq]
  rintro π ⟨c, hc, hU⟩
  exact h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq ε0 hc hU

/-- If `f` is integrable on `I`, then `fun J ↦ integral J l f vol` is box-additive on subboxes of
`I`: if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `BoxIntegral.Integrable.toBoxAdditive` for a bundled version. -/
/-
**BoxIntegral.Integrable.sum_integral_congr** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Integrable`。
形式化陈述：sum_integral_congr (h : Integrable I l f vol) {π₁ π₂ : Prepartition I} (hU
 : π₁.iUnion = π₂.iUnion) : ∑ J in π₁.boxes, integral J l f vol = ∑ J in π₂.boxe
s, integral J l f vol
参数：h : Integrable I l f vol；hU : π₁.iUnion = π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `BoxIntegral.Integrable.tendsto_integralSum_sum_integral`：tendsto_integra
lSum_sum_integral (h : Integrable I l f vol) (π₀ : Prepartition I) : Tendsto (in
tegralSum f vol) (l.toFilteriUnion I π₀) (𝓝 <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.IntegrationParams.toFilteriUnion_congr`：toFilteriUnion_congr
 (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π
₂.iUnion) : l.toFilteriUnion I π₁ = l.to…

--- 原说明 ---
If `f` is integrable on `I`, then `fun J ↦ integral J l f vol` is box-additive o
n subboxes of
`I`: if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, t
he sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the b
oxes of `π₂`.

See also `BoxIntegral.Integrable.toBoxAdditive` for a bundled version.
-/
theorem sum_integral_congr (h : Integrable I l f vol) {π₁ π₂ : Prepartition I}
    (hU : π₁.iUnion = π₂.iUnion) :
    ∑ J ∈ π₁.boxes, integral J l f vol = ∑ J ∈ π₂.boxes, integral J l f vol := by
  refine tendsto_nhds_unique (h.tendsto_integralSum_sum_integral π₁) ?_
  rw [l.toFilteriUnion_congr _ hU]
  exact h.tendsto_integralSum_sum_integral π₂

/-- If `f` is integrable on `I`, then `fun J ↦ integral J l f vol` is box-additive on subboxes of
`I`: if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `BoxIntegral.Integrable.sum_integral_congr` for an unbundled version. -/
@[simps]
/-
**BoxIntegral.Integrable.toBoxAdditive** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.In
tegrable`。
形式化陈述：toBoxAdditive (h : Integrable I l f vol) : ι ->ᵇᵃ[I] F where toFun J
参数：h : Integrable I l f vol。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is integrable on `I`, then `fun J ↦ integral J l f vol` is box-additive o
n subboxes of
`I`: if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, t
he sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the b
oxes of `π₂`.

See also `BoxIntegral.Integrable.sum_integral_congr` for an unbundled version.
-/
def toBoxAdditive (h : Integrable I l f vol) : ι →ᵇᵃ[I] F where
  toFun J := integral J l f vol
  sum_partition_boxes' J hJ π hπ := by
    replace hπ := hπ.iUnion_eq; rw [← Prepartition.iUnion_top] at hπ
    rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ, Prepartition.top_boxes,
      sum_singleton]

end Integrable

open MeasureTheory

/-!
### Integrability conditions
-/

open Prepartition EMetric ENNReal BoxAdditiveMap Finset Metric TaggedPrepartition

variable (l)

/-- A function that is bounded and a.e. continuous on a box `I` is integrable on `I`. -/
/-
**BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt** 是 Mathlib 中的一个定理
，位于命名空间 `BoxIntegral`。
形式化陈述：integrable_of_bounded_and_ae_continuousWithinAt [CompleteSpace E] {I : Box
 ι} {f : Realⁿ -> E} (hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C) (
μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] (hc : forallᵐ x ∂(μ.restrict (Box.
Icc I)), ContinuousWithinAt f (Box.Icc I) x) : Integrable I l f μ.toBoxAdditive.
toSMul
参数：hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C；μ : Measure Realⁿ；hc 
: forallᵐ x ∂(μ.restrict (Box.Icc I)), ContinuousWithinAt f (Box.Icc I) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.integrable_iff_cauchy_basis`：integrable_iff_cauchy_basis [Co
mpleteSpace F] : Integrable I l f vol ↔ forall ε > (0 : Real), exists r : Real>=
0 -> Realⁿ -> Ioi (0 : Real),…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `BoxIntegral.Box.nonempty_coe`：nonempty_coe : Set.Nonempty (I : Set (ι ->
 Real))
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Set.exists_isOpen_lt_add`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ
 : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRegular]   (A 
: Set α), μ A …
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.instIsLocallyFiniteMeasureRestrict`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {s : Set α} [inst : TopologicalSpace α] (μ : MeasureTheory.M
easure α)   [hμ : MeasureTheory.IsLoca…
（共 190 条，此处仅展示前 30 条）

--- 原说明 ---
A function that is bounded and a.e. continuous on a box `I` is integrable on `I`
.
-/
theorem integrable_of_bounded_and_ae_continuousWithinAt [CompleteSpace E] {I : Box ι} {f : ℝⁿ → E}
    (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖f x‖ ≤ C) (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ]
    (hc : ∀ᵐ x ∂(μ.restrict (Box.Icc I)), ContinuousWithinAt f (Box.Icc I) x) :
    Integrable I l f μ.toBoxAdditive.toSMul := by
  /- We prove that f is integrable by proving that we can ensure that the integrals over any
     two tagged prepartitions π₁ and π₂ can be made ε-close by making the partitions
     sufficiently fine.

     Start by defining some constants C, ε₁, ε₂ that will be useful later. -/
  refine integrable_iff_cauchy_basis.2 fun ε ε0 ↦ ?_
  rcases exists_pos_mul_lt ε0 (2 * μ.toBoxAdditive I) with ⟨ε₁, ε₁0, hε₁⟩
  rcases hb with ⟨C, hC⟩
  have C0 : 0 ≤ C := by
    obtain ⟨x, hx⟩ := BoxIntegral.Box.nonempty_coe I
    exact le_trans (norm_nonneg (f x)) <| hC x (I.coe_subset_Icc hx)
  rcases exists_pos_mul_lt ε0 (4 * C) with ⟨ε₂, ε₂0, hε₂⟩
  have ε₂0' : ENNReal.ofReal ε₂ ≠ 0 := ne_of_gt <| ofReal_pos.2 ε₂0
  -- The set of discontinuities of f is contained in an open set U with μ U < ε₂.
  let D := { x ∈ Box.Icc I | ¬ ContinuousWithinAt f (Box.Icc I) x }
  let μ' := μ.restrict (Box.Icc I)
  have μ'D : μ' D = 0 := by
    rcases eventually_iff_exists_mem.1 hc with ⟨V, ae, hV⟩
    exact eq_of_le_of_not_lt (mem_ae_iff.1 ae ▸ (μ'.mono <| fun x h xV ↦ h.2 (hV x xV)))
      _root_.not_lt_zero
  obtain ⟨U, UD, Uopen, hU⟩ := Set.exists_isOpen_lt_add D (show μ' D ≠ ⊤ by simp [μ'D]) ε₂0'
  rw [μ'D, zero_add] at hU
  /- Box.Icc I \ U is compact and avoids discontinuities of f, so there exists r > 0 such that for
     every x ∈ Box.Icc I \ U, the oscillation (within Box.Icc I) of f on the ball of radius r
     centered at x is ≤ ε₁ -/
  have comp : IsCompact (Box.Icc I \ U) :=
    I.isCompact_Icc.of_isClosed_subset (I.isCompact_Icc.isClosed.sdiff Uopen) Set.sdiff_subset
  have : ∀ x ∈ (Box.Icc I \ U), oscillationWithin f (Box.Icc I) x < (ENNReal.ofReal ε₁) := by
    intro x hx
    suffices oscillationWithin f (Box.Icc I) x = 0 by rw [this]; exact ofReal_pos.2 ε₁0
    simpa [OscillationWithin.eq_zero_iff_continuousWithinAt, D, hx.1] using hx.2 ∘ (fun a ↦ UD a)
  rcases comp.uniform_oscillationWithin this with ⟨r, r0, hr⟩
  /- We prove the claim for partitions π₁ and π₂ subordinate to r/2, by writing the difference as
     an integralSum over π₁ ⊓ π₂ and considering separately the boxes of π₁ ⊓ π₂ which are/aren't
     fully contained within U. -/
  refine ⟨fun _ _ ↦ ⟨r / 2, half_pos r0⟩, fun _ _ _ ↦ rfl, fun c₁ c₂ π₁ π₂ h₁ h₁p h₂ h₂p ↦ ?_⟩
  simp only [dist_eq_norm, integralSum_sub_partitions _ _ h₁p h₂p, toSMul_apply, ← smul_sub]
  have μI : μ I < ⊤ := lt_of_le_of_lt (μ.mono I.coe_subset_Icc) I.isCompact_Icc.measure_lt_top
  let t₁ (J : Box ι) : ℝⁿ := (π₁.infPrepartition π₂.toPrepartition).tag J
  let t₂ (J : Box ι) : ℝⁿ := (π₂.infPrepartition π₁.toPrepartition).tag J
  let B := (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes
  classical
  let B' := {J ∈ B | J.toSet ⊆ U}
  have hB' : B' ⊆ B := B.filter_subset (fun J ↦ J.toSet ⊆ U)
  have μJ_ne_top : ∀ J ∈ B, μ J ≠ ⊤ :=
    fun J hJ ↦ lt_top_iff_ne_top.1 <| lt_of_le_of_lt (μ.mono (Prepartition.le_of_mem' _ J hJ)) μI
  have un : ∀ S ⊆ B, ⋃ J ∈ S, J.toSet ⊆ I.toSet :=
    fun S hS ↦ iUnion_subset_iff.2 (fun J ↦ iUnion_subset_iff.2 fun hJ ↦ le_of_mem' _ J (hS hJ))
  rw [← sum_sdiff hB', ← add_halves ε]
  apply le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  /- If a box J is not contained within U, then the oscillation of f on J is small, which bounds
     the contribution of J to the overall sum. -/
  · have : ∀ J ∈ B \ B', ‖μ.toBoxAdditive J • (f (t₁ J) - f (t₂ J))‖ ≤ μ.toBoxAdditive J * ε₁ := by
      intro J hJ
      rw [Finset.mem_sdiff, B.mem_filter, not_and] at hJ
      rw [norm_smul, μ.toBoxAdditive_apply, Real.norm_of_nonneg measureReal_nonneg]
      gcongr _ * ?_
      obtain ⟨x, xJ, xnU⟩ : ∃ x ∈ J, x ∉ U := Set.not_subset.1 (hJ.2 hJ.1)
      have hx : x ∈ Box.Icc I \ U := ⟨Box.coe_subset_Icc ((le_of_mem' _ J hJ.1) xJ), xnU⟩
      have ineq : edist (f (t₁ J)) (f (t₂ J)) ≤ ediam (f '' (ball x r ∩ (Box.Icc I))) := by
        apply edist_le_ediam_of_mem <;>
          refine Set.mem_image_of_mem f ⟨?_, tag_mem_Icc _ J⟩ <;>
          refine closedBall_subset_ball (div_two_lt_of_pos r0) <| mem_closedBall_comm.1 ?_
        · exact h₁.isSubordinate.infPrepartition π₂.toPrepartition J hJ.1 (Box.coe_subset_Icc xJ)
        · exact h₂.isSubordinate.infPrepartition π₁.toPrepartition J
            ((π₁.mem_infPrepartition_comm).1 hJ.1) (Box.coe_subset_Icc xJ)
      rw [← Metric.eball_ofReal] at ineq
      simpa only [edist_le_ofReal (le_of_lt ε₁0), dist_eq_norm, hJ.1] using ineq.trans (hr x hx)
    refine (norm_sum_le _ _).trans <| (sum_le_sum this).trans ?_
    rw [← sum_mul]
    trans μ.toBoxAdditive I * ε₁; swap
    · linarith
    simp_rw [mul_le_mul_iff_left₀ ε₁0, μ.toBoxAdditive_apply]
    refine le_trans ?_ <| toReal_mono (lt_top_iff_ne_top.1 μI) <| μ.mono <| un (B \ B') sdiff_subset
    simp_rw [measureReal_def]
    rw [← toReal_sum (fun J hJ ↦ μJ_ne_top J (mem_sdiff.1 hJ).1), ← Finset.tsum_subtype]
    refine (toReal_mono <| ne_of_lt <| lt_of_le_of_lt (μ.mono <| un (B \ B') sdiff_subset) μI) ?_
    refine le_of_eq (measure_biUnion (countable_toSet _) ?_ (fun J _ ↦ J.measurableSet_coe)).symm
    exact fun J hJ J' hJ' hJJ' ↦ pairwiseDisjoint _ (mem_sdiff.1 hJ).1 (mem_sdiff.1 hJ').1 hJJ'
  -- The contribution of the boxes contained within U is bounded because f is bounded and μ U < ε₂.
  · have : ∀ J ∈ B', ‖μ.toBoxAdditive J • (f (t₁ J) - f (t₂ J))‖ ≤ μ.toBoxAdditive J * (2 * C) := by
      intro J _
      rw [norm_smul, μ.toBoxAdditive_apply, Real.norm_of_nonneg measureReal_nonneg, two_mul]
      gcongr
      apply norm_sub_le_of_le <;> exact hC _ (TaggedPrepartition.tag_mem_Icc _ J)
    apply (norm_sum_le_of_le B' this).trans
    simp_rw [← sum_mul, μ.toBoxAdditive_apply, measureReal_def,
      ← toReal_sum (fun J hJ ↦ μJ_ne_top J (hB' hJ))]
    suffices (∑ J ∈ B', μ J).toReal ≤ ε₂ by
      linarith [mul_le_mul_of_nonneg_right this <| (mul_nonneg_iff_of_pos_left two_pos).2 C0]
    rw [← toReal_ofReal (le_of_lt ε₂0)]
    refine toReal_mono ofReal_ne_top (le_trans ?_ (le_of_lt hU))
    trans μ' (⋃ J ∈ B', J)
    · simp only [μ', μ.restrict_eq_self <| (un _ hB').trans I.coe_subset_Icc]
      exact le_of_eq <| Eq.symm <| measure_biUnion_finset
        (fun J hJ K hK hJK ↦ pairwiseDisjoint _ (hB' hJ) (hB' hK) hJK) fun J _ ↦ J.measurableSet_coe
    · apply μ'.mono
      simp_rw [iUnion_subset_iff]
      exact fun J hJ ↦ (mem_filter.1 hJ).2

/-- A function that is bounded on a box `I` and a.e. continuous is integrable on `I`.

This is a version of `integrable_of_bounded_and_ae_continuousWithinAt` with a stronger continuity
assumption so that the user does not need to specialize the continuity assumption to each box on
which the theorem is to be applied. -/
/-
**BoxIntegral.integrable_of_bounded_and_ae_continuous** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral`。
形式化陈述：integrable_of_bounded_and_ae_continuous [CompleteSpace E] {I : Box ι} {f :
 Realⁿ -> E} (hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C) (μ : Meas
ure Realⁿ) [IsLocallyFiniteMeasure μ] (hc : forallᵐ x ∂μ, ContinuousAt f x) : In
tegrable I l f μ.toBoxAdditive.toSMul
参数：hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C；μ : Measure Realⁿ；hc 
: forallᵐ x ∂μ, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt`：integrable_
of_bounded_and_ae_continuousWithinAt [CompleteSpace E] {I : Box ι} {f : Realⁿ ->
 E} (hb : exists C : Real, forall x in Box.Icc I,…
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x

--- 原说明 ---
A function that is bounded on a box `I` and a.e. continuous is integrable on `I`
.

This is a version of `integrable_of_bounded_and_ae_continuousWithinAt` with a st
ronger continuity
assumption so that the user does not need to specialize the continuity assumptio
n to each box on
which the theorem is to be applied.
-/
theorem integrable_of_bounded_and_ae_continuous [CompleteSpace E] {I : Box ι} {f : ℝⁿ → E}
    (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖f x‖ ≤ C) (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ]
    (hc : ∀ᵐ x ∂μ, ContinuousAt f x) : Integrable I l f μ.toBoxAdditive.toSMul :=
  integrable_of_bounded_and_ae_continuousWithinAt l hb μ <|
    Eventually.filter_mono (ae_mono μ.restrict_le_self) (hc.mono fun _ h ↦ h.continuousWithinAt)


/-- A continuous function is box-integrable with respect to any locally finite measure.

This is true for any volume with bounded variation. -/
/-
**BoxIntegral.integrable_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`
。
形式化陈述：integrable_of_continuousOn [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E} 
(hc : ContinuousOn f (Box.Icc I)) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ]
 : Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul
参数：hc : ContinuousOn f (Box.Icc I)；μ : Measure Realⁿ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt`：integrable_
of_bounded_and_ae_continuousWithinAt [CompleteSpace E] {I : Box ι} {f : Realⁿ ->
 E} (hb : exists C : Real, forall x in Box.Icc I,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedSpace.isBounded_iff_subset_smul_closedBall`：isBounded_iff_subset_s
mul_closedBall {s : Set E} : Bornology.IsBounded s ↔ exists a : 𝕜, s subseteq a 
• Metric.closedBall (0 : E) 1
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `BoxIntegral.Box.isCompact_Icc`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι),
 IsCompact (BoxIntegral.Box.Icc I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitClosedBall`：smul_unitClosedBall (c : 𝕜) : c • closedBall (0 : E
) (1 : Real) = closedBall (0 : E) ‖c‖
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSet.compl_iff`：MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ Me
asurableSet s
· 使用定理 `BoxIntegral.Box.measurableSet_Icc`：measurableSet_Icc : MeasurableSet (Bo
x.Icc I)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x

--- 原说明 ---
A continuous function is box-integrable with respect to any locally finite measu
re.

This is true for any volume with bounded variation.
-/
theorem integrable_of_continuousOn [CompleteSpace E] {I : Box ι} {f : ℝⁿ → E}
    (hc : ContinuousOn f (Box.Icc I)) (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ] :
    Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul := by
  apply integrable_of_bounded_and_ae_continuousWithinAt
  · obtain ⟨C, hC⟩ := (NormedSpace.isBounded_iff_subset_smul_closedBall ℝ).1
                        (I.isCompact_Icc.image_of_continuousOn hc).isBounded
    use ‖C‖, fun x hx ↦ by
      simpa only [smul_unitClosedBall, mem_closedBall_zero_iff] using hC (Set.mem_image_of_mem f hx)
  · refine eventually_of_mem ?_ (fun x hx ↦ hc.continuousWithinAt hx)
    rw [mem_ae_iff, μ.restrict_apply] <;> simp [MeasurableSet.compl_iff.2 I.measurableSet_Icc]

variable {l}

/-- This is an auxiliary lemma used to prove two statements at once. Use one of the next two
lemmas instead. -/
/-
**BoxIntegral.HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO** 是 Mathlib 中
的一个定理，位于命名空间 `BoxIntegral.HasIntegral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤},   
l.bRiemann = false →     ∀ (B : BoxIntegral.BoxAdditiveMap ι ℝ ↑I),       (∀ (J 
: BoxIntegral.Box ι), 0 ≤ B J) →         ∀ (g : BoxIntegral.BoxAdditiveMap ι F ↑
I) (s : Set (ι → ℝ)),           s.Countable →             (s.Nonempty → l.bHenst
ock = true) →               (∀ (c : NNReal),                   ∀ x ∈ BoxIntegral
.Box.Icc I ∩ s,                     ∀ ε > 0,                       ∃ δ > 0,     
                    ∀ J ≤ I,                           BoxIntegral.Box.Icc J ⊆ M
etric.closedBall x δ →                             x ∈ BoxIntegral.Box.Icc J →  
                             (l.bDistortion = true → J.distortion ≤ c) → dist ((
vol J) (f x)) (g J) ≤ ε) →                 (∀ (c : NNReal),                     
∀ x ∈ BoxIntegral.Box.Icc I \ s,                       ∀ ε > 0,                 
        ∃ δ > 0,                           ∀ J ≤ I,                             
BoxIntegral.Box.Icc J ⊆ Metric.closedBall x δ →                               (l
.bHenstock = true → x ∈ BoxIntegral.Box.Icc J) →                                
 (l.bDistortion = true → J.distortion ≤ c) → dist ((vol J) (f x)) (g J) ≤ ε * B 
J) →                   BoxIntegral.HasIntegral I l f vol (g I)
参数：ι → ℝ；E →L[ℝ] F；B : BoxIntegral.BoxAdditiveMap ι ℝ ↑I；∀ (J : BoxIntegral.Box 
ι), 0 ≤ B J；g : BoxIntegral.BoxAdditiveMap ι F ↑I；s : Set (ι → ℝ)；s.Nonempty → l
.bHenstock = true；∀ (c : NNReal),                   ∀ x ∈ BoxIntegral.Box.Icc I 
∩ s,                     ∀ ε > 0,                       ∃ δ > 0,                
         ∀ J ≤ I,                           BoxIntegral.Box.Icc J ⊆ Metric.close
dBall x δ →                             x ∈ BoxIntegral.Box.Icc J →             
                  (l.bDistortion = true → J.distortion ≤ c) → dist ((vol J) (f x
)) (g J) ≤ ε；∀ (c : NNReal),                     ∀ x ∈ BoxIntegral.Box.Icc I \ s
,                       ∀ ε > 0,                         ∃ δ > 0,               
            ∀ J ≤ I,                             BoxIntegral.Box.Icc J ⊆ Metric.
closedBall x δ →                               (l.bHenstock = true → x ∈ BoxInte
gral.Box.Icc J) →                                 (l.bDistortion = true → J.dist
ortion ≤ c) → dist ((vol J) (f x)) (g J) ≤ ε * B J；g I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion_top`：hasBasis_toFi
lteriUnion_top (l : IntegrationParams) (I : Box ι) : (l.toFilteriUnion I ⊤).HasB
asis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 …
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.Countable.exists_pos_forall_sum_le`：Set.Countable.exists_pos_forall_
sum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : Real} (hε : 0 < ε) : exis
ts ε' : ι -> Real, (forall i…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `BoxIntegral.IntegrationParams.rCond_of_bRiemann_eq_false`：rCond_of_bRiem
ann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = false) {r : (ι -> Re
al) -> Ioi (0 : Real)} : l.RCond r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.BoxAdditiveMap.sum_partition_boxes`：sum_partition_boxes (f :
 ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I} (h : π.IsPartition) : ∑ J in
 π.boxes, f J = f I
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `BoxIntegral.integralSum.eq_1`：∀ {ι : Type u} {E : Type v} {F : Type w} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [inst_3 …
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `dist_add_add_le_of_le`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E
] {a₁ a₂ b₁ b₂ : E} {r₁ r₂ : ℝ},   dist a₁ b₁ ≤ r₁ → dist a₂ b₂ ≤ r₂ → dist (a₁ 
+ a₂) (b₁ +…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
This is an auxiliary lemma used to prove two statements at once. Use one of the 
next two
lemmas instead.
-/
theorem HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (hl : l.bRiemann = false)
    (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J) (g : ι →ᵇᵃ[I] F) (s : Set ℝⁿ) (hs : s.Countable)
    (hlH : s.Nonempty → l.bHenstock = true)
    (H₁ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I ∩ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → x ∈ Box.Icc J →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε)
    (H₂ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I \ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → (l.bHenstock → x ∈ Box.Icc J) →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε * B J) :
    HasIntegral I l f vol (g I) := by
  /- We choose `r x` differently for `x ∈ s` and `x ∉ s`.

    For `x ∈ s`, we choose `εs` such that `∑' x : s, εs x < ε / 2 / 2 ^ #ι`, then choose `r x` so
    that `dist (vol J (f x)) (g J) ≤ εs x` for `J` in the `r x`-neighborhood of `x`. This guarantees
    that the sum of these distances over boxes `J` such that `π.tag J ∈ s` is less than `ε / 2`. We
    need an additional multiplier `2 ^ #ι` because different boxes can have the same tag.

    For `x ∉ s`, we choose `r x` so that `dist (vol (J (f x))) (g J) ≤ (ε / 2 / B I) * B J` for a
    box `J` in the `δ`-neighborhood of `x`. -/
  refine ((l.hasBasis_toFilteriUnion_top _).tendsto_iff Metric.nhds_basis_closedBall).2 ?_
  intro ε ε0
  simp only [← exists_prop, gt_iff_lt, Subtype.exists'] at H₁ H₂
  choose! δ₁ Hδ₁ using H₁
  choose! δ₂ Hδ₂ using H₂
  have ε0' := half_pos ε0; have H0 : 0 < (2 : ℝ) ^ Fintype.card ι := pow_pos zero_lt_two _
  rcases hs.exists_pos_forall_sum_le (div_pos ε0' H0) with ⟨εs, hεs0, hεs⟩
  simp only [le_div_iff₀' H0, mul_sum] at hεs
  rcases exists_pos_mul_lt ε0' (B I) with ⟨ε', ε'0, hεI⟩
  classical
  set δ : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ) := fun c x => if x ∈ s then δ₁ c x (εs x) else (δ₂ c) x ε'
  refine ⟨δ, fun c => l.rCond_of_bRiemann_eq_false hl, ?_⟩
  simp only [mem_ofPred_eq]
  rintro π ⟨c, hπδ, hπp⟩
  -- Now we split the sum into two parts based on whether `π.tag J` belongs to `s` or not.
  rw [← g.sum_partition_boxes le_rfl hπp, Metric.mem_closedBall, integralSum,
    ← sum_filter_add_sum_filter_not π.boxes fun J => π.tag J ∈ s,
    ← sum_filter_add_sum_filter_not π.boxes fun J => π.tag J ∈ s, ← add_halves ε]
  refine dist_add_add_le_of_le ?_ ?_
  · rcases s.eq_empty_or_nonempty with (rfl | hsne); · simp [ε0'.le]
    /- For the boxes such that `π.tag J ∈ s`, we use the fact that at most `2 ^ #ι` boxes have the
        same tag. -/
    specialize hlH hsne
    have : ∀ J ∈ {J ∈ π.boxes | π.tag J ∈ s},
        dist (vol J (f <| π.tag J)) (g J) ≤ εs (π.tag J) := fun J hJ ↦ by
      rw [Finset.mem_filter] at hJ; obtain ⟨hJ, hJs⟩ := hJ
      refine Hδ₁ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ (hεs0 _) _ (π.le_of_mem' _ hJ) ?_
        (hπδ.2 hlH J hJ) fun hD => (Finset.le_sup hJ).trans (hπδ.3 hD)
      convert! hπδ.1 J hJ using 3; exact (if_pos hJs).symm
    refine (dist_sum_sum_le_of_le _ this).trans ?_
    rw [sum_comp]
    refine (sum_le_sum ?_).trans (hεs _ ?_)
    · rintro b -
      rw [← Nat.cast_two, ← Nat.cast_pow, ← nsmul_eq_mul]
      refine nsmul_le_nsmul_left (hεs0 _).le ?_
      refine (Finset.card_le_card ?_).trans ((hπδ.isHenstock hlH).card_filter_tag_eq_le b)
      exact filter_subset_filter _ (filter_subset _ _)
    · rw [Finset.coe_image, Set.image_subset_iff]
      exact fun J hJ => (Finset.mem_filter.1 hJ).2
  /- Now we deal with boxes such that `π.tag J ∉ s`.
    In this case the estimate is straightforward. -/
  calc
    dist (∑ J ∈ π.boxes with tag π J ∉ s, vol J (f (tag π J)))
      (∑ J ∈ π.boxes with tag π J ∉ s, g J)
      ≤ ∑ J ∈ π.boxes with tag π J ∉ s, ε' * B J := dist_sum_sum_le_of_le _ fun J hJ ↦ by
      rw [Finset.mem_filter] at hJ; obtain ⟨hJ, hJs⟩ := hJ
      refine Hδ₂ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ ε'0 _ (π.le_of_mem' _ hJ) ?_ (fun hH => hπδ.2 hH J hJ)
        fun hD => (Finset.le_sup hJ).trans (hπδ.3 hD)
      convert! hπδ.1 J hJ using 3; exact (if_neg hJs).symm
    _ ≤ ∑ J ∈ π.boxes, ε' * B J := by
      gcongr
      · exact fun _ _ _ ↦ mul_nonneg ε'0.le (hB0 _)
      · apply filter_subset
    _ = B I * ε' := by rw [← mul_sum, B.sum_partition_boxes le_rfl hπp, mul_comm]
    _ ≤ ε / 2 := hεI.le

/-- A function `f` has Henstock (or `⊥`) integral over `I` is equal to the value of a box-additive
function `g` on `I` provided that `vol J (f x)` is sufficiently close to `g J` for sufficiently
small boxes `J ∋ x`. This lemma is useful to prove, e.g., to prove the Divergence theorem for
integral along `⊥`.

Let `l` be either `BoxIntegral.IntegrationParams.Henstock` or `⊥`. Let `g` a box-additive function
on subboxes of `I`. Suppose that there exists a nonnegative box-additive function `B` and a
countable set `s` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0` such that for any
box `J ≤ I` such that

- `x ∈ J.Icc ⊆ Metric.closedBall x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to `J` and `g J` is
less than or equal to `ε` if `x ∈ s` and is less than or equal to `ε * B J` otherwise.

Then `f` is integrable on `I` along `l` with integral `g I`. -/
/-
**BoxIntegral.HasIntegral.of_le_Henstock_of_forall_isLittleO** 是 Mathlib 中的一个定理，
位于命名空间 `BoxIntegral.HasIntegral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {l : BoxIntegral.Integration
Params} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤},   
l ≤ BoxIntegral.IntegrationParams.Henstock →     ∀ (B : BoxIntegral.BoxAdditiveM
ap ι ℝ ↑I),       (∀ (J : BoxIntegral.Box ι), 0 ≤ B J) →         ∀ (g : BoxInteg
ral.BoxAdditiveMap ι F ↑I) (s : Set (ι → ℝ)),           s.Countable →           
  (∀ (c : NNReal),                 ∀ x ∈ BoxIntegral.Box.Icc I ∩ s,             
      ∀ ε > 0,                     ∃ δ > 0,                       ∀ J ≤ I,      
                   BoxIntegral.Box.Icc J ⊆ Metric.closedBall x δ →              
             x ∈ BoxIntegral.Box.Icc J →                             (l.bDistort
ion = true → J.distortion ≤ c) → dist ((vol J) (f x)) (g J) ≤ ε) →              
 (∀ (c : NNReal),                   ∀ x ∈ BoxIntegral.Box.Icc I \ s,            
         ∀ ε > 0,                       ∃ δ > 0,                         ∀ J ≤ I
,                           BoxIntegral.Box.Icc J ⊆ Metric.closedBall x δ →     
                        x ∈ BoxIntegral.Box.Icc J →                             
  (l.bDistortion = true → J.distortion ≤ c) → dist ((vol J) (f x)) (g J) ≤ ε * B
 J) →                 BoxIntegral.HasIntegral I l f vol (g I)
参数：ι → ℝ；E →L[ℝ] F；B : BoxIntegral.BoxAdditiveMap ι ℝ ↑I；∀ (J : BoxIntegral.Box 
ι), 0 ≤ B J；g : BoxIntegral.BoxAdditiveMap ι F ↑I；s : Set (ι → ℝ)；∀ (c : NNReal)
,                 ∀ x ∈ BoxIntegral.Box.Icc I ∩ s,                   ∀ ε > 0,   
                  ∃ δ > 0,                       ∀ J ≤ I,                       
  BoxIntegral.Box.Icc J ⊆ Metric.closedBall x δ →                           x ∈ 
BoxIntegral.Box.Icc J →                             (l.bDistortion = true → J.di
stortion ≤ c) → dist ((vol J) (f x)) (g J) ≤ ε；∀ (c : NNReal),                  
 ∀ x ∈ BoxIntegral.Box.Icc I \ s,                     ∀ ε > 0,                  
     ∃ δ > 0,                         ∀ J ≤ I,                           BoxInte
gral.Box.Icc J ⊆ Metric.closedBall x δ →                             x ∈ BoxInte
gral.Box.Icc J →                               (l.bDistortion = true → J.distort
ion ≤ c) → dist ((vol J) (f x)) (g J) ≤ ε * B J；g I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Bool.eq_true_of_true_le`：∀ {x : Bool}, true ≤ x → x = true
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO`：∀ {ι :
 Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [inst_1 : Norme
dSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 …
· 使用定理 `Bool.eq_false_of_le_false`：∀ {x : Bool}, x ≤ false → x = false
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A function `f` has Henstock (or `⊥`) integral over `I` is equal to the value of 
a box-additive
function `g` on `I` provided that `vol J (f x)` is sufficiently close to `g J` f
or sufficiently
small boxes `J ∋ x`. This lemma is useful to prove, e.g., to prove the Divergenc
e theorem for
integral along `⊥`.

Let `l` be either `BoxIntegral.IntegrationParams.Henstock` or `⊥`. Let `g` a box
-additive function
on subboxes of `I`. Suppose that there exists a nonnegative box-additive functio
n `B` and a
countable set `s` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0
` such that for any
box `J ≤ I` such that

- `x ∈ J.Icc ⊆ Metric.closedBall x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or
 equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to 
`J` and `g J` is
less than or equal to `ε` if `x ∈ s` and is less than or equal to `ε * B J` othe
rwise.

Then `f` is integrable on `I` along `l` with integral `g I`.
-/
theorem HasIntegral.of_le_Henstock_of_forall_isLittleO (hl : l ≤ Henstock) (B : ι →ᵇᵃ[I] ℝ)
    (hB0 : ∀ J, 0 ≤ B J) (g : ι →ᵇᵃ[I] F) (s : Set ℝⁿ) (hs : s.Countable)
    (H₁ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I ∩ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → x ∈ Box.Icc J →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε)
    (H₂ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I \ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → x ∈ Box.Icc J →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε * B J) :
    HasIntegral I l f vol (g I) :=
  have A : l.bHenstock := Bool.eq_true_of_true_le hl.2.1
  HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (Bool.eq_false_of_le_false hl.1) B hB0 _ s hs
    (fun _ => A) H₁ <| by simpa only [A, true_imp_iff] using H₂

/-- Suppose that there exists a nonnegative box-additive function `B` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0` such that for any
box `J ≤ I` such that

- `J.Icc ⊆ Metric.closedBall x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to `J` and `g J` is
less than or equal to `ε * B J`.

Then `f` is McShane integrable on `I` with integral `g I`. -/
/-
**BoxIntegral.HasIntegral.mcShane_of_forall_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.HasIntegral`。
形式化陈述：∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace 
ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]   {f : (ι → ℝ) → E} {vol : Box
Integral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} (B : BoxIntegral.BoxAdditiveMap ι ℝ ↑I)
,   (∀ (J : BoxIntegral.Box ι), 0 ≤ B J) →     ∀ (g : BoxIntegral.BoxAdditiveMap
 ι F ↑I),       (∀ (x : NNReal),           ∀ x ∈ BoxIntegral.Box.Icc I,         
    ∀ ε > 0,               ∃ δ > 0, ∀ J ≤ I, BoxIntegral.Box.Icc J ⊆ Metric.clos
edBall x δ → dist ((vol J) (f x)) (g J) ≤ ε * B J) →         BoxIntegral.HasInte
gral I BoxIntegral.IntegrationParams.McShane f vol (g I)
参数：ι → ℝ；E →L[ℝ] F；B : BoxIntegral.BoxAdditiveMap ι ℝ ↑I；∀ (J : BoxIntegral.Box 
ι), 0 ≤ B J；g : BoxIntegral.BoxAdditiveMap ι F ↑I；∀ (x : NNReal),           ∀ x 
∈ BoxIntegral.Box.Icc I,             ∀ ε > 0,               ∃ δ > 0, ∀ J ≤ I, Bo
xIntegral.Box.Icc J ⊆ Metric.closedBall x δ → dist ((vol J) (f x)) (g J) ≤ ε * B
 J；g I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoxIntegral.HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO`：∀ {ι :
 Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [inst_1 : Norme
dSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 …
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.coe_sort_false`：coe_sort_false : (false : Prop) = False

--- 原说明 ---
Suppose that there exists a nonnegative box-additive function `B` with the follo
wing property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0
` such that for any
box `J ≤ I` such that

- `J.Icc ⊆ Metric.closedBall x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or
 equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to 
`J` and `g J` is
less than or equal to `ε * B J`.

Then `f` is McShane integrable on `I` with integral `g I`.
-/
theorem HasIntegral.mcShane_of_forall_isLittleO (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J)
    (g : ι →ᵇᵃ[I] F) (H : ∀ (_ : ℝ≥0), ∀ x ∈ Box.Icc I, ∀ ε > (0 : ℝ), ∃ δ > 0, ∀ J ≤ I,
      Box.Icc J ⊆ Metric.closedBall x δ → dist (vol J (f x)) (g J) ≤ ε * B J) :
    HasIntegral I McShane f vol (g I) :=
  (HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (l := McShane) rfl B hB0 g ∅ countable_empty
      (fun ⟨_x, hx⟩ => hx.elim) fun _ _ hx => hx.2.elim) <| by
    simpa only [McShane, Bool.coe_sort_false, false_imp_iff, true_imp_iff, sdiff_empty] using H

end BoxIntegral

