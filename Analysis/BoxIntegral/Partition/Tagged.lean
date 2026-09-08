/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
`π`. For simplicity we require that the function `BoxIntegral.TaggedPrepartition.tag` is defined
on all boxes `J : Box ι` but use its values only on boxes of the partition. Given
`π : BoxIntegral.TaggedPrepartition I`, we require that each `BoxIntegral.TaggedPrepartition π J`
belongs to `BoxIntegral.Box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is
called a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

## Tags

rectangular box, box partition
-/

@[expose] public section


noncomputable section

open Finset Function ENNReal NNReal Set

namespace BoxIntegral

variable {ι : Type*}

/-- A tagged prepartition is a prepartition enriched with a tagged point for each box of the
prepartition. For simplicity we require that `tag` is defined for all boxes in `ι → ℝ` but
we will use only the values of `tag` on the boxes of the partition. -/
/-
**BoxIntegral.TaggedPrepartition** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoxIntegral`。
形式化陈述：{ι : Type u_1} → BoxIntegral.Box ι → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tagged prepartition is a prepartition enriched with a tagged point for each bo
x of the
prepartition. For simplicity we require that `tag` is defined for all boxes in `
ι → ℝ` but
we will use only the values of `tag` on the boxes of the partition.
-/
structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  /-- Choice of tagged point of each box in this prepartition:
  we extend this to a total function, on all boxes in `ι → ℝ`. -/
  tag : Box ι → ι → ℝ
  /-- Each tagged point belongs to `I` -/
  tag_mem_Icc : ∀ J, tag J ∈ Box.Icc I

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}

/-
**BoxIntegral.TaggedPrepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.TaggedP
repartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (Box ι) (TaggedPrepartition I) :=
  ⟨fun π J => J ∈ π.boxes⟩

@[simp]
/-
**BoxIntegral.TaggedPrepartition.mem_toPrepartition** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.TaggedPrepartition`。
形式化陈述：mem_toPrepartition {π : TaggedPrepartition I} : J in π.toPrepartition ↔ J 
in π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toPrepartition {π : TaggedPrepartition I} : J ∈ π.toPrepartition ↔ J ∈ π := Iff.rfl

@[simp]
/-
**BoxIntegral.TaggedPrepartition.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.T
aggedPrepartition`。
形式化陈述：mem_mk (π : Prepartition I) (f h) : J in mk π f h ↔ J in π
参数：π : Prepartition I；f h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk (π : Prepartition I) (f h) : J ∈ mk π f h ↔ J ∈ π := Iff.rfl

/-- Union of all boxes of a tagged prepartition. -/
/-
**BoxIntegral.TaggedPrepartition.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.T
aggedPrepartition`。
形式化陈述：iUnion : Set (ι -> Real)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Union of all boxes of a tagged prepartition.
-/
def iUnion : Set (ι → ℝ) :=
  π.toPrepartition.iUnion
/-
**BoxIntegral.TaggedPrepartition.iUnion_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.TaggedPrepartition`。
形式化陈述：iUnion_def : π.iUnion = ⋃ J in π, ↑J
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion_def : π.iUnion = ⋃ J ∈ π, ↑J := rfl

@[simp]
/-
**BoxIntegral.TaggedPrepartition.iUnion_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.TaggedPrepartition`。
形式化陈述：iUnion_mk (π : Prepartition I) (f h) : (mk π f h).iUnion = π.iUnion
参数：π : Prepartition I；f h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion_mk (π : Prepartition I) (f h) : (mk π f h).iUnion = π.iUnion := rfl

@[simp]
/-
**BoxIntegral.TaggedPrepartition.iUnion_toPrepartition** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.TaggedPrepartition`。
形式化陈述：iUnion_toPrepartition : π.toPrepartition.iUnion = π.iUnion
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion_toPrepartition : π.toPrepartition.iUnion = π.iUnion := rfl

@[simp]
/-
**BoxIntegral.TaggedPrepartition.mem_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.TaggedPrepartition`。
形式化陈述：mem_iUnion : x in π.iUnion ↔ exists J in π, x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.mem_coe`：mem_coe : x in (I : Set (ι -> Real)) ↔ x in I
· 使用定理 `BoxIntegral.TaggedPrepartition.mem_toPrepartition`：mem_toPrepartition {π
 : TaggedPrepartition I} : J in π.toPrepartition ↔ J in π
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem mem_iUnion : x ∈ π.iUnion ↔ ∃ J ∈ π, x ∈ J := by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe, mem_toPrepartition, exists_prop]
/-
**BoxIntegral.TaggedPrepartition.subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.TaggedPrepartition`。
形式化陈述：subset_iUnion (h : J in π) : ↑J subseteq π.iUnion
参数：h : J in π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
theorem subset_iUnion (h : J ∈ π) : ↑J ⊆ π.iUnion :=
  subset_biUnion_of_mem h
/-
**BoxIntegral.TaggedPrepartition.iUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.TaggedPrepartition`。
形式化陈述：iUnion_subset : π.iUnion subseteq I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `BoxIntegral.Prepartition.le_of_mem'`：∀ {ι : Type u_1} {I : BoxIntegral.B
ox ι} (self : BoxIntegral.Prepartition I), ∀ J ∈ self.boxes, J ≤ I
-/
theorem iUnion_subset : π.iUnion ⊆ I :=
  iUnion₂_subset π.le_of_mem'

/-- A tagged prepartition is a partition if it covers the whole box. -/
/-
**BoxIntegral.TaggedPrepartition.IsPartition** 是 Mathlib 中的一个定义，位于命名空间 `BoxInteg
ral.TaggedPrepartition`。
形式化陈述：IsPartition
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tagged prepartition is a partition if it covers the whole box.
-/
def IsPartition :=
  π.toPrepartition.IsPartition
/-
**BoxIntegral.TaggedPrepartition.isPartition_iff_iUnion_eq** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：isPartition_iff_iUnion_eq : IsPartition π ↔ π.iUnion = I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq`：isPartition_iff_iUni
on_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I
-/
theorem isPartition_iff_iUnion_eq : IsPartition π ↔ π.iUnion = I :=
  Prepartition.isPartition_iff_iUnion_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps! -fullyApplied]
/-
**BoxIntegral.TaggedPrepartition.filter** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.T
aggedPrepartition`。
形式化陈述：filter (p : Box ι -> Prop) : TaggedPrepartition I
参数：p : Box ι -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.tag_mem_Icc`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (self : BoxIntegral.TaggedPrepartition I) (J : BoxIntegral.Box ι), 
  self.tag J ∈ BoxIntegral.Box.I…

--- 原说明 ---
The tagged partition made of boxes of `π` that satisfy predicate `p`.
-/
def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩

@[simp]
/-
**BoxIntegral.TaggedPrepartition.mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.TaggedPrepartition`。
形式化陈述：mem_filter {p : Box ι -> Prop} : J in π.filter p ↔ J in π ∧ p J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J := by
  classical exact Finset.mem_filter

@[simp]
/-
**BoxIntegral.TaggedPrepartition.iUnion_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Bo
xIntegral.TaggedPrepartition`。
形式化陈述：iUnion_filter_not (π : TaggedPrepartition I) (p : Box ι -> Prop) : (π.filt
er fun J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion
参数：π : TaggedPrepartition I；p : Box ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.iUnion_filter_not`：iUnion_filter_not (π : Prepa
rtition I) (p : Box ι -> Prop) : (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π
.filter p).iUnion
-/
theorem iUnion_filter_not (π : TaggedPrepartition I) (p : Box ι → Prop) :
    (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion :=
  π.toPrepartition.iUnion_filter_not p

end TaggedPrepartition

namespace Prepartition

variable {I J : Box ι}

/-- Given a partition `π` of `I : BoxIntegral.Box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
/-
**BoxIntegral.Prepartition.biUnionTagged** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：biUnionTagged (π : Prepartition I) (πi : forall J : Box ι, TaggedPrepartit
ion J) : TaggedPrepartition I where toPrepartition
参数：π : Prepartition I；πi : forall J : Box ι, TaggedPrepartition J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a partition `π` of `I : BoxIntegral.Box ι` and a collection of tagged part
itions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the bo
xes of `πi J`
with tags coming from `(πi J).tag`.
-/
def biUnionTagged (π : Prepartition I) (πi : ∀ J : Box ι, TaggedPrepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.biUnion fun J => (πi J).toPrepartition
  tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)

@[simp]
/-
**BoxIntegral.Prepartition.mem_biUnionTagged** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.Prepartition`。
形式化陈述：mem_biUnionTagged (π : Prepartition I) {πi : forall J, TaggedPrepartition 
J} : J in π.biUnionTagged πi ↔ exists J' in π, J in πi J'
参数：π : Prepartition I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
-/
theorem mem_biUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} :
    J ∈ π.biUnionTagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
  π.mem_biUnion
/-
**BoxIntegral.Prepartition.tag_biUnionTagged** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.Prepartition`。
形式化陈述：tag_biUnionTagged (π : Prepartition I) {πi : forall J, TaggedPrepartition 
J} (hJ : J in π) {J'} (hJ' : J' in πi J) : (π.biUnionTagged πi).tag J' = (πi J).
tag J'
参数：π : Prepartition I；hJ : J in π；hJ' : J' in πi J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex_of_mem`：biUnionIndex_of_mem (hJ : 
J in π) {J'} (hJ' : J' in πi J) : π.biUnionIndex πi J' = J
-/
theorem tag_biUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} (hJ : J ∈ π) {J'}
    (hJ' : J' ∈ πi J) : (π.biUnionTagged πi).tag J' = (πi J).tag J' := by
  rw [← π.biUnionIndex_of_mem (πi := fun J => (πi J).toPrepartition) hJ hJ']
  rfl

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_biUnionTagged** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：iUnion_biUnionTagged (π : Prepartition I) (πi : forall J, TaggedPrepartiti
on J) : (π.biUnionTagged πi).iUnion = ⋃ J in π, (πi J).iUnion
参数：π : Prepartition I；πi : forall J, TaggedPrepartition J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.iUnion_biUnion`：iUnion_biUnion (πi : forall J :
 Box ι, Prepartition J) : (π.biUnion πi).iUnion = ⋃ J in π, (πi J).iUnion
-/
theorem iUnion_biUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (π.biUnionTagged πi).iUnion = ⋃ J ∈ π, (πi J).iUnion :=
  iUnion_biUnion _ _
/-
**BoxIntegral.Prepartition.forall_biUnionTagged** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：forall_biUnionTagged (p : (ι -> Real) -> Box ι -> Prop) (π : Prepartition 
I) (πi : forall J, TaggedPrepartition J) : (forall J in π.biUnionTagged πi, p ((
π.biUnionTagged πi).tag J) J) ↔ forall J in π, forall J' in πi J, p ((πi J).tag 
J') J'
参数：p : (ι -> Real) -> Box ι -> Prop；π : Prepartition I；πi : forall J, TaggedPrep
artition J。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.tag_biUnionTagged`：tag_biUnionTagged (π : Prepa
rtition I) {πi : forall J, TaggedPrepartition J} (hJ : J in π) {J'} (hJ' : J' in
 πi J) : (π.biUnionTagged πi).ta…
-/
theorem forall_biUnionTagged (p : (ι → ℝ) → Box ι → Prop) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (∀ J ∈ π.biUnionTagged πi, p ((π.biUnionTagged πi).tag J) J) ↔
      ∀ J ∈ π, ∀ J' ∈ πi J, p ((πi J).tag J') J' := by
  simp only [mem_biUnionTagged]
  refine ⟨fun H J hJ J' hJ' => ?_, fun H J' ⟨J, hJ, hJ'⟩ => ?_⟩
  · rw [← π.tag_biUnionTagged hJ hJ']
    exact H J' ⟨J, hJ, hJ'⟩
  · rw [π.tag_biUnionTagged hJ hJ']
    exact H J hJ J' hJ'
/-
**BoxIntegral.Prepartition.IsPartition.biUnionTagged** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.Prepartition I},
   π.IsPartition →     ∀ {πi : (J : BoxIntegral.Box ι) → BoxIntegral.TaggedPrepa
rtition J},       (∀ J ∈ π, (πi J).IsPartition) → (π.biUnionTagged πi).IsPartiti
on
参数：J : BoxIntegral.Box ι；∀ J ∈ π, (πi J).IsPartition；π.biUnionTagged πi。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.biUnion`：∀ {ι : Type u_1} {I : BoxI
ntegral.Box ι} {π : BoxIntegral.Prepartition I}   {πi : (J : BoxIntegral.Box ι) 
→ BoxIntegral.Prepartition J},   π…
-/
theorem IsPartition.biUnionTagged {π : Prepartition I} (h : IsPartition π)
    {πi : ∀ J, TaggedPrepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnionTagged πi).IsPartition :=
  h.biUnion hi

end Prepartition

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps -fullyApplied tag]
/-
**BoxIntegral.TaggedPrepartition.biUnionPrepartition** 是 Mathlib 中的一个定义，位于命名空间 `
BoxIntegral.TaggedPrepartition`。
形式化陈述：biUnionPrepartition (π : TaggedPrepartition I) (πi : forall J : Box ι, Pre
partition J) : TaggedPrepartition I where toPrepartition
参数：π : TaggedPrepartition I；πi : forall J : Box ι, Prepartition J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of ea
ch `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag
 of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition.
-/
def biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J : Box ι, Prepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _
/-
**BoxIntegral.TaggedPrepartition.IsPartition.biUnionPrepartition** 是 Mathlib 中的一
个定理，位于命名空间 `BoxIntegral.TaggedPrepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.TaggedPrepartiti
on I},   π.IsPartition →     ∀ {πi : (J : BoxIntegral.Box ι) → BoxIntegral.Prepa
rtition J},       (∀ J ∈ π, (πi J).IsPartition) → (π.biUnionPrepartition πi).IsP
artition
参数：J : BoxIntegral.Box ι；∀ J ∈ π, (πi J).IsPartition；π.biUnionPrepartition πi。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.biUnion`：∀ {ι : Type u_1} {I : BoxI
ntegral.Box ι} {π : BoxIntegral.Prepartition I}   {πi : (J : BoxIntegral.Box ι) 
→ BoxIntegral.Prepartition J},   π…
-/
theorem IsPartition.biUnionPrepartition {π : TaggedPrepartition I} (h : IsPartition π)
    {πi : ∀ J, Prepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnionPrepartition πi).IsPartition :=
  h.biUnion hi

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `toPrepartition = π₁.toPrepartition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
/-
**BoxIntegral.TaggedPrepartition.infPrepartition** 是 Mathlib 中的一个定义，位于命名空间 `BoxI
ntegral.TaggedPrepartition`。
形式化陈述：infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedP
repartition I
参数：π : TaggedPrepartition I；π' : Prepartition I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, ret
urns the tagged
partition with `toPrepartition = π₁.toPrepartition ⊓ π₂` and tags coming from `π
₁`.

Note that usually the result is not a Henstock partition.
-/
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.biUnionPrepartition fun J => π'.restrict J

@[simp]
/-
**BoxIntegral.TaggedPrepartition.infPrepartition_toPrepartition** 是 Mathlib 中的一个
定理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartiti
on I) : (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π'
参数：π : TaggedPrepartition I；π' : Prepartition I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π' := rfl
/-
**BoxIntegral.TaggedPrepartition.mem_infPrepartition_comm** 是 Mathlib 中的一个定理，位于命
名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：mem_infPrepartition_comm : J in π₁.infPrepartition π₂.toPrepartition ↔ J i
n π₂.infPrepartition π₁.toPrepartition
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_infPrepartition_comm :
    J ∈ π₁.infPrepartition π₂.toPrepartition ↔ J ∈ π₂.infPrepartition π₁.toPrepartition := by
  simp only [← mem_toPrepartition, infPrepartition_toPrepartition, inf_comm]
/-
**BoxIntegral.TaggedPrepartition.IsPartition.infPrepartition** 是 Mathlib 中的一个定理，
位于命名空间 `BoxIntegral.TaggedPrepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π₁ : BoxIntegral.TaggedPrepartit
ion I},   π₁.IsPartition → ∀ {π₂ : BoxIntegral.Prepartition I}, π₂.IsPartition →
 (π₁.infPrepartition π₂).IsPartition
参数：π₁.infPrepartition π₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.inf`：∀ {ι : Type u_1} {I : BoxInteg
ral.Box ι} {π₁ π₂ : BoxIntegral.Prepartition I},   π₁.IsPartition → π₂.IsPartiti
on → (π₁ ⊓ π₂).IsPartition
-/
theorem IsPartition.infPrepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
    (h₂ : π₂.IsPartition) : (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂

open Metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
/-
**BoxIntegral.TaggedPrepartition.IsHenstock** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegr
al.TaggedPrepartition`。
形式化陈述：IsHenstock (π : TaggedPrepartition I) : Prop
参数：π : TaggedPrepartition I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the t
ag of `J`
belongs to `J.Icc`.
-/
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀ J ∈ π, π.tag J ∈ Box.Icc J

@[simp]
/-
**BoxIntegral.TaggedPrepartition.isHenstock_biUnionTagged** 是 Mathlib 中的一个定理，位于命
名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：isHenstock_biUnionTagged {π : Prepartition I} {πi : forall J, TaggedPrepar
tition J} : IsHenstock (π.biUnionTagged πi) ↔ forall J in π, (πi J).IsHenstock
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.forall_biUnionTagged`：forall_biUnionTagged (p :
 (ι -> Real) -> Box ι -> Prop) (π : Prepartition I) (πi : forall J, TaggedPrepar
tition J) : (forall J in π.biUnionT…
-/
theorem isHenstock_biUnionTagged {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsHenstock (π.biUnionTagged πi) ↔ ∀ J ∈ π, (πi J).IsHenstock :=
  π.forall_biUnionTagged (fun x J => x ∈ Box.Icc J) πi

/-- In a Henstock prepartition, there are at most `2 ^ Fintype.card ι` boxes with a given tag. -/
/-
**BoxIntegral.TaggedPrepartition.IsHenstock.card_filter_tag_eq_le** 是 Mathlib 中的
一个定理，位于命名空间 `BoxIntegral.TaggedPrepartition.IsHenstock`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.TaggedPrepartiti
on I} [inst : Fintype ι],   π.IsHenstock → ∀ (x : ι → ℝ), {J ∈ π.boxes | π.tag J
 = x}.card ≤ 2 ^ Fintype.card ι
参数：x : ι → ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `BoxIntegral.Prepartition.card_filter_mem_Icc_le`：card_filter_mem_Icc_le 
[Fintype ι] (x : ι -> Real) : #{J in π.boxes | x in Box.Icc J} <= 2 ^ Fintype.ca
rd ι

--- 原说明 ---
In a Henstock prepartition, there are at most `2 ^ Fintype.card ι` boxes with a 
given tag.
-/
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι → ℝ) :
    #{J ∈ π.boxes | π.tag J = x} ≤ 2 ^ Fintype.card ι := by
  classical
  calc
    #{J ∈ π.boxes | π.tag J = x} ≤ #{J ∈ π.boxes | x ∈ Box.Icc J} := by
      refine Finset.card_le_card fun J hJ => ?_
      rw [Finset.mem_filter] at hJ ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate** 是 Mathlib 中的一个定义，位于命名空间 `BoxInt
egral.TaggedPrepartition`。
形式化陈述：IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι -> Real) -> I
oi (0 : Real)) : Prop
参数：π : TaggedPrepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` i
s included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`.
-/
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J ∈ π, Box.Icc J ⊆ closedBall (π.tag J) (r <| π.tag J)

variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

@[simp]
/-
**BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTagged** 是 Mathlib 中的一个定理，
位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：isSubordinate_biUnionTagged [Fintype ι] {π : Prepartition I} {πi : forall 
J, TaggedPrepartition J} : IsSubordinate (π.biUnionTagged πi) r ↔ forall J in π,
 (πi J).IsSubordinate r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.forall_biUnionTagged`：forall_biUnionTagged (p :
 (ι -> Real) -> Box ι -> Prop) (π : Prepartition I) (πi : forall J, TaggedPrepar
tition J) : (forall J in π.biUnionT…
-/
theorem isSubordinate_biUnionTagged [Fintype ι] {π : Prepartition I}
    {πi : ∀ J, TaggedPrepartition J} :
    IsSubordinate (π.biUnionTagged πi) r ↔ ∀ J ∈ π, (πi J).IsSubordinate r :=
  π.forall_biUnionTagged (fun x J => Box.Icc J ⊆ closedBall x (r x)) πi
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate.biUnionPrepartition** 是 Mathlib 中
的一个定理，位于命名空间 `BoxIntegral.TaggedPrepartition.IsSubordinate`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.TaggedPrepartiti
on I} {r : (ι → ℝ) → ↑(Set.Ioi 0)}   [inst : Fintype ι],   π.IsSubordinate r →  
   ∀ (πi : (J : BoxIntegral.Box ι) → BoxIntegral.Prepartition J), (π.biUnionPrep
artition πi).IsSubordinate r
参数：ι → ℝ；Set.Ioi 0；πi : (J : BoxIntegral.Box ι) → BoxIntegral.Prepartition J；π.b
iUnionPrepartition πi。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.le_iff_Icc`：le_iff_Icc : I <= J ↔ Box.Icc I subseteq Box
.Icc J
· 使用定理 `BoxIntegral.Prepartition.le_biUnionIndex`：le_biUnionIndex (hJ : J in π.b
iUnion πi) : J <= π.biUnionIndex πi J
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex_mem`：biUnionIndex_mem (hJ : J in π
.biUnion πi) : π.biUnionIndex πi J in π
-/
theorem IsSubordinate.biUnionPrepartition [Fintype ι] (h : IsSubordinate π r)
    (πi : ∀ J, Prepartition J) : IsSubordinate (π.biUnionPrepartition πi) r :=
  fun _ hJ => Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_biUnionIndex hJ) <|
    h _ <| π.toPrepartition.biUnionIndex_mem hJ
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate.infPrepartition** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.TaggedPrepartition.IsSubordinate`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.TaggedPrepartiti
on I} {r : (ι → ℝ) → ↑(Set.Ioi 0)}   [inst : Fintype ι], π.IsSubordinate r → ∀ (
π' : BoxIntegral.Prepartition I), (π.infPrepartition π').IsSubordinate r
参数：ι → ℝ；Set.Ioi 0；π' : BoxIntegral.Prepartition I；π.infPrepartition π'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.IsSubordinate.biUnionPrepartition`：∀ {ι :
 Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.TaggedPrepartition I} {r : (
ι → ℝ) → ↑(Set.Ioi 0)}   [inst : Fintype ι],   π.IsSub…
-/
theorem IsSubordinate.infPrepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.biUnionPrepartition _
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate.mono'** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.TaggedPrepartition.IsSubordinate`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} 
[inst : Fintype ι]   {π : BoxIntegral.TaggedPrepartition I},   π.IsSubordinate r
₁ → (∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) → π.IsSubordinate r₂
参数：ι → ℝ；Set.Ioi 0；∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂
-/
theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) : π.IsSubordinate r₂ :=
  fun _ hJ _ hx => closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate.mono** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.TaggedPrepartition.IsSubordinate`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} 
[inst : Fintype ι]   {π : BoxIntegral.TaggedPrepartition I},   π.IsSubordinate r
₁ → (∀ x ∈ BoxIntegral.Box.Icc I, r₁ x ≤ r₂ x) → π.IsSubordinate r₂
参数：ι → ℝ；Set.Ioi 0；∀ x ∈ BoxIntegral.Box.Icc I, r₁ x ≤ r₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.IsSubordinate.mono'`：∀ {ι : Type u_1} {I 
: BoxIntegral.Box ι} {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} [inst : Fintype ι]   {π : 
BoxIntegral.TaggedPrepartition I},   π.I…
· 使用定理 `BoxIntegral.TaggedPrepartition.tag_mem_Icc`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (self : BoxIntegral.TaggedPrepartition I) (J : BoxIntegral.Box ι), 
  self.tag J ∈ BoxIntegral.Box.I…
-/
theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ x ∈ Box.Icc I, r₁ x ≤ r₂ x) : π.IsSubordinate r₂ :=
  hr₁.mono' fun J _ => h _ <| π.tag_mem_Icc J
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate.diam_le** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.TaggedPrepartition.IsSubordinate`。
形式化陈述：∀ {ι : Type u_1} {I J : BoxIntegral.Box ι} {r : (ι → ℝ) → ↑(Set.Ioi 0)} [i
nst : Fintype ι]   {π : BoxIntegral.TaggedPrepartition I},   π.IsSubordinate r →
 J ∈ π.boxes → Metric.diam (BoxIntegral.Box.Icc J) ≤ 2 * ↑(r (π.tag J))
参数：ι → ℝ；Set.Ioi 0；BoxIntegral.Box.Icc J；r (π.tag J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.diam_mono`：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBou
nded t) : diam s <= diam t
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `Metric.diam_closedBall`：diam_closedBall {r : Real} (h : 0 <= r) : diam (
closedBall x r) <= 2 * r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
    (hJ : J ∈ π.boxes) : diam (Box.Icc J) ≤ 2 * r (π.tag J) :=
  calc
    diam (Box.Icc J) ≤ diam (closedBall (π.tag J) (r <| π.tag J)) :=
      diam_mono (h J hJ) isBounded_closedBall
    _ ≤ 2 * r (π.tag J) := diam_closedBall (le_of_lt (r _).2)

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps! -fullyApplied]
/-
**BoxIntegral.TaggedPrepartition.single** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.T
aggedPrepartition`。
形式化陈述：single (I J : Box ι) (hJ : J <= I) (x : ι -> Real) (h : x in Box.Icc I) : 
TaggedPrepartition I
参数：I J : Box ι；hJ : J <= I；x : ι -> Real；h : x in Box.Icc I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tagged prepartition with single box and prescribed tag.
-/
def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ Box.Icc I) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun _ => x, fun _ => h⟩

@[simp]
/-
**BoxIntegral.TaggedPrepartition.mem_single** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.TaggedPrepartition`。
形式化陈述：mem_single {J'} (hJ : J <= I) (h : x in Box.Icc I) : J' in single I J hJ x
 h ↔ J' = J
参数：hJ : J <= I；h : x in Box.Icc I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ Box.Icc I) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton
/-
**BoxIntegral.TaggedPrepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.TaggedP
repartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩
/-
**BoxIntegral.TaggedPrepartition.isPartition_single_iff** 是 Mathlib 中的一个定理，位于命名空
间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：isPartition_single_iff (hJ : J <= I) (h : x in Box.Icc I) : (single I J hJ
 x h).IsPartition ↔ J = I
参数：hJ : J <= I；h : x in Box.Icc I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.isPartition_single_iff`：isPartition_single_iff 
(h : J <= I) : IsPartition (single I J h) ↔ J = I
-/
theorem isPartition_single_iff (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.isPartition_single_iff hJ
/-
**BoxIntegral.TaggedPrepartition.isPartition_single** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.TaggedPrepartition`。
形式化陈述：isPartition_single (h : x in Box.Icc I) : (single I I le_rfl x h).IsPartit
ion
参数：h : x in Box.Icc I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.isPartitionTop`：isPartitionTop (I : Box ι) : Is
Partition (⊤ : Prepartition I)
-/
theorem isPartition_single (h : x ∈ Box.Icc I) : (single I I le_rfl x h).IsPartition :=
  Prepartition.isPartitionTop I
/-
**BoxIntegral.TaggedPrepartition.forall_mem_single** 是 Mathlib 中的一个定理，位于命名空间 `Bo
xIntegral.TaggedPrepartition`。
形式化陈述：forall_mem_single (p : (ι -> Real) -> Box ι -> Prop) (hJ : J <= I) (h : x 
in Box.Icc I) : (forall J' in single I J hJ x h, p ((single I J hJ x h).tag J') 
J') ↔ p x J
参数：p : (ι -> Real) -> Box ι -> Prop；hJ : J <= I；h : x in Box.Icc I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoxIntegral.TaggedPrepartition.single_tag`：∀ {ι : Type u_1} (I J : BoxIn
tegral.Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ BoxIntegral.Box.Icc I),   (BoxIn
tegral.TaggedPrepartition.singl…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_single (p : (ι → ℝ) → Box ι → Prop) (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).tag J') J') ↔ p x J := by simp

@[simp]
/-
**BoxIntegral.TaggedPrepartition.isHenstock_single_iff** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.TaggedPrepartition`。
形式化陈述：isHenstock_single_iff (hJ : J <= I) (h : x in Box.Icc I) : IsHenstock (sin
gle I J hJ x h) ↔ x in Box.Icc J
参数：hJ : J <= I；h : x in Box.Icc I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.forall_mem_single`：forall_mem_single (p :
 (ι -> Real) -> Box ι -> Prop) (hJ : J <= I) (h : x in Box.Icc I) : (forall J' i
n single I J hJ x h, p ((single I J hJ…
-/
theorem isHenstock_single_iff (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    IsHenstock (single I J hJ x h) ↔ x ∈ Box.Icc J :=
  forall_mem_single (fun x J => x ∈ Box.Icc J) hJ h
/-
**BoxIntegral.TaggedPrepartition.isHenstock_single** 是 Mathlib 中的一个定理，位于命名空间 `Bo
xIntegral.TaggedPrepartition`。
形式化陈述：isHenstock_single (h : x in Box.Icc I) : IsHenstock (single I I le_rfl x h
)
参数：h : x in Box.Icc I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `BoxIntegral.TaggedPrepartition.isHenstock_single_iff`：isHenstock_single_
iff (hJ : J <= I) (h : x in Box.Icc I) : IsHenstock (single I J hJ x h) ↔ x in B
ox.Icc J
-/
theorem isHenstock_single (h : x ∈ Box.Icc I) : IsHenstock (single I I le_rfl x h) :=
  (isHenstock_single_iff (le_refl I) h).2 h

@[simp]
/-
**BoxIntegral.TaggedPrepartition.isSubordinate_single** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.TaggedPrepartition`。
形式化陈述：isSubordinate_single [Fintype ι] (hJ : J <= I) (h : x in Box.Icc I) : IsSu
bordinate (single I J hJ x h) r ↔ Box.Icc J subseteq closedBall x (r x)
参数：hJ : J <= I；h : x in Box.Icc I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.forall_mem_single`：forall_mem_single (p :
 (ι -> Real) -> Box ι -> Prop) (hJ : J <= I) (h : x in Box.Icc I) : (forall J' i
n single I J hJ x h, p ((single I J hJ…
-/
theorem isSubordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    IsSubordinate (single I J hJ x h) r ↔ Box.Icc J ⊆ closedBall x (r x) :=
  forall_mem_single (fun x J => Box.Icc J ⊆ closedBall x (r x)) hJ h

@[simp]
/-
**BoxIntegral.TaggedPrepartition.iUnion_single** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.TaggedPrepartition`。
形式化陈述：iUnion_single (hJ : J <= I) (h : x in Box.Icc I) : (single I J hJ x h).iUn
ion = J
参数：hJ : J <= I；h : x in Box.Icc I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.iUnion_single`：iUnion_single (h : J <= I) : (si
ngle I J h).iUnion = J
-/
theorem iUnion_single (hJ : J ≤ I) (h : x ∈ Box.Icc I) : (single I J hJ x h).iUnion = J :=
  Prepartition.iUnion_single hJ

open scoped Classical in
/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
/-
**BoxIntegral.TaggedPrepartition.disjUnion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegra
l.TaggedPrepartition`。
形式化陈述：disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion
) : TaggedPrepartition I where toPrepartition
参数：π₁ π₂ : TaggedPrepartition I；h : Disjoint π₁.iUnion π₂.iUnion。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Union of two tagged prepartitions with disjoint unions of boxes.
-/
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) :
    TaggedPrepartition I where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]

open scoped Classical in
@[simp]
/-
**BoxIntegral.TaggedPrepartition.disjUnion_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.TaggedPrepartition`。
形式化陈述：disjUnion_boxes (h : Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).b
oxes = π₁.boxes union π₂.boxes
参数：h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjUnion_boxes (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).boxes = π₁.boxes ∪ π₂.boxes := rfl

@[simp]
/-
**BoxIntegral.TaggedPrepartition.mem_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.TaggedPrepartition`。
形式化陈述：mem_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) : J in π₁.disjUnion π₂ h 
↔ J in π₁ ∨ J in π₂
参数：h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
theorem mem_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    J ∈ π₁.disjUnion π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ := by
  classical exact Finset.mem_union

@[simp]
/-
**BoxIntegral.TaggedPrepartition.iUnion_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.TaggedPrepartition`。
形式化陈述：iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).
iUnion = π₁.iUnion union π₂.iUnion
参数：h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.iUnion_disjUnion`：iUnion_disjUnion (h : Disjoin
t π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).iUnion = π₁.iUnion union π₂.iUnion
-/
theorem iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).iUnion = π₁.iUnion ∪ π₂.iUnion :=
  Prepartition.iUnion_disjUnion h
/-
**BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：disjUnion_tag_of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁
) : (π₁.disjUnion π₂ h).tag J = π₁.tag J
参数：h : Disjoint π₁.iUnion π₂.iUnion；hJ : J in π₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem disjUnion_tag_of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J ∈ π₁) :
    (π₁.disjUnion π₂ h).tag J = π₁.tag J :=
  dif_pos hJ
/-
**BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right** 是 Mathlib 中的一个定理，位
于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：disjUnion_tag_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π
₂) : (π₁.disjUnion π₂ h).tag J = π₂.tag J
参数：h : Disjoint π₁.iUnion π₂.iUnion；hJ : J in π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `BoxIntegral.TaggedPrepartition.subset_iUnion`：subset_iUnion (h : J in π)
 : ↑J subseteq π.iUnion
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
-/
theorem disjUnion_tag_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J ∈ π₂) :
    (π₁.disjUnion π₂ h).tag J = π₂.tag J :=
  dif_neg fun h₁ => h.le_bot ⟨π₁.subset_iUnion h₁ J.upper_mem, π₂.subset_iUnion hJ J.upper_mem⟩
/-
**BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnion** 是 Mathlib 中的一个定理，位于命名
空间 `BoxIntegral.TaggedPrepartition.IsSubordinate`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π₁ π₂ : BoxIntegral.TaggedPrepar
tition I} {r : (ι → ℝ) → ↑(Set.Ioi 0)}   [inst : Fintype ι],   π₁.IsSubordinate 
r → π₂.IsSubordinate r → ∀ (h : Disjoint π₁.iUnion π₂.iUnion), (π₁.disjUnion π₂ 
h).IsSubordinate r
参数：ι → ℝ；Set.Ioi 0；h : Disjoint π₁.iUnion π₂.iUnion；π₁.disjUnion π₂ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left`：disjUnion_tag_
of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁) : (π₁.disjUnion π₂
 h).tag J = π₁.tag J
· 使用定理 `BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right`：disjUnion_tag
_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₂) : (π₁.disjUnion 
π₂ h).tag J = π₂.tag J
-/
theorem IsSubordinate.disjUnion [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsSubordinate (π₁.disjUnion π₂ h) r := by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
/-
**BoxIntegral.TaggedPrepartition.IsHenstock.disjUnion** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.TaggedPrepartition.IsHenstock`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π₁ π₂ : BoxIntegral.TaggedPrepar
tition I},   π₁.IsHenstock → π₂.IsHenstock → ∀ (h : Disjoint π₁.iUnion π₂.iUnion
), (π₁.disjUnion π₂ h).IsHenstock
参数：h : Disjoint π₁.iUnion π₂.iUnion；π₁.disjUnion π₂ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left`：disjUnion_tag_
of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁) : (π₁.disjUnion π₂
 h).tag J = π₁.tag J
· 使用定理 `BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right`：disjUnion_tag
_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₂) : (π₁.disjUnion 
π₂ h).tag J = π₂.tag J
-/
theorem IsHenstock.disjUnion (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsHenstock (π₁.disjUnion π₂ h) := by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
/-
**BoxIntegral.TaggedPrepartition.embedBox** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral
.TaggedPrepartition`。
形式化陈述：embedBox (I J : Box ι) (h : I <= J) : TaggedPrepartition I ↪ TaggedPrepart
ition J where toFun π
参数：I J : Box ι；h : I <= J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J
`.
-/
def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J where
  toFun π :=
    { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H

section Distortion

variable [Fintype ι] (π)

open Finset

/-- The distortion of a tagged prepartition is the maximum of distortions of its boxes. -/
/-
**BoxIntegral.TaggedPrepartition.distortion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegr
al.TaggedPrepartition`。
形式化陈述：distortion : Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distortion of a tagged prepartition is the maximum of distortions of its box
es.
-/
def distortion : ℝ≥0 :=
  π.toPrepartition.distortion
/-
**BoxIntegral.TaggedPrepartition.distortion_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.TaggedPrepartition`。
形式化陈述：distortion_le_of_mem (h : J in π) : J.distortion <= π.distortion
参数：h : J in π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h
/-
**BoxIntegral.TaggedPrepartition.distortion_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bo
xIntegral.TaggedPrepartition`。
形式化陈述：distortion_le_iff {c : Real>=0} : π.distortion <= c ↔ forall J in π, Box.d
istortion J <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
-/
theorem distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, Box.distortion J ≤ c :=
  Finset.sup_le_iff

@[simp]
/-
**BoxIntegral.TaggedPrepartition._root_.BoxIntegral.Prepartition.distortion_biUn
ionTagged** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoxIntegral.Prepartition.distortion_biUnionTagged (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (π.biUnionTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion := by
  classical exact sup_biUnion _ _

@[simp]
/-
**BoxIntegral.TaggedPrepartition.distortion_biUnionPrepartition** 是 Mathlib 中的一个
定理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：distortion_biUnionPrepartition (π : TaggedPrepartition I) (πi : forall J, 
Prepartition J) : (π.biUnionPrepartition πi).distortion = π.boxes.sup fun J => (
πi J).distortion
参数：π : TaggedPrepartition I；πi : forall J, Prepartition J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
-/
theorem distortion_biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) :
    (π.biUnionPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion := by
  classical exact sup_biUnion _ _

@[simp]
/-
**BoxIntegral.TaggedPrepartition.distortion_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.TaggedPrepartition`。
形式化陈述：distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂
 h).distortion = max π₁.distortion π₂.distortion
参数：h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
-/
theorem distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion := by
  classical exact sup_union
/-
**BoxIntegral.TaggedPrepartition.distortion_of_const** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.TaggedPrepartition`。
形式化陈述：distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.d
istortion J = c) : π.distortion = c
参数：h₁ : π.boxes.Nonempty；h₂ : forall J in π, Box.distortion J = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `Finset.sup_const`：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s
.sup fun _ => c) = c
-/
theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀ J ∈ π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]
/-
**BoxIntegral.TaggedPrepartition.distortion_single** 是 Mathlib 中的一个定理，位于命名空间 `Bo
xIntegral.TaggedPrepartition`。
形式化陈述：distortion_single (hJ : J <= I) (h : x in Box.Icc I) : distortion (single 
I J hJ x h) = J.distortion
参数：hJ : J <= I；h : x in Box.Icc I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
-/
theorem distortion_single (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    distortion (single I J hJ x h) = J.distortion :=
  sup_singleton
/-
**BoxIntegral.TaggedPrepartition.distortion_filter_le** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.TaggedPrepartition`。
形式化陈述：distortion_filter_le (p : Box ι -> Prop) : (π.filter p).distortion <= π.di
stortion
参数：p : Box ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
theorem distortion_filter_le (p : Box ι → Prop) : (π.filter p).distortion ≤ π.distortion := by
  classical exact sup_mono (filter_subset _ _)

end Distortion

end TaggedPrepartition

end BoxIntegral

