/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Split
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Box additive functions

We say that a function `f : Box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : WithTop (Box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' ∈ π.boxes, f J'`. We use `I₀ : WithTop (Box ι)` instead of `I₀ : Box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

## Tags

rectangular box, additive function
-/

@[expose] public section

noncomputable section

open Function Set

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

/-- A function on `Box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji ∈ π.boxes, f Ji`. A function is called box additive on subboxes of `I : Box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the same definition
using `I : WithBot (Box ι)`: the value `I = ⊤` corresponds to functions box additive on the whole
space. -/
/-
**BoxIntegral.BoxAdditiveMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoxIntegral`。
形式化陈述：(ι : Type u_3) → (M : Type u_4) → [AddCommMonoid M] → WithTop (BoxIntegral
.Box ι) → Type (max u_3 u_4)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function on `Box ι` is called box additive if for every box `J` and a partitio
n `π` of `J`
we have `f J = ∑ Ji ∈ π.boxes, f Ji`. A function is called box additive on subbo
xes of `I : Box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the sa
me definition
using `I : WithBot (Box ι)`: the value `I = ⊤` corresponds to functions box addi
tive on the whole
space.
-/
structure BoxAdditiveMap (ι M : Type*) [AddCommMonoid M] (I : WithTop (Box ι)) where
  /-- The function underlying this additive map. -/
  toFun : Box ι → M
  sum_partition_boxes' : ∀ J : Box ι, ↑J ≤ I → ∀ π : Prepartition J, π.IsPartition →
    ∑ Ji ∈ π.boxes, toFun Ji = toFun J


/-- A function on `Box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji ∈ π.boxes, f Ji`. -/
scoped notation:25 ι " →ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤

@[inherit_doc] scoped notation:25 ι " →ᵇᵃ[" I "] " M => BoxIntegral.BoxAdditiveMap ι M I

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type*} [AddCommMonoid M] [AddCommMonoid N] {I₀ : WithTop (Box ι)} {I : Box ι}
  {i : ι}

/-! ### Coercion, extensionality, and the defining property -/

/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Coercion, extensionality, and the defining property
-/
instance : FunLike (ι →ᵇᵃ[I₀] M) (Box ι) M where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

initialize_simps_projections BoxIntegral.BoxAdditiveMap (toFun → apply)

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.BoxAd
ditiveMap`。
形式化陈述：coe_mk (f h) : ⇑(mk f h : ι ->ᵇᵃ[I₀] M) = f
参数：f h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f h) : ⇑(mk f h : ι →ᵇᵃ[I₀] M) = f := rfl
/-
**BoxIntegral.BoxAdditiveMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.BoxAdditiveMap`。
形式化陈述：coe_injective : Injective fun (f : ι ->ᵇᵃ[I₀] M) x => f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : Injective fun (f : ι →ᵇᵃ[I₀] M) x => f x :=
  DFunLike.coe_injective
/-
**BoxIntegral.BoxAdditiveMap.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.BoxA
dditiveMap`。
形式化陈述：coe_inj {f g : ι ->ᵇᵃ[I₀] M} : (f : Box ι -> M) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : Box ι → M) = g ↔ f = g := DFunLike.coe_fn_eq

@[ext]
/-
**BoxIntegral.BoxAdditiveMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.BoxAddit
iveMap`。
形式化陈述：ext {f g : ι ->ᵇᵃ[I₀] M} (h : forall J, f J = g J) : f = g
参数：h : forall J, f J = g J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : ι →ᵇᵃ[I₀] M} (h : ∀ J, f J = g J) : f = g :=
  DFunLike.ext _ _ h
/-
**BoxIntegral.BoxAdditiveMap.sum_partition_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.BoxAdditiveMap`。
形式化陈述：sum_partition_boxes (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I
} (h : π.IsPartition) : ∑ J in π.boxes, f J = f I
参数：f : ι ->ᵇᵃ[I₀] M；hI : ↑I <= I₀；h : π.IsPartition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.BoxAdditiveMap.sum_partition_boxes'`：∀ {ι : Type u_3} {M : T
ype u_4} [inst : AddCommMonoid M] {I : WithTop (BoxIntegral.Box ι)}   (self : Bo
xIntegral.BoxAdditiveMap ι M I) (J : …
-/
theorem sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π : Prepartition I}
    (h : π.IsPartition) : ∑ J ∈ π.boxes, f J = f I :=
  f.sum_partition_boxes' I hI π h

/-! ### Additive monoid structure -/

@[simps -fullyApplied]
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Additive monoid structure
-/
instance : Zero (ι →ᵇᵃ[I₀] M) :=
  ⟨⟨0, fun _ _ _ _ => sum_const_zero⟩⟩
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ι →ᵇᵃ[I₀] M) :=
  ⟨0⟩
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Monoid R] [DistribMulAction R M] : SMul R (ι →ᵇᵃ[I₀] M) :=
  ⟨fun r f =>
    ⟨r • (f : Box ι → M), fun I hI π hπ => by
      simp only [Pi.smul_apply, ← smul_sum, sum_partition_boxes _ hI hπ]⟩⟩
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.add_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoxIntegral.Bo
xAdditiveMap`。
形式化陈述：add_apply (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (f + g) J = f J + g J
参数：f g : ι ->ᵇᵃ[I₀] M；J : Box ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_apply (f g : ι →ᵇᵃ[I₀] M) (J : Box ι) : (f + g) J = f J + g J := rfl

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoxIntegral.B
oxAdditiveMap`。
形式化陈述：smul_apply {R : Type*} [Monoid R] [DistribMulAction R M] (c : R) (f : ι ->
ᵇᵃ[I₀] M) (J : Box ι) : (c • f) J = c • (f J)
参数：c : R；f : ι ->ᵇᵃ[I₀] M；J : Box ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply {R : Type*} [Monoid R] [DistribMulAction R M]
    (c : R) (f : ι →ᵇᵃ[I₀] M) (J : Box ι) : (c • f) J = c • (f J) := rfl

/-! ### Constructions and combinators -/

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.map_split_add** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.BoxAdditiveMap`。
形式化陈述：map_split_add (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) (i : ι) (x : Real) : (I.s
plitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I
参数：f : ι ->ᵇᵃ[I₀] M；hI : ↑I <= I₀；i : ι；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.BoxAdditiveMap.sum_partition_boxes`：sum_partition_boxes (f :
 ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I} (h : π.IsPartition) : ∑ J in
 π.boxes, f J = f I
· 使用定理 `BoxIntegral.Prepartition.isPartitionSplit`：isPartitionSplit (I : Box ι) 
(i : ι) (x : Real) : IsPartition (split I i x)
· 使用定理 `BoxIntegral.Prepartition.sum_split_boxes`：sum_split_boxes {M : Type*} [A
ddCommMonoid M] (I : Box ι) (i : ι) (x : Real) (f : Box ι -> M) : (∑ J in (split
 I i x).boxes, f J) = (I.split…

--- 原说明 ---
### Constructions and combinators
-/
theorem map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) (i : ι) (x : ℝ) :
    (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I := by
  rw [← f.sum_partition_boxes hI (isPartitionSplit I i x), sum_split_boxes]

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps]
/-
**BoxIntegral.BoxAdditiveMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box
AdditiveMap`。
形式化陈述：restrict (f : ι ->ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I <= I₀) : ι ->ᵇᵃ[
I] M
参数：f : ι ->ᵇᵃ[I₀] M；I : WithTop (Box ι)；hI : I <= I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes 
of any
`I ≤ I₀`.
-/
def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩

/-- If `f : Box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
/-
**BoxIntegral.BoxAdditiveMap.ofMapSplitAdd** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegra
l.BoxAdditiveMap`。
形式化陈述：ofMapSplitAdd [Finite ι] (f : Box ι -> M) (I₀ : WithTop (Box ι)) (hf : for
all I : Box ι, ↑I <= I₀ -> forall {i x}, x in Ioo (I.lower i) (I.upper i) -> (I.
splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I) : ι ->ᵇᵃ[I₀] M
参数：f : Box ι -> M；I₀ : WithTop (Box ι)；hf : forall I : Box ι, ↑I <= I₀ -> forall
 {i x}, x in Ioo (I.lower i) (I.upper i) -> (I.splitLower i x).elim' 0 f + (I.sp
litUpper i x).elim' 0 f = f I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…

--- 原说明 ---
If `f : Box ι → M` is box additive on partitions of the form `split I i x`, then
 it is box
additive.
-/
def ofMapSplitAdd [Finite ι] (f : Box ι → M) (I₀ : WithTop (Box ι))
    (hf : ∀ I : Box ι, ↑I ≤ I₀ → ∀ {i x}, x ∈ Ioo (I.lower i) (I.upper i) →
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I) :
    ι →ᵇᵃ[I₀] M := by
  classical
  refine ⟨f, ?_⟩
  replace hf (I : Box ι) (hI : ↑I ≤ I₀) (s) : ∑ J ∈ (splitMany I s).boxes, f J = f I := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ihs =>
      rw [splitMany_insert, inf_split, ← ihs, biUnion_boxes, sum_biUnion_boxes]
      refine Finset.sum_congr rfl fun J' hJ' => ?_
      by_cases h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1)
      · rw [sum_split_boxes]
        exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
      · rw [split_of_notMem_Ioo h, top_boxes, Finset.sum_singleton]
  intro I hI π hπ
  have Hle : ∀ J ∈ π, ↑J ≤ I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_splitMany_le with ⟨s, hs⟩
  rw [← hf _ hI, ← inf_of_le_right hs, inf_splitMany, biUnion_boxes, sum_biUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps -fullyApplied]
/-
**BoxIntegral.BoxAdditiveMap.map** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.BoxAddit
iveMap`。
形式化陈述：map (f : ι ->ᵇᵃ[I₀] M) (g : M ->+ N) : ι ->ᵇᵃ[I₀] N where toFun
参数：f : ι ->ᵇᵃ[I₀] M；g : M ->+ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is
 a box additive
map.
-/
def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) : ι →ᵇᵃ[I₀] N where
  toFun := g ∘ f
  sum_partition_boxes' I hI π hπ := by simp_rw [comp, ← map_sum, f.sum_partition_boxes hI hπ]

/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J ∈ π₁.boxes, f J = ∑ J ∈ π₂.boxes, f J`. -/
/-
**BoxIntegral.BoxAdditiveMap.sum_boxes_congr** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.BoxAdditiveMap`。
形式化陈述：sum_boxes_congr [Finite ι] (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π₁ π₂ : Pre
partition I} (h : π₁.iUnion = π₂.iUnion) : ∑ J in π₁.boxes, f J = ∑ J in π₂.boxe
s, f J
参数：f : ι ->ᵇᵃ[I₀] M；hI : ↑I <= I₀；h : π₁.iUnion = π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.exists_splitMany_inf_eq_filter_of_finite`：exist
s_splitMany_inf_eq_filter_of_finite (s : Set (Prepartition I)) (hs : s.Finite) :
 exists t : Finset (ι × Real), forall π in s, π ⊓ split…
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.BoxAdditiveMap.sum_partition_boxes`：sum_partition_boxes (f :
 ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I} (h : π.IsPartition) : ∑ J in
 π.boxes, f J = f I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `BoxIntegral.Prepartition.isPartition_splitMany`：isPartition_splitMany (I
 : Box ι) (s : Finset (ι × Real)) : IsPartition (splitMany I s)
· 使用定理 `BoxIntegral.Prepartition.sum_biUnion_boxes`：sum_biUnion_boxes {M : Type*
} [AddCommMonoid M] (π : Prepartition I) (πi : forall J, Prepartition J) (f : Bo
x ι -> M) : (∑ J in π.boxes.biUn…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.inf_splitMany`：inf_splitMany {I : Box ι} (π : P
repartition I) (s : Finset (ι × Real)) : π ⊓ splitMany I s = π.biUnion fun J => 
splitMany J s

--- 原说明 ---
If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prep
artitions of
`I` that cover the same part of `I`, then `∑ J ∈ π₁.boxes, f J = ∑ J ∈ π₂.boxes,
 f J`.
-/
theorem sum_boxes_congr [Finite ι] (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : ∑ J ∈ π₁.boxes, f J = ∑ J ∈ π₂.boxes, f J := by
  rcases exists_splitMany_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with
    ⟨s, hs⟩
  simp only [inf_splitMany] at hs
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩; clear hs
  rw [h] at h₁
  calc
    ∑ J ∈ π₁.boxes, f J = ∑ J ∈ π₁.boxes, ∑ J' ∈ (splitMany J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ => (f.sum_partition_boxes ?_ (isPartition_splitMany _ _)).symm
    _ = ∑ J ∈ (π₁.biUnion fun J => splitMany J s).boxes, f J := (sum_biUnion_boxes _ _ _).symm
    _ = ∑ J ∈ (π₂.biUnion fun J => splitMany J s).boxes, f J := by rw [h₁, h₂]
    _ = ∑ J ∈ π₂.boxes, ∑ J' ∈ (splitMany J s).boxes, f J' := sum_biUnion_boxes _ _ _
    _ = ∑ J ∈ π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes ?_ (isPartition_splitMany _ _)
  exacts [(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI,
    (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]

section AddCommGroup

/-! ### Additive group structure -/

variable {M : Type*} [AddCommGroup M]

/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f ↦
    ⟨-(f : Box ι → M), fun I hI π hπ ↦ by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, sum_partition_boxes _ hI hπ]⟩⟩
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g ↦
    ⟨(f : Box ι → M) - g, fun I hI π hπ ↦ by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_partition_boxes _ hI hπ]⟩⟩
/-
**BoxIntegral.BoxAdditiveMap.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.BoxAdditive
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommGroup _ DFunLike.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoxIntegral.Bo
xAdditiveMap`。
形式化陈述：neg_apply (f : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (-f) J = -(f J)
参数：f : ι ->ᵇᵃ[I₀] M；J : Box ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_apply (f : ι →ᵇᵃ[I₀] M) (J : Box ι) : (-f) J = -(f J) := rfl

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.sub_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoxIntegral.Bo
xAdditiveMap`。
形式化陈述：sub_apply (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (f - g) J = f J - g J
参数：f g : ι ->ᵇᵃ[I₀] M；J : Box ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_apply (f g : ι →ᵇᵃ[I₀] M) (J : Box ι) : (f - g) J = f J - g J := rfl

end AddCommGroup

section ToSMul

/-! ### Scalar multiplication on a normed space -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
/-
**BoxIntegral.BoxAdditiveMap.toSMul** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.BoxAd
ditiveMap`。
形式化陈述：toSMul (f : ι ->ᵇᵃ[I₀] Real) : ι ->ᵇᵃ[I₀] E ->L[Real] E
参数：f : ι ->ᵇᵃ[I₀] Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a box-additive map, then so is the map sending `I` to the scalar multi
plication
by `f I` as a continuous linear map from `E` to itself.
-/
def toSMul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] E →L[ℝ] E :=
  f.map (ContinuousLinearMap.lsmul ℝ ℝ).toLinearMap.toAddMonoidHom

@[simp]
/-
**BoxIntegral.BoxAdditiveMap.toSMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.BoxAdditiveMap`。
形式化陈述：toSMul_apply (f : ι ->ᵇᵃ[I₀] Real) (I : Box ι) (x : E) : f.toSMul I x = f 
I • x
参数：f : ι ->ᵇᵃ[I₀] Real；I : Box ι；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toSMul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : Box ι) (x : E) : f.toSMul I x = f I • x := rfl

end ToSMul

/-! ### Difference along an axis: `upper − lower` over faces -/

/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : Box (Fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `fun J ↦ f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes
of `I₀`. -/
@[simps!]
/-
**BoxIntegral.BoxAdditiveMap.upperSubLower.** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegr
al.BoxAdditiveMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a box `I₀` in `ℝⁿ⁺¹`, `f x : Box (Fin n) → G` is a family of functions ind
exed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of
 the `i`-th face of
`I₀`, then `fun J ↦ f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-
additive on subboxes
of `I₀`.
-/
def upperSubLower.{u} {G : Type u} [AddCommGroup G] (I₀ : Box (Fin (n + 1))) (i : Fin (n + 1))
    (f : ℝ → Box (Fin n) → G) (fb : Icc (I₀.lower i) (I₀.upper i) → Fin n →ᵇᵃ[I₀.face i] G)
    (hf : ∀ (x) (hx : x ∈ Icc (I₀.lower i) (I₀.upper i)) (J), f x J = fb ⟨x, hx⟩ J) :
    Fin (n + 1) →ᵇᵃ[I₀] G :=
  ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j x
      rw [WithTop.coe_le_coe] at hJ
      refine i.succAboveCases (fun hx => ?_) (fun j hx => ?_) j
      · simp only [Box.splitLower_def hx, Box.splitUpper_def hx, update_self, ← WithBot.some_eq_coe,
          Option.elim', Box.face, Function.comp_def, update_of_ne (Fin.succAbove_ne _ _)]
        abel
      · have : (J.face i : WithTop (Box (Fin n))) ≤ I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc, @Box.Icc_eq_pi _ I₀] at hJ
        rw [hf _ (hJ J.upper_mem_Icc _ trivial), hf _ (hJ J.lower_mem_Icc _ trivial),
          ← (fb _).map_split_add this j x, ← (fb _).map_split_add this j x]
        have hx' : x ∈ Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Box.splitLower_def hx',
          Box.splitUpper_def hx', ← WithBot.some_eq_coe, Option.elim', Box.face_mk,
          update_of_ne (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ (Fin.strictMono_succAbove i).injective j x, ← hf]
        simp only [Box.face])

end BoxAdditiveMap

end BoxIntegral

