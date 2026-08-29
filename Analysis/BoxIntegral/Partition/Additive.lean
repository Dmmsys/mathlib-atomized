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

variable {ι M : Type*} {n : Nat}

/--
Definition of `BoxAdditiveMap` / `BoxAdditiveMap` 的定义

English:
structure BoxAdditiveMap
  parameters: (ι M : Type*) [AddCommMonoid M] (I : WithTop (Box ι))
  axioms and operations (2):
    - toFun : Box ι -> M
    - sum_partition_boxes' : forall J : Box ι, ↑J <= I -> forall π : Prepartition J, π.IsPartition -> ∑ Ji in π.boxes, toFun Ji = toFun J

中文:
结构 BoxAdditive映射
  参数: (ι M : 类型) [加法交换幺半群 M] (I : WithTop (Box ι))
  公理与运算 (2 个):
    - toFun : Box ι -> M
    - sum_partition_boxes' : 对任意 J : Box ι, ↑J <= I -> 对任意 π : 预分拆 J, π.IsPartition -> ∑ Ji in π.boxes, toFun Ji = toFun J
-/
structure BoxAdditiveMap (ι M : Type*) [AddCommMonoid M] (I : WithTop (Box ι)) where
  /-- The function underlying this additive map. -/
  toFun : Box ι -> M
  sum_partition_boxes' : forall J : Box ι, ↑J <= I -> forall π : Prepartition J, π.IsPartition ->
    ∑ Ji in π.boxes, toFun Ji = toFun J


/-- A function on `Box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji ∈ π.boxes, f Ji`. -/
scoped notation:25 ι " ->ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤

@[inherit_doc] scoped notation:25 ι " ->ᵇᵃ[" I "] " M => BoxIntegral.BoxAdditiveMap ι M I

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type*} [AddCommMonoid M] [AddCommMonoid N] {I₀ : WithTop (Box ι)} {I : Box ι}
  {i : ι}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (ι ->ᵇᵃ[I₀] M) (Box ι) M
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

initialize_simps_projections BoxIntegral.BoxAdditiveMap (toFun -> apply)

@[simp]

中文:
实例 :
  签名: 函数状 (ι ->ᵇᵃ[I₀] M) (Box ι) M
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr

initialize_simps_projections BoxIntegral.BoxAdditiveMap (toFun -> apply)

@[simp]
-/
instance : FunLike (ι ->ᵇᵃ[I₀] M) (Box ι) M where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

initialize_simps_projections BoxIntegral.BoxAdditiveMap (toFun -> apply)

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f h)
  statement: ⇑(mk f h : ι ->ᵇᵃ[I₀] M) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f h)
  结论: ⇑(mk f h : ι ->ᵇᵃ[I₀] M) = f
  证明: rfl
-/
theorem coe_mk (f h) : ⇑(mk f h : ι ->ᵇᵃ[I₀] M) = f := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective fun (f : ι ->ᵇᵃ[I₀] M) x => f x
  proof: DFunLike.coe_injective

中文:
定理 coe_injective
  结论: 单射 fun (f : ι ->ᵇᵃ[I₀] M) x => f x
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : Injective fun (f : ι ->ᵇᵃ[I₀] M) x => f x :=
  DFunLike.coe_injective

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : ι ->ᵇᵃ[I₀] M}
  statement: (f : Box ι -> M) = g ↔ f = g
  proof: DFunLike.coe_fn_eq

@[ext]

中文:
定理 coe_inj
  条件: {f g : ι ->ᵇᵃ[I₀] M}
  结论: (f : Box ι -> M) = g ↔ f = g
  证明: DFunLike.coe_fn_eq

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_inj {f g : ι ->ᵇᵃ[I₀] M} : (f : Box ι -> M) = g ↔ f = g := DFunLike.coe_fn_eq

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : ι ->ᵇᵃ[I₀] M} (h : forall J, f J = g J)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : ι ->ᵇᵃ[I₀] M} (h : 对任意 J, f J = g J)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : ι ->ᵇᵃ[I₀] M} (h : forall J, f J = g J) : f = g :=
  DFunLike.ext _ _ h

/--
theorem `sum_partition_boxes` / 定理 `sum_partition_boxes`

English:
theorem sum_partition_boxes
  statement: (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I}
  proof: f.sum_partition_boxes' I hI π h

中文:
定理 sum_partition_boxes
  结论: (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : 预分拆 I}
  证明: f.sum_partition_boxes' I hI π h

Depends on / 依赖: f.sum_partition_boxes, sum_partition_boxes
-/
theorem sum_partition_boxes (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π : Prepartition I}
    (h : π.IsPartition) : ∑ J in π.boxes, f J = f I :=
  f.sum_partition_boxes' I hI π h

/-! ### Additive monoid structure -/

@[simps -fullyApplied]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ι ->ᵇᵃ[I₀] M)
  body: ⟨⟨0, fun _ _ _ _ => sum_const_zero⟩⟩

中文:
实例 :
  签名: 零 (ι ->ᵇᵃ[I₀] M)
  定义体: ⟨⟨0, fun _ _ _ _ => sum_const_zero⟩⟩

Depends on / 依赖: sum_const_zero
-/
instance : Zero (ι ->ᵇᵃ[I₀] M) :=
  ⟨⟨0, fun _ _ _ _ => sum_const_zero⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ι ->ᵇᵃ[I₀] M)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (ι ->ᵇᵃ[I₀] M)
  定义体: ⟨0⟩
-/
instance : Inhabited (ι ->ᵇᵃ[I₀] M) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (ι ->ᵇᵃ[I₀] M)
  body: ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

中文:
实例 :
  签名: 加法 (ι ->ᵇᵃ[I₀] M)
  定义体: ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

Depends on / 依赖: Pi.add_apply, add_apply, sum_add_distrib, sum_partition_boxes
-/
instance : Add (ι ->ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance {R} [Monoid R] [DistribMulAction R M] : SMul R (ι ->ᵇᵃ[I₀] M) :=
  ⟨fun r f =>
    ⟨r • (f : Box ι -> M), fun I hI π hπ => by
      simp only [Pi.smul_apply, ← smul_sum, sum_partition_boxes _ hI hπ]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (ι ->ᵇᵃ[I₀] M)
  body: Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]

中文:
实例 :
  签名: 加法交换幺半群 (ι ->ᵇᵃ[I₀] M)
  定义体: Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]

Depends on / 依赖: Function, Function.Injective.addCommMonoid, Injective, addCommMonoid, coe_injective
-/
instance : AddCommMonoid (ι ->ᵇᵃ[I₀] M) :=
  Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]
/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι)
  statement: (f + g) J = f J + g J
  proof: rfl

@[simp]

中文:
引理 add_apply
  条件: (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι)
  结论: (f + g) J = f J + g J
  证明: rfl

@[simp]
-/
lemma add_apply (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (f + g) J = f J + g J := rfl

@[simp]
/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  statement: {R : Type*} [Monoid R] [DistribMulAction R M]
  proof: rfl

中文:
引理 smul_apply
  结论: {R : 类型} [幺半群 R] [分配乘法作用 R M]
  证明: rfl
-/
lemma smul_apply {R : Type*} [Monoid R] [DistribMulAction R M]
    (c : R) (f : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (c • f) J = c • (f J) := rfl

/-! ### Constructions and combinators -/

@[simp]
/--
theorem `map_split_add` / 定理 `map_split_add`

English:
theorem map_split_add
  given: (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) (i : ι) (x : Real)
  proof: by
  rw [← f.sum_partition_boxes hI (isPartitionSplit I i x)]; rw [sum_split_boxes]

中文:
定理 map_split_add
  条件: (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) (i : ι) (x : 实数)
  证明: by
  rw [← f.sum_partition_boxes hI (isPartitionSplit I i x)]; rw [sum_split_boxes]

Depends on / 依赖: f.sum_partition_boxes, isPartitionSplit, sum_partition_boxes, sum_split_boxes
-/
theorem map_split_add (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) (i : ι) (x : Real) :
    (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I := by
  rw [← f.sum_partition_boxes hI (isPartitionSplit I i x)]; rw [sum_split_boxes]

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : ι ->ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I <= I₀)
  body: ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩

中文:
定义 restrict
  签名: (f : ι ->ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I <= I₀)
  定义体: ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩

Depends on / 依赖: hJ.trans
-/
def restrict (f : ι ->ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I <= I₀) : ι ->ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩

/--
Definition of `ofMapSplitAdd` / `ofMapSplitAdd` 的定义

English:
definition ofMapSplitAdd
  signature: [Finite ι] (f : Box ι -> M) (I₀ : WithTop (Box ι))
  body: by
  classical
  refine ⟨f, ?_⟩
  replace hf (I : Box ι) (hI : ↑I <= I₀) (s) : ∑ J in (splitMany I s).boxes, f J = f I := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ihs =>
      rw [splitMany_insert]; rw [inf_split]; rw [← ihs]; rw [biUnion_boxes]; rw [sum_biUnion_boxes]
      refine Finset.sum_congr rfl fun J' hJ' => ?_
      by_cases h : a.2 in Ioo (J'.lower a.1) (J'.upper a.1)
      · rw [sum_split_boxes]
        exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
      · rw [split_of_notMem_Ioo h, top_boxes, Finset.sum_singleton]
  intro I hI π hπ
  have Hle : forall J in π, ↑J <= I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_splitMany_le with ⟨s, hs⟩
  rw [← hf _ hI]; rw [← inf_of_le_right hs]; rw [inf_splitMany]; rw [biUnion_boxes]; rw [sum_biUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm

中文:
定义 ofMapSplitAdd
  签名: [有限 ι] (f : Box ι -> M) (I₀ : WithTop (Box ι))
  定义体: by
  classical
  refine ⟨f, ?_⟩
  replace hf (I : Box ι) (hI : ↑I <= I₀) (s) : ∑ J in (splitMany I s).boxes, f J = f I := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ihs =>
      rw [splitMany_insert]; rw [inf_split]; rw [← ihs]; rw [biUnion_boxes]; rw [sum_biUnion_boxes]
      refine Finset.sum_congr rfl fun J' hJ' => ?_
      by_cases h : a.2 in Ioo (J'.lower a.1) (J'.upper a.1)
      · rw [sum_split_boxes]
        exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
      · rw [split_of_notMem_Ioo h, top_boxes, Finset.sum_singleton]
  intro I hI π hπ
  have Hle : forall J in π, ↑J <= I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_splitMany_le with ⟨s, hs⟩
  rw [← hf _ hI]; rw [← inf_of_le_right hs]; rw [inf_splitMany]; rw [biUnion_boxes]; rw [sum_biUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_congr, WithTop, WithTop.coe_le_coe, biUnion_boxes, classical, coe_le_coe, induction_on, inf_split, insert, le_of_mem, replace, splitMany, splitMany_insert, split_of_not, sum_biUnion_boxes, sum_congr, sum_split_boxes
-/
def ofMapSplitAdd [Finite ι] (f : Box ι -> M) (I₀ : WithTop (Box ι))
    (hf : forall I : Box ι, ↑I <= I₀ -> forall {i x}, x in Ioo (I.lower i) (I.upper i) ->
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I) :
    ι ->ᵇᵃ[I₀] M := by
  classical
  refine ⟨f, ?_⟩
  replace hf (I : Box ι) (hI : ↑I <= I₀) (s) : ∑ J in (splitMany I s).boxes, f J = f I := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ihs =>
      rw [splitMany_insert]; rw [inf_split]; rw [← ihs]; rw [biUnion_boxes]; rw [sum_biUnion_boxes]
      refine Finset.sum_congr rfl fun J' hJ' => ?_
      by_cases h : a.2 in Ioo (J'.lower a.1) (J'.upper a.1)
      · rw [sum_split_boxes]
        exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
      · rw [split_of_notMem_Ioo h, top_boxes, Finset.sum_singleton]
  intro I hI π hπ
  have Hle : forall J in π, ↑J <= I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_splitMany_le with ⟨s, hs⟩
  rw [← hf _ hI]; rw [← inf_of_le_right hs]; rw [inf_splitMany]; rw [biUnion_boxes]; rw [sum_biUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps -fullyApplied]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : ι ->ᵇᵃ[I₀] M) (g : M ->+ N)
  body: g ∘ f
  sum_partition_boxes' I hI π hπ := by simp_rw [comp, ← map_sum, f.sum_partition_boxes hI hπ]

中文:
定义 map
  签名: (f : ι ->ᵇᵃ[I₀] M) (g : M ->+ N)
  定义体: g ∘ f
  sum_partition_boxes' I hI π hπ := by simp_rw [comp, ← map_sum, f.sum_partition_boxes hI hπ]
-/
def map (f : ι ->ᵇᵃ[I₀] M) (g : M ->+ N) : ι ->ᵇᵃ[I₀] N where
  toFun := g ∘ f
  sum_partition_boxes' I hI π hπ := by simp_rw [comp, ← map_sum, f.sum_partition_boxes hI hπ]

/--
theorem `sum_boxes_congr` / 定理 `sum_boxes_congr`

English:
theorem sum_boxes_congr
  statement: [Finite ι] (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π₁ π₂ : Prepartition I}
  proof: by
  rcases exists_splitMany_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with
    ⟨s, hs⟩
  simp only [inf_splitMany] at hs
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩; clear hs
  rw [h] at h₁
  calc
    ∑ J in π₁.boxes, f J = ∑ J in π₁.boxes, ∑ J' in (splitMany J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ => (f.sum_partition_boxes ?_ (isPartition_splitMany _ _)).symm
    _ = ∑ J in (π₁.biUnion fun J => splitMany J s).boxes, f J := (sum_biUnion_boxes _ _ _).symm
    _ = ∑ J in (π₂.biUnion fun J => splitMany J s).boxes, f J := by rw [h₁, h₂]
    _ = ∑ J in π₂.boxes, ∑ J' in (splitMany J s).boxes, f J' := sum_biUnion_boxes _ _ _
    _ = ∑ J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes ?_ (isPartition_splitMany _ _)
  exacts [(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI,
    (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]

中文:
定理 sum_boxes_congr
  结论: [有限 ι] (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π₁ π₂ : 预分拆 I}
  证明: by
  rcases exists_splitMany_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with
    ⟨s, hs⟩
  simp only [inf_splitMany] at hs
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩; clear hs
  rw [h] at h₁
  calc
    ∑ J in π₁.boxes, f J = ∑ J in π₁.boxes, ∑ J' in (splitMany J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ => (f.sum_partition_boxes ?_ (isPartition_splitMany _ _)).symm
    _ = ∑ J in (π₁.biUnion fun J => splitMany J s).boxes, f J := (sum_biUnion_boxes _ _ _).symm
    _ = ∑ J in (π₂.biUnion fun J => splitMany J s).boxes, f J := by rw [h₁, h₂]
    _ = ∑ J in π₂.boxes, ∑ J' in (splitMany J s).boxes, f J' := sum_biUnion_boxes _ _ _
    _ = ∑ J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes ?_ (isPartition_splitMany _ _)
  exacts [(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI,
    (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]

Depends on / 依赖: Finset, Finset.sum_congr, Or.inl, Or.inr, biUnion, exists_splitMany_inf_eq_filter_of_finite, f.sum_partition_boxes, finite_singleton, inf_splitMany, insert, isPartition_splitMany, splitMany, sum_biUnion_boxes, sum_congr, sum_partition_boxes
-/
theorem sum_boxes_congr [Finite ι] (f : ι ->ᵇᵃ[I₀] M) (hI : ↑I <= I₀) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : ∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J := by
  rcases exists_splitMany_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with
    ⟨s, hs⟩
  simp only [inf_splitMany] at hs
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩; clear hs
  rw [h] at h₁
  calc
    ∑ J in π₁.boxes, f J = ∑ J in π₁.boxes, ∑ J' in (splitMany J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ => (f.sum_partition_boxes ?_ (isPartition_splitMany _ _)).symm
    _ = ∑ J in (π₁.biUnion fun J => splitMany J s).boxes, f J := (sum_biUnion_boxes _ _ _).symm
    _ = ∑ J in (π₂.biUnion fun J => splitMany J s).boxes, f J := by rw [h₁, h₂]
    _ = ∑ J in π₂.boxes, ∑ J' in (splitMany J s).boxes, f J' := sum_biUnion_boxes _ _ _
    _ = ∑ J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes ?_ (isPartition_splitMany _ _)
  exacts [(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI,
    (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]

section AddCommGroup

/-! ### Additive group structure -/

variable {M : Type*} [AddCommGroup M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (ι ->ᵇᵃ[I₀] M)
  body: ⟨fun f =>
    ⟨-(f : Box ι -> M), fun I hI π hπ => by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, sum_partition_boxes _ hI hπ]⟩⟩

中文:
实例 :
  签名: 取负 (ι ->ᵇᵃ[I₀] M)
  定义体: ⟨fun f =>
    ⟨-(f : Box ι -> M), fun I hI π hπ => by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, sum_partition_boxes _ hI hπ]⟩⟩

Depends on / 依赖: Finset, Finset.sum_neg_distrib, Pi.neg_apply, neg_apply, sum_neg_distrib, sum_partition_boxes
-/
instance : Neg (ι ->ᵇᵃ[I₀] M) :=
  ⟨fun f =>
    ⟨-(f : Box ι -> M), fun I hI π hπ => by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, sum_partition_boxes _ hI hπ]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (ι ->ᵇᵃ[I₀] M)
  body: ⟨fun f g =>
    ⟨(f : Box ι -> M) - g, fun I hI π hπ => by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_partition_boxes _ hI hπ]⟩⟩

中文:
实例 :
  签名: 减法 (ι ->ᵇᵃ[I₀] M)
  定义体: ⟨fun f g =>
    ⟨(f : Box ι -> M) - g, fun I hI π hπ => by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_partition_boxes _ hI hπ]⟩⟩

Depends on / 依赖: Finset, Finset.sum_sub_distrib, Pi.sub_apply, sub_apply, sum_partition_boxes, sum_sub_distrib
-/
instance : Sub (ι ->ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
    ⟨(f : Box ι -> M) - g, fun I hI π hπ => by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_partition_boxes _ hI hπ]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (ι ->ᵇᵃ[I₀] M)
  body: Function.Injective.addCommGroup _ DFunLike.coe_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp]

中文:
实例 :
  签名: 加法交换群 (ι ->ᵇᵃ[I₀] M)
  定义体: Function.Injective.addCommGroup _ DFunLike.coe_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.Injective.addCommGroup, Injective, addCommGroup, coe_injective
-/
instance : AddCommGroup (ι ->ᵇᵃ[I₀] M) :=
  Function.Injective.addCommGroup _ DFunLike.coe_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp]
/--
lemma `neg_apply` / 引理 `neg_apply`

English:
lemma neg_apply
  given: (f : ι ->ᵇᵃ[I₀] M) (J : Box ι)
  statement: (-f) J = -(f J)
  proof: rfl

@[simp]

中文:
引理 neg_apply
  条件: (f : ι ->ᵇᵃ[I₀] M) (J : Box ι)
  结论: (-f) J = -(f J)
  证明: rfl

@[simp]
-/
lemma neg_apply (f : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (-f) J = -(f J) := rfl

@[simp]
/--
lemma `sub_apply` / 引理 `sub_apply`

English:
lemma sub_apply
  given: (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι)
  statement: (f - g) J = f J - g J
  proof: rfl

中文:
引理 sub_apply
  条件: (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι)
  结论: (f - g) J = f J - g J
  证明: rfl
-/
lemma sub_apply (f g : ι ->ᵇᵃ[I₀] M) (J : Box ι) : (f - g) J = f J - g J := rfl

end AddCommGroup

section ToSMul

/-! ### Scalar multiplication on a normed space -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
Definition of `toSMul` / `toSMul` 的定义

English:
definition toSMul
  signature: (f : ι ->ᵇᵃ[I₀] Real)
  body: f.map (ContinuousLinearMap.lsmul Real Real).toLinearMap.toAddMonoidHom

@[simp]

中文:
定义 toSMul
  签名: (f : ι ->ᵇᵃ[I₀] 实数)
  定义体: f.map (ContinuousLinearMap.lsmul Real Real).toLinearMap.toAddMonoidHom

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, f.map, toAddMonoidHom, toLinearMap, toLinearMap.toAddMonoidHom
-/
def toSMul (f : ι ->ᵇᵃ[I₀] Real) : ι ->ᵇᵃ[I₀] E ->L[Real] E :=
  f.map (ContinuousLinearMap.lsmul Real Real).toLinearMap.toAddMonoidHom

@[simp]
/--
theorem `toSMul_apply` / 定理 `toSMul_apply`

English:
theorem toSMul_apply
  given: (f : ι ->ᵇᵃ[I₀] Real) (I : Box ι) (x : E)
  statement: f.toSMul I x = f I • x
  proof: rfl

中文:
定理 toSMul_apply
  条件: (f : ι ->ᵇᵃ[I₀] 实数) (I : Box ι) (x : E)
  结论: f.toSMul I x = f I • x
  证明: rfl
-/
theorem toSMul_apply (f : ι ->ᵇᵃ[I₀] Real) (I : Box ι) (x : E) : f.toSMul I x = f I • x := rfl

end ToSMul

/-! ### Difference along an axis: `upper − lower` over faces -/

/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : Box (Fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `fun J ↦ f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes
of `I₀`. -/
@[simps!]
/--
Definition of `upperSubLower.` / `upperSubLower.` 的定义

English:
definition upperSubLower.{u}
  signature: {G : Type u} [AddCommGroup G] (I₀ : Box (Fin (n + 1))) (i : Fin (n + 1))
  body: ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j x
      rw [WithTop.coe_le_coe] at hJ
      refine i.succAboveCases (fun hx => ?_) (fun j hx => ?_) j
      · simp only [Box.splitLower_def hx, Box.splitUpper_def hx, update_self, ← WithBot.some_eq_coe,
          Option.elim', Box.face, Function.comp_def, update_of_ne (Fin.succAbove_ne _ _)]
        abel
      · have : (J.face i : WithTop (Box (Fin n))) <= I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc]; rw [@Box.Icc_eq_pi _ I₀] at hJ
        rw [hf _ (hJ J.upper_mem_Icc _ trivial)]; rw [hf _ (hJ J.lower_mem_Icc _ trivial)]; rw [← (fb _).map_split_add this j x]; rw [← (fb _).map_split_add this j x]
        have hx' : x in Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Box.splitLower_def hx',
          Box.splitUpper_def hx', ← WithBot.some_eq_coe, Option.elim', Box.face_mk,
          update_of_ne (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ (Fin.strictMono_succAbove i).injective j x, ← hf]
        simp only [Box.face])

中文:
定义 upperSubLower.{u}
  签名: {G : 类型u} [加法交换群 G] (I₀ : Box (有限集 (n + 1))) (i : 有限集 (n + 1))
  定义体: ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j x
      rw [WithTop.coe_le_coe] at hJ
      refine i.succAboveCases (fun hx => ?_) (fun j hx => ?_) j
      · simp only [Box.splitLower_def hx, Box.splitUpper_def hx, update_self, ← WithBot.some_eq_coe,
          Option.elim', Box.face, Function.comp_def, update_of_ne (Fin.succAbove_ne _ _)]
        abel
      · have : (J.face i : WithTop (Box (Fin n))) <= I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc]; rw [@Box.Icc_eq_pi _ I₀] at hJ
        rw [hf _ (hJ J.upper_mem_Icc _ trivial)]; rw [hf _ (hJ J.lower_mem_Icc _ trivial)]; rw [← (fb _).map_split_add this j x]; rw [← (fb _).map_split_add this j x]
        have hx' : x in Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Box.splitLower_def hx',
          Box.splitUpper_def hx', ← WithBot.some_eq_coe, Option.elim', Box.face_mk,
          update_of_ne (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ (Fin.strictMono_succAbove i).injective j x, ← hf]
        simp only [Box.face])

Depends on / 依赖: Box.face, Box.splitLower_def, Box.splitUpper_def, Fin.succAbove_ne, Function, Function.comp_def, J.face, J.lower, J.upper, Option.elim, WithBot, WithBot.some_eq_coe, WithTop, WithTop.coe_le_coe, coe_le_coe, comp_def, face_mono, i.succAboveCases, le_iff_Icc, ofMapSplitAdd
-/
def upperSubLower.{u} {G : Type u} [AddCommGroup G] (I₀ : Box (Fin (n + 1))) (i : Fin (n + 1))
    (f : Real -> Box (Fin n) -> G) (fb : Icc (I₀.lower i) (I₀.upper i) -> Fin n ->ᵇᵃ[I₀.face i] G)
    (hf : forall (x) (hx : x in Icc (I₀.lower i) (I₀.upper i)) (J), f x J = fb ⟨x, hx⟩ J) :
    Fin (n + 1) ->ᵇᵃ[I₀] G :=
  ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j x
      rw [WithTop.coe_le_coe] at hJ
      refine i.succAboveCases (fun hx => ?_) (fun j hx => ?_) j
      · simp only [Box.splitLower_def hx, Box.splitUpper_def hx, update_self, ← WithBot.some_eq_coe,
          Option.elim', Box.face, Function.comp_def, update_of_ne (Fin.succAbove_ne _ _)]
        abel
      · have : (J.face i : WithTop (Box (Fin n))) <= I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc]; rw [@Box.Icc_eq_pi _ I₀] at hJ
        rw [hf _ (hJ J.upper_mem_Icc _ trivial)]; rw [hf _ (hJ J.lower_mem_Icc _ trivial)]; rw [← (fb _).map_split_add this j x]; rw [← (fb _).map_split_add this j x]
        have hx' : x in Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Box.splitLower_def hx',
          Box.splitUpper_def hx', ← WithBot.some_eq_coe, Option.elim', Box.face_mk,
          update_of_ne (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ (Fin.strictMono_succAbove i).injective j x, ← hf]
        simp only [Box.face])

end BoxAdditiveMap

end BoxIntegral
