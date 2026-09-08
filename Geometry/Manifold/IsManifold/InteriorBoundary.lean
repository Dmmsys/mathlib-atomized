/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Ben Eltschig
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Notation

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Interior and boundary of a manifold

Define the interior and boundary of a manifold.

## Main definitions
- **IsInteriorPoint x**: `x ∈ M` is an interior point if, with `φ` being the preferred chart at `x`,
  `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `x ∈ M` is a boundary point if `(extChartAt I x) x ∈ frontier (range I)`.
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `ModelWithCorners.univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `ModelWithCorners.interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- `BoundarylessManifold.isInteriorPoint`: if `M` is boundaryless, every point is an interior point
- `ModelWithCorners.Boundaryless.boundary_eq_empty` and `of_boundary_eq_empty`:
  `M` is boundaryless if and only if its boundary is empty

- `isInteriorPoint_iff_of_mem_atlas`: a point is an interior point iff any given chart around it
  sends it to the interior of the model; that is, the notion of interior is independent of choices
  of charts
- `ModelWithCorners.isOpen_interior`, `ModelWithCorners.isClosed_boundary`: the interior is open and
  and the boundary is closed. This is currently only proven for C¹ manifolds.

- `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`: differentiable maps with surjective
  differential send interior points to interior points
- `IsLocalDiffeomorphAt.isInteriorPoint_iff` etc.: local diffeomorphisms preserve both the boundary
  and interior

- `ModelWithCorners.interior_open`: the interior of `u : Opens M` is the preimage of the interior
  of `M` under the inclusion
- `ModelWithCorners.boundary_open`: the boundary of `u : Opens M` is the preimage of the boundary
  of `M` under the inclusion
- `ModelWithCorners.BoundarylessManifold.open`: if `M` is boundaryless, so is `u : Opens M`

- `ModelWithCorners.interior_prod`: the interior of `M × N` is the product of the interiors
  of `M` and `N`.
- `ModelWithCorners.boundary_prod`: the boundary of `M × N` is `∂M × N ∪ (M × ∂N)`.
- `ModelWithCorners.BoundarylessManifold.prod`: if `M` and `N` are boundaryless, so is `M × N`

- `ModelWithCorners.interior_disjointUnion`: the interior of a disjoint union `M ⊔ M'`
  is the union of the interior of `M` and `M'`
- `ModelWithCorners.boundary_disjointUnion`: the boundary of a disjoint union `M ⊔ M'`
  is the union of the boundaries of `M` and `M'`
- `ModelWithCorners.boundaryless_disjointUnion`: if `M` and `M'` are boundaryless,
  so is their disjoint union `M ⊔ M'`

## Tags
manifold, interior, boundary

## TODO
- the interior of `M` is dense, the boundary nowhere dense
- the interior of `M` is a boundaryless manifold
- `boundary M` is a submanifold (possibly with boundary and corners):
  follows from the corresponding statement for the model with corners `I`;
  this requires a definition of submanifolds
- if `M` is finite-dimensional, its boundary has measure zero
- generalise lemmas about C¹ manifolds with boundary to also hold for finite-dimensional topological
  manifolds; this will require e.g. the homology of spheres.
- submersions send interior points to interior points. This should be an easy consequence of
  `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv` once submersions are defined.

-/

@[expose] public section

open Set Function
open scoped Topology Manifold

-- Let `M` be a manifold with corners over the pair `(E, H)`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

variable (I) in
/-- `p ∈ M` is an interior point of a manifold `M` if and only if its image in the extended chart
lies in the interior of the model space. -/
/-
**ModelWithCorners.IsInteriorPoint** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：IsInteriorPoint (x : M)
参数：x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p ∈ M` is an interior point of a manifold `M` if and only if its image in the e
xtended chart
lies in the interior of the model space.
-/
def IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (range I)

variable (I) in
/-- `p ∈ M` is a boundary point of a manifold `M` if and only if its image in the extended chart
lies on the boundary of the model space. -/
/-
**ModelWithCorners.IsBoundaryPoint** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：IsBoundaryPoint (x : M)
参数：x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p ∈ M` is a boundary point of a manifold `M` if and only if its image in the ex
tended chart
lies on the boundary of the model space.
-/
def IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

variable (M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
/-
**ModelWithCorners.interior** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     {I : ModelWithCorners 𝕜 E H} → (M : Type u_4) → [inst : TopologicalSpace M]
 → [ChartedSpace H M] → Set M
参数：M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **interior** of a manifold `M` is the set of its interior points.
-/
protected def interior : Set M := { x : M | I.IsInteriorPoint x }
/-
**ModelWithCorners.isInteriorPoint_iff** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorne
rs`。
形式化陈述：isInteriorPoint_iff {x : M} : I.IsInteriorPoint x ↔ extChartAt I x x in in
terior (extChartAt I x).target
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OpenPartialHomeomorph.mem_interior_extend_target`：mem_interior_extend_ta
rget {y : H} (hy : y in f.target) (hy' : I y in interior (range I)) : I y in int
erior (f.extend I).target
· 使用定理 `mem_chart_target`：mem_chart_target (x : M) : chartAt H x x in (chartAt H
 x).target
· 使用引理 `OpenPartialHomeomorph.interior_extend_target_subset_interior_range`：inte
rior_extend_target_subset_interior_range : interior (f.extend I).target subseteq
 interior (range I)
-/
lemma isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (extChartAt I x).target :=
  ⟨fun h ↦ (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h,
    fun h ↦ OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

variable (M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
/-
**ModelWithCorners.boundary** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     {I : ModelWithCorners 𝕜 E H} → (M : Type u_4) → [inst : TopologicalSpace M]
 → [ChartedSpace H M] → Set M
参数：M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **boundary** of a manifold `M` is the set of its boundary points.
-/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }
/-
**ModelWithCorners.isBoundaryPoint_iff** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorne
rs`。
形式化陈述：isBoundaryPoint_iff {x : M} : I.IsBoundaryPoint x ↔ extChartAt I x x in fr
ontier (range I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isBoundaryPoint_iff {x : M} : I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) :=
  Iff.rfl

/-- Every point is either an interior or a boundary point. -/
/-
**ModelWithCorners.isInteriorPoint_or_isBoundaryPoint** 是 Mathlib 中的一个引理，位于命名空间 
`ModelWithCorners`。
形式化陈述：isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBou
ndaryPoint x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.IsInteriorPoint.eq_1`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `ModelWithCorners.isBoundaryPoint_iff`：isBoundaryPoint_iff {x : M} : I.Is
BoundaryPoint x ↔ extChartAt I x x in frontier (range I)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_sdiff_interior`：closure_sdiff_interior (s : Set X) : closure s \
 interior s = frontier s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `ModelWithCorners.isClosed_range`：isClosed_range : IsClosed (range I)
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
Every point is either an interior or a boundary point.
-/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  rw [IsInteriorPoint, or_iff_not_imp_left, I.isBoundaryPoint_iff, ← closure_sdiff_interior,
    I.isClosed_range.closure_eq, mem_sdiff]
  exact fun h ↦ ⟨mem_range_self _, h⟩

/-- A manifold decomposes into interior and boundary. -/
/-
**ModelWithCorners.interior_union_boundary_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Mo
delWithCorners`。
形式化陈述：interior_union_boundary_eq_univ : (I.interior M) union (I.boundary M) = (u
niv : Set M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用引理 `ModelWithCorners.isInteriorPoint_or_isBoundaryPoint`：isInteriorPoint_or_
isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x

--- 原说明 ---
A manifold decomposes into interior and boundary.
-/
lemma interior_union_boundary_eq_univ : (I.interior M) ∪ (I.boundary M) = (univ : Set M) :=
  eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of a manifold `M` are disjoint. -/
/-
**ModelWithCorners.disjoint_interior_boundary** 是 Mathlib 中的一个引理，位于命名空间 `ModelWi
thCorners`。
形式化陈述：disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用引理 `disjoint_interior_frontier`：disjoint_interior_frontier : Disjoint (inter
ior s) (frontier s)
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b

--- 原说明 ---
The interior and boundary of a manifold `M` are disjoint.
-/
lemma disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M) := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier, mem_inter_iff]
  exact ⟨h1, h2⟩
/-
**ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint** 是 Mathlib 中的一个引理，位于
命名空间 `ModelWithCorners`。
形式化陈述：isInteriorPoint_iff_not_isBoundaryPoint (x : M) : I.IsInteriorPoint x ↔ ¬I
.IsBoundaryPoint x
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用引理 `disjoint_interior_frontier`：disjoint_interior_frontier : Disjoint (inter
ior s) (frontier s)
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ModelWithCorners.isInteriorPoint_or_isBoundaryPoint`：isInteriorPoint_or_
isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x
-/
lemma isInteriorPoint_iff_not_isBoundaryPoint (x : M) :
    I.IsInteriorPoint x ↔ ¬I.IsBoundaryPoint x := by
  refine ⟨?_,
    by simpa only [or_iff_not_imp_right] using isInteriorPoint_or_isBoundaryPoint x (I := I)⟩
  by_contra! h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier, mem_inter_iff]
  exact h
/-
**ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint** 是 Mathlib 中的一个引理，位于
命名空间 `ModelWithCorners`。
形式化陈述：isBoundaryPoint_iff_not_isInteriorPoint (x : M) : I.IsBoundaryPoint x ↔ ¬I
.IsInteriorPoint x
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isBoundaryPoint_iff_not_isInteriorPoint (x : M) :
    I.IsBoundaryPoint x ↔ ¬I.IsInteriorPoint x := by
  simp [isInteriorPoint_iff_not_isBoundaryPoint]

/-- The boundary is the complement of the interior. -/
/-
**ModelWithCorners.compl_interior** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：compl_interior : (I.interior M)ᶜ = I.boundary M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_unique`：compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用引理 `ModelWithCorners.disjoint_interior_boundary`：disjoint_interior_boundary 
: Disjoint (I.interior M) (I.boundary M)
· 使用引理 `ModelWithCorners.interior_union_boundary_eq_univ`：interior_union_boundar
y_eq_univ : (I.interior M) union (I.boundary M) = (univ : Set M)

--- 原说明 ---
The boundary is the complement of the interior.
-/
lemma compl_interior : (I.interior M)ᶜ = I.boundary M := by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

/-- The interior is the complement of the boundary. -/
/-
**ModelWithCorners.compl_boundary** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：compl_boundary : (I.boundary M)ᶜ = I.interior M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.compl_interior`：compl_interior : (I.interior M)ᶜ = I.bo
undary M
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
The interior is the complement of the boundary.
-/
lemma compl_boundary : (I.boundary M)ᶜ = I.interior M := by
  rw [← compl_interior, compl_compl]
/-
**ModelWithCorners._root_.range_mem_nhds_isInteriorPoint** 是 Mathlib 中的一个引理，位于命名
空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.range_mem_nhds_isInteriorPoint {x : M} (h : I.IsInteriorPoint x) :
    range I ∈ 𝓝 (extChartAt I x x) := by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

/-- Type class for manifold without boundary. This differs from `ModelWithCorners.Boundaryless`,
which states that the `ModelWithCorners` maps to the whole model vector space. -/
/-
**ModelWithCorners._root_.BoundarylessManifold** 是 Mathlib 中的一个类，位于命名空间 `ModelWi
thCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for manifold without boundary. This differs from `ModelWithCorners.Bo
undaryless`,
which states that the `ModelWithCorners` maps to the whole model vector space.
-/
class _root_.BoundarylessManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  isInteriorPoint' : ∀ x : M, IsInteriorPoint I x

section Boundaryless
variable [I.Boundaryless]

/-- Boundaryless `ModelWithCorners` implies boundaryless manifold. -/
/-
**ModelWithCorners.** 是 Mathlib 中的一个实例，位于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Boundaryless `ModelWithCorners` implies boundaryless manifold.
-/
instance : BoundarylessManifold I M where
  isInteriorPoint' x := by
    let r := ((chartAt H x).isOpen_extend_target (I := I)).interior_eq
    have : extChartAt I x = (chartAt H x).extend I := rfl
    rw [← this] at r
    rw [isInteriorPoint_iff, r]
    exact PartialEquiv.map_source _ (mem_extChartAt_source _)

end Boundaryless

section BoundarylessManifold

/-- The empty manifold is boundaryless. -/
/-
**ModelWithCorners.BoundarylessManifold.of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Mode
lWithCorners.BoundarylessManifold`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] [IsEmpty M], BoundarylessManifold I M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False

--- 原说明 ---
The empty manifold is boundaryless.
-/
instance BoundarylessManifold.of_empty [IsEmpty M] : BoundarylessManifold I M where
  isInteriorPoint' x := (IsEmpty.false x).elim
/-
**ModelWithCorners._root_.BoundarylessManifold.isInteriorPoint** 是 Mathlib 中的一个引
理，位于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.BoundarylessManifold.isInteriorPoint {x : M} [BoundarylessManifold I M] :
    IsInteriorPoint I x := BoundarylessManifold.isInteriorPoint' x

/-- If `I` is boundaryless, `M` has full interior. -/
/-
**ModelWithCorners.interior_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`
。
形式化陈述：interior_eq_univ [BoundarylessManifold I M] : I.interior M = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `BoundarylessManifold.isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
If `I` is boundaryless, `M` has full interior.
-/
lemma interior_eq_univ [BoundarylessManifold I M] : I.interior M = univ :=
  eq_univ_of_forall fun _ => BoundarylessManifold.isInteriorPoint

/-- Boundaryless manifolds have empty boundary. -/
/-
**ModelWithCorners.Boundaryless.boundary_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Mod
elWithCorners.Boundaryless`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] [BoundarylessManifold I M], ModelWith
Corners.boundary M = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.compl_interior`：compl_interior : (I.interior M)ᶜ = I.bo
undary M
· 使用引理 `ModelWithCorners.interior_eq_univ`：interior_eq_univ [BoundarylessManifol
d I M] : I.interior M = univ
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ

--- 原说明 ---
Boundaryless manifolds have empty boundary.
-/
lemma Boundaryless.boundary_eq_empty [BoundarylessManifold I M] : I.boundary M = ∅ := by
  rw [← I.compl_interior, I.interior_eq_univ, compl_empty_iff]
/-
**ModelWithCorners.** 是 Mathlib 中的一个实例，位于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundarylessManifold I M] : IsEmpty (I.boundary M) :=
  isEmpty_coe_sort.mpr Boundaryless.boundary_eq_empty

/-- `M` is boundaryless if and only if its boundary is empty. -/
/-
**ModelWithCorners.Boundaryless.iff_boundary_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 
`ModelWithCorners.Boundaryless`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M], ModelWithCorners.boundary M = ∅ ↔ Bo
undarylessManifold I M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.compl_interior`：compl_interior : (I.interior M)ᶜ = I.bo
undary M
· 使用定理 `ModelWithCorners.Boundaryless.boundary_eq_empty`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
`M` is boundaryless if and only if its boundary is empty.
-/
lemma Boundaryless.iff_boundary_eq_empty : I.boundary M = ∅ ↔ BoundarylessManifold I M := by
  refine ⟨fun h ↦ { isInteriorPoint' := ?_ }, fun a ↦ boundary_eq_empty⟩
  intro x
  change x ∈ I.interior M
  rw [← compl_interior, compl_empty_iff] at h
  rw [h]
  trivial

/-- Manifolds with empty boundary are boundaryless. -/
/-
**ModelWithCorners.Boundaryless.of_boundary_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `
ModelWithCorners.Boundaryless`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M], ModelWithCorners.boundary M = ∅ → Bo
undarylessManifold I M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModelWithCorners.Boundaryless.iff_boundary_eq_empty`：∀ {𝕜 : Type u_1} [i
nst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] 
  [inst_2 : NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
Manifolds with empty boundary are boundaryless.
-/
lemma Boundaryless.of_boundary_eq_empty (h : I.boundary M = ∅) : BoundarylessManifold I M :=
  (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

end BoundarylessManifold

section ChartIndependence

/-- If a function `f : E → H` is differentiable at `x`, sends a neighbourhood `u` of `x` to a
closed convex set `s` with nonempty interior and has surjective differential at `x`, it must send
`x` to the interior of `s`. -/
/-
**ModelWithCorners._root_.DifferentiableAt.mem_interior_convex_of_surjective_fde
riv** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f : E → H` is differentiable at `x`, sends a neighbourhood `u` of
 `x` to a
closed convex set `s` with nonempty interior and has surjective differential at 
`x`, it must send
`x` to the interior of `s`.
-/
lemma _root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → H} {x : E} (hf : DifferentiableAt ℝ f x) {u : Set E} (hu : u ∈ 𝓝 x) {s : Set H}
    (hs : Convex ℝ s) (hs' : IsClosed s) (hs'' : (interior s).Nonempty) (hfus : Set.MapsTo f u s)
    (hfx : Function.Surjective (fderiv ℝ f x)) : f x ∈ interior s := by
  contrapose hfx
  have ⟨F, hF⟩ := geometric_hahn_banach_open_point hs.interior isOpen_interior hfx
  -- It suffices to show that `fderiv ℝ f x` sends everything to the kernel of `F`.
  suffices h : ∀ y, F (fderiv ℝ f x y) = 0 by
    have ⟨y, hy⟩ := hs''
    unfold Function.Surjective; push Not
    refine ⟨f x - y, fun z ↦ ne_of_apply_ne F ?_⟩
    rw [h z, F.map_sub]
    exact (sub_pos.2 <| hF _ hy).ne
  -- This follows from `F ∘ f` taking on a local maximum at `e.extend I x`.
  have hF' : MapsTo F s (Iic (F (f x))) := by
    rw [← hs'.closure_eq, ← closure_Iio, ← hs.closure_interior_eq_closure_of_nonempty_interior hs'']
    exact .closure hF F.continuous
  have hFφ : IsLocalMax (F ∘ f) x := Filter.eventually_of_mem hu fun y hy ↦ hF' <| hfus hy
  have h := hFφ.fderiv_eq_zero
  rw [fderiv_comp _ (by fun_prop) hf, ContinuousLinearMap.fderiv] at h
  exact DFunLike.congr_fun h

variable {n : WithTop ℕ∞} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H} {x : M}

/-- For any two charts `e`, `e'` around a point `x` in a C¹ manifold, if `e` maps `x` to the
interior of the model space, `e'` does too - in other words, the notion of interior points does not
depend on any choice of charts.

Note that in general, this is actually quite nontrivial; that is why are focusing only on C¹
manifolds here. For merely topological finite-dimensional manifolds the proof involves singular
homology, and for infinite-dimensional topological manifolds I don't even know if this lemma holds.
-/
/-
**ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas** 是 Mat
hlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：mem_interior_range_of_mem_interior_range_of_mem_atlas (hn : n != 0) (he : 
e in atlas H M) (he' : e' in atlas H M) (hex : x in e.source) (hex' : x in e'.so
urce) (hx : e.extend I x in interior (e.extend I).target) : e'.extend I x in int
erior (e'.extend I).target
参数：hn : n != 0；he : e in atlas H M；he' : e' in atlas H M；hex : x in e.source；hex
' : x in e'.source；hx : e.extend I x in interior (e.extend I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange`：contDiffOn_extendCoordCha
nge (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : ContDiffOn
 𝕜 n (I.extendCoordChange e e') (I.…
· 使用定理 `IsManifold.subset_maximalAtlas`：subset_maximalAtlas [IsManifold I n M] :
 atlas H M subseteq maximalAtlas I n M
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `OpenPartialHomeomorph.extend_preimage_mem_nhds`：extend_preimage_mem_nhds
 {x : M} (h : x in f.source) (ht : t in 𝓝 x) : (f.extend I).symm ⁻¹' t in 𝓝 (f.e
xtend I x)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiffOn.differentiableOn`：ContDiffOn.differentiableOn (h : ContDiffOn
 𝕜 n f s) (hn : n != 0) : DifferentiableOn 𝕜 f s
· 使用定理 `ContDiffOn.restrict_scalars`：ContDiffOn.restrict_scalars (h : ContDiffOn
 𝕜' n f s) : ContDiffOn 𝕜 n f s
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DifferentiableAt.mem_interior_convex_of_surjective_fderiv`：∀ {E : Type u
_5} {H : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [ins
t_2 : NormedAddCommGroup H]   [inst_3 : NormedS…
· 使用定理 `ModelWithCorners.convex_range`：convex_range [NormedSpace Real E] : Conve
x Real (range I)
· 使用定理 `ModelWithCorners.isClosed_range`：isClosed_range : IsClosed (range I)
· 使用定理 `ModelWithCorners.nonempty_interior`：nonempty_interior : (interior (range
 I)).Nonempty
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
For any two charts `e`, `e'` around a point `x` in a C¹ manifold, if `e` maps `x
` to the
interior of the model space, `e'` does too - in other words, the notion of inter
ior points does not
depend on any choice of charts.

Note that in general, this is actually quite nontrivial; that is why are focusin
g only on C¹
manifolds here. For merely topological finite-dimensional manifolds the proof in
volves singular
homology, and for infinite-dimensional topological manifolds I don't even know i
f this lemma holds.
-/
lemma mem_interior_range_of_mem_interior_range_of_mem_atlas (hn : n ≠ 0)
    (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  /- Since transition maps are diffeomorphisms, it suffices to show that if `e'` were to send `x`
  to the boundary of `range I`, the differential of the transition map `φ` from `e` to `e'` at `x`
  could not be surjective. -/
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (isInvertible_fderivWithin_extendCoordChange hn (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he') <| by simp [hex, hex']).surjective
  intro hφx'
  /- Reduce the situation to the real case, then apply
  `DifferentiableAt.mem_interior_convex_of_surjective_fderiv`. -/
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds <| hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- For any two charts `e`, `e'` around a point `x` in a C¹ manifold, `e` maps `x` to the interior
of the model space iff `e'` does. - in other words, the notion of interior points does not
depend on any choice of charts. -/
/-
**ModelWithCorners.mem_interior_range_iff_of_mem_atlas** 是 Mathlib 中的一个引理，位于命名空间
 `ModelWithCorners`。
形式化陈述：mem_interior_range_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (h
e' : e' in atlas H M) (hex : x in e.source) (hex' : x in e'.source) : e.extend I
 x in interior (e.extend I).target ↔ e'.extend I x in interior (e'.extend I).tar
get
参数：hn : n != 0；he : e in atlas H M；he' : e' in atlas H M；hex : x in e.source；hex
' : x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas`：
mem_interior_range_of_mem_interior_range_of_mem_atlas (hn : n != 0) (he : e in a
tlas H M) (he' : e' in atlas H M) (hex : x in e.source) (hex…

--- 原说明 ---
For any two charts `e`, `e'` around a point `x` in a C¹ manifold, `e` maps `x` t
o the interior
of the model space iff `e'` does. - in other words, the notion of interior point
s does not
depend on any choice of charts.
-/
lemma mem_interior_range_iff_of_mem_atlas (hn : n ≠ 0) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source) :
    e.extend I x ∈ interior (e.extend I).target ↔
    e'.extend I x ∈ interior (e'.extend I).target := by
  constructor <;> apply mem_interior_range_of_mem_interior_range_of_mem_atlas hn <;> assumption

/-- A point `x` in a C¹ manifold is an interior point if and only if it gets mapped to the interior
of the model space by any given chart - in other words, the notion of interior points does not
depend on any choice of charts. -/
/-
**ModelWithCorners.isInteriorPoint_iff_of_mem_atlas** 是 Mathlib 中的一个引理，位于命名空间 `M
odelWithCorners`。
形式化陈述：isInteriorPoint_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (hx :
 x in e.source) : I.IsInteriorPoint x ↔ e.extend I x in interior (e.extend I).ta
rget
参数：hn : n != 0；he : e in atlas H M；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isInteriorPoint_iff`：isInteriorPoint_iff {x : M} : I.Is
InteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target
· 使用引理 `ModelWithCorners.mem_interior_range_iff_of_mem_atlas`：mem_interior_range
_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (he' : e' in atlas H M) (h
ex : x in e.source) (hex' : x in e'.source…
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce

--- 原说明 ---
A point `x` in a C¹ manifold is an interior point if and only if it gets mapped 
to the interior
of the model space by any given chart - in other words, the notion of interior p
oints does not
depend on any choice of charts.
-/
lemma isInteriorPoint_iff_of_mem_atlas (hn : n ≠ 0) (he : e ∈ atlas H M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_atlas hn (chart_mem_atlas H x) he (mem_chart_source H x) hx

/-- A point `x` in a C¹ manifold is a boundary point if and only if it gets mapped to the boundary
of the model space by any given chart - in other words, the notion of boundary points does not
depend on any choice of charts.

Also see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`. -/
/-
**ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas** 是 Mathlib 中的一个引理，位于命名空间 `M
odelWithCorners`。
形式化陈述：isBoundaryPoint_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (hx :
 x in e.source) : I.IsBoundaryPoint x ↔ e.extend I x in frontier (e.extend I).ta
rget
参数：hn : n != 0；he : e in atlas H M；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint`：isInteriorPoin
t_iff_not_isBoundaryPoint (x : M) : I.IsInteriorPoint x ↔ ¬I.IsBoundaryPoint x
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`：isInteriorPoint_iff_o
f_mem_atlas (hn : n != 0) (he : e in atlas H M) (hx : x in e.source) : I.IsInter
iorPoint x ↔ e.extend I x in interior (…
· 使用引理 `mem_interior_iff_notMem_frontier`：mem_interior_iff_notMem_frontier {s : 
Set X} {x : X} (hx : x in s) : x in interior s ↔ x ∉ frontier s
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point `x` in a C¹ manifold is a boundary point if and only if it gets mapped t
o the boundary
of the model space by any given chart - in other words, the notion of boundary p
oints does not
depend on any choice of charts.

Also see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`.
-/
lemma isBoundaryPoint_iff_of_mem_atlas (hn : n ≠ 0) (he : e ∈ atlas H M) (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x ∈ frontier (e.extend I).target := by
  rw [← not_iff_not, ← I.isInteriorPoint_iff_not_isBoundaryPoint,
    I.isInteriorPoint_iff_of_mem_atlas hn he hx, mem_interior_iff_notMem_frontier]
  exact (e.extend I).mapsTo <| e.extend_source (I := I) ▸ hx

/-- The interior of any C¹ manifold is open.

This is currently only proven for C¹ manifolds, but holds at least for finite-dimensional
topological manifolds too; see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`. -/
/-
**ModelWithCorners.isOpen_interior** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M], 
  n ≠ 0 → IsOpen (ModelWithCorners.interior M)
参数：ModelWithCorners.interior M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`：isInteriorPoint_iff_o
f_mem_atlas (hn : n != 0) (he : e in atlas H M) (hx : x in e.source) : I.IsInter
iorPoint x ↔ e.extend I x in interior (…
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isOpen_extChartAt_preimage`：isOpen_extChartAt_preimage (x : M) {s : Set 
E} (hs : IsOpen s) : IsOpen ((chartAt H x).source inter extChartAt I x ⁻¹' s)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ModelWithCorners.isInteriorPoint_iff`：isInteriorPoint_iff {x : M} : I.Is
InteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target

--- 原说明 ---
The interior of any C¹ manifold is open.

This is currently only proven for C¹ manifolds, but holds at least for finite-di
mensional
topological manifolds too; see `ModelWithCorners.isInteriorPoint_iff_of_mem_atla
s`.
-/
protected lemma isOpen_interior (hn : n ≠ 0) : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ⟨_, ?_, isOpen_extChartAt_preimage (I := I) x
    isOpen_interior, mem_chart_source H x, isInteriorPoint_iff.1 hx⟩
  exact fun y hy ↦ (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).2 hy.2

/-- The boundary of any C¹ manifold is closed.

This is currently only proven for C¹ manifolds, but holds at least for finite-dimensional
topological manifolds too; see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`. -/
/-
**ModelWithCorners.isClosed_boundary** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M], 
  n ≠ 0 → IsClosed (ModelWithCorners.boundary M)
参数：ModelWithCorners.boundary M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.compl_interior`：compl_interior : (I.interior M)ᶜ = I.bo
undary M
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `ModelWithCorners.isOpen_interior`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…

--- 原说明 ---
The boundary of any C¹ manifold is closed.

This is currently only proven for C¹ manifolds, but holds at least for finite-di
mensional
topological manifolds too; see `ModelWithCorners.isInteriorPoint_iff_of_mem_atla
s`.
-/
protected lemma isClosed_boundary (hn : n ≠ 0) : IsClosed (I.boundary M) := by
  rw [← I.compl_interior, isClosed_compl_iff]
  exact I.isOpen_interior hn

end ChartIndependence

end ModelWithCorners

/-! Interior and boundary are preserved under (local) diffeomorphisms. -/
section Diffeomorph

open ModelWithCorners

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

/-- If a function `f` is differentiable at `x` with surjective `mfderiv I I' f x` and `x` is an
interior point with respect to `I`, `f x` must be an interior point with respect to `I'`. -/
/-
**MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv {f : M -> N} {x : 
M} (hf : MDiffAt f x) (hf' : Surjective (mfderiv% f x)) (hx : I.IsInteriorPoint 
x) : I'.IsInteriorPoint (f x)
参数：hf : MDiffAt f x；hf' : Surjective (mfderiv% f x)；hx : I.IsInteriorPoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt`：MDifferent
iableAt.differentiableWithinAt_writtenInExtChartAt {f : M -> M'} {x : M} (hf : M
DifferentiableAt I I' f x) : DifferentiableWithinA…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderiv_restrictScalars`：DifferentiableAt.fderiv_restric
tScalars (h : DifferentiableAt 𝕜' f x) : fderiv 𝕜 f x = (fderiv 𝕜' f x).restrict
Scalars 𝕜
· 使用定理 `ContinuousLinearMap.coe_restrictScalars'`：coe_restrictScalars' (f : M₁ -
>L[A] M₂) : ⇑(f.restrictScalars R) = f
· 使用定理 `fderivWithin_eq_fderiv`：fderivWithin_eq_fderiv [ContinuousAdd E] [Contin
uousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (hs : UniqueDif
fWithinAt 𝕜 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `DifferentiableAt.restrictScalars`：DifferentiableAt.restrictScalars (h : 
DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableAt.mem_interior_convex_of_surjective_fderiv`：∀ {E : Type u
_5} {H : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [ins
t_2 : NormedAddCommGroup H]   [inst_3 : NormedS…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `extChartAt_preimage_mem_nhds`：extChartAt_preimage_mem_nhds {x : M} (ht :
 t in 𝓝 x) : (extChartAt I x).symm ⁻¹' t in 𝓝 ((extChartAt I x) x)
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f` is differentiable at `x` with surjective `mfderiv I I' f x` an
d `x` is an
interior point with respect to `I`, `f x` must be an interior point with respect
 to `I'`.
-/
lemma MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv {f : M → N} {x : M}
    (hf : MDiffAt f x) (hf' : Surjective (mfderiv% f x))
    (hx : I.IsInteriorPoint x) : I'.IsInteriorPoint (f x) := by
  -- Since p-adic manifolds don't have boundary, WLOG `𝕜` is `ℝ` or `ℂ` and `E` is normed over `ℝ`.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let _ : NormedSpace ℝ E' := NormedSpace.restrictScalars ℝ 𝕜 E'
  -- Write everything in terms of extended charts around `x` and `f x`.
  simp only [mfderiv, hf] at hf'
  have hf'' := hf.differentiableWithinAt_writtenInExtChartAt.differentiableAt <| by
    simpa [← mem_interior_iff_mem_nhds] using! hx
  rw [fderivWithin_eq_fderiv (I.uniqueDiffOn _ <| by simp) hf''] at hf'
  /- Since `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x`
  over `𝕜`, it also is so over `ℝ`. -/
  replace hf' : Surjective (fderiv ℝ (writtenInExtChartAt I I' x f) (extChartAt I x x)) := by
    rwa [hf''.fderiv_restrictScalars (𝕜 := ℝ), ContinuousLinearMap.coe_restrictScalars']
  replace hf'' := hf''.restrictScalars ℝ
  /- The lemma is now essentially just `mem_interior_convex_of_surjective_fderiv`: because
  `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x` over `ℝ` and
  sends a neighbourhood of `x` (the region in which it could be written in the extended charts) to
  a closed convex set with nonempty interior (`I'.range`), it must send `x` to that interior. -/
  have := hf''.mem_interior_convex_of_surjective_fderiv (Filter.inter_mem ?_ ?_) I'.convex_range
    I'.isClosed_range I'.nonempty_interior (writtenInExtChartAt_mapsTo.mono_right ?_) hf'
  · simpa using! this
  · rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hx)]
    exact extChartAt_target_mem_nhdsWithin x
  · exact extChartAt_preimage_mem_nhds <| hf.continuousAt.preimage_mem_nhds <|
      extChartAt_source_mem_nhds _
  · exact extChartAt_target_subset_range _
/-
**IsLocalDiffeomorphAt.isInteriorPoint_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphAt.isInteriorPoint_iff (hn : n != 0) {f : M -> N} {x : M
} (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsInteriorPoint x ↔ I'.IsInteriorPo
int (f x)
参数：hn : n != 0；hf : IsLocalDiffeomorphAt I I' n f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`：MDifferentiable
At.isInteriorPoint_of_surjective_mfderiv {f : M -> N} {x : M} (hf : MDiffAt f x)
 (hf' : Surjective (mfderiv% f x)) (hx : I.Is…
· 使用引理 `IsLocalDiffeomorphAt.mdifferentiableAt`：IsLocalDiffeomorphAt.mdifferenti
ableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `ContinuousLinearEquiv.surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalDiffeomorphAt.localInverse_left_inv`：localInverse_left_inv (hf : 
IsLocalDiffeomorphAt I J n f x) {x' : M} (hx' : x' in hf.localInverse.target) : 
hf.localInverse (f x') = x'
· 使用引理 `IsLocalDiffeomorphAt.localInverse_mem_target`：localInverse_mem_target (h
f : IsLocalDiffeomorphAt I J n f x) : x in hf.localInverse.target
· 使用引理 `IsLocalDiffeomorphAt.localInverse_mdifferentiableAt`：localInverse_mdiffe
rentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) : MDiffAt hf.loc
alInverse (f x)
-/
lemma IsLocalDiffeomorphAt.isInteriorPoint_iff (hn : n ≠ 0) {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsInteriorPoint x ↔ I'.IsInteriorPoint (f x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (hf.mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).surjective
  · rw [← hf.localInverse_left_inv hf.localInverse_mem_target]
    refine (hf.localInverse_mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).symm.surjective
/-
**IsLocalDiffeomorphAt.isBoundaryPoint_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphAt.isBoundaryPoint_iff (hn : n != 0) {f : M -> N} {x : M
} (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsBoundaryPoint x ↔ I'.IsBoundaryPo
int (f x)
参数：hn : n != 0；hf : IsLocalDiffeomorphAt I I' n f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalDiffeomorphAt.isInteriorPoint_iff`：IsLocalDiffeomorphAt.isInterio
rPoint_iff (hn : n != 0) {f : M -> N} {x : M} (hf : IsLocalDiffeomorphAt I I' n 
f x) : I.IsInteriorPoint x ↔ I…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsLocalDiffeomorphAt.isBoundaryPoint_iff (hn : n ≠ 0) {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (f x) := by
  simp [isBoundaryPoint_iff_not_isInteriorPoint, hf.isInteriorPoint_iff hn]
/-
**IsLocalDiffeomorphOn.preimage_interior_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphOn.preimage_interior_inter (hn : n != 0) {f : M -> N} {s
 : Set M} (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.interior N inter s =
 I.interior M inter s
参数：hn : n != 0；hf : IsLocalDiffeomorphOn I I' n f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `IsLocalDiffeomorphAt.isInteriorPoint_iff`：IsLocalDiffeomorphAt.isInterio
rPoint_iff (hn : n != 0) {f : M -> N} {x : M} (hf : IsLocalDiffeomorphAt I I' n 
f x) : I.IsInteriorPoint x ↔ I…
-/
lemma IsLocalDiffeomorphOn.preimage_interior_inter (hn : n ≠ 0) {f : M → N} {s : Set M}
    (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.interior N ∩ s = I.interior M ∩ s := by
  ext x
  simpa using! fun hx ↦ ((hf ⟨x, hx⟩).isInteriorPoint_iff hn).symm
/-
**IsLocalDiffeomorphOn.preimage_boundary_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphOn.preimage_boundary_inter (hn : n != 0) {f : M -> N} {s
 : Set M} (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.boundary N inter s =
 I.boundary M inter s
参数：hn : n != 0；hf : IsLocalDiffeomorphOn I I' n f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `IsLocalDiffeomorphAt.isBoundaryPoint_iff`：IsLocalDiffeomorphAt.isBoundar
yPoint_iff (hn : n != 0) {f : M -> N} {x : M} (hf : IsLocalDiffeomorphAt I I' n 
f x) : I.IsBoundaryPoint x ↔ I…
-/
lemma IsLocalDiffeomorphOn.preimage_boundary_inter (hn : n ≠ 0) {f : M → N} {s : Set M}
    (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.boundary N ∩ s = I.boundary M ∩ s := by
  ext x
  simpa using! fun hx ↦ ((hf ⟨x, hx⟩).isBoundaryPoint_iff hn).symm
/-
**IsLocalDiffeomorph.preimage_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.preimage_interior (hn : n != 0) {f : M -> N} (hf : IsLo
calDiffeomorph I I' n f) : f ⁻¹' I'.interior N = I.interior M
参数：hn : n != 0；hf : IsLocalDiffeomorph I I' n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用引理 `IsLocalDiffeomorphOn.preimage_interior_inter`：IsLocalDiffeomorphOn.preim
age_interior_inter (hn : n != 0) {f : M -> N} {s : Set M} (hf : IsLocalDiffeomor
phOn I I' n f s) : f ⁻¹' I'.interi…
· 使用引理 `IsLocalDiffeomorph.isLocalDiffeomorphOn`：IsLocalDiffeomorph.isLocalDiffe
omorphOn {f : M -> N} (hf : IsLocalDiffeomorph I J n f) (s : Set M) : IsLocalDif
feomorphOn I J n f s
-/
lemma IsLocalDiffeomorph.preimage_interior (hn : n ≠ 0) {f : M → N}
    (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.interior N = I.interior M := by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_interior_inter hn
/-
**IsLocalDiffeomorph.preimage_boundary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.preimage_boundary (hn : n != 0) {f : M -> N} (hf : IsLo
calDiffeomorph I I' n f) : f ⁻¹' I'.boundary N = I.boundary M
参数：hn : n != 0；hf : IsLocalDiffeomorph I I' n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用引理 `IsLocalDiffeomorphOn.preimage_boundary_inter`：IsLocalDiffeomorphOn.preim
age_boundary_inter (hn : n != 0) {f : M -> N} {s : Set M} (hf : IsLocalDiffeomor
phOn I I' n f s) : f ⁻¹' I'.bounda…
· 使用引理 `IsLocalDiffeomorph.isLocalDiffeomorphOn`：IsLocalDiffeomorph.isLocalDiffe
omorphOn {f : M -> N} (hf : IsLocalDiffeomorph I J n f) (s : Set M) : IsLocalDif
feomorphOn I J n f s
-/
lemma IsLocalDiffeomorph.preimage_boundary (hn : n ≠ 0) {f : M → N}
    (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.boundary N = I.boundary M := by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_boundary_inter hn
/-
**IsLocalDiffeomorph.boundarylessManifold** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.boundarylessManifold (hn : n != 0) {f : M -> N} (hf : I
sLocalDiffeomorph I I' n f) [BoundarylessManifold I' N] : BoundarylessManifold I
 M
参数：hn : n != 0；hf : IsLocalDiffeomorph I I' n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalDiffeomorph.preimage_boundary`：IsLocalDiffeomorph.preimage_bounda
ry (hn : n != 0) {f : M -> N} (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.boun
dary N = I.boundary M
· 使用定理 `ModelWithCorners.Boundaryless.boundary_eq_empty`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsLocalDiffeomorph.boundarylessManifold (hn : n ≠ 0) {f : M → N}
    (hf : IsLocalDiffeomorph I I' n f) [BoundarylessManifold I' N] : BoundarylessManifold I M := by
  simp [← Boundaryless.iff_boundary_eq_empty, ← hf.preimage_boundary hn,
    Boundaryless.boundary_eq_empty]
/-
**Diffeomorph.preimage_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.preimage_interior (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) : Φ ⁻¹' 
I'.interior N = I.interior M
参数：hn : n != 0；Φ : M ≃ₘ^n⟮I, I'⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorph.preimage_interior`：IsLocalDiffeomorph.preimage_interi
or (hn : n != 0) {f : M -> N} (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.inte
rior N = I.interior M
· 使用引理 `Diffeomorph.isLocalDiffeomorph`：Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ
^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ
-/
lemma Diffeomorph.preimage_interior (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ ⁻¹' I'.interior N = I.interior M :=
  Φ.isLocalDiffeomorph.preimage_interior hn
/-
**Diffeomorph.preimage_boundary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.preimage_boundary (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) : Φ ⁻¹' 
I'.boundary N = I.boundary M
参数：hn : n != 0；Φ : M ≃ₘ^n⟮I, I'⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorph.preimage_boundary`：IsLocalDiffeomorph.preimage_bounda
ry (hn : n != 0) {f : M -> N} (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.boun
dary N = I.boundary M
· 使用引理 `Diffeomorph.isLocalDiffeomorph`：Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ
^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ
-/
lemma Diffeomorph.preimage_boundary (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ ⁻¹' I'.boundary N = I.boundary M :=
  Φ.isLocalDiffeomorph.preimage_boundary hn
/-
**Diffeomorph.image_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.image_interior (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) : Φ '' I.in
terior M = I'.interior N
参数：hn : n != 0；Φ : M ≃ₘ^n⟮I, I'⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {α β} (e : α ≃ 
β) (s t) : s = e ⁻¹' t ↔ e '' s = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Diffeomorph.preimage_interior`：Diffeomorph.preimage_interior (hn : n != 
0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) : Φ ⁻¹' I'.interior N = I.interior M
-/
lemma Diffeomorph.image_interior (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ '' I.interior M = I'.interior N :=
  (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_interior hn).symm
/-
**Diffeomorph.image_boundary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.image_boundary (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) : Φ '' I.bo
undary M = I'.boundary N
参数：hn : n != 0；Φ : M ≃ₘ^n⟮I, I'⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {α β} (e : α ≃ 
β) (s t) : s = e ⁻¹' t ↔ e '' s = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Diffeomorph.preimage_boundary`：Diffeomorph.preimage_boundary (hn : n != 
0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) : Φ ⁻¹' I'.boundary N = I.boundary M
-/
lemma Diffeomorph.image_boundary (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ '' I.boundary M = I'.boundary N :=
  (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_boundary hn).symm
/-
**Diffeomorph.boundarylessManifold** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.boundarylessManifold (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) [Boun
darylessManifold I M] : BoundarylessManifold I' N
参数：hn : n != 0；Φ : M ≃ₘ^n⟮I, I'⟯ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorph.boundarylessManifold`：IsLocalDiffeomorph.boundaryless
Manifold (hn : n != 0) {f : M -> N} (hf : IsLocalDiffeomorph I I' n f) [Boundary
lessManifold I' N] : Boundary…
· 使用引理 `Diffeomorph.isLocalDiffeomorph`：Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ
^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ
-/
lemma Diffeomorph.boundarylessManifold (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
    [BoundarylessManifold I M] : BoundarylessManifold I' N :=
  Φ.symm.isLocalDiffeomorph.boundarylessManifold hn
/-
**Diffeomorph.boundarylessManifold_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.boundarylessManifold_iff (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
 BoundarylessManifold I M ↔ BoundarylessManifold I' N
参数：hn : n != 0；Φ : M ≃ₘ^n⟮I, I'⟯ N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Diffeomorph.boundarylessManifold`：Diffeomorph.boundarylessManifold (hn :
 n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) [BoundarylessManifold I M] : BoundarylessManifold
 I' N
-/
lemma Diffeomorph.boundarylessManifold_iff (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    BoundarylessManifold I M ↔ BoundarylessManifold I' N :=
  ⟨fun _ ↦ Φ.boundarylessManifold hn, fun _ ↦ Φ.symm.boundarylessManifold hn⟩

end Diffeomorph

namespace ModelWithCorners

/-! Interior and boundary of open subsets of a manifold. -/
section opens

open TopologicalSpace

/-- For `u : Opens M`, `x : u` is an interior point iff `x.val : M` is. -/
/-
**ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val** 是 Mathlib 中的一个引理，位于
命名空间 `ModelWithCorners`。
形式化陈述：isInteriorPoint_iff_isInteriorPoint_val {u : Opens M} {x : u} : I.IsInteri
orPoint x ↔ I.IsInteriorPoint x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isInteriorPoint_iff`：isInteriorPoint_iff {x : M} : I.Is
InteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TopologicalSpace.Opens.chartAt_eq`：chartAt_eq {s : Opens M} {x : s} : ch
artAt H x = (chartAt H x.1).subtypeRestr ⟨x⟩
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target`：openParti
alHomeomorphSubtypeCoe_target : (s.openPartialHomeomorphSubtypeCoe hs).target = 
s
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `OpenPartialHomeomorph.extend_preimage_mem_nhds`：extend_preimage_mem_nhds
 {x : M} (h : x in f.source) (ht : t in 𝓝 x) : (f.extend I).symm ⁻¹' t in 𝓝 (f.e
xtend I x)
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
For `u : Opens M`, `x : u` is an interior point iff `x.val : M` is.
-/
lemma isInteriorPoint_iff_isInteriorPoint_val {u : Opens M} {x : u} :
    I.IsInteriorPoint x ↔ I.IsInteriorPoint x.1 := by
  simpa [I.isInteriorPoint_iff, u.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr, mem_interior_iff_mem_nhds] using!
    fun _ _ ↦ (chartAt H x.1).extend_preimage_mem_nhds (mem_chart_source H x.1) (u.2.mem_nhds x.2)

/-- For `u : Opens M`, `x : u` is a boundary point iff `x.val : M` is. -/
/-
**ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val** 是 Mathlib 中的一个引理，位于
命名空间 `ModelWithCorners`。
形式化陈述：isBoundaryPoint_iff_isBoundaryPoint_val {u : Opens M} {x : u} : I.IsBounda
ryPoint x ↔ I.IsBoundaryPoint x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint`：isInteriorPoin
t_iff_not_isBoundaryPoint (x : M) : I.IsInteriorPoint x ↔ ¬I.IsBoundaryPoint x
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val`：isInteriorPoin
t_iff_isInteriorPoint_val {u : Opens M} {x : u} : I.IsInteriorPoint x ↔ I.IsInte
riorPoint x.1

--- 原说明 ---
For `u : Opens M`, `x : u` is a boundary point iff `x.val : M` is.
-/
lemma isBoundaryPoint_iff_isBoundaryPoint_val {u : Opens M} {x : u} :
    I.IsBoundaryPoint x ↔ I.IsBoundaryPoint x.1 := by
  simpa [I.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not] using
    I.isInteriorPoint_iff_isInteriorPoint_val

/-- The interior of `u : Opens M` is the preimage of the interior of `M` under the inclusion. -/
/-
**ModelWithCorners.interior_open** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：interior_open {u : Opens M} : I.interior u = (↑) ⁻¹' I.interior M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val`：isInteriorPoin
t_iff_isInteriorPoint_val {u : Opens M} {x : u} : I.IsInteriorPoint x ↔ I.IsInte
riorPoint x.1

--- 原说明 ---
The interior of `u : Opens M` is the preimage of the interior of `M` under the i
nclusion.
-/
lemma interior_open {u : Opens M} : I.interior u = (↑) ⁻¹' I.interior M := by
  ext1; exact I.isInteriorPoint_iff_isInteriorPoint_val

/-- The boundary of `u : Opens M` is the preimage of the boundary of `M` under the inclusion. -/
/-
**ModelWithCorners.boundary_open** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：boundary_open {u : Opens M} : I.boundary u = (↑) ⁻¹' I.boundary M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.compl_interior`：compl_interior : (I.interior M)ᶜ = I.bo
undary M
· 使用引理 `ModelWithCorners.interior_open`：interior_open {u : Opens M} : I.interior
 u = (↑) ⁻¹' I.interior M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The boundary of `u : Opens M` is the preimage of the boundary of `M` under the i
nclusion.
-/
lemma boundary_open {u : Opens M} : I.boundary u = (↑) ⁻¹' I.boundary M := by
  simp [← I.compl_interior, I.interior_open]

/-- Open subsets of boundaryless manifolds are boundaryless. -/
/-
**ModelWithCorners.BoundarylessManifold.open** 是 Mathlib 中的一个定理，位于命名空间 `ModelWit
hCorners.BoundarylessManifold`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] [BoundarylessManifold I M] (u : Topol
ogicalSpace.Opens M),   BoundarylessManifold I ↥u
参数：u : TopologicalSpace.Opens M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val`：isInteriorPoin
t_iff_isInteriorPoint_val {u : Opens M} {x : u} : I.IsInteriorPoint x ↔ I.IsInte
riorPoint x.1
· 使用定理 `BoundarylessManifold.isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
Open subsets of boundaryless manifolds are boundaryless.
-/
instance BoundarylessManifold.open [BoundarylessManifold I M] (u : Opens M) :
    BoundarylessManifold I u :=
  ⟨fun _ ↦ I.isInteriorPoint_iff_isInteriorPoint_val.2 BoundarylessManifold.isInteriorPoint⟩

end opens

/-! Interior and boundary of the product of two manifolds. -/
section prod

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'} {x : M} {y : N}

/-- The interior of `M × N` is the product of the interiors of `M` and `N`. -/
/-
**ModelWithCorners.interior_prod** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：interior_prod : (I.prod J).interior (M × N) = (I.interior M) ×ˢ (J.interio
r N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_prod_eq`：interior_prod_eq (s : Set X) (t : Set Y) : interior (s
 ×ˢ t) = interior s ×ˢ interior t
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `modelWithCorners_prod_coe`：modelWithCorners_prod_coe (I : ModelWithCorne
rs 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') : (I.prod I' : _ × _ -> _ × _) = Prod.
map I I'
· 使用定理 `ModelWithCorners.IsInteriorPoint.eq_1`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `ModelWithCorners.interior.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
The interior of `M × N` is the product of the interiors of `M` and `N`.
-/
lemma interior_prod :
    (I.prod J).interior (M × N) = (I.interior M) ×ˢ (J.interior N) := by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq, ← range_prodMap, modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint, ← aux] at hp
    exact hp
  · change (I.prod J).IsInteriorPoint p
    rw [IsInteriorPoint, ← aux, mem_prod]
    obtain h := Set.mem_prod.mp hp
    rw [ModelWithCorners.interior] at h
    exact h

/-- The boundary of `M × N` is `∂M × N ∪ (M × ∂N)`. -/
/-
**ModelWithCorners.boundary_prod** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners`。
形式化陈述：boundary_prod : (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N)
 union Set.prod (I.boundary M) univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.compl_interior`：compl_interior : (I.interior M)ᶜ = I.bo
undary M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.interior_prod`：interior_prod : (I.prod J).interior (M ×
 N) = (I.interior M) ×ˢ (J.interior N)
· 使用引理 `Set.compl_prod_eq_union`：compl_prod_eq_union {α β : Type*} (s : Set α) (
t : Set β) : (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) union (univ ×ˢ tᶜ)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a

--- 原说明 ---
The boundary of `M × N` is `∂M × N ∪ (M × ∂N)`.
-/
lemma boundary_prod :
    (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N) ∪ Set.prod (I.boundary M) univ := by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ ∪ univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h, I.compl_interior, J.compl_interior, union_comm]
  rfl

/-- If `M` is boundaryless, `∂(M×N) = M × ∂N`. -/
/-
**ModelWithCorners.boundary_of_boundaryless_left** 是 Mathlib 中的一个引理，位于命名空间 `Mode
lWithCorners`。
形式化陈述：boundary_of_boundaryless_left [BoundarylessManifold I M] : (I.prod J).boun
dary (M × N) = Set.prod (univ : Set M) (J.boundary N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.boundary_prod`：boundary_prod : (I.prod J).boundary (M ×
 N) = Set.prod univ (J.boundary N) union Set.prod (I.boundary M) univ
· 使用定理 `ModelWithCorners.Boundaryless.boundary_eq_empty`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a

--- 原说明 ---
If `M` is boundaryless, `∂(M×N) = M × ∂N`.
-/
lemma boundary_of_boundaryless_left [BoundarylessManifold I M] :
    (I.prod J).boundary (M × N) = Set.prod (univ : Set M) (J.boundary N) := by
  rw [boundary_prod, Boundaryless.boundary_eq_empty (I := I)]
  have : Set.prod (∅ : Set M) (univ : Set N) = ∅ := Set.empty_prod
  rw [this, union_empty]

/-- If `N` is boundaryless, `∂(M×N) = ∂M × N`. -/
/-
**ModelWithCorners.boundary_of_boundaryless_right** 是 Mathlib 中的一个引理，位于命名空间 `Mod
elWithCorners`。
形式化陈述：boundary_of_boundaryless_right [BoundarylessManifold J N] : (I.prod J).bou
ndary (M × N) = Set.prod (I.boundary M) (univ : Set N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.boundary_prod`：boundary_prod : (I.prod J).boundary (M ×
 N) = Set.prod univ (J.boundary N) union Set.prod (I.boundary M) univ
· 使用定理 `ModelWithCorners.Boundaryless.boundary_eq_empty`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a

--- 原说明 ---
If `N` is boundaryless, `∂(M×N) = ∂M × N`.
-/
lemma boundary_of_boundaryless_right [BoundarylessManifold J N] :
    (I.prod J).boundary (M × N) = Set.prod (I.boundary M) (univ : Set N) := by
  rw [boundary_prod, Boundaryless.boundary_eq_empty (I := J)]
  have : Set.prod (univ : Set M) (∅ : Set N) = ∅ := Set.prod_empty
  rw [this, empty_union]

/-- The product of two boundaryless manifolds is boundaryless. -/
/-
**ModelWithCorners.BoundarylessManifold.prod** 是 Mathlib 中的一个定理，位于命名空间 `ModelWit
hCorners.BoundarylessManifold`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {N : Type u_7}   [inst_9 : TopologicalSpace N] [inst_10 : ChartedSpace 
H' N] {J : ModelWithCorners 𝕜 E' H'} [BoundarylessManifold I M]   [BoundarylessM
anifold J N], BoundarylessManifold (I.prod J) (M × N)
参数：I.prod J；M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.Boundaryless.of_boundary_eq_empty`：∀ {𝕜 : Type u_1} [in
st : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.boundary_prod`：boundary_prod : (I.prod J).boundary (M ×
 N) = Set.prod univ (J.boundary N) union Set.prod (I.boundary M) univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.Boundaryless.boundary_eq_empty`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅

--- 原说明 ---
The product of two boundaryless manifolds is boundaryless.
-/
instance BoundarylessManifold.prod [BoundarylessManifold I M] [BoundarylessManifold J N] :
    BoundarylessManifold (I.prod J) (M × N) := by
  apply Boundaryless.of_boundary_eq_empty
  simp only [boundary_prod, Boundaryless.boundary_eq_empty, union_empty_iff]
  -- These are simp lemmas, but `simp` does not apply them on its own:
  -- presumably because of the distinction between `Prod` and `ModelProd`
  exact ⟨Set.prod_empty, Set.empty_prod⟩

end prod

/-! Interior and boundary of the disjoint union of two manifolds. -/
section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞}

open Topology

/-
**ModelWithCorners.interiorPoint_inl** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners
`。
形式化陈述：interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) : I.IsInteriorPoint (
.inl x : M oplus M')
参数：x : M；hx : I.IsInteriorPoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isInteriorPoint_iff`：isInteriorPoint_iff {x : M} : I.Is
InteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
-/
lemma interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inl x : M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx
/-
**ModelWithCorners.boundaryPoint_inl** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners
`。
形式化陈述：boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) : I.IsBoundaryPoint (
.inl x : M oplus M')
参数：x : M；hx : I.IsBoundaryPoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isBoundaryPoint_iff`：isBoundaryPoint_iff {x : M} : I.Is
BoundaryPoint x ↔ extChartAt I x x in frontier (range I)
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
lemma boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inl x : M ⊕ M') := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx
/-
**ModelWithCorners.interiorPoint_inr** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners
`。
形式化陈述：interiorPoint_inr (x : M') (hx : I.IsInteriorPoint x) : I.IsInteriorPoint 
(.inr x : M oplus M')
参数：x : M'；hx : I.IsInteriorPoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isInteriorPoint_iff`：isInteriorPoint_iff {x : M} : I.Is
InteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
-/
lemma interiorPoint_inr (x : M') (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inr x : M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx
/-
**ModelWithCorners.boundaryPoint_inr** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCorners
`。
形式化陈述：boundaryPoint_inr (x : M') (hx : I.IsBoundaryPoint x) : I.IsBoundaryPoint 
(.inr x : M oplus M')
参数：x : M'；hx : I.IsBoundaryPoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isBoundaryPoint_iff`：isBoundaryPoint_iff {x : M} : I.Is
BoundaryPoint x ↔ extChartAt I x x in frontier (range I)
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
lemma boundaryPoint_inr (x : M') (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inr x : M ⊕ M') := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

-- Converse to the previous direction: if `x` were not an interior point,
-- it had to be a boundary point, hence `p` were a boundary point also, contradiction.
/-
**ModelWithCorners.isInteriorPoint_disjointUnion_left** 是 Mathlib 中的一个引理，位于命名空间 
`ModelWithCorners`。
形式化陈述：isInteriorPoint_disjointUnion_left {p : M oplus M'} (hp : I.IsInteriorPoin
t p) (hleft : Sum.isLeft p) : I.IsInteriorPoint (Sum.getLeft p hleft)
参数：hp : I.IsInteriorPoint p；hleft : Sum.isLeft p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isInteriorPoint_disjointUnion_left {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hleft : Sum.isLeft p) : I.IsInteriorPoint (Sum.getLeft p hleft) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inl]
/-
**ModelWithCorners.isInteriorPoint_disjointUnion_right** 是 Mathlib 中的一个引理，位于命名空间
 `ModelWithCorners`。
形式化陈述：isInteriorPoint_disjointUnion_right {p : M oplus M'} (hp : I.IsInteriorPoi
nt p) (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright)
参数：hp : I.IsInteriorPoint p；hright : Sum.isRight p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isInteriorPoint_disjointUnion_right {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inr]
/-
**ModelWithCorners.interior_disjointUnion** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCo
rners`。
形式化陈述：interior_disjointUnion : ModelWithCorners.interior (I
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma interior_disjointUnion :
    ModelWithCorners.interior (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.interior (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
  grind [boundaryPoint_inl, boundaryPoint_inr, interior.eq_def, interiorPoint_inl,
    interiorPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint]
/-
**ModelWithCorners.boundary_disjointUnion** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCo
rners`。
形式化陈述：boundary_disjointUnion : ModelWithCorners.boundary (I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.interior_disjointUnion`：interior_disjointUnion : ModelW
ithCorners.interior (I
· 使用引理 `Set.inl_compl_union_inr_compl`：inl_compl_union_inr_compl {s : Set α} {t 
: Set β} : Sum.inl '' sᶜ union Sum.inr '' tᶜ = (Sum.inl '' s union Sum.inr '' t)
ᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma boundary_disjointUnion : ModelWithCorners.boundary (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.boundary (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.boundary (I := I) M') := by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, inl_compl_union_inr_compl]

/-- If `M` and `M'` are boundaryless, so is their disjoint union `M ⊔ M'`. -/
/-
**ModelWithCorners.boundaryless_disjointUnion** 是 Mathlib 中的一个实例，位于命名空间 `ModelWi
thCorners`。
形式化陈述：boundaryless_disjointUnion [hM : BoundarylessManifold I M] [hM' : Boundary
lessManifold I M'] : BoundarylessManifold I (M oplus M')
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.Boundaryless.iff_boundary_eq_empty`：∀ {𝕜 : Type u_1} [i
nst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] 
  [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ModelWithCorners.boundary_disjointUnion`：boundary_disjointUnion : ModelW
ithCorners.boundary (I
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `M'` are boundaryless, so is their disjoint union `M ⊔ M'`.
-/
instance boundaryless_disjointUnion
    [hM : BoundarylessManifold I M] [hM' : BoundarylessManifold I M'] :
    BoundarylessManifold I (M ⊕ M') := by
  rw [← Boundaryless.iff_boundary_eq_empty] at hM hM' ⊢
  simp [boundary_disjointUnion, hM, hM']

end disjointUnion

end ModelWithCorners

