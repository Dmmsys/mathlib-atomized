/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Totally Bounded sets and Convex Hulls

## Main statements

- `totallyBounded_convexHull`: The convex hull of a totally bounded set is totally bounded.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

convex, totally bounded
-/

public section

open Set Pointwise

variable {E : Type*} {s : Set E}
variable [AddCommGroup E] [Module ℝ E]
variable [UniformSpace E] [IsUniformAddGroup E] [LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

/-
**TotallyBounded.convexHull** 是 Mathlib 中的一个定理，位于命名空间 `TotallyBounded`。
形式化陈述：∀ {E : Type u_1} {s : Set E} [inst : AddCommGroup E] [inst_1 : _root_.Modu
le ℝ E] [inst_2 : UniformSpace E]   [IsUniformAddGroup E] [LocallyConvexSpace ℝ 
E] [ContinuousSMul ℝ E],   TotallyBounded s → TotallyBounded ((convexHull ℝ) s)
参数：(convexHull ℝ) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyBounded_iff_subset_finite_iUnion_nhds_zero`：∀ {α : Type u_1} [ins
t : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {s : Set α},   T
otallyBounded s ↔ ∀ U ∈ nhds 0, ∃ t, t.…
· 使用定理 `exists_nhds_zero_half`：∀ {M : Type u_3} [inst : TopologicalSpace M] [ins
t_1 : AddZeroClass M] [ContinuousAdd M] {s : Set M},   s ∈ nhds 0 → ∃ V ∈ nhds 0
, ∀ v ∈ V, …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `locallyConvexSpace_iff_exists_convex_subset_zero`：locallyConvexSpace_iff
_exists_convex_subset_zero : LocallyConvexSpace 𝕜 E ↔ forall U in (𝓝 0 : Filter 
E), exists S in (𝓝 0 : Filter E), Conv…
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s
· 使用定理 `Set.Finite.isCompact_convexHull`：Set.Finite.isCompact_convexHull {s : Se
t E} (hs : s.Finite) : IsCompact (convexHull 𝕜 s)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
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
· 使用定理 `Set.iUnion_vadd_set`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] (
s : Set α) (t : Set β), ⋃ a ∈ s, a +ᵥ t = s +ᵥ t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `convexHull_add_subset`：convexHull_add_subset {s t : Set E} : convexHull 
𝕜 (s + t) subseteq convexHull 𝕜 s + convexHull 𝕜 t
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Set.instAddLeftMono`：∀ {α : Type u_2} [inst : Add α], AddLeftMono (Set α
)
· 使用定理 `Set.instAddRightMono`：∀ {α : Type u_2} [inst : Add α], AddRightMono (Set
 α)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.add_subset_iff`：∀ {α : Type u_2} [inst : Add α] {s t u : Set α}, s +
 t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x + y ∈ u
-/
protected lemma TotallyBounded.convexHull (hs : TotallyBounded s) :
    TotallyBounded (convexHull ℝ s) := by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at ⊢ hs
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, hV₁,hV₂, hV₃⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp ‹_› W hW₁
  obtain ⟨t, htf, hts⟩ := hs _ hV₁
  obtain ⟨t', htf', hts'⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (htf.isCompact_convexHull ℝ).totallyBounded _ hV₁
  use t', htf'
  simp only [iUnion_vadd_set, vadd_eq_add] at hts hts' ⊢
  grw [hts, convexHull_add_subset, hV₂.convexHull_eq, hts', add_assoc, hV₃, add_subset_iff.mpr hW₂]
/-
**totallyBounded_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} {s : Set E} [inst : AddCommGroup E] [inst_1 : _root_.Modu
le ℝ E] [inst_2 : UniformSpace E]   [IsUniformAddGroup E] [LocallyConvexSpace ℝ 
E] [ContinuousSMul ℝ E],   TotallyBounded ((convexHull ℝ) s) ↔ TotallyBounded s
参数：(convexHull ℝ) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `TotallyBounded.convexHull`：∀ {E : Type u_1} {s : Set E} [inst : AddCommG
roup E] [inst_1 : _root_.Module ℝ E] [inst_2 : UniformSpace E]   [IsUniformAddGr
oup E] [Locally…
-/
@[simp] lemma totallyBounded_convexHull : TotallyBounded (convexHull ℝ s) ↔ TotallyBounded s where
  mp := .subset <| subset_convexHull ..
  mpr := .convexHull
