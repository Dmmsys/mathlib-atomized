/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `Preperfect C`: A set `C` is preperfect if every point of `C` is an accumulation point
  of `C`. Equivalently, if it has no isolated points in the induced topology.
  This property is also called dense-in-itself.
* `Perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `PerfectSpace X`: A topological space `X` is perfect if its universe is a perfect set.

## Main Statements

* `preperfect_iff_perfect_closure`: In a T1 space, a set is preperfect iff its closure is perfect.
* `Perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_isClosed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty.

## See also

`Mathlib/Topology/MetricSpace/Perfect.lean`, for properties of perfect sets in metric spaces,
namely Polish spaces.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, dense-in-itself, cantor-bendixson.

-/

@[expose] public section


open Topology Filter Set TopologicalSpace

section Basic

variable {α : Type*} [TopologicalSpace α] {C : Set α}

/--
theorem `AccPt.nhds_inter` / 定理 `AccPt.nhds_inter`

English:
theorem AccPt.nhds_inter
  given: {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U in 𝓝 x)
  proof: by
  have : 𝓝[!=] x <= 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt]; rw [← inf_principal]; rw [← inf_assoc]; rw [inf_of_le_left this]
  exact h_acc

中文:
定理 聚点.nhds_inter
  条件: {x : α} {U : 集合 α} (h_acc : 聚点 x (𝓟 C)) (hU : U in 𝓝 x)
  证明: by
  have : 𝓝[!=] x <= 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt]; rw [← inf_principal]; rw [← inf_assoc]; rw [inf_of_le_left this]
  exact h_acc

Depends on / 依赖: h_acc, inf_assoc, inf_of_le_left, inf_principal, le_principal_iff, mem_nhdsWithin_of_mem_nhds
-/
theorem AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U in 𝓝 x) :
    AccPt x (𝓟 (U inter C)) := by
  have : 𝓝[!=] x <= 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt]; rw [← inf_principal]; rw [← inf_assoc]; rw [inf_of_le_left this]
  exact h_acc

/--
Definition of `Preperfect` / `Preperfect` 的定义

English:
definition Preperfect
  signature: (C : Set α)
  body: forall x in C, AccPt x (𝓟 C)

中文:
定义 Preperfect
  签名: (C : 集合 α)
  定义体: forall x in C, AccPt x (𝓟 C)
-/
def Preperfect (C : Set α) : Prop :=
  forall x in C, AccPt x (𝓟 C)

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty. -/
@[mk_iff perfect_def]
/--
Definition of `Perfect` / `Perfect` 的定义

English:
structure Perfect
  parameters: (C : Set α)
  axioms and operations (2):
    - closed : IsClosed C
    - acc : Preperfect C

中文:
结构 完美
  参数: (C : 集合 α)
  公理与运算 (2 个):
    - closed : 是闭集 C
    - acc : Preperfect C
-/
structure Perfect (C : Set α) : Prop where
  closed : IsClosed C
  acc : Preperfect C

/--
theorem `preperfect_iff_nhds` / 定理 `preperfect_iff_nhds`

English:
theorem preperfect_iff_nhds
  statement: Preperfect C ↔ forall x in C, forall U in 𝓝 x, exists y in U inter C, y != x
  proof: by
  simp only [Preperfect, accPt_iff_nhds]

中文:
定理 preperfect_iff_nhds
  结论: Preperfect C ↔ 对任意 x in C, 对任意 U in 𝓝 x, 存在 y in U inter C, y != x
  证明: by
  simp only [Preperfect, accPt_iff_nhds]

Depends on / 依赖: Preperfect, accPt_iff_nhds
-/
theorem preperfect_iff_nhds : Preperfect C ↔ forall x in C, forall U in 𝓝 x, exists y in U inter C, y != x := by
  simp only [Preperfect, accPt_iff_nhds]

section PerfectSpace

variable (α)

/--
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
@[mk_iff perfectSpace_def]
/--
Definition of `PerfectSpace` / `PerfectSpace` 的定义

English:
class PerfectSpace
  parameters: : Prop where
  axioms and operations (1):
    - univ_preperfect : Preperfect (Set.univ : Set α)

中文:
类 完美空间
  参数: : 命题 where
  公理与运算 (1 个):
    - univ_preperfect : Preperfect (集合.univ : 集合 α)
-/
class PerfectSpace : Prop where
  univ_preperfect : Preperfect (Set.univ : Set α)

/--
theorem `PerfectSpace.univ_perfect` / 定理 `PerfectSpace.univ_perfect`

English:
theorem PerfectSpace.univ_perfect
  given: [PerfectSpace α]
  statement: Perfect (Set.univ : Set α)
  proof: ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩

中文:
定理 完美空间.univ_perfect
  条件: [完美空间 α]
  结论: 完美 (集合.univ : 集合 α)
  证明: ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩

Depends on / 依赖: PerfectSpace, PerfectSpace.univ_preperfect, isClosed_univ, univ_preperfect
-/
theorem PerfectSpace.univ_perfect [PerfectSpace α] : Perfect (Set.univ : Set α) :=
  ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩

end PerfectSpace

section Preperfect

/--
theorem `Preperfect.open_inter` / 定理 `Preperfect.open_inter`

English:
theorem Preperfect.open_inter
  given: {U : Set α} (hC : Preperfect C) (hU : IsOpen U)
  proof: by
  rintro x ⟨xU, xC⟩
  apply (hC _ xC).nhds_inter
  exact hU.mem_nhds xU

中文:
定理 Preperfect.open_inter
  条件: {U : 集合 α} (hC : Preperfect C) (hU : 是开集 U)
  证明: by
  rintro x ⟨xU, xC⟩
  apply (hC _ xC).nhds_inter
  exact hU.mem_nhds xU

Depends on / 依赖: hU.mem_nhds, mem_nhds, nhds_inter
-/
theorem Preperfect.open_inter {U : Set α} (hC : Preperfect C) (hU : IsOpen U) :
    Preperfect (U inter C) := by
  rintro x ⟨xU, xC⟩
  apply (hC _ xC).nhds_inter
  exact hU.mem_nhds xU

/--
theorem `Preperfect.perfect_closure` / 定理 `Preperfect.perfect_closure`

English:
theorem Preperfect.perfect_closure
  given: (hC : Preperfect C)
  statement: Perfect (closure C)
  proof: by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x in C <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact hC _ h
  have : {x}ᶜ inter C = C := by simp [h]
  rw [AccPt]; rw [nhdsWithin]; rw [inf_assoc]; rw [inf_principal]; rw [this]
  rw [closure_eq_cluster_pts] at hx
  exact hx

中文:
定理 Preperfect.perfect_closure
  条件: (hC : Preperfect C)
  结论: 完美 (closure C)
  证明: by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x in C <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact hC _ h
  have : {x}ᶜ inter C = C := by simp [h]
  rw [AccPt]; rw [nhdsWithin]; rw [inf_assoc]; rw [inf_principal]; rw [this]
  rw [closure_eq_cluster_pts] at hx
  exact hx

Depends on / 依赖: AccPt.mono, closure_eq_cluster_pts, inf_assoc, inf_principal, isClosed_closure, nhdsWithin, principal_mono, principal_mono.mpr, subset_closure
-/
theorem Preperfect.perfect_closure (hC : Preperfect C) : Perfect (closure C) := by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x in C <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact hC _ h
  have : {x}ᶜ inter C = C := by simp [h]
  rw [AccPt]; rw [nhdsWithin]; rw [inf_assoc]; rw [inf_principal]; rw [this]
  rw [closure_eq_cluster_pts] at hx
  exact hx

/--
theorem `IsOpen.preperfect` / 定理 `IsOpen.preperfect`

English:
theorem IsOpen.preperfect
  given: [PerfectSpace α] {U : Set α} (hU : IsOpen U)
  proof: by
  simpa using PerfectSpace.univ_preperfect.open_inter hU

中文:
定理 是开集.preperfect
  条件: [完美空间 α] {U : 集合 α} (hU : 是开集 U)
  证明: by
  simpa using PerfectSpace.univ_preperfect.open_inter hU

Depends on / 依赖: PerfectSpace, PerfectSpace.univ_preperfect.open_inter, open_inter, univ_preperfect
-/
theorem IsOpen.preperfect [PerfectSpace α] {U : Set α} (hU : IsOpen U) :
    Preperfect U := by
  simpa using PerfectSpace.univ_preperfect.open_inter hU

/--
theorem `IsOpen.perfect_closure` / 定理 `IsOpen.perfect_closure`

English:
theorem IsOpen.perfect_closure
  given: [PerfectSpace α] {U : Set α} (hU : IsOpen U)
  proof: hU.preperfect.perfect_closure

中文:
定理 是开集.perfect_closure
  条件: [完美空间 α] {U : 集合 α} (hU : 是开集 U)
  证明: hU.preperfect.perfect_closure

Depends on / 依赖: hU.preperfect.perfect_closure, perfect_closure, preperfect
-/
theorem IsOpen.perfect_closure [PerfectSpace α] {U : Set α} (hU : IsOpen U) :
    Perfect (closure U) :=
  hU.preperfect.perfect_closure

/--
theorem `preperfect_iff_perfect_closure` / 定理 `preperfect_iff_perfect_closure`

English:
theorem preperfect_iff_perfect_closure
  given: [T1Space α]
  statement: Preperfect C ↔ Perfect (closure C)
  proof: by
  constructor <;> intro h
  · exact h.perfect_closure
  intro x xC
  have H : AccPt x (𝓟 (closure C)) := h.acc _ (subset_closure xC)
  rw [accPt_iff_frequently] at *
  have : forall y, y != x ∧ y in closure C -> existsᶠ z in 𝓝 y, z != x ∧ z in C := by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, and_comm, ← frequently_nhdsWithin_iff,
      hyx.nhdsWithin_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  exact H.mono this

中文:
定理 preperfect_iff_perfect_closure
  条件: [T1空间 α]
  结论: Preperfect C ↔ 完美 (closure C)
  证明: by
  constructor <;> intro h
  · exact h.perfect_closure
  intro x xC
  have H : AccPt x (𝓟 (closure C)) := h.acc _ (subset_closure xC)
  rw [accPt_iff_frequently] at *
  have : forall y, y != x ∧ y in closure C -> existsᶠ z in 𝓝 y, z != x ∧ z in C := by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, and_comm, ← frequently_nhdsWithin_iff,
      hyx.nhdsWithin_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  exact H.mono this

Depends on / 依赖: H.mono, accPt_iff_frequently, and_comm, closure, frequently_frequently_nhds, frequently_nhdsWithin_iff, h.acc, h.perfect_closure, hyx.nhdsWithin_compl_singleton, mem_closure_iff_frequently, mem_compl_singleton_iff, nhdsWithin_compl_singleton, perfect_closure, subset_closure
-/
theorem preperfect_iff_perfect_closure [T1Space α] : Preperfect C ↔ Perfect (closure C) := by
  constructor <;> intro h
  · exact h.perfect_closure
  intro x xC
  have H : AccPt x (𝓟 (closure C)) := h.acc _ (subset_closure xC)
  rw [accPt_iff_frequently] at *
  have : forall y, y != x ∧ y in closure C -> existsᶠ z in 𝓝 y, z != x ∧ z in C := by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, and_comm, ← frequently_nhdsWithin_iff,
      hyx.nhdsWithin_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  exact H.mono this

/--
theorem `Perfect.closure_nhds_inter` / 定理 `Perfect.closure_nhds_inter`

English:
theorem Perfect.closure_nhds_inter
  statement: {U : Set α} (hC : Perfect C) (x : α) (xC : x in C) (xU : x in U)
  proof: by
  constructor
  · apply Preperfect.perfect_closure
    exact hC.acc.open_inter Uop
  apply Nonempty.closure
  exact ⟨x, ⟨xU, xC⟩⟩

中文:
定理 完美.closure_nhds_inter
  结论: {U : 集合 α} (hC : 完美 C) (x : α) (xC : x in C) (xU : x in U)
  证明: by
  constructor
  · apply Preperfect.perfect_closure
    exact hC.acc.open_inter Uop
  apply Nonempty.closure
  exact ⟨x, ⟨xU, xC⟩⟩

Depends on / 依赖: Nonempty, Nonempty.closure, Preperfect, Preperfect.perfect_closure, closure, hC.acc.open_inter, open_inter, perfect_closure
-/
theorem Perfect.closure_nhds_inter {U : Set α} (hC : Perfect C) (x : α) (xC : x in C) (xU : x in U)
    (Uop : IsOpen U) : Perfect (closure (U inter C)) ∧ (closure (U inter C)).Nonempty := by
  constructor
  · apply Preperfect.perfect_closure
    exact hC.acc.open_inter Uop
  apply Nonempty.closure
  exact ⟨x, ⟨xU, xC⟩⟩

/--
theorem `Perfect.splitting` / 定理 `Perfect.splitting`

English:
theorem Perfect.splitting
  given: [T25Space α] (hC : Perfect C) (hnonempty : C.Nonempty)
  proof: by
  obtain ⟨y, yC⟩ := hnonempty
  obtain ⟨x, xC, hxy⟩ : exists x in C, x != y := by
    have := hC.acc _ yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U inter C), closure (V inter C)
  constructor <;> rw [← and_assoc]
  · refine ⟨hC.closure_nhds_inter x xC xU Uop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  constructor
  · refine ⟨hC.closure_nhds_inter y yC yV Vop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left

中文:
定理 完美.splitting
  条件: [T25空间 α] (hC : 完美 C) (hnonempty : C.非空)
  证明: by
  obtain ⟨y, yC⟩ := hnonempty
  obtain ⟨x, xC, hxy⟩ : exists x in C, x != y := by
    have := hC.acc _ yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U inter C), closure (V inter C)
  constructor <;> rw [← and_assoc]
  · refine ⟨hC.closure_nhds_inter x xC xU Uop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  constructor
  · refine ⟨hC.closure_nhds_inter y yC yV Vop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left

Depends on / 依赖: accPt_iff_nhds, and_assoc, closed, closure, closure_nhds_inte, closure_nhds_inter, closure_subset_iff, exists_open_nhds_disjoint_closure, hC.acc, hC.closed.closure_subset_iff, hC.closure_nhds_inte, hC.closure_nhds_inter, hnonempty, inter_subset_right, univ_mem
-/
theorem Perfect.splitting [T25Space α] (hC : Perfect C) (hnonempty : C.Nonempty) :
    exists C₀ C₁ : Set α,
    (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ subseteq C) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ subseteq C) ∧ Disjoint C₀ C₁ := by
  obtain ⟨y, yC⟩ := hnonempty
  obtain ⟨x, xC, hxy⟩ : exists x in C, x != y := by
    have := hC.acc _ yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U inter C), closure (V inter C)
  constructor <;> rw [← and_assoc]
  · refine ⟨hC.closure_nhds_inter x xC xU Uop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  constructor
  · refine ⟨hC.closure_nhds_inter y yC yV Vop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left

/--
lemma `IsPreconnected.preperfect_of_nontrivial` / 引理 `IsPreconnected.preperfect_of_nontrivial`

English:
lemma IsPreconnected.preperfect_of_nontrivial
  statement: [T1Space α] {U : Set α} (hu : U.Nontrivial)
  proof: by
  intro x hx
  rw [isPreconnected_closed_iff] at h
  specialize h {x} (closure (U \ {x})) isClosed_singleton isClosed_closure ?_ ?_ ?_
  · trans {x} union (U \ {x})
    · simp
    apply Set.union_subset_union_right
    exact subset_closure
  · exact Set.inter_singleton_nonempty.mpr hx
  · obtain ⟨y, hy⟩ := Set.Nontrivial.exists_ne hu x
    use y
    simp only [Set.mem_inter_iff, hy, true_and]
    apply subset_closure
    simp [hy]
  · apply Set.Nonempty.right at h
    rw [Set.singleton_inter_nonempty]; rw [mem_closure_iff_clusterPt]; rw [← accPt_principal_iff_clusterPt] at h
    exact h

中文:
引理 是预连通.preperfect_of_nontrivial
  结论: [T1空间 α] {U : 集合 α} (hu : U.非平凡)
  证明: by
  intro x hx
  rw [isPreconnected_closed_iff] at h
  specialize h {x} (closure (U \ {x})) isClosed_singleton isClosed_closure ?_ ?_ ?_
  · trans {x} union (U \ {x})
    · simp
    apply Set.union_subset_union_right
    exact subset_closure
  · exact Set.inter_singleton_nonempty.mpr hx
  · obtain ⟨y, hy⟩ := Set.Nontrivial.exists_ne hu x
    use y
    simp only [Set.mem_inter_iff, hy, true_and]
    apply subset_closure
    simp [hy]
  · apply Set.Nonempty.right at h
    rw [Set.singleton_inter_nonempty]; rw [mem_closure_iff_clusterPt]; rw [← accPt_principal_iff_clusterPt] at h
    exact h

Depends on / 依赖: Nonempty, Nontrivial, Set.Nonempty.right, Set.Nontrivial.exists_ne, Set.inter_singleton_nonempty.mpr, Set.mem_inter_iff, Set.singleton_inter_nonempty, Set.union_subset_union_right, closure, exists_ne, inter_singleton_nonempty, isClosed_closure, isClosed_singleton, isPreconnected_closed_iff, mem_closure_iff_clusterPt, mem_inter_iff, singleton_inter_nonempty, specialize, subset_closure, true_and
-/
lemma IsPreconnected.preperfect_of_nontrivial [T1Space α] {U : Set α} (hu : U.Nontrivial)
    (h : IsPreconnected U) : Preperfect U := by
  intro x hx
  rw [isPreconnected_closed_iff] at h
  specialize h {x} (closure (U \ {x})) isClosed_singleton isClosed_closure ?_ ?_ ?_
  · trans {x} union (U \ {x})
    · simp
    apply Set.union_subset_union_right
    exact subset_closure
  · exact Set.inter_singleton_nonempty.mpr hx
  · obtain ⟨y, hy⟩ := Set.Nontrivial.exists_ne hu x
    use y
    simp only [Set.mem_inter_iff, hy, true_and]
    apply subset_closure
    simp [hy]
  · apply Set.Nonempty.right at h
    rw [Set.singleton_inter_nonempty]; rw [mem_closure_iff_clusterPt]; rw [← accPt_principal_iff_clusterPt] at h
    exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: α] [ConnectedSpace α] [Nontrivial α] : PerfectSpace α
  body: by
  constructor
  apply isPreconnected_univ.preperfect_of_nontrivial
  rw [Set.nontrivial_univ_iff]
  infer_instance

中文:
实例 [T1空间
  签名: α] [连通空间 α] [非平凡 α] : 完美空间 α
  定义体: by
  constructor
  apply isPreconnected_univ.preperfect_of_nontrivial
  rw [Set.nontrivial_univ_iff]
  infer_instance

Depends on / 依赖: Set.nontrivial_univ_iff, infer_instance, isPreconnected_univ, isPreconnected_univ.preperfect_of_nontrivial, nontrivial_univ_iff, preperfect_of_nontrivial
-/
instance [T1Space α] [ConnectedSpace α] [Nontrivial α] : PerfectSpace α := by
  constructor
  apply isPreconnected_univ.preperfect_of_nontrivial
  rw [Set.nontrivial_univ_iff]
  infer_instance

end Preperfect

section Kernel

/--
theorem `exists_countable_union_perfect_of_isClosed` / 定理 `exists_countable_union_perfect_of_isClosed`

English:
theorem exists_countable_union_perfect_of_isClosed
  statement: [SecondCountableTopology α]
  proof: by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  let v := { U in b | (U inter C).Countable }
  let V := ⋃ U in v, U
  let D := C \ V
  have Vct : (V inter C).Countable := by
    simp only [V, iUnion_inter]
    apply Countable.biUnion
    · exact bct.mono (sep_subset _ _)
    · exact sep_subset_ofPred _ _
  refine ⟨V inter C, D, Vct, ⟨?_, ?_⟩, ?_⟩
  · refine hclosed.sdiff (isOpen_biUnion fun _ => ?_)
    exact fun ⟨Ub, _⟩ => IsTopologicalBasis.isOpen bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E inter D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : exists U in b, x in U ∧ U subseteq E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U inter C).Countable := by
        apply @Countable.mono _ _ (E inter D union V inter C)
        · rintro y ⟨yU, yC⟩
          by_cases h : y in V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U in v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_biUnion this xU
    by_contra! h
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
  · rw [inter_comm, inter_union_sdiff]

中文:
定理 存在_countable_union_perfect_of_isClosed
  结论: [第二可数拓扑 α]
  证明: by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  let v := { U in b | (U inter C).Countable }
  let V := ⋃ U in v, U
  let D := C \ V
  have Vct : (V inter C).Countable := by
    simp only [V, iUnion_inter]
    apply Countable.biUnion
    · exact bct.mono (sep_subset _ _)
    · exact sep_subset_ofPred _ _
  refine ⟨V inter C, D, Vct, ⟨?_, ?_⟩, ?_⟩
  · refine hclosed.sdiff (isOpen_biUnion fun _ => ?_)
    exact fun ⟨Ub, _⟩ => IsTopologicalBasis.isOpen bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E inter D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : exists U in b, x in U ∧ U subseteq E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U inter C).Countable := by
        apply @Countable.mono _ _ (E inter D union V inter C)
        · rintro y ⟨yU, yC⟩
          by_cases h : y in V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U in v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_biUnion this xU
    by_contra! h
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
  · rw [inter_comm, inter_union_sdiff]

Depends on / 依赖: Countable, Countable.biUnion, IsTopologicalBasis, IsTopologicalBasis.isOpen, TopologicalSpace, TopologicalSpace.exists_countable_basis, bbasis, bct.mono, biUnion, exists_countable_basis, hclosed, hclosed.sdiff, iUnion_inter, isOpen, isOpen_biUnion, preperfect_iff_nhds, sep_subset, sep_subset_ofPred
-/
theorem exists_countable_union_perfect_of_isClosed [SecondCountableTopology α]
    (hclosed : IsClosed C) : exists V D : Set α, V.Countable ∧ Perfect D ∧ C = V union D := by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  let v := { U in b | (U inter C).Countable }
  let V := ⋃ U in v, U
  let D := C \ V
  have Vct : (V inter C).Countable := by
    simp only [V, iUnion_inter]
    apply Countable.biUnion
    · exact bct.mono (sep_subset _ _)
    · exact sep_subset_ofPred _ _
  refine ⟨V inter C, D, Vct, ⟨?_, ?_⟩, ?_⟩
  · refine hclosed.sdiff (isOpen_biUnion fun _ => ?_)
    exact fun ⟨Ub, _⟩ => IsTopologicalBasis.isOpen bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E inter D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : exists U in b, x in U ∧ U subseteq E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U inter C).Countable := by
        apply @Countable.mono _ _ (E inter D union V inter C)
        · rintro y ⟨yU, yC⟩
          by_cases h : y in V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U in v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_biUnion this xU
    by_contra! h
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
  · rw [inter_comm, inter_union_sdiff]

/--
theorem `exists_perfect_nonempty_of_isClosed_of_not_countable` / 定理 `exists_perfect_nonempty_of_isClosed_of_not_countable`

English:
theorem exists_perfect_nonempty_of_isClosed_of_not_countable
  statement: [SecondCountableTopology α]
  proof: by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  refine ⟨D, ⟨Dperf, ?_⟩⟩
  constructor
  · rw [nonempty_iff_ne_empty]
    by_contra h
    rw [h]; rw [union_empty] at VD
    rw [VD] at hunc
    contradiction
  rw [VD]
  exact subset_union_right

中文:
定理 存在_perfect_nonempty_of_isClosed_of_not_countable
  结论: [第二可数拓扑 α]
  证明: by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  refine ⟨D, ⟨Dperf, ?_⟩⟩
  constructor
  · rw [nonempty_iff_ne_empty]
    by_contra h
    rw [h]; rw [union_empty] at VD
    rw [VD] at hunc
    contradiction
  rw [VD]
  exact subset_union_right

Depends on / 依赖: exists_countable_union_perfect_of_isClosed, hclosed, nonempty_iff_ne_empty, subset_union_right, union_empty
-/
theorem exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopology α]
    (hclosed : IsClosed C) (hunc : ¬C.Countable) : exists D : Set α, Perfect D ∧ D.Nonempty ∧ D subseteq C := by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  refine ⟨D, ⟨Dperf, ?_⟩⟩
  constructor
  · rw [nonempty_iff_ne_empty]
    by_contra h
    rw [h]; rw [union_empty] at VD
    rw [VD] at hunc
    contradiction
  rw [VD]
  exact subset_union_right

end Kernel

end Basic

section PerfectSpace

variable {X : Type*} [TopologicalSpace X]

/--
theorem `perfectSpace_iff_forall_not_isolated` / 定理 `perfectSpace_iff_forall_not_isolated`

English:
theorem perfectSpace_iff_forall_not_isolated
  statement: PerfectSpace X ↔ forall x : X, Filter.NeBot (𝓝[!=] x)
  proof: by
  simp [perfectSpace_def, Preperfect, AccPt]

中文:
定理 perfectSpace_iff_对任意_not_isolated
  结论: 完美空间 X ↔ 对任意 x : X, 滤子.NeBot (𝓝[!=] x)
  证明: by
  simp [perfectSpace_def, Preperfect, AccPt]

Depends on / 依赖: Preperfect, perfectSpace_def
-/
theorem perfectSpace_iff_forall_not_isolated : PerfectSpace X ↔ forall x : X, Filter.NeBot (𝓝[!=] x) := by
  simp [perfectSpace_def, Preperfect, AccPt]

/--
Instance `PerfectSpace.not_isolated` / 实例 `PerfectSpace.not_isolated`

English:
instance PerfectSpace.not_isolated
  signature: [PerfectSpace X] (x : X)
  body: perfectSpace_iff_forall_not_isolated.mp ‹_› x

中文:
实例 完美空间.not_isolated
  签名: [完美空间 X] (x : X)
  定义体: perfectSpace_iff_forall_not_isolated.mp ‹_› x

Depends on / 依赖: perfectSpace_iff_forall_not_isolated, perfectSpace_iff_forall_not_isolated.mp
-/
instance PerfectSpace.not_isolated [PerfectSpace X] (x : X) : Filter.NeBot (𝓝[!=] x) :=
  perfectSpace_iff_forall_not_isolated.mp ‹_› x

end PerfectSpace
