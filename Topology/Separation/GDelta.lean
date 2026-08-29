/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.GDelta.Basic

/-!
# Separation properties of topological spaces.

## Main definitions

* `PerfectlyNormalSpace`: A perfectly normal space is a normal space such that
  closed sets are Gδ.
* `T6Space`: A T₆ space is a perfectly normal T₀ space. T₆ implies T₅.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

-/

public section

open Function Set Filter Topology TopologicalSpace

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Separation

/--
theorem `IsGδ.compl_singleton` / 定理 `IsGδ.compl_singleton`

English:
theorem IsGδ.compl_singleton
  given: (x : X) [T1Space X]
  statement: IsGδ ({x}ᶜ : Set X)
  proof: isOpen_compl_singleton.isGδ

中文:
定理 IsGδ.compl_singleton
  条件: (x : X) [T1空间 X]
  结论: IsGδ ({x}ᶜ : 集合 X)
  证明: isOpen_compl_singleton.isGδ

Depends on / 依赖: isOpen_compl_singleton, isOpen_compl_singleton.isG
-/
theorem IsGδ.compl_singleton (x : X) [T1Space X] : IsGδ ({x}ᶜ : Set X) :=
  isOpen_compl_singleton.isGδ

/--
theorem `Set.Countable.isGδ_compl` / 定理 `Set.Countable.isGδ_compl`

English:
theorem Set.Countable.isGδ_compl
  given: {s : Set X} [T1Space X] (hs : s.Countable)
  statement: IsGδ sᶜ
  proof: by
  rw [← biUnion_of_singleton s]; rw [compl_iUnion₂]
  exact .biInter hs fun x _ => .compl_singleton x

中文:
定理 集合.可数.isGδ_compl
  条件: {s : 集合 X} [T1空间 X] (hs : s.可数)
  结论: IsGδ sᶜ
  证明: by
  rw [← biUnion_of_singleton s]; rw [compl_iUnion₂]
  exact .biInter hs fun x _ => .compl_singleton x

Depends on / 依赖: biInter, biUnion_of_singleton, compl_singleton
-/
theorem Set.Countable.isGδ_compl {s : Set X} [T1Space X] (hs : s.Countable) : IsGδ sᶜ := by
  rw [← biUnion_of_singleton s]; rw [compl_iUnion₂]
  exact .biInter hs fun x _ => .compl_singleton x

/--
theorem `Set.Finite.isGδ_compl` / 定理 `Set.Finite.isGδ_compl`

English:
theorem Set.Finite.isGδ_compl
  given: {s : Set X} [T1Space X] (hs : s.Finite)
  statement: IsGδ sᶜ
  proof: hs.countable.isGδ_compl

中文:
定理 集合.有限.isGδ_compl
  条件: {s : 集合 X} [T1空间 X] (hs : s.有限)
  结论: IsGδ sᶜ
  证明: hs.countable.isGδ_compl

Depends on / 依赖: countable, hs.countable.isG
-/
theorem Set.Finite.isGδ_compl {s : Set X} [T1Space X] (hs : s.Finite) : IsGδ sᶜ :=
  hs.countable.isGδ_compl

/--
theorem `Set.Subsingleton.isGδ_compl` / 定理 `Set.Subsingleton.isGδ_compl`

English:
theorem Set.Subsingleton.isGδ_compl
  given: {s : Set X} [T1Space X] (hs : s.Subsingleton)
  statement: IsGδ sᶜ
  proof: hs.finite.isGδ_compl

中文:
定理 集合.子单例.isGδ_compl
  条件: {s : 集合 X} [T1空间 X] (hs : s.子单例)
  结论: IsGδ sᶜ
  证明: hs.finite.isGδ_compl

Depends on / 依赖: finite, hs.finite.isG
-/
theorem Set.Subsingleton.isGδ_compl {s : Set X} [T1Space X] (hs : s.Subsingleton) : IsGδ sᶜ :=
  hs.finite.isGδ_compl

/--
theorem `Finset.isGδ_compl` / 定理 `Finset.isGδ_compl`

English:
theorem Finset.isGδ_compl
  given: [T1Space X] (s : Finset X)
  statement: IsGδ (sᶜ : Set X)
  proof: s.finite_toSet.isGδ_compl

中文:
定理 有限集.isGδ_compl
  条件: [T1空间 X] (s : 有限集 X)
  结论: IsGδ (sᶜ : 集合 X)
  证明: s.finite_toSet.isGδ_compl

Depends on / 依赖: finite_toSet, s.finite_toSet.isG
-/
theorem Finset.isGδ_compl [T1Space X] (s : Finset X) : IsGδ (sᶜ : Set X) :=
  s.finite_toSet.isGδ_compl

/--
theorem `IsGδ.singleton` / 定理 `IsGδ.singleton`

English:
theorem IsGδ.singleton
  given: [FirstCountableTopology X] [T1Space X] (x : X)
  proof: by
  rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact .biInter (to_countable _) fun n _ => (hU n).2.isGδ

中文:
定理 IsGδ.singleton
  条件: [第一可数拓扑 X] [T1空间 X] (x : X)
  证明: by
  rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact .biInter (to_countable _) fun n _ => (hU n).2.isGδ
-/
protected theorem IsGδ.singleton [FirstCountableTopology X] [T1Space X] (x : X) :
    IsGδ ({x} : Set X) := by
  rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact .biInter (to_countable _) fun n _ => (hU n).2.isGδ

/--
theorem `Set.Finite.isGδ` / 定理 `Set.Finite.isGδ`

English:
theorem Set.Finite.isGδ
  given: [FirstCountableTopology X] {s : Set X} [T1Space X] (hs : s.Finite)
  proof: Finite.induction_on _ hs .empty fun _ _ => .union (.singleton _)

中文:
定理 集合.有限.isGδ
  条件: [第一可数拓扑 X] {s : 集合 X} [T1空间 X] (hs : s.有限)
  证明: Finite.induction_on _ hs .empty fun _ _ => .union (.singleton _)

Depends on / 依赖: Finite, Finite.induction_on, induction_on, singleton
-/
theorem Set.Finite.isGδ [FirstCountableTopology X] {s : Set X} [T1Space X] (hs : s.Finite) :
    IsGδ s :=
  Finite.induction_on _ hs .empty fun _ _ => .union (.singleton _)


section PerfectlyNormal

/--
Definition of `PerfectlyNormalSpace` / `PerfectlyNormalSpace` 的定义

English:
class PerfectlyNormalSpace
  parameters: (X : Type u) [TopologicalSpace X]
  extends: NormalSpace X
  axioms and operations (1):
    - closed_gdelta : forall ⦃h : Set X⦄, IsClosed h -> IsGδ h

中文:
类 PerfectlyNormal空间
  参数: (X : 类型u) [拓扑空间 X]
  继承: 正规空间 X
  公理与运算 (1 个):
    - closed_gdelta : 对任意 ⦃h : 集合 X⦄, 是闭集 h -> IsGδ h
-/
class PerfectlyNormalSpace (X : Type u) [TopologicalSpace X] : Prop extends NormalSpace X where
    closed_gdelta : forall ⦃h : Set X⦄, IsClosed h -> IsGδ h

/--
theorem `Disjoint.hasSeparatingCover_closed_gdelta_right` / 定理 `Disjoint.hasSeparatingCover_closed_gdelta_right`

English:
theorem Disjoint.hasSeparatingCover_closed_gdelta_right
  statement: {s t : Set X} [NormalSpace X]
  proof: by
  obtain ⟨T, T_open, T_count, T_int⟩ := t_gd
  rcases T.eq_empty_or_nonempty with rfl | T_nonempty
  · rw [T_int, sInter_empty] at st_dis
    rw [(s.disjoint_univ).mp st_dis]
    exact t.hasSeparatingCover_empty_left
  obtain ⟨g, g_surj⟩ := T_count.exists_surjective T_nonempty
  choose g' g'_open clt_sub_g' clg'_sub_g using fun n => by
    apply normal_exists_closure_subset t_cl (T_open (g n).1 (g n).2)
    rw [T_int]
    exact sInter_subset_of_mem (g n).2
  have clg'_int : t = ⋂ i, closure (g' i) := by
    apply (subset_iInter fun n => (clt_sub_g' n).trans subset_closure).antisymm
    rw [T_int]
    refine subset_sInter fun t tinT => ?_
    obtain ⟨n, gn⟩ := g_surj ⟨t, tinT⟩
refine iInter_subset_of_subset n (clg'_sub_g n).trans ?_
    rw [gn]
  use fun n => (closure (g' n))ᶜ
  constructor
  · rw [← compl_iInter, subset_compl_comm, ← clg'_int]
    exact st_dis.subset_compl_left
  · refine fun n => ⟨isOpen_compl_iff.mpr isClosed_closure, ?_⟩
    simp only [closure_compl, disjoint_compl_left_iff_subset]
    rw [← closure_eq_iff_isClosed.mpr t_cl] at clt_sub_g'
exact subset_closure.trans (clt_sub_g' n).trans (g'_open n).subset_interior_closure

中文:
定理 Disjoint.hasSeparatingCover_closed_gdelta_right
  结论: {s t : 集合 X} [正规空间 X]
  证明: by
  obtain ⟨T, T_open, T_count, T_int⟩ := t_gd
  rcases T.eq_empty_or_nonempty with rfl | T_nonempty
  · rw [T_int, sInter_empty] at st_dis
    rw [(s.disjoint_univ).mp st_dis]
    exact t.hasSeparatingCover_empty_left
  obtain ⟨g, g_surj⟩ := T_count.exists_surjective T_nonempty
  choose g' g'_open clt_sub_g' clg'_sub_g using fun n => by
    apply normal_exists_closure_subset t_cl (T_open (g n).1 (g n).2)
    rw [T_int]
    exact sInter_subset_of_mem (g n).2
  have clg'_int : t = ⋂ i, closure (g' i) := by
    apply (subset_iInter fun n => (clt_sub_g' n).trans subset_closure).antisymm
    rw [T_int]
    refine subset_sInter fun t tinT => ?_
    obtain ⟨n, gn⟩ := g_surj ⟨t, tinT⟩
refine iInter_subset_of_subset n (clg'_sub_g n).trans ?_
    rw [gn]
  use fun n => (closure (g' n))ᶜ
  constructor
  · rw [← compl_iInter, subset_compl_comm, ← clg'_int]
    exact st_dis.subset_compl_left
  · refine fun n => ⟨isOpen_compl_iff.mpr isClosed_closure, ?_⟩
    simp only [closure_compl, disjoint_compl_left_iff_subset]
    rw [← closure_eq_iff_isClosed.mpr t_cl] at clt_sub_g'
exact subset_closure.trans (clt_sub_g' n).trans (g'_open n).subset_interior_closure

Depends on / 依赖: T.eq_empty_or_nonempty, T_count, T_count.exists_surjective, T_int, T_nonempty, T_open, _int, _open, _sub_g, closure, clt_sub_g, disjoint_univ, eq_empty_or_nonempty, exists_surjective, g_surj, hasSeparatingCover_empty_left, normal_exists_closure_subset, s.disjoint_univ, sInter_empty, sInter_subset_of_mem
-/
theorem Disjoint.hasSeparatingCover_closed_gdelta_right {s t : Set X} [NormalSpace X]
    (st_dis : Disjoint s t) (t_cl : IsClosed t) (t_gd : IsGδ t) : HasSeparatingCover s t := by
  obtain ⟨T, T_open, T_count, T_int⟩ := t_gd
  rcases T.eq_empty_or_nonempty with rfl | T_nonempty
  · rw [T_int, sInter_empty] at st_dis
    rw [(s.disjoint_univ).mp st_dis]
    exact t.hasSeparatingCover_empty_left
  obtain ⟨g, g_surj⟩ := T_count.exists_surjective T_nonempty
  choose g' g'_open clt_sub_g' clg'_sub_g using fun n => by
    apply normal_exists_closure_subset t_cl (T_open (g n).1 (g n).2)
    rw [T_int]
    exact sInter_subset_of_mem (g n).2
  have clg'_int : t = ⋂ i, closure (g' i) := by
    apply (subset_iInter fun n => (clt_sub_g' n).trans subset_closure).antisymm
    rw [T_int]
    refine subset_sInter fun t tinT => ?_
    obtain ⟨n, gn⟩ := g_surj ⟨t, tinT⟩
refine iInter_subset_of_subset n (clg'_sub_g n).trans ?_
    rw [gn]
  use fun n => (closure (g' n))ᶜ
  constructor
  · rw [← compl_iInter, subset_compl_comm, ← clg'_int]
    exact st_dis.subset_compl_left
  · refine fun n => ⟨isOpen_compl_iff.mpr isClosed_closure, ?_⟩
    simp only [closure_compl, disjoint_compl_left_iff_subset]
    rw [← closure_eq_iff_isClosed.mpr t_cl] at clt_sub_g'
exact subset_closure.trans (clt_sub_g' n).trans (g'_open n).subset_interior_closure

instance (priority := 100) PerfectlyNormalSpace.toCompletelyNormalSpace
    [PerfectlyNormalSpace X] : CompletelyNormalSpace X where
completely_normal _ _ hd₁ hd₂ := separatedNhds_iff_disjoint.mp
    hasSeparatingCovers_iff_separatedNhds.mp
      ⟨(hd₂.hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a => a) subset_closure,
       ((Disjoint.symm hd₁).hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a => a) subset_closure⟩

/--
theorem `IsClosed.isGδ` / 定理 `IsClosed.isGδ`

English:
theorem IsClosed.isGδ
  given: [PerfectlyNormalSpace X] {s : Set X} (hs : IsClosed s)
  statement: IsGδ s
  proof: PerfectlyNormalSpace.closed_gdelta hs

中文:
定理 是闭集.isGδ
  条件: [PerfectlyNormal空间 X] {s : 集合 X} (hs : 是闭集 s)
  结论: IsGδ s
  证明: PerfectlyNormalSpace.closed_gdelta hs

Depends on / 依赖: PerfectlyNormalSpace, PerfectlyNormalSpace.closed_gdelta, closed_gdelta
-/
theorem IsClosed.isGδ [PerfectlyNormalSpace X] {s : Set X} (hs : IsClosed s) : IsGδ s :=
  PerfectlyNormalSpace.closed_gdelta hs

instance (priority := 100) [PerfectlyNormalSpace X] : R0Space X where
  specializes_symm.symm x y hxy := by
    rw [specializes_iff_forall_closed]
    intro K hK hyK
    apply IsClosed.isGδ at hK
    obtain ⟨Ts, hoTs, -, rfl⟩ := hK
    rw [mem_sInter] at hyK ⊢
    intros
    solve_by_elim [hxy.mem_open]

/--
theorem `Topology.IsInducing.perfectlyNormalSpace` / 定理 `Topology.IsInducing.perfectlyNormalSpace`

English:
theorem Topology.IsInducing.perfectlyNormalSpace
  statement: [PerfectlyNormalSpace Y] {e : X -> Y}
  proof: he.completelyNormalSpace.toNormalSpace
  closed_gdelta _ hs := (he.isClosed_iff.1 hs).elim fun _ ht =>
    ht.2 ▸ ht.1.isGδ.preimage he.continuous

中文:
定理 拓扑.是Inducing.perfectlyNormalSpace
  结论: [PerfectlyNormal空间 Y] {e : X -> Y}
  证明: he.completelyNormalSpace.toNormalSpace
  closed_gdelta _ hs := (he.isClosed_iff.1 hs).elim fun _ ht =>
    ht.2 ▸ ht.1.isGδ.preimage he.continuous

Depends on / 依赖: completelyNormalSpace, he.completelyNormalSpace.toNormalSpace, toNormalSpace
-/
theorem Topology.IsInducing.perfectlyNormalSpace [PerfectlyNormalSpace Y] {e : X -> Y}
    (he : IsInducing e) : PerfectlyNormalSpace X where
  toNormalSpace := he.completelyNormalSpace.toNormalSpace
  closed_gdelta _ hs := (he.isClosed_iff.1 hs).elim fun _ ht =>
    ht.2 ▸ ht.1.isGδ.preimage he.continuous

instance {s : Set X} [PerfectlyNormalSpace X] : PerfectlyNormalSpace s :=
  IsEmbedding.subtypeVal.perfectlyNormalSpace

/--
Definition of `T6Space` / `T6Space` 的定义

English:
class T6Space
  parameters: (X : Type u) [TopologicalSpace X]
  extends: T0Space X, PerfectlyNormalSpace X
  (no additional axioms)

中文:
类 T6空间
  参数: (X : 类型u) [拓扑空间 X]
  继承: T0空间 X, PerfectlyNormal空间 X
  (无附加公理)
-/
class T6Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, PerfectlyNormalSpace X

-- see Note [lower instance priority]
/-- A `T₆` space is a `T₅` space. -/
instance (priority := 100) T6Space.toT5Space [T6Space X] : T5Space X where

/--
theorem `Topology.IsEmbedding.t6Space` / 定理 `Topology.IsEmbedding.t6Space`

English:
theorem Topology.IsEmbedding.t6Space
  statement: [T6Space Y] {e : X -> Y}
  proof: he.perfectlyNormalSpace
  toT0Space := he.t0Space

中文:
定理 拓扑.是嵌入.t6Space
  结论: [T6空间 Y] {e : X -> Y}
  证明: he.perfectlyNormalSpace
  toT0Space := he.t0Space

Depends on / 依赖: he.perfectlyNormalSpace, perfectlyNormalSpace
-/
theorem Topology.IsEmbedding.t6Space [T6Space Y] {e : X -> Y}
    (he : IsEmbedding e) : T6Space X where
  toPerfectlyNormalSpace := he.perfectlyNormalSpace
  toT0Space := he.t0Space

instance {s : Set X} [T6Space X] : T6Space s :=
  IsEmbedding.subtypeVal.t6Space

end PerfectlyNormal

end Separation
