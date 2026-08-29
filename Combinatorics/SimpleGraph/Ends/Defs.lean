/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finite.Set

/-!
# Ends

This file contains a definition of the ends of a simple graph, as sections of the inverse system
assigning, to each finite set of vertices, the connected components of its complement.
-/

@[expose] public section


universe u

variable {V : Type u} (G : SimpleGraph V) (K L M : Set V)

namespace SimpleGraph

/--
Definition of `ComponentCompl` / `ComponentCompl` 的定义

English:
abbreviation ComponentCompl
  body: (G.induce Kᶜ).ConnectedComponent

中文:
缩写 ComponentCompl
  定义体: (G.induce Kᶜ).ConnectedComponent

Depends on / 依赖: ConnectedComponent, G.induce, _eq_dite, decide_eq_true_eq, induce, simp_rw
-/
abbrev ComponentCompl :=
  (G.induce Kᶜ).ConnectedComponent

variable {G} {K L M}

/--
Definition of `componentComplMk` / `componentComplMk` 的定义

English:
abbreviation componentComplMk
  signature: (G : SimpleGraph V) {v : V} (vK : v ∉ K)
  body: connectedComponentMk (G.induce Kᶜ) ⟨v, vK⟩

中文:
缩写 componentComplMk
  签名: (G : 简单图 V) {v : V} (vK : v ∉ K)
  定义体: connectedComponentMk (G.induce Kᶜ) ⟨v, vK⟩

Depends on / 依赖: G.induce, connectedComponentMk, induce
-/
abbrev componentComplMk (G : SimpleGraph V) {v : V} (vK : v ∉ K) : G.ComponentCompl K :=
  connectedComponentMk (G.induce Kᶜ) ⟨v, vK⟩

/--
Definition of `ComponentCompl.supp` / `ComponentCompl.supp` 的定义

English:
definition ComponentCompl.supp
  signature: (C : G.ComponentCompl K)
  body: { v : V | exists h : v ∉ K, G.componentComplMk h = C }

@[ext]

中文:
定义 ComponentCompl.supp
  签名: (C : G.ComponentCompl K)
  定义体: { v : V | exists h : v ∉ K, G.componentComplMk h = C }

@[ext]

Depends on / 依赖: G.componentComplMk, componentComplMk, h.choose
-/
def ComponentCompl.supp (C : G.ComponentCompl K) : Set V :=
  { v : V | exists h : v ∉ K, G.componentComplMk h = C }

@[ext]
/--
theorem `ComponentCompl.supp_injective` / 定理 `ComponentCompl.supp_injective`

English:
theorem ComponentCompl.supp_injective
  proof: by
  refine ConnectedComponent.ind₂ ?_
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  simp only [Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq, ComponentCompl.supp] at h ⊢
  exact ((h v).mp ⟨hv, Reachable.refl _⟩).choose_spec

中文:
定理 ComponentCompl.supp_injective
  证明: by
  refine ConnectedComponent.ind₂ ?_
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  simp only [Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq, ComponentCompl.supp] at h ⊢
  exact ((h v).mp ⟨hv, Reachable.refl _⟩).choose_spec

Depends on / 依赖: ComponentCompl, ComponentCompl.supp, ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.ind, Reachable, Reachable.refl, Set.ext_iff, Set.mem_ofPred_eq, choose_spec, ext_iff, mem_ofPred_eq
-/
theorem ComponentCompl.supp_injective :
    Function.Injective (ComponentCompl.supp : G.ComponentCompl K -> Set V) := by
  refine ConnectedComponent.ind₂ ?_
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  simp only [Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq, ComponentCompl.supp] at h ⊢
  exact ((h v).mp ⟨hv, Reachable.refl _⟩).choose_spec

/--
theorem `ComponentCompl.supp_inj` / 定理 `ComponentCompl.supp_inj`

English:
theorem ComponentCompl.supp_inj
  given: {C D : G.ComponentCompl K}
  statement: C.supp = D.supp ↔ C = D
  proof: ComponentCompl.supp_injective.eq_iff

中文:
定理 ComponentCompl.supp_inj
  条件: {C D : G.ComponentCompl K}
  结论: C.supp = D.supp ↔ C = D
  证明: ComponentCompl.supp_injective.eq_iff

Depends on / 依赖: ComponentCompl, ComponentCompl.supp_injective.eq_iff, eq_iff, supp_injective
-/
theorem ComponentCompl.supp_inj {C D : G.ComponentCompl K} : C.supp = D.supp ↔ C = D :=
  ComponentCompl.supp_injective.eq_iff

/--
Instance `ComponentCompl.setLike` / 实例 `ComponentCompl.setLike`

English:
instance ComponentCompl.setLike
  signature: : SetLike (G.ComponentCompl K) V where
  body: ComponentCompl.supp
  coe_injective _ _ := ComponentCompl.supp_inj.mp

中文:
实例 ComponentCompl.setLike
  签名: : 集合状 (G.ComponentCompl K) V where
  定义体: ComponentCompl.supp
  coe_injective _ _ := ComponentCompl.supp_inj.mp

Depends on / 依赖: ComponentCompl, ComponentCompl.supp, _eq_dite, dite_true, simp_rw
-/
instance ComponentCompl.setLike : SetLike (G.ComponentCompl K) V where
  coe := ComponentCompl.supp
  coe_injective _ _ := ComponentCompl.supp_inj.mp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (G.ComponentCompl K)
  body: .ofSetLike (G.ComponentCompl K) V

@[simp]

中文:
实例 :
  签名: 偏序 (G.ComponentCompl K)
  定义体: .ofSetLike (G.ComponentCompl K) V

@[simp]

Depends on / 依赖: ComponentCompl, G.ComponentCompl, _eq_dite, dite_true, exists_eq_true_of_isSome_find, ofSetLike, simp_rw
-/
instance : PartialOrder (G.ComponentCompl K) := .ofSetLike (G.ComponentCompl K) V

@[simp]
/--
theorem `ComponentCompl.mem_supp_iff` / 定理 `ComponentCompl.mem_supp_iff`

English:
theorem ComponentCompl.mem_supp_iff
  given: {v : V} {C : ComponentCompl G K}
  proof: Iff.rfl

中文:
定理 ComponentCompl.mem_supp_iff
  条件: {v : V} {C : ComponentCompl G K}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ComponentCompl.mem_supp_iff {v : V} {C : ComponentCompl G K} :
    v in C ↔ exists vK : v ∉ K, G.componentComplMk vK = C :=
  Iff.rfl

/--
theorem `componentComplMk_mem` / 定理 `componentComplMk_mem`

English:
theorem componentComplMk_mem
  given: (G : SimpleGraph V) {v : V} (vK : v ∉ K)
  statement: v in G.componentComplMk vK
  proof: ⟨vK, rfl⟩

中文:
定理 componentComplMk_mem
  条件: (G : 简单图 V) {v : V} (vK : v ∉ K)
  结论: v in G.componentComplMk vK
  证明: ⟨vK, rfl⟩
-/
theorem componentComplMk_mem (G : SimpleGraph V) {v : V} (vK : v ∉ K) : v in G.componentComplMk vK :=
  ⟨vK, rfl⟩

/--
theorem `componentComplMk_eq_of_adj` / 定理 `componentComplMk_eq_of_adj`

English:
theorem componentComplMk_eq_of_adj
  statement: (G : SimpleGraph V) {v w : V} (vK : v ∉ K) (wK : w ∉ K)
  proof: by
  rw [ConnectedComponent.eq]
  apply Adj.reachable
  exact a

中文:
定理 componentComplMk_eq_of_adj
  结论: (G : 简单图 V) {v w : V} (vK : v ∉ K) (wK : w ∉ K)
  证明: by
  rw [ConnectedComponent.eq]
  apply Adj.reachable
  exact a

Depends on / 依赖: Adj.reachable, ConnectedComponent, ConnectedComponent.eq, reachable
-/
theorem componentComplMk_eq_of_adj (G : SimpleGraph V) {v w : V} (vK : v ∉ K) (wK : w ∉ K)
    (a : G.Adj v w) : G.componentComplMk vK = G.componentComplMk wK := by
  rw [ConnectedComponent.eq]
  apply Adj.reachable
  exact a

/--
Instance `componentCompl_nonempty_of_infinite` / 实例 `componentCompl_nonempty_of_infinite`

English:
instance componentCompl_nonempty_of_infinite
  signature: (G : SimpleGraph V) [Infinite V] (K : Finset V)
  body: let ⟨_, kK⟩ := K.finite_toSet.infinite_compl.nonempty
  ⟨componentComplMk _ kK⟩

中文:
实例 componentCompl_nonempty_of_infinite
  签名: (G : 简单图 V) [无限 V] (K : 有限集 V)
  定义体: let ⟨_, kK⟩ := K.finite_toSet.infinite_compl.nonempty
  ⟨componentComplMk _ kK⟩

Depends on / 依赖: K.finite_toSet.infinite_compl.nonempty, componentComplMk, finite_toSet, infinite_compl, nonempty
-/
instance componentCompl_nonempty_of_infinite (G : SimpleGraph V) [Infinite V] (K : Finset V) :
    Nonempty (G.ComponentCompl K) :=
  let ⟨_, kK⟩ := K.finite_toSet.infinite_compl.nonempty
  ⟨componentComplMk _ kK⟩

namespace ComponentCompl

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {β : Sort*} (f : forall ⦃v⦄ (_ : v ∉ K), β)
  body: ConnectedComponent.lift (fun vv => f vv.prop) fun v w p => by
    induction p with
    | nil => rintro _; rfl
    | cons a q ih => rename_i u v w; rintro h'; exact (h u.prop v.prop a).trans (ih h'.of_cons)

@[elab_as_elim]

中文:
定义 lift
  签名: {β : 类型层*} (f : 对任意 ⦃v⦄ (_ : v ∉ K), β)
  定义体: ConnectedComponent.lift (fun vv => f vv.prop) fun v w p => by
    induction p with
    | nil => rintro _; rfl
    | cons a q ih => rename_i u v w; rintro h'; exact (h u.prop v.prop a).trans (ih h'.of_cons)

@[elab_as_elim]
-/
protected def lift {β : Sort*} (f : forall ⦃v⦄ (_ : v ∉ K), β)
    (h : forall ⦃v w⦄ (hv : v ∉ K) (hw : w ∉ K), G.Adj v w -> f hv = f hw) : G.ComponentCompl K -> β :=
  ConnectedComponent.lift (fun vv => f vv.prop) fun v w p => by
    induction p with
    | nil => rintro _; rfl
    | cons a q ih => rename_i u v w; rintro h'; exact (h u.prop v.prop a).trans (ih h'.of_cons)

@[elab_as_elim]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {β : G.ComponentCompl K -> Prop}
  proof: by
  apply ConnectedComponent.ind
  exact fun ⟨v, vnK⟩ => f vnK

中文:
定理 ind
  结论: {β : G.ComponentCompl K -> 命题}
  证明: by
  apply ConnectedComponent.ind
  exact fun ⟨v, vnK⟩ => f vnK
-/
protected theorem ind {β : G.ComponentCompl K -> Prop}
    (f : forall ⦃v⦄ (hv : v ∉ K), β (G.componentComplMk hv)) : forall C : G.ComponentCompl K, β C := by
  apply ConnectedComponent.ind
  exact fun ⟨v, vnK⟩ => f vnK

/--
Definition of `coeGraph` / `coeGraph` 的定义

English:
abbreviation coeGraph
  signature: (C : ComponentCompl G K)
  body: G.induce (C : Set V)

中文:
缩写 coeGraph
  签名: (C : ComponentCompl G K)
  定义体: G.induce (C : Set V)
-/
protected abbrev coeGraph (C : ComponentCompl G K) : SimpleGraph C :=
  G.induce (C : Set V)

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {C D : G.ComponentCompl K}
  statement: (C : Set V) = (D : Set V) ↔ C = D
  proof: SetLike.coe_set_eq

@[simp]

中文:
定理 coe_inj
  条件: {C D : G.ComponentCompl K}
  结论: (C : 集合 V) = (D : 集合 V) ↔ C = D
  证明: SetLike.coe_set_eq

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
theorem coe_inj {C D : G.ComponentCompl K} : (C : Set V) = (D : Set V) ↔ C = D :=
  SetLike.coe_set_eq

@[simp]
/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (C : G.ComponentCompl K)
  statement: (C : Set V).Nonempty
  proof: C.ind fun v vnK => ⟨v, vnK, rfl⟩

中文:
定理 nonempty
  条件: (C : G.ComponentCompl K)
  结论: (C : 集合 V).非空
  证明: C.ind fun v vnK => ⟨v, vnK, rfl⟩
-/
protected theorem nonempty (C : G.ComponentCompl K) : (C : Set V).Nonempty :=
  C.ind fun v vnK => ⟨v, vnK, rfl⟩

/--
theorem `exists_eq_mk` / 定理 `exists_eq_mk`

English:
theorem exists_eq_mk
  given: (C : G.ComponentCompl K)
  proof: C.nonempty

中文:
定理 存在_eq_mk
  条件: (C : G.ComponentCompl K)
  证明: C.nonempty
-/
protected theorem exists_eq_mk (C : G.ComponentCompl K) :
    exists (v : _) (h : v ∉ K), G.componentComplMk h = C :=
  C.nonempty

/--
theorem `disjoint_right` / 定理 `disjoint_right`

English:
theorem disjoint_right
  given: (C : G.ComponentCompl K)
  statement: Disjoint K C
  proof: by
  rw [Set.disjoint_iff]
  exact fun v ⟨vK, vC⟩ => vC.choose vK

中文:
定理 disjoint_right
  条件: (C : G.ComponentCompl K)
  结论: Disjoint K C
  证明: by
  rw [Set.disjoint_iff]
  exact fun v ⟨vK, vC⟩ => vC.choose vK
-/
protected theorem disjoint_right (C : G.ComponentCompl K) : Disjoint K C := by
  rw [Set.disjoint_iff]
  exact fun v ⟨vK, vC⟩ => vC.choose vK

/--
theorem `notMem_of_mem` / 定理 `notMem_of_mem`

English:
theorem notMem_of_mem
  given: {C : G.ComponentCompl K} {c : V} (cC : c in C)
  statement: c ∉ K
  proof: fun cK =>
  Set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩

中文:
定理 notMem_of_mem
  条件: {C : G.ComponentCompl K} {c : V} (cC : c in C)
  结论: c ∉ K
  证明: fun cK =>
  Set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩
-/
theorem notMem_of_mem {C : G.ComponentCompl K} {c : V} (cC : c in C) : c ∉ K := fun cK =>
  Set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩

/--
theorem `pairwise_disjoint` / 定理 `pairwise_disjoint`

English:
theorem pairwise_disjoint
  proof: by
  rintro C D ne
  rw [Set.disjoint_iff]
  exact fun u ⟨uC, uD⟩ => ne (uC.choose_spec.symm.trans uD.choose_spec)

中文:
定理 pairwise_disjoint
  证明: by
  rintro C D ne
  rw [Set.disjoint_iff]
  exact fun u ⟨uC, uD⟩ => ne (uC.choose_spec.symm.trans uD.choose_spec)
-/
protected theorem pairwise_disjoint :
    Pairwise fun C D : G.ComponentCompl K => Disjoint (C : Set V) (D : Set V) := by
  rintro C D ne
  rw [Set.disjoint_iff]
  exact fun u ⟨uC, uD⟩ => ne (uC.choose_spec.symm.trans uD.choose_spec)

/--
theorem `mem_of_adj` / 定理 `mem_of_adj`

English:
theorem mem_of_adj
  statement: forall {C : G.ComponentCompl K} (c d : V), c in C -> d ∉ K -> G.Adj c d -> d in C
  proof: fun {C} c d ⟨cnK, h⟩ dnK cd =>
  ⟨dnK, by
    rw [← h]; rw [ConnectedComponent.eq]
    exact Adj.reachable cd.symm⟩

中文:
定理 mem_of_adj
  结论: 对任意 {C : G.ComponentCompl K} (c d : V), c in C -> d ∉ K -> G.伴随 c d -> d in C
  证明: fun {C} c d ⟨cnK, h⟩ dnK cd =>
  ⟨dnK, by
    rw [← h]; rw [ConnectedComponent.eq]
    exact Adj.reachable cd.symm⟩

Depends on / 依赖: Adj.reachable, ConnectedComponent, ConnectedComponent.eq, cd.symm, reachable
-/
theorem mem_of_adj : forall {C : G.ComponentCompl K} (c d : V), c in C -> d ∉ K -> G.Adj c d -> d in C :=
  fun {C} c d ⟨cnK, h⟩ dnK cd =>
  ⟨dnK, by
    rw [← h]; rw [ConnectedComponent.eq]
    exact Adj.reachable cd.symm⟩

/--
theorem `exists_adj_boundary_pair` / 定理 `exists_adj_boundary_pair`

English:
theorem exists_adj_boundary_pair
  given: (Gc : G.Preconnected) (hK : K.Nonempty)
  proof: by
  refine ComponentCompl.ind fun v vnK => ?_
  let C : G.ComponentCompl K := G.componentComplMk vnK
  let dis := Set.disjoint_iff.mp C.disjoint_right
  by_contra! h
  suffices Set.univ = (C : Set V) by exact dis ⟨hK.choose_spec, this ▸ Set.mem_univ hK.some⟩
  symm
  rw [Set.eq_univ_iff_forall]
  rintro u
  by_contra unC
  obtain ⟨p⟩ := Gc v u
  obtain ⟨⟨⟨x, y⟩, xy⟩, -, xC, ynC⟩ :=
    p.exists_boundary_dart (C : Set V) (G.componentComplMk_mem vnK) unC
  exact ynC (mem_of_adj x y xC (fun yK : y in K => h ⟨x, y⟩ xC yK xy) xy)

中文:
定理 存在_adj_boundary_pair
  条件: (Gc : G.预连通) (hK : K.非空)
  证明: by
  refine ComponentCompl.ind fun v vnK => ?_
  let C : G.ComponentCompl K := G.componentComplMk vnK
  let dis := Set.disjoint_iff.mp C.disjoint_right
  by_contra! h
  suffices Set.univ = (C : Set V) by exact dis ⟨hK.choose_spec, this ▸ Set.mem_univ hK.some⟩
  symm
  rw [Set.eq_univ_iff_forall]
  rintro u
  by_contra unC
  obtain ⟨p⟩ := Gc v u
  obtain ⟨⟨⟨x, y⟩, xy⟩, -, xC, ynC⟩ :=
    p.exists_boundary_dart (C : Set V) (G.componentComplMk_mem vnK) unC
  exact ynC (mem_of_adj x y xC (fun yK : y in K => h ⟨x, y⟩ xC yK xy) xy)

Depends on / 依赖: C.disjoint_right, ComponentCompl, ComponentCompl.ind, G.ComponentCompl, G.componentComplMk, G.componentComplMk_mem, Set.disjoint_iff.mp, Set.eq_univ_iff_forall, Set.mem_univ, Set.univ, choose_spec, componentComplMk, componentComplMk_mem, disjoint_iff, disjoint_right, eq_univ_iff_forall, exists_boundary_dart, hK.choose_spec, hK.some, mem_of_adj
-/
theorem exists_adj_boundary_pair (Gc : G.Preconnected) (hK : K.Nonempty) :
    forall C : G.ComponentCompl K, exists ck : V × V, ck.1 in C ∧ ck.2 in K ∧ G.Adj ck.1 ck.2 := by
  refine ComponentCompl.ind fun v vnK => ?_
  let C : G.ComponentCompl K := G.componentComplMk vnK
  let dis := Set.disjoint_iff.mp C.disjoint_right
  by_contra! h
  suffices Set.univ = (C : Set V) by exact dis ⟨hK.choose_spec, this ▸ Set.mem_univ hK.some⟩
  symm
  rw [Set.eq_univ_iff_forall]
  rintro u
  by_contra unC
  obtain ⟨p⟩ := Gc v u
  obtain ⟨⟨⟨x, y⟩, xy⟩, -, xC, ynC⟩ :=
    p.exists_boundary_dart (C : Set V) (G.componentComplMk_mem vnK) unC
  exact ynC (mem_of_adj x y xC (fun yK : y in K => h ⟨x, y⟩ xC yK xy) xy)

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: (h : K subseteq L) (C : G.ComponentCompl L)
  body: C.map induceHom Hom.id Set.compl_subset_compl.2 h

中文:
缩写 hom
  签名: (h : K subseteq L) (C : G.ComponentCompl L)
  定义体: C.map induceHom Hom.id Set.compl_subset_compl.2 h

Depends on / 依赖: C.map, Hom.id, Set.compl_subset_compl, compl_subset_compl, induceHom
-/
abbrev hom (h : K subseteq L) (C : G.ComponentCompl L) : G.ComponentCompl K :=
C.map induceHom Hom.id Set.compl_subset_compl.2 h

/--
theorem `subset_hom` / 定理 `subset_hom`

English:
theorem subset_hom
  given: (C : G.ComponentCompl L) (h : K subseteq L)
  statement: (C : Set V) subseteq (C.hom h : Set V)
  proof: by
  rintro c ⟨cL, rfl⟩
  exact ⟨fun h' => cL (h h'), rfl⟩

中文:
定理 subset_hom
  条件: (C : G.ComponentCompl L) (h : K subseteq L)
  结论: (C : 集合 V) subseteq (C.hom h : 集合 V)
  证明: by
  rintro c ⟨cL, rfl⟩
  exact ⟨fun h' => cL (h h'), rfl⟩
-/
theorem subset_hom (C : G.ComponentCompl L) (h : K subseteq L) : (C : Set V) subseteq (C.hom h : Set V) := by
  rintro c ⟨cL, rfl⟩
  exact ⟨fun h' => cL (h h'), rfl⟩

/--
theorem `_root_.SimpleGraph.componentComplMk_mem_hom` / 定理 `_root_.SimpleGraph.componentComplMk_mem_hom`

English:
theorem _root_.SimpleGraph.componentComplMk_mem_hom
  proof: subset_hom (G.componentComplMk vK) h (G.componentComplMk_mem vK)

中文:
定理 _root_.简单图.componentComplMk_mem_hom
  证明: subset_hom (G.componentComplMk vK) h (G.componentComplMk_mem vK)

Depends on / 依赖: G.componentComplMk, G.componentComplMk_mem, componentComplMk, componentComplMk_mem, subset_hom
-/
theorem _root_.SimpleGraph.componentComplMk_mem_hom
    (G : SimpleGraph V) {v : V} (vK : v ∉ K) (h : L subseteq K) :
    v in (G.componentComplMk vK).hom h :=
  subset_hom (G.componentComplMk vK) h (G.componentComplMk_mem vK)

/--
theorem `hom_eq_iff_le` / 定理 `hom_eq_iff_le`

English:
theorem hom_eq_iff_le
  given: (C : G.ComponentCompl L) (h : K subseteq L) (D : G.ComponentCompl K)
  proof: ⟨fun h' => h' ▸ C.subset_hom h, C.ind fun _ vnL vD => (vD ⟨vnL, rfl⟩).choose_spec⟩

中文:
定理 hom_eq_iff_le
  条件: (C : G.ComponentCompl L) (h : K subseteq L) (D : G.ComponentCompl K)
  证明: ⟨fun h' => h' ▸ C.subset_hom h, C.ind fun _ vnL vD => (vD ⟨vnL, rfl⟩).choose_spec⟩

Depends on / 依赖: C.ind, C.subset_hom, choose_spec, subset_hom
-/
theorem hom_eq_iff_le (C : G.ComponentCompl L) (h : K subseteq L) (D : G.ComponentCompl K) :
    C.hom h = D ↔ (C : Set V) subseteq (D : Set V) :=
  ⟨fun h' => h' ▸ C.subset_hom h, C.ind fun _ vnL vD => (vD ⟨vnL, rfl⟩).choose_spec⟩

/--
theorem `hom_eq_iff_not_disjoint` / 定理 `hom_eq_iff_not_disjoint`

English:
theorem hom_eq_iff_not_disjoint
  given: (C : G.ComponentCompl L) (h : K subseteq L) (D : G.ComponentCompl K)
  proof: by
  rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    refine C.ind fun x xnL => ?_
    exact ⟨x, ⟨xnL, rfl⟩, ⟨fun xK => xnL (h xK), rfl⟩⟩
  · refine C.ind fun x xnL => ?_
    rintro ⟨x, ⟨_, e₁⟩, _, rfl⟩
    rw [← e₁]
    rfl

中文:
定理 hom_eq_iff_not_disjoint
  条件: (C : G.ComponentCompl L) (h : K subseteq L) (D : G.ComponentCompl K)
  证明: by
  rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    refine C.ind fun x xnL => ?_
    exact ⟨x, ⟨xnL, rfl⟩, ⟨fun xK => xnL (h xK), rfl⟩⟩
  · refine C.ind fun x xnL => ?_
    rintro ⟨x, ⟨_, e₁⟩, _, rfl⟩
    rw [← e₁]
    rfl

Depends on / 依赖: C.ind, Set.not_disjoint_iff, not_disjoint_iff
-/
theorem hom_eq_iff_not_disjoint (C : G.ComponentCompl L) (h : K subseteq L) (D : G.ComponentCompl K) :
    C.hom h = D ↔ ¬Disjoint (C : Set V) (D : Set V) := by
  rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    refine C.ind fun x xnL => ?_
    exact ⟨x, ⟨xnL, rfl⟩, ⟨fun xK => xnL (h xK), rfl⟩⟩
  · refine C.ind fun x xnL => ?_
    rintro ⟨x, ⟨_, e₁⟩, _, rfl⟩
    rw [← e₁]
    rfl

/--
theorem `hom_refl` / 定理 `hom_refl`

English:
theorem hom_refl
  given: (C : G.ComponentCompl L)
  statement: C.hom (subset_refl L) = C
  proof: by
  change C.map _ = C
  rw [induceHom_id G Lᶜ]; rw [ConnectedComponent.map_id]

中文:
定理 hom_refl
  条件: (C : G.ComponentCompl L)
  结论: C.hom (subset_refl L) = C
  证明: by
  change C.map _ = C
  rw [induceHom_id G Lᶜ]; rw [ConnectedComponent.map_id]

Depends on / 依赖: C.map, ConnectedComponent, ConnectedComponent.map_id, induceHom_id, map_id
-/
theorem hom_refl (C : G.ComponentCompl L) : C.hom (subset_refl L) = C := by
  change C.map _ = C
  rw [induceHom_id G Lᶜ]; rw [ConnectedComponent.map_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `hom_trans` / 定理 `hom_trans`

English:
theorem hom_trans
  given: (C : G.ComponentCompl L) (h : K subseteq L) (h' : M subseteq K)
  proof: by
  change C.map _ = (C.map _).map _
  rw [ConnectedComponent.map_comp]; rw [induceHom_comp]
  rfl

中文:
定理 hom_trans
  条件: (C : G.ComponentCompl L) (h : K subseteq L) (h' : M subseteq K)
  证明: by
  change C.map _ = (C.map _).map _
  rw [ConnectedComponent.map_comp]; rw [induceHom_comp]
  rfl

Depends on / 依赖: C.map, ConnectedComponent, ConnectedComponent.map_comp, induceHom_comp, map_comp
-/
theorem hom_trans (C : G.ComponentCompl L) (h : K subseteq L) (h' : M subseteq K) :
    C.hom (h'.trans h) = (C.hom h).hom h' := by
  change C.map _ = (C.map _).map _
  rw [ConnectedComponent.map_comp]; rw [induceHom_comp]
  rfl

/--
theorem `hom_mk` / 定理 `hom_mk`

English:
theorem hom_mk
  given: {v : V} (vnL : v ∉ L) (h : K subseteq L)
  proof: rfl

中文:
定理 hom_mk
  条件: {v : V} (vnL : v ∉ L) (h : K subseteq L)
  证明: rfl
-/
theorem hom_mk {v : V} (vnL : v ∉ L) (h : K subseteq L) :
    (G.componentComplMk vnL).hom h = G.componentComplMk (Set.notMem_subset h vnL) :=
  rfl

/--
theorem `hom_infinite` / 定理 `hom_infinite`

English:
theorem hom_infinite
  given: (C : G.ComponentCompl L) (h : K subseteq L) (Cinf : (C : Set V).Infinite)
  proof: Set.Infinite.mono (C.subset_hom h) Cinf

中文:
定理 hom_infinite
  条件: (C : G.ComponentCompl L) (h : K subseteq L) (Cinf : (C : 集合 V).无限)
  证明: Set.Infinite.mono (C.subset_hom h) Cinf

Depends on / 依赖: C.subset_hom, Infinite, Set.Infinite.mono, subset_hom
-/
theorem hom_infinite (C : G.ComponentCompl L) (h : K subseteq L) (Cinf : (C : Set V).Infinite) :
    (C.hom h : Set V).Infinite :=
  Set.Infinite.mono (C.subset_hom h) Cinf

/--
theorem `infinite_iff_in_all_ranges` / 定理 `infinite_iff_in_all_ranges`

English:
theorem infinite_iff_in_all_ranges
  given: {K : Finset V} (C : G.ComponentCompl K)
  proof: by
  classical
    constructor
    · rintro Cinf L h
      obtain ⟨v, ⟨vK, rfl⟩, vL⟩ := Set.Infinite.nonempty (Set.Infinite.sdiff Cinf L.finite_toSet)
      exact ⟨componentComplMk _ vL, rfl⟩
    · rintro h Cfin
      obtain ⟨D, e⟩ := h (K union Cfin.toFinset) Finset.subset_union_left
      obtain ⟨v, vD⟩ := D.nonempty
      let Ddis := D.disjoint_right
      simp_rw [Finset.coe_union, Set.Finite.coe_toFinset, Set.disjoint_union_left,
        Set.disjoint_iff] at Ddis
      exact Ddis.right ⟨(ComponentCompl.hom_eq_iff_le _ _ _).mp e vD, vD⟩

中文:
定理 infinite_iff_in_all_ranges
  条件: {K : 有限集 V} (C : G.ComponentCompl K)
  证明: by
  classical
    constructor
    · rintro Cinf L h
      obtain ⟨v, ⟨vK, rfl⟩, vL⟩ := Set.Infinite.nonempty (Set.Infinite.sdiff Cinf L.finite_toSet)
      exact ⟨componentComplMk _ vL, rfl⟩
    · rintro h Cfin
      obtain ⟨D, e⟩ := h (K union Cfin.toFinset) Finset.subset_union_left
      obtain ⟨v, vD⟩ := D.nonempty
      let Ddis := D.disjoint_right
      simp_rw [Finset.coe_union, Set.Finite.coe_toFinset, Set.disjoint_union_left,
        Set.disjoint_iff] at Ddis
      exact Ddis.right ⟨(ComponentCompl.hom_eq_iff_le _ _ _).mp e vD, vD⟩

Depends on / 依赖: Cfin.toFinset, ComponentCompl, ComponentCompl.hom_eq_iff_le, D.disjoint_right, D.nonempty, Ddis.right, Finite, Finset, Finset.coe_union, Finset.subset_union_left, Infinite, L.finite_toSet, Set.Finite.coe_toFinset, Set.Infinite.nonempty, Set.Infinite.sdiff, Set.disjoint_iff, Set.disjoint_union_left, classical, coe_toFinset, coe_union
-/
theorem infinite_iff_in_all_ranges {K : Finset V} (C : G.ComponentCompl K) :
    C.supp.Infinite ↔ forall (L) (h : K subseteq L), exists D : G.ComponentCompl L, D.hom h = C := by
  classical
    constructor
    · rintro Cinf L h
      obtain ⟨v, ⟨vK, rfl⟩, vL⟩ := Set.Infinite.nonempty (Set.Infinite.sdiff Cinf L.finite_toSet)
      exact ⟨componentComplMk _ vL, rfl⟩
    · rintro h Cfin
      obtain ⟨D, e⟩ := h (K union Cfin.toFinset) Finset.subset_union_left
      obtain ⟨v, vD⟩ := D.nonempty
      let Ddis := D.disjoint_right
      simp_rw [Finset.coe_union, Set.Finite.coe_toFinset, Set.disjoint_union_left,
        Set.disjoint_iff] at Ddis
      exact Ddis.right ⟨(ComponentCompl.hom_eq_iff_le _ _ _).mp e vD, vD⟩

end ComponentCompl

/--
Instance `componentCompl_finite` / 实例 `componentCompl_finite`

English:
instance componentCompl_finite
  signature: [LocallyFinite G] [Gpc : Fact G.Preconnected] (K : Finset V)
  body: by
  classical
  rcases K.eq_empty_or_nonempty with rfl | h
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  · dsimp [ComponentCompl]
    rw [Finset.coe_empty]; rw [Set.compl_empty]
    have := Gpc.out.subsingleton_connectedComponent
    exact Finite.of_equiv _ (induceUnivIso G).connectedComponentEquiv.symm
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  · let touch (C : G.ComponentCompl K) : {v : V | exists k : V, k in K ∧ G.Adj k v} :=
      let p := C.exists_adj_boundary_pair Gpc.out h
      ⟨p.choose.1, p.choose.2, p.choose_spec.2.1, p.choose_spec.2.2.symm⟩
    -- `touch` is injective
    have touch_inj : touch.Injective := fun C D h' => ComponentCompl.pairwise_disjoint.eq
      (Set.not_disjoint_iff.mpr ⟨touch C, (C.exists_adj_boundary_pair Gpc.out h).choose_spec.1,
                                 h'.symm ▸ (D.exists_adj_boundary_pair Gpc.out h).choose_spec.1⟩)
    -- `touch` has finite range
    have : Finite (Set.range touch) := by
      refine @Subtype.finite _ (Set.Finite.to_subtype ?_) _
      apply Set.Finite.ofFinset (K.biUnion (fun v => G.neighborFinset v))
      simp only [Finset.mem_biUnion, mem_neighborFinset, Set.mem_ofPred_eq, implies_true]
    -- hence `touch` has a finite domain
    apply Finite.of_injective_finite_range touch_inj

中文:
实例 componentCompl_finite
  签名: [局部有限 G] [Gpc : Fact G.预连通] (K : 有限集 V)
  定义体: by
  classical
  rcases K.eq_empty_or_nonempty with rfl | h
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  · dsimp [ComponentCompl]
    rw [Finset.coe_empty]; rw [Set.compl_empty]
    have := Gpc.out.subsingleton_connectedComponent
    exact Finite.of_equiv _ (induceUnivIso G).connectedComponentEquiv.symm
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  · let touch (C : G.ComponentCompl K) : {v : V | exists k : V, k in K ∧ G.Adj k v} :=
      let p := C.exists_adj_boundary_pair Gpc.out h
      ⟨p.choose.1, p.choose.2, p.choose_spec.2.1, p.choose_spec.2.2.symm⟩
    -- `touch` is injective
    have touch_inj : touch.Injective := fun C D h' => ComponentCompl.pairwise_disjoint.eq
      (Set.not_disjoint_iff.mpr ⟨touch C, (C.exists_adj_boundary_pair Gpc.out h).choose_spec.1,
                                 h'.symm ▸ (D.exists_adj_boundary_pair Gpc.out h).choose_spec.1⟩)
    -- `touch` has finite range
    have : Finite (Set.range touch) := by
      refine @Subtype.finite _ (Set.Finite.to_subtype ?_) _
      apply Set.Finite.ofFinset (K.biUnion (fun v => G.neighborFinset v))
      simp only [Finset.mem_biUnion, mem_neighborFinset, Set.mem_ofPred_eq, implies_true]
    -- hence `touch` has a finite domain
    apply Finite.of_injective_finite_range touch_inj

Depends on / 依赖: K.eq_empty_or_nonempty, classical, eq_empty_or_nonempty
-/
instance componentCompl_finite [LocallyFinite G] [Gpc : Fact G.Preconnected] (K : Finset V) :
    Finite (G.ComponentCompl K) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | h
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  · dsimp [ComponentCompl]
    rw [Finset.coe_empty]; rw [Set.compl_empty]
    have := Gpc.out.subsingleton_connectedComponent
    exact Finite.of_equiv _ (induceUnivIso G).connectedComponentEquiv.symm
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  · let touch (C : G.ComponentCompl K) : {v : V | exists k : V, k in K ∧ G.Adj k v} :=
      let p := C.exists_adj_boundary_pair Gpc.out h
      ⟨p.choose.1, p.choose.2, p.choose_spec.2.1, p.choose_spec.2.2.symm⟩
    -- `touch` is injective
    have touch_inj : touch.Injective := fun C D h' => ComponentCompl.pairwise_disjoint.eq
      (Set.not_disjoint_iff.mpr ⟨touch C, (C.exists_adj_boundary_pair Gpc.out h).choose_spec.1,
                                 h'.symm ▸ (D.exists_adj_boundary_pair Gpc.out h).choose_spec.1⟩)
    -- `touch` has finite range
    have : Finite (Set.range touch) := by
      refine @Subtype.finite _ (Set.Finite.to_subtype ?_) _
      apply Set.Finite.ofFinset (K.biUnion (fun v => G.neighborFinset v))
      simp only [Finset.mem_biUnion, mem_neighborFinset, Set.mem_ofPred_eq, implies_true]
    -- hence `touch` has a finite domain
    apply Finite.of_injective_finite_range touch_inj

section Ends

variable (G)

open CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/--
The functor assigning, to a finite set in `V`, the set of connected components in its complement.
-/
@[simps]
/--
Definition of `componentComplFunctor` / `componentComplFunctor` 的定义

English:
definition componentComplFunctor
  signature: : (Finset V)ᵒᵖ ⥤ Type u where
  body: G.ComponentCompl K.unop
  map f := ↾(ComponentCompl.hom (le_of_op_hom f))
  map_id _ := by
    ext
    simp [ComponentCompl.hom_refl]
  map_comp {_ Y Z} h h' := by
    ext C
    simp

中文:
定义 componentComplFunctor
  签名: : (有限集 V)ᵒᵖ ⥤ 类型u where
  定义体: G.ComponentCompl K.unop
  map f := ↾(ComponentCompl.hom (le_of_op_hom f))
  map_id _ := by
    ext
    simp [ComponentCompl.hom_refl]
  map_comp {_ Y Z} h h' := by
    ext C
    simp

Depends on / 依赖: ComponentCompl, G.ComponentCompl, K.unop
-/
def componentComplFunctor : (Finset V)ᵒᵖ ⥤ Type u where
  obj K := G.ComponentCompl K.unop
  map f := ↾(ComponentCompl.hom (le_of_op_hom f))
  map_id _ := by
    ext
    simp [ComponentCompl.hom_refl]
  map_comp {_ Y Z} h h' := by
    ext C
    simp

/--
Definition of `«end»` / `«end»` 的定义

English:
definition «end»
  body: (componentComplFunctor G).sections

中文:
定义 «end»
  定义体: (componentComplFunctor G).sections
-/
protected def «end» :=
  (componentComplFunctor G).sections

/--
theorem `end_hom_mk_of_mk` / 定理 `end_hom_mk_of_mk`

English:
theorem end_hom_mk_of_mk
  statement: {s} (sec : s in G.end) {K L : (Finset V)ᵒᵖ} (h : L ⟶ K) {v : V}
  proof: by
  rw [← sec h]; rw [hs]
  apply ComponentCompl.hom_mk _ (le_of_op_hom h)

中文:
定理 end_hom_mk_of_mk
  结论: {s} (sec : s in G.end) {K L : (有限集 V)ᵒᵖ} (h : L ⟶ K) {v : V}
  证明: by
  rw [← sec h]; rw [hs]
  apply ComponentCompl.hom_mk _ (le_of_op_hom h)

Depends on / 依赖: ComponentCompl, ComponentCompl.hom_mk, hom_mk, le_of_op_hom
-/
theorem end_hom_mk_of_mk {s} (sec : s in G.end) {K L : (Finset V)ᵒᵖ} (h : L ⟶ K) {v : V}
    (vnL : v ∉ L.unop) (hs : s L = G.componentComplMk vnL) :
    s K = G.componentComplMk (Set.notMem_subset (le_of_op_hom h) vnL) := by
  rw [← sec h]; rw [hs]
  apply ComponentCompl.hom_mk _ (le_of_op_hom h)

/--
theorem `infinite_iff_in_eventualRange` / 定理 `infinite_iff_in_eventualRange`

English:
theorem infinite_iff_in_eventualRange
  given: {K : (Finset V)ᵒᵖ} (C : G.componentComplFunctor.obj K)
  proof: by
  simp only [C.infinite_iff_in_all_ranges, CategoryTheory.Functor.eventualRange, Set.mem_iInter,
    Set.mem_range, componentComplFunctor_map]
  exact
    ⟨fun h Lop KL => h Lop.unop (le_of_op_hom KL), fun h L KL =>
      h (Opposite.op L) (opHomOfLE KL)⟩

中文:
定理 infinite_iff_in_eventualRange
  条件: {K : (有限集 V)ᵒᵖ} (C : G.componentComplFunctor.obj K)
  证明: by
  simp only [C.infinite_iff_in_all_ranges, CategoryTheory.Functor.eventualRange, Set.mem_iInter,
    Set.mem_range, componentComplFunctor_map]
  exact
    ⟨fun h Lop KL => h Lop.unop (le_of_op_hom KL), fun h L KL =>
      h (Opposite.op L) (opHomOfLE KL)⟩

Depends on / 依赖: C.infinite_iff_in_all_ranges, CategoryTheory, CategoryTheory.Functor.eventualRange, Functor, Lop.unop, Opposite, Opposite.op, Set.mem_iInter, Set.mem_range, componentComplFunctor_map, eventualRange, infinite_iff_in_all_ranges, le_of_op_hom, mem_iInter, mem_range, opHomOfLE
-/
theorem infinite_iff_in_eventualRange {K : (Finset V)ᵒᵖ} (C : G.componentComplFunctor.obj K) :
    C.supp.Infinite ↔ C in G.componentComplFunctor.eventualRange K := by
  simp only [C.infinite_iff_in_all_ranges, CategoryTheory.Functor.eventualRange, Set.mem_iInter,
    Set.mem_range, componentComplFunctor_map]
  exact
    ⟨fun h Lop KL => h Lop.unop (le_of_op_hom KL), fun h L KL =>
      h (Opposite.op L) (opHomOfLE KL)⟩

end Ends

end SimpleGraph
