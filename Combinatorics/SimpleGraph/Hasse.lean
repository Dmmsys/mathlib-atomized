/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.SuccPred.Relation
public import Mathlib.Tactic.FinCases

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `CovBy`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `SimpleGraph.hasse`: Hasse diagram of an order.
* `SimpleGraph.pathGraph`: Path graph on `n` vertices.
-/

@[expose] public section


open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type*)

section Preorder

variable [Preorder α]

/--
Definition of `hasse` / `hasse` 的定义

English:
definition hasse
  signature: : SimpleGraph α where
  body: a ⋖ b ∨ b ⋖ a

中文:
定义 hasse
  签名: : SimpleGraph α where
  定义体: a ⋖ b ∨ b ⋖ a
-/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a

variable {α β} {a b : α}

@[simp]
/--
theorem `hasse_adj` / 定理 `hasse_adj`

English:
theorem hasse_adj
  statement: (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a
  proof: Iff.rfl

中文:
定理 hasse_adj
  结论: (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl

/--
Definition of `hasseDualIso` / `hasseDualIso` 的定义

English:
definition hasseDualIso
  signature: : hasse αᵒᵈ ≃g hasse α
  body: { ofDual with map_rel_iff' := by simp [or_comm] }

@[simp]

中文:
定义 hasseDualIso
  签名: : hasse αᵒᵈ ≃g hasse α
  定义体: { ofDual with map_rel_iff' := by simp [or_comm] }

@[simp]

Depends on / 依赖: map_rel_iff, ofDual, or_comm
-/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with map_rel_iff' := by simp [or_comm] }

@[simp]
/--
theorem `hasseDualIso_apply` / 定理 `hasseDualIso_apply`

English:
theorem hasseDualIso_apply
  given: (a : αᵒᵈ)
  statement: hasseDualIso a = ofDual a
  proof: rfl

@[simp]

中文:
定理 hasseDualIso_apply
  条件: (a : αᵒᵈ)
  结论: hasseDualIso a = ofDual a
  证明: rfl

@[simp]
-/
theorem hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl

@[simp]
/--
theorem `hasseDualIso_symm_apply` / 定理 `hasseDualIso_symm_apply`

English:
theorem hasseDualIso_symm_apply
  given: (a : α)
  statement: hasseDualIso.symm a = toDual a
  proof: rfl

中文:
定理 hasseDualIso_symm_apply
  条件: (a : α)
  结论: hasseDualIso.symm a = toDual a
  证明: rfl
-/
theorem hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl

/--
theorem `cliqueFree_hasse_three` / 定理 `cliqueFree_hasse_three`

English:
theorem cliqueFree_hasse_three
  statement: (hasse α).CliqueFree 3
  proof: by
  classical
  intro s ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := s.card_eq_three.mp hcard
  have := hc (by simp) (by simp) hab
  have := hc (by simp) (by simp) hbc
  have := hc (by simp) (by simp) hac
  grind [hasse_adj, CovBy]

中文:
定理 cliqueFree_hasse_three
  结论: (hasse α).CliqueFree 3
  证明: by
  classical
  intro s ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := s.card_eq_three.mp hcard
  have := hc (by simp) (by simp) hab
  have := hc (by simp) (by simp) hbc
  have := hc (by simp) (by simp) hac
  grind [hasse_adj, CovBy]

Depends on / 依赖: card_eq_three, classical, hasse_adj, s.card_eq_three.mp
-/
theorem cliqueFree_hasse_three : (hasse α).CliqueFree 3 := by
  classical
  intro s ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := s.card_eq_three.mp hcard
  have := hc (by simp) (by simp) hab
  have := hc (by simp) (by simp) hbc
  have := hc (by simp) (by simp) hac
  grind [hasse_adj, CovBy]

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

@[simp]
/--
theorem `hasse_prod` / 定理 `hasse_prod`

English:
theorem hasse_prod
  statement: hasse (α × β) = hasse α □ hasse β
  proof: by
  ext x y
  simp_rw [boxProd_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]

中文:
定理 hasse_prod
  结论: hasse (α × β) = hasse α □ hasse β
  证明: by
  ext x y
  simp_rw [boxProd_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]

Depends on / 依赖: Prod.covBy_iff, boxProd_adj, covBy_iff, eq_comm, hasse_adj, or_and_right, or_or_or_comm, simp_rw
-/
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by
  ext x y
  simp_rw [boxProd_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/--
theorem `hasse_preconnected_of_succ` / 定理 `hasse_preconnected_of_succ`

English:
theorem hasse_preconnected_of_succ
  given: [SuccOrder α] [IsSuccArchimedean α]
  statement: (hasse α).Preconnected
  proof: fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covBy_succ_of_not_isMax hc.2.not_isMax)
fun c hc => Or.inr covBy_succ_of_not_isMax hc.2.not_isMax

中文:
定理 hasse_preconnected_of_succ
  条件: [SuccOrder α] [IsSuccArchimedean α]
  结论: (hasse α).Preconnected
  证明: fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covBy_succ_of_not_isMax hc.2.not_isMax)
fun c hc => Or.inr covBy_succ_of_not_isMax hc.2.not_isMax

Depends on / 依赖: Or.inl, Or.inr, covBy_succ_of_not_isMax, not_isMax, reachable_iff_reflTransGen, reflTransGen_of_succ
-/
theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covBy_succ_of_not_isMax hc.2.not_isMax)
fun c hc => Or.inr covBy_succ_of_not_isMax hc.2.not_isMax

/--
theorem `hasse_preconnected_of_pred` / 定理 `hasse_preconnected_of_pred`

English:
theorem hasse_preconnected_of_pred
  given: [PredOrder α] [IsPredArchimedean α]
  statement: (hasse α).Preconnected
  proof: fun a b => by
  rw [reachable_iff_reflTransGen]; rw [← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covBy_of_not_isMin hc.1.not_isMin)
fun c hc => Or.inr pred_covBy_of_not_isMin hc.1.not_isMin

中文:
定理 hasse_preconnected_of_pred
  条件: [PredOrder α] [IsPredArchimedean α]
  结论: (hasse α).Preconnected
  证明: fun a b => by
  rw [reachable_iff_reflTransGen]; rw [← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covBy_of_not_isMin hc.1.not_isMin)
fun c hc => Or.inr pred_covBy_of_not_isMin hc.1.not_isMin

Depends on / 依赖: Or.inl, Or.inr, not_isMin, pred_covBy_of_not_isMin, reachable_iff_reflTransGen, reflTransGen_of_pred, reflTransGen_swap
-/
theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]; rw [← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covBy_of_not_isMin hc.1.not_isMin)
fun c hc => Or.inr pred_covBy_of_not_isMin hc.1.not_isMin

end LinearOrder

/--
Definition of `pathGraph` / `pathGraph` 的定义

English:
definition pathGraph
  signature: (n : Nat)
  body: hasse _

中文:
定义 pathGraph
  签名: (n : 自然数)
  定义体: hasse _
-/
def pathGraph (n : Nat) : SimpleGraph (Fin n) :=
  hasse _

/--
theorem `pathGraph_adj` / 定理 `pathGraph_adj`

English:
theorem pathGraph_adj
  given: {n : Nat} {u v : Fin n}
  proof: by simp [pathGraph, hasse]

中文:
定理 pathGraph_adj
  条件: {n : 自然数} {u v : Fin n}
  证明: by simp [pathGraph, hasse]

Depends on / 依赖: pathGraph
-/
theorem pathGraph_adj {n : Nat} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by simp [pathGraph, hasse]

/--
theorem `pathGraph_preconnected` / 定理 `pathGraph_preconnected`

English:
theorem pathGraph_preconnected
  given: (n : Nat)
  statement: (pathGraph n).Preconnected
  proof: hasse_preconnected_of_succ _

中文:
定理 pathGraph_preconnected
  条件: (n : 自然数)
  结论: (pathGraph n).Preconnected
  证明: hasse_preconnected_of_succ _

Depends on / 依赖: hasse_preconnected_of_succ
-/
theorem pathGraph_preconnected (n : Nat) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _

/--
theorem `pathGraph_connected` / 定理 `pathGraph_connected`

English:
theorem pathGraph_connected
  given: (n : Nat)
  statement: (pathGraph (n + 1)).Connected
  proof: ⟨pathGraph_preconnected _⟩

中文:
定理 pathGraph_connected
  条件: (n : 自然数)
  结论: (pathGraph (n + 1)).Connected
  证明: ⟨pathGraph_preconnected _⟩

Depends on / 依赖: pathGraph_preconnected
-/
theorem pathGraph_connected (n : Nat) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩

/--
theorem `pathGraph_two_eq_top` / 定理 `pathGraph_two_eq_top`

English:
theorem pathGraph_two_eq_top
  statement: pathGraph 2 = ⊤
  proof: by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph]

中文:
定理 pathGraph_two_eq_top
  结论: pathGraph 2 = ⊤
  证明: by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph]

Depends on / 依赖: fin_cases, pathGraph
-/
theorem pathGraph_two_eq_top : pathGraph 2 = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph]

namespace Walk

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} (w : G.Walk u v)

/--
Definition of `pathGraphHomToSubgraph` / `pathGraphHomToSubgraph` 的定义

English:
definition pathGraphHomToSubgraph
  signature: : pathGraph (w.length + 1) ->g w.toSubgraph.coe where
  body: ⟨w.support[n], w.mem_verts_toSubgraph.mpr List.getElem_mem _⟩
  map_rel' {a b} h := by
    grind [support_getElem_eq_getVert, Subgraph.coe_adj, pathGraph_adj, toSubgraph_adj_getVert,
      Subgraph.Adj.symm]

中文:
定义 pathGraphHomToSubgraph
  签名: : pathGraph (w.length + 1) ->g w.toSubgraph.coe where
  定义体: ⟨w.support[n], w.mem_verts_toSubgraph.mpr List.getElem_mem _⟩
  map_rel' {a b} h := by
    grind [support_getElem_eq_getVert, Subgraph.coe_adj, pathGraph_adj, toSubgraph_adj_getVert,
      Subgraph.Adj.symm]

Depends on / 依赖: List.getElem_mem, getElem_mem, mem_verts_toSubgraph, support, w.mem_verts_toSubgraph.mpr, w.support
-/
def pathGraphHomToSubgraph : pathGraph (w.length + 1) ->g w.toSubgraph.coe where
toFun n := ⟨w.support[n], w.mem_verts_toSubgraph.mpr List.getElem_mem _⟩
  map_rel' {a b} h := by
    grind [support_getElem_eq_getVert, Subgraph.coe_adj, pathGraph_adj, toSubgraph_adj_getVert,
      Subgraph.Adj.symm]

/--
Definition of `pathGraphHom` / `pathGraphHom` 的定义

English:
definition pathGraphHom
  signature: : pathGraph (w.length + 1) ->g G
  body: w.toSubgraph.hom.comp w.pathGraphHomToSubgraph

中文:
定义 pathGraphHom
  签名: : pathGraph (w.length + 1) ->g G
  定义体: w.toSubgraph.hom.comp w.pathGraphHomToSubgraph

Depends on / 依赖: pathGraphHomToSubgraph, toSubgraph, w.pathGraphHomToSubgraph, w.toSubgraph.hom.comp
-/
def pathGraphHom : pathGraph (w.length + 1) ->g G :=
  w.toSubgraph.hom.comp w.pathGraphHomToSubgraph

variable {w} in
/--
Definition of `IsPath.pathGraphIsoToSubgraph` / `IsPath.pathGraphIsoToSubgraph` 的定义

English:
definition IsPath.pathGraphIsoToSubgraph
  signature: (hw : w.IsPath)
  body: w.pathGraphHomToSubgraph
  invFun v := ⟨w.support.idxOf v.val, by grind [w.mem_verts_toSubgraph]⟩
  left_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup]
  right_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk]
  map_rel_iff' := by
    refine ⟨fun hadj => ?_, w.pa

中文:
定义 IsPath.pathGraphIsoToSubgraph
  签名: (hw : w.IsPath)
  定义体: w.pathGraphHomToSubgraph
  invFun v := ⟨w.support.idxOf v.val, by grind [w.mem_verts_toSubgraph]⟩
  left_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup]
  right_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk]
  map_rel_iff' := by
    refine ⟨fun hadj => ?_, w.pa

Depends on / 依赖: pathGraphHomToSubgraph, w.pathGraphHomToSubgraph
-/
def IsPath.pathGraphIsoToSubgraph (hw : w.IsPath) :
    pathGraph (w.length + 1) ≃g w.toSubgraph.coe where
  toFun := w.pathGraphHomToSubgraph
  invFun v := ⟨w.support.idxOf v.val, by grind [w.mem_verts_toSubgraph]⟩
  left_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup]
  right_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk]
  map_rel_iff' := by
    refine ⟨fun hadj => ?_, w.pathGraphHomToSubgraph.map_rel'⟩
    grind [w.toSubgraph_adj_iff.mp hadj, pathGraph_adj, getVert_eq_getD_support,
      pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup.getElem_inj_iff]

variable {w} in
/--
Definition of `IsPath.pathGraphCopy` / `IsPath.pathGraphCopy` 的定义

English:
definition IsPath.pathGraphCopy
  signature: (hw : w.IsPath)
  body: w.toSubgraph.coeCopy.comp hw.pathGraphIsoToSubgraph.toCopy

中文:
定义 IsPath.pathGraphCopy
  签名: (hw : w.IsPath)
  定义体: w.toSubgraph.coeCopy.comp hw.pathGraphIsoToSubgraph.toCopy

Depends on / 依赖: coeCopy, hw.pathGraphIsoToSubgraph.toCopy, pathGraphIsoToSubgraph, toCopy, toSubgraph, w.toSubgraph.coeCopy.comp
-/
def IsPath.pathGraphCopy (hw : w.IsPath) : Copy (pathGraph <| w.length + 1) G :=
  w.toSubgraph.coeCopy.comp hw.pathGraphIsoToSubgraph.toCopy

variable {w} in
omit [DecidableEq V] in
/--
theorem `IsPath.isContained_pathGraph` / 定理 `IsPath.isContained_pathGraph`

English:
theorem IsPath.isContained_pathGraph
  given: (hw : w.IsPath)
  statement: pathGraph (w.length + 1) ⊑ G
  proof: by
  classical
  exact ⟨hw.pathGraphCopy⟩

中文:
定理 IsPath.isContained_pathGraph
  条件: (hw : w.IsPath)
  结论: pathGraph (w.length + 1) ⊑ G
  证明: by
  classical
  exact ⟨hw.pathGraphCopy⟩

Depends on / 依赖: classical, hw.pathGraphCopy, pathGraphCopy
-/
theorem IsPath.isContained_pathGraph (hw : w.IsPath) : pathGraph (w.length + 1) ⊑ G := by
  classical
  exact ⟨hw.pathGraphCopy⟩

end Walk

end SimpleGraph
