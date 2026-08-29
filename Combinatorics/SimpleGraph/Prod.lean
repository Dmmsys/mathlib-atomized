/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Graph products

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `SimpleGraph.boxProd`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/

@[expose] public section

variable {α β γ V V₁ V₂ W W₁ W₂ : Type*}

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β}

/--
Definition of `boxProd` / `boxProd` 的定义

English:
definition boxProd
  signature: (G : SimpleGraph α) (H : SimpleGraph β)
  body: G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm.symm x y := by simp [eq_comm, adj_comm]

中文:
定义 boxProd
  签名: (G : 简单图 α) (H : 简单图 β)
  定义体: G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm.symm x y := by simp [eq_comm, adj_comm]

Depends on / 依赖: G.Adj, H.Adj
-/
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm.symm x y := by simp [eq_comm, adj_comm]

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
infixl:70 " □ " => boxProd

@[simp]
/--
theorem `boxProd_adj` / 定理 `boxProd_adj`

English:
theorem boxProd_adj
  given: {x y : α × β}
  proof: Iff.rfl

中文:
定理 boxProd_adj
  条件: {x y : α × β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem boxProd_adj {x y : α × β} :
    (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl

/--
theorem `boxProd_adj_left` / 定理 `boxProd_adj_left`

English:
theorem boxProd_adj_left
  given: {a₁ : α} {b : β} {a₂ : α}
  proof: by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]

中文:
定理 boxProd_adj_left
  条件: {a₁ : α} {b : β} {a₂ : α}
  证明: by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]

Depends on / 依赖: SimpleGraph, SimpleGraph.irrefl, and_true, boxProd_adj, false_and, irrefl, or_false
-/
theorem boxProd_adj_left {a₁ : α} {b : β} {a₂ : α} :
    (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]

/--
theorem `boxProd_adj_right` / 定理 `boxProd_adj_right`

English:
theorem boxProd_adj_right
  given: {a : α} {b₁ b₂ : β}
  statement: (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂
  proof: by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]

中文:
定理 boxProd_adj_right
  条件: {a : α} {b₁ b₂ : β}
  结论: (G □ H).伴随 (a, b₁) (a, b₂) ↔ H.伴随 b₁ b₂
  证明: by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]

Depends on / 依赖: SimpleGraph, SimpleGraph.irrefl, and_true, boxProd_adj, false_and, false_or, irrefl
-/
theorem boxProd_adj_right {a : α} {b₁ b₂ : β} : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]

/--
theorem `neighborSet_boxProd` / 定理 `neighborSet_boxProd`

English:
theorem neighborSet_boxProd
  given: (x : α × β)
  proof: by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm]

中文:
定理 neighborSet_boxProd
  条件: (x : α × β)
  证明: by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm]

Depends on / 依赖: Set.mem_prod, Set.mem_singleton_iff, Set.mem_union, and_comm, boxProd_adj, eq_comm, mem_neighborSet, mem_prod, mem_singleton_iff, mem_union
-/
theorem neighborSet_boxProd (x : α × β) :
    (G □ H).neighborSet x = G.neighborSet x.1 ×ˢ {x.2} union {x.1} ×ˢ H.neighborSet x.2 := by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm]

variable (G H)

/-- The box product is commutative up to isomorphism. `Equiv.prodComm` as a graph isomorphism. -/
@[simps!]
/--
Definition of `boxProdComm` / `boxProdComm` 的定义

English:
definition boxProdComm
  signature: : G □ H ≃g H □ G
  body: ⟨Equiv.prodComm _ _, or_comm⟩

中文:
定义 boxProdComm
  签名: : G □ H ≃g H □ G
  定义体: ⟨Equiv.prodComm _ _, or_comm⟩

Depends on / 依赖: Equiv.prodComm, or_comm, prodComm
-/
def boxProdComm : G □ H ≃g H □ G := ⟨Equiv.prodComm _ _, or_comm⟩

/-- The box product is associative up to isomorphism. `Equiv.prodAssoc` as a graph isomorphism. -/
@[simps!]
/--
Definition of `boxProdAssoc` / `boxProdAssoc` 的定义

English:
definition boxProdAssoc
  signature: (I : SimpleGraph γ)
  body: ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩

中文:
定义 boxProdAssoc
  签名: (I : 简单图 γ)
  定义体: ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩

Depends on / 依赖: Equiv.prodAssoc, Equiv.prodAssoc_apply, Prod.ext_iff, and_assoc, and_comm, boxProd_adj, ext_iff, or_and_right, or_assoc, prodAssoc, prodAssoc_apply, x.fst.fst
-/
def boxProdAssoc (I : SimpleGraph γ) : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩

/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps]
/--
Definition of `boxProdLeft` / `boxProdLeft` 的定义

English:
definition boxProdLeft
  signature: (b : β)
  body: (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left

中文:
定义 boxProdLeft
  签名: (b : β)
  定义体: (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left
-/
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun a := (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left

/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps]
/--
Definition of `boxProdRight` / `boxProdRight` 的定义

English:
definition boxProdRight
  signature: (a : α)
  body: Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right

中文:
定义 boxProdRight
  签名: (a : α)
  定义体: Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right

Depends on / 依赖: Prod.mk
-/
def boxProdRight (a : α) : H ↪g G □ H where
  toFun := Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right

namespace Iso

/-- The box product distributes over the disjoint sum of graphs. -/
@[simps!, simps toEquiv]
/--
Definition of `boxProdSumDistrib` / `boxProdSumDistrib` 的定义

English:
definition boxProdSumDistrib
  signature: (G : SimpleGraph V) (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
  body: .prodSumDistrib ..
  map_rel_iff' := by simp

中文:
定义 boxProdSumDistrib
  签名: (G : 简单图 V) (H₁ : 简单图 W₁) (H₂ : 简单图 W₂)
  定义体: .prodSumDistrib ..
  map_rel_iff' := by simp

Depends on / 依赖: prodSumDistrib
-/
def boxProdSumDistrib (G : SimpleGraph V) (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
    G □ (H₁ oplusg H₂) ≃g G □ H₁ oplusg G □ H₂ where
  toEquiv := .prodSumDistrib ..
  map_rel_iff' := by simp

/-- The box product distributes over the disjoint sum of graphs. -/
@[simps!, simps toEquiv]
/--
Definition of `sumBoxProdDistrib` / `sumBoxProdDistrib` 的定义

English:
definition sumBoxProdDistrib
  signature: (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (H : SimpleGraph W)
  body: .sumProdDistrib ..
  map_rel_iff' := by simp

中文:
定义 sumBoxProdDistrib
  签名: (G₁ : 简单图 V₁) (G₂ : 简单图 V₂) (H : 简单图 W)
  定义体: .sumProdDistrib ..
  map_rel_iff' := by simp

Depends on / 依赖: sumProdDistrib
-/
def sumBoxProdDistrib (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (H : SimpleGraph W) :
    (G₁ oplusg G₂) □ H ≃g G₁ □ H oplusg G₂ □ H where
  toEquiv := .sumProdDistrib ..
  map_rel_iff' := by simp

end Iso

namespace Walk

variable {G}

/--
Definition of `boxProdLeft` / `boxProdLeft` 的定义

English:
definition boxProdLeft
  signature: {a₁ a₂ : α} (b : β)
  body: Walk.map (G.boxProdLeft H b).toHom

中文:
定义 boxProdLeft
  签名: {a₁ a₂ : α} (b : β)
  定义体: Walk.map (G.boxProdLeft H b).toHom
-/
protected def boxProdLeft {a₁ a₂ : α} (b : β) : G.Walk a₁ a₂ -> (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom

variable (G) {H}

/--
Definition of `boxProdRight` / `boxProdRight` 的定义

English:
definition boxProdRight
  signature: {b₁ b₂ : β} (a : α)
  body: Walk.map (G.boxProdRight H a).toHom

中文:
定义 boxProdRight
  签名: {b₁ b₂ : β} (a : α)
  定义体: Walk.map (G.boxProdRight H a).toHom
-/
protected def boxProdRight {b₁ b₂ : β} (a : α) : H.Walk b₁ b₂ -> (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom

variable {G}

/--
Definition of `ofBoxProdLeft` / `ofBoxProdLeft` 的定义

English:
definition ofBoxProdLeft
  signature: [DecidableEq β] [DecidableRel G.Adj] {x y : α × β}

中文:
定义 ofBoxProdLeft
  签名: [DecidableEq β] [DecidableRel G.伴随] {x y : α × β}
-/
def ofBoxProdLeft [DecidableEq β] [DecidableRel G.Adj] {x y : α × β} :
    (G □ H).Walk x y -> G.Walk x.1 y.1
  | nil => nil
  | cons h w =>
    Or.by_cases h
      (fun hG => w.ofBoxProdLeft.cons hG.1)
      (fun hH => hH.2 ▸ w.ofBoxProdLeft)

/--
Definition of `ofBoxProdRight` / `ofBoxProdRight` 的定义

English:
definition ofBoxProdRight
  signature: [DecidableEq α] [DecidableRel H.Adj] {x y : α × β}

中文:
定义 ofBoxProdRight
  签名: [DecidableEq α] [DecidableRel H.伴随] {x y : α × β}
-/
def ofBoxProdRight [DecidableEq α] [DecidableRel H.Adj] {x y : α × β} :
    (G □ H).Walk x y -> H.Walk x.2 y.2
  | nil => nil
  | cons h w =>
    (Or.symm h).by_cases
      (fun hH => w.ofBoxProdRight.cons hH.1)
      (fun hG => hG.2 ▸ w.ofBoxProdRight)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofBoxProdLeft_boxProdLeft` / 定理 `ofBoxProdLeft_boxProdLeft`

English:
theorem ofBoxProdLeft_boxProdLeft
  given: [DecidableEq β] [DecidableRel G.Adj] {a₁ a₂ : α} {b : β}

中文:
定理 ofBoxProdLeft_boxProdLeft
  条件: [DecidableEq β] [DecidableRel G.伴随] {a₁ a₂ : α} {b : β}
-/
theorem ofBoxProdLeft_boxProdLeft [DecidableEq β] [DecidableRel G.Adj] {a₁ a₂ : α} {b : β} :
    forall (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdLeft]; rw [map_cons]; rw [ofBoxProdLeft]; rw [Or.by_cases]; rw [dif_pos]; rw [← Walk.boxProdLeft]
    · simp [ofBoxProdLeft_boxProdLeft]
    · exact ⟨h, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofBoxProdRight_boxProdRight` / 定理 `ofBoxProdRight_boxProdRight`

English:
theorem ofBoxProdRight_boxProdRight
  given: [DecidableEq α] [DecidableRel G.Adj] {a b₁ b₂ : α}

中文:
定理 ofBoxProdRight_boxProdRight
  条件: [DecidableEq α] [DecidableRel G.伴随] {a b₁ b₂ : α}
-/
theorem ofBoxProdRight_boxProdRight [DecidableEq α] [DecidableRel G.Adj] {a b₁ b₂ : α} :
    forall (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdRight]; rw [map_cons]; rw [ofBoxProdRight]; rw [Or.by_cases]; rw [dif_pos]; rw [←
      Walk.boxProdRight]
    · simp [ofBoxProdRight_boxProdRight]
    · exact ⟨h, rfl⟩

/--
lemma `length_boxProd` / 引理 `length_boxProd`

English:
lemma length_boxProd
  statement: {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β]
  proof: by
  match w with
  | .nil => simp [ofBoxProdLeft, ofBoxProdRight]
  | .cons x w' => next c =>
    unfold ofBoxProdLeft ofBoxProdRight
    rw [length_cons]; rw [length_boxProd w']
    have disj : (G.Adj a₁ c.1 ∧ b₁ = c.2) ∨ (H.Adj b₁ c.2 ∧ a₁ = c.1) := by simp_all
    rcases disj with h₁ | h₂
    · simp only [h₁, and_self, ↓reduceDIte, length_cons, Or.by_cases]
      rw [add_comm]; rw [add_comm w'.ofBoxProdLeft.length 1]; rw [add_assoc]
      congr <;> simp [h₁.2.symm]
    · simp only [h₂, add_assoc, Or.by_cases]
      congr <;> simp [h₂.2.symm]

中文:
引理 length_boxProd
  结论: {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β]
  证明: by
  match w with
  | .nil => simp [ofBoxProdLeft, ofBoxProdRight]
  | .cons x w' => next c =>
    unfold ofBoxProdLeft ofBoxProdRight
    rw [length_cons]; rw [length_boxProd w']
    have disj : (G.Adj a₁ c.1 ∧ b₁ = c.2) ∨ (H.Adj b₁ c.2 ∧ a₁ = c.1) := by simp_all
    rcases disj with h₁ | h₂
    · simp only [h₁, and_self, ↓reduceDIte, length_cons, Or.by_cases]
      rw [add_comm]; rw [add_comm w'.ofBoxProdLeft.length 1]; rw [add_assoc]
      congr <;> simp [h₁.2.symm]
    · simp only [h₂, add_assoc, Or.by_cases]
      congr <;> simp [h₂.2.symm]

Depends on / 依赖: G.Adj, H.Adj, Or.by_cases, add_assoc, add_comm, and_self, length, length_boxProd, length_cons, ofBoxProdLeft, ofBoxProdLeft.length, ofBoxProdRight, reduceDIte
-/
lemma length_boxProd {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (w : (G □ H).Walk (a₁, b₁) (a₂, b₂)) :
    w.length = w.ofBoxProdLeft.length + w.ofBoxProdRight.length := by
  match w with
  | .nil => simp [ofBoxProdLeft, ofBoxProdRight]
  | .cons x w' => next c =>
    unfold ofBoxProdLeft ofBoxProdRight
    rw [length_cons]; rw [length_boxProd w']
    have disj : (G.Adj a₁ c.1 ∧ b₁ = c.2) ∨ (H.Adj b₁ c.2 ∧ a₁ = c.1) := by simp_all
    rcases disj with h₁ | h₂
    · simp only [h₁, and_self, ↓reduceDIte, length_cons, Or.by_cases]
      rw [add_comm]; rw [add_comm w'.ofBoxProdLeft.length 1]; rw [add_assoc]
      congr <;> simp [h₁.2.symm]
    · simp only [h₂, add_assoc, Or.by_cases]
      congr <;> simp [h₂.2.symm]

end Walk

variable {G H}

/--
theorem `Preconnected.boxProd` / 定理 `Preconnected.boxProd`

English:
theorem Preconnected.boxProd
  given: (hG : G.Preconnected) (hH : H.Preconnected)
  proof: by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

中文:
定理 预连通.boxProd
  条件: (hG : G.预连通) (hH : H.预连通)
  证明: by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩
-/
protected theorem Preconnected.boxProd (hG : G.Preconnected) (hH : H.Preconnected) :
    (G □ H).Preconnected := by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

/--
theorem `Preconnected.ofBoxProdLeft` / 定理 `Preconnected.ofBoxProdLeft`

English:
theorem Preconnected.ofBoxProdLeft
  given: [Nonempty β] (h : (G □ H).Preconnected)
  proof: by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩

中文:
定理 预连通.ofBoxProdLeft
  条件: [非空 β] (h : (G □ H).预连通)
  证明: by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩
-/
protected theorem Preconnected.ofBoxProdLeft [Nonempty β] (h : (G □ H).Preconnected) :
    G.Preconnected := by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩

/--
theorem `Preconnected.ofBoxProdRight` / 定理 `Preconnected.ofBoxProdRight`

English:
theorem Preconnected.ofBoxProdRight
  given: [Nonempty α] (h : (G □ H).Preconnected)
  proof: by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩

中文:
定理 预连通.ofBoxProdRight
  条件: [非空 α] (h : (G □ H).预连通)
  证明: by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩
-/
protected theorem Preconnected.ofBoxProdRight [Nonempty α] (h : (G □ H).Preconnected) :
    H.Preconnected := by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩

/--
theorem `Connected.boxProd` / 定理 `Connected.boxProd`

English:
theorem Connected.boxProd
  given: (hG : G.Connected) (hH : H.Connected)
  statement: (G □ H).Connected
  proof: by
  have := hG.nonempty
  have := hH.nonempty
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩

中文:
定理 连通.boxProd
  条件: (hG : G.连通) (hH : H.连通)
  结论: (G □ H).连通
  证明: by
  have := hG.nonempty
  have := hH.nonempty
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩
-/
protected theorem Connected.boxProd (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  have := hG.nonempty
  have := hH.nonempty
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩

/--
theorem `Connected.ofBoxProdLeft` / 定理 `Connected.ofBoxProdLeft`

English:
theorem Connected.ofBoxProdLeft
  given: (h : (G □ H).Connected)
  statement: G.Connected
  proof: by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdLeft⟩

中文:
定理 连通.ofBoxProdLeft
  条件: (h : (G □ H).连通)
  结论: G.连通
  证明: by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdLeft⟩
-/
protected theorem Connected.ofBoxProdLeft (h : (G □ H).Connected) : G.Connected := by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdLeft⟩

/--
theorem `Connected.ofBoxProdRight` / 定理 `Connected.ofBoxProdRight`

English:
theorem Connected.ofBoxProdRight
  given: (h : (G □ H).Connected)
  statement: H.Connected
  proof: by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdRight⟩

@[simp]

中文:
定理 连通.ofBoxProdRight
  条件: (h : (G □ H).连通)
  结论: H.连通
  证明: by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdRight⟩

@[simp]
-/
protected theorem Connected.ofBoxProdRight (h : (G □ H).Connected) : H.Connected := by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdRight⟩

@[simp]
/--
theorem `connected_boxProd` / 定理 `connected_boxProd`

English:
theorem connected_boxProd
  statement: (G □ H).Connected ↔ G.Connected ∧ H.Connected
  proof: ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩

中文:
定理 connected_boxProd
  结论: (G □ H).连通 ↔ G.连通 ∧ H.连通
  证明: ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩

Depends on / 依赖: boxProd, h.ofBoxProdLeft, h.ofBoxProdRight, ofBoxProdLeft, ofBoxProdRight
-/
theorem connected_boxProd : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩

/--
Instance `boxProdFintypeNeighborSet` / 实例 `boxProdFintypeNeighborSet`

English:
instance boxProdFintypeNeighborSet
  signature: (x : α × β)
  body: Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
Finset.disjoint_product.mpr Or.inl neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y => by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighborFinset,
        mem_neighborSet, Equiv.refl_apply, boxProd_adj]
      simp only [eq_comm, and_comm])

中文:
实例 boxProdFintypeNeighborSet
  签名: (x : α × β)
  定义体: Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
Finset.disjoint_product.mpr Or.inl neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y => by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighborFinset,
        mem_neighborSet, Equiv.refl_apply, boxProd_adj]
      simp only [eq_comm, and_comm])

Depends on / 依赖: Equiv.refl, Equiv.refl_apply, Finset, Finset.disjoint_product.mpr, Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, Fintype, Fintype.ofEquiv, G.neighborFinset, H.neighborFinset, Or.inl, and_comm, boxProd_adj, disjUnion, disjoint_product, eq_comm, mem_disjUnion, mem_neighborFinset, mem_neighborSet
-/
instance boxProdFintypeNeighborSet (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] :
    Fintype ((G □ H).neighborSet x) :=
  Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
Finset.disjoint_product.mpr Or.inl neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y => by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighborFinset,
        mem_neighborSet, Equiv.refl_apply, boxProd_adj]
      simp only [eq_comm, and_comm])

/--
theorem `neighborFinset_boxProd` / 定理 `neighborFinset_boxProd`

English:
theorem neighborFinset_boxProd
  statement: (x : α × β)
  proof: by
  -- swap out the fintype instance for the canonical one
  let : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  convert_to (G □ H).neighborFinset x = _ using 2
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val

中文:
定理 neighborFinset_boxProd
  结论: (x : α × β)
  证明: by
  -- swap out the fintype instance for the canonical one
  let : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  convert_to (G □ H).neighborFinset x = _ using 2
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val
-/
theorem neighborFinset_boxProd (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).neighborFinset x =
      (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2)
        (Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _) := by
  -- swap out the fintype instance for the canonical one
  let : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  convert_to (G □ H).neighborFinset x = _ using 2
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val

/--
theorem `degree_boxProd` / 定理 `degree_boxProd`

English:
theorem degree_boxProd
  statement: (x : α × β)
  proof: by
  rw [degree]; rw [degree]; rw [degree]; rw [neighborFinset_boxProd]; rw [Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]

中文:
定理 degree_boxProd
  结论: (x : α × β)
  证明: by
  rw [degree]; rw [degree]; rw [degree]; rw [neighborFinset_boxProd]; rw [Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]

Depends on / 依赖: Finset, Finset.card_disjUnion, Finset.card_product, Finset.card_singleton, card_disjUnion, card_product, card_singleton, degree, mul_one, neighborFinset_boxProd, one_mul, simp_rw
-/
theorem degree_boxProd (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).degree x = G.degree x.1 + H.degree x.2 := by
  rw [degree]; rw [degree]; rw [degree]; rw [neighborFinset_boxProd]; rw [Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]

/--
lemma `reachable_boxProd` / 引理 `reachable_boxProd`

English:
lemma reachable_boxProd
  given: {x y : α × β}
  proof: by
  classical
  constructor
  · intro ⟨w⟩
    exact ⟨⟨w.ofBoxProdLeft⟩, ⟨w.ofBoxProdRight⟩⟩
  · intro ⟨⟨w₁⟩, ⟨w₂⟩⟩
    exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

中文:
引理 reachable_boxProd
  条件: {x y : α × β}
  证明: by
  classical
  constructor
  · intro ⟨w⟩
    exact ⟨⟨w.ofBoxProdLeft⟩, ⟨w.ofBoxProdRight⟩⟩
  · intro ⟨⟨w₁⟩, ⟨w₂⟩⟩
    exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

Depends on / 依赖: append, boxProdLeft, boxProdRight, classical, ofBoxProdLeft, ofBoxProdRight, w.ofBoxProdLeft, w.ofBoxProdRight
-/
lemma reachable_boxProd {x y : α × β} :
    (G □ H).Reachable x y ↔ G.Reachable x.1 y.1 ∧ H.Reachable x.2 y.2 := by
  classical
  constructor
  · intro ⟨w⟩
    exact ⟨⟨w.ofBoxProdLeft⟩, ⟨w.ofBoxProdRight⟩⟩
  · intro ⟨⟨w₁⟩, ⟨w₂⟩⟩
    exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `edist_boxProd` / 引理 `edist_boxProd`

English:
lemma edist_boxProd
  given: (x y : α × β)
  proof: by
  classical
  -- The case `(G □ H).edist x y = ⊤` is used twice, so better to factor it out.
  have top_case : (G □ H).edist x y = ⊤ ↔ G.edist x.1 y.1 = ⊤ ∨ H.edist x.2 y.2 = ⊤ := by
    simp_rw [← not_ne_iff, edist_ne_top_iff_reachable, reachable_boxProd, not_and_or]
  by_cases h : (G □ H).edist x y = ⊤
  · rw [top_case] at h
    aesop
  · have rGH : G.edist x.1 y.1 != ⊤ ∧ H.edist x.2 y.2 != ⊤ := by rw [top_case] at h; aesop
    have ⟨wG, hwG⟩ := exists_walk_of_edist_ne_top rGH.1
    have ⟨wH, hwH⟩ := exists_walk_of_edist_ne_top rGH.2
    let w_app := (wG.boxProdLeft _ _).append (wH.boxProdRight _ _)
    have w_len : w_app.length = wG.length + wH.length := by
      unfold w_app Walk.boxProdLeft Walk.boxProdRight; simp
    refine le_antisymm ?_ ?_
    · calc (G □ H).edist x y <= w_app.length := by exact edist_le _
          _ = wG.length + wH.length := by exact_mod_cast w_len
          _ = G.edist x.1 y.1 + H.edist x.2 y.2 := by simp only [hwG, hwH]
    · have ⟨w, hw⟩ := exists_walk_of_edist_ne_top h
      rw [← hw]; rw [Walk.length_boxProd]
      exact add_le_add (edist_le w.ofBoxProdLeft) (edist_le w.ofBoxProdRight)

中文:
引理 edist_boxProd
  条件: (x y : α × β)
  证明: by
  classical
  -- The case `(G □ H).edist x y = ⊤` is used twice, so better to factor it out.
  have top_case : (G □ H).edist x y = ⊤ ↔ G.edist x.1 y.1 = ⊤ ∨ H.edist x.2 y.2 = ⊤ := by
    simp_rw [← not_ne_iff, edist_ne_top_iff_reachable, reachable_boxProd, not_and_or]
  by_cases h : (G □ H).edist x y = ⊤
  · rw [top_case] at h
    aesop
  · have rGH : G.edist x.1 y.1 != ⊤ ∧ H.edist x.2 y.2 != ⊤ := by rw [top_case] at h; aesop
    have ⟨wG, hwG⟩ := exists_walk_of_edist_ne_top rGH.1
    have ⟨wH, hwH⟩ := exists_walk_of_edist_ne_top rGH.2
    let w_app := (wG.boxProdLeft _ _).append (wH.boxProdRight _ _)
    have w_len : w_app.length = wG.length + wH.length := by
      unfold w_app Walk.boxProdLeft Walk.boxProdRight; simp
    refine le_antisymm ?_ ?_
    · calc (G □ H).edist x y <= w_app.length := by exact edist_le _
          _ = wG.length + wH.length := by exact_mod_cast w_len
          _ = G.edist x.1 y.1 + H.edist x.2 y.2 := by simp only [hwG, hwH]
    · have ⟨w, hw⟩ := exists_walk_of_edist_ne_top h
      rw [← hw]; rw [Walk.length_boxProd]
      exact add_le_add (edist_le w.ofBoxProdLeft) (edist_le w.ofBoxProdRight)

Depends on / 依赖: classical
-/
lemma edist_boxProd (x y : α × β) :
    (G □ H).edist x y = G.edist x.1 y.1 + H.edist x.2 y.2 := by
  classical
  -- The case `(G □ H).edist x y = ⊤` is used twice, so better to factor it out.
  have top_case : (G □ H).edist x y = ⊤ ↔ G.edist x.1 y.1 = ⊤ ∨ H.edist x.2 y.2 = ⊤ := by
    simp_rw [← not_ne_iff, edist_ne_top_iff_reachable, reachable_boxProd, not_and_or]
  by_cases h : (G □ H).edist x y = ⊤
  · rw [top_case] at h
    aesop
  · have rGH : G.edist x.1 y.1 != ⊤ ∧ H.edist x.2 y.2 != ⊤ := by rw [top_case] at h; aesop
    have ⟨wG, hwG⟩ := exists_walk_of_edist_ne_top rGH.1
    have ⟨wH, hwH⟩ := exists_walk_of_edist_ne_top rGH.2
    let w_app := (wG.boxProdLeft _ _).append (wH.boxProdRight _ _)
    have w_len : w_app.length = wG.length + wH.length := by
      unfold w_app Walk.boxProdLeft Walk.boxProdRight; simp
    refine le_antisymm ?_ ?_
    · calc (G □ H).edist x y <= w_app.length := by exact edist_le _
          _ = wG.length + wH.length := by exact_mod_cast w_len
          _ = G.edist x.1 y.1 + H.edist x.2 y.2 := by simp only [hwG, hwH]
    · have ⟨w, hw⟩ := exists_walk_of_edist_ne_top h
      rw [← hw]; rw [Walk.length_boxProd]
      exact add_le_add (edist_le w.ofBoxProdLeft) (edist_le w.ofBoxProdRight)

end SimpleGraph
