/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Behrend
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to at most one triangle.

The lower bound comes from turning the big 3AP-free set from Behrend's construction into a graph
that has the property that every triangle gives a (possibly trivial) arithmetic progression on the
original set.

## Main declarations

* `ruzsaSzemerediNumberNat n`: Maximum number of edges a graph on `n` vertices can have such that
  each edge belongs to exactly one triangle.
* `ruzsaSzemerediNumberNat_asymptotic_lower_bound`: There exists a graph with `n` vertices and
  `Ω((n ^ 2 * exp (-4 * √(log n))))` edges such that each edge belongs to exactly one triangle.
-/

@[expose] public section

open Finset Nat Real SimpleGraph Sum3 SimpleGraph.TripartiteFromTriangles
open Fintype (card)
open scoped Pointwise

variable {α β : Type*}

/-! ### The Ruzsa-Szemerédi number -/

section ruzsaSzemerediNumber
variable [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {G H : SimpleGraph α}

variable (α) in
/--
Definition of `ruzsaSzemerediNumber` / `ruzsaSzemerediNumber` 的定义

English:
definition ruzsaSzemerediNumber
  signature: : Nat
  body: by
  classical
  exact Nat.findGreatest (fun m => exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) ((card α).choose 3)

中文:
定义 ruzsaSzemerediNumber
  签名: : 自然数
  定义体: by
  classical
  exact Nat.findGreatest (fun m => exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) ((card α).choose 3)

Depends on / 依赖: DecidableRel, G.Adj, G.LocallyLinear, G.cliqueFinset, LocallyLinear, Nat.findGreatest, SimpleGraph, classical, cliqueFinset, findGreatest
-/
noncomputable def ruzsaSzemerediNumber : Nat := by
  classical
  exact Nat.findGreatest (fun m => exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) ((card α).choose 3)

/--
lemma `ruzsaSzemerediNumber_le` / 引理 `ruzsaSzemerediNumber_le`

English:
lemma ruzsaSzemerediNumber_le
  statement: ruzsaSzemerediNumber α <= (card α).choose 3
  proof: by
  classical
  exact Nat.findGreatest_le _

中文:
引理 ruzsaSzemerediNumber_le
  结论: ruzsaSzemerediNumber α <= (card α).choose 3
  证明: by
  classical
  exact Nat.findGreatest_le _

Depends on / 依赖: Nat.findGreatest_le, classical, findGreatest_le
-/
lemma ruzsaSzemerediNumber_le : ruzsaSzemerediNumber α <= (card α).choose 3 := by
  classical
  exact Nat.findGreatest_le _

/--
lemma `ruzsaSzemerediNumber_spec` / 引理 `ruzsaSzemerediNumber_spec`

English:
lemma ruzsaSzemerediNumber_spec
  proof: by
  classical
  exact @Nat.findGreatest_spec _
    (fun m => exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) _ _ (Nat.zero_le _)
    ⟨⊥, inferInstance, by simp, locallyLinear_bot⟩

中文:
引理 ruzsaSzemerediNumber_spec
  证明: by
  classical
  exact @Nat.findGreatest_spec _
    (fun m => exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) _ _ (Nat.zero_le _)
    ⟨⊥, inferInstance, by simp, locallyLinear_bot⟩

Depends on / 依赖: DecidableRel, G.Adj, G.LocallyLinear, G.cliqueFinset, LocallyLinear, Nat.findGreatest_spec, Nat.zero_le, SimpleGraph, classical, cliqueFinset, findGreatest_spec, locallyLinear_bot, zero_le
-/
lemma ruzsaSzemerediNumber_spec :
    exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = ruzsaSzemerediNumber α ∧ G.LocallyLinear := by
  classical
  exact @Nat.findGreatest_spec _
    (fun m => exists (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) _ _ (Nat.zero_le _)
    ⟨⊥, inferInstance, by simp, locallyLinear_bot⟩

variable {m n : Nat}

/--
lemma `SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber` / 引理 `SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber`

English:
lemma SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber
  statement: [DecidableRel G.Adj]
  proof: by
  classical
  exact le_findGreatest card_cliqueFinset_le ⟨G, inferInstance, by congr, hG⟩

中文:
引理 简单图.LocallyLinear.le_ruzsaSzemerediNumber
  结论: [DecidableRel G.伴随]
  证明: by
  classical
  exact le_findGreatest card_cliqueFinset_le ⟨G, inferInstance, by congr, hG⟩

Depends on / 依赖: card_cliqueFinset_le, classical, le_findGreatest
-/
lemma SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : #(G.cliqueFinset 3) <= ruzsaSzemerediNumber α := by
  classical
  exact le_findGreatest card_cliqueFinset_le ⟨G, inferInstance, by congr, hG⟩

/--
lemma `ruzsaSzemerediNumber_mono` / 引理 `ruzsaSzemerediNumber_mono`

English:
lemma ruzsaSzemerediNumber_mono
  given: (f : α ↪ β)
  statement: ruzsaSzemerediNumber α <= ruzsaSzemerediNumber β
  proof: by
  classical
  refine findGreatest_mono ?_ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, _, rfl, hG⟩
  refine ⟨G.map f, inferInstance, ?_, hG.map _⟩
  rw [← card_map ⟨map f]; rw [Finset.map_injective _⟩]; rw [← cliqueFinset_map G f]
  decide

中文:
引理 ruzsaSzemerediNumber_mono
  条件: (f : α ↪ β)
  结论: ruzsaSzemerediNumber α <= ruzsaSzemerediNumber β
  证明: by
  classical
  refine findGreatest_mono ?_ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, _, rfl, hG⟩
  refine ⟨G.map f, inferInstance, ?_, hG.map _⟩
  rw [← card_map ⟨map f]; rw [Finset.map_injective _⟩]; rw [← cliqueFinset_map G f]
  decide

Depends on / 依赖: Finset, Finset.map_injective, Fintype, Fintype.card_le_of_embedding, G.map, card_le_of_embedding, card_map, choose_mono, classical, cliqueFinset_map, findGreatest_mono, hG.map, map_injective
-/
lemma ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsaSzemerediNumber α <= ruzsaSzemerediNumber β := by
  classical
  refine findGreatest_mono ?_ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, _, rfl, hG⟩
  refine ⟨G.map f, inferInstance, ?_, hG.map _⟩
  rw [← card_map ⟨map f]; rw [Finset.map_injective _⟩]; rw [← cliqueFinset_map G f]
  decide

/--
lemma `ruzsaSzemerediNumber_congr` / 引理 `ruzsaSzemerediNumber_congr`

English:
lemma ruzsaSzemerediNumber_congr
  given: (e : α ≃ β)
  statement: ruzsaSzemerediNumber α = ruzsaSzemerediNumber β
  proof: (ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm ruzsaSzemerediNumber_mono e.symm

中文:
引理 ruzsaSzemerediNumber_congr
  条件: (e : α ≃ β)
  结论: ruzsaSzemerediNumber α = ruzsaSzemerediNumber β
  证明: (ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm ruzsaSzemerediNumber_mono e.symm

Depends on / 依赖: antisymm, e.symm, ruzsaSzemerediNumber_mono
-/
lemma ruzsaSzemerediNumber_congr (e : α ≃ β) : ruzsaSzemerediNumber α = ruzsaSzemerediNumber β :=
(ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm ruzsaSzemerediNumber_mono e.symm

/--
Definition of `ruzsaSzemerediNumberNat` / `ruzsaSzemerediNumberNat` 的定义

English:
definition ruzsaSzemerediNumberNat
  signature: (n : Nat)
  body: ruzsaSzemerediNumber (Fin n)

@[simp]

中文:
定义 ruzsaSzemerediNumber自然数
  签名: (n : 自然数)
  定义体: ruzsaSzemerediNumber (Fin n)

@[simp]

Depends on / 依赖: ruzsaSzemerediNumber
-/
noncomputable def ruzsaSzemerediNumberNat (n : Nat) : Nat := ruzsaSzemerediNumber (Fin n)

@[simp]
/--
lemma `ruzsaSzemerediNumberNat_card` / 引理 `ruzsaSzemerediNumberNat_card`

English:
lemma ruzsaSzemerediNumberNat_card
  statement: ruzsaSzemerediNumberNat (card α) = ruzsaSzemerediNumber α
  proof: ruzsaSzemerediNumber_congr (Fintype.equivFin _).symm

@[gcongr]

中文:
引理 ruzsaSzemerediNumber自然数_card
  结论: ruzsaSzemerediNumber自然数 (card α) = ruzsaSzemerediNumber α
  证明: ruzsaSzemerediNumber_congr (Fintype.equivFin _).symm

@[gcongr]

Depends on / 依赖: Fintype, Fintype.equivFin, equivFin, ruzsaSzemerediNumber_congr
-/
lemma ruzsaSzemerediNumberNat_card : ruzsaSzemerediNumberNat (card α) = ruzsaSzemerediNumber α :=
  ruzsaSzemerediNumber_congr (Fintype.equivFin _).symm

@[gcongr]
/--
lemma `ruzsaSzemerediNumberNat_mono` / 引理 `ruzsaSzemerediNumberNat_mono`

English:
lemma ruzsaSzemerediNumberNat_mono
  statement: Monotone ruzsaSzemerediNumberNat
  proof: fun _m _n h =>
  ruzsaSzemerediNumber_mono (Fin.castLEEmb h)

中文:
引理 ruzsaSzemerediNumber自然数_mono
  结论: 递增 ruzsaSzemerediNumber自然数
  证明: fun _m _n h =>
  ruzsaSzemerediNumber_mono (Fin.castLEEmb h)
-/
lemma ruzsaSzemerediNumberNat_mono : Monotone ruzsaSzemerediNumberNat := fun _m _n h =>
  ruzsaSzemerediNumber_mono (Fin.castLEEmb h)

/--
lemma `ruzsaSzemerediNumberNat_le` / 引理 `ruzsaSzemerediNumberNat_le`

English:
lemma ruzsaSzemerediNumberNat_le
  statement: ruzsaSzemerediNumberNat n <= n.choose 3
  proof: ruzsaSzemerediNumber_le.trans_eq by rw [Fintype.card_fin]

中文:
引理 ruzsaSzemerediNumber自然数_le
  结论: ruzsaSzemerediNumber自然数 n <= n.choose 3
  证明: ruzsaSzemerediNumber_le.trans_eq by rw [Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, ruzsaSzemerediNumber_le, ruzsaSzemerediNumber_le.trans_eq, trans_eq
-/
lemma ruzsaSzemerediNumberNat_le : ruzsaSzemerediNumberNat n <= n.choose 3 :=
ruzsaSzemerediNumber_le.trans_eq by rw [Fintype.card_fin]

/--
lemma `ruzsaSzemerediNumberNat_zero` / 引理 `ruzsaSzemerediNumberNat_zero`

English:
lemma ruzsaSzemerediNumberNat_zero
  statement: ruzsaSzemerediNumberNat 0 = 0
  proof: le_zero_iff.1 ruzsaSzemerediNumberNat_le

中文:
引理 ruzsaSzemerediNumber自然数_zero
  结论: ruzsaSzemerediNumber自然数 0 = 0
  证明: le_zero_iff.1 ruzsaSzemerediNumberNat_le
-/
@[simp] lemma ruzsaSzemerediNumberNat_zero : ruzsaSzemerediNumberNat 0 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

/--
lemma `ruzsaSzemerediNumberNat_one` / 引理 `ruzsaSzemerediNumberNat_one`

English:
lemma ruzsaSzemerediNumberNat_one
  statement: ruzsaSzemerediNumberNat 1 = 0
  proof: le_zero_iff.1 ruzsaSzemerediNumberNat_le

中文:
引理 ruzsaSzemerediNumber自然数_one
  结论: ruzsaSzemerediNumber自然数 1 = 0
  证明: le_zero_iff.1 ruzsaSzemerediNumberNat_le
-/
@[simp] lemma ruzsaSzemerediNumberNat_one : ruzsaSzemerediNumberNat 1 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

/--
lemma `ruzsaSzemerediNumberNat_two` / 引理 `ruzsaSzemerediNumberNat_two`

English:
lemma ruzsaSzemerediNumberNat_two
  statement: ruzsaSzemerediNumberNat 2 = 0
  proof: le_zero_iff.1 ruzsaSzemerediNumberNat_le

中文:
引理 ruzsaSzemerediNumber自然数_two
  结论: ruzsaSzemerediNumber自然数 2 = 0
  证明: le_zero_iff.1 ruzsaSzemerediNumberNat_le
-/
@[simp] lemma ruzsaSzemerediNumberNat_two : ruzsaSzemerediNumberNat 2 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

end ruzsaSzemerediNumber

/-! ### The Ruzsa-Szemerédi construction -/

section RuzsaSzemeredi
variable [Fintype α] [CommRing α] {s : Finset α} {x : α × α × α}

/--
Definition of `triangleIndices` / `triangleIndices` 的定义

English:
definition triangleIndices
  signature: (s : Finset α)
  body: (univ ×ˢ s).map
    ⟨fun xa => (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      simp only [Prod.ext_iff] at h
      obtain rfl := h.1
      obtain rfl := add_right_injective _ h.2.1
      rfl⟩

中文:
定义 triangleIndices
  签名: (s : 有限集 α)
  定义体: (univ ×ˢ s).map
    ⟨fun xa => (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      simp only [Prod.ext_iff] at h
      obtain rfl := h.1
      obtain rfl := add_right_injective _ h.2.1
      rfl⟩
-/
private def triangleIndices (s : Finset α) : Finset (α × α × α) :=
  (univ ×ˢ s).map
    ⟨fun xa => (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      simp only [Prod.ext_iff] at h
      obtain rfl := h.1
      obtain rfl := add_right_injective _ h.2.1
      rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mem_triangleIndices` / 引理 `mem_triangleIndices`

English:
lemma mem_triangleIndices
  proof: by simp [triangleIndices]

@[simp]

中文:
引理 mem_triangleIndices
  证明: by simp [triangleIndices]

@[simp]
-/
private lemma mem_triangleIndices :
    x in triangleIndices s ↔ exists y, exists a in s, (y, y + a, y + 2 * a) = x := by simp [triangleIndices]

@[simp]
/--
lemma `card_triangleIndices` / 引理 `card_triangleIndices`

English:
lemma card_triangleIndices
  statement: #(triangleIndices s) = card α * #s
  proof: by
  simp [triangleIndices]

中文:
引理 card_triangleIndices
  结论: #(triangleIndices s) = card α * #s
  证明: by
  simp [triangleIndices]
-/
private lemma card_triangleIndices : #(triangleIndices s) = card α * #s := by
  simp [triangleIndices]

/--
lemma `noAccidental` / 引理 `noAccidental`

English:
lemma noAccidental
  given: (hs : ThreeAPFree (s : Set α))
  proof: by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl
    have : a + c = b + b := by linear_combination h₁.symm - h₂.symm
    obtain rfl := hs ha hb hc this
    simp_all

中文:
引理 noAccidental
  条件: (hs : ThreeAPFree (s : 集合 α))
  证明: by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl
    have : a + c = b + b := by linear_combination h₁.symm - h₂.symm
    obtain rfl := hs ha hb hc this
    simp_all
-/
private lemma noAccidental (hs : ThreeAPFree (s : Set α)) :
    NoAccidental (triangleIndices s : Finset (α × α × α)) where
  eq_or_eq_or_eq := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl
    have : a + c = b + b := by linear_combination h₁.symm - h₂.symm
    obtain rfl := hs ha hb hc this
    simp_all

variable [Fact <| IsUnit (2 : α)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ExplicitDisjoint (triangleIndices s : Finset (α × α × α))
  body: by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂
    linear_combination 2 * h₁.symm - h₂.symm
  inj₁ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha 

中文:
实例 :
  签名: ExplicitDisjoint (triangleIndices s : 有限集 (α × α × α))
  定义体: by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂
    linear_combination 2 * h₁.symm - h₂.symm
  inj₁ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha 
-/
private instance : ExplicitDisjoint (triangleIndices s : Finset (α × α × α)) where
  inj₀ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂
    linear_combination 2 * h₁.symm - h₂.symm
  inj₁ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl rfl h
    simpa [(Fact.out (p := IsUnit (2 : α))).mul_right_inj, eq_comm] using h
  inj₂ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h rfl
    simpa [(Fact.out (p := IsUnit (2 : α))).mul_right_inj, eq_comm] using h

/--
lemma `locallyLinear` / 引理 `locallyLinear`

English:
lemma locallyLinear
  given: (hs : ThreeAPFree (s : Set α))
  proof: haveI := noAccidental hs; TripartiteFromTriangles.locallyLinear _

中文:
引理 locallyLinear
  条件: (hs : ThreeAPFree (s : 集合 α))
  证明: haveI := noAccidental hs; TripartiteFromTriangles.locallyLinear _
-/
private lemma locallyLinear (hs : ThreeAPFree (s : Set α)) :
    (graph <| triangleIndices s).LocallyLinear :=
  haveI := noAccidental hs; TripartiteFromTriangles.locallyLinear _

/--
lemma `card_edgeFinset` / 引理 `card_edgeFinset`

English:
lemma card_edgeFinset
  given: (hs : ThreeAPFree (s : Set α)) [DecidableEq α]
  proof: by
  have := noAccidental hs
  rw [(locallyLinear hs).card_edgeFinset]; rw [card_triangles]; rw [card_triangleIndices]; rw [mul_assoc]

中文:
引理 card_edgeFinset
  条件: (hs : ThreeAPFree (s : 集合 α)) [DecidableEq α]
  证明: by
  have := noAccidental hs
  rw [(locallyLinear hs).card_edgeFinset]; rw [card_triangles]; rw [card_triangleIndices]; rw [mul_assoc]
-/
private lemma card_edgeFinset (hs : ThreeAPFree (s : Set α)) [DecidableEq α] :
    #(graph <| triangleIndices s).edgeFinset = 3 * card α * #s := by
  have := noAccidental hs
  rw [(locallyLinear hs).card_edgeFinset]; rw [card_triangles]; rw [card_triangleIndices]; rw [mul_assoc]

end RuzsaSzemeredi

variable (α) [Fintype α] [DecidableEq α] [CommRing α] [Fact <| IsUnit (2 : α)]

/--
lemma `addRothNumber_le_ruzsaSzemerediNumber` / 引理 `addRothNumber_le_ruzsaSzemerediNumber`

English:
lemma addRothNumber_le_ruzsaSzemerediNumber
  proof: by
  obtain ⟨s, -, hscard, hs⟩ := addRothNumber_spec (univ : Finset α)
  have := noAccidental hs
  rw [← hscard]; rw [← card_triangleIndices]; rw [← card_triangles]
  exact (locallyLinear hs).le_ruzsaSzemerediNumber

中文:
引理 addRothNumber_le_ruzsaSzemerediNumber
  证明: by
  obtain ⟨s, -, hscard, hs⟩ := addRothNumber_spec (univ : Finset α)
  have := noAccidental hs
  rw [← hscard]; rw [← card_triangleIndices]; rw [← card_triangles]
  exact (locallyLinear hs).le_ruzsaSzemerediNumber

Depends on / 依赖: Finset, addRothNumber_spec, card_triangleIndices, card_triangles, hscard, le_ruzsaSzemerediNumber, locallyLinear, noAccidental
-/
lemma addRothNumber_le_ruzsaSzemerediNumber :
    card α * addRothNumber (univ : Finset α) <= ruzsaSzemerediNumber (Sum α (Sum α α)) := by
  obtain ⟨s, -, hscard, hs⟩ := addRothNumber_spec (univ : Finset α)
  have := noAccidental hs
  rw [← hscard]; rw [← card_triangleIndices]; rw [← card_triangles]
  exact (locallyLinear hs).le_ruzsaSzemerediNumber

/--
lemma `rothNumberNat_le_ruzsaSzemerediNumberNat` / 引理 `rothNumberNat_le_ruzsaSzemerediNumberNat`

English:
lemma rothNumberNat_le_ruzsaSzemerediNumberNat
  given: (n : Nat)
  proof: by
  let α := Fin (2 * n + 1)
  have : Nat.Coprime 2 (2 * n + 1) := by simp
  have : Fact (IsUnit (2 : Fin (2 * n + 1))) := ⟨by simpa
    using! (ZMod.unitOfCoprime 2 this).isUnit⟩
  open scoped Fin.CommRing in
  calc
    (2 * n + 1) * rothNumberNat n
    _ = Fintype.card α * addRothNumber (Iio (⟨n,

中文:
引理 rothNumber自然数_le_ruzsaSzemerediNumber自然数
  条件: (n : 自然数)
  证明: by
  let α := Fin (2 * n + 1)
  have : Nat.Coprime 2 (2 * n + 1) := by simp
  have : Fact (IsUnit (2 : Fin (2 * n + 1))) := ⟨by simpa
    using! (ZMod.unitOfCoprime 2 this).isUnit⟩
  open scoped Fin.CommRing in
  calc
    (2 * n + 1) * rothNumberNat n
    _ = Fintype.card α * addRothNumber (Iio (⟨n,

Depends on / 依赖: CommRing, Coprime, Fin.CommRing, Fin.addRothNumber_eq_rothNumberNat, Finset, Fintype, Fintype.card, Fintype.card_fin, IsUnit, Nat.Coprime, ZMod.unitOfCoprime, addRothNumber, addRothNumber_eq_rothNumberNat, card_fin, isUnit, rothNumberNat, ruzsaSzemerediNumber, scoped, subset_univ, unitOfCoprime
-/
lemma rothNumberNat_le_ruzsaSzemerediNumberNat (n : Nat) :
    (2 * n + 1) * rothNumberNat n <= ruzsaSzemerediNumberNat (6 * n + 3) := by
  let α := Fin (2 * n + 1)
  have : Nat.Coprime 2 (2 * n + 1) := by simp
  have : Fact (IsUnit (2 : Fin (2 * n + 1))) := ⟨by simpa
    using! (ZMod.unitOfCoprime 2 this).isUnit⟩
  open scoped Fin.CommRing in
  calc
    (2 * n + 1) * rothNumberNat n
    _ = Fintype.card α * addRothNumber (Iio (⟨n, by lia⟩ : α)) := by
      rw [Fin.addRothNumber_eq_rothNumberNat (by simp)]; rw [Fintype.card_fin]
    _ <= Fintype.card α * addRothNumber (univ : Finset α) := by
      gcongr; exact subset_univ _
    _ <= ruzsaSzemerediNumber (Sum α (Sum α α)) := addRothNumber_le_ruzsaSzemerediNumber _
    _ = ruzsaSzemerediNumberNat (6 * n + 3) := by
      simp_rw [← ruzsaSzemerediNumberNat_card, Fintype.card_sum, α, Fintype.card_fin]
      ring_nf

/--
theorem `rothNumberNat_le_ruzsaSzemerediNumberNat'` / 定理 `rothNumberNat_le_ruzsaSzemerediNumberNat'`

English:
theorem rothNumberNat_le_ruzsaSzemerediNumberNat'
  proof: mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      _ <= (ruzsaSzemerediNumberNat (6 * (n / 6) + 3) : Real) := ?_
      _ <= _ := by grw [Nat.mul_div_le]
    · simp only [cast_add, cast_ofNat, cast_mul, cast_one, tsub_le_iff_right]
      rw [← div_add_one (three_ne_zero' Real)]; rw [← le_sub_iff

中文:
定理 rothNumber自然数_le_ruzsaSzemerediNumber自然数'
  证明: mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      _ <= (ruzsaSzemerediNumberNat (6 * (n / 6) + 3) : Real) := ?_
      _ <= _ := by grw [Nat.mul_div_le]
    · simp only [cast_add, cast_ofNat, cast_mul, cast_one, tsub_le_iff_right]
      rw [← div_add_one (three_ne_zero' Real)]; rw [← le_sub_iff

Depends on / 依赖: Nat.cast_nonneg, Nat.lt_mul_div_succ, Nat.mul_div_le, add_assoc, add_mul, add_sub_assoc, add_sub_cancel_left, cast_add, cast_mul, cast_nonneg, cast_ofNat, cast_one, div_add_one, le_sub_iff_add_le, lt_mul_div_succ, mul_add_one, mul_div_le, mul_le_mul_of_nonneg_right, mul_right_comm, ruzsaSzemerediNumberNat
-/
theorem rothNumberNat_le_ruzsaSzemerediNumberNat' :
    forall n : Nat, (n / 3 - 2 : Real) * rothNumberNat ((n - 3) / 6) <= ruzsaSzemerediNumberNat n
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    calc
      _ <= (↑(2 * (n / 6) + 1) : Real) * rothNumberNat (n / 6) :=
        mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      _ <= (ruzsaSzemerediNumberNat (6 * (n / 6) + 3) : Real) := ?_
      _ <= _ := by grw [Nat.mul_div_le]
    · simp only [cast_add, cast_ofNat, cast_mul, cast_one, tsub_le_iff_right]
      rw [← div_add_one (three_ne_zero' Real)]; rw [← le_sub_iff_add_le]; rw [div_le_iff₀ (zero_lt_three' Real)]; rw [add_assoc]; rw [add_sub_assoc]; rw [add_mul]; rw [mul_right_comm]; rw [add_sub_cancel_left]
      norm_cast
      rw [← mul_add_one]
      exact (Nat.lt_mul_div_succ _ <| by simp).le
    · norm_cast
      exact rothNumberNat_le_ruzsaSzemerediNumberNat _

/--
theorem `ruzsaSzemerediNumberNat_lower_bound` / 定理 `ruzsaSzemerediNumberNat_lower_bound`

English:
theorem ruzsaSzemerediNumberNat_lower_bound
  given: (n : Nat)
  proof: by
  rw [mul_assoc]
  obtain hn | hn := le_total (n / 3 - 2 : Real) 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hn <| by positivity).trans (Nat.cast_nonneg _)
  exact
    (mul_le_mul_of_nonneg_left Behrend.roth_lower_bound hn).trans
      (rothNumberNat_le_ruzsaSzemerediNumberNat' _)

中文:
定理 ruzsaSzemerediNumber自然数_lower_bound
  条件: (n : 自然数)
  证明: by
  rw [mul_assoc]
  obtain hn | hn := le_total (n / 3 - 2 : Real) 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hn <| by positivity).trans (Nat.cast_nonneg _)
  exact
    (mul_le_mul_of_nonneg_left Behrend.roth_lower_bound hn).trans
      (rothNumberNat_le_ruzsaSzemerediNumberNat' _)

Depends on / 依赖: Behrend, Behrend.roth_lower_bound, Nat.cast_nonneg, cast_nonneg, le_total, mul_assoc, mul_le_mul_of_nonneg_left, mul_nonpos_of_nonpos_of_nonneg, rothNumberNat_le_ruzsaSzemerediNumberNat, roth_lower_bound
-/
theorem ruzsaSzemerediNumberNat_lower_bound (n : Nat) :
    (n / 3 - 2 : Real) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6))) <=
      ruzsaSzemerediNumberNat n := by
  rw [mul_assoc]
  obtain hn | hn := le_total (n / 3 - 2 : Real) 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hn <| by positivity).trans (Nat.cast_nonneg _)
  exact
    (mul_le_mul_of_nonneg_left Behrend.roth_lower_bound hn).trans
      (rothNumberNat_le_ruzsaSzemerediNumberNat' _)

open Asymptotics Filter

/--
theorem `ruzsaSzemerediNumberNat_asymptotic_lower_bound` / 定理 `ruzsaSzemerediNumberNat_asymptotic_lower_bound`

English:
theorem ruzsaSzemerediNumberNat_asymptotic_lower_bound
  proof: by
  trans fun n => (n / 3 - 2) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6)))
  · simp_rw [sq]
    refine (IsBigO.mul ?_ ?_).mul ?_
    · trans fun n => n / 3
      · simp_rw [div_eq_inv_mul]
        exact (isBigO_refl ..).const_mul_right (by simp)
      refine IsLittleO.right_isBigO_sub ?_
  

中文:
定理 ruzsaSzemerediNumber自然数_asymptotic_lower_bound
  证明: by
  trans fun n => (n / 3 - 2) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6)))
  · simp_rw [sq]
    refine (IsBigO.mul ?_ ?_).mul ?_
    · trans fun n => n / 3
      · simp_rw [div_eq_inv_mul]
        exact (isBigO_refl ..).const_mul_right (by simp)
      refine IsLittleO.right_isBigO_sub ?_
  

Depends on / 依赖: Function, Function.comp_def, IsBigO, IsBigO.mul, IsBigOWith, IsBigO_def, IsLittleO, IsLittleO.right_isBigO_sub, comp_def, const_mul_right, div_eq_inv_mul, eventually_atTop, isBigO_refl, norm_natCast, right_isBigO_sub, simp_rw, tendsto_natCast_atTop_atTop, zero_lt_three
-/
theorem ruzsaSzemerediNumberNat_asymptotic_lower_bound :
    (fun n => n ^ 2 * exp (-4 * √(log n)) : Nat -> Real) =O[atTop]
     fun n => (ruzsaSzemerediNumberNat n : Real) := by
  trans fun n => (n / 3 - 2) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6)))
  · simp_rw [sq]
    refine (IsBigO.mul ?_ ?_).mul ?_
    · trans fun n => n / 3
      · simp_rw [div_eq_inv_mul]
        exact (isBigO_refl ..).const_mul_right (by simp)
      refine IsLittleO.right_isBigO_sub ?_
      simpa [div_eq_inv_mul, Function.comp_def] using
        .atTop_of_const_mul₀ zero_lt_three (by simp [tendsto_natCast_atTop_atTop])
    · rw [IsBigO_def]
      refine ⟨12, ?_⟩
      simp only [IsBigOWith, norm_natCast, eventually_atTop]
      exact ⟨15, fun x hx => by norm_cast; lia⟩
    · rw [isBigO_exp_comp_exp_comp]
      refine ⟨0, ?_⟩
      simp only [neg_mul, eventually_map, Pi.sub_apply, sub_neg_eq_add, neg_add_le_iff_le_add,
        add_zero, eventually_atTop]
      refine ⟨9, fun x hx => ?_⟩
      gcongr
      · simp
        lia
      · lia
  · refine .of_norm_eventuallyLE ?_
    filter_upwards [eventually_ge_atTop 6] with n hn
    have : (0 : Real) <= n / 3 - 2 := by rify at hn; linarith
    simpa [neg_mul, abs_mul, abs_of_nonneg this] using ruzsaSzemerediNumberNat_lower_bound n
