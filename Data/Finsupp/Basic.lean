/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Rat.BigOperators

/-!
# Miscellaneous definitions, lemmas, and constructions using finsupp

## Main declarations

* `Finsupp.graph`: the finset of input and output pairs with non-zero outputs.
* `Finsupp.mapRange.equiv`: `Finsupp.mapRange` as an equiv.
* `Finsupp.mapDomain`: maps the domain of a `Finsupp` by a function and by summing.
* `Finsupp.comapDomain`: postcomposition of a `Finsupp` with a function injective on the preimage
  of its support.
* `Finsupp.filter`: `filter p f` is the finitely supported function that is `f a` if `p a` is true
  and 0 otherwise.
* `Finsupp.frange`: the image of a finitely supported function on its support.
* `Finsupp.subtype_domain`: the restriction of a finitely supported function `f` to a subtype.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/

@[expose] public section


noncomputable section

open Finset Function

variable {α β γ ι M N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `graph` -/


section Graph

variable [Zero M]

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (f : α ->₀ M)
  body: f.support.map ⟨fun a => Prod.mk a (f a), fun _ _ h => (Prod.mk.inj h).1⟩

中文:
定义 graph
  签名: (f : α ->₀ M)
  定义体: f.support.map ⟨fun a => Prod.mk a (f a), fun _ _ h => (Prod.mk.inj h).1⟩

Depends on / 依赖: Prod.mk, Prod.mk.inj, f.support.map, support
-/
def graph (f : α ->₀ M) : Finset (α × M) :=
  f.support.map ⟨fun a => Prod.mk a (f a), fun _ _ h => (Prod.mk.inj h).1⟩

/--
theorem `mk_mem_graph_iff` / 定理 `mk_mem_graph_iff`

English:
theorem mk_mem_graph_iff
  given: {a : α} {m : M} {f : α ->₀ M}
  statement: (a, m) in f.graph ↔ f a = m ∧ m != 0
  proof: by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp]

中文:
定理 mk_mem_graph_iff
  条件: {a : α} {m : M} {f : α ->₀ M}
  结论: (a, m) in f.graph ↔ f a = m ∧ m != 0
  证明: by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp]

Depends on / 依赖: mem_map, mem_support_iff, simp_rw
-/
theorem mk_mem_graph_iff {a : α} {m : M} {f : α ->₀ M} : (a, m) in f.graph ↔ f a = m ∧ m != 0 := by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp]
/--
theorem `mem_graph_iff` / 定理 `mem_graph_iff`

English:
theorem mem_graph_iff
  given: {c : α × M} {f : α ->₀ M}
  statement: c in f.graph ↔ f c.1 = c.2 ∧ c.2 != 0
  proof: by
  cases c
  exact mk_mem_graph_iff

中文:
定理 mem_graph_iff
  条件: {c : α × M} {f : α ->₀ M}
  结论: c in f.graph ↔ f c.1 = c.2 ∧ c.2 != 0
  证明: by
  cases c
  exact mk_mem_graph_iff

Depends on / 依赖: mk_mem_graph_iff
-/
theorem mem_graph_iff {c : α × M} {f : α ->₀ M} : c in f.graph ↔ f c.1 = c.2 ∧ c.2 != 0 := by
  cases c
  exact mk_mem_graph_iff

/--
theorem `mk_mem_graph` / 定理 `mk_mem_graph`

English:
theorem mk_mem_graph
  given: (f : α ->₀ M) {a : α} (ha : a in f.support)
  statement: (a, f a) in f.graph
  proof: mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

中文:
定理 mk_mem_graph
  条件: (f : α ->₀ M) {a : α} (ha : a in f.support)
  结论: (a, f a) in f.graph
  证明: mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

Depends on / 依赖: mem_support_iff, mk_mem_graph_iff
-/
theorem mk_mem_graph (f : α ->₀ M) {a : α} (ha : a in f.support) : (a, f a) in f.graph :=
  mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

/--
theorem `apply_eq_of_mem_graph` / 定理 `apply_eq_of_mem_graph`

English:
theorem apply_eq_of_mem_graph
  given: {a : α} {m : M} {f : α ->₀ M} (h : (a, m) in f.graph)
  statement: f a = m
  proof: (mem_graph_iff.1 h).1

@[simp 1100] -- Higher priority shortcut instance for `mem_graph_iff`.

中文:
定理 apply_eq_of_mem_graph
  条件: {a : α} {m : M} {f : α ->₀ M} (h : (a, m) in f.graph)
  结论: f a = m
  证明: (mem_graph_iff.1 h).1

@[simp 1100] -- Higher priority shortcut instance for `mem_graph_iff`.

Depends on / 依赖: mem_graph_iff
-/
theorem apply_eq_of_mem_graph {a : α} {m : M} {f : α ->₀ M} (h : (a, m) in f.graph) : f a = m :=
  (mem_graph_iff.1 h).1

@[simp 1100] -- Higher priority shortcut instance for `mem_graph_iff`.
/--
theorem `notMem_graph_snd_zero` / 定理 `notMem_graph_snd_zero`

English:
theorem notMem_graph_snd_zero
  given: (a : α) (f : α ->₀ M)
  statement: (a, (0 : M)) ∉ f.graph
  proof: fun h =>
  (mem_graph_iff.1 h).2.irrefl

中文:
定理 notMem_graph_snd_zero
  条件: (a : α) (f : α ->₀ M)
  结论: (a, (0 : M)) ∉ f.graph
  证明: fun h =>
  (mem_graph_iff.1 h).2.irrefl
-/
theorem notMem_graph_snd_zero (a : α) (f : α ->₀ M) : (a, (0 : M)) ∉ f.graph := fun h =>
  (mem_graph_iff.1 h).2.irrefl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `image_fst_graph` / 定理 `image_fst_graph`

English:
theorem image_fst_graph
  given: [DecidableEq α] (f : α ->₀ M)
  statement: f.graph.image Prod.fst = f.support
  proof: by
  classical
  simp_rw [graph, map_eq_image, image_image, Embedding.coeFn_mk, Function.comp_def, image_id']

中文:
定理 image_fst_graph
  条件: [DecidableEq α] (f : α ->₀ M)
  结论: f.graph.image Prod.fst = f.support
  证明: by
  classical
  simp_rw [graph, map_eq_image, image_image, Embedding.coeFn_mk, Function.comp_def, image_id']

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Function, Function.comp_def, classical, coeFn_mk, comp_def, image_id, image_image, map_eq_image, simp_rw
-/
theorem image_fst_graph [DecidableEq α] (f : α ->₀ M) : f.graph.image Prod.fst = f.support := by
  classical
  simp_rw [graph, map_eq_image, image_image, Embedding.coeFn_mk, Function.comp_def, image_id']

/--
theorem `graph_injective` / 定理 `graph_injective`

English:
theorem graph_injective
  given: (α M) [Zero M]
  statement: Injective (@graph α M _)
  proof: by
  intro f g h
  classical
    have hsup : f.support = g.support := by rw [← image_fst_graph, h, image_fst_graph]
refine ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph h.symm ▸ ?_⟩
    exact mk_mem_graph _ (hsup ▸ hx)

@[simp]

中文:
定理 graph_injective
  条件: (α M) [Zero M]
  结论: Injective (@graph α M _)
  证明: by
  intro f g h
  classical
    have hsup : f.support = g.support := by rw [← image_fst_graph, h, image_fst_graph]
refine ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph h.symm ▸ ?_⟩
    exact mk_mem_graph _ (hsup ▸ hx)

@[simp]

Depends on / 依赖: apply_eq_of_mem_graph, classical, ext_iff, f.support, g.support, h.symm, image_fst_graph, mk_mem_graph, support
-/
theorem graph_injective (α M) [Zero M] : Injective (@graph α M _) := by
  intro f g h
  classical
    have hsup : f.support = g.support := by rw [← image_fst_graph, h, image_fst_graph]
refine ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph h.symm ▸ ?_⟩
    exact mk_mem_graph _ (hsup ▸ hx)

@[simp]
/--
theorem `graph_inj` / 定理 `graph_inj`

English:
theorem graph_inj
  given: {f g : α ->₀ M}
  statement: f.graph = g.graph ↔ f = g
  proof: (graph_injective α M).eq_iff

@[simp]

中文:
定理 graph_inj
  条件: {f g : α ->₀ M}
  结论: f.graph = g.graph ↔ f = g
  证明: (graph_injective α M).eq_iff

@[simp]

Depends on / 依赖: eq_iff, graph_injective
-/
theorem graph_inj {f g : α ->₀ M} : f.graph = g.graph ↔ f = g :=
  (graph_injective α M).eq_iff

@[simp]
/--
theorem `graph_zero` / 定理 `graph_zero`

English:
theorem graph_zero
  statement: graph (0 : α ->₀ M) = ∅
  proof: by simp [graph]

@[simp]

中文:
定理 graph_zero
  结论: graph (0 : α ->₀ M) = ∅
  证明: by simp [graph]

@[simp]
-/
theorem graph_zero : graph (0 : α ->₀ M) = ∅ := by simp [graph]

@[simp]
/--
theorem `graph_eq_empty` / 定理 `graph_eq_empty`

English:
theorem graph_eq_empty
  given: {f : α ->₀ M}
  statement: f.graph = ∅ ↔ f = 0
  proof: (graph_injective α M).eq_iff' graph_zero

中文:
定理 graph_eq_empty
  条件: {f : α ->₀ M}
  结论: f.graph = ∅ ↔ f = 0
  证明: (graph_injective α M).eq_iff' graph_zero

Depends on / 依赖: eq_iff, graph_injective, graph_zero
-/
theorem graph_eq_empty {f : α ->₀ M} : f.graph = ∅ ↔ f = 0 :=
  (graph_injective α M).eq_iff' graph_zero

end Graph

end Finsupp

/-! ### Declarations about `mapRange` -/


section MapRange

namespace Finsupp
variable [AddCommMonoid M] [AddCommMonoid N]
variable {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]

/--
theorem `mapRange_multiset_sum` / 定理 `mapRange_multiset_sum`

English:
theorem mapRange_multiset_sum
  given: (f : F) (m : Multiset (α ->₀ M))
  proof: (mapRange.addMonoidHom (f : M ->+ N) : (α ->₀ _) ->+ _).map_multiset_sum _

中文:
定理 mapRange_multiset_sum
  条件: (f : F) (m : Multiset (α ->₀ M))
  证明: (mapRange.addMonoidHom (f : M ->+ N) : (α ->₀ _) ->+ _).map_multiset_sum _

Depends on / 依赖: addMonoidHom, mapRange, mapRange.addMonoidHom, map_multiset_sum
-/
theorem mapRange_multiset_sum (f : F) (m : Multiset (α ->₀ M)) :
    mapRange f (map_zero f) m.sum = (m.map fun x => mapRange f (map_zero f) x).sum :=
  (mapRange.addMonoidHom (f : M ->+ N) : (α ->₀ _) ->+ _).map_multiset_sum _

/--
theorem `mapRange_finsetSum` / 定理 `mapRange_finsetSum`

English:
theorem mapRange_finsetSum
  given: (f : F) (s : Finset ι) (g : ι -> α ->₀ M)
  proof: map_sum (mapRange.addMonoidHom (f : M ->+ N)) _ _

@[deprecated (since := "2026-04-08")] alias mapRange_finset_sum := mapRange_finsetSum

中文:
定理 mapRange_finsetSum
  条件: (f : F) (s : Finset ι) (g : ι -> α ->₀ M)
  证明: map_sum (mapRange.addMonoidHom (f : M ->+ N)) _ _

@[deprecated (since := "2026-04-08")] alias mapRange_finset_sum := mapRange_finsetSum

Depends on / 依赖: addMonoidHom, mapRange, mapRange.addMonoidHom, map_sum
-/
theorem mapRange_finsetSum (f : F) (s : Finset ι) (g : ι -> α ->₀ M) :
    mapRange f (map_zero f) (∑ x in s, g x) = ∑ x in s, mapRange f (map_zero f) (g x) :=
  map_sum (mapRange.addMonoidHom (f : M ->+ N)) _ _

@[deprecated (since := "2026-04-08")] alias mapRange_finset_sum := mapRange_finsetSum

end Finsupp

end MapRange

/-! ### Declarations about `equivCongrLeft` -/


section EquivCongrLeft

variable [Zero M]

namespace Finsupp

/--
Definition of `equivMapDomain` / `equivMapDomain` 的定义

English:
definition equivMapDomain
  signature: (f : α ≃ β) (l : α ->₀ M)
  body: l.support.map f.toEmbedding
  toFun a := l (f.symm a)
  mem_support_toFun a := by simp only [Finset.mem_map_equiv, mem_support_toFun]; rfl

@[simp]

中文:
定义 equivMapDomain
  签名: (f : α ≃ β) (l : α ->₀ M)
  定义体: l.support.map f.toEmbedding
  toFun a := l (f.symm a)
  mem_support_toFun a := by simp only [Finset.mem_map_equiv, mem_support_toFun]; rfl

@[simp]

Depends on / 依赖: f.toEmbedding, l.support.map, support, toEmbedding
-/
def equivMapDomain (f : α ≃ β) (l : α ->₀ M) : β ->₀ M where
  support := l.support.map f.toEmbedding
  toFun a := l (f.symm a)
  mem_support_toFun a := by simp only [Finset.mem_map_equiv, mem_support_toFun]; rfl

@[simp]
/--
theorem `equivMapDomain_apply` / 定理 `equivMapDomain_apply`

English:
theorem equivMapDomain_apply
  given: (f : α ≃ β) (l : α ->₀ M) (b : β)
  proof: rfl

中文:
定理 equivMapDomain_apply
  条件: (f : α ≃ β) (l : α ->₀ M) (b : β)
  证明: rfl
-/
theorem equivMapDomain_apply (f : α ≃ β) (l : α ->₀ M) (b : β) :
    equivMapDomain f l b = l (f.symm b) :=
  rfl

/--
theorem `equivMapDomain_symm_apply` / 定理 `equivMapDomain_symm_apply`

English:
theorem equivMapDomain_symm_apply
  given: (f : α ≃ β) (l : β ->₀ M) (a : α)
  proof: rfl

@[simp]

中文:
定理 equivMapDomain_symm_apply
  条件: (f : α ≃ β) (l : β ->₀ M) (a : α)
  证明: rfl

@[simp]
-/
theorem equivMapDomain_symm_apply (f : α ≃ β) (l : β ->₀ M) (a : α) :
    equivMapDomain f.symm l a = l (f a) :=
  rfl

@[simp]
/--
theorem `equivMapDomain_refl` / 定理 `equivMapDomain_refl`

English:
theorem equivMapDomain_refl
  given: (l : α ->₀ M)
  statement: equivMapDomain (Equiv.refl _) l = l
  proof: by ext x; rfl

中文:
定理 equivMapDomain_refl
  条件: (l : α ->₀ M)
  结论: equivMapDomain (Equiv.refl _) l = l
  证明: by ext x; rfl
-/
theorem equivMapDomain_refl (l : α ->₀ M) : equivMapDomain (Equiv.refl _) l = l := by ext x; rfl

/--
theorem `equivMapDomain_refl'` / 定理 `equivMapDomain_refl'`

English:
theorem equivMapDomain_refl'
  statement: equivMapDomain (Equiv.refl _) = @id (α ->₀ M)
  proof: by ext x; rfl

中文:
定理 equivMapDomain_refl'
  结论: equivMapDomain (Equiv.refl _) = @id (α ->₀ M)
  证明: by ext x; rfl
-/
theorem equivMapDomain_refl' : equivMapDomain (Equiv.refl _) = @id (α ->₀ M) := by ext x; rfl

/--
theorem `equivMapDomain_trans` / 定理 `equivMapDomain_trans`

English:
theorem equivMapDomain_trans
  given: (f : α ≃ β) (g : β ≃ γ) (l : α ->₀ M)
  proof: by ext x; rfl

中文:
定理 equivMapDomain_trans
  条件: (f : α ≃ β) (g : β ≃ γ) (l : α ->₀ M)
  证明: by ext x; rfl
-/
theorem equivMapDomain_trans (f : α ≃ β) (g : β ≃ γ) (l : α ->₀ M) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by ext x; rfl

/--
theorem `equivMapDomain_trans'` / 定理 `equivMapDomain_trans'`

English:
theorem equivMapDomain_trans'
  given: (f : α ≃ β) (g : β ≃ γ)
  proof: by ext x; rfl

@[simp]

中文:
定理 equivMapDomain_trans'
  条件: (f : α ≃ β) (g : β ≃ γ)
  证明: by ext x; rfl

@[simp]
-/
theorem equivMapDomain_trans' (f : α ≃ β) (g : β ≃ γ) :
    @equivMapDomain _ _ M _ (f.trans g) = equivMapDomain g ∘ equivMapDomain f := by ext x; rfl

@[simp]
/--
theorem `equivMapDomain_single` / 定理 `equivMapDomain_single`

English:
theorem equivMapDomain_single
  given: (f : α ≃ β) (a : α) (b : M)
  proof: by
  classical
    ext x
    simp only [single_apply, ← Equiv.eq_symm_apply, equivMapDomain_apply]

@[simp]

中文:
定理 equivMapDomain_single
  条件: (f : α ≃ β) (a : α) (b : M)
  证明: by
  classical
    ext x
    simp only [single_apply, ← Equiv.eq_symm_apply, equivMapDomain_apply]

@[simp]

Depends on / 依赖: Equiv.eq_symm_apply, classical, eq_symm_apply, equivMapDomain_apply, single_apply
-/
theorem equivMapDomain_single (f : α ≃ β) (a : α) (b : M) :
    equivMapDomain f (single a b) = single (f a) b := by
  classical
    ext x
    simp only [single_apply, ← Equiv.eq_symm_apply, equivMapDomain_apply]

@[simp]
/--
theorem `equivMapDomain_zero` / 定理 `equivMapDomain_zero`

English:
theorem equivMapDomain_zero
  given: {f : α ≃ β}
  statement: equivMapDomain f (0 : α ->₀ M) = (0 : β ->₀ M)
  proof: by
  ext; simp only [equivMapDomain_apply, coe_zero, Pi.zero_apply]

@[to_additive (attr := simp)]

中文:
定理 equivMapDomain_zero
  条件: {f : α ≃ β}
  结论: equivMapDomain f (0 : α ->₀ M) = (0 : β ->₀ M)
  证明: by
  ext; simp only [equivMapDomain_apply, coe_zero, Pi.zero_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.zero_apply, coe_zero, equivMapDomain_apply, zero_apply
-/
theorem equivMapDomain_zero {f : α ≃ β} : equivMapDomain f (0 : α ->₀ M) = (0 : β ->₀ M) := by
  ext; simp only [equivMapDomain_apply, coe_zero, Pi.zero_apply]

@[to_additive (attr := simp)]
/--
theorem `prod_equivMapDomain` / 定理 `prod_equivMapDomain`

English:
theorem prod_equivMapDomain
  given: [CommMonoid N] (f : α ≃ β) (l : α ->₀ M) (g : β -> M -> N)
  proof: by
  simp [prod, equivMapDomain]

中文:
定理 prod_equivMapDomain
  条件: [CommMonoid N] (f : α ≃ β) (l : α ->₀ M) (g : β -> M -> N)
  证明: by
  simp [prod, equivMapDomain]

Depends on / 依赖: equivMapDomain
-/
theorem prod_equivMapDomain [CommMonoid N] (f : α ≃ β) (l : α ->₀ M) (g : β -> M -> N) :
    prod (equivMapDomain f l) g = prod l (fun a m => g (f a) m) := by
  simp [prod, equivMapDomain]

/--
Definition of `equivCongrLeft` / `equivCongrLeft` 的定义

English:
definition equivCongrLeft
  signature: (f : α ≃ β)
  body: by
  refine ⟨equivMapDomain f, equivMapDomain f.symm, fun f => ?_, fun f => ?_⟩ <;> ext x <;>
    simp only [equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]

@[simp]

中文:
定义 equivCongrLeft
  签名: (f : α ≃ β)
  定义体: by
  refine ⟨equivMapDomain f, equivMapDomain f.symm, fun f => ?_, fun f => ?_⟩ <;> ext x <;>
    simp only [equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]

@[simp]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm, apply_symm_apply, equivMapDomain, equivMapDomain_apply, f.symm, symm_apply_apply, symm_symm
-/
def equivCongrLeft (f : α ≃ β) : (α ->₀ M) ≃ (β ->₀ M) := by
  refine ⟨equivMapDomain f, equivMapDomain f.symm, fun f => ?_, fun f => ?_⟩ <;> ext x <;>
    simp only [equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]

@[simp]
/--
theorem `equivCongrLeft_apply` / 定理 `equivCongrLeft_apply`

English:
theorem equivCongrLeft_apply
  given: (f : α ≃ β) (l : α ->₀ M)
  statement: equivCongrLeft f l = equivMapDomain f l
  proof: rfl

@[simp]

中文:
定理 equivCongrLeft_apply
  条件: (f : α ≃ β) (l : α ->₀ M)
  结论: equivCongrLeft f l = equivMapDomain f l
  证明: rfl

@[simp]
-/
theorem equivCongrLeft_apply (f : α ≃ β) (l : α ->₀ M) : equivCongrLeft f l = equivMapDomain f l :=
  rfl

@[simp]
/--
theorem `equivCongrLeft_symm` / 定理 `equivCongrLeft_symm`

English:
theorem equivCongrLeft_symm
  given: (f : α ≃ β)
  proof: rfl

中文:
定理 equivCongrLeft_symm
  条件: (f : α ≃ β)
  证明: rfl
-/
theorem equivCongrLeft_symm (f : α ≃ β) :
    (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm :=
  rfl

end Finsupp

end EquivCongrLeft

section CastFinsupp

variable [Zero M] (f : α ->₀ M)

namespace Nat

@[simp, norm_cast]
/--
theorem `cast_finsuppProd` / 定理 `cast_finsuppProd`

English:
theorem cast_finsuppProd
  given: [CommSemiring R] (g : α -> M -> Nat)
  proof: Nat.cast_prod _ _

@[simp, norm_cast]

中文:
定理 cast_finsuppProd
  条件: [CommSemiring R] (g : α -> M -> 自然数)
  证明: Nat.cast_prod _ _

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_prod, cast_prod
-/
theorem cast_finsuppProd [CommSemiring R] (g : α -> M -> Nat) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Nat.cast_prod _ _

@[simp, norm_cast]
/--
theorem `cast_finsupp_sum` / 定理 `cast_finsupp_sum`

English:
theorem cast_finsupp_sum
  given: [AddCommMonoidWithOne R] (g : α -> M -> Nat)
  proof: Nat.cast_sum _ _

中文:
定理 cast_finsupp_sum
  条件: [AddCommMonoidWithOne R] (g : α -> M -> 自然数)
  证明: Nat.cast_sum _ _

Depends on / 依赖: Nat.cast_sum, cast_sum
-/
theorem cast_finsupp_sum [AddCommMonoidWithOne R] (g : α -> M -> Nat) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Nat.cast_sum _ _

end Nat

namespace Int

@[simp, norm_cast]
/--
theorem `cast_finsuppProd` / 定理 `cast_finsuppProd`

English:
theorem cast_finsuppProd
  given: [CommRing R] (g : α -> M -> Int)
  proof: Int.cast_prod _ _

@[simp, norm_cast]

中文:
定理 cast_finsuppProd
  条件: [CommRing R] (g : α -> M -> 整数)
  证明: Int.cast_prod _ _

@[simp, norm_cast]

Depends on / 依赖: Int.cast_prod, cast_prod
-/
theorem cast_finsuppProd [CommRing R] (g : α -> M -> Int) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Int.cast_prod _ _

@[simp, norm_cast]
/--
theorem `cast_finsupp_sum` / 定理 `cast_finsupp_sum`

English:
theorem cast_finsupp_sum
  given: [AddCommGroupWithOne R] (g : α -> M -> Int)
  proof: Int.cast_sum _ _

中文:
定理 cast_finsupp_sum
  条件: [AddCommGroupWithOne R] (g : α -> M -> 整数)
  证明: Int.cast_sum _ _

Depends on / 依赖: Int.cast_sum, cast_sum
-/
theorem cast_finsupp_sum [AddCommGroupWithOne R] (g : α -> M -> Int) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Int.cast_sum _ _

end Int

namespace Rat

@[simp, norm_cast]
/--
theorem `cast_finsupp_sum` / 定理 `cast_finsupp_sum`

English:
theorem cast_finsupp_sum
  given: [DivisionRing R] [CharZero R] (g : α -> M -> Rat)
  proof: cast_sum _ _

@[simp, norm_cast]

中文:
定理 cast_finsupp_sum
  条件: [DivisionRing R] [CharZero R] (g : α -> M -> Rat)
  证明: cast_sum _ _

@[simp, norm_cast]

Depends on / 依赖: cast_sum
-/
theorem cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α -> M -> Rat) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  cast_sum _ _

@[simp, norm_cast]
/--
theorem `cast_finsuppProd` / 定理 `cast_finsuppProd`

English:
theorem cast_finsuppProd
  given: [Field R] [CharZero R] (g : α -> M -> Rat)
  proof: cast_prod _ _

中文:
定理 cast_finsuppProd
  条件: [Field R] [CharZero R] (g : α -> M -> Rat)
  证明: cast_prod _ _

Depends on / 依赖: cast_prod
-/
theorem cast_finsuppProd [Field R] [CharZero R] (g : α -> M -> Rat) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  cast_prod _ _

end Rat

end CastFinsupp

/-! ### Declarations about `mapDomain` -/


namespace Finsupp

section MapDomain

variable [AddCommMonoid M] {v v₁ v₂ : α ->₀ M}

/--
Definition of `mapDomain` / `mapDomain` 的定义

English:
definition mapDomain
  signature: (f : α -> β) (v : α ->₀ M)
  body: v.sum fun a => single (f a)

中文:
定义 mapDomain
  签名: (f : α -> β) (v : α ->₀ M)
  定义体: v.sum fun a => single (f a)

Depends on / 依赖: single, v.sum
-/
def mapDomain (f : α -> β) (v : α ->₀ M) : β ->₀ M :=
  v.sum fun a => single (f a)

/--
theorem `mapDomain_apply` / 定理 `mapDomain_apply`

English:
theorem mapDomain_apply
  given: {f : α -> β} (hf : Function.Injective f) (x : α ->₀ M) (a : α)
  proof: by
  rw [mapDomain]; rw [sum_apply]; rw [sum_eq_single a]; rw [single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne' (hf.ne hba)
  · intro _
    rw [single_zero]; rw [coe_zero]; rw [Pi.zero_apply]

中文:
定理 mapDomain_apply
  条件: {f : α -> β} (hf : Function.Injective f) (x : α ->₀ M) (a : α)
  证明: by
  rw [mapDomain]; rw [sum_apply]; rw [sum_eq_single a]; rw [single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne' (hf.ne hba)
  · intro _
    rw [single_zero]; rw [coe_zero]; rw [Pi.zero_apply]
-/
@[simp] theorem mapDomain_apply {f : α -> β} (hf : Function.Injective f) (x : α ->₀ M) (a : α) :
    mapDomain f x (f a) = x a := by
  rw [mapDomain]; rw [sum_apply]; rw [sum_eq_single a]; rw [single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne' (hf.ne hba)
  · intro _
    rw [single_zero]; rw [coe_zero]; rw [Pi.zero_apply]

/--
lemma `mapDomain_of_not_mem_image_support` / 引理 `mapDomain_of_not_mem_image_support`

English:
lemma mapDomain_of_not_mem_image_support
  statement: {f : α -> β} {x : α ->₀ M} {b : β}
  proof: by
  rw [mapDomain]; rw [sum_apply]; rw [sum]; rw [Finset.sum_eq_zero]
exact fun a ha => single_eq_of_ne fun eq => hb eq ▸ Set.mem_image_of_mem _ ha

中文:
引理 mapDomain_of_not_mem_image_support
  结论: {f : α -> β} {x : α ->₀ M} {b : β}
  证明: by
  rw [mapDomain]; rw [sum_apply]; rw [sum]; rw [Finset.sum_eq_zero]
exact fun a ha => single_eq_of_ne fun eq => hb eq ▸ Set.mem_image_of_mem _ ha

Depends on / 依赖: Finset, Finset.sum_eq_zero, Set.mem_image_of_mem, mapDomain, mem_image_of_mem, single_eq_of_ne, sum_apply, sum_eq_zero
-/
lemma mapDomain_of_not_mem_image_support {f : α -> β} {x : α ->₀ M} {b : β}
    (hb : b ∉ f '' x.support) : mapDomain f x b = 0 := by
  rw [mapDomain]; rw [sum_apply]; rw [sum]; rw [Finset.sum_eq_zero]
exact fun a ha => single_eq_of_ne fun eq => hb eq ▸ Set.mem_image_of_mem _ ha

/--
theorem `mapDomain_of_notMem_range` / 定理 `mapDomain_of_notMem_range`

English:
theorem mapDomain_of_notMem_range
  given: {f : α -> β} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f)
  proof: mapDomain_of_not_mem_image_support by grw [Set.image_subset_range]; exact h

@[deprecated (since := "2026-07-15")] alias mapDomain_notin_range := mapDomain_of_notMem_range

中文:
定理 mapDomain_of_notMem_range
  条件: {f : α -> β} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f)
  证明: mapDomain_of_not_mem_image_support by grw [Set.image_subset_range]; exact h

@[deprecated (since := "2026-07-15")] alias mapDomain_notin_range := mapDomain_of_notMem_range

Depends on / 依赖: Set.image_subset_range, image_subset_range, mapDomain_of_not_mem_image_support
-/
theorem mapDomain_of_notMem_range {f : α -> β} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f) :
    mapDomain f x a = 0 :=
mapDomain_of_not_mem_image_support by grw [Set.image_subset_range]; exact h

@[deprecated (since := "2026-07-15")] alias mapDomain_notin_range := mapDomain_of_notMem_range

/--
lemma `mem_range_of_mapDomain_ne_zero` / 引理 `mem_range_of_mapDomain_ne_zero`

English:
lemma mem_range_of_mapDomain_ne_zero
  given: {f : α -> β} {x : α ->₀ M} {b : β} (h : mapDomain f x b != 0)
  proof: by contrapose! h; exact mapDomain_of_notMem_range _ _ h

@[simp]

中文:
引理 mem_range_of_mapDomain_ne_zero
  条件: {f : α -> β} {x : α ->₀ M} {b : β} (h : mapDomain f x b != 0)
  证明: by contrapose! h; exact mapDomain_of_notMem_range _ _ h

@[simp]

Depends on / 依赖: contrapose, mapDomain_of_notMem_range
-/
lemma mem_range_of_mapDomain_ne_zero {f : α -> β} {x : α ->₀ M} {b : β} (h : mapDomain f x b != 0) :
    b in Set.range f := by contrapose! h; exact mapDomain_of_notMem_range _ _ h

@[simp]
/--
theorem `mapDomain_id` / 定理 `mapDomain_id`

English:
theorem mapDomain_id
  statement: mapDomain id v = v
  proof: sum_single _

中文:
定理 mapDomain_id
  结论: mapDomain id v = v
  证明: sum_single _

Depends on / 依赖: sum_single
-/
theorem mapDomain_id : mapDomain id v = v :=
  sum_single _

/--
theorem `mapDomain_comp` / 定理 `mapDomain_comp`

English:
theorem mapDomain_comp
  given: {f : α -> β} {g : β -> γ}
  proof: by
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr fun _ _ => sum_single_index ?_
  exact single_zero _

@[simp]

中文:
定理 mapDomain_comp
  条件: {f : α -> β} {g : β -> γ}
  证明: by
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr fun _ _ => sum_single_index ?_
  exact single_zero _

@[simp]

Depends on / 依赖: single_add, single_zero, sum_congr, sum_single_index, sum_sum_index
-/
theorem mapDomain_comp {f : α -> β} {g : β -> γ} :
    mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) := by
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr fun _ _ => sum_single_index ?_
  exact single_zero _

@[simp]
/--
theorem `mapDomain_single` / 定理 `mapDomain_single`

English:
theorem mapDomain_single
  given: {f : α -> β} {a : α} {b : M}
  statement: mapDomain f (single a b) = single (f a) b
  proof: sum_single_index single_zero _

@[simp]

中文:
定理 mapDomain_single
  条件: {f : α -> β} {a : α} {b : M}
  结论: mapDomain f (single a b) = single (f a) b
  证明: sum_single_index single_zero _

@[simp]

Depends on / 依赖: single_zero, sum_single_index
-/
theorem mapDomain_single {f : α -> β} {a : α} {b : M} : mapDomain f (single a b) = single (f a) b :=
sum_single_index single_zero _

@[simp]
/--
theorem `mapDomain_zero` / 定理 `mapDomain_zero`

English:
theorem mapDomain_zero
  given: {f : α -> β}
  statement: mapDomain f (0 : α ->₀ M) = (0 : β ->₀ M)
  proof: sum_zero_index

中文:
定理 mapDomain_zero
  条件: {f : α -> β}
  结论: mapDomain f (0 : α ->₀ M) = (0 : β ->₀ M)
  证明: sum_zero_index

Depends on / 依赖: sum_zero_index
-/
theorem mapDomain_zero {f : α -> β} : mapDomain f (0 : α ->₀ M) = (0 : β ->₀ M) :=
  sum_zero_index

/--
theorem `mapDomain_congr` / 定理 `mapDomain_congr`

English:
theorem mapDomain_congr
  given: {f g : α -> β} (h : forall x in v.support, f x = g x)
  proof: Finset.sum_congr rfl fun _ H => by simp only [h _ H]

中文:
定理 mapDomain_congr
  条件: {f g : α -> β} (h : 对任意 x in v.support, f x = g x)
  证明: Finset.sum_congr rfl fun _ H => by simp only [h _ H]

Depends on / 依赖: Finset, Finset.sum_congr, sum_congr
-/
theorem mapDomain_congr {f g : α -> β} (h : forall x in v.support, f x = g x) :
    v.mapDomain f = v.mapDomain g :=
  Finset.sum_congr rfl fun _ H => by simp only [h _ H]

/--
theorem `mapDomain_add` / 定理 `mapDomain_add`

English:
theorem mapDomain_add
  given: {f : α -> β}
  statement: mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂
  proof: sum_add_index' (fun _ => single_zero _) fun _ => single_add _

中文:
定理 mapDomain_add
  条件: {f : α -> β}
  结论: mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂
  证明: sum_add_index' (fun _ => single_zero _) fun _ => single_add _

Depends on / 依赖: single_add, single_zero, sum_add_index
-/
theorem mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  sum_add_index' (fun _ => single_zero _) fun _ => single_add _

/--
lemma `mapDomain_sub` / 引理 `mapDomain_sub`

English:
lemma mapDomain_sub
  given: {α β M : Type*} [AddCommGroup M] {v₁ v₂ : α ->₀ M} {f : α -> β}
  proof: by
  simp [mapDomain, sum_sub_index]

@[simp]

中文:
引理 mapDomain_sub
  条件: {α β M : 类型} [AddCommGroup M] {v₁ v₂ : α ->₀ M} {f : α -> β}
  证明: by
  simp [mapDomain, sum_sub_index]

@[simp]

Depends on / 依赖: mapDomain, sum_sub_index
-/
lemma mapDomain_sub {α β M : Type*} [AddCommGroup M] {v₁ v₂ : α ->₀ M} {f : α -> β} :
    mapDomain f (v₁ - v₂) = mapDomain f v₁ - mapDomain f v₂ := by
  simp [mapDomain, sum_sub_index]

@[simp]
/--
theorem `mapDomain_equiv_apply` / 定理 `mapDomain_equiv_apply`

English:
theorem mapDomain_equiv_apply
  given: {f : α ≃ β} (x : α ->₀ M) (a : β)
  proof: by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact mapDomain_apply f.injective _ _

中文:
定理 mapDomain_equiv_apply
  条件: {f : α ≃ β} (x : α ->₀ M) (a : β)
  证明: by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact mapDomain_apply f.injective _ _

Depends on / 依赖: apply_symm_apply, conv_lhs, f.apply_symm_apply, f.injective, injective, mapDomain_apply
-/
theorem mapDomain_equiv_apply {f : α ≃ β} (x : α ->₀ M) (a : β) :
    mapDomain f x a = x (f.symm a) := by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact mapDomain_apply f.injective _ _

/--
lemma `support_mapDomain_embedding` / 引理 `support_mapDomain_embedding`

English:
lemma support_mapDomain_embedding
  given: (f : α ↪ β) (x : α ->₀ M)
  proof: by
  ext b
  simp only [mem_support_iff, ne_eq, mem_map]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := mem_range_of_mapDomain_ne_zero h
    exact ⟨a, by simpa [f.injective] using h⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [f.injective]

中文:
引理 support_mapDomain_embedding
  条件: (f : α ↪ β) (x : α ->₀ M)
  证明: by
  ext b
  simp only [mem_support_iff, ne_eq, mem_map]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := mem_range_of_mapDomain_ne_zero h
    exact ⟨a, by simpa [f.injective] using h⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [f.injective]
-/
@[simp] lemma support_mapDomain_embedding (f : α ↪ β) (x : α ->₀ M) :
    (mapDomain f x).support = x.support.map f := by
  ext b
  simp only [mem_support_iff, ne_eq, mem_map]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := mem_range_of_mapDomain_ne_zero h
    exact ⟨a, by simpa [f.injective] using h⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [f.injective]

/-- `Finsupp.mapDomain` is an `AddMonoidHom`. -/
@[simps]
/--
Definition of `mapDomain.addMonoidHom` / `mapDomain.addMonoidHom` 的定义

English:
definition mapDomain.addMonoidHom
  signature: (f : α -> β)
  body: mapDomain f
  map_zero' := mapDomain_zero
  map_add' _ _ := mapDomain_add

@[simp]

中文:
定义 mapDomain.addMonoidHom
  签名: (f : α -> β)
  定义体: mapDomain f
  map_zero' := mapDomain_zero
  map_add' _ _ := mapDomain_add

@[simp]

Depends on / 依赖: mapDomain
-/
def mapDomain.addMonoidHom (f : α -> β) : (α ->₀ M) ->+ β ->₀ M where
  toFun := mapDomain f
  map_zero' := mapDomain_zero
  map_add' _ _ := mapDomain_add

@[simp]
/--
theorem `mapDomain.addMonoidHom_id` / 定理 `mapDomain.addMonoidHom_id`

English:
theorem mapDomain.addMonoidHom_id
  statement: mapDomain.addMonoidHom id = AddMonoidHom.id (α ->₀ M)
  proof: AddMonoidHom.ext fun _ => mapDomain_id

中文:
定理 mapDomain.addMonoidHom_id
  结论: mapDomain.addMonoidHom id = AddMonoidHom.id (α ->₀ M)
  证明: AddMonoidHom.ext fun _ => mapDomain_id

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, mapDomain_id
-/
theorem mapDomain.addMonoidHom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (α ->₀ M) :=
  AddMonoidHom.ext fun _ => mapDomain_id

/--
theorem `mapDomain.addMonoidHom_comp` / 定理 `mapDomain.addMonoidHom_comp`

English:
theorem mapDomain.addMonoidHom_comp
  given: (f : β -> γ) (g : α -> β)
  proof: AddMonoidHom.ext fun _ => mapDomain_comp

中文:
定理 mapDomain.addMonoidHom_comp
  条件: (f : β -> γ) (g : α -> β)
  证明: AddMonoidHom.ext fun _ => mapDomain_comp

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, mapDomain_comp
-/
theorem mapDomain.addMonoidHom_comp (f : β -> γ) (g : α -> β) :
    (mapDomain.addMonoidHom (f ∘ g) : (α ->₀ M) ->+ γ ->₀ M) =
      (mapDomain.addMonoidHom f).comp (mapDomain.addMonoidHom g) :=
  AddMonoidHom.ext fun _ => mapDomain_comp

/--
theorem `mapDomain_finsetSum` / 定理 `mapDomain_finsetSum`

English:
theorem mapDomain_finsetSum
  given: {f : α -> β} {s : Finset ι} {v : ι -> α ->₀ M}
  proof: map_sum (mapDomain.addMonoidHom f) _ _

@[deprecated (since := "2026-04-08")] alias mapDomain_finset_sum := mapDomain_finsetSum

中文:
定理 mapDomain_finsetSum
  条件: {f : α -> β} {s : Finset ι} {v : ι -> α ->₀ M}
  证明: map_sum (mapDomain.addMonoidHom f) _ _

@[deprecated (since := "2026-04-08")] alias mapDomain_finset_sum := mapDomain_finsetSum

Depends on / 依赖: addMonoidHom, mapDomain, mapDomain.addMonoidHom, map_sum
-/
theorem mapDomain_finsetSum {f : α -> β} {s : Finset ι} {v : ι -> α ->₀ M} :
    mapDomain f (∑ i in s, v i) = ∑ i in s, mapDomain f (v i) :=
  map_sum (mapDomain.addMonoidHom f) _ _

@[deprecated (since := "2026-04-08")] alias mapDomain_finset_sum := mapDomain_finsetSum

/--
theorem `mapDomain_sum` / 定理 `mapDomain_sum`

English:
theorem mapDomain_sum
  given: [Zero N] {f : α -> β} {s : α ->₀ N} {v : α -> N -> α ->₀ M}
  proof: map_finsuppSum (mapDomain.addMonoidHom f : (α ->₀ M) ->+ β ->₀ M) _ _

中文:
定理 mapDomain_sum
  条件: [Zero N] {f : α -> β} {s : α ->₀ N} {v : α -> N -> α ->₀ M}
  证明: map_finsuppSum (mapDomain.addMonoidHom f : (α ->₀ M) ->+ β ->₀ M) _ _

Depends on / 依赖: addMonoidHom, mapDomain, mapDomain.addMonoidHom, map_finsuppSum
-/
theorem mapDomain_sum [Zero N] {f : α -> β} {s : α ->₀ N} {v : α -> N -> α ->₀ M} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  map_finsuppSum (mapDomain.addMonoidHom f : (α ->₀ M) ->+ β ->₀ M) _ _

/--
theorem `mapDomain_support` / 定理 `mapDomain_support`

English:
theorem mapDomain_support
  given: [DecidableEq β] {f : α -> β} {s : α ->₀ M}
  proof: Finset.Subset.trans support_sum
Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) by
      rw [Finset.biUnion_singleton]

中文:
定理 mapDomain_support
  条件: [DecidableEq β] {f : α -> β} {s : α ->₀ M}
  证明: Finset.Subset.trans support_sum
Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) by
      rw [Finset.biUnion_singleton]

Depends on / 依赖: Finset, Finset.Subset.trans, Finset.biUnion_mono, Finset.biUnion_singleton, Subset, biUnion_mono, biUnion_singleton, support_single_subset, support_sum
-/
theorem mapDomain_support [DecidableEq β] {f : α -> β} {s : α ->₀ M} :
    (s.mapDomain f).support subseteq s.support.image f :=
Finset.Subset.trans support_sum
Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) by
      rw [Finset.biUnion_singleton]

/--
theorem `mapDomain_apply'` / 定理 `mapDomain_apply'`

English:
theorem mapDomain_apply'
  statement: (S : Set α) {f : α -> β} (x : α ->₀ M) (hS : (x.support : Set α) subseteq S)
  proof: by
  classical
    rw [mapDomain]; rw [sum_apply]; rw [sum]
    simp_rw [single_apply]
    by_cases hax : a in x.support
    · rw [← Finset.add_sum_erase _ _ hax, if_pos rfl]
      convert! add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact (hf.mono hS).ne (Finset.mem_o

中文:
定理 mapDomain_apply'
  结论: (S : Set α) {f : α -> β} (x : α ->₀ M) (hS : (x.support : Set α) subseteq S)
  证明: by
  classical
    rw [mapDomain]; rw [sum_apply]; rw [sum]
    simp_rw [single_apply]
    by_cases hax : a in x.support
    · rw [← Finset.add_sum_erase _ _ hax, if_pos rfl]
      convert! add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact (hf.mono hS).ne (Finset.mem_o

Depends on / 依赖: Finset, Finset.add_sum_erase, Finset.mem_of_mem_erase, Finset.ne_of_mem_erase, Finset.sum_eq_zero, add_sum_erase, add_zero, classical, convert, hf.mono, hf.ne, if_neg, if_pos, mapDomain, mem_of_mem_erase, ne_of_mem_erase, ne_of_mem_of_not_mem, notMem_support_iff, simp_rw, single_apply
-/
theorem mapDomain_apply' (S : Set α) {f : α -> β} (x : α ->₀ M) (hS : (x.support : Set α) subseteq S)
    (hf : Set.InjOn f S) {a : α} (ha : a in S) : mapDomain f x (f a) = x a := by
  classical
    rw [mapDomain]; rw [sum_apply]; rw [sum]
    simp_rw [single_apply]
    by_cases hax : a in x.support
    · rw [← Finset.add_sum_erase _ _ hax, if_pos rfl]
      convert! add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact (hf.mono hS).ne (Finset.mem_of_mem_erase hi) hax (Finset.ne_of_mem_erase hi)
    · rw [notMem_support_iff.1 hax]
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax)

/--
theorem `mapDomain_support_of_injOn` / 定理 `mapDomain_support_of_injOn`

English:
theorem mapDomain_support_of_injOn
  statement: [DecidableEq β] {f : α -> β} (s : α ->₀ M)
  proof: Finset.Subset.antisymm mapDomain_support by
    intro x hx
    simp only [mem_image, mem_support_iff, Ne] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne]
    rw [mapDomain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
    · simp_rw [mem_coe, mem_suppor

中文:
定理 mapDomain_support_of_injOn
  结论: [DecidableEq β] {f : α -> β} (s : α ->₀ M)
  证明: Finset.Subset.antisymm mapDomain_support by
    intro x hx
    simp only [mem_image, mem_support_iff, Ne] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne]
    rw [mapDomain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
    · simp_rw [mem_coe, mem_suppor

Depends on / 依赖: Finset, Finset.Subset.antisymm, Subset, Subset.refl, antisymm, hx_h_left, hx_w, mapDomain_apply, mapDomain_support, mem_coe, mem_image, mem_support_iff, s.support, simp_rw, support
-/
theorem mapDomain_support_of_injOn [DecidableEq β] {f : α -> β} (s : α ->₀ M)
    (hf : Set.InjOn f s.support) : (mapDomain f s).support = Finset.image f s.support :=
Finset.Subset.antisymm mapDomain_support by
    intro x hx
    simp only [mem_image, mem_support_iff, Ne] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne]
    rw [mapDomain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
    · simp_rw [mem_coe, mem_support_iff, Ne]
      exact hx_h_left
    · exact Subset.refl _

/--
theorem `mapDomain_support_of_injective` / 定理 `mapDomain_support_of_injective`

English:
theorem mapDomain_support_of_injective
  statement: [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
  proof: mapDomain_support_of_injOn s hf.injOn

@[to_additive]

中文:
定理 mapDomain_support_of_injective
  结论: [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
  证明: mapDomain_support_of_injOn s hf.injOn

@[to_additive]

Depends on / 依赖: hf.injOn, mapDomain_support_of_injOn
-/
theorem mapDomain_support_of_injective [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
    (s : α ->₀ M) : (mapDomain f s).support = Finset.image f s.support :=
  mapDomain_support_of_injOn s hf.injOn

@[to_additive]
/--
theorem `prod_mapDomain_index` / 定理 `prod_mapDomain_index`

English:
theorem prod_mapDomain_index
  statement: [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M -> N}
  proof: (prod_sum_index h_zero h_add).trans prod_congr fun _ _ => prod_single_index (h_zero _)

中文:
定理 prod_mapDomain_index
  结论: [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M -> N}
  证明: (prod_sum_index h_zero h_add).trans prod_congr fun _ _ => prod_single_index (h_zero _)

Depends on / 依赖: h_add, h_zero, prod_congr, prod_single_index, prod_sum_index
-/
theorem prod_mapDomain_index [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M -> N}
    (h_zero : forall b, h b 0 = 1) (h_add : forall b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
    (mapDomain f s).prod h = s.prod fun a m => h (f a) m :=
(prod_sum_index h_zero h_add).trans prod_congr fun _ _ => prod_single_index (h_zero _)

-- Note that in `prod_mapDomain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `MonoidHom`.
/-- A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
@[simp]
/--
theorem `sum_mapDomain_index_addMonoidHom` / 定理 `sum_mapDomain_index_addMonoidHom`

English:
theorem sum_mapDomain_index_addMonoidHom
  statement: [AddCommMonoid N] {f : α -> β} {s : α ->₀ M}
  proof: sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)

中文:
定理 sum_mapDomain_index_addMonoidHom
  结论: [AddCommMonoid N] {f : α -> β} {s : α ->₀ M}
  证明: sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)

Depends on / 依赖: map_add, map_zero, sum_mapDomain_index
-/
theorem sum_mapDomain_index_addMonoidHom [AddCommMonoid N] {f : α -> β} {s : α ->₀ M}
    (h : β -> M ->+ N) : ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)

/--
theorem `embDomain_eq_mapDomain` / 定理 `embDomain_eq_mapDomain`

English:
theorem embDomain_eq_mapDomain
  given: (f : α ↪ β) (v : α ->₀ M)
  statement: embDomain f v = mapDomain f v
  proof: by
  ext a
  by_cases h : a in Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective]; rw [embDomain_apply_self]
  · rw [mapDomain_of_notMem_range, embDomain_of_notMem_range] <;> assumption

@[to_additive]

中文:
定理 embDomain_eq_mapDomain
  条件: (f : α ↪ β) (v : α ->₀ M)
  结论: embDomain f v = mapDomain f v
  证明: by
  ext a
  by_cases h : a in Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective]; rw [embDomain_apply_self]
  · rw [mapDomain_of_notMem_range, embDomain_of_notMem_range] <;> assumption

@[to_additive]

Depends on / 依赖: Set.range, embDomain_apply_self, embDomain_of_notMem_range, f.injective, injective, mapDomain_apply, mapDomain_of_notMem_range
-/
theorem embDomain_eq_mapDomain (f : α ↪ β) (v : α ->₀ M) : embDomain f v = mapDomain f v := by
  ext a
  by_cases h : a in Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective]; rw [embDomain_apply_self]
  · rw [mapDomain_of_notMem_range, embDomain_of_notMem_range] <;> assumption

@[to_additive]
/--
theorem `prod_mapDomain_index_inj` / 定理 `prod_mapDomain_index_inj`

English:
theorem prod_mapDomain_index_inj
  statement: [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M -> N}
  proof: by
  rw [← Function.Embedding.coeFn_mk f hf]; rw [← embDomain_eq_mapDomain]; rw [prod_embDomain]

中文:
定理 prod_mapDomain_index_inj
  结论: [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M -> N}
  证明: by
  rw [← Function.Embedding.coeFn_mk f hf]; rw [← embDomain_eq_mapDomain]; rw [prod_embDomain]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, coeFn_mk, embDomain_eq_mapDomain, prod_embDomain
-/
theorem prod_mapDomain_index_inj [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M -> N}
    (hf : Function.Injective f) : (s.mapDomain f).prod h = s.prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coeFn_mk f hf]; rw [← embDomain_eq_mapDomain]; rw [prod_embDomain]

/--
theorem `mapDomain_injective` / 定理 `mapDomain_injective`

English:
theorem mapDomain_injective
  given: {f : α -> β} (hf : Function.Injective f)
  proof: by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this

中文:
定理 mapDomain_injective
  条件: {f : α -> β} (hf : Function.Injective f)
  证明: by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this

Depends on / 依赖: mapDomain, mapDomain_apply
-/
theorem mapDomain_injective {f : α -> β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this

/--
theorem `mapDomain_surjective` / 定理 `mapDomain_surjective`

English:
theorem mapDomain_surjective
  given: {f : α -> β} (hf : f.Surjective)
  proof: by
  intro x
  use mapDomain (surjInv hf) x
  rw [← mapDomain_comp]; rw [(rightInverse_surjInv hf).id]; rw [mapDomain_id]

中文:
定理 mapDomain_surjective
  条件: {f : α -> β} (hf : f.Surjective)
  证明: by
  intro x
  use mapDomain (surjInv hf) x
  rw [← mapDomain_comp]; rw [(rightInverse_surjInv hf).id]; rw [mapDomain_id]

Depends on / 依赖: Surjective, mapDomain, mapDomain_comp, mapDomain_id, rightInverse_surjInv, surjInv
-/
theorem mapDomain_surjective {f : α -> β} (hf : f.Surjective) :
    (mapDomain (M := M) f).Surjective := by
  intro x
  use mapDomain (surjInv hf) x
  rw [← mapDomain_comp]; rw [(rightInverse_surjInv hf).id]; rw [mapDomain_id]

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `mapDomain`. -/
@[simps]
/--
Definition of `mapDomainEmbedding` / `mapDomainEmbedding` 的定义

English:
definition mapDomainEmbedding
  signature: {α β : Type*} (f : α ↪ β)
  body: ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩

中文:
定义 mapDomainEmbedding
  签名: {α β : 类型} (f : α ↪ β)
  定义体: ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩

Depends on / 依赖: Finsupp, Finsupp.mapDomain, Finsupp.mapDomain_injective, f.injective, injective, mapDomain, mapDomain_injective
-/
def mapDomainEmbedding {α β : Type*} (f : α ↪ β) : (α ->₀ Nat) ↪ β ->₀ Nat :=
  ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩

/--
theorem `mapDomain.addMonoidHom_comp_mapRange` / 定理 `mapDomain.addMonoidHom_comp_mapRange`

English:
theorem mapDomain.addMonoidHom_comp_mapRange
  given: [AddCommMonoid N] (f : α -> β) (g : M ->+ N)
  proof: by
  ext
  simp

中文:
定理 mapDomain.addMonoidHom_comp_mapRange
  条件: [AddCommMonoid N] (f : α -> β) (g : M ->+ N)
  证明: by
  ext
  simp
-/
theorem mapDomain.addMonoidHom_comp_mapRange [AddCommMonoid N] (f : α -> β) (g : M ->+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) := by
  ext
  simp

/--
theorem `mapDomain_mapRange` / 定理 `mapDomain_mapRange`

English:
theorem mapDomain_mapRange
  statement: [AddCommMonoid N] (f : α -> β) (v : α ->₀ M) (g : M -> N) (h0 : g 0 = 0)
  proof: let g' : M ->+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v

中文:
定理 mapDomain_mapRange
  结论: [AddCommMonoid N] (f : α -> β) (v : α ->₀ M) (g : M -> N) (h0 : g 0 = 0)
  证明: let g' : M ->+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v

Depends on / 依赖: DFunLike, DFunLike.congr_fun, addMonoidHom_comp_mapRange, congr_fun, mapDomain, mapDomain.addMonoidHom_comp_mapRange, map_add, map_zero
-/
theorem mapDomain_mapRange [AddCommMonoid N] (f : α -> β) (v : α ->₀ M) (g : M -> N) (h0 : g 0 = 0)
    (hadd : forall x y, g (x + y) = g x + g y) :
    mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M ->+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v

/--
theorem `sum_update_add` / 定理 `sum_update_add`

English:
theorem sum_update_add
  statement: [AddZeroClass α] [AddCommMonoid β] (f : ι ->₀ α) (i : ι) (a : α)
  proof: by
  rw [update_eq_erase_add_single]; rw [sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single]; rw [sum_add_index' hg hgg]; rw [add_assoc]; rw [add_assoc]
  congr 1
  rw [add_comm]; rw [sum_single_index (hg _)]; rw [sum_single_index (hg _)]

中文:
定理 sum_update_add
  结论: [AddZeroClass α] [AddCommMonoid β] (f : ι ->₀ α) (i : ι) (a : α)
  证明: by
  rw [update_eq_erase_add_single]; rw [sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single]; rw [sum_add_index' hg hgg]; rw [add_assoc]; rw [add_assoc]
  congr 1
  rw [add_comm]; rw [sum_single_index (hg _)]; rw [sum_single_index (hg _)]

Depends on / 依赖: Finsupp, Finsupp.update_self, add_assoc, add_comm, conv_rhs, sum_add_index, sum_single_index, update_eq_erase_add_single, update_self
-/
theorem sum_update_add [AddZeroClass α] [AddCommMonoid β] (f : ι ->₀ α) (i : ι) (a : α)
    (g : ι -> α -> β) (hg : forall i, g i 0 = 0)
    (hgg : forall (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  rw [update_eq_erase_add_single]; rw [sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single]; rw [sum_add_index' hg hgg]; rw [add_assoc]; rw [add_assoc]
  congr 1
  rw [add_comm]; rw [sum_single_index (hg _)]; rw [sum_single_index (hg _)]

/--
theorem `mapDomain_injOn` / 定理 `mapDomain_injOn`

English:
theorem mapDomain_injOn
  given: (S : Set α) {f : α -> β} (hf : Set.InjOn f S)
  proof: by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a in v₁.support union v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp_all

中文:
定理 mapDomain_injOn
  条件: (S : Set α) {f : α -> β} (hf : Set.InjOn f S)
  证明: by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a in v₁.support union v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp_all

Depends on / 依赖: Set.union_subset, classical, mapDomain_apply, mod_cast, support, union_subset
-/
theorem mapDomain_injOn (S : Set α) {f : α -> β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (α ->₀ M) -> β ->₀ M) { w | (w.support : Set α) subseteq S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a in v₁.support union v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp_all

/--
theorem `equivMapDomain_eq_mapDomain` / 定理 `equivMapDomain_eq_mapDomain`

English:
theorem equivMapDomain_eq_mapDomain
  given: {M} [AddCommMonoid M] (f : α ≃ β) (l : α ->₀ M)
  proof: by ext x; simp

中文:
定理 equivMapDomain_eq_mapDomain
  条件: {M} [AddCommMonoid M] (f : α ≃ β) (l : α ->₀ M)
  证明: by ext x; simp
-/
theorem equivMapDomain_eq_mapDomain {M} [AddCommMonoid M] (f : α ≃ β) (l : α ->₀ M) :
    equivMapDomain f l = mapDomain f l := by ext x; simp

end MapDomain

/-! ### Declarations about `comapDomain` -/


section ComapDomain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comapDomain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps support]
/--
Definition of `comapDomain` / `comapDomain` 的定义

English:
definition comapDomain
  signature: [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
  body: l.support.preimage f hf
  toFun a := l (f a)
  mem_support_toFun := by
    intro a
    rw [Finset.mem_preimage]
    exact l.mem_support_toFun (f a)

@[simp]

中文:
定义 comapDomain
  签名: [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
  定义体: l.support.preimage f hf
  toFun a := l (f a)
  mem_support_toFun := by
    intro a
    rw [Finset.mem_preimage]
    exact l.mem_support_toFun (f a)

@[simp]

Depends on / 依赖: l.support.preimage, preimage, support
-/
def comapDomain [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) :
    α ->₀ M where
  support := l.support.preimage f hf
  toFun a := l (f a)
  mem_support_toFun := by
    intro a
    rw [Finset.mem_preimage]
    exact l.mem_support_toFun (f a)

@[simp]
/--
theorem `comapDomain_apply` / 定理 `comapDomain_apply`

English:
theorem comapDomain_apply
  statement: [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
  proof: rfl

中文:
定理 comapDomain_apply
  结论: [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
  证明: rfl
-/
theorem comapDomain_apply [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
    (a : α) : comapDomain f l hf a = l (f a) :=
  rfl

/--
theorem `sum_comapDomain` / 定理 `sum_comapDomain`

English:
theorem sum_comapDomain
  statement: [Zero M] [AddCommMonoid N] (f : α -> β) (l : β ->₀ M) (g : β -> M -> N)
  proof: Finset.sum_preimage_of_bij f _ hf fun x => g x (l x)

中文:
定理 sum_comapDomain
  结论: [Zero M] [AddCommMonoid N] (f : α -> β) (l : β ->₀ M) (g : β -> M -> N)
  证明: Finset.sum_preimage_of_bij f _ hf fun x => g x (l x)

Depends on / 依赖: Finset, Finset.sum_preimage_of_bij, sum_preimage_of_bij
-/
theorem sum_comapDomain [Zero M] [AddCommMonoid N] (f : α -> β) (l : β ->₀ M) (g : β -> M -> N)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) :
    (comapDomain f l hf.injOn).sum (g ∘ f) = l.sum g :=
  Finset.sum_preimage_of_bij f _ hf fun x => g x (l x)

/--
theorem `eq_zero_of_comapDomain_eq_zero` / 定理 `eq_zero_of_comapDomain_eq_zero`

English:
theorem eq_zero_of_comapDomain_eq_zero
  statement: [Zero M] (f : α -> β) (l : β ->₀ M)
  proof: by
  rw [← support_eq_empty]; rw [← support_eq_empty]; rw [comapDomain]
  simp_rw [Finset.ext_iff, Finset.notMem_empty, iff_false, mem_preimage]
  intro h a ha
  obtain ⟨b, hb⟩ := hf.2.2 ha
  exact h b (hb.2.symm ▸ ha)

@[simp]

中文:
定理 eq_zero_of_comapDomain_eq_zero
  结论: [Zero M] (f : α -> β) (l : β ->₀ M)
  证明: by
  rw [← support_eq_empty]; rw [← support_eq_empty]; rw [comapDomain]
  simp_rw [Finset.ext_iff, Finset.notMem_empty, iff_false, mem_preimage]
  intro h a ha
  obtain ⟨b, hb⟩ := hf.2.2 ha
  exact h b (hb.2.symm ▸ ha)

@[simp]

Depends on / 依赖: Finset, Finset.ext_iff, Finset.notMem_empty, comapDomain, ext_iff, iff_false, mem_preimage, notMem_empty, simp_rw, support_eq_empty
-/
theorem eq_zero_of_comapDomain_eq_zero [Zero M] (f : α -> β) (l : β ->₀ M)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) : comapDomain f l hf.injOn = 0 -> l = 0 := by
  rw [← support_eq_empty]; rw [← support_eq_empty]; rw [comapDomain]
  simp_rw [Finset.ext_iff, Finset.notMem_empty, iff_false, mem_preimage]
  intro h a ha
  obtain ⟨b, hb⟩ := hf.2.2 ha
  exact h b (hb.2.symm ▸ ha)

@[simp]
/--
lemma `comapDomain_single_of_not_mem_range` / 引理 `comapDomain_single_of_not_mem_range`

English:
lemma comapDomain_single_of_not_mem_range
  statement: [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f)
  proof: by
  classical
  ext a
  simp only [comapDomain, single_apply, coe_mk, coe_zero, Pi.zero_apply, ite_eq_right_iff]
  rintro rfl
  simp at hb

中文:
引理 comapDomain_single_of_not_mem_range
  结论: [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f)
  证明: by
  classical
  ext a
  simp only [comapDomain, single_apply, coe_mk, coe_zero, Pi.zero_apply, ite_eq_right_iff]
  rintro rfl
  simp at hb

Depends on / 依赖: Pi.zero_apply, classical, coe_mk, coe_zero, comapDomain, ite_eq_right_iff, single_apply, zero_apply
-/
lemma comapDomain_single_of_not_mem_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f)
    (m : M) (hf) : comapDomain f (single b m) hf = 0 := by
  classical
  ext a
  simp only [comapDomain, single_apply, coe_mk, coe_zero, Pi.zero_apply, ite_eq_right_iff]
  rintro rfl
  simp at hb

section FInjective

section Zero

variable [Zero M]

/--
lemma `embDomain_comapDomain` / 引理 `embDomain_comapDomain`

English:
lemma embDomain_comapDomain
  given: {f : α ↪ β} {g : β ->₀ M} (hg : ↑g.support subseteq Set.range f)
  proof: by
  ext b
  by_cases hb : b in Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply_self]; rw [comapDomain_apply]
· replace hg : g b = 0 := notMem_support_iff.mp mt (hg ·) hb
    rw [embDomain_of_notMem_range _ _ _ hb]; rw [hg]

@[simp]

中文:
引理 embDomain_comapDomain
  条件: {f : α ↪ β} {g : β ->₀ M} (hg : ↑g.support subseteq Set.range f)
  证明: by
  ext b
  by_cases hb : b in Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply_self]; rw [comapDomain_apply]
· replace hg : g b = 0 := notMem_support_iff.mp mt (hg ·) hb
    rw [embDomain_of_notMem_range _ _ _ hb]; rw [hg]

@[simp]

Depends on / 依赖: Set.range, comapDomain_apply, embDomain_apply_self, embDomain_of_notMem_range, notMem_support_iff, notMem_support_iff.mp, replace
-/
lemma embDomain_comapDomain {f : α ↪ β} {g : β ->₀ M} (hg : ↑g.support subseteq Set.range f) :
    embDomain f (comapDomain f g f.injective.injOn) = g := by
  ext b
  by_cases hb : b in Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply_self]; rw [comapDomain_apply]
· replace hg : g b = 0 := notMem_support_iff.mp mt (hg ·) hb
    rw [embDomain_of_notMem_range _ _ _ hb]; rw [hg]

@[simp]
/--
theorem `comapDomain_embDomain` / 定理 `comapDomain_embDomain`

English:
theorem comapDomain_embDomain
  given: (f : α ↪ β) (l : α ->₀ M)
  proof: by
  ext; simp

中文:
定理 comapDomain_embDomain
  条件: (f : α ↪ β) (l : α ->₀ M)
  证明: by
  ext; simp
-/
theorem comapDomain_embDomain (f : α ↪ β) (l : α ->₀ M) :
    comapDomain f (embDomain f l) f.injective.injOn = l := by
  ext; simp

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp]
/--
theorem `comapDomain_zero` / 定理 `comapDomain_zero`

English:
theorem comapDomain_zero
  statement: (f : α -> β)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 comapDomain_zero
  结论: (f : α -> β)
  证明: by
  ext
  rfl

@[simp]

Depends on / 依赖: Finset, Finset.coe_empty, Set.injOn_empty, coe_empty, injOn_empty
-/
theorem comapDomain_zero (f : α -> β)
    (hif : Set.InjOn f (f ⁻¹' ↑(0 : β ->₀ M).support) := Finset.coe_empty ▸ (Set.injOn_empty f)) :
    comapDomain f (0 : β ->₀ M) hif = (0 : α ->₀ M) := by
  ext
  rfl

@[simp]
/--
theorem `comapDomain_single` / 定理 `comapDomain_single`

English:
theorem comapDomain_single
  statement: (f : α -> β) (a : α) (m : M)
  proof: by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_rw [single_zero, comapDomain_zero]
  · rw [eq_single_iff, comapDomain_apply, comapDomain_support, ← Finset.coe_subset, coe_preimage,
      support_single _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single _ hm]; rw [coe_single

中文:
定理 comapDomain_single
  结论: (f : α -> β) (a : α) (m : M)
  证明: by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_rw [single_zero, comapDomain_zero]
  · rw [eq_single_iff, comapDomain_apply, comapDomain_support, ← Finset.coe_subset, coe_preimage,
      support_single _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single _ hm]; rw [coe_single

Depends on / 依赖: Finset, Finset.coe_subset, coe_preimage, coe_singleton, coe_subset, comapDomain_apply, comapDomain_support, comapDomain_zero, eq_or_ne, eq_single_iff, simp_rw, single_eq_same, single_zero, support_single
-/
theorem comapDomain_single (f : α -> β) (a : α) (m : M)
    (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) :
    comapDomain f (Finsupp.single (f a) m) hif = Finsupp.single a m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_rw [single_zero, comapDomain_zero]
  · rw [eq_single_iff, comapDomain_apply, comapDomain_support, ← Finset.coe_subset, coe_preimage,
      support_single _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single _ hm]; rw [coe_singleton] at hif
    exact ⟨fun x hx => hif hx rfl hx, rfl⟩

/--
lemma `comapDomain_surjective` / 引理 `comapDomain_surjective`

English:
lemma comapDomain_surjective
  given: {f : α -> β} (hf : Function.Injective f)
  proof: by
  intro l'
  use l'.embDomain ⟨f, hf⟩
  exact Finsupp.comapDomain_embDomain ..

中文:
引理 comapDomain_surjective
  条件: {f : α -> β} (hf : Function.Injective f)
  证明: by
  intro l'
  use l'.embDomain ⟨f, hf⟩
  exact Finsupp.comapDomain_embDomain ..

Depends on / 依赖: Finsupp, Finsupp.comapDomain_embDomain, comapDomain_embDomain, embDomain
-/
lemma comapDomain_surjective {f : α -> β} (hf : Function.Injective f) :
    Function.Surjective fun l : β ->₀ M => Finsupp.comapDomain f l hf.injOn := by
  intro l'
  use l'.embDomain ⟨f, hf⟩
  exact Finsupp.comapDomain_embDomain ..

end Zero

section AddZeroClass

variable [AddZeroClass M] {f : α -> β}

/--
theorem `comapDomain_add` / 定理 `comapDomain_add`

English:
theorem comapDomain_add
  statement: (v₁ v₂ : β ->₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support))
  proof: by
  ext
  simp

中文:
定理 comapDomain_add
  结论: (v₁ v₂ : β ->₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support))
  证明: by
  ext
  simp
-/
theorem comapDomain_add (v₁ v₂ : β ->₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support))
    (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).support)) :
    comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂ hv₂ := by
  ext
  simp

/--
theorem `comapDomain_add_of_injective` / 定理 `comapDomain_add_of_injective`

English:
theorem comapDomain_add_of_injective
  given: (hf : Function.Injective f) (v₁ v₂ : β ->₀ M)
  proof: comapDomain_add ..

中文:
定理 comapDomain_add_of_injective
  条件: (hf : Function.Injective f) (v₁ v₂ : β ->₀ M)
  证明: comapDomain_add ..

Depends on / 依赖: comapDomain_add
-/
theorem comapDomain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β ->₀ M) :
    comapDomain f (v₁ + v₂) hf.injOn =
      comapDomain f v₁ hf.injOn + comapDomain f v₂ hf.injOn :=
  comapDomain_add ..

/-- `Finsupp.comapDomain` is an `AddMonoidHom`. -/
@[simps]
/--
Definition of `comapDomain.addMonoidHom` / `comapDomain.addMonoidHom` 的定义

English:
definition comapDomain.addMonoidHom
  signature: (hf : Function.Injective f)
  body: comapDomain f x hf.injOn
  map_zero' := comapDomain_zero f
  map_add' := comapDomain_add_of_injective hf

中文:
定义 comapDomain.addMonoidHom
  签名: (hf : Function.Injective f)
  定义体: comapDomain f x hf.injOn
  map_zero' := comapDomain_zero f
  map_add' := comapDomain_add_of_injective hf

Depends on / 依赖: comapDomain, hf.injOn
-/
def comapDomain.addMonoidHom (hf : Function.Injective f) : (β ->₀ M) ->+ α ->₀ M where
  toFun x := comapDomain f x hf.injOn
  map_zero' := comapDomain_zero f
  map_add' := comapDomain_add_of_injective hf

end AddZeroClass

variable [AddCommMonoid M] (f : α -> β)

/--
theorem `mapDomain_comapDomain` / 定理 `mapDomain_comapDomain`

English:
theorem mapDomain_comapDomain
  statement: (hf : Function.Injective f) (l : β ->₀ M)
  proof: by
  conv_rhs => rw [← embDomain_comapDomain (f := ⟨f, hf⟩) hl (M := M), embDomain_eq_mapDomain]
  rfl

中文:
定理 mapDomain_comapDomain
  结论: (hf : Function.Injective f) (l : β ->₀ M)
  证明: by
  conv_rhs => rw [← embDomain_comapDomain (f := ⟨f, hf⟩) hl (M := M), embDomain_eq_mapDomain]
  rfl

Depends on / 依赖: conv_rhs, embDomain_comapDomain, embDomain_eq_mapDomain
-/
theorem mapDomain_comapDomain (hf : Function.Injective f) (l : β ->₀ M)
    (hl : ↑l.support subseteq Set.range f) :
    mapDomain f (comapDomain f l hf.injOn) = l := by
  conv_rhs => rw [← embDomain_comapDomain (f := ⟨f, hf⟩) hl (M := M), embDomain_eq_mapDomain]
  rfl

/--
theorem `mapDomain_comapDomain_nat_add_one` / 定理 `mapDomain_comapDomain_nat_add_one`

English:
theorem mapDomain_comapDomain_nat_add_one
  given: (l : Nat ->₀ M)
  proof: by
  refine .trans ?_ (mapDomain_comapDomain _ (add_left_injective 1) _ fun _ => ?_)
  · congr; ext; simp
  · simp_all [Nat.pos_iff_ne_zero]

中文:
定理 mapDomain_comapDomain_nat_add_one
  条件: (l : 自然数 ->₀ M)
  证明: by
  refine .trans ?_ (mapDomain_comapDomain _ (add_left_injective 1) _ fun _ => ?_)
  · congr; ext; simp
  · simp_all [Nat.pos_iff_ne_zero]

Depends on / 依赖: Nat.pos_iff_ne_zero, add_left_injective, mapDomain_comapDomain, pos_iff_ne_zero
-/
theorem mapDomain_comapDomain_nat_add_one (l : Nat ->₀ M) :
    mapDomain (· + 1) (comapDomain.addMonoidHom (add_left_injective 1) l) = l.erase 0 := by
  refine .trans ?_ (mapDomain_comapDomain _ (add_left_injective 1) _ fun _ => ?_)
  · congr; ext; simp
  · simp_all [Nat.pos_iff_ne_zero]

/--
theorem `comapDomain_mapDomain` / 定理 `comapDomain_mapDomain`

English:
theorem comapDomain_mapDomain
  given: (hf : Function.Injective f) (l : α ->₀ M)
  proof: by
  ext; rw [comapDomain_apply, mapDomain_apply hf]

中文:
定理 comapDomain_mapDomain
  条件: (hf : Function.Injective f) (l : α ->₀ M)
  证明: by
  ext; rw [comapDomain_apply, mapDomain_apply hf]

Depends on / 依赖: comapDomain_apply, mapDomain_apply
-/
theorem comapDomain_mapDomain (hf : Function.Injective f) (l : α ->₀ M) :
    comapDomain f (mapDomain f l) hf.injOn = l := by
  ext; rw [comapDomain_apply, mapDomain_apply hf]

/--
lemma `mem_range_mapDomain_iff` / 引理 `mem_range_mapDomain_iff`

English:
lemma mem_range_mapDomain_iff
  given: (hf : Function.Injective f) (x : β ->₀ M)
  proof: by
  refine ⟨fun ⟨y, hy⟩ x hx => hy ▸ Finsupp.mapDomain_of_notMem_range y x hx, fun h => ?_⟩
  refine ⟨Finsupp.comapDomain f x hf.injOn, Finsupp.mapDomain_comapDomain f hf _ fun i hi => ?_⟩
  by_contra hc
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq] at hi
  exact hi (h _ hc)

中文:
引理 mem_range_mapDomain_iff
  条件: (hf : Function.Injective f) (x : β ->₀ M)
  证明: by
  refine ⟨fun ⟨y, hy⟩ x hx => hy ▸ Finsupp.mapDomain_of_notMem_range y x hx, fun h => ?_⟩
  refine ⟨Finsupp.comapDomain f x hf.injOn, Finsupp.mapDomain_comapDomain f hf _ fun i hi => ?_⟩
  by_contra hc
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq] at hi
  exact hi (h _ hc)

Depends on / 依赖: Finset, Finset.mem_coe, Finsupp, Finsupp.comapDomain, Finsupp.mapDomain_comapDomain, Finsupp.mapDomain_of_notMem_range, Finsupp.mem_support_iff, comapDomain, hf.injOn, mapDomain_comapDomain, mapDomain_of_notMem_range, mem_coe, mem_support_iff, ne_eq
-/
lemma mem_range_mapDomain_iff (hf : Function.Injective f) (x : β ->₀ M) :
    x in Set.range (Finsupp.mapDomain f) ↔ forall b ∉ Set.range f, x b = 0 := by
  refine ⟨fun ⟨y, hy⟩ x hx => hy ▸ Finsupp.mapDomain_of_notMem_range y x hx, fun h => ?_⟩
  refine ⟨Finsupp.comapDomain f x hf.injOn, Finsupp.mapDomain_comapDomain f hf _ fun i hi => ?_⟩
  by_contra hc
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq] at hi
  exact hi (h _ hc)

end FInjective

end ComapDomain


/-! ### Declarations about `Finsupp.filter` -/


section Filter

section Zero

variable [Zero M] (p : α -> Prop) [DecidablePred p] (f : α ->₀ M)

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (p : α -> Prop) [DecidablePred p] (f : α ->₀ M)
  body: if p a then f a else 0
  support := f.support.filter p
  mem_support_toFun a := by
    split_ifs with h <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto

中文:
定义 filter
  签名: (p : α -> 命题) [DecidablePred p] (f : α ->₀ M)
  定义体: if p a then f a else 0
  support := f.support.filter p
  mem_support_toFun a := by
    split_ifs with h <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto
-/
def filter (p : α -> Prop) [DecidablePred p] (f : α ->₀ M) : α ->₀ M where
  toFun a := if p a then f a else 0
  support := f.support.filter p
  mem_support_toFun a := by
    split_ifs with h <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto

/--
theorem `filter_apply` / 定理 `filter_apply`

English:
theorem filter_apply
  given: (a : α)
  statement: f.filter p a = if p a then f a else 0
  proof: rfl

中文:
定理 filter_apply
  条件: (a : α)
  结论: f.filter p a = if p a then f a else 0
  证明: rfl

Depends on / 依赖: Nat.pos_of_ne_zero, NeZero, NeZero.ne, pos_of_ne_zero
-/
theorem filter_apply (a : α) : f.filter p a = if p a then f a else 0 := rfl

/--
lemma `filter_eq` / 引理 `filter_eq`

English:
lemma filter_eq
  given: [DecidableEq α] (f : α ->₀ M) (a : α)
  proof: by ext; rw [filter_apply, single_apply]; congr!; simp_all

中文:
引理 filter_eq
  条件: [DecidableEq α] (f : α ->₀ M) (a : α)
  证明: by ext; rw [filter_apply, single_apply]; congr!; simp_all
-/
@[simp] lemma filter_eq [DecidableEq α] (f : α ->₀ M) (a : α) :
    f.filter (a = ·) = single a (f a) := by ext; rw [filter_apply, single_apply]; congr!; simp_all

/--
lemma `filter_eq'` / 引理 `filter_eq'`

English:
lemma filter_eq'
  given: [DecidableEq α] (f : α ->₀ M) (a : α)
  proof: by simp [eq_comm]

中文:
引理 filter_eq'
  条件: [DecidableEq α] (f : α ->₀ M) (a : α)
  证明: by simp [eq_comm]
-/
@[simp] lemma filter_eq' [DecidableEq α] (f : α ->₀ M) (a : α) :
    f.filter (· = a) = single a (f a) := by simp [eq_comm]

/--
theorem `filter_eq_indicator` / 定理 `filter_eq_indicator`

English:
theorem filter_eq_indicator
  statement: ⇑(f.filter p) = Set.indicator { x | p x } f
  proof: by
  ext
  simp [filter_apply, Set.indicator_apply]

中文:
定理 filter_eq_indicator
  结论: ⇑(f.filter p) = Set.indicator { x | p x } f
  证明: by
  ext
  simp [filter_apply, Set.indicator_apply]

Depends on / 依赖: Set.indicator_apply, filter_apply, indicator_apply
-/
theorem filter_eq_indicator : ⇑(f.filter p) = Set.indicator { x | p x } f := by
  ext
  simp [filter_apply, Set.indicator_apply]

/--
theorem `filter_eq_zero_iff` / 定理 `filter_eq_zero_iff`

English:
theorem filter_eq_zero_iff
  statement: f.filter p = 0 ↔ forall x, p x -> f x = 0
  proof: by
  simp [DFunLike.ext_iff, filter_eq_indicator]

中文:
定理 filter_eq_zero_iff
  结论: f.filter p = 0 ↔ 对任意 x, p x -> f x = 0
  证明: by
  simp [DFunLike.ext_iff, filter_eq_indicator]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, filter_eq_indicator
-/
theorem filter_eq_zero_iff : f.filter p = 0 ↔ forall x, p x -> f x = 0 := by
  simp [DFunLike.ext_iff, filter_eq_indicator]

/--
theorem `filter_eq_self_iff` / 定理 `filter_eq_self_iff`

English:
theorem filter_eq_self_iff
  statement: f.filter p = f ↔ forall x, f x != 0 -> p x
  proof: by
  simp only [DFunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_ofPred_eq,
    not_imp_comm]

@[simp]

中文:
定理 filter_eq_self_iff
  结论: f.filter p = f ↔ 对任意 x, f x != 0 -> p x
  证明: by
  simp only [DFunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_ofPred_eq,
    not_imp_comm]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Set.indicator_apply_eq_self, Set.mem_ofPred_eq, ext_iff, filter_eq_indicator, indicator_apply_eq_self, mem_ofPred_eq, not_imp_comm
-/
theorem filter_eq_self_iff : f.filter p = f ↔ forall x, f x != 0 -> p x := by
  simp only [DFunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_ofPred_eq,
    not_imp_comm]

@[simp]
/--
theorem `filter_apply_pos` / 定理 `filter_apply_pos`

English:
theorem filter_apply_pos
  given: {a : α} (h : p a)
  statement: f.filter p a = f a
  proof: if_pos h

@[simp]

中文:
定理 filter_apply_pos
  条件: {a : α} (h : p a)
  结论: f.filter p a = f a
  证明: if_pos h

@[simp]

Depends on / 依赖: if_pos
-/
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a := if_pos h

@[simp]
/--
theorem `filter_apply_neg` / 定理 `filter_apply_neg`

English:
theorem filter_apply_neg
  given: {a : α} (h : ¬p a)
  statement: f.filter p a = 0
  proof: if_neg h

@[simp]

中文:
定理 filter_apply_neg
  条件: {a : α} (h : ¬p a)
  结论: f.filter p a = 0
  证明: if_neg h

@[simp]

Depends on / 依赖: if_neg
-/
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 := if_neg h

@[simp]
/--
theorem `support_filter` / 定理 `support_filter`

English:
theorem support_filter
  statement: (f.filter p).support = {x in f.support | p x}
  proof: rfl

中文:
定理 support_filter
  结论: (f.filter p).support = {x in f.support | p x}
  证明: rfl
-/
theorem support_filter : (f.filter p).support = {x in f.support | p x} := rfl

/--
theorem `filter_zero` / 定理 `filter_zero`

English:
theorem filter_zero
  statement: (0 : α ->₀ M).filter p = 0
  proof: by
  rw [← support_eq_empty]; rw [support_filter]; rw [support_zero]; rw [Finset.filter_empty]

@[simp]

中文:
定理 filter_zero
  结论: (0 : α ->₀ M).filter p = 0
  证明: by
  rw [← support_eq_empty]; rw [support_filter]; rw [support_zero]; rw [Finset.filter_empty]

@[simp]

Depends on / 依赖: Finset, Finset.filter_empty, filter_empty, support_eq_empty, support_filter, support_zero
-/
theorem filter_zero : (0 : α ->₀ M).filter p = 0 := by
  rw [← support_eq_empty]; rw [support_filter]; rw [support_zero]; rw [Finset.filter_empty]

@[simp]
/--
theorem `filter_single_of_pos` / 定理 `filter_single_of_pos`

English:
theorem filter_single_of_pos
  given: {a : α} {b : M} (h : p a)
  statement: (single a b).filter p = single a b
  proof: (filter_eq_self_iff _ _).2 fun _ hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]

中文:
定理 filter_single_of_pos
  条件: {a : α} {b : M} (h : p a)
  结论: (single a b).filter p = single a b
  证明: (filter_eq_self_iff _ _).2 fun _ hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]

Depends on / 依赖: filter_eq_self_iff, single_apply_ne_zero
-/
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  (filter_eq_self_iff _ _).2 fun _ hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]
/--
theorem `filter_single_of_neg` / 定理 `filter_single_of_neg`

English:
theorem filter_single_of_neg
  given: {a : α} {b : M} (h : ¬p a)
  statement: (single a b).filter p = 0
  proof: (filter_eq_zero_iff _ _).2 fun _ hpx =>
    single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]

中文:
定理 filter_single_of_neg
  条件: {a : α} {b : M} (h : ¬p a)
  结论: (single a b).filter p = 0
  证明: (filter_eq_zero_iff _ _).2 fun _ hpx =>
    single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]

Depends on / 依赖: absurd, filter_eq_zero_iff, hxa.symm, single_apply_eq_zero
-/
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  (filter_eq_zero_iff _ _).2 fun _ hpx =>
    single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]
/--
theorem `prod_filter_index` / 定理 `prod_filter_index`

English:
theorem prod_filter_index
  given: [CommMonoid N] (g : α -> M -> N)
  proof: by
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [support_filter]; rw [Finset.mem_filter] at hx
  rw [filter_apply_pos _ _ hx.2]

@[to_additive (attr := simp)]

中文:
定理 prod_filter_index
  条件: [CommMonoid N] (g : α -> M -> N)
  证明: by
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [support_filter]; rw [Finset.mem_filter] at hx
  rw [filter_apply_pos _ _ hx.2]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.mem_filter, Finset.prod_congr, filter_apply_pos, mem_filter, prod_congr, support_filter
-/
theorem prod_filter_index [CommMonoid N] (g : α -> M -> N) :
    (f.filter p).prod g = ∏ x in (f.filter p).support, g x (f x) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [support_filter]; rw [Finset.mem_filter] at hx
  rw [filter_apply_pos _ _ hx.2]

@[to_additive (attr := simp)]
/--
theorem `prod_filter_mul_prod_filter_not` / 定理 `prod_filter_mul_prod_filter_not`

English:
theorem prod_filter_mul_prod_filter_not
  given: [CommMonoid N] (g : α -> M -> N)
  proof: by
  simp_rw [prod_filter_index, support_filter, Finset.prod_filter_mul_prod_filter_not, Finsupp.prod]

@[to_additive (attr := simp)]

中文:
定理 prod_filter_mul_prod_filter_not
  条件: [CommMonoid N] (g : α -> M -> N)
  证明: by
  simp_rw [prod_filter_index, support_filter, Finset.prod_filter_mul_prod_filter_not, Finsupp.prod]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_filter_mul_prod_filter_not, Finsupp, Finsupp.prod, prod_filter_index, prod_filter_mul_prod_filter_not, simp_rw, support_filter
-/
theorem prod_filter_mul_prod_filter_not [CommMonoid N] (g : α -> M -> N) :
    (f.filter p).prod g * (f.filter fun a => ¬p a).prod g = f.prod g := by
  simp_rw [prod_filter_index, support_filter, Finset.prod_filter_mul_prod_filter_not, Finsupp.prod]

@[to_additive (attr := simp)]
/--
theorem `prod_div_prod_filter` / 定理 `prod_div_prod_filter`

English:
theorem prod_div_prod_filter
  given: [CommGroup G] (g : α -> M -> G)
  proof: div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

中文:
定理 prod_div_prod_filter
  条件: [CommGroup G] (g : α -> M -> G)
  证明: div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

Depends on / 依赖: div_eq_of_eq_mul, prod_filter_mul_prod_filter_not
-/
theorem prod_div_prod_filter [CommGroup G] (g : α -> M -> G) :
    f.prod g / (f.filter p).prod g = (f.filter fun a => ¬p a).prod g :=
  div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end Zero

section AddCommMonoid
variable [AddCommMonoid M]

@[simp]
/--
lemma `filter_add_filter_not` / 引理 `filter_add_filter_not`

English:
lemma filter_add_filter_not
  given: (f : α ->₀ M) (p : α -> Prop) [DecidablePred p]
  proof: by ext; simp [filter_apply]; split <;> simp

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

中文:
引理 filter_add_filter_not
  条件: (f : α ->₀ M) (p : α -> 命题) [DecidablePred p]
  证明: by ext; simp [filter_apply]; split <;> simp

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

Depends on / 依赖: filter_apply
-/
lemma filter_add_filter_not (f : α ->₀ M) (p : α -> Prop) [DecidablePred p] :
    f.filter p + f.filter (¬ p ·) = f := by ext; simp [filter_apply]; split <;> simp

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

end AddCommMonoid
end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [Zero M]

/--
Definition of `frange` / `frange` 的定义

English:
definition frange
  signature: (f : α ->₀ M)
  body: haveI := Classical.decEq M
  Finset.image f f.support

@[simp, grind =]

中文:
定义 frange
  签名: (f : α ->₀ M)
  定义体: haveI := Classical.decEq M
  Finset.image f f.support

@[simp, grind =]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.image, f.support, support
-/
def frange (f : α ->₀ M) : Finset M :=
  haveI := Classical.decEq M
  Finset.image f f.support

@[simp, grind =]
/--
theorem `mem_frange` / 定理 `mem_frange`

English:
theorem mem_frange
  given: {f : α ->₀ M} {y : M}
  statement: y in f.frange ↔ y != 0 ∧ y in Set.range f
  proof: by
  rw [frange]; rw [@Finset.mem_image _ _ (Classical.decEq _) _ f.support]
  exact ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
    ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

中文:
定理 mem_frange
  条件: {f : α ->₀ M} {y : M}
  结论: y in f.frange ↔ y != 0 ∧ y in Set.range f
  证明: by
  rw [frange]; rw [@Finset.mem_image _ _ (Classical.decEq _) _ f.support]
  exact ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
    ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.mem_image, f.support, frange, hx.symm, mem_image, mem_support_iff, support
-/
theorem mem_frange {f : α ->₀ M} {y : M} : y in f.frange ↔ y != 0 ∧ y in Set.range f := by
  rw [frange]; rw [@Finset.mem_image _ _ (Classical.decEq _) _ f.support]
  exact ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
    ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

/--
theorem `zero_notMem_frange` / 定理 `zero_notMem_frange`

English:
theorem zero_notMem_frange
  given: {f : α ->₀ M}
  statement: (0 : M) ∉ f.frange
  proof: fun H => (mem_frange.1 H).1 rfl

中文:
定理 zero_notMem_frange
  条件: {f : α ->₀ M}
  结论: (0 : M) ∉ f.frange
  证明: fun H => (mem_frange.1 H).1 rfl

Depends on / 依赖: mem_frange
-/
theorem zero_notMem_frange {f : α ->₀ M} : (0 : M) ∉ f.frange := fun H => (mem_frange.1 H).1 rfl

/--
theorem `frange_single` / 定理 `frange_single`

English:
theorem frange_single
  given: {x : α} {y : M}
  statement: frange (single x y) subseteq {y}
  proof: by
  classical grind

中文:
定理 frange_single
  条件: {x : α} {y : M}
  结论: frange (single x y) subseteq {y}
  证明: by
  classical grind

Depends on / 依赖: classical
-/
theorem frange_single {x : α} {y : M} : frange (single x y) subseteq {y} := by
  classical grind

/--
theorem `mem_frange_of_mem` / 定理 `mem_frange_of_mem`

English:
theorem mem_frange_of_mem
  given: {x} {f : α ->₀ M} (h : x in f.support)
  statement: f x in f.frange
  proof: by
  simp_all

中文:
定理 mem_frange_of_mem
  条件: {x} {f : α ->₀ M} (h : x in f.support)
  结论: f x in f.frange
  证明: by
  simp_all
-/
theorem mem_frange_of_mem {x} {f : α ->₀ M} (h : x in f.support) : f x in f.frange := by
  simp_all

/--
theorem `range_subset_insert_frange` / 定理 `range_subset_insert_frange`

English:
theorem range_subset_insert_frange
  given: (f : α ->₀ M)
  statement: Set.range f subseteq insert 0 f.frange
  proof: by
  grind

中文:
定理 range_subset_insert_frange
  条件: (f : α ->₀ M)
  结论: Set.range f subseteq insert 0 f.frange
  证明: by
  grind
-/
theorem range_subset_insert_frange (f : α ->₀ M) : Set.range f subseteq insert 0 f.frange := by
  grind

/--
theorem `finite_range` / 定理 `finite_range`

English:
theorem finite_range
  given: (f : α ->₀ M)
  statement: (Set.range f).Finite
  proof: .subset (by simp) (range_subset_insert_frange f)

中文:
定理 finite_range
  条件: (f : α ->₀ M)
  结论: (Set.range f).Finite
  证明: .subset (by simp) (range_subset_insert_frange f)

Depends on / 依赖: range_subset_insert_frange, subset
-/
theorem finite_range (f : α ->₀ M) : (Set.range f).Finite :=
  .subset (by simp) (range_subset_insert_frange f)

end Frange

/-! ### Declarations about `Finsupp.subtypeDomain` -/


section SubtypeDomain

section Zero

variable [Zero M] {p : α -> Prop}

/--
Definition of `subtypeDomain` / `subtypeDomain` 的定义

English:
definition subtypeDomain
  signature: (p : α -> Prop) (f : α ->₀ M)
  body: haveI := Classical.decPred p
    f.support.subtype p
  toFun := f ∘ Subtype.val
  mem_support_toFun a := by simp only [@mem_subtype _ _ (Classical.decPred p), mem_support_iff]; rfl

@[simp]

中文:
定义 subtypeDomain
  签名: (p : α -> 命题) (f : α ->₀ M)
  定义体: haveI := Classical.decPred p
    f.support.subtype p
  toFun := f ∘ Subtype.val
  mem_support_toFun a := by simp only [@mem_subtype _ _ (Classical.decPred p), mem_support_iff]; rfl

@[simp]

Depends on / 依赖: Classical, Classical.decPred, Subtype, Subtype.val, decPred, f.support.subtype, mem_subtype, mem_support_iff, mem_support_toFun, subtype, support
-/
def subtypeDomain (p : α -> Prop) (f : α ->₀ M) : Subtype p ->₀ M where
  support :=
    haveI := Classical.decPred p
    f.support.subtype p
  toFun := f ∘ Subtype.val
  mem_support_toFun a := by simp only [@mem_subtype _ _ (Classical.decPred p), mem_support_iff]; rfl

@[simp]
/--
theorem `support_subtypeDomain` / 定理 `support_subtypeDomain`

English:
theorem support_subtypeDomain
  given: [D : DecidablePred p] {f : α ->₀ M}
  proof: by rw [Subsingleton.elim D] <;> rfl

@[simp]

中文:
定理 support_subtypeDomain
  条件: [D : DecidablePred p] {f : α ->₀ M}
  证明: by rw [Subsingleton.elim D] <;> rfl

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem support_subtypeDomain [D : DecidablePred p] {f : α ->₀ M} :
    (subtypeDomain p f).support = f.support.subtype p := by rw [Subsingleton.elim D] <;> rfl

@[simp]
/--
theorem `subtypeDomain_apply` / 定理 `subtypeDomain_apply`

English:
theorem subtypeDomain_apply
  given: {a : Subtype p} {v : α ->₀ M}
  statement: (subtypeDomain p v) a = v a.val
  proof: rfl

@[simp]

中文:
定理 subtypeDomain_apply
  条件: {a : Subtype p} {v : α ->₀ M}
  结论: (subtypeDomain p v) a = v a.val
  证明: rfl

@[simp]
-/
theorem subtypeDomain_apply {a : Subtype p} {v : α ->₀ M} : (subtypeDomain p v) a = v a.val :=
  rfl

@[simp]
/--
theorem `subtypeDomain_zero` / 定理 `subtypeDomain_zero`

English:
theorem subtypeDomain_zero
  statement: subtypeDomain p (0 : α ->₀ M) = 0
  proof: rfl

中文:
定理 subtypeDomain_zero
  结论: subtypeDomain p (0 : α ->₀ M) = 0
  证明: rfl
-/
theorem subtypeDomain_zero : subtypeDomain p (0 : α ->₀ M) = 0 :=
  rfl

/--
theorem `subtypeDomain_eq_iff_forall` / 定理 `subtypeDomain_eq_iff_forall`

English:
theorem subtypeDomain_eq_iff_forall
  given: {f g : α ->₀ M}
  proof: by
  simp_rw [DFunLike.ext_iff, subtypeDomain_apply, Subtype.forall]

中文:
定理 subtypeDomain_eq_iff_forall
  条件: {f g : α ->₀ M}
  证明: by
  simp_rw [DFunLike.ext_iff, subtypeDomain_apply, Subtype.forall]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Subtype, Subtype.forall, ext_iff, simp_rw, subtypeDomain_apply
-/
theorem subtypeDomain_eq_iff_forall {f g : α ->₀ M} :
    f.subtypeDomain p = g.subtypeDomain p ↔ forall x, p x -> f x = g x := by
  simp_rw [DFunLike.ext_iff, subtypeDomain_apply, Subtype.forall]

/--
theorem `subtypeDomain_eq_iff` / 定理 `subtypeDomain_eq_iff`

English:
theorem subtypeDomain_eq_iff
  statement: {f g : α ->₀ M}
  proof: subtypeDomain_eq_iff_forall.trans
    ⟨fun H => Finsupp.ext fun _a => (em _).elim (H _ <| hf _ ·) fun haf => (em _).elim (H _ <| hg _ ·)
        fun hag => (notMem_support_iff.mp haf).trans (notMem_support_iff.mp hag).symm,
      fun H _ _ => congr($H _)⟩

中文:
定理 subtypeDomain_eq_iff
  结论: {f g : α ->₀ M}
  证明: subtypeDomain_eq_iff_forall.trans
    ⟨fun H => Finsupp.ext fun _a => (em _).elim (H _ <| hf _ ·) fun haf => (em _).elim (H _ <| hg _ ·)
        fun hag => (notMem_support_iff.mp haf).trans (notMem_support_iff.mp hag).symm,
      fun H _ _ => congr($H _)⟩

Depends on / 依赖: Finsupp, Finsupp.ext, notMem_support_iff, notMem_support_iff.mp, subtypeDomain_eq_iff_forall, subtypeDomain_eq_iff_forall.trans
-/
theorem subtypeDomain_eq_iff {f g : α ->₀ M}
    (hf : forall x in f.support, p x) (hg : forall x in g.support, p x) :
    f.subtypeDomain p = g.subtypeDomain p ↔ f = g :=
  subtypeDomain_eq_iff_forall.trans
    ⟨fun H => Finsupp.ext fun _a => (em _).elim (H _ <| hf _ ·) fun haf => (em _).elim (H _ <| hg _ ·)
        fun hag => (notMem_support_iff.mp haf).trans (notMem_support_iff.mp hag).symm,
      fun H _ _ => congr($H _)⟩

/--
theorem `subtypeDomain_eq_zero_iff'` / 定理 `subtypeDomain_eq_zero_iff'`

English:
theorem subtypeDomain_eq_zero_iff'
  given: {f : α ->₀ M}
  statement: f.subtypeDomain p = 0 ↔ forall x, p x -> f x = 0
  proof: subtypeDomain_eq_iff_forall (g := 0)

中文:
定理 subtypeDomain_eq_zero_iff'
  条件: {f : α ->₀ M}
  结论: f.subtypeDomain p = 0 ↔ 对任意 x, p x -> f x = 0
  证明: subtypeDomain_eq_iff_forall (g := 0)

Depends on / 依赖: subtypeDomain_eq_iff_forall
-/
theorem subtypeDomain_eq_zero_iff' {f : α ->₀ M} : f.subtypeDomain p = 0 ↔ forall x, p x -> f x = 0 :=
  subtypeDomain_eq_iff_forall (g := 0)

/--
theorem `subtypeDomain_eq_zero_iff` / 定理 `subtypeDomain_eq_zero_iff`

English:
theorem subtypeDomain_eq_zero_iff
  given: {f : α ->₀ M} (hf : forall x in f.support, p x)
  proof: subtypeDomain_eq_iff (g := 0) hf (by simp)

@[to_additive]

中文:
定理 subtypeDomain_eq_zero_iff
  条件: {f : α ->₀ M} (hf : 对任意 x in f.support, p x)
  证明: subtypeDomain_eq_iff (g := 0) hf (by simp)

@[to_additive]

Depends on / 依赖: subtypeDomain_eq_iff
-/
theorem subtypeDomain_eq_zero_iff {f : α ->₀ M} (hf : forall x in f.support, p x) :
    f.subtypeDomain p = 0 ↔ f = 0 :=
  subtypeDomain_eq_iff (g := 0) hf (by simp)

@[to_additive]
/--
theorem `prod_subtypeDomain_index` / 定理 `prod_subtypeDomain_index`

English:
theorem prod_subtypeDomain_index
  statement: [CommMonoid N] {v : α ->₀ M} {h : α -> M -> N}
  proof: by
  refine Finset.prod_bij (fun p _ => p) ?_ ?_ ?_ ?_ <;> aesop

中文:
定理 prod_subtypeDomain_index
  结论: [CommMonoid N] {v : α ->₀ M} {h : α -> M -> N}
  证明: by
  refine Finset.prod_bij (fun p _ => p) ?_ ?_ ?_ ?_ <;> aesop

Depends on / 依赖: Finset, Finset.prod_bij, prod_bij
-/
theorem prod_subtypeDomain_index [CommMonoid N] {v : α ->₀ M} {h : α -> M -> N}
    (hp : forall x in v.support, p x) : (v.subtypeDomain p).prod (fun a b => h a b) = v.prod h := by
  refine Finset.prod_bij (fun p _ => p) ?_ ?_ ?_ ?_ <;> aesop

end Zero

section AddZeroClass

variable [AddZeroClass M] {p : α -> Prop} {v v' : α ->₀ M}

@[simp]
/--
theorem `subtypeDomain_add` / 定理 `subtypeDomain_add`

English:
theorem subtypeDomain_add
  given: {v v' : α ->₀ M}
  proof: ext fun _ => rfl

中文:
定理 subtypeDomain_add
  条件: {v v' : α ->₀ M}
  证明: ext fun _ => rfl
-/
theorem subtypeDomain_add {v v' : α ->₀ M} :
    (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun _ => rfl

/--
Definition of `subtypeDomainAddMonoidHom` / `subtypeDomainAddMonoidHom` 的定义

English:
definition subtypeDomainAddMonoidHom
  signature: : (α ->₀ M) ->+ Subtype p ->₀ M where
  body: subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' _ _ := subtypeDomain_add

中文:
定义 subtypeDomainAddMonoidHom
  签名: : (α ->₀ M) ->+ Subtype p ->₀ M where
  定义体: subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' _ _ := subtypeDomain_add

Depends on / 依赖: subtypeDomain
-/
def subtypeDomainAddMonoidHom : (α ->₀ M) ->+ Subtype p ->₀ M where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' _ _ := subtypeDomain_add

/--
Definition of `filterAddHom` / `filterAddHom` 的定义

English:
definition filterAddHom
  signature: (p : α -> Prop) [DecidablePred p]
  body: filter p
  map_zero' := filter_zero p
map_add' f g := DFunLike.coe_injective by
    simp_rw [coe_add, filter_eq_indicator]
    exact Set.indicator_add { x | p x } f g

@[simp]

中文:
定义 filterAddHom
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: filter p
  map_zero' := filter_zero p
map_add' f g := DFunLike.coe_injective by
    simp_rw [coe_add, filter_eq_indicator]
    exact Set.indicator_add { x | p x } f g

@[simp]

Depends on / 依赖: filter
-/
def filterAddHom (p : α -> Prop) [DecidablePred p] : (α ->₀ M) ->+ α ->₀ M where
  toFun := filter p
  map_zero' := filter_zero p
map_add' f g := DFunLike.coe_injective by
    simp_rw [coe_add, filter_eq_indicator]
    exact Set.indicator_add { x | p x } f g

@[simp]
/--
theorem `filter_add` / 定理 `filter_add`

English:
theorem filter_add
  given: [DecidablePred p] {v v' : α ->₀ M}
  proof: (filterAddHom p).map_add v v'

中文:
定理 filter_add
  条件: [DecidablePred p] {v v' : α ->₀ M}
  证明: (filterAddHom p).map_add v v'

Depends on / 依赖: filterAddHom, map_add
-/
theorem filter_add [DecidablePred p] {v v' : α ->₀ M} :
    (v + v').filter p = v.filter p + v'.filter p :=
  (filterAddHom p).map_add v v'

end AddZeroClass

section CommMonoid

variable [AddCommMonoid M] {p : α -> Prop}

/--
theorem `subtypeDomain_sum` / 定理 `subtypeDomain_sum`

English:
theorem subtypeDomain_sum
  given: {s : Finset ι} {h : ι -> α ->₀ M}
  proof: map_sum subtypeDomainAddMonoidHom _ s

中文:
定理 subtypeDomain_sum
  条件: {s : Finset ι} {h : ι -> α ->₀ M}
  证明: map_sum subtypeDomainAddMonoidHom _ s

Depends on / 依赖: map_sum, subtypeDomainAddMonoidHom
-/
theorem subtypeDomain_sum {s : Finset ι} {h : ι -> α ->₀ M} :
    (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  map_sum subtypeDomainAddMonoidHom _ s

/--
theorem `subtypeDomain_finsupp_sum` / 定理 `subtypeDomain_finsupp_sum`

English:
theorem subtypeDomain_finsupp_sum
  given: [Zero N] {s : β ->₀ N} {h : β -> N -> α ->₀ M}
  proof: subtypeDomain_sum

中文:
定理 subtypeDomain_finsupp_sum
  条件: [Zero N] {s : β ->₀ N} {h : β -> N -> α ->₀ M}
  证明: subtypeDomain_sum

Depends on / 依赖: subtypeDomain_sum
-/
theorem subtypeDomain_finsupp_sum [Zero N] {s : β ->₀ N} {h : β -> N -> α ->₀ M} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum

/--
theorem `filter_sum` / 定理 `filter_sum`

English:
theorem filter_sum
  given: [DecidablePred p] (s : Finset ι) (f : ι -> α ->₀ M)
  proof: map_sum (filterAddHom p) f s

中文:
定理 filter_sum
  条件: [DecidablePred p] (s : Finset ι) (f : ι -> α ->₀ M)
  证明: map_sum (filterAddHom p) f s

Depends on / 依赖: filterAddHom, map_sum
-/
theorem filter_sum [DecidablePred p] (s : Finset ι) (f : ι -> α ->₀ M) :
    (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
  map_sum (filterAddHom p) f s

/--
theorem `filter_eq_sum` / 定理 `filter_eq_sum`

English:
theorem filter_eq_sum
  given: (p : α -> Prop) [DecidablePred p] (f : α ->₀ M)
  proof: (f.filter p).sum_single.symm.trans
    Finset.sum_congr rfl fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

中文:
定理 filter_eq_sum
  条件: (p : α -> 命题) [DecidablePred p] (f : α ->₀ M)
  证明: (f.filter p).sum_single.symm.trans
    Finset.sum_congr rfl fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

Depends on / 依赖: Finset, Finset.sum_congr, f.filter, filter, filter_apply_pos, mem_filter, sum_congr, sum_single, sum_single.symm.trans
-/
theorem filter_eq_sum (p : α -> Prop) [DecidablePred p] (f : α ->₀ M) :
    f.filter p = ∑ i in f.support.filter p, single i (f i) :=
(f.filter p).sum_single.symm.trans
    Finset.sum_congr rfl fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end CommMonoid

section Group

variable [AddGroup G] {p : α -> Prop} {v v' : α ->₀ G}

@[simp]
/--
theorem `subtypeDomain_neg` / 定理 `subtypeDomain_neg`

English:
theorem subtypeDomain_neg
  statement: (-v).subtypeDomain p = -v.subtypeDomain p
  proof: ext fun _ => rfl

@[simp]

中文:
定理 subtypeDomain_neg
  结论: (-v).subtypeDomain p = -v.subtypeDomain p
  证明: ext fun _ => rfl

@[simp]
-/
theorem subtypeDomain_neg : (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
/--
theorem `subtypeDomain_sub` / 定理 `subtypeDomain_sub`

English:
theorem subtypeDomain_sub
  statement: (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p
  proof: ext fun _ => rfl

@[simp]

中文:
定理 subtypeDomain_sub
  结论: (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p
  证明: ext fun _ => rfl

@[simp]
-/
theorem subtypeDomain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
/--
theorem `filter_neg` / 定理 `filter_neg`

English:
theorem filter_neg
  given: (p : α -> Prop) [DecidablePred p] (f : α ->₀ G)
  statement: filter p (-f) = -filter p f
  proof: (filterAddHom p : (_ ->₀ G) ->+ _).map_neg f

@[simp]

中文:
定理 filter_neg
  条件: (p : α -> 命题) [DecidablePred p] (f : α ->₀ G)
  结论: filter p (-f) = -filter p f
  证明: (filterAddHom p : (_ ->₀ G) ->+ _).map_neg f

@[simp]

Depends on / 依赖: filterAddHom, map_neg
-/
theorem filter_neg (p : α -> Prop) [DecidablePred p] (f : α ->₀ G) : filter p (-f) = -filter p f :=
  (filterAddHom p : (_ ->₀ G) ->+ _).map_neg f

@[simp]
/--
theorem `filter_sub` / 定理 `filter_sub`

English:
theorem filter_sub
  given: (p : α -> Prop) [DecidablePred p] (f₁ f₂ : α ->₀ G)
  proof: (filterAddHom p : (_ ->₀ G) ->+ _).map_sub f₁ f₂

中文:
定理 filter_sub
  条件: (p : α -> 命题) [DecidablePred p] (f₁ f₂ : α ->₀ G)
  证明: (filterAddHom p : (_ ->₀ G) ->+ _).map_sub f₁ f₂

Depends on / 依赖: filterAddHom, map_sub
-/
theorem filter_sub (p : α -> Prop) [DecidablePred p] (f₁ f₂ : α ->₀ G) :
    filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filterAddHom p : (_ ->₀ G) ->+ _).map_sub f₁ f₂

end Group

end SubtypeDomain

/--
theorem `mem_support_multiset_sum` / 定理 `mem_support_multiset_sum`

English:
theorem mem_support_multiset_sum
  given: [AddCommMonoid M] {s : Multiset (α ->₀ M)} (a : α)
  proof: Multiset.induction_on s (fun h => False.elim (by simp at h))
    (by
      intro f s ih ha
      by_cases h : a in f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      · simp_rw [Multiset.sum_cons, mem_support_iff, add_apply, notMem_support_iff.1 h,
          zero_add] at ha
        rcas

中文:
定理 mem_support_multiset_sum
  条件: [AddCommMonoid M] {s : Multiset (α ->₀ M)} (a : α)
  证明: Multiset.induction_on s (fun h => False.elim (by simp at h))
    (by
      intro f s ih ha
      by_cases h : a in f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      · simp_rw [Multiset.sum_cons, mem_support_iff, add_apply, notMem_support_iff.1 h,
          zero_add] at ha
        rcas

Depends on / 依赖: False.elim, Multiset, Multiset.induction_on, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Multiset.sum_cons, add_apply, f.support, induction_on, mem_cons_of_mem, mem_cons_self, mem_support_iff, notMem_support_iff, simp_rw, sum_cons, support, zero_add
-/
theorem mem_support_multiset_sum [AddCommMonoid M] {s : Multiset (α ->₀ M)} (a : α) :
    a in s.sum.support -> exists f in s, a in (f : α ->₀ M).support :=
  Multiset.induction_on s (fun h => False.elim (by simp at h))
    (by
      intro f s ih ha
      by_cases h : a in f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      · simp_rw [Multiset.sum_cons, mem_support_iff, add_apply, notMem_support_iff.1 h,
          zero_add] at ha
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩)

/--
theorem `mem_support_finsetSum` / 定理 `mem_support_finsetSum`

English:
theorem mem_support_finsetSum
  statement: [AddCommMonoid M] {s : Finset ι} {h : ι -> α ->₀ M} (a : α)
  proof: let ⟨_, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

@[deprecated (since := "2026-04-08")] alias mem_support_finset_sum := mem_support_finsetSum

中文:
定理 mem_support_finsetSum
  结论: [AddCommMonoid M] {s : Finset ι} {h : ι -> α ->₀ M} (a : α)
  证明: let ⟨_, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

@[deprecated (since := "2026-04-08")] alias mem_support_finset_sum := mem_support_finsetSum

Depends on / 依赖: Eq.symm, Multiset, Multiset.mem_map, mem_map, mem_support_multiset_sum
-/
theorem mem_support_finsetSum [AddCommMonoid M] {s : Finset ι} {h : ι -> α ->₀ M} (a : α)
    (ha : a in (∑ c in s, h c).support) : exists c in s, a in (h c).support :=
  let ⟨_, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

@[deprecated (since := "2026-04-08")] alias mem_support_finset_sum := mem_support_finsetSum

/-! ### Declarations about `curry` and `uncurry` -/


section Uncurry

variable [Zero M]

/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: (f : α ->₀ β ->₀ M)
  body: f x.1 x.2
support := f.support.disjiUnion (fun a => (f a).support.map <| .sectR a _) by
    intro a₁ _ a₂ _ hne
    simp [Finset.disjoint_iff_ne, hne]
  mem_support_toFun := by aesop

中文:
定义 uncurry
  签名: (f : α ->₀ β ->₀ M)
  定义体: f x.1 x.2
support := f.support.disjiUnion (fun a => (f a).support.map <| .sectR a _) by
    intro a₁ _ a₂ _ hne
    simp [Finset.disjoint_iff_ne, hne]
  mem_support_toFun := by aesop
-/
protected def uncurry (f : α ->₀ β ->₀ M) : α × β ->₀ M where
  toFun x := f x.1 x.2
support := f.support.disjiUnion (fun a => (f a).support.map <| .sectR a _) by
    intro a₁ _ a₂ _ hne
    simp [Finset.disjoint_iff_ne, hne]
  mem_support_toFun := by aesop

/--
theorem `uncurry_apply` / 定理 `uncurry_apply`

English:
theorem uncurry_apply
  given: (f : α ->₀ β ->₀ M) (x : α × β)
  statement: f.uncurry x = f x.1 x.2
  proof: rfl

@[simp]

中文:
定理 uncurry_apply
  条件: (f : α ->₀ β ->₀ M) (x : α × β)
  结论: f.uncurry x = f x.1 x.2
  证明: rfl

@[simp]
-/
protected theorem uncurry_apply (f : α ->₀ β ->₀ M) (x : α × β) : f.uncurry x = f x.1 x.2 := rfl

@[simp]
/--
theorem `uncurry_apply_pair` / 定理 `uncurry_apply_pair`

English:
theorem uncurry_apply_pair
  given: (f : α ->₀ β ->₀ M) (a : α) (b : β)
  proof: rfl

@[simp]

中文:
定理 uncurry_apply_pair
  条件: (f : α ->₀ β ->₀ M) (a : α) (b : β)
  证明: rfl

@[simp]
-/
protected theorem uncurry_apply_pair (f : α ->₀ β ->₀ M) (a : α) (b : β) :
    f.uncurry (a, b) = f a b :=
  rfl

@[simp]
/--
lemma `uncurry_single` / 引理 `uncurry_single`

English:
lemma uncurry_single
  given: (a : α) (b : β) (m : M)
  proof: by
  ext ⟨x, y⟩
  rcases eq_or_ne a x with rfl | hne <;> classical simp [single_apply, *]

中文:
引理 uncurry_single
  条件: (a : α) (b : β) (m : M)
  证明: by
  ext ⟨x, y⟩
  rcases eq_or_ne a x with rfl | hne <;> classical simp [single_apply, *]

Depends on / 依赖: classical, eq_or_ne, single_apply
-/
lemma uncurry_single (a : α) (b : β) (m : M) :
    (single a (single b m)).uncurry = single (a, b) m := by
  ext ⟨x, y⟩
  rcases eq_or_ne a x with rfl | hne <;> classical simp [single_apply, *]

/--
theorem `sum_uncurry_index` / 定理 `sum_uncurry_index`

English:
theorem sum_uncurry_index
  given: [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α × β -> M -> N)
  proof: by
  simp [Finsupp.sum, Finsupp.uncurry, Finset.sum_disjiUnion]

中文:
定理 sum_uncurry_index
  条件: [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α × β -> M -> N)
  证明: by
  simp [Finsupp.sum, Finsupp.uncurry, Finset.sum_disjiUnion]

Depends on / 依赖: Finset, Finset.sum_disjiUnion, Finsupp, Finsupp.sum, Finsupp.uncurry, sum_disjiUnion, uncurry
-/
theorem sum_uncurry_index [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α × β -> M -> N) :
    f.uncurry.sum (fun p c => g p c) = f.sum fun a f => f.sum fun b => g (a, b) := by
  simp [Finsupp.sum, Finsupp.uncurry, Finset.sum_disjiUnion]

/--
theorem `sum_uncurry_index'` / 定理 `sum_uncurry_index'`

English:
theorem sum_uncurry_index'
  given: [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α -> β -> M -> N)
  proof: sum_uncurry_index ..

中文:
定理 sum_uncurry_index'
  条件: [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α -> β -> M -> N)
  证明: sum_uncurry_index ..

Depends on / 依赖: sum_uncurry_index
-/
theorem sum_uncurry_index' [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α -> β -> M -> N) :
    f.uncurry.sum (fun p c => g p.1 p.2 c) = f.sum fun a f => f.sum (g a) :=
  sum_uncurry_index ..

end Uncurry

section Curry

variable [Zero M]

open scoped Classical in
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (f : α × β ->₀ M)
  body: { toFun b := f (a, b)
support := f.support.filterMap (fun x => if x.1 = a then x.2 else none) by simp +contextual
      mem_support_toFun := by simp }
  support := f.support.image Prod.fst
  mem_support_toFun := by simp [DFunLike.ext_iff]

@[simp]

中文:
定义 curry
  签名: (f : α × β ->₀ M)
  定义体: { toFun b := f (a, b)
support := f.support.filterMap (fun x => if x.1 = a then x.2 else none) by simp +contextual
      mem_support_toFun := by simp }
  support := f.support.image Prod.fst
  mem_support_toFun := by simp [DFunLike.ext_iff]

@[simp]
-/
protected def curry (f : α × β ->₀ M) : α ->₀ β ->₀ M where
  toFun a :=
    { toFun b := f (a, b)
support := f.support.filterMap (fun x => if x.1 = a then x.2 else none) by simp +contextual
      mem_support_toFun := by simp }
  support := f.support.image Prod.fst
  mem_support_toFun := by simp [DFunLike.ext_iff]

@[simp]
/--
theorem `curry_apply` / 定理 `curry_apply`

English:
theorem curry_apply
  given: (f : α × β ->₀ M) (x : α) (y : β)
  statement: f.curry x y = f (x, y)
  proof: rfl

@[simp]

中文:
定理 curry_apply
  条件: (f : α × β ->₀ M) (x : α) (y : β)
  结论: f.curry x y = f (x, y)
  证明: rfl

@[simp]
-/
theorem curry_apply (f : α × β ->₀ M) (x : α) (y : β) : f.curry x y = f (x, y) := rfl

@[simp]
/--
lemma `support_curry` / 引理 `support_curry`

English:
lemma support_curry
  given: [DecidableEq α] (f : α × β ->₀ M)
  proof: by unfold Finsupp.curry; congr!

@[simp]

中文:
引理 support_curry
  条件: [DecidableEq α] (f : α × β ->₀ M)
  证明: by unfold Finsupp.curry; congr!

@[simp]

Depends on / 依赖: Finsupp, Finsupp.curry
-/
lemma support_curry [DecidableEq α] (f : α × β ->₀ M) :
    f.curry.support = f.support.image Prod.fst := by unfold Finsupp.curry; congr!

@[simp]
/--
theorem `curry_uncurry` / 定理 `curry_uncurry`

English:
theorem curry_uncurry
  given: (f : α ->₀ β ->₀ M)
  statement: f.uncurry.curry = f
  proof: by
  ext a b
  simp

@[simp]

中文:
定理 curry_uncurry
  条件: (f : α ->₀ β ->₀ M)
  结论: f.uncurry.curry = f
  证明: by
  ext a b
  simp

@[simp]
-/
theorem curry_uncurry (f : α ->₀ β ->₀ M) : f.uncurry.curry = f := by
  ext a b
  simp

@[simp]
/--
theorem `uncurry_curry` / 定理 `uncurry_curry`

English:
theorem uncurry_curry
  given: (f : α × β ->₀ M)
  statement: f.curry.uncurry = f
  proof: by
  ext ⟨a, b⟩
  simp

@[simp]

中文:
定理 uncurry_curry
  条件: (f : α × β ->₀ M)
  结论: f.curry.uncurry = f
  证明: by
  ext ⟨a, b⟩
  simp

@[simp]
-/
theorem uncurry_curry (f : α × β ->₀ M) : f.curry.uncurry = f := by
  ext ⟨a, b⟩
  simp

@[simp]
/--
lemma `curry_single` / 引理 `curry_single`

English:
lemma curry_single
  given: (a : α × β) (m : M)
  proof: by
  rw [← curry_uncurry (single _ _)]; rw [uncurry_single]

中文:
引理 curry_single
  条件: (a : α × β) (m : M)
  证明: by
  rw [← curry_uncurry (single _ _)]; rw [uncurry_single]

Depends on / 依赖: curry_uncurry, single, uncurry_single
-/
lemma curry_single (a : α × β) (m : M) :
    (single a m).curry = single a.1 (single a.2 m) := by
  rw [← curry_uncurry (single _ _)]; rw [uncurry_single]

/--
theorem `sum_curry_index` / 定理 `sum_curry_index`

English:
theorem sum_curry_index
  given: [AddCommMonoid N] (f : α × β ->₀ M) (g : α -> β -> M -> N)
  proof: by
  rw [← sum_uncurry_index']; rw [uncurry_curry]

中文:
定理 sum_curry_index
  条件: [AddCommMonoid N] (f : α × β ->₀ M) (g : α -> β -> M -> N)
  证明: by
  rw [← sum_uncurry_index']; rw [uncurry_curry]

Depends on / 依赖: sum_uncurry_index, uncurry_curry
-/
theorem sum_curry_index [AddCommMonoid N] (f : α × β ->₀ M) (g : α -> β -> M -> N) :
    (f.curry.sum fun a f => f.sum (g a)) = f.sum fun p c => g p.1 p.2 c := by
  rw [← sum_uncurry_index']; rw [uncurry_curry]

/-- The equivalence between `α × β →₀ M` and `α →₀ β →₀ M` given by currying/uncurrying. -/
@[simps]
/--
Definition of `curryEquiv` / `curryEquiv` 的定义

English:
definition curryEquiv
  signature: : (α × β ->₀ M) ≃ (α ->₀ β ->₀ M) where
  body: Finsupp.curry
  invFun := Finsupp.uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

@[deprecated (since := "2026-01-03")] noncomputable alias finsuppProdEquiv := curryEquiv

中文:
定义 curryEquiv
  签名: : (α × β ->₀ M) ≃ (α ->₀ β ->₀ M) where
  定义体: Finsupp.curry
  invFun := Finsupp.uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

@[deprecated (since := "2026-01-03")] noncomputable alias finsuppProdEquiv := curryEquiv

Depends on / 依赖: Finsupp, Finsupp.curry
-/
def curryEquiv : (α × β ->₀ M) ≃ (α ->₀ β ->₀ M) where
  toFun := Finsupp.curry
  invFun := Finsupp.uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

@[deprecated (since := "2026-01-03")] noncomputable alias finsuppProdEquiv := curryEquiv

/--
theorem `filter_curry` / 定理 `filter_curry`

English:
theorem filter_curry
  given: (f : α × β ->₀ M) (p : α -> Prop) [DecidablePred p]
  proof: by
  ext a b
  simp [filter_apply, apply_ite (DFunLike.coe · b)]

中文:
定理 filter_curry
  条件: (f : α × β ->₀ M) (p : α -> 命题) [DecidablePred p]
  证明: by
  ext a b
  simp [filter_apply, apply_ite (DFunLike.coe · b)]

Depends on / 依赖: DFunLike, DFunLike.coe, apply_ite, filter_apply
-/
theorem filter_curry (f : α × β ->₀ M) (p : α -> Prop) [DecidablePred p] :
    (f.filter fun a : α × β => p a.1).curry = f.curry.filter p := by
  ext a b
  simp [filter_apply, apply_ite (DFunLike.coe · b)]

end Curry

section
variable [AddZeroClass M]

/-- The additive monoid isomorphism between `α × β →₀ M` and `α →₀ β →₀ M` given by
currying/uncurrying. -/
@[simps! symm_apply]
/--
Definition of `curryAddEquiv` / `curryAddEquiv` 的定义

English:
definition curryAddEquiv
  signature: : (α × β ->₀ M) ≃+ (α ->₀ β ->₀ M) where
  body: curryEquiv
  map_add' _ _ := by ext; simp

中文:
定义 curryAddEquiv
  签名: : (α × β ->₀ M) ≃+ (α ->₀ β ->₀ M) where
  定义体: curryEquiv
  map_add' _ _ := by ext; simp

Depends on / 依赖: curryEquiv
-/
noncomputable def curryAddEquiv : (α × β ->₀ M) ≃+ (α ->₀ β ->₀ M) where
  __ := curryEquiv
  map_add' _ _ := by ext; simp

/--
lemma `coe_curryAddEquiv` / 引理 `coe_curryAddEquiv`

English:
lemma coe_curryAddEquiv
  statement: (curryAddEquiv : (α × β ->₀ M) -> α ->₀ β ->₀ M) = .curry
  proof: rfl

中文:
引理 coe_curryAddEquiv
  结论: (curryAddEquiv : (α × β ->₀ M) -> α ->₀ β ->₀ M) = .curry
  证明: rfl
-/
@[simp] lemma coe_curryAddEquiv : (curryAddEquiv : (α × β ->₀ M) -> α ->₀ β ->₀ M) = .curry := rfl

end

/-! ### Declarations about finitely supported functions whose support is a `Sum` type -/


section Sum
variable [Zero γ]

/-- `Finsupp.sumElim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
@[simps support]
/--
Definition of `sumElim` / `sumElim` 的定义

English:
definition sumElim
  signature: (f : α ->₀ γ) (g : β ->₀ γ)
  body: f.support.disjSum g.support
  toFun := Sum.elim f g
  mem_support_toFun := by simp

@[simp, norm_cast]

中文:
定义 sumElim
  签名: (f : α ->₀ γ) (g : β ->₀ γ)
  定义体: f.support.disjSum g.support
  toFun := Sum.elim f g
  mem_support_toFun := by simp

@[simp, norm_cast]

Depends on / 依赖: disjSum, f.support.disjSum, g.support, support
-/
def sumElim (f : α ->₀ γ) (g : β ->₀ γ) : α oplus β ->₀ γ where
  support := f.support.disjSum g.support
  toFun := Sum.elim f g
  mem_support_toFun := by simp

@[simp, norm_cast]
/--
theorem `coe_sumElim` / 定理 `coe_sumElim`

English:
theorem coe_sumElim
  given: (f : α ->₀ γ) (g : β ->₀ γ)
  statement: ⇑(sumElim f g) = Sum.elim f g
  proof: rfl

中文:
定理 coe_sumElim
  条件: (f : α ->₀ γ) (g : β ->₀ γ)
  结论: ⇑(sumElim f g) = Sum.elim f g
  证明: rfl
-/
theorem coe_sumElim (f : α ->₀ γ) (g : β ->₀ γ) : ⇑(sumElim f g) = Sum.elim f g := rfl

/--
theorem `sumElim_apply` / 定理 `sumElim_apply`

English:
theorem sumElim_apply
  given: (f : α ->₀ γ) (g : β ->₀ γ) (x : α oplus β)
  statement: sumElim f g x = Sum.elim f g x
  proof: rfl

中文:
定理 sumElim_apply
  条件: (f : α ->₀ γ) (g : β ->₀ γ) (x : α oplus β)
  结论: sumElim f g x = Sum.elim f g x
  证明: rfl
-/
theorem sumElim_apply (f : α ->₀ γ) (g : β ->₀ γ) (x : α oplus β) : sumElim f g x = Sum.elim f g x := rfl

/--
lemma `sumElim_inl` / 引理 `sumElim_inl`

English:
lemma sumElim_inl
  given: (f : α ->₀ γ) (g : β ->₀ γ) (x : α)
  statement: sumElim f g (Sum.inl x) = f x
  proof: rfl

中文:
引理 sumElim_inl
  条件: (f : α ->₀ γ) (g : β ->₀ γ) (x : α)
  结论: sumElim f g (Sum.inl x) = f x
  证明: rfl
-/
lemma sumElim_inl (f : α ->₀ γ) (g : β ->₀ γ) (x : α) : sumElim f g (Sum.inl x) = f x := rfl
/--
lemma `sumElim_inr` / 引理 `sumElim_inr`

English:
lemma sumElim_inr
  given: (f : α ->₀ γ) (g : β ->₀ γ) (x : β)
  statement: sumElim f g (Sum.inr x) = g x
  proof: rfl

中文:
引理 sumElim_inr
  条件: (f : α ->₀ γ) (g : β ->₀ γ) (x : β)
  结论: sumElim f g (Sum.inr x) = g x
  证明: rfl
-/
lemma sumElim_inr (f : α ->₀ γ) (g : β ->₀ γ) (x : β) : sumElim f g (Sum.inr x) = g x := rfl

/--
lemma `sumElim_zero_zero` / 引理 `sumElim_zero_zero`

English:
lemma sumElim_zero_zero
  statement: sumElim 0 0 = (0 : α oplus β ->₀ γ)
  proof: by ext (_ | _) <;> simp

中文:
引理 sumElim_zero_zero
  结论: sumElim 0 0 = (0 : α oplus β ->₀ γ)
  证明: by ext (_ | _) <;> simp
-/
@[simp] lemma sumElim_zero_zero : sumElim 0 0 = (0 : α oplus β ->₀ γ) := by ext (_ | _) <;> simp

/--
lemma `sumElim_single_zero` / 引理 `sumElim_single_zero`

English:
lemma sumElim_single_zero
  given: (a : α) (c : γ)
  proof: by
  classical ext (_ | _) <;> simp [single_apply]

中文:
引理 sumElim_single_zero
  条件: (a : α) (c : γ)
  证明: by
  classical ext (_ | _) <;> simp [single_apply]
-/
@[simp] lemma sumElim_single_zero (a : α) (c : γ) :
    sumElim (single a c) (0 : β ->₀ γ) = single (.inl a) c := by
  classical ext (_ | _) <;> simp [single_apply]

/--
lemma `sumElim_zero_single` / 引理 `sumElim_zero_single`

English:
lemma sumElim_zero_single
  given: (b : β) (c : γ)
  proof: by
  classical ext (_ | _) <;> simp [single_apply]

中文:
引理 sumElim_zero_single
  条件: (b : β) (c : γ)
  证明: by
  classical ext (_ | _) <;> simp [single_apply]
-/
@[simp] lemma sumElim_zero_single (b : β) (c : γ) :
    sumElim (0 : α ->₀ γ) (single b c) = single (.inr b) c := by
  classical ext (_ | _) <;> simp [single_apply]

/--
lemma `sumElim_single_single` / 引理 `sumElim_single_single`

English:
lemma sumElim_single_single
  given: [AddMonoid M] (a : α) (b : β) (m₁ m₂ : M)
  proof: by
  classical ext (_ | _) <;> simp [single_apply]

中文:
引理 sumElim_single_single
  条件: [AddMonoid M] (a : α) (b : β) (m₁ m₂ : M)
  证明: by
  classical ext (_ | _) <;> simp [single_apply]
-/
@[simp] lemma sumElim_single_single [AddMonoid M] (a : α) (b : β) (m₁ m₂ : M) :
    sumElim (single a m₁) (single b m₂) = single (.inl a) m₁ + single (.inr b) m₂ := by
  classical ext (_ | _) <;> simp [single_apply]

/--
lemma `sumElim_eq_add` / 引理 `sumElim_eq_add`

English:
lemma sumElim_eq_add
  given: [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M)
  proof: by
  ext (_ | _) <;> simp [mapDomain_of_notMem_range, Sum.inl_injective, Sum.inr_injective]

中文:
引理 sumElim_eq_add
  条件: [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M)
  证明: by
  ext (_ | _) <;> simp [mapDomain_of_notMem_range, Sum.inl_injective, Sum.inr_injective]

Depends on / 依赖: Sum.inl_injective, Sum.inr_injective, inl_injective, inr_injective, mapDomain_of_notMem_range
-/
lemma sumElim_eq_add [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M) :
    sumElim f g = mapDomain Sum.inl f + mapDomain Sum.inr g := by
  ext (_ | _) <;> simp [mapDomain_of_notMem_range, Sum.inl_injective, Sum.inr_injective]

/--
lemma `mapDomain_swap_sumElim` / 引理 `mapDomain_swap_sumElim`

English:
lemma mapDomain_swap_sumElim
  given: [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M)
  proof: by
  simp [sumElim_eq_add, mapDomain_add, ← mapDomain_comp, Function.comp_def, add_comm]

@[to_additive]

中文:
引理 mapDomain_swap_sumElim
  条件: [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M)
  证明: by
  simp [sumElim_eq_add, mapDomain_add, ← mapDomain_comp, Function.comp_def, add_comm]

@[to_additive]
-/
@[simp] lemma mapDomain_swap_sumElim [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M) :
    mapDomain Sum.swap (sumElim f g) = sumElim g f := by
  simp [sumElim_eq_add, mapDomain_add, ← mapDomain_comp, Function.comp_def, add_comm]

@[to_additive]
/--
lemma `prod_sumElim` / 引理 `prod_sumElim`

English:
lemma prod_sumElim
  statement: {ι₁ ι₂ α M : Type*} [Zero α] [CommMonoid M]
  proof: by
  simp [Finsupp.prod, Finset.prod_disjSum]

@[simp]

中文:
引理 prod_sumElim
  结论: {ι₁ ι₂ α M : 类型} [Zero α] [CommMonoid M]
  证明: by
  simp [Finsupp.prod, Finset.prod_disjSum]

@[simp]

Depends on / 依赖: Finset, Finset.prod_disjSum, Finsupp, Finsupp.prod, prod_disjSum
-/
lemma prod_sumElim {ι₁ ι₂ α M : Type*} [Zero α] [CommMonoid M]
    (f₁ : ι₁ ->₀ α) (f₂ : ι₂ ->₀ α) (g : ι₁ oplus ι₂ -> α -> M) :
    (f₁.sumElim f₂).prod g = f₁.prod (g ∘ Sum.inl) * f₂.prod (g ∘ Sum.inr) := by
  simp [Finsupp.prod, Finset.prod_disjSum]

@[simp]
/--
lemma `comapDomain_inl_sumElim` / 引理 `comapDomain_inl_sumElim`

English:
lemma comapDomain_inl_sumElim
  given: (f : α ->₀ γ) (g : β ->₀ γ)
  proof: by
  ext; simp

@[simp]

中文:
引理 comapDomain_inl_sumElim
  条件: (f : α ->₀ γ) (g : β ->₀ γ)
  证明: by
  ext; simp

@[simp]
-/
lemma comapDomain_inl_sumElim (f : α ->₀ γ) (g : β ->₀ γ) :
    comapDomain Sum.inl (f.sumElim g) Sum.inl_injective.injOn = f := by
  ext; simp

@[simp]
/--
lemma `comapDomain_inr_sumElim` / 引理 `comapDomain_inr_sumElim`

English:
lemma comapDomain_inr_sumElim
  given: (f : α ->₀ γ) (g : β ->₀ γ)
  proof: by
  ext; simp

@[simp]

中文:
引理 comapDomain_inr_sumElim
  条件: (f : α ->₀ γ) (g : β ->₀ γ)
  证明: by
  ext; simp

@[simp]
-/
lemma comapDomain_inr_sumElim (f : α ->₀ γ) (g : β ->₀ γ) :
    comapDomain Sum.inr (f.sumElim g) Sum.inr_injective.injOn = g := by
  ext; simp

@[simp]
/--
lemma `embDomain_inl` / 引理 `embDomain_inl`

English:
lemma embDomain_inl
  given: (a : α ->₀ γ)
  proof: by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]

中文:
引理 embDomain_inl
  条件: (a : α ->₀ γ)
  证明: by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]

Depends on / 依赖: embDomain_apply
-/
lemma embDomain_inl (a : α ->₀ γ) :
    embDomain Function.Embedding.inl a = sumElim a (0 : β ->₀ γ) := by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]
/--
lemma `embDomain_inr` / 引理 `embDomain_inr`

English:
lemma embDomain_inr
  given: (b : β ->₀ γ)
  proof: by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]

中文:
引理 embDomain_inr
  条件: (b : β ->₀ γ)
  证明: by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]

Depends on / 依赖: embDomain_apply
-/
lemma embDomain_inr (b : β ->₀ γ) :
    embDomain Function.Embedding.inr b = sumElim (0 : α ->₀ γ) b := by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]
/--
lemma `comapDomain_sumElim_comapDomain` / 引理 `comapDomain_sumElim_comapDomain`

English:
lemma comapDomain_sumElim_comapDomain
  given: (c : α oplus β ->₀ γ)
  proof: by
  ext (_ | _) <;> simp

@[simp]

中文:
引理 comapDomain_sumElim_comapDomain
  条件: (c : α oplus β ->₀ γ)
  证明: by
  ext (_ | _) <;> simp

@[simp]
-/
lemma comapDomain_sumElim_comapDomain (c : α oplus β ->₀ γ) :
    (comapDomain Sum.inl c Sum.inl_injective.injOn).sumElim
      (comapDomain Sum.inr c Sum.inr_injective.injOn) = c := by
  ext (_ | _) <;> simp

@[simp]
/--
lemma `sumElim_add` / 引理 `sumElim_add`

English:
lemma sumElim_add
  given: [AddZeroClass M] (a b : α ->₀ M) (c d : β ->₀ M)
  proof: by
  ext (_ | _) <;> simp

中文:
引理 sumElim_add
  条件: [AddZeroClass M] (a b : α ->₀ M) (c d : β ->₀ M)
  证明: by
  ext (_ | _) <;> simp
-/
lemma sumElim_add [AddZeroClass M] (a b : α ->₀ M) (c d : β ->₀ M) :
    (a + b).sumElim (c + d) = a.sumElim c + b.sumElim d := by
  ext (_ | _) <;> simp

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply]
/--
Definition of `sumFinsuppEquivProdFinsupp` / `sumFinsuppEquivProdFinsupp` 的定义

English:
definition sumFinsuppEquivProdFinsupp
  signature: {α β γ : Type*} [Zero γ]
  body: ⟨f.comapDomain Sum.inl Sum.inl_injective.injOn,
      f.comapDomain Sum.inr Sum.inr_injective.injOn⟩
  invFun fg := sumElim fg.1 fg.2
  left_inv f := by
    ext ab
    rcases ab with a | b <;> simp
  right_inv fg := by ext <;> simp

中文:
定义 sumFinsuppEquivProdFinsupp
  签名: {α β γ : 类型} [Zero γ]
  定义体: ⟨f.comapDomain Sum.inl Sum.inl_injective.injOn,
      f.comapDomain Sum.inr Sum.inr_injective.injOn⟩
  invFun fg := sumElim fg.1 fg.2
  left_inv f := by
    ext ab
    rcases ab with a | b <;> simp
  right_inv fg := by ext <;> simp

Depends on / 依赖: Sum.inl, Sum.inl_injective.injOn, Sum.inr, Sum.inr_injective.injOn, comapDomain, f.comapDomain, inl_injective, inr_injective, invFun, left_inv, right_inv, sumElim
-/
def sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] : (α oplus β ->₀ γ) ≃ (α ->₀ γ) × (β ->₀ γ) where
  toFun f :=
    ⟨f.comapDomain Sum.inl Sum.inl_injective.injOn,
      f.comapDomain Sum.inr Sum.inr_injective.injOn⟩
  invFun fg := sumElim fg.1 fg.2
  left_inv f := by
    ext ab
    rcases ab with a | b <;> simp
  right_inv fg := by ext <;> simp

/--
theorem `fst_sumFinsuppEquivProdFinsupp` / 定理 `fst_sumFinsuppEquivProdFinsupp`

English:
theorem fst_sumFinsuppEquivProdFinsupp
  given: {α β γ : Type*} [Zero γ] (f : α oplus β ->₀ γ) (x : α)
  proof: rfl

中文:
定理 fst_sumFinsuppEquivProdFinsupp
  条件: {α β γ : 类型} [Zero γ] (f : α oplus β ->₀ γ) (x : α)
  证明: rfl
-/
theorem fst_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α oplus β ->₀ γ) (x : α) :
    (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

/--
theorem `snd_sumFinsuppEquivProdFinsupp` / 定理 `snd_sumFinsuppEquivProdFinsupp`

English:
theorem snd_sumFinsuppEquivProdFinsupp
  given: {α β γ : Type*} [Zero γ] (f : α oplus β ->₀ γ) (y : β)
  proof: rfl

中文:
定理 snd_sumFinsuppEquivProdFinsupp
  条件: {α β γ : 类型} [Zero γ] (f : α oplus β ->₀ γ) (y : β)
  证明: rfl
-/
theorem snd_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α oplus β ->₀ γ) (y : β) :
    (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

/--
theorem `sumFinsuppEquivProdFinsupp_symm_inl` / 定理 `sumFinsuppEquivProdFinsupp_symm_inl`

English:
theorem sumFinsuppEquivProdFinsupp_symm_inl
  statement: {α β γ : Type*} [Zero γ] (fg : (α ->₀ γ) × (β ->₀ γ))
  proof: rfl

中文:
定理 sumFinsuppEquivProdFinsupp_symm_inl
  结论: {α β γ : 类型} [Zero γ] (fg : (α ->₀ γ) × (β ->₀ γ))
  证明: rfl
-/
theorem sumFinsuppEquivProdFinsupp_symm_inl {α β γ : Type*} [Zero γ] (fg : (α ->₀ γ) × (β ->₀ γ))
    (x : α) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

/--
theorem `sumFinsuppEquivProdFinsupp_symm_inr` / 定理 `sumFinsuppEquivProdFinsupp_symm_inr`

English:
theorem sumFinsuppEquivProdFinsupp_symm_inr
  statement: {α β γ : Type*} [Zero γ] (fg : (α ->₀ γ) × (β ->₀ γ))
  proof: rfl

中文:
定理 sumFinsuppEquivProdFinsupp_symm_inr
  结论: {α β γ : 类型} [Zero γ] (fg : (α ->₀ γ) × (β ->₀ γ))
  证明: rfl
-/
theorem sumFinsuppEquivProdFinsupp_symm_inr {α β γ : Type*} [Zero γ] (fg : (α ->₀ γ) × (β ->₀ γ))
    (y : β) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

variable [AddMonoid M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps! apply symm_apply]
/--
Definition of `sumFinsuppAddEquivProdFinsupp` / `sumFinsuppAddEquivProdFinsupp` 的定义

English:
definition sumFinsuppAddEquivProdFinsupp
  signature: {α β : Type*}
  body: { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply,
          snd_sumFinsuppEquivProdFinsupp, fst_sumFinsuppEquivProdFinsupp] }

中文:
定义 sumFinsuppAddEquivProdFinsupp
  签名: {α β : 类型}
  定义体: { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply,
          snd_sumFinsuppEquivProdFinsupp, fst_sumFinsuppEquivProdFinsupp] }

Depends on / 依赖: Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply, fst_add, fst_sumFinsuppEquivProdFinsupp, intros, map_add, snd_add, snd_sumFinsuppEquivProdFinsupp, sumFinsuppEquivProdFinsupp, toFun_as_coe
-/
def sumFinsuppAddEquivProdFinsupp {α β : Type*} : (α oplus β ->₀ M) ≃+ (α ->₀ M) × (β ->₀ M) :=
  { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply,
          snd_sumFinsuppEquivProdFinsupp, fst_sumFinsuppEquivProdFinsupp] }

/--
theorem `fst_sumFinsuppAddEquivProdFinsupp` / 定理 `fst_sumFinsuppAddEquivProdFinsupp`

English:
theorem fst_sumFinsuppAddEquivProdFinsupp
  given: {α β : Type*} (f : α oplus β ->₀ M) (x : α)
  proof: rfl

中文:
定理 fst_sumFinsuppAddEquivProdFinsupp
  条件: {α β : 类型} (f : α oplus β ->₀ M) (x : α)
  证明: rfl
-/
theorem fst_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (x : α) :
    (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

/--
theorem `snd_sumFinsuppAddEquivProdFinsupp` / 定理 `snd_sumFinsuppAddEquivProdFinsupp`

English:
theorem snd_sumFinsuppAddEquivProdFinsupp
  given: {α β : Type*} (f : α oplus β ->₀ M) (y : β)
  proof: rfl

中文:
定理 snd_sumFinsuppAddEquivProdFinsupp
  条件: {α β : 类型} (f : α oplus β ->₀ M) (y : β)
  证明: rfl
-/
theorem snd_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (y : β) :
    (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

/--
theorem `sumFinsuppAddEquivProdFinsupp_symm_inl` / 定理 `sumFinsuppAddEquivProdFinsupp_symm_inl`

English:
theorem sumFinsuppAddEquivProdFinsupp_symm_inl
  given: {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (x : α)
  proof: rfl

中文:
定理 sumFinsuppAddEquivProdFinsupp_symm_inl
  条件: {α β : 类型} (fg : (α ->₀ M) × (β ->₀ M)) (x : α)
  证明: rfl
-/
theorem sumFinsuppAddEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (x : α) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

/--
theorem `sumFinsuppAddEquivProdFinsupp_symm_inr` / 定理 `sumFinsuppAddEquivProdFinsupp_symm_inr`

English:
theorem sumFinsuppAddEquivProdFinsupp_symm_inr
  given: {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (y : β)
  proof: rfl

中文:
定理 sumFinsuppAddEquivProdFinsupp_symm_inr
  条件: {α β : 类型} (fg : (α ->₀ M) × (β ->₀ M)) (y : β)
  证明: rfl
-/
theorem sumFinsuppAddEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (y : β) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section

variable [Zero R]

/--
Instance `uniqueOfRight` / 实例 `uniqueOfRight`

English:
instance uniqueOfRight
  signature: [Subsingleton R]
  body: DFunLike.coe_injective.unique

中文:
实例 uniqueOfRight
  签名: [Subsingleton R]
  定义体: DFunLike.coe_injective.unique

Depends on / 依赖: DFunLike, DFunLike.coe_injective.unique, coe_injective, unique
-/
instance uniqueOfRight [Subsingleton R] : Unique (α ->₀ R) :=
  DFunLike.coe_injective.unique

/--
Instance `uniqueOfLeft` / 实例 `uniqueOfLeft`

English:
instance uniqueOfLeft
  signature: [IsEmpty α]
  body: DFunLike.coe_injective.unique

中文:
实例 uniqueOfLeft
  签名: [IsEmpty α]
  定义体: DFunLike.coe_injective.unique

Depends on / 依赖: DFunLike, DFunLike.coe_injective.unique, coe_injective, unique
-/
instance uniqueOfLeft [IsEmpty α] : Unique (α ->₀ R) :=
  DFunLike.coe_injective.unique

end

section
variable {M : Type*} [Zero M] {P : α -> Prop} [DecidablePred P]

/-- Combine finitely supported functions over `{a // P a}` and `{a // ¬P a}`, by case-splitting on
`P a`. -/
@[simps]
/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
  body: if h : P a then f ⟨a, h⟩ else g ⟨a, h⟩
support := (f.support.map (.subtype _)).disjUnion (g.support.map (.subtype _)) by
    simp_rw [Finset.disjoint_left, mem_map, forall_exists_index, Embedding.coe_subtype,
      Subtype.forall, Subtype.exists]
    rintro _ a ha ⟨-, rfl⟩ ⟨b, hb, -, rfl⟩
    exact 

中文:
定义 piecewise
  签名: (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
  定义体: if h : P a then f ⟨a, h⟩ else g ⟨a, h⟩
support := (f.support.map (.subtype _)).disjUnion (g.support.map (.subtype _)) by
    simp_rw [Finset.disjoint_left, mem_map, forall_exists_index, Embedding.coe_subtype,
      Subtype.forall, Subtype.exists]
    rintro _ a ha ⟨-, rfl⟩ ⟨b, hb, -, rfl⟩
    exact 
-/
def piecewise (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M) : α ->₀ M where
  toFun a := if h : P a then f ⟨a, h⟩ else g ⟨a, h⟩
support := (f.support.map (.subtype _)).disjUnion (g.support.map (.subtype _)) by
    simp_rw [Finset.disjoint_left, mem_map, forall_exists_index, Embedding.coe_subtype,
      Subtype.forall, Subtype.exists]
    rintro _ a ha ⟨-, rfl⟩ ⟨b, hb, -, rfl⟩
    exact hb ha
  mem_support_toFun a := by
    by_cases ha : P a <;> simp [ha]

@[simp]
/--
theorem `subtypeDomain_piecewise` / 定理 `subtypeDomain_piecewise`

English:
theorem subtypeDomain_piecewise
  given: (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
  proof: Finsupp.ext fun a => dif_pos a.prop

@[simp]

中文:
定理 subtypeDomain_piecewise
  条件: (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
  证明: Finsupp.ext fun a => dif_pos a.prop

@[simp]

Depends on / 依赖: Finsupp, Finsupp.ext, a.prop, dif_pos
-/
theorem subtypeDomain_piecewise (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M) :
    subtypeDomain P (f.piecewise g) = f :=
  Finsupp.ext fun a => dif_pos a.prop

@[simp]
/--
theorem `subtypeDomain_not_piecewise` / 定理 `subtypeDomain_not_piecewise`

English:
theorem subtypeDomain_not_piecewise
  given: (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
  proof: Finsupp.ext fun a => dif_neg a.prop

#adaptation_note

中文:
定理 subtypeDomain_not_piecewise
  条件: (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
  证明: Finsupp.ext fun a => dif_neg a.prop

#adaptation_note

Depends on / 依赖: Finsupp, Finsupp.ext, a.prop, dif_neg
-/
theorem subtypeDomain_not_piecewise (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M) :
    subtypeDomain (¬P ·) (f.piecewise g) = g :=
  Finsupp.ext fun a => dif_neg a.prop

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend the domain of a `Finsupp` by using `0` where `P x` does not hold. -/
@[simps! (attr := grind =) support apply]
/--
Definition of `extendDomain` / `extendDomain` 的定义

English:
definition extendDomain
  signature: (f : Subtype P ->₀ M)
  body: piecewise f 0

中文:
定义 extendDomain
  签名: (f : Subtype P ->₀ M)
  定义体: piecewise f 0

Depends on / 依赖: piecewise
-/
def extendDomain (f : Subtype P ->₀ M) : α ->₀ M := piecewise f 0

/--
theorem `extendDomain_eq_embDomain_subtype` / 定理 `extendDomain_eq_embDomain_subtype`

English:
theorem extendDomain_eq_embDomain_subtype
  given: (f : Subtype P ->₀ M)
  proof: by
  ext a
  by_cases h : P a
  · refine Eq.trans ?_ (embDomain_apply_self (.subtype P) f (Subtype.mk a h)).symm
    simp [h]
  · rw [embDomain_of_notMem_range] <;> simp [*]

中文:
定理 extendDomain_eq_embDomain_subtype
  条件: (f : Subtype P ->₀ M)
  证明: by
  ext a
  by_cases h : P a
  · refine Eq.trans ?_ (embDomain_apply_self (.subtype P) f (Subtype.mk a h)).symm
    simp [h]
  · rw [embDomain_of_notMem_range] <;> simp [*]

Depends on / 依赖: Eq.trans, Subtype, Subtype.mk, embDomain_apply_self, embDomain_of_notMem_range, subtype
-/
theorem extendDomain_eq_embDomain_subtype (f : Subtype P ->₀ M) :
    extendDomain f = embDomain (.subtype _) f := by
  ext a
  by_cases h : P a
  · refine Eq.trans ?_ (embDomain_apply_self (.subtype P) f (Subtype.mk a h)).symm
    simp [h]
  · rw [embDomain_of_notMem_range] <;> simp [*]

/--
theorem `support_extendDomain_subset` / 定理 `support_extendDomain_subset`

English:
theorem support_extendDomain_subset
  given: (f : Subtype P ->₀ M)
  proof: by
  grind

@[simp]

中文:
定理 support_extendDomain_subset
  条件: (f : Subtype P ->₀ M)
  证明: by
  grind

@[simp]
-/
theorem support_extendDomain_subset (f : Subtype P ->₀ M) :
    ↑(f.extendDomain).support subseteq {x | P x} := by
  grind

@[simp]
/--
theorem `subtypeDomain_extendDomain` / 定理 `subtypeDomain_extendDomain`

English:
theorem subtypeDomain_extendDomain
  given: (f : Subtype P ->₀ M)
  proof: subtypeDomain_piecewise _ _

中文:
定理 subtypeDomain_extendDomain
  条件: (f : Subtype P ->₀ M)
  证明: subtypeDomain_piecewise _ _

Depends on / 依赖: subtypeDomain_piecewise
-/
theorem subtypeDomain_extendDomain (f : Subtype P ->₀ M) :
    subtypeDomain P f.extendDomain = f :=
  subtypeDomain_piecewise _ _

/--
theorem `extendDomain_subtypeDomain` / 定理 `extendDomain_subtypeDomain`

English:
theorem extendDomain_subtypeDomain
  given: (f : α ->₀ M) (hf : forall a in f.support, P a)
  proof: by
  ext
  simp only [extendDomain_apply, subtypeDomain_apply, dite_eq_ite, ite_eq_left_iff]
  grind

@[simp]

中文:
定理 extendDomain_subtypeDomain
  条件: (f : α ->₀ M) (hf : 对任意 a in f.support, P a)
  证明: by
  ext
  simp only [extendDomain_apply, subtypeDomain_apply, dite_eq_ite, ite_eq_left_iff]
  grind

@[simp]

Depends on / 依赖: dite_eq_ite, extendDomain_apply, ite_eq_left_iff, subtypeDomain_apply
-/
theorem extendDomain_subtypeDomain (f : α ->₀ M) (hf : forall a in f.support, P a) :
    (subtypeDomain P f).extendDomain = f := by
  ext
  simp only [extendDomain_apply, subtypeDomain_apply, dite_eq_ite, ite_eq_left_iff]
  grind

@[simp]
/--
theorem `extendDomain_single` / 定理 `extendDomain_single`

English:
theorem extendDomain_single
  given: (a : Subtype P) (m : M)
  proof: by
  ext a'
  obtain rfl | ha := eq_or_ne a' a.val <;>
    simp [*, a.prop, single, Pi.single, Function.update, Subtype.ext_iff]

中文:
定理 extendDomain_single
  条件: (a : Subtype P) (m : M)
  证明: by
  ext a'
  obtain rfl | ha := eq_or_ne a' a.val <;>
    simp [*, a.prop, single, Pi.single, Function.update, Subtype.ext_iff]

Depends on / 依赖: Function, Function.update, Pi.single, Subtype, Subtype.ext_iff, a.prop, a.val, eq_or_ne, ext_iff, single, update
-/
theorem extendDomain_single (a : Subtype P) (m : M) :
    (single a m).extendDomain = single a.val m := by
  ext a'
  obtain rfl | ha := eq_or_ne a' a.val <;>
    simp [*, a.prop, single, Pi.single, Function.update, Subtype.ext_iff]

end

-- TODO: add [DecidablePred (· ∈ s)] as an assumption
/--
Definition of `restrictSupportEquiv` / `restrictSupportEquiv` 的定义

English:
definition restrictSupportEquiv
  signature: (s : Set α) (M : Type*) [AddCommMonoid M]
  body: subtypeDomain (· in s) f.1
  invFun f := letI := Classical.decPred (· in s); ⟨f.extendDomain, support_extendDomain_subset _⟩
  left_inv f :=
letI := Classical.decPred (· in s); Subtype.ext extendDomain_subtypeDomain f.1 f.prop
  right_inv _ := letI := Classical.decPred (· in s); subtypeDomain_extend

中文:
定义 restrictSupportEquiv
  签名: (s : Set α) (M : 类型) [AddCommMonoid M]
  定义体: subtypeDomain (· in s) f.1
  invFun f := letI := Classical.decPred (· in s); ⟨f.extendDomain, support_extendDomain_subset _⟩
  left_inv f :=
letI := Classical.decPred (· in s); Subtype.ext extendDomain_subtypeDomain f.1 f.prop
  right_inv _ := letI := Classical.decPred (· in s); subtypeDomain_extend
-/
@[simps apply] def restrictSupportEquiv (s : Set α) (M : Type*) [AddCommMonoid M] :
    { f : α ->₀ M // ↑f.support subseteq s } ≃ (s ->₀ M) where
  toFun f := subtypeDomain (· in s) f.1
  invFun f := letI := Classical.decPred (· in s); ⟨f.extendDomain, support_extendDomain_subset _⟩
  left_inv f :=
letI := Classical.decPred (· in s); Subtype.ext extendDomain_subtypeDomain f.1 f.prop
  right_inv _ := letI := Classical.decPred (· in s); subtypeDomain_extendDomain _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `restrictSupportEquiv_symm_apply_coe` / 引理 `restrictSupportEquiv_symm_apply_coe`

English:
lemma restrictSupportEquiv_symm_apply_coe
  statement: (s : Set α) (M : Type*) [AddCommMonoid M]
  proof: by
  rw [restrictSupportEquiv]; rw [Equiv.coe_fn_symm_mk]; rw [Subtype.coe_mk]; congr

中文:
引理 restrictSupportEquiv_symm_apply_coe
  结论: (s : Set α) (M : 类型) [AddCommMonoid M]
  证明: by
  rw [restrictSupportEquiv]; rw [Equiv.coe_fn_symm_mk]; rw [Subtype.coe_mk]; congr
-/
@[simp] lemma restrictSupportEquiv_symm_apply_coe (s : Set α) (M : Type*) [AddCommMonoid M]
    [DecidablePred (· in s)] (f : s ->₀ M) :
    (restrictSupportEquiv s M).symm f = f.extendDomain := by
  rw [restrictSupportEquiv]; rw [Equiv.coe_fn_symm_mk]; rw [Subtype.coe_mk]; congr

/--
lemma `restrictSupportEquiv_symm_single` / 引理 `restrictSupportEquiv_symm_single`

English:
lemma restrictSupportEquiv_symm_single
  statement: (s : Set α) (M : Type*) [AddCommMonoid M]
  proof: by
  classical simp

中文:
引理 restrictSupportEquiv_symm_single
  结论: (s : Set α) (M : 类型) [AddCommMonoid M]
  证明: by
  classical simp
-/
@[simp] lemma restrictSupportEquiv_symm_single (s : Set α) (M : Type*) [AddCommMonoid M]
    (a : s) (x : M) :
    (restrictSupportEquiv s M).symm (single a x) = single (a : α) x := by
  classical simp

/-- Given `AddCommMonoid M` and `e : α ≃ β`, `domCongr e` is the corresponding `Equiv` between
`α →₀ M` and `β →₀ M`.

This is `Finsupp.equivCongrLeft` as an `AddEquiv`. -/
@[simps apply]
/--
Definition of `domCongr` / `domCongr` 的定义

English:
definition domCongr
  signature: [AddCommMonoid M] (e : α ≃ β)
  body: equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by
    simp_rw [← equivMapDomain_trans, Equiv.self_trans_symm]
    exact equivMapDomain_refl _
  right_inv := by
    intro v
    simp_rw [← equivMapDomain_trans, Equiv.symm_trans_self]
    exact equivMapDomain_refl _
  map_add' a b :

中文:
定义 domCongr
  签名: [AddCommMonoid M] (e : α ≃ β)
  定义体: equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by
    simp_rw [← equivMapDomain_trans, Equiv.self_trans_symm]
    exact equivMapDomain_refl _
  right_inv := by
    intro v
    simp_rw [← equivMapDomain_trans, Equiv.symm_trans_self]
    exact equivMapDomain_refl _
  map_add' a b :
-/
protected def domCongr [AddCommMonoid M] (e : α ≃ β) : (α ->₀ M) ≃+ (β ->₀ M) where
  toFun := equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by
    simp_rw [← equivMapDomain_trans, Equiv.self_trans_symm]
    exact equivMapDomain_refl _
  right_inv := by
    intro v
    simp_rw [← equivMapDomain_trans, Equiv.symm_trans_self]
    exact equivMapDomain_refl _
  map_add' a b := by simp only [equivMapDomain_eq_mapDomain, mapDomain_add]

@[simp]
/--
theorem `domCongr_refl` / 定理 `domCongr_refl`

English:
theorem domCongr_refl
  given: [AddCommMonoid M]
  proof: AddEquiv.ext fun _ => equivMapDomain_refl _

@[simp]

中文:
定理 domCongr_refl
  条件: [AddCommMonoid M]
  证明: AddEquiv.ext fun _ => equivMapDomain_refl _

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.ext, equivMapDomain_refl
-/
theorem domCongr_refl [AddCommMonoid M] :
    Finsupp.domCongr (Equiv.refl α) = AddEquiv.refl (α ->₀ M) :=
  AddEquiv.ext fun _ => equivMapDomain_refl _

@[simp]
/--
theorem `domCongr_symm` / 定理 `domCongr_symm`

English:
theorem domCongr_symm
  given: [AddCommMonoid M] (e : α ≃ β)
  proof: AddEquiv.ext fun _ => rfl

@[simp]

中文:
定理 domCongr_symm
  条件: [AddCommMonoid M] (e : α ≃ β)
  证明: AddEquiv.ext fun _ => rfl

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.ext
-/
theorem domCongr_symm [AddCommMonoid M] (e : α ≃ β) :
    (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β ->₀ M) ≃+ (α ->₀ M)) :=
  AddEquiv.ext fun _ => rfl

@[simp]
/--
theorem `domCongr_trans` / 定理 `domCongr_trans`

English:
theorem domCongr_trans
  given: [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ)
  proof: AddEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

中文:
定理 domCongr_trans
  条件: [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ)
  证明: AddEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

Depends on / 依赖: AddEquiv, AddEquiv.ext, equivMapDomain_trans
-/
theorem domCongr_trans [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ) :
    (Finsupp.domCongr e).trans (Finsupp.domCongr f) =
      (Finsupp.domCongr (e.trans f) : (α ->₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι -> Type*} [Zero M] (l : (Σ i, αs i) ->₀ M)

/--
Definition of `split` / `split` 的定义

English:
definition split
  signature: (i : ι)
  body: l.comapDomain (Sigma.mk i) fun _ _ _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

中文:
定义 split
  签名: (i : ι)
  定义体: l.comapDomain (Sigma.mk i) fun _ _ _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

Depends on / 依赖: Sigma.mk, Sigma.mk.inj, comapDomain, heq_iff_eq, l.comapDomain
-/
def split (i : ι) : αs i ->₀ M :=
  l.comapDomain (Sigma.mk i) fun _ _ _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

set_option backward.isDefEq.respectTransparency false in
/--
theorem `split_apply` / 定理 `split_apply`

English:
theorem split_apply
  given: (i : ι) (x : αs i)
  statement: split l i x = l ⟨i, x⟩
  proof: by
  rw [split]; rw [comapDomain_apply]

中文:
定理 split_apply
  条件: (i : ι) (x : αs i)
  结论: split l i x = l ⟨i, x⟩
  证明: by
  rw [split]; rw [comapDomain_apply]

Depends on / 依赖: comapDomain_apply
-/
theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ := by
  rw [split]; rw [comapDomain_apply]

/--
Definition of `splitSupport` / `splitSupport` 的定义

English:
definition splitSupport
  signature: (l : (Σ i, αs i) ->₀ M)
  body: haveI := Classical.decEq ι
  l.support.image Sigma.fst

中文:
定义 splitSupport
  签名: (l : (Σ i, αs i) ->₀ M)
  定义体: haveI := Classical.decEq ι
  l.support.image Sigma.fst

Depends on / 依赖: Classical, Classical.decEq, Sigma.fst, l.support.image, support
-/
def splitSupport (l : (Σ i, αs i) ->₀ M) : Finset ι :=
  haveI := Classical.decEq ι
  l.support.image Sigma.fst

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_splitSupport_iff_nonzero` / 定理 `mem_splitSupport_iff_nonzero`

English:
theorem mem_splitSupport_iff_nonzero
  given: (i : ι)
  statement: i in splitSupport l ↔ split l i != 0
  proof: by
  classical rw [splitSupport, mem_image, Ne, ← support_eq_empty, ← Ne,
    ← Finset.nonempty_iff_ne_empty, split, comapDomain, Finset.Nonempty]
  simp only [Finset.mem_preimage, exists_and_right, exists_eq_right, mem_support_iff,
    Sigma.exists, Ne]

中文:
定理 mem_splitSupport_iff_nonzero
  条件: (i : ι)
  结论: i in splitSupport l ↔ split l i != 0
  证明: by
  classical rw [splitSupport, mem_image, Ne, ← support_eq_empty, ← Ne,
    ← Finset.nonempty_iff_ne_empty, split, comapDomain, Finset.Nonempty]
  simp only [Finset.mem_preimage, exists_and_right, exists_eq_right, mem_support_iff,
    Sigma.exists, Ne]

Depends on / 依赖: Finset, Finset.Nonempty, Finset.mem_preimage, Finset.nonempty_iff_ne_empty, Nonempty, Sigma.exists, classical, comapDomain, exists_and_right, exists_eq_right, mem_image, mem_preimage, mem_support_iff, nonempty_iff_ne_empty, splitSupport, support_eq_empty
-/
theorem mem_splitSupport_iff_nonzero (i : ι) : i in splitSupport l ↔ split l i != 0 := by
  classical rw [splitSupport, mem_image, Ne, ← support_eq_empty, ← Ne,
    ← Finset.nonempty_iff_ne_empty, split, comapDomain, Finset.Nonempty]
  simp only [Finset.mem_preimage, exists_and_right, exists_eq_right, mem_support_iff,
    Sigma.exists, Ne]

/--
Definition of `splitComp` / `splitComp` 的定义

English:
definition splitComp
  signature: [Zero N] (g : forall i, (αs i ->₀ M) -> N) (hg : forall i x, x = 0 ↔ g i x = 0)
  body: splitSupport l
  toFun i := g i (split l i)
  mem_support_toFun := by
    intro i
    rw [mem_splitSupport_iff_nonzero]; rw [not_iff_not]; rw [hg]

中文:
定义 splitComp
  签名: [Zero N] (g : 对任意 i, (αs i ->₀ M) -> N) (hg : 对任意 i x, x = 0 ↔ g i x = 0)
  定义体: splitSupport l
  toFun i := g i (split l i)
  mem_support_toFun := by
    intro i
    rw [mem_splitSupport_iff_nonzero]; rw [not_iff_not]; rw [hg]

Depends on / 依赖: splitSupport
-/
def splitComp [Zero N] (g : forall i, (αs i ->₀ M) -> N) (hg : forall i x, x = 0 ↔ g i x = 0) : ι ->₀ N where
  support := splitSupport l
  toFun i := g i (split l i)
  mem_support_toFun := by
    intro i
    rw [mem_splitSupport_iff_nonzero]; rw [not_iff_not]; rw [hg]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sigma_support` / 定理 `sigma_support`

English:
theorem sigma_support
  statement: l.support = l.splitSupport.sigma fun i => (l.split i).support
  proof: by
  simp_rw [Finset.ext_iff, splitSupport, split, comapDomain, Sigma.forall, mem_sigma, mem_image,
    mem_preimage]
  tauto

中文:
定理 sigma_support
  结论: l.support = l.splitSupport.sigma fun i => (l.split i).support
  证明: by
  simp_rw [Finset.ext_iff, splitSupport, split, comapDomain, Sigma.forall, mem_sigma, mem_image,
    mem_preimage]
  tauto

Depends on / 依赖: Finset, Finset.ext_iff, Sigma.forall, comapDomain, ext_iff, mem_image, mem_preimage, mem_sigma, simp_rw, splitSupport
-/
theorem sigma_support : l.support = l.splitSupport.sigma fun i => (l.split i).support := by
  simp_rw [Finset.ext_iff, splitSupport, split, comapDomain, Sigma.forall, mem_sigma, mem_image,
    mem_preimage]
  tauto

/--
theorem `sigma_sum` / 定理 `sigma_sum`

English:
theorem sigma_sum
  given: [AddCommMonoid N] (f : (Σ i : ι, αs i) -> M -> N)
  proof: by
  simp only [sum, sigma_support, sum_sigma, split_apply]

中文:
定理 sigma_sum
  条件: [AddCommMonoid N] (f : (Σ i : ι, αs i) -> M -> N)
  证明: by
  simp only [sum, sigma_support, sum_sigma, split_apply]

Depends on / 依赖: sigma_support, split_apply, sum_sigma
-/
theorem sigma_sum [AddCommMonoid N] (f : (Σ i : ι, αs i) -> M -> N) :
    l.sum f = ∑ i in splitSupport l, (split l i).sum fun (a : αs i) b => f ⟨i, a⟩ b := by
  simp only [sum, sigma_support, sum_sigma, split_apply]

variable {η : Type*} [Fintype η] {ιs : η -> Type*} [Zero α]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sigmaFinsuppEquivPiFinsupp` / `sigmaFinsuppEquivPiFinsupp` 的定义

English:
definition sigmaFinsuppEquivPiFinsupp
  signature: : ((Σ j, ιs j) ->₀ α) ≃ forall j, ιs j ->₀ α where
  body: split
  invFun f :=
    onFinset (Finset.univ.sigma fun j => (f j).support) (fun ji => f ji.1 ji.2) fun _ hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv f := by
    ext
    simp [split]
  right_inv f := by
    ext
    simp [split]

@[simp]

中文:
定义 sigmaFinsuppEquivPiFinsupp
  签名: : ((Σ j, ιs j) ->₀ α) ≃ 对任意 j, ιs j ->₀ α where
  定义体: split
  invFun f :=
    onFinset (Finset.univ.sigma fun j => (f j).support) (fun ji => f ji.1 ji.2) fun _ hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv f := by
    ext
    simp [split]
  right_inv f := by
    ext
    simp [split]

@[simp]
-/
noncomputable def sigmaFinsuppEquivPiFinsupp : ((Σ j, ιs j) ->₀ α) ≃ forall j, ιs j ->₀ α where
  toFun := split
  invFun f :=
    onFinset (Finset.univ.sigma fun j => (f j).support) (fun ji => f ji.1 ji.2) fun _ hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv f := by
    ext
    simp [split]
  right_inv f := by
    ext
    simp [split]

@[simp]
/--
theorem `sigmaFinsuppEquivPiFinsupp_apply` / 定理 `sigmaFinsuppEquivPiFinsupp_apply`

English:
theorem sigmaFinsuppEquivPiFinsupp_apply
  given: (f : (Σ j, ιs j) ->₀ α) (j i)
  proof: rfl

中文:
定理 sigmaFinsuppEquivPiFinsupp_apply
  条件: (f : (Σ j, ιs j) ->₀ α) (j i)
  证明: rfl
-/
theorem sigmaFinsuppEquivPiFinsupp_apply (f : (Σ j, ιs j) ->₀ α) (j i) :
    sigmaFinsuppEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

/--
Definition of `sigmaFinsuppAddEquivPiFinsupp` / `sigmaFinsuppAddEquivPiFinsupp` 的定义

English:
definition sigmaFinsuppAddEquivPiFinsupp
  signature: {α : Type*} {ιs : η -> Type*} [AddMonoid α]
  body: { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]

中文:
定义 sigmaFinsuppAddEquivPiFinsupp
  签名: {α : 类型} {ιs : η -> 类型} [AddMonoid α]
  定义体: { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]

Depends on / 依赖: map_add, sigmaFinsuppEquivPiFinsupp
-/
noncomputable def sigmaFinsuppAddEquivPiFinsupp {α : Type*} {ιs : η -> Type*} [AddMonoid α] :
    ((Σ j, ιs j) ->₀ α) ≃+ forall j, ιs j ->₀ α :=
  { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]
/--
theorem `sigmaFinsuppAddEquivPiFinsupp_apply` / 定理 `sigmaFinsuppAddEquivPiFinsupp_apply`

English:
theorem sigmaFinsuppAddEquivPiFinsupp_apply
  statement: {α : Type*} {ιs : η -> Type*} [AddMonoid α]
  proof: rfl

中文:
定理 sigmaFinsuppAddEquivPiFinsupp_apply
  结论: {α : 类型} {ιs : η -> 类型} [AddMonoid α]
  证明: rfl
-/
theorem sigmaFinsuppAddEquivPiFinsupp_apply {α : Type*} {ιs : η -> Type*} [AddMonoid α]
    (f : (Σ j, ιs j) ->₀ α) (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

end Sigma

/--
lemma `mem_range_embDomain_iff` / 引理 `mem_range_embDomain_iff`

English:
lemma mem_range_embDomain_iff
  given: [AddCommMonoid M] (f : α ↪ β) (x : β ->₀ M)
  proof: by
  convert! mem_range_mapDomain_iff _ f.injective _
  · ext; rw [embDomain_eq_mapDomain]
  · grind

中文:
引理 mem_range_embDomain_iff
  条件: [AddCommMonoid M] (f : α ↪ β) (x : β ->₀ M)
  证明: by
  convert! mem_range_mapDomain_iff _ f.injective _
  · ext; rw [embDomain_eq_mapDomain]
  · grind

Depends on / 依赖: convert, embDomain_eq_mapDomain, f.injective, injective, mem_range_mapDomain_iff
-/
lemma mem_range_embDomain_iff [AddCommMonoid M] (f : α ↪ β) (x : β ->₀ M) :
    x in Set.range (embDomain f) ↔ ↑x.support subseteq Set.range f := by
  convert! mem_range_mapDomain_iff _ f.injective _
  · ext; rw [embDomain_eq_mapDomain]
  · grind

/--
theorem `embDomain_trans_apply` / 定理 `embDomain_trans_apply`

English:
theorem embDomain_trans_apply
  given: [AddCommMonoid M] (v : α ->₀ M) (f : α ↪ β) (g : β ↪ γ)
  proof: by
  simp only [embDomain_eq_mapDomain, ← mapDomain_comp, Embedding.coe_trans]

中文:
定理 embDomain_trans_apply
  条件: [AddCommMonoid M] (v : α ->₀ M) (f : α ↪ β) (g : β ↪ γ)
  证明: by
  simp only [embDomain_eq_mapDomain, ← mapDomain_comp, Embedding.coe_trans]

Depends on / 依赖: Embedding, Embedding.coe_trans, coe_trans, embDomain_eq_mapDomain, mapDomain_comp
-/
theorem embDomain_trans_apply [AddCommMonoid M] (v : α ->₀ M) (f : α ↪ β) (g : β ↪ γ) :
    embDomain (f.trans g) v = embDomain g (embDomain f v) := by
  simp only [embDomain_eq_mapDomain, ← mapDomain_comp, Embedding.coe_trans]

/--
theorem `mapDomain_support_of_subsingletonAddUnits` / 定理 `mapDomain_support_of_subsingletonAddUnits`

English:
theorem mapDomain_support_of_subsingletonAddUnits
  statement: [DecidableEq β] [AddCommMonoid M]
  proof: by
  ext t
  rw [mem_support_iff]; rw [ne_eq]; rw [Finset.mem_image]
  refine ⟨?_, fun ⟨i, i_in, hi⟩ => ?_⟩
  · simpa [mapDomain, sum, single_apply] using fun i h h' _ => ⟨i, h, h'⟩
  simpa [mapDomain, sum, ← hi, single_apply] using ⟨i, by simp [mem_support_iff.mp i_in]⟩

中文:
定理 mapDomain_support_of_subsingletonAddUnits
  结论: [DecidableEq β] [AddCommMonoid M]
  证明: by
  ext t
  rw [mem_support_iff]; rw [ne_eq]; rw [Finset.mem_image]
  refine ⟨?_, fun ⟨i, i_in, hi⟩ => ?_⟩
  · simpa [mapDomain, sum, single_apply] using fun i h h' _ => ⟨i, h, h'⟩
  simpa [mapDomain, sum, ← hi, single_apply] using ⟨i, by simp [mem_support_iff.mp i_in]⟩

Depends on / 依赖: Finset, Finset.mem_image, i_in, mapDomain, mem_image, mem_support_iff, mem_support_iff.mp, ne_eq, single_apply
-/
theorem mapDomain_support_of_subsingletonAddUnits [DecidableEq β] [AddCommMonoid M]
    (f : α -> β) [Subsingleton (AddUnits M)] (x : α ->₀ M) :
      (x.mapDomain f).support = x.support.image f := by
  ext t
  rw [mem_support_iff]; rw [ne_eq]; rw [Finset.mem_image]
  refine ⟨?_, fun ⟨i, i_in, hi⟩ => ?_⟩
  · simpa [mapDomain, sum, single_apply] using fun i h h' _ => ⟨i, h, h'⟩
  simpa [mapDomain, sum, ← hi, single_apply] using ⟨i, by simp [mem_support_iff.mp i_in]⟩

/--
theorem `mapDomain_apply_eq_sum` / 定理 `mapDomain_apply_eq_sum`

English:
theorem mapDomain_apply_eq_sum
  statement: [DecidableEq β] [AddCommMonoid M] (f : α -> β)
  proof: by
  simp [mapDomain, sum, single_apply, Finset.sum_ite]

中文:
定理 mapDomain_apply_eq_sum
  结论: [DecidableEq β] [AddCommMonoid M] (f : α -> β)
  证明: by
  simp [mapDomain, sum, single_apply, Finset.sum_ite]

Depends on / 依赖: Finset, Finset.sum_ite, mapDomain, single_apply, sum_ite
-/
theorem mapDomain_apply_eq_sum [DecidableEq β] [AddCommMonoid M] (f : α -> β)
    (x : α ->₀ M) {a : α} : (x.mapDomain f) (f a) = ∑ i in x.support with f i = f a, x i := by
  simp [mapDomain, sum, single_apply, Finset.sum_ite]

/--
theorem `mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits` / 定理 `mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits`

English:
theorem mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits
  statement: [AddCommMonoid M] (f : α -> β)
  proof: by
  classical
  refine ⟨fun h => Finsupp.ext (fun i => ?_), fun h => by rw [h, mapDomain_zero]⟩
  replace h := Finsupp.ext_iff.mp h (f i)
  simp [mapDomain_apply_eq_sum] at h; grind

中文:
定理 mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits
  结论: [AddCommMonoid M] (f : α -> β)
  证明: by
  classical
  refine ⟨fun h => Finsupp.ext (fun i => ?_), fun h => by rw [h, mapDomain_zero]⟩
  replace h := Finsupp.ext_iff.mp h (f i)
  simp [mapDomain_apply_eq_sum] at h; grind

Depends on / 依赖: Finsupp, Finsupp.ext, Finsupp.ext_iff.mp, classical, ext_iff, mapDomain_apply_eq_sum, mapDomain_zero, replace
-/
theorem mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits [AddCommMonoid M] (f : α -> β)
    [Subsingleton (AddUnits M)] (x : α ->₀ M) : mapDomain (M := M) f x = 0 ↔ x = 0 := by
  classical
  refine ⟨fun h => Finsupp.ext (fun i => ?_), fun h => by rw [h, mapDomain_zero]⟩
  replace h := Finsupp.ext_iff.mp h (f i)
  simp [mapDomain_apply_eq_sum] at h; grind

end Finsupp
