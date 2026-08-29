/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.CompleteLattice.Chain
public import Mathlib.Order.Minimal

/-!
# Zorn's lemmas

This file proves several formulations of Zorn's Lemma.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_le`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices ∃ m, ∀ a, m ≺ a → a ≺ m by ...`
  (or whatever you actually need) followed by an `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement := by
  let s : Set α := {x | whatever x}
  suffices ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x by -- or with another operator xxx
    proof_post_zorn
  apply zorn_subset -- or another variant
  rintro c hcs hc
  obtain rfl | hcnemp := c.eq_empty_or_nonempty -- you might need to disjunct on c empty or not
  · exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩
  · exact ⟨construction,
      proof_that_construction_respects_whatever,
      proof_that_construction_contains_all_stuff_in_c⟩
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

public section

open Set

variable {α β : Type*} {r : α -> α -> Prop} {c : Set α}

/-- Local notation for the relation being considered. -/
local infixl:50 " ≺ " => r

/--
theorem `exists_maximal_of_chains_bounded` / 定理 `exists_maximal_of_chains_bounded`

English:
theorem exists_maximal_of_chains_bounded
  statement: (h : forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub)
  proof: have : exists ub, forall a in maxChain r, a ≺ ub := h _ maxChain_spec.left
  let ⟨ub, (hub : forall a in maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
maxChain_spec.1.insert fun b hb _ => Or.inr trans (hub b hb) ha
hub a by
      rw [maxChain_spec.r

中文:
定理 存在_maximal_of_chains_bounded
  结论: (h : 对任意 c, IsChain r c -> 存在 ub, 对任意 a in c, a ≺ ub)
  证明: have : exists ub, forall a in maxChain r, a ≺ ub := h _ maxChain_spec.left
  let ⟨ub, (hub : forall a in maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
maxChain_spec.1.insert fun b hb _ => Or.inr trans (hub b hb) ha
hub a by
      rw [maxChain_spec.r

Depends on / 依赖: IsChain, Or.inr, insert, maxChain, maxChain_spec, maxChain_spec.left, maxChain_spec.right, mem_insert, subset_insert
-/
theorem exists_maximal_of_chains_bounded (h : forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub)
    (trans : forall {a b c}, a ≺ b -> b ≺ c -> a ≺ c) : exists m, forall a, m ≺ a -> a ≺ m :=
have : exists ub, forall a in maxChain r, a ≺ ub := h _ maxChain_spec.left
  let ⟨ub, (hub : forall a in maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
maxChain_spec.1.insert fun b hb _ => Or.inr trans (hub b hb) ha
hub a by
      rw [maxChain_spec.right this (subset_insert _ _)]
      exact mem_insert _ _⟩

/--
theorem `exists_maximal_of_nonempty_chains_bounded` / 定理 `exists_maximal_of_nonempty_chains_bounded`

English:
theorem exists_maximal_of_nonempty_chains_bounded
  statement: [Nonempty α]
  proof: exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x in (∅ : Set α)).elim⟩) (h c hc))
    trans

中文:
定理 存在_maximal_of_nonempty_chains_bounded
  结论: [非空 α]
  证明: exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x in (∅ : Set α)).elim⟩) (h c hc))
    trans

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, eq_empty_or_nonempty, exists_maximal_of_chains_bounded
-/
theorem exists_maximal_of_nonempty_chains_bounded [Nonempty α]
    (h : forall c, IsChain r c -> c.Nonempty -> exists ub, forall a in c, a ≺ ub)
    (trans : forall {a b c}, a ≺ b -> b ≺ c -> a ≺ c) : exists m, forall a, m ≺ a -> a ≺ m :=
  exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x in (∅ : Set α)).elim⟩) (h c hc))
    trans

section Preorder

variable [Preorder α]

/--
theorem `zorn_le` / 定理 `zorn_le`

English:
theorem zorn_le
  given: (h : forall c : Set α, IsChain (· <= ·) c -> BddAbove c)
  statement: exists m : α, IsMax m
  proof: exists_maximal_of_chains_bounded h le_trans

中文:
定理 zorn_le
  条件: (h : 对任意 c : 集合 α, IsChain (· <= ·) c -> BddAbove c)
  结论: 存在 m : α, IsMax m
  证明: exists_maximal_of_chains_bounded h le_trans

Depends on / 依赖: exists_maximal_of_chains_bounded, le_trans
-/
theorem zorn_le (h : forall c : Set α, IsChain (· <= ·) c -> BddAbove c) : exists m : α, IsMax m :=
  exists_maximal_of_chains_bounded h le_trans

/--
theorem `zorn_le_nonempty` / 定理 `zorn_le_nonempty`

English:
theorem zorn_le_nonempty
  statement: [Nonempty α]
  proof: exists_maximal_of_nonempty_chains_bounded h le_trans

中文:
定理 zorn_le_nonempty
  结论: [非空 α]
  证明: exists_maximal_of_nonempty_chains_bounded h le_trans

Depends on / 依赖: exists_maximal_of_nonempty_chains_bounded, le_trans
-/
theorem zorn_le_nonempty [Nonempty α]
    (h : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> BddAbove c) : exists m : α, IsMax m :=
  exists_maximal_of_nonempty_chains_bounded h le_trans

/--
theorem `zorn_le₀` / 定理 `zorn_le₀`

English:
theorem zorn_le₀
  given: (s : Set α) (ih : forall c subseteq s, IsChain (· <= ·) c -> exists ub in s, forall z in c, z <= ub)
  proof: let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_le s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨_, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq
            exact hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun 

中文:
定理 zorn_le₀
  条件: (s : 集合 α) (ih : 对任意 c subseteq s, IsChain (· <= ·) c -> 存在 ub in s, 对任意 z in c, z <= ub)
  证明: let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_le s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨_, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq
            exact hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun 

Depends on / 依赖: Subtype, Subtype.ext_iff, Subtype.val, ext_iff, zorn_le
-/
theorem zorn_le₀ (s : Set α) (ih : forall c subseteq s, IsChain (· <= ·) c -> exists ub in s, forall z in c, z <= ub) :
    exists m, Maximal (· in s) m :=
  let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_le s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨_, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq
            exact hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun ⟨_, _⟩ hc => hub _ ⟨_, hc, rfl⟩⟩
  ⟨m, hms, fun z hzs hmz => @h ⟨z, hzs⟩ hmz⟩

/--
theorem `zorn_le_nonempty₀` / 定理 `zorn_le_nonempty₀`

English:
theorem zorn_le_nonempty₀
  statement: (s : Set α)
  proof: by
  have H := zorn_le₀ ({ y in s | x <= y }) fun c hcs hc => ?_
  · rcases H with ⟨m, ⟨hms, hxm⟩, hm⟩
    exact ⟨m, hxm, hms, fun z hzs hmz => @hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c

中文:
定理 zorn_le_nonempty₀
  结论: (s : 集合 α)
  证明: by
  have H := zorn_le₀ ({ y in s | x <= y }) fun c hcs hc => ?_
  · rcases H with ⟨m, ⟨hms, hxm⟩, hm⟩
    exact ⟨m, hxm, hms, fun z hzs hmz => @hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c

Depends on / 依赖: False.elim, c.eq_empty_or_nonempty, eq_empty_or_nonempty, hxm.trans, le_rfl
-/
theorem zorn_le_nonempty₀ (s : Set α)
    (ih : forall c subseteq s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub) (x : α) (hxs : x in s) :
    exists m, x <= m ∧ Maximal (· in s) m := by
  have H := zorn_le₀ ({ y in s | x <= y }) fun c hcs hc => ?_
  · rcases H with ⟨m, ⟨hms, hxm⟩, hm⟩
    exact ⟨m, hxm, hms, fun z hzs hmz => @hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c (fun z hz => (hcs hz).1) hc y hy with ⟨z, hzs, hz⟩
exact ⟨z, ⟨hzs, (hcs hy).2.trans hz _ hy⟩, hz⟩

/--
theorem `zorn_le_nonempty_Ici₀` / 定理 `zorn_le_nonempty_Ici₀`

English:
theorem zorn_le_nonempty_Ici₀
  statement: (a : α)
  proof: by
  let ⟨m, hxm, ham, hm⟩ := zorn_le_nonempty₀ (Ici a) (fun c hca hc y hy => ?_) x hax
  · exact ⟨m, hxm, fun z hmz => hm (ham.trans hmz) hmz⟩
  · have ⟨ub, hub⟩ := ih c hca hc y hy
    exact ⟨ub, (hca hy).trans (hub y hy), hub⟩

中文:
定理 zorn_le_nonempty_Ici₀
  结论: (a : α)
  证明: by
  let ⟨m, hxm, ham, hm⟩ := zorn_le_nonempty₀ (Ici a) (fun c hca hc y hy => ?_) x hax
  · exact ⟨m, hxm, fun z hmz => hm (ham.trans hmz) hmz⟩
  · have ⟨ub, hub⟩ := ih c hca hc y hy
    exact ⟨ub, (hca hy).trans (hub y hy), hub⟩

Depends on / 依赖: ham.trans
-/
theorem zorn_le_nonempty_Ici₀ (a : α)
    (ih : forall c subseteq Ici a, IsChain (· <= ·) c -> forall y in c, exists ub, forall z in c, z <= ub) (x : α) (hax : a <= x) :
    exists m, x <= m ∧ IsMax m := by
  let ⟨m, hxm, ham, hm⟩ := zorn_le_nonempty₀ (Ici a) (fun c hca hc y hy => ?_) x hax
  · exact ⟨m, hxm, fun z hmz => hm (ham.trans hmz) hmz⟩
  · have ⟨ub, hub⟩ := ih c hca hc y hy
    exact ⟨ub, (hca hy).trans (hub y hy), hub⟩

end Preorder

/--
theorem `zorn_subset` / 定理 `zorn_subset`

English:
theorem zorn_subset
  statement: (S : Set (Set α))
  proof: zorn_le₀ S h

中文:
定理 zorn_subset
  结论: (S : 集合 (集合 α))
  证明: zorn_le₀ S h
-/
theorem zorn_subset (S : Set (Set α))
    (h : forall c subseteq S, IsChain (· subseteq ·) c -> exists ub in S, forall s in c, s subseteq ub) : exists m, Maximal (· in S) m :=
  zorn_le₀ S h

/--
theorem `zorn_subset_nonempty` / 定理 `zorn_subset_nonempty`

English:
theorem zorn_subset_nonempty
  statement: (S : Set (Set α))
  proof: zorn_le_nonempty₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx

中文:
定理 zorn_subset_nonempty
  结论: (S : 集合 (集合 α))
  证明: zorn_le_nonempty₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx
-/
theorem zorn_subset_nonempty (S : Set (Set α))
    (H : forall c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall s in c, s subseteq ub) (x) (hx : x in S) :
    exists m, x subseteq m ∧ Maximal (· in S) m :=
  zorn_le_nonempty₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx

/--
theorem `zorn_superset` / 定理 `zorn_superset`

English:
theorem zorn_superset
  statement: (S : Set (Set α))
  proof: (@zorn_le₀ (Set α)ᵒᵈ _ S) fun c cS hc => h c cS hc.symm

中文:
定理 zorn_superset
  结论: (S : 集合 (集合 α))
  证明: (@zorn_le₀ (Set α)ᵒᵈ _ S) fun c cS hc => h c cS hc.symm

Depends on / 依赖: hc.symm
-/
theorem zorn_superset (S : Set (Set α))
    (h : forall c subseteq S, IsChain (· subseteq ·) c -> exists lb in S, forall s in c, lb subseteq s) : exists m, Minimal (· in S) m :=
  (@zorn_le₀ (Set α)ᵒᵈ _ S) fun c cS hc => h c cS hc.symm

/--
theorem `zorn_superset_nonempty` / 定理 `zorn_superset_nonempty`

English:
theorem zorn_superset_nonempty
  statement: (S : Set (Set α))
  proof: @zorn_le_nonempty₀ (Set α)ᵒᵈ _ S (fun _ cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx

中文:
定理 zorn_superset_nonempty
  结论: (S : 集合 (集合 α))
  证明: @zorn_le_nonempty₀ (Set α)ᵒᵈ _ S (fun _ cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx

Depends on / 依赖: hc.symm
-/
theorem zorn_superset_nonempty (S : Set (Set α))
    (H : forall c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists lb in S, forall s in c, lb subseteq s) (x) (hx : x in S) :
    exists m, m subseteq x ∧ Minimal (· in S) m :=
  @zorn_le_nonempty₀ (Set α)ᵒᵈ _ S (fun _ cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx

/--
theorem `IsChain.exists_maxChain` / 定理 `IsChain.exists_maxChain`

English:
theorem IsChain.exists_maxChain
  given: (hc : IsChain r c)
  statement: exists M, @IsMaxChain _ r M ∧ c subseteq M
  proof: by
  have H := zorn_subset_nonempty { s | c subseteq s ∧ IsChain r s } ?_ c ⟨Subset.rfl, hc⟩
  · obtain ⟨M, hcM, hM⟩ := H
    exact ⟨M, ⟨hM.prop.2, fun d hd hMd => hM.eq_of_subset ⟨hcM.trans hMd, hd⟩ hMd⟩, hcM⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine
    ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hc

中文:
定理 IsChain.存在_maxChain
  条件: (hc : IsChain r c)
  结论: 存在 M, @IsMaxChain _ r M ∧ c subseteq M
  证明: by
  have H := zorn_subset_nonempty { s | c subseteq s ∧ IsChain r s } ?_ c ⟨Subset.rfl, hc⟩
  · obtain ⟨M, hcM, hM⟩ := H
    exact ⟨M, ⟨hM.prop.2, fun d hd hMd => hM.eq_of_subset ⟨hcM.trans hMd, hd⟩ hMd⟩, hcM⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine
    ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hc

Depends on / 依赖: IsChain, Set.mem_sUnion_of_mem, Set.subset_sUnion_of_mem, Subset, Subset.rfl, eq_of_subset, eq_or_ne, hM.eq_of_subset, hM.prop, hcM.trans, mem_sUnion_of_mem, subset_sUnion_of_mem, subseteq, zorn_subset_nonempty
-/
theorem IsChain.exists_maxChain (hc : IsChain r c) : exists M, @IsMaxChain _ r M ∧ c subseteq M := by
  have H := zorn_subset_nonempty { s | c subseteq s ∧ IsChain r s } ?_ c ⟨Subset.rfl, hc⟩
  · obtain ⟨M, hcM, hM⟩ := H
    exact ⟨M, ⟨hM.prop.2, fun d hd hMd => hM.eq_of_subset ⟨hcM.trans hMd, hd⟩ hMd⟩, hcM⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine
    ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, ?_⟩, fun _ =>
      Set.subset_sUnion_of_mem⟩
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz
  obtain rfl | hsseq := eq_or_ne sy sz
  · exact (hcs₀ hsy).right hysy hzsz hyz
  rcases hcs₁ hsy hsz hsseq with h | h
  · exact (hcs₀ hsz).right (h hysy) hzsz hyz
  · exact (hcs₀ hsy).right hysy (h hzsz) hyz

/-! ### Flags -/

namespace Flag

variable [Preorder α] {c : Set α} {s : Flag α} {a b : α}

/--
lemma `_root_.IsChain.exists_subset_flag` / 引理 `_root_.IsChain.exists_subset_flag`

English:
lemma _root_.IsChain.exists_subset_flag
  given: (hc : IsChain (· <= ·) c)
  statement: exists s : Flag α, c subseteq s
  proof: let ⟨s, hs, hcs⟩ := hc.exists_maxChain; ⟨ofIsMaxChain s hs, hcs⟩

中文:
引理 _root_.IsChain.存在_subset_flag
  条件: (hc : IsChain (· <= ·) c)
  结论: 存在 s : 旗 α, c subseteq s
  证明: let ⟨s, hs, hcs⟩ := hc.exists_maxChain; ⟨ofIsMaxChain s hs, hcs⟩

Depends on / 依赖: exists_maxChain, hc.exists_maxChain, ofIsMaxChain
-/
lemma _root_.IsChain.exists_subset_flag (hc : IsChain (· <= ·) c) : exists s : Flag α, c subseteq s :=
  let ⟨s, hs, hcs⟩ := hc.exists_maxChain; ⟨ofIsMaxChain s hs, hcs⟩

/--
lemma `exists_mem` / 引理 `exists_mem`

English:
lemma exists_mem
  given: (a : α)
  statement: exists s : Flag α, a in s
  proof: let ⟨s, hs⟩ := Set.subsingleton_singleton (a := a).isChain.exists_subset_flag
  ⟨s, hs rfl⟩

中文:
引理 存在_mem
  条件: (a : α)
  结论: 存在 s : 旗 α, a in s
  证明: let ⟨s, hs⟩ := Set.subsingleton_singleton (a := a).isChain.exists_subset_flag
  ⟨s, hs rfl⟩

Depends on / 依赖: Set.subsingleton_singleton, exists_subset_flag, isChain, isChain.exists_subset_flag, subsingleton_singleton
-/
lemma exists_mem (a : α) : exists s : Flag α, a in s :=
  let ⟨s, hs⟩ := Set.subsingleton_singleton (a := a).isChain.exists_subset_flag
  ⟨s, hs rfl⟩

/--
lemma `exists_mem_mem` / 引理 `exists_mem_mem`

English:
lemma exists_mem_mem
  given: (hab : a <= b)
  statement: exists s : Flag α, a in s ∧ b in s
  proof: by
  simpa [Set.insert_subset_iff] using (IsChain.pair hab).exists_subset_flag

中文:
引理 存在_mem_mem
  条件: (hab : a <= b)
  结论: 存在 s : 旗 α, a in s ∧ b in s
  证明: by
  simpa [Set.insert_subset_iff] using (IsChain.pair hab).exists_subset_flag

Depends on / 依赖: IsChain, IsChain.pair, Set.insert_subset_iff, exists_subset_flag, insert_subset_iff
-/
lemma exists_mem_mem (hab : a <= b) : exists s : Flag α, a in s ∧ b in s := by
  simpa [Set.insert_subset_iff] using (IsChain.pair hab).exists_subset_flag

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (Flag α)
  body: ⟨.ofIsMaxChain _ maxChain_spec⟩

中文:
实例 :
  签名: 非空 (旗 α)
  定义体: ⟨.ofIsMaxChain _ maxChain_spec⟩

Depends on / 依赖: maxChain_spec, ofIsMaxChain
-/
instance : Nonempty (Flag α) := ⟨.ofIsMaxChain _ maxChain_spec⟩

end Flag
