/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
/-!
# Partial homeomorphisms: Images of sets

## Main definitions

* `OpenPartialHomeomorph.IsImage`: predicate for when one set is an image of another
* `OpenPartialHomeomorph.ofSet`: the identity on a set `s`
* `OpenPartialHomeomorph.EqOnSource`: equivalence relation describing the "right" notion of equality
  for open partial homeomorphisms

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

section IsImage

/-!
## `OpenPartialHomeomorph.IsImage` relation

We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomorphism `e` if any of
the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for open partial homeomorphisms.
In this section we transfer API about `PartialEquiv.IsImage` to open partial homeomorphisms and
add a few `OpenPartialHomeomorph`-specific lemmas like `OpenPartialHomeomorph.IsImage.closure`.
-/

/--
Definition of `IsImage` / `IsImage` 的定义

English:
definition IsImage
  signature: (s : Set X) (t : Set Y)
  body: forall ⦃x⦄, x in e.source -> (e x in t ↔ x in s)

中文:
定义 是像
  签名: (s : 集合 X) (t : 集合 Y)
  定义体: forall ⦃x⦄, x in e.source -> (e x in t ↔ x in s)

Depends on / 依赖: e.source, source
-/
def IsImage (s : Set X) (t : Set Y) : Prop :=
  forall ⦃x⦄, x in e.source -> (e x in t ↔ x in s)

namespace IsImage

variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}

/--
theorem `toPartialEquiv` / 定理 `toPartialEquiv`

English:
theorem toPartialEquiv
  given: (h : e.IsImage s t)
  statement: e.toPartialEquiv.IsImage s t
  proof: h

中文:
定理 toPartialEquiv
  条件: (h : e.是像 s t)
  结论: e.toPartialEquiv.是像 s t
  证明: h
-/
theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h

/--
theorem `apply_mem_iff` / 定理 `apply_mem_iff`

English:
theorem apply_mem_iff
  given: (h : e.IsImage s t) (hx : x in e.source)
  statement: e x in t ↔ x in s
  proof: h hx

中文:
定理 apply_mem_iff
  条件: (h : e.是像 s t) (hx : x in e.source)
  结论: e x in t ↔ x in s
  证明: h hx
-/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x in e.source) : e x in t ↔ x in s :=
  h hx

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : e.IsImage s t)
  statement: e.symm.IsImage t s
  proof: h.toPartialEquiv.symm

中文:
定理 symm
  条件: (h : e.是像 s t)
  结论: e.symm.是像 t s
  证明: h.toPartialEquiv.symm
-/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm

/--
theorem `symm_apply_mem_iff` / 定理 `symm_apply_mem_iff`

English:
theorem symm_apply_mem_iff
  given: (h : e.IsImage s t) (hy : y in e.target)
  statement: e.symm y in s ↔ y in t
  proof: h.symm hy

@[simp]

中文:
定理 symm_apply_mem_iff
  条件: (h : e.是像 s t) (hy : y in e.target)
  结论: e.symm y in s ↔ y in t
  证明: h.symm hy

@[simp]

Depends on / 依赖: h.symm
-/
theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y in e.target) : e.symm y in s ↔ y in t :=
  h.symm hy

@[simp]
/--
theorem `symm_iff` / 定理 `symm_iff`

English:
theorem symm_iff
  statement: e.symm.IsImage t s ↔ e.IsImage s t
  proof: ⟨fun h => h.symm, fun h => h.symm⟩

中文:
定理 symm_iff
  结论: e.symm.是像 t s ↔ e.是像 s t
  证明: ⟨fun h => h.symm, fun h => h.symm⟩

Depends on / 依赖: h.symm
-/
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/--
theorem `mapsTo` / 定理 `mapsTo`

English:
theorem mapsTo
  given: (h : e.IsImage s t)
  statement: MapsTo e (e.source inter s) (e.target inter t)
  proof: h.toPartialEquiv.mapsTo

中文:
定理 mapsTo
  条件: (h : e.是像 s t)
  结论: 映射到 e (e.source inter s) (e.target inter t)
  证明: h.toPartialEquiv.mapsTo
-/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source inter s) (e.target inter t) :=
  h.toPartialEquiv.mapsTo

/--
theorem `symm_mapsTo` / 定理 `symm_mapsTo`

English:
theorem symm_mapsTo
  given: (h : e.IsImage s t)
  statement: MapsTo e.symm (e.target inter t) (e.source inter s)
  proof: h.symm.mapsTo

中文:
定理 symm_mapsTo
  条件: (h : e.是像 s t)
  结论: 映射到 e.symm (e.target inter t) (e.source inter s)
  证明: h.symm.mapsTo

Depends on / 依赖: h.symm.mapsTo, mapsTo
-/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target inter t) (e.source inter s) :=
  h.symm.mapsTo

/--
theorem `image_eq` / 定理 `image_eq`

English:
theorem image_eq
  given: (h : e.IsImage s t)
  statement: e '' (e.source inter s) = e.target inter t
  proof: h.toPartialEquiv.image_eq

中文:
定理 image_eq
  条件: (h : e.是像 s t)
  结论: e '' (e.source inter s) = e.target inter t
  证明: h.toPartialEquiv.image_eq

Depends on / 依赖: h.toPartialEquiv.image_eq, image_eq, toPartialEquiv
-/
theorem image_eq (h : e.IsImage s t) : e '' (e.source inter s) = e.target inter t :=
  h.toPartialEquiv.image_eq

/--
theorem `symm_image_eq` / 定理 `symm_image_eq`

English:
theorem symm_image_eq
  given: (h : e.IsImage s t)
  statement: e.symm '' (e.target inter t) = e.source inter s
  proof: h.symm.image_eq

中文:
定理 symm_image_eq
  条件: (h : e.是像 s t)
  结论: e.symm '' (e.target inter t) = e.source inter s
  证明: h.symm.image_eq

Depends on / 依赖: h.symm.image_eq, image_eq
-/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target inter t) = e.source inter s :=
  h.symm.image_eq

/--
theorem `iff_preimage_eq` / 定理 `iff_preimage_eq`

English:
theorem iff_preimage_eq
  statement: e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter s
  proof: PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

中文:
定理 iff_preimage_eq
  结论: e.是像 s t ↔ e.source inter e ⁻¹' t = e.source inter s
  证明: PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

Depends on / 依赖: IsImage, PartialEquiv, PartialEquiv.IsImage.iff_preimage_eq, iff_preimage_eq
-/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter s :=
  PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

/--
theorem `iff_symm_preimage_eq` / 定理 `iff_symm_preimage_eq`

English:
theorem iff_symm_preimage_eq
  statement: e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t
  proof: symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

中文:
定理 iff_symm_preimage_eq
  结论: e.是像 s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t
  证明: symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

Depends on / 依赖: iff_preimage_eq, symm_iff, symm_iff.symm.trans
-/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

/--
theorem `iff_symm_preimage_eq'` / 定理 `iff_symm_preimage_eq'`

English:
theorem iff_symm_preimage_eq'
  proof: by
  rw [iff_symm_preimage_eq]; rw [← image_source_inter_eq]; rw [← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'

中文:
定理 iff_symm_preimage_eq'
  证明: by
  rw [iff_symm_preimage_eq]; rw [← image_source_inter_eq]; rw [← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'

Depends on / 依赖: iff_symm_preimage_eq, image_source_inter_eq
-/
theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target inter e.symm ⁻¹' (e.source inter s) = e.target inter t := by
  rw [iff_symm_preimage_eq]; rw [← image_source_inter_eq]; rw [← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'

/--
theorem `iff_preimage_eq'` / 定理 `iff_preimage_eq'`

English:
theorem iff_preimage_eq'
  statement: e.IsImage s t ↔ e.source inter e ⁻¹' (e.target inter t) = e.source inter s
  proof: symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'

中文:
定理 iff_preimage_eq'
  结论: e.是像 s t ↔ e.source inter e ⁻¹' (e.target inter t) = e.source inter s
  证明: symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'

Depends on / 依赖: iff_symm_preimage_eq, symm_iff, symm_iff.symm.trans
-/
theorem iff_preimage_eq' : e.IsImage s t ↔ e.source inter e ⁻¹' (e.target inter t) = e.source inter s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'

/--
theorem `of_image_eq` / 定理 `of_image_eq`

English:
theorem of_image_eq
  given: (h : e '' (e.source inter s) = e.target inter t)
  statement: e.IsImage s t
  proof: PartialEquiv.IsImage.of_image_eq h

中文:
定理 of_image_eq
  条件: (h : e '' (e.source inter s) = e.target inter t)
  结论: e.是像 s t
  证明: PartialEquiv.IsImage.of_image_eq h

Depends on / 依赖: IsImage, PartialEquiv, PartialEquiv.IsImage.of_image_eq, of_image_eq
-/
theorem of_image_eq (h : e '' (e.source inter s) = e.target inter t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h

/--
theorem `of_symm_image_eq` / 定理 `of_symm_image_eq`

English:
theorem of_symm_image_eq
  given: (h : e.symm '' (e.target inter t) = e.source inter s)
  statement: e.IsImage s t
  proof: PartialEquiv.IsImage.of_symm_image_eq h

中文:
定理 of_symm_image_eq
  条件: (h : e.symm '' (e.target inter t) = e.source inter s)
  结论: e.是像 s t
  证明: PartialEquiv.IsImage.of_symm_image_eq h

Depends on / 依赖: IsImage, PartialEquiv, PartialEquiv.IsImage.of_symm_image_eq, of_symm_image_eq
-/
theorem of_symm_image_eq (h : e.symm '' (e.target inter t) = e.source inter s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h

/--
theorem `compl` / 定理 `compl`

English:
theorem compl
  given: (h : e.IsImage s t)
  statement: e.IsImage sᶜ tᶜ
  proof: fun _ hx => (h hx).not

中文:
定理 compl
  条件: (h : e.是像 s t)
  结论: e.是像 sᶜ tᶜ
  证明: fun _ hx => (h hx).not
-/
protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  proof: fun _ hx => (h hx).and (h' hx)

中文:
定理 inter
  条件: {s' t'} (h : e.是像 s t) (h' : e.是像 s' t')
  证明: fun _ hx => (h hx).and (h' hx)
-/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s inter s') (t inter t') := fun _ hx => (h hx).and (h' hx)

/--
theorem `union` / 定理 `union`

English:
theorem union
  given: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  proof: fun _ hx => (h hx).or (h' hx)

中文:
定理 union
  条件: {s' t'} (h : e.是像 s t) (h' : e.是像 s' t')
  证明: fun _ hx => (h hx).or (h' hx)
-/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s union s') (t union t') := fun _ hx => (h hx).or (h' hx)

/--
theorem `diff` / 定理 `diff`

English:
theorem diff
  given: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  proof: h.inter h'.compl

中文:
定理 diff
  条件: {s' t'} (h : e.是像 s t) (h' : e.是像 s' t')
  证明: h.inter h'.compl
-/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

/--
theorem `leftInvOn_piecewise` / 定理 `leftInvOn_piecewise`

English:
theorem leftInvOn_piecewise
  statement: {e' : OpenPartialHomeomorph X Y} [forall i, Decidable (i in s)]
  proof: h.toPartialEquiv.leftInvOn_piecewise h'

中文:
定理 leftInvOn_piecewise
  结论: {e' : OpenPartialHomeomorph X Y} [对任意 i, 可判定 (i in s)]
  证明: h.toPartialEquiv.leftInvOn_piecewise h'

Depends on / 依赖: h.toPartialEquiv.leftInvOn_piecewise, leftInvOn_piecewise, toPartialEquiv
-/
theorem leftInvOn_piecewise {e' : OpenPartialHomeomorph X Y} [forall i, Decidable (i in s)]
    [forall i, Decidable (i in t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'

/--
theorem `inter_eq_of_inter_eq_of_eqOn` / 定理 `inter_eq_of_inter_eq_of_eqOn`

English:
theorem inter_eq_of_inter_eq_of_eqOn
  statement: {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t)
  proof: h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq

中文:
定理 inter_eq_of_inter_eq_of_eqOn
  结论: {e' : OpenPartialHomeomorph X Y} (h : e.是像 s t)
  证明: h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq

Depends on / 依赖: h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn, inter_eq_of_inter_eq_of_eqOn, toPartialEquiv
-/
theorem inter_eq_of_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source inter s = e'.source inter s) (Heq : EqOn e e' (e.source inter s)) :
    e.target inter t = e'.target inter t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq

/--
theorem `symm_eqOn_of_inter_eq_of_eqOn` / 定理 `symm_eqOn_of_inter_eq_of_eqOn`

English:
theorem symm_eqOn_of_inter_eq_of_eqOn
  statement: {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t)
  proof: h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq

中文:
定理 symm_eqOn_of_inter_eq_of_eqOn
  结论: {e' : OpenPartialHomeomorph X Y} (h : e.是像 s t)
  证明: h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq

Depends on / 依赖: h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn, symm_eq_on_of_inter_eq_of_eqOn, toPartialEquiv
-/
theorem symm_eqOn_of_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t)
    (hs : e.source inter s = e'.source inter s) (Heq : EqOn e e' (e.source inter s)) :
    EqOn e.symm e'.symm (e.target inter t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq

/--
theorem `map_nhdsWithin_eq` / 定理 `map_nhdsWithin_eq`

English:
theorem map_nhdsWithin_eq
  given: (h : e.IsImage s t) (hx : x in e.source)
  statement: map e (𝓝[s] x) = 𝓝[t] e x
  proof: by
  rw [e.map_nhdsWithin_eq hx]; rw [h.image_eq]; rw [e.nhdsWithin_target_inter (e.map_source hx)]

中文:
定理 map_nhdsWithin_eq
  条件: (h : e.是像 s t) (hx : x in e.source)
  结论: map e (𝓝[s] x) = 𝓝[t] e x
  证明: by
  rw [e.map_nhdsWithin_eq hx]; rw [h.image_eq]; rw [e.nhdsWithin_target_inter (e.map_source hx)]

Depends on / 依赖: e.map_nhdsWithin_eq, e.map_source, e.nhdsWithin_target_inter, h.image_eq, image_eq, map_nhdsWithin_eq, map_source, nhdsWithin_target_inter
-/
theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x in e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhdsWithin_eq hx]; rw [h.image_eq]; rw [e.nhdsWithin_target_inter (e.map_source hx)]

/--
theorem `closure` / 定理 `closure`

English:
theorem closure
  given: (h : e.IsImage s t)
  statement: e.IsImage (closure s) (closure t)
  proof: fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]

中文:
定理 closure
  条件: (h : e.是像 s t)
  结论: e.是像 (closure s) (closure t)
  证明: fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]
-/
protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]

/--
theorem `interior` / 定理 `interior`

English:
theorem interior
  given: (h : e.IsImage s t)
  statement: e.IsImage (interior s) (interior t)
  proof: by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl

中文:
定理 interior
  条件: (h : e.是像 s t)
  结论: e.是像 (interior s) (interior t)
  证明: by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
-/
protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl

/--
theorem `frontier` / 定理 `frontier`

English:
theorem frontier
  given: (h : e.IsImage s t)
  statement: e.IsImage (frontier s) (frontier t)
  proof: h.closure.diff h.interior

中文:
定理 frontier
  条件: (h : e.是像 s t)
  结论: e.是像 (frontier s) (frontier t)
  证明: h.closure.diff h.interior
-/
protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (h : e.IsImage s t)
  statement: IsOpen (e.source inter s) ↔ IsOpen (e.target inter t)
  proof: ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩

中文:
定理 isOpen_iff
  条件: (h : e.是像 s t)
  结论: 是开集 (e.source inter s) ↔ 是开集 (e.target inter t)
  证明: ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩

Depends on / 依赖: e.isOpen_inter_preimage, e.symm.isOpen_inter_preimage, h.preimage_eq, h.symm_preimage_eq, isOpen_inter_preimage, preimage_eq, symm_preimage_eq
-/
theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source inter s) ↔ IsOpen (e.target inter t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩

/-- Restrict an `OpenPartialHomeomorph` to a pair of corresponding open sets. -/
@[simps! -fullyApplied apply symm_apply toPartialHomeomorph]
/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: (h : e.IsImage s t) (hs : IsOpen (e.source inter s))
  body: h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left

中文:
定义 restr
  签名: (h : e.是像 s t) (hs : 是开集 (e.source inter s))
  定义体: h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left

Depends on / 依赖: h.toPartialEquiv.restr, toPartialEquiv
-/
def restr (h : e.IsImage s t) (hs : IsOpen (e.source inter s)) : OpenPartialHomeomorph X Y where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left

end IsImage

/--
theorem `isImage_source_target` / 定理 `isImage_source_target`

English:
theorem isImage_source_target
  statement: e.IsImage e.source e.target
  proof: e.toPartialEquiv.isImage_source_target

中文:
定理 isImage_source_target
  结论: e.是像 e.source e.target
  证明: e.toPartialEquiv.isImage_source_target

Depends on / 依赖: e.toPartialEquiv.isImage_source_target, isImage_source_target, toPartialEquiv
-/
theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target

/--
theorem `isImage_source_target_of_disjoint` / 定理 `isImage_source_target_of_disjoint`

English:
theorem isImage_source_target_of_disjoint
  statement: (e' : OpenPartialHomeomorph X Y)
  proof: e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

中文:
定理 isImage_source_target_of_disjoint
  结论: (e' : OpenPartialHomeomorph X Y)
  证明: e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

Depends on / 依赖: e.toPartialEquiv.isImage_source_target_of_disjoint, isImage_source_target_of_disjoint, toPartialEquiv
-/
theorem isImage_source_target_of_disjoint (e' : OpenPartialHomeomorph X Y)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

/--
theorem `preimage_interior` / 定理 `preimage_interior`

English:
theorem preimage_interior
  given: (s : Set Y)
  proof: (IsImage.of_preimage_eq rfl).interior.preimage_eq

中文:
定理 preimage_interior
  条件: (s : 集合 Y)
  证明: (IsImage.of_preimage_eq rfl).interior.preimage_eq

Depends on / 依赖: IsImage, IsImage.of_preimage_eq, interior, interior.preimage_eq, of_preimage_eq, preimage_eq
-/
theorem preimage_interior (s : Set Y) :
    e.source inter e ⁻¹' interior s = e.source inter interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq

/--
theorem `preimage_closure` / 定理 `preimage_closure`

English:
theorem preimage_closure
  given: (s : Set Y)
  statement: e.source inter e ⁻¹' closure s = e.source inter closure (e ⁻¹' s)
  proof: (IsImage.of_preimage_eq rfl).closure.preimage_eq

中文:
定理 preimage_closure
  条件: (s : 集合 Y)
  结论: e.source inter e ⁻¹' closure s = e.source inter closure (e ⁻¹' s)
  证明: (IsImage.of_preimage_eq rfl).closure.preimage_eq

Depends on / 依赖: IsImage, IsImage.of_preimage_eq, closure, closure.preimage_eq, of_preimage_eq, preimage_eq
-/
theorem preimage_closure (s : Set Y) : e.source inter e ⁻¹' closure s = e.source inter closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq

/--
theorem `preimage_frontier` / 定理 `preimage_frontier`

English:
theorem preimage_frontier
  given: (s : Set Y)
  proof: (IsImage.of_preimage_eq rfl).frontier.preimage_eq

中文:
定理 preimage_frontier
  条件: (s : 集合 Y)
  证明: (IsImage.of_preimage_eq rfl).frontier.preimage_eq

Depends on / 依赖: IsImage, IsImage.of_preimage_eq, frontier, frontier.preimage_eq, of_preimage_eq, preimage_eq
-/
theorem preimage_frontier (s : Set Y) :
    e.source inter e ⁻¹' frontier s = e.source inter frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq

end IsImage


section restrOpen
/-!
## Restriction
-/

/--
Definition of `restrOpen` / `restrOpen` 的定义

English:
definition restrOpen
  signature: (s : Set X) (hs : IsOpen s)
  body: (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]

中文:
定义 restrOpen
  签名: (s : 集合 X) (hs : 是开集 s)
  定义体: (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]
-/
protected def restrOpen (s : Set X) (hs : IsOpen s) : OpenPartialHomeomorph X Y :=
  (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]
/--
theorem `restrOpen_toPartialEquiv` / 定理 `restrOpen_toPartialEquiv`

English:
theorem restrOpen_toPartialEquiv
  given: (s : Set X) (hs : IsOpen s)
  proof: rfl

中文:
定理 restrOpen_toPartialEquiv
  条件: (s : 集合 X) (hs : 是开集 s)
  证明: rfl
-/
theorem restrOpen_toPartialEquiv (s : Set X) (hs : IsOpen s) :
    (e.restrOpen s hs).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl

-- Already simp via `PartialEquiv`
/--
theorem `restrOpen_source` / 定理 `restrOpen_source`

English:
theorem restrOpen_source
  given: (s : Set X) (hs : IsOpen s)
  statement: (e.restrOpen s hs).source = e.source inter s
  proof: rfl

中文:
定理 restrOpen_source
  条件: (s : 集合 X) (hs : 是开集 s)
  结论: (e.restrOpen s hs).source = e.source inter s
  证明: rfl
-/
theorem restrOpen_source (s : Set X) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source inter s :=
  rfl

/--
theorem `coe_restrOpen` / 定理 `coe_restrOpen`

English:
theorem coe_restrOpen
  given: {s : Set X} (hs : IsOpen s)
  statement: ⇑(e.restrOpen s hs) = e
  proof: rfl

@[simp]

中文:
定理 coe_restrOpen
  条件: {s : 集合 X} (hs : 是开集 s)
  结论: ⇑(e.restrOpen s hs) = e
  证明: rfl

@[simp]
-/
@[simp] theorem coe_restrOpen {s : Set X} (hs : IsOpen s) : ⇑(e.restrOpen s hs) = e := rfl

@[simp]
/--
theorem `coe_restrOpen_symm` / 定理 `coe_restrOpen_symm`

English:
theorem coe_restrOpen_symm
  given: {s : Set X} (hs : IsOpen s)
  statement: ⇑(e.restrOpen s hs).symm = e.symm
  proof: rfl

中文:
定理 coe_restrOpen_symm
  条件: {s : 集合 X} (hs : 是开集 s)
  结论: ⇑(e.restrOpen s hs).symm = e.symm
  证明: rfl
-/
theorem coe_restrOpen_symm {s : Set X} (hs : IsOpen s) : ⇑(e.restrOpen s hs).symm = e.symm := rfl

/-- Restricting an open partial homeomorphism `e` to `e.source ∩ interior s`. We use the interior to
make sure that the restriction is well defined whatever the set s, since open partial homeomorphisms
are by definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of partial equivalences. -/
@[simps! (attr := mfld_simps) -fullyApplied apply symm_apply,
  simps! (attr := grind =) -isSimp source target]
/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: (s : Set X)
  body: e.restrOpen (interior s) isOpen_interior

@[simp, mfld_simps]

中文:
定义 restr
  签名: (s : 集合 X)
  定义体: e.restrOpen (interior s) isOpen_interior

@[simp, mfld_simps]
-/
protected def restr (s : Set X) : OpenPartialHomeomorph X Y :=
  e.restrOpen (interior s) isOpen_interior

@[simp, mfld_simps]
/--
theorem `restr_toPartialEquiv` / 定理 `restr_toPartialEquiv`

English:
theorem restr_toPartialEquiv
  given: (s : Set X)
  proof: rfl

中文:
定理 restr_toPartialEquiv
  条件: (s : 集合 X)
  证明: rfl
-/
theorem restr_toPartialEquiv (s : Set X) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s) :=
  rfl

/--
theorem `restr_source'` / 定理 `restr_source'`

English:
theorem restr_source'
  given: (s : Set X) (hs : IsOpen s)
  statement: (e.restr s).source = e.source inter s
  proof: by
  grind

中文:
定理 restr_source'
  条件: (s : 集合 X) (hs : 是开集 s)
  结论: (e.restr s).source = e.source inter s
  证明: by
  grind
-/
theorem restr_source' (s : Set X) (hs : IsOpen s) : (e.restr s).source = e.source inter s := by
  grind

/--
theorem `restr_toPartialEquiv'` / 定理 `restr_toPartialEquiv'`

English:
theorem restr_toPartialEquiv'
  given: (s : Set X) (hs : IsOpen s)
  proof: by
  rw [e.restr_toPartialEquiv]; rw [hs.interior_eq]

中文:
定理 restr_toPartialEquiv'
  条件: (s : 集合 X) (hs : 是开集 s)
  证明: by
  rw [e.restr_toPartialEquiv]; rw [hs.interior_eq]

Depends on / 依赖: e.restr_toPartialEquiv, hs.interior_eq, interior_eq, restr_toPartialEquiv
-/
theorem restr_toPartialEquiv' (s : Set X) (hs : IsOpen s) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s := by
  rw [e.restr_toPartialEquiv]; rw [hs.interior_eq]

/--
theorem `restr_eq_of_source_subset` / 定理 `restr_eq_of_source_subset`

English:
theorem restr_eq_of_source_subset
  given: {e : OpenPartialHomeomorph X Y} {s : Set X} (h : e.source subseteq s)
  proof: toPartialEquiv_injective PartialEquiv.restr_eq_of_source_subset
    interior_maximal h e.open_source

@[simp, mfld_simps]

中文:
定理 restr_eq_of_source_subset
  条件: {e : OpenPartialHomeomorph X Y} {s : 集合 X} (h : e.source subseteq s)
  证明: toPartialEquiv_injective PartialEquiv.restr_eq_of_source_subset
    interior_maximal h e.open_source

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.restr_eq_of_source_subset, e.open_source, interior_maximal, open_source, restr_eq_of_source_subset, toPartialEquiv_injective
-/
theorem restr_eq_of_source_subset {e : OpenPartialHomeomorph X Y} {s : Set X} (h : e.source subseteq s) :
    e.restr s = e :=
toPartialEquiv_injective PartialEquiv.restr_eq_of_source_subset
    interior_maximal h e.open_source

@[simp, mfld_simps]
/--
theorem `restr_univ` / 定理 `restr_univ`

English:
theorem restr_univ
  given: {e : OpenPartialHomeomorph X Y}
  statement: e.restr univ = e
  proof: restr_eq_of_source_subset (subset_univ _)

@[simp, grind =]

中文:
定理 restr_univ
  条件: {e : OpenPartialHomeomorph X Y}
  结论: e.restr univ = e
  证明: restr_eq_of_source_subset (subset_univ _)

@[simp, grind =]

Depends on / 依赖: restr_eq_of_source_subset, subset_univ
-/
theorem restr_univ {e : OpenPartialHomeomorph X Y} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

@[simp, grind =]
/--
theorem `restr_source_inter` / 定理 `restr_source_inter`

English:
theorem restr_source_inter
  given: (s : Set X)
  statement: e.restr (e.source inter s) = e.restr s
  proof: by
  refine OpenPartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [e.open_source.interior_eq, ← inter_assoc]

中文:
定理 restr_source_inter
  条件: (s : 集合 X)
  结论: e.restr (e.source inter s) = e.restr s
  证明: by
  refine OpenPartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [e.open_source.interior_eq, ← inter_assoc]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.ext, e.open_source.interior_eq, inter_assoc, interior_eq, open_source
-/
theorem restr_source_inter (s : Set X) : e.restr (e.source inter s) = e.restr s := by
  refine OpenPartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [e.open_source.interior_eq, ← inter_assoc]

end restrOpen

/-!
## ofSet

The identity on a set `s`
-/
section ofSet

variable {s : Set X} (hs : IsOpen s)

/-- The identity partial equivalence on a set `s` -/
@[simps! (attr := mfld_simps) -fullyApplied apply, simps! -isSimp source target]
/--
Definition of `ofSet` / `ofSet` 的定义

English:
definition ofSet
  signature: (s : Set X) (hs : IsOpen s)
  body: PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp, mfld_simps]

中文:
定义 ofSet
  签名: (s : 集合 X) (hs : 是开集 s)
  定义体: PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.ofSet
-/
def ofSet (s : Set X) (hs : IsOpen s) : OpenPartialHomeomorph X X where
  toPartialEquiv := PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp, mfld_simps]
/--
theorem `ofSet_toPartialEquiv` / 定理 `ofSet_toPartialEquiv`

English:
theorem ofSet_toPartialEquiv
  statement: (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s
  proof: rfl

@[simp, mfld_simps]

中文:
定理 ofSet_toPartialEquiv
  结论: (ofSet s hs).toPartialEquiv = 部分等价.ofSet s
  证明: rfl

@[simp, mfld_simps]
-/
theorem ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl

@[simp, mfld_simps]
/--
theorem `ofSet_symm` / 定理 `ofSet_symm`

English:
theorem ofSet_symm
  statement: (ofSet s hs).symm = ofSet s hs
  proof: rfl

@[simp, mfld_simps]

中文:
定理 ofSet_symm
  结论: (ofSet s hs).symm = ofSet s hs
  证明: rfl

@[simp, mfld_simps]
-/
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl

@[simp, mfld_simps]
/--
theorem `ofSet_univ_eq_refl` / 定理 `ofSet_univ_eq_refl`

English:
theorem ofSet_univ_eq_refl
  statement: ofSet univ isOpen_univ = OpenPartialHomeomorph.refl X
  proof: by
  ext <;> simp

中文:
定理 ofSet_univ_eq_refl
  结论: ofSet univ isOpen_univ = OpenPartialHomeomorph.refl X
  证明: by
  ext <;> simp
-/
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = OpenPartialHomeomorph.refl X := by
  ext <;> simp

end ofSet


/-! `EqOnSource`: equivalence on their source -/
section EqOnSource

/--
Definition of `EqOnSource` / `EqOnSource` 的定义

English:
definition EqOnSource
  signature: (e e' : OpenPartialHomeomorph X Y)
  body: e.source = e'.source ∧ EqOn e e' e.source

中文:
定义 EqOnSource
  签名: (e e' : OpenPartialHomeomorph X Y)
  定义体: e.source = e'.source ∧ EqOn e e' e.source

Depends on / 依赖: e.source, source
-/
def EqOnSource (e e' : OpenPartialHomeomorph X Y) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source

/--
theorem `eqOnSource_iff` / 定理 `eqOnSource_iff`

English:
theorem eqOnSource_iff
  given: (e e' : OpenPartialHomeomorph X Y)
  proof: Iff.rfl

中文:
定理 eqOnSource_iff
  条件: (e e' : OpenPartialHomeomorph X Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eqOnSource_iff (e e' : OpenPartialHomeomorph X Y) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl

/--
Instance `eqOnSourceSetoid` / 实例 `eqOnSourceSetoid`

English:
instance eqOnSourceSetoid
  signature: : Setoid (OpenPartialHomeomorph X Y)
  body: { PartialEquiv.eqOnSourceSetoid.comap
    (fun x => (toPartialHomeomorph x).toPartialEquiv) with r := EqOnSource }

中文:
实例 eqOnSourceSetoid
  签名: : 集合等价关系 (OpenPartialHomeomorph X Y)
  定义体: { PartialEquiv.eqOnSourceSetoid.comap
    (fun x => (toPartialHomeomorph x).toPartialEquiv) with r := EqOnSource }

Depends on / 依赖: EqOnSource, PartialEquiv, PartialEquiv.eqOnSourceSetoid.comap, eqOnSourceSetoid, toPartialEquiv, toPartialHomeomorph
-/
instance eqOnSourceSetoid : Setoid (OpenPartialHomeomorph X Y) :=
  { PartialEquiv.eqOnSourceSetoid.comap
    (fun x => (toPartialHomeomorph x).toPartialEquiv) with r := EqOnSource }

/--
theorem `eqOnSource_refl` / 定理 `eqOnSource_refl`

English:
theorem eqOnSource_refl
  statement: e ≈ e
  proof: Setoid.refl _

中文:
定理 eqOnSource_refl
  结论: e ≈ e
  证明: Setoid.refl _

Depends on / 依赖: Setoid, Setoid.refl
-/
theorem eqOnSource_refl : e ≈ e := Setoid.refl _

/--
theorem `EqOnSource.symm'` / 定理 `EqOnSource.symm'`

English:
theorem EqOnSource.symm'
  given: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  statement: e.symm ≈ e'.symm
  proof: PartialEquiv.EqOnSource.symm' h

中文:
定理 EqOnSource.symm'
  条件: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  结论: e.symm ≈ e'.symm
  证明: PartialEquiv.EqOnSource.symm' h
-/
theorem EqOnSource.symm' {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h

/--
theorem `EqOnSource.source_eq` / 定理 `EqOnSource.source_eq`

English:
theorem EqOnSource.source_eq
  given: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  proof: h.1

中文:
定理 EqOnSource.source_eq
  条件: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  证明: h.1
-/
theorem EqOnSource.source_eq {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') :
    e.source = e'.source :=
  h.1

/--
theorem `EqOnSource.target_eq` / 定理 `EqOnSource.target_eq`

English:
theorem EqOnSource.target_eq
  given: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  proof: h.symm'.1

中文:
定理 EqOnSource.target_eq
  条件: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  证明: h.symm'.1
-/
theorem EqOnSource.target_eq {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') :
    e.target = e'.target :=
  h.symm'.1

/--
theorem `EqOnSource.eqOn` / 定理 `EqOnSource.eqOn`

English:
theorem EqOnSource.eqOn
  given: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  statement: EqOn e e' e.source
  proof: h.2

中文:
定理 EqOnSource.eqOn
  条件: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  结论: EqOn e e' e.source
  证明: h.2
-/
theorem EqOnSource.eqOn {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') : EqOn e e' e.source :=
  h.2

/--
theorem `EqOnSource.symm_eqOn_target` / 定理 `EqOnSource.symm_eqOn_target`

English:
theorem EqOnSource.symm_eqOn_target
  given: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  proof: h.symm'.2

中文:
定理 EqOnSource.symm_eqOn_target
  条件: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e')
  证明: h.symm'.2

Depends on / 依赖: h.symm
-/
theorem EqOnSource.symm_eqOn_target {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2

/--
theorem `EqOnSource.restr` / 定理 `EqOnSource.restr`

English:
theorem EqOnSource.restr
  given: {e e' : OpenPartialHomeomorph X Y} (he : e ≈ e') (s : Set X)
  proof: PartialEquiv.EqOnSource.restr he _

中文:
定理 EqOnSource.restr
  条件: {e e' : OpenPartialHomeomorph X Y} (he : e ≈ e') (s : 集合 X)
  证明: PartialEquiv.EqOnSource.restr he _
-/
theorem EqOnSource.restr {e e' : OpenPartialHomeomorph X Y} (he : e ≈ e') (s : Set X) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _

/--
theorem `Set.EqOn.restr_eqOn_source` / 定理 `Set.EqOn.restr_eqOn_source`

English:
theorem Set.EqOn.restr_eqOn_source
  statement: {e e' : OpenPartialHomeomorph X Y}
  proof: by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [mfld_simps, eqOn_refl]

中文:
定理 集合.EqOn.restr_eqOn_source
  结论: {e e' : OpenPartialHomeomorph X Y}
  证明: by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [mfld_simps, eqOn_refl]

Depends on / 依赖: EqOn.trans, Set.inter_comm, e.open_source, e.restr_source, eqOn_refl, inter_comm, mfld_simps, open_source, restr_source
-/
theorem Set.EqOn.restr_eqOn_source {e e' : OpenPartialHomeomorph X Y}
    (h : EqOn e e' (e.source inter e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [mfld_simps, eqOn_refl]

/--
theorem `restr_eqOnSource_of_eqOn` / 定理 `restr_eqOnSource_of_eqOn`

English:
theorem restr_eqOnSource_of_eqOn
  statement: {e e' : OpenPartialHomeomorph X Y} {s : Set X}
  proof: by
  refine ⟨?_, fun z hz => heq (by simpa [e'.open_source.interior_eq] using hz.2)⟩
  rw [e'.restr_source s]; rw [e.restr_source' _ (e'.open_source.inter isOpen_interior)]; rw [inter_eq_right.mpr hsub]

中文:
定理 restr_eqOnSource_of_eqOn
  结论: {e e' : OpenPartialHomeomorph X Y} {s : 集合 X}
  证明: by
  refine ⟨?_, fun z hz => heq (by simpa [e'.open_source.interior_eq] using hz.2)⟩
  rw [e'.restr_source s]; rw [e.restr_source' _ (e'.open_source.inter isOpen_interior)]; rw [inter_eq_right.mpr hsub]

Depends on / 依赖: e.restr_source, inter_eq_right, inter_eq_right.mpr, interior_eq, isOpen_interior, open_source, open_source.inter, open_source.interior_eq, restr_source
-/
theorem restr_eqOnSource_of_eqOn {e e' : OpenPartialHomeomorph X Y} {s : Set X}
    (heq : EqOn e e' (e'.source inter interior s)) (hsub : e'.source inter interior s subseteq e.source) :
    e.restr (e'.source inter interior s) ≈ e'.restr s := by
  refine ⟨?_, fun z hz => heq (by simpa [e'.open_source.interior_eq] using hz.2)⟩
  rw [e'.restr_source s]; rw [e.restr_source' _ (e'.open_source.inter isOpen_interior)]; rw [inter_eq_right.mpr hsub]

/--
theorem `restr_eqOnSource_of_eqOn'` / 定理 `restr_eqOnSource_of_eqOn'`

English:
theorem restr_eqOnSource_of_eqOn'
  statement: {e e' : OpenPartialHomeomorph X Y} {s : Set X} (hs : IsOpen s)
  proof: (hs.interior_eq ▸ restr_eqOnSource_of_eqOn) (heq.mono Set.inter_subset_right) hsub

中文:
定理 restr_eqOnSource_of_eqOn'
  结论: {e e' : OpenPartialHomeomorph X Y} {s : 集合 X} (hs : 是开集 s)
  证明: (hs.interior_eq ▸ restr_eqOnSource_of_eqOn) (heq.mono Set.inter_subset_right) hsub

Depends on / 依赖: Set.inter_subset_right, heq.mono, hs.interior_eq, inter_subset_right, interior_eq, restr_eqOnSource_of_eqOn
-/
theorem restr_eqOnSource_of_eqOn' {e e' : OpenPartialHomeomorph X Y} {s : Set X} (hs : IsOpen s)
    (heq : EqOn e e' s) (hsub : e'.source inter s subseteq e.source) :
    e.restr (e'.source inter s) ≈ e'.restr s :=
  (hs.interior_eq ▸ restr_eqOnSource_of_eqOn) (heq.mono Set.inter_subset_right) hsub

/--
theorem `eq_of_eqOnSource_univ` / 定理 `eq_of_eqOnSource_univ`

English:
theorem eq_of_eqOnSource_univ
  statement: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
  proof: toPartialEquiv_injective PartialEquiv.eq_of_eqOnSource_univ _ _ h s t

中文:
定理 eq_of_eqOnSource_univ
  结论: {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
  证明: toPartialEquiv_injective PartialEquiv.eq_of_eqOnSource_univ _ _ h s t

Depends on / 依赖: PartialEquiv, PartialEquiv.eq_of_eqOnSource_univ, eq_of_eqOnSource_univ, toPartialEquiv_injective
-/
theorem eq_of_eqOnSource_univ {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
toPartialEquiv_injective PartialEquiv.eq_of_eqOnSource_univ _ _ h s t

variable {s : Set X}

/--
lemma `restr_eqOnSource_restr` / 引理 `restr_eqOnSource_restr`

English:
lemma restr_eqOnSource_restr
  statement: {s' : Set X}
  proof: by
  constructor
  · simpa [e.restr_source]
  · simp [Set.eqOn_refl]

中文:
引理 restr_eqOnSource_restr
  结论: {s' : 集合 X}
  证明: by
  constructor
  · simpa [e.restr_source]
  · simp [Set.eqOn_refl]

Depends on / 依赖: Set.eqOn_refl, e.restr_source, eqOn_refl, restr_source
-/
lemma restr_eqOnSource_restr {s' : Set X}
    (hss' : e.source inter interior s = e.source inter interior s') :
    e.restr s ≈ e.restr s' := by
  constructor
  · simpa [e.restr_source]
  · simp [Set.eqOn_refl]

/--
lemma `restr_inter_source` / 引理 `restr_inter_source`

English:
lemma restr_inter_source
  statement: e.restr (e.source inter s) ≈ e.restr s
  proof: e.restr_eqOnSource_restr (by simp [interior_eq_iff_isOpen.mpr e.open_source])

中文:
引理 restr_inter_source
  结论: e.restr (e.source inter s) ≈ e.restr s
  证明: e.restr_eqOnSource_restr (by simp [interior_eq_iff_isOpen.mpr e.open_source])

Depends on / 依赖: e.open_source, e.restr_eqOnSource_restr, interior_eq_iff_isOpen, interior_eq_iff_isOpen.mpr, open_source, restr_eqOnSource_restr
-/
lemma restr_inter_source : e.restr (e.source inter s) ≈ e.restr s :=
  e.restr_eqOnSource_restr (by simp [interior_eq_iff_isOpen.mpr e.open_source])

end EqOnSource

end OpenPartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

/- Register as simp lemmas that the fields of an open partial homeomorphism built from a
homeomorphism correspond to the fields of the original homeomorphism. -/

@[simp, mfld_simps]
/--
theorem `refl_toOpenPartialHomeomorph` / 定理 `refl_toOpenPartialHomeomorph`

English:
theorem refl_toOpenPartialHomeomorph
  proof: rfl

@[simp, mfld_simps]

中文:
定理 refl_toOpenPartialHomeomorph
  证明: rfl

@[simp, mfld_simps]
-/
theorem refl_toOpenPartialHomeomorph :
    (Homeomorph.refl X).toOpenPartialHomeomorph = OpenPartialHomeomorph.refl X :=
  rfl

@[simp, mfld_simps]
/--
theorem `symm_toOpenPartialHomeomorph` / 定理 `symm_toOpenPartialHomeomorph`

English:
theorem symm_toOpenPartialHomeomorph
  proof: rfl

中文:
定理 symm_toOpenPartialHomeomorph
  证明: rfl
-/
theorem symm_toOpenPartialHomeomorph :
    e.symm.toOpenPartialHomeomorph = e.toOpenPartialHomeomorph.symm :=
  rfl

end Homeomorph
