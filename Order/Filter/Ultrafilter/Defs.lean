/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Map
public import Mathlib.Order.ZornAtoms

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `Ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `Ultrafilter`: subtype of ultrafilters;
* `pure x : Ultrafilter α`: `pure x` as an `Ultrafilter`;
* `Ultrafilter.map`, `Ultrafilter.bind`, `Ultrafilter.comap` : operations on ultrafilters;
-/

@[expose] public section

assert_not_exists Set.Finite

universe u v

variable {α : Type u} {β : Type v} {γ : Type*}

open Set Filter Function

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAtomic (Filter α)
  body: IsAtomic.of_isChain_bounded fun c hc hne hb =>
    ⟨sInf c, (sInf_neBot_of_directed' hne (show IsChain (· >= ·) c from hc.symm).directedOn hb).ne,
      fun _ hx => sInf_le hx⟩

中文:
实例 :
  签名: 是原子的 (滤子 α)
  定义体: IsAtomic.of_isChain_bounded fun c hc hne hb =>
    ⟨sInf c, (sInf_neBot_of_directed' hne (show IsChain (· >= ·) c from hc.symm).directedOn hb).ne,
      fun _ hx => sInf_le hx⟩

Depends on / 依赖: IsAtomic, IsAtomic.of_isChain_bounded, IsChain, directedOn, hc.symm, of_isChain_bounded, sInf_le, sInf_neBot_of_directed
-/
instance : IsAtomic (Filter α) :=
  IsAtomic.of_isChain_bounded fun c hc hne hb =>
    ⟨sInf c, (sInf_neBot_of_directed' hne (show IsChain (· >= ·) c from hc.symm).directedOn hb).ne,
      fun _ hx => sInf_le hx⟩

/--
Definition of `Ultrafilter` / `Ultrafilter` 的定义

English:
structure Ultrafilter
  parameters: (α : Type*)
  extends: Filter α
  axioms and operations (2):
    - neBot' : NeBot toFilter
    - le_of_le : forall g, Filter.NeBot g -> g <= toFilter -> toFilter <= g

中文:
结构 Ultrafilter
  参数: (α : 类型)
  继承: 滤子 α
  公理与运算 (2 个):
    - neBot' : NeBot toFilter
    - le_of_le : 对任意 g, 滤子.NeBot g -> g <= toFilter -> toFilter <= g
-/
structure Ultrafilter (α : Type*) extends Filter α where
  /-- An ultrafilter is nontrivial. -/
  protected neBot' : NeBot toFilter
  /-- If `g` is a nontrivial filter that is less than or equal to an ultrafilter, then it is greater
  than or equal to the ultrafilter. -/
  protected le_of_le : forall g, Filter.NeBot g -> g <= toFilter -> toFilter <= g

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α -> Prop}

attribute [coe] Ultrafilter.toFilter

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC (Ultrafilter α) (Filter α)
  body: ⟨Ultrafilter.toFilter⟩

中文:
实例 :
  签名: CoeTC (Ultrafilter α) (滤子 α)
  定义体: ⟨Ultrafilter.toFilter⟩

Depends on / 依赖: Ultrafilter, Ultrafilter.toFilter, toFilter
-/
instance : CoeTC (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.toFilter⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Set α) (Ultrafilter α)
  body: ⟨fun f s => s in (f : Filter α)⟩

中文:
实例 :
  签名: Membership (集合 α) (Ultrafilter α)
  定义体: ⟨fun f s => s in (f : Filter α)⟩

Depends on / 依赖: Filter
-/
instance : Membership (Set α) (Ultrafilter α) :=
  ⟨fun f s => s in (f : Filter α)⟩

/--
theorem `unique` / 定理 `unique`

English:
theorem unique
  given: (f : Ultrafilter α) {g : Filter α} (h : g <= f) (hne : NeBot g := by infer_instance)
  proof: le_antisymm h f.le_of_le g hne h

中文:
定理 unique
  条件: (f : Ultrafilter α) {g : 滤子 α} (h : g <= f) (hne : NeBot g := by infer_instance)
  证明: le_antisymm h f.le_of_le g hne h

Depends on / 依赖: f.le_of_le, infer_instance, le_antisymm, le_of_le
-/
theorem unique (f : Ultrafilter α) {g : Filter α} (h : g <= f) (hne : NeBot g := by infer_instance) :
    g = f :=
le_antisymm h f.le_of_le g hne h

/--
Instance `neBot` / 实例 `neBot`

English:
instance neBot
  signature: (f : Ultrafilter α)
  body: f.neBot'

中文:
实例 neBot
  签名: (f : Ultrafilter α)
  定义体: f.neBot'

Depends on / 依赖: f.neBot
-/
instance neBot (f : Ultrafilter α) : NeBot (f : Filter α) :=
  f.neBot'

/--
theorem `isAtom` / 定理 `isAtom`

English:
theorem isAtom
  given: (f : Ultrafilter α)
  statement: IsAtom (f : Filter α)
  proof: ⟨f.neBot.ne, fun _ hgf => by_contra fun hg => hgf.ne f.unique hgf.le ⟨hg⟩⟩

@[simp, norm_cast]

中文:
定理 isAtom
  条件: (f : Ultrafilter α)
  结论: IsAtom (f : 滤子 α)
  证明: ⟨f.neBot.ne, fun _ hgf => by_contra fun hg => hgf.ne f.unique hgf.le ⟨hg⟩⟩

@[simp, norm_cast]
-/
protected theorem isAtom (f : Ultrafilter α) : IsAtom (f : Filter α) :=
⟨f.neBot.ne, fun _ hgf => by_contra fun hg => hgf.ne f.unique hgf.le ⟨hg⟩⟩

@[simp, norm_cast]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  statement: s in (f : Filter α) ↔ s in f
  proof: Iff.rfl

中文:
定理 mem_coe
  结论: s in (f : 滤子 α) ↔ s in f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe : s in (f : Filter α) ↔ s in f :=
  Iff.rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Ultrafilter α -> Filter α)

中文:
定理 coe_injective
  结论: 单射 ((↑) : Ultrafilter α -> 滤子 α)
-/
theorem coe_injective : Injective ((↑) : Ultrafilter α -> Filter α)
  | ⟨f, h₁, h₂⟩, ⟨g, _, _⟩, _ => by congr

/--
theorem `eq_of_le` / 定理 `eq_of_le`

English:
theorem eq_of_le
  given: {f g : Ultrafilter α} (h : (f : Filter α) <= g)
  statement: f = g
  proof: coe_injective (g.unique h)

@[simp, norm_cast]

中文:
定理 eq_of_le
  条件: {f g : Ultrafilter α} (h : (f : 滤子 α) <= g)
  结论: f = g
  证明: coe_injective (g.unique h)

@[simp, norm_cast]

Depends on / 依赖: coe_injective, g.unique, unique
-/
theorem eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) <= g) : f = g :=
  coe_injective (g.unique h)

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: {f g : Ultrafilter α}
  statement: (f : Filter α) <= g ↔ f = g
  proof: ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩

@[simp, norm_cast]

中文:
定理 coe_le_coe
  条件: {f g : Ultrafilter α}
  结论: (f : 滤子 α) <= g ↔ f = g
  证明: ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩

@[simp, norm_cast]

Depends on / 依赖: eq_of_le, le_rfl
-/
theorem coe_le_coe {f g : Ultrafilter α} : (f : Filter α) <= g ↔ f = g :=
  ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (f : Filter α) = g ↔ f = g
  proof: coe_injective.eq_iff

@[ext]

中文:
定理 coe_inj
  结论: (f : 滤子 α) = g ↔ f = g
  证明: coe_injective.eq_iff

@[ext]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj : (f : Filter α) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: Ultrafilter α⦄ (h : forall s, s in f ↔ s in g) : f = g
  proof: coe_injective Filter.ext h

中文:
定理 ext
  条件: ⦃f g
  结论: Ultrafilter α⦄ (h : 对任意 s, s in f ↔ s in g) : f = g
  证明: coe_injective Filter.ext h

Depends on / 依赖: Filter, Filter.ext, coe_injective
-/
theorem ext ⦃f g : Ultrafilter α⦄ (h : forall s, s in f ↔ s in g) : f = g :=
coe_injective Filter.ext h

/--
theorem `le_of_inf_neBot` / 定理 `le_of_inf_neBot`

English:
theorem le_of_inf_neBot
  given: (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f ⊓ g))
  statement: ↑f <= g
  proof: le_of_inf_eq (f.unique inf_le_left hg)

中文:
定理 le_of_inf_neBot
  条件: (f : Ultrafilter α) {g : 滤子 α} (hg : NeBot (↑f ⊓ g))
  结论: ↑f <= g
  证明: le_of_inf_eq (f.unique inf_le_left hg)

Depends on / 依赖: f.unique, inf_le_left, le_of_inf_eq, unique
-/
theorem le_of_inf_neBot (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f ⊓ g)) : ↑f <= g :=
  le_of_inf_eq (f.unique inf_le_left hg)

/--
theorem `le_of_inf_neBot'` / 定理 `le_of_inf_neBot'`

English:
theorem le_of_inf_neBot'
  given: (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g ⊓ f))
  statement: ↑f <= g
  proof: f.le_of_inf_neBot by rwa [inf_comm]

中文:
定理 le_of_inf_neBot'
  条件: (f : Ultrafilter α) {g : 滤子 α} (hg : NeBot (g ⊓ f))
  结论: ↑f <= g
  证明: f.le_of_inf_neBot by rwa [inf_comm]

Depends on / 依赖: f.le_of_inf_neBot, inf_comm, le_of_inf_neBot
-/
theorem le_of_inf_neBot' (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g ⊓ f)) : ↑f <= g :=
f.le_of_inf_neBot by rwa [inf_comm]

/--
theorem `inf_neBot_iff` / 定理 `inf_neBot_iff`

English:
theorem inf_neBot_iff
  given: {f : Ultrafilter α} {g : Filter α}
  statement: NeBot (↑f ⊓ g) ↔ ↑f <= g
  proof: ⟨le_of_inf_neBot f, fun h => (inf_of_le_left h).symm ▸ f.neBot⟩

中文:
定理 inf_neBot_iff
  条件: {f : Ultrafilter α} {g : 滤子 α}
  结论: NeBot (↑f ⊓ g) ↔ ↑f <= g
  证明: ⟨le_of_inf_neBot f, fun h => (inf_of_le_left h).symm ▸ f.neBot⟩

Depends on / 依赖: f.neBot, inf_of_le_left, le_of_inf_neBot
-/
theorem inf_neBot_iff {f : Ultrafilter α} {g : Filter α} : NeBot (↑f ⊓ g) ↔ ↑f <= g :=
  ⟨le_of_inf_neBot f, fun h => (inf_of_le_left h).symm ▸ f.neBot⟩

/--
theorem `disjoint_iff_not_le` / 定理 `disjoint_iff_not_le`

English:
theorem disjoint_iff_not_le
  given: {f : Ultrafilter α} {g : Filter α}
  statement: Disjoint (↑f) g ↔ ¬↑f <= g
  proof: by
  rw [← inf_neBot_iff]; rw [neBot_iff]; rw [Ne]; rw [not_not]; rw [disjoint_iff]

@[simp]

中文:
定理 disjoint_iff_not_le
  条件: {f : Ultrafilter α} {g : 滤子 α}
  结论: Disjoint (↑f) g ↔ ¬↑f <= g
  证明: by
  rw [← inf_neBot_iff]; rw [neBot_iff]; rw [Ne]; rw [not_not]; rw [disjoint_iff]

@[simp]

Depends on / 依赖: disjoint_iff, inf_neBot_iff, neBot_iff, not_not
-/
theorem disjoint_iff_not_le {f : Ultrafilter α} {g : Filter α} : Disjoint (↑f) g ↔ ¬↑f <= g := by
  rw [← inf_neBot_iff]; rw [neBot_iff]; rw [Ne]; rw [not_not]; rw [disjoint_iff]

@[simp]
/--
theorem `compl_notMem_iff` / 定理 `compl_notMem_iff`

English:
theorem compl_notMem_iff
  statement: sᶜ ∉ f ↔ s in f
  proof: ⟨fun hsc =>
le_principal_iff.1
f.le_of_inf_neBot ⟨fun h => hsc mem_of_eq_bot by rwa [compl_compl]⟩,
    compl_notMem⟩

@[simp]

中文:
定理 compl_notMem_iff
  结论: sᶜ ∉ f ↔ s in f
  证明: ⟨fun hsc =>
le_principal_iff.1
f.le_of_inf_neBot ⟨fun h => hsc mem_of_eq_bot by rwa [compl_compl]⟩,
    compl_notMem⟩

@[simp]

Depends on / 依赖: compl_compl, compl_notMem, f.le_of_inf_neBot, le_of_inf_neBot, le_principal_iff, mem_of_eq_bot
-/
theorem compl_notMem_iff : sᶜ ∉ f ↔ s in f :=
  ⟨fun hsc =>
le_principal_iff.1
f.le_of_inf_neBot ⟨fun h => hsc mem_of_eq_bot by rwa [compl_compl]⟩,
    compl_notMem⟩

@[simp]
/--
theorem `frequently_iff_eventually` / 定理 `frequently_iff_eventually`

English:
theorem frequently_iff_eventually
  statement: (existsᶠ x in f, p x) ↔ forallᶠ x in f, p x
  proof: compl_notMem_iff

alias ⟨_root_.Filter.Frequently.eventually, _⟩ := frequently_iff_eventually

中文:
定理 frequently_iff_eventually
  结论: (存在ᶠ x in f, p x) ↔ 对任意ᶠ x in f, p x
  证明: compl_notMem_iff

alias ⟨_root_.Filter.Frequently.eventually, _⟩ := frequently_iff_eventually

Depends on / 依赖: compl_notMem_iff
-/
theorem frequently_iff_eventually : (existsᶠ x in f, p x) ↔ forallᶠ x in f, p x :=
  compl_notMem_iff

alias ⟨_root_.Filter.Frequently.eventually, _⟩ := frequently_iff_eventually

/--
theorem `compl_mem_iff_notMem` / 定理 `compl_mem_iff_notMem`

English:
theorem compl_mem_iff_notMem
  statement: sᶜ in f ↔ s ∉ f
  proof: by rw [← compl_notMem_iff, compl_compl]

中文:
定理 compl_mem_iff_notMem
  结论: sᶜ in f ↔ s ∉ f
  证明: by rw [← compl_notMem_iff, compl_compl]

Depends on / 依赖: compl_compl, compl_notMem_iff
-/
theorem compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f := by rw [← compl_notMem_iff, compl_compl]

/--
theorem `sdiff_mem_iff` / 定理 `sdiff_mem_iff`

English:
theorem sdiff_mem_iff
  given: (f : Ultrafilter α)
  statement: s \ t in f ↔ s in f ∧ t ∉ f
  proof: inter_mem_iff.trans and_congr Iff.rfl compl_mem_iff_notMem

@[deprecated (since := "2026-06-03")] alias diff_mem_iff := sdiff_mem_iff

中文:
定理 sdiff_mem_iff
  条件: (f : Ultrafilter α)
  结论: s \ t in f ↔ s in f ∧ t ∉ f
  证明: inter_mem_iff.trans and_congr Iff.rfl compl_mem_iff_notMem

@[deprecated (since := "2026-06-03")] alias diff_mem_iff := sdiff_mem_iff

Depends on / 依赖: Decidable, DecidableEq, Iff.rfl, Quotient, and_congr, c.Quotient, compl_mem_iff_notMem, inter_mem_iff, inter_mem_iff.trans
-/
theorem sdiff_mem_iff (f : Ultrafilter α) : s \ t in f ↔ s in f ∧ t ∉ f :=
inter_mem_iff.trans and_congr Iff.rfl compl_mem_iff_notMem

@[deprecated (since := "2026-06-03")] alias diff_mem_iff := sdiff_mem_iff

/--
Definition of `ofComplNotMemIff` / `ofComplNotMemIff` 的定义

English:
definition ofComplNotMemIff
  signature: (f : Filter α) (h : forall s, sᶜ ∉ f ↔ s in f)
  body: f
  neBot' := ⟨fun hf => by simp [hf] at h⟩
  le_of_le _ _ hgf s hs := (h s).1 fun hsc => compl_notMem hs (hgf hsc)

中文:
定义 ofComplNotMemIff
  签名: (f : 滤子 α) (h : 对任意 s, sᶜ ∉ f ↔ s in f)
  定义体: f
  neBot' := ⟨fun hf => by simp [hf] at h⟩
  le_of_le _ _ hgf s hs := (h s).1 fun hsc => compl_notMem hs (hgf hsc)
-/
def ofComplNotMemIff (f : Filter α) (h : forall s, sᶜ ∉ f ↔ s in f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨fun hf => by simp [hf] at h⟩
  le_of_le _ _ hgf s hs := (h s).1 fun hsc => compl_notMem hs (hgf hsc)

/--
Definition of `ofAtom` / `ofAtom` 的定义

English:
definition ofAtom
  signature: (f : Filter α) (hf : IsAtom f)
  body: f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (isAtom_iff_le_of_ge.1 hf).2 g hg.ne

中文:
定义 ofAtom
  签名: (f : 滤子 α) (hf : IsAtom f)
  定义体: f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (isAtom_iff_le_of_ge.1 hf).2 g hg.ne
-/
def ofAtom (f : Filter α) (hf : IsAtom f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (isAtom_iff_le_of_ge.1 hf).2 g hg.ne

/--
theorem `nonempty_of_mem` / 定理 `nonempty_of_mem`

English:
theorem nonempty_of_mem
  given: (hs : s in f)
  statement: s.Nonempty
  proof: Filter.nonempty_of_mem hs

中文:
定理 nonempty_of_mem
  条件: (hs : s in f)
  结论: s.非空
  证明: Filter.nonempty_of_mem hs

Depends on / 依赖: Filter, Filter.nonempty_of_mem, nonempty_of_mem
-/
theorem nonempty_of_mem (hs : s in f) : s.Nonempty :=
  Filter.nonempty_of_mem hs

/--
theorem `ne_empty_of_mem` / 定理 `ne_empty_of_mem`

English:
theorem ne_empty_of_mem
  given: (hs : s in f)
  statement: s != ∅
  proof: (nonempty_of_mem hs).ne_empty

@[simp]

中文:
定理 ne_empty_of_mem
  条件: (hs : s in f)
  结论: s != ∅
  证明: (nonempty_of_mem hs).ne_empty

@[simp]

Depends on / 依赖: ne_empty, nonempty_of_mem
-/
theorem ne_empty_of_mem (hs : s in f) : s != ∅ :=
  (nonempty_of_mem hs).ne_empty

@[simp]
/--
theorem `empty_notMem` / 定理 `empty_notMem`

English:
theorem empty_notMem
  statement: ∅ ∉ f
  proof: Filter.empty_notMem (f : Filter α)

@[simp]

中文:
定理 empty_notMem
  结论: ∅ ∉ f
  证明: Filter.empty_notMem (f : Filter α)

@[simp]

Depends on / 依赖: Filter, Filter.empty_notMem, empty_notMem
-/
theorem empty_notMem : ∅ ∉ f :=
  Filter.empty_notMem (f : Filter α)

@[simp]
/--
theorem `le_sup_iff` / 定理 `le_sup_iff`

English:
theorem le_sup_iff
  given: {u : Ultrafilter α} {f g : Filter α}
  statement: ↑u <= f ⊔ g ↔ ↑u <= f ∨ ↑u <= g
  proof: not_iff_not.1 by simp only [← disjoint_iff_not_le, not_or, disjoint_sup_right]

@[simp]

中文:
定理 le_sup_iff
  条件: {u : Ultrafilter α} {f g : 滤子 α}
  结论: ↑u <= f ⊔ g ↔ ↑u <= f ∨ ↑u <= g
  证明: not_iff_not.1 by simp only [← disjoint_iff_not_le, not_or, disjoint_sup_right]

@[simp]

Depends on / 依赖: disjoint_iff_not_le, disjoint_sup_right, not_iff_not, not_or
-/
theorem le_sup_iff {u : Ultrafilter α} {f g : Filter α} : ↑u <= f ⊔ g ↔ ↑u <= f ∨ ↑u <= g :=
not_iff_not.1 by simp only [← disjoint_iff_not_le, not_or, disjoint_sup_right]

@[simp]
/--
theorem `union_mem_iff` / 定理 `union_mem_iff`

English:
theorem union_mem_iff
  statement: s union t in f ↔ s in f ∨ t in f
  proof: by
  simp only [← mem_coe, ← le_principal_iff, ← sup_principal, le_sup_iff]

中文:
定理 union_mem_iff
  结论: s union t in f ↔ s in f ∨ t in f
  证明: by
  simp only [← mem_coe, ← le_principal_iff, ← sup_principal, le_sup_iff]

Depends on / 依赖: le_principal_iff, le_sup_iff, mem_coe, sup_principal
-/
theorem union_mem_iff : s union t in f ↔ s in f ∨ t in f := by
  simp only [← mem_coe, ← le_principal_iff, ← sup_principal, le_sup_iff]

/--
theorem `mem_or_compl_mem` / 定理 `mem_or_compl_mem`

English:
theorem mem_or_compl_mem
  given: (f : Ultrafilter α) (s : Set α)
  statement: s in f ∨ sᶜ in f
  proof: or_iff_not_imp_left.2 compl_mem_iff_notMem.2

中文:
定理 mem_or_compl_mem
  条件: (f : Ultrafilter α) (s : 集合 α)
  结论: s in f ∨ sᶜ in f
  证明: or_iff_not_imp_left.2 compl_mem_iff_notMem.2

Depends on / 依赖: compl_mem_iff_notMem, or_iff_not_imp_left
-/
theorem mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s in f ∨ sᶜ in f :=
  or_iff_not_imp_left.2 compl_mem_iff_notMem.2

/--
theorem `em` / 定理 `em`

English:
theorem em
  given: (f : Ultrafilter α) (p : α -> Prop)
  statement: (forallᶠ x in f, p x) ∨ forallᶠ x in f, ¬p x
  proof: f.mem_or_compl_mem { x | p x }

中文:
定理 em
  条件: (f : Ultrafilter α) (p : α -> 命题)
  结论: (对任意ᶠ x in f, p x) ∨ 对任意ᶠ x in f, ¬p x
  证明: f.mem_or_compl_mem { x | p x }
-/
protected theorem em (f : Ultrafilter α) (p : α -> Prop) : (forallᶠ x in f, p x) ∨ forallᶠ x in f, ¬p x :=
  f.mem_or_compl_mem { x | p x }

/--
theorem `eventually_or` / 定理 `eventually_or`

English:
theorem eventually_or
  statement: (forallᶠ x in f, p x ∨ q x) ↔ (forallᶠ x in f, p x) ∨ forallᶠ x in f, q x
  proof: union_mem_iff

@[push ← high] -- higher priority than `Filter.not_eventually`

中文:
定理 eventually_or
  结论: (对任意ᶠ x in f, p x ∨ q x) ↔ (对任意ᶠ x in f, p x) ∨ 对任意ᶠ x in f, q x
  证明: union_mem_iff

@[push ← high] -- higher priority than `Filter.not_eventually`

Depends on / 依赖: union_mem_iff
-/
theorem eventually_or : (forallᶠ x in f, p x ∨ q x) ↔ (forallᶠ x in f, p x) ∨ forallᶠ x in f, q x :=
  union_mem_iff

@[push ← high] -- higher priority than `Filter.not_eventually`
/--
theorem `eventually_not` / 定理 `eventually_not`

English:
theorem eventually_not
  statement: (forallᶠ x in f, ¬p x) ↔ ¬forallᶠ x in f, p x
  proof: compl_mem_iff_notMem

中文:
定理 eventually_not
  结论: (对任意ᶠ x in f, ¬p x) ↔ ¬对任意ᶠ x in f, p x
  证明: compl_mem_iff_notMem

Depends on / 依赖: compl_mem_iff_notMem
-/
theorem eventually_not : (forallᶠ x in f, ¬p x) ↔ ¬forallᶠ x in f, p x :=
  compl_mem_iff_notMem

/--
theorem `eventually_imp` / 定理 `eventually_imp`

English:
theorem eventually_imp
  statement: (forallᶠ x in f, p x -> q x) ↔ (forallᶠ x in f, p x) -> forallᶠ x in f, q x
  proof: by
  simp only [imp_iff_not_or, eventually_or, eventually_not]

中文:
定理 eventually_imp
  结论: (对任意ᶠ x in f, p x -> q x) ↔ (对任意ᶠ x in f, p x) -> 对任意ᶠ x in f, q x
  证明: by
  simp only [imp_iff_not_or, eventually_or, eventually_not]

Depends on / 依赖: eventually_not, eventually_or, imp_iff_not_or
-/
theorem eventually_imp : (forallᶠ x in f, p x -> q x) ↔ (forallᶠ x in f, p x) -> forallᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or, eventually_not]

/-- Pushforward for ultrafilters. -/
nonrec def map (m : α -> β) (f : Ultrafilter α) : Ultrafilter β :=
  ofComplNotMemIff (map m f) fun s => @compl_notMem_iff _ f (m ⁻¹' s)

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (m : α -> β) (f : Ultrafilter α)
  statement: (map m f : Filter β) = Filter.map m ↑f
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (m : α -> β) (f : Ultrafilter α)
  结论: (map m f : 滤子 β) = 滤子.map m ↑f
  证明: rfl

@[simp]
-/
theorem coe_map (m : α -> β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.map m ↑f :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {m : α -> β} {f : Ultrafilter α} {s : Set β}
  statement: s in map m f ↔ m ⁻¹' s in f
  proof: Iff.rfl

@[simp]
nonrec theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id

@[simp]

中文:
定理 mem_map
  条件: {m : α -> β} {f : Ultrafilter α} {s : 集合 β}
  结论: s in map m f ↔ m ⁻¹' s in f
  证明: Iff.rfl

@[simp]
nonrec theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {m : α -> β} {f : Ultrafilter α} {s : Set β} : s in map m f ↔ m ⁻¹' s in f :=
  Iff.rfl

@[simp]
nonrec theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id

@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: (f : Ultrafilter α)
  statement: (f.map fun x => x) = f
  proof: map_id _

@[simp]
nonrec theorem map_map (f : Ultrafilter α) (m : α -> β) (n : β -> γ) :
    (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map

中文:
定理 map_id'
  条件: (f : Ultrafilter α)
  结论: (f.map fun x => x) = f
  证明: map_id _

@[simp]
nonrec theorem map_map (f : Ultrafilter α) (m : α -> β) (n : β -> γ) :
    (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map

Depends on / 依赖: map_id
-/
theorem map_id' (f : Ultrafilter α) : (f.map fun x => x) = f :=
  map_id _

@[simp]
nonrec theorem map_map (f : Ultrafilter α) (m : α -> β) (n : β -> γ) :
    (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
nonrec def comap {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m in u) :
    Ultrafilter α where
  toFilter := comap m u
  neBot' := u.neBot'.comap_of_range_mem large
  le_of_le g hg hgu := by
    simp only [← u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl]

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  statement: {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m in u)
  proof: mem_comap_iff inj large

@[simp, norm_cast]

中文:
定理 mem_comap
  结论: {m : α -> β} (u : Ultrafilter β) (inj : 单射 m) (large : 集合.range m in u)
  证明: mem_comap_iff inj large

@[simp, norm_cast]

Depends on / 依赖: mem_comap_iff
-/
theorem mem_comap {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m in u)
    {s : Set α} : s in u.comap inj large ↔ m '' s in u :=
  mem_comap_iff inj large

@[simp, norm_cast]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m in u)
  proof: rfl

@[simp]
nonrec theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α -> α) := injective_id)
    (h₁ : range id in f := (by rw [range_id]; exact univ_mem)) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id

@[simp]
nonrec theorem comap_comap (f : Ultrafilter γ) {m : α -> β} {n : β -> γ}

中文:
定理 coe_comap
  条件: {m : α -> β} (u : Ultrafilter β) (inj : 单射 m) (large : 集合.range m in u)
  证明: rfl

@[simp]
nonrec theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α -> α) := injective_id)
    (h₁ : range id in f := (by rw [range_id]; exact univ_mem)) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id

@[simp]
nonrec theorem comap_comap (f : Ultrafilter γ) {m : α -> β} {n : β -> γ}
-/
theorem coe_comap {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m in u) :
    (u.comap inj large : Filter α) = Filter.comap m u :=
  rfl

@[simp]
nonrec theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α -> α) := injective_id)
    (h₁ : range id in f := (by rw [range_id]; exact univ_mem)) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id

@[simp]
nonrec theorem comap_comap (f : Ultrafilter γ) {m : α -> β} {n : β -> γ} (inj₀ : Injective n)
    (large₀ : range n in f) (inj₁ : Injective m) (large₁ : range m in f.comap inj₀ large₀)
    (inj₂ : Injective (n ∘ m) := inj₀.comp inj₁)
    (large₂ : range (n ∘ m) in f :=
      (by rw [range_comp]; exact image_mem_of_mem_comap large₀ large₁)) :
    (f.comap inj₀ large₀).comap inj₁ large₁ = f.comap inj₂ large₂ :=
  coe_injective comap_comap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pure Ultrafilter
  body: ⟨fun a => ofComplNotMemIff (pure a) fun s => by simp⟩

@[simp]

中文:
实例 :
  签名: Pure Ultrafilter
  定义体: ⟨fun a => ofComplNotMemIff (pure a) fun s => by simp⟩

@[simp]

Depends on / 依赖: ofComplNotMemIff
-/
instance : Pure Ultrafilter :=
  ⟨fun a => ofComplNotMemIff (pure a) fun s => by simp⟩

@[simp]
/--
theorem `mem_pure` / 定理 `mem_pure`

English:
theorem mem_pure
  given: {a : α} {s : Set α}
  statement: s in (pure a : Ultrafilter α) ↔ a in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_pure
  条件: {a : α} {s : 集合 α}
  结论: s in (pure a : Ultrafilter α) ↔ a in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_pure {a : α} {s : Set α} : s in (pure a : Ultrafilter α) ↔ a in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_pure` / 定理 `coe_pure`

English:
theorem coe_pure
  given: (a : α)
  statement: ↑(pure a : Ultrafilter α) = (pure a : Filter α)
  proof: rfl

@[simp]

中文:
定理 coe_pure
  条件: (a : α)
  结论: ↑(pure a : Ultrafilter α) = (pure a : 滤子 α)
  证明: rfl

@[simp]
-/
theorem coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pure a : Filter α) :=
  rfl

@[simp]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (m : α -> β) (a : α)
  statement: map m (pure a) = pure (m a)
  proof: rfl

@[simp]

中文:
定理 map_pure
  条件: (m : α -> β) (a : α)
  结论: map m (pure a) = pure (m a)
  证明: rfl

@[simp]
-/
theorem map_pure (m : α -> β) (a : α) : map m (pure a) = pure (m a) :=
  rfl

@[simp]
/--
theorem `comap_pure` / 定理 `comap_pure`

English:
theorem comap_pure
  given: {m : α -> β} (a : α) (inj : Injective m) (large)
  proof: coe_injective
Filter.comap_pure.trans by
      rw [coe_pure]; rw [← principal_singleton]; rw [← image_singleton]; rw [preimage_image_eq _ inj]

中文:
定理 comap_pure
  条件: {m : α -> β} (a : α) (inj : 单射 m) (large)
  证明: coe_injective
Filter.comap_pure.trans by
      rw [coe_pure]; rw [← principal_singleton]; rw [← image_singleton]; rw [preimage_image_eq _ inj]

Depends on / 依赖: Filter, Filter.comap_pure.trans, coe_injective, coe_pure, comap_pure, image_singleton, preimage_image_eq, principal_singleton
-/
theorem comap_pure {m : α -> β} (a : α) (inj : Injective m) (large) :
    comap (pure <| m a) inj large = pure a :=
coe_injective
Filter.comap_pure.trans by
      rw [coe_pure]; rw [← principal_singleton]; rw [← image_singleton]; rw [preimage_image_eq _ inj]

/--
theorem `pure_injective` / 定理 `pure_injective`

English:
theorem pure_injective
  statement: Injective (pure : α -> Ultrafilter α)
  proof: fun _ _ h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h :)

中文:
定理 pure_injective
  结论: 单射 (pure : α -> Ultrafilter α)
  证明: fun _ _ h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h :)
-/
theorem pure_injective : Injective (pure : α -> Ultrafilter α) := fun _ _ h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Ultrafilter α)
  body: ⟨pure default⟩

中文:
实例 [可居
  签名: α] : 可居 (Ultrafilter α)
  定义体: ⟨pure default⟩
-/
instance [Inhabited α] : Inhabited (Ultrafilter α) :=
  ⟨pure default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (Ultrafilter α)
  body: Nonempty.map pure inferInstance

中文:
实例 [非空
  签名: α] : 非空 (Ultrafilter α)
  定义体: Nonempty.map pure inferInstance

Depends on / 依赖: Nonempty, Nonempty.map
-/
instance [Nonempty α] : Nonempty (Ultrafilter α) :=
  Nonempty.map pure inferInstance

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (f : Ultrafilter α) (m : α -> Ultrafilter β)
  body: ofComplNotMemIff (Filter.bind ↑f fun x => ↑(m x)) fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_notMem, compl_ofPred, compl_compl]

中文:
定义 bind
  签名: (f : Ultrafilter α) (m : α -> Ultrafilter β)
  定义体: ofComplNotMemIff (Filter.bind ↑f fun x => ↑(m x)) fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_notMem, compl_ofPred, compl_compl]

Depends on / 依赖: Filter, Filter.bind, compl_compl, compl_mem_iff_notMem, compl_ofPred, mem_bind, mem_coe, ofComplNotMemIff
-/
def bind (f : Ultrafilter α) (m : α -> Ultrafilter β) : Ultrafilter β :=
  ofComplNotMemIff (Filter.bind ↑f fun x => ↑(m x)) fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_notMem, compl_ofPred, compl_compl]

/--
Instance `instBind` / 实例 `instBind`

English:
instance instBind
  signature: : Bind Ultrafilter
  body: ⟨@Ultrafilter.bind⟩

中文:
实例 instBind
  签名: : Bind Ultrafilter
  定义体: ⟨@Ultrafilter.bind⟩

Depends on / 依赖: Ultrafilter, Ultrafilter.bind
-/
instance instBind : Bind Ultrafilter :=
  ⟨@Ultrafilter.bind⟩

/--
Instance `functor` / 实例 `functor`

English:
instance functor
  signature: : Functor Ultrafilter where map
  body: @Ultrafilter.map

中文:
实例 functor
  签名: : 函子 Ultrafilter where map
  定义体: @Ultrafilter.map

Depends on / 依赖: Ultrafilter, Ultrafilter.map
-/
instance functor : Functor Ultrafilter where map := @Ultrafilter.map

/--
Instance `monad` / 实例 `monad`

English:
instance monad
  signature: : Monad Ultrafilter where map
  body: @Ultrafilter.map

中文:
实例 monad
  签名: : 单子 Ultrafilter where map
  定义体: @Ultrafilter.map

Depends on / 依赖: Ultrafilter, Ultrafilter.map
-/
instance monad : Monad Ultrafilter where map := @Ultrafilter.map

section

attribute [local instance] Filter.monad Filter.lawfulMonad

/--
Instance `lawfulMonad` / 实例 `lawfulMonad`

English:
instance lawfulMonad
  signature: : LawfulMonad Ultrafilter where
  body: coe_injective (id_map f.toFilter)
  pure_bind a f := coe_injective (Filter.pure_bind a ((Ultrafilter.toFilter) ∘ f))
  bind_assoc _ _ _ := coe_injective (filter_eq rfl)
  bind_pure_comp f x := coe_injective (bind_pure_comp f x.1)
  map_const := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  

中文:
实例 lawfulMonad
  签名: : 合法单子 Ultrafilter where
  定义体: coe_injective (id_map f.toFilter)
  pure_bind a f := coe_injective (Filter.pure_bind a ((Ultrafilter.toFilter) ∘ f))
  bind_assoc _ _ _ := coe_injective (filter_eq rfl)
  bind_pure_comp f x := coe_injective (bind_pure_comp f x.1)
  map_const := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  

Depends on / 依赖: coe_injective, f.toFilter, id_map, toFilter
-/
instance lawfulMonad : LawfulMonad Ultrafilter where
  id_map f := coe_injective (id_map f.toFilter)
  pure_bind a f := coe_injective (Filter.pure_bind a ((Ultrafilter.toFilter) ∘ f))
  bind_assoc _ _ _ := coe_injective (filter_eq rfl)
  bind_pure_comp f x := coe_injective (bind_pure_comp f x.1)
  map_const := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_map _ _ := rfl

end

/--
theorem `exists_le` / 定理 `exists_le`

English:
theorem exists_le
  given: (f : Filter α) [h : NeBot f]
  statement: exists u : Ultrafilter α, ↑u <= f
  proof: let ⟨u, hu, huf⟩ := (eq_bot_or_exists_atom_le f).resolve_left h.ne
  ⟨ofAtom u hu, huf⟩

alias _root_.Filter.exists_ultrafilter_le := exists_le

中文:
定理 存在_le
  条件: (f : 滤子 α) [h : NeBot f]
  结论: 存在 u : Ultrafilter α, ↑u <= f
  证明: let ⟨u, hu, huf⟩ := (eq_bot_or_exists_atom_le f).resolve_left h.ne
  ⟨ofAtom u hu, huf⟩

alias _root_.Filter.exists_ultrafilter_le := exists_le

Depends on / 依赖: eq_bot_or_exists_atom_le, h.ne, ofAtom, resolve_left
-/
theorem exists_le (f : Filter α) [h : NeBot f] : exists u : Ultrafilter α, ↑u <= f :=
  let ⟨u, hu, huf⟩ := (eq_bot_or_exists_atom_le f).resolve_left h.ne
  ⟨ofAtom u hu, huf⟩

alias _root_.Filter.exists_ultrafilter_le := exists_le

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (f : Filter α) [NeBot f]
  body: Classical.choose (exists_le f)

中文:
定义 of
  签名: (f : 滤子 α) [NeBot f]
  定义体: Classical.choose (exists_le f)

Depends on / 依赖: Classical, Classical.choose, exists_le
-/
noncomputable def of (f : Filter α) [NeBot f] : Ultrafilter α :=
  Classical.choose (exists_le f)

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: (f : Filter α) [NeBot f]
  statement: ↑(of f) <= f
  proof: Classical.choose_spec (exists_le f)

中文:
定理 of_le
  条件: (f : 滤子 α) [NeBot f]
  结论: ↑(of f) <= f
  证明: Classical.choose_spec (exists_le f)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_le
-/
theorem of_le (f : Filter α) [NeBot f] : ↑(of f) <= f :=
  Classical.choose_spec (exists_le f)

/--
theorem `of_coe` / 定理 `of_coe`

English:
theorem of_coe
  given: (f : Ultrafilter α)
  statement: of ↑f = f
  proof: coe_inj.1 f.unique (of_le f.toFilter)

中文:
定理 of_coe
  条件: (f : Ultrafilter α)
  结论: of ↑f = f
  证明: coe_inj.1 f.unique (of_le f.toFilter)

Depends on / 依赖: coe_inj, f.toFilter, f.unique, of_le, toFilter, unique
-/
theorem of_coe (f : Ultrafilter α) : of ↑f = f :=
coe_inj.1 f.unique (of_le f.toFilter)

end Ultrafilter

namespace Filter

variable {f : Filter α} {s : Set α} {a : α}

open Ultrafilter

/--
theorem `isAtom_pure` / 定理 `isAtom_pure`

English:
theorem isAtom_pure
  statement: IsAtom (pure a : Filter α)
  proof: (pure a : Ultrafilter α).isAtom

中文:
定理 isAtom_pure
  结论: IsAtom (pure a : 滤子 α)
  证明: (pure a : Ultrafilter α).isAtom

Depends on / 依赖: Ultrafilter, isAtom
-/
theorem isAtom_pure : IsAtom (pure a : Filter α) :=
  (pure a : Ultrafilter α).isAtom

/--
theorem `NeBot.le_pure_iff` / 定理 `NeBot.le_pure_iff`

English:
theorem NeBot.le_pure_iff
  given: (hf : f.NeBot)
  statement: f <= pure a ↔ f = pure a
  proof: ⟨Ultrafilter.unique (pure a), le_of_eq⟩

中文:
定理 NeBot.le_pure_iff
  条件: (hf : f.NeBot)
  结论: f <= pure a ↔ f = pure a
  证明: ⟨Ultrafilter.unique (pure a), le_of_eq⟩
-/
protected theorem NeBot.le_pure_iff (hf : f.NeBot) : f <= pure a ↔ f = pure a :=
  ⟨Ultrafilter.unique (pure a), le_of_eq⟩

/--
theorem `NeBot.eq_pure_iff` / 定理 `NeBot.eq_pure_iff`

English:
theorem NeBot.eq_pure_iff
  given: (hf : f.NeBot) {x : α}
  proof: by
  rw [← hf.le_pure_iff]; rw [le_pure_iff]

@[simp]

中文:
定理 NeBot.eq_pure_iff
  条件: (hf : f.NeBot) {x : α}
  证明: by
  rw [← hf.le_pure_iff]; rw [le_pure_iff]

@[simp]
-/
protected theorem NeBot.eq_pure_iff (hf : f.NeBot) {x : α} :
    f = pure x ↔ {x} in f := by
  rw [← hf.le_pure_iff]; rw [le_pure_iff]

@[simp]
/--
theorem `lt_pure_iff` / 定理 `lt_pure_iff`

English:
theorem lt_pure_iff
  statement: f < pure a ↔ f = ⊥
  proof: isAtom_pure.lt_iff

中文:
定理 lt_pure_iff
  结论: f < pure a ↔ f = ⊥
  证明: isAtom_pure.lt_iff

Depends on / 依赖: isAtom_pure, isAtom_pure.lt_iff, lt_iff
-/
theorem lt_pure_iff : f < pure a ↔ f = ⊥ :=
  isAtom_pure.lt_iff

/--
theorem `le_pure_iff'` / 定理 `le_pure_iff'`

English:
theorem le_pure_iff'
  statement: f <= pure a ↔ f = ⊥ ∨ f = pure a
  proof: isAtom_pure.le_iff

@[simp]

中文:
定理 le_pure_iff'
  结论: f <= pure a ↔ f = ⊥ ∨ f = pure a
  证明: isAtom_pure.le_iff

@[simp]

Depends on / 依赖: isAtom_pure, isAtom_pure.le_iff, le_iff
-/
theorem le_pure_iff' : f <= pure a ↔ f = ⊥ ∨ f = pure a :=
  isAtom_pure.le_iff

@[simp]
/--
theorem `Iic_pure` / 定理 `Iic_pure`

English:
theorem Iic_pure
  given: (a : α)
  statement: Iic (pure a : Filter α) = {⊥, pure a}
  proof: isAtom_pure.Iic_eq

中文:
定理 Iic_pure
  条件: (a : α)
  结论: 左无界右闭区间 (pure a : 滤子 α) = {⊥, pure a}
  证明: isAtom_pure.Iic_eq

Depends on / 依赖: Iic_eq, isAtom_pure, isAtom_pure.Iic_eq
-/
theorem Iic_pure (a : α) : Iic (pure a : Filter α) = {⊥, pure a} :=
  isAtom_pure.Iic_eq

/--
theorem `mem_iff_ultrafilter` / 定理 `mem_iff_ultrafilter`

English:
theorem mem_iff_ultrafilter
  statement: s in f ↔ forall g : Ultrafilter α, ↑g <= f -> s in g
  proof: by
  refine ⟨fun hf g hg => hg hf, fun H => by_contra fun hf => ?_⟩
  set g : Filter (sᶜ : Set α) := comap (↑) f
  have : NeBot g := comap_neBot_iff_compl_range.2 (by simpa [compl_ofPred])
  simpa using H ((of g).map (↑)) (map_le_iff_le_comap.mpr (of_le g))

中文:
定理 mem_iff_ultrafilter
  结论: s in f ↔ 对任意 g : Ultrafilter α, ↑g <= f -> s in g
  证明: by
  refine ⟨fun hf g hg => hg hf, fun H => by_contra fun hf => ?_⟩
  set g : Filter (sᶜ : Set α) := comap (↑) f
  have : NeBot g := comap_neBot_iff_compl_range.2 (by simpa [compl_ofPred])
  simpa using H ((of g).map (↑)) (map_le_iff_le_comap.mpr (of_le g))

Depends on / 依赖: Filter, comap_neBot_iff_compl_range, compl_ofPred, map_le_iff_le_comap, map_le_iff_le_comap.mpr, of_le
-/
theorem mem_iff_ultrafilter : s in f ↔ forall g : Ultrafilter α, ↑g <= f -> s in g := by
  refine ⟨fun hf g hg => hg hf, fun H => by_contra fun hf => ?_⟩
  set g : Filter (sᶜ : Set α) := comap (↑) f
  have : NeBot g := comap_neBot_iff_compl_range.2 (by simpa [compl_ofPred])
  simpa using H ((of g).map (↑)) (map_le_iff_le_comap.mpr (of_le g))

/--
theorem `le_iff_ultrafilter` / 定理 `le_iff_ultrafilter`

English:
theorem le_iff_ultrafilter
  given: {f₁ f₂ : Filter α}
  statement: f₁ <= f₂ ↔ forall g : Ultrafilter α, ↑g <= f₁ -> ↑g <= f₂
  proof: ⟨fun h _ h₁ => h₁.trans h, fun h _ hs => mem_iff_ultrafilter.2 fun g hg => h g hg hs⟩

中文:
定理 le_iff_ultrafilter
  条件: {f₁ f₂ : 滤子 α}
  结论: f₁ <= f₂ ↔ 对任意 g : Ultrafilter α, ↑g <= f₁ -> ↑g <= f₂
  证明: ⟨fun h _ h₁ => h₁.trans h, fun h _ hs => mem_iff_ultrafilter.2 fun g hg => h g hg hs⟩

Depends on / 依赖: mem_iff_ultrafilter
-/
theorem le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ <= f₂ ↔ forall g : Ultrafilter α, ↑g <= f₁ -> ↑g <= f₂ :=
  ⟨fun h _ h₁ => h₁.trans h, fun h _ hs => mem_iff_ultrafilter.2 fun g hg => h g hg hs⟩

/--
theorem `iSup_ultrafilter_le_eq` / 定理 `iSup_ultrafilter_le_eq`

English:
theorem iSup_ultrafilter_le_eq
  given: (f : Filter α)
  proof: eq_of_forall_ge_iff fun f' => by simp only [iSup_le_iff, ← le_iff_ultrafilter]

中文:
定理 iSup_ultrafilter_le_eq
  条件: (f : 滤子 α)
  证明: eq_of_forall_ge_iff fun f' => by simp only [iSup_le_iff, ← le_iff_ultrafilter]

Depends on / 依赖: eq_of_forall_ge_iff, iSup_le_iff, le_iff_ultrafilter
-/
theorem iSup_ultrafilter_le_eq (f : Filter α) :
    ⨆ (g : Ultrafilter α) (_ : g <= f), (g : Filter α) = f :=
  eq_of_forall_ge_iff fun f' => by simp only [iSup_le_iff, ← le_iff_ultrafilter]

/--
theorem `exists_ultrafilter_iff` / 定理 `exists_ultrafilter_iff`

English:
theorem exists_ultrafilter_iff
  given: {f : Filter α}
  statement: (exists u : Ultrafilter α, ↑u <= f) ↔ NeBot f
  proof: ⟨fun ⟨_, uf⟩ => neBot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩

中文:
定理 存在_ultrafilter_iff
  条件: {f : 滤子 α}
  结论: (存在 u : Ultrafilter α, ↑u <= f) ↔ NeBot f
  证明: ⟨fun ⟨_, uf⟩ => neBot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩

Depends on / 依赖: exists_ultrafilter_le, neBot_of_le
-/
theorem exists_ultrafilter_iff {f : Filter α} : (exists u : Ultrafilter α, ↑u <= f) ↔ NeBot f :=
  ⟨fun ⟨_, uf⟩ => neBot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩

/--
theorem `forall_neBot_le_iff` / 定理 `forall_neBot_le_iff`

English:
theorem forall_neBot_le_iff
  given: {g : Filter α} {p : Filter α -> Prop} (hp : Monotone p)
  proof: by
  refine ⟨fun H f hf => H f f.neBot hf, ?_⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))

中文:
定理 对任意_neBot_le_iff
  条件: {g : 滤子 α} {p : 滤子 α -> 命题} (hp : 递增 p)
  证明: by
  refine ⟨fun H f hf => H f f.neBot hf, ?_⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))

Depends on / 依赖: f.neBot, of_le
-/
theorem forall_neBot_le_iff {g : Filter α} {p : Filter α -> Prop} (hp : Monotone p) :
    (forall f : Filter α, NeBot f -> f <= g -> p f) ↔ forall f : Ultrafilter α, ↑f <= g -> p f := by
  refine ⟨fun H f hf => H f f.neBot hf, ?_⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))

end Filter

namespace Ultrafilter

variable {m : α -> β} {s : Set α} {g : Ultrafilter β}

/--
theorem `comap_inf_principal_neBot_of_image_mem` / 定理 `comap_inf_principal_neBot_of_image_mem`

English:
theorem comap_inf_principal_neBot_of_image_mem
  given: (h : m '' s in g)
  statement: (Filter.comap m g ⊓ 𝓟 s).NeBot
  proof: Filter.comap_inf_principal_neBot_of_image_mem g.neBot h

中文:
定理 comap_inf_principal_neBot_of_image_mem
  条件: (h : m '' s in g)
  结论: (滤子.comap m g ⊓ 𝓟 s).NeBot
  证明: Filter.comap_inf_principal_neBot_of_image_mem g.neBot h

Depends on / 依赖: Filter, Filter.comap_inf_principal_neBot_of_image_mem, comap_inf_principal_neBot_of_image_mem, g.neBot
-/
theorem comap_inf_principal_neBot_of_image_mem (h : m '' s in g) : (Filter.comap m g ⊓ 𝓟 s).NeBot :=
  Filter.comap_inf_principal_neBot_of_image_mem g.neBot h

/--
Definition of `ofComapInfPrincipal` / `ofComapInfPrincipal` 的定义

English:
definition ofComapInfPrincipal
  signature: (h : m '' s in g)
  body: @of _ (Filter.comap m g ⊓ 𝓟 s) (comap_inf_principal_neBot_of_image_mem h)

中文:
定义 ofComapInfPrincipal
  签名: (h : m '' s in g)
  定义体: @of _ (Filter.comap m g ⊓ 𝓟 s) (comap_inf_principal_neBot_of_image_mem h)

Depends on / 依赖: Filter, Filter.comap, comap_inf_principal_neBot_of_image_mem
-/
noncomputable def ofComapInfPrincipal (h : m '' s in g) : Ultrafilter α :=
  @of _ (Filter.comap m g ⊓ 𝓟 s) (comap_inf_principal_neBot_of_image_mem h)

/--
theorem `ofComapInfPrincipal_mem` / 定理 `ofComapInfPrincipal_mem`

English:
theorem ofComapInfPrincipal_mem
  given: (h : m '' s in g)
  statement: s in ofComapInfPrincipal h
  proof: by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  have : s in f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this

中文:
定理 ofComapInfPrincipal_mem
  条件: (h : m '' s in g)
  结论: s in ofComapInfPrincipal h
  证明: by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  have : s in f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this

Depends on / 依赖: Filter, Filter.comap, comap_inf_principal_neBot_of_image_mem, f.NeBot, le_def, le_def.mp, mem_inf_of_right, mem_principal_self, of_le
-/
theorem ofComapInfPrincipal_mem (h : m '' s in g) : s in ofComapInfPrincipal h := by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  have : s in f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this

/--
theorem `ofComapInfPrincipal_eq_of_map` / 定理 `ofComapInfPrincipal_eq_of_map`

English:
theorem ofComapInfPrincipal_eq_of_map
  given: (h : m '' s in g)
  statement: (ofComapInfPrincipal h).map m = g
  proof: by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  apply eq_of_le
  calc
    Filter.map m (of f) <= Filter.map m f := map_mono (of_le _)
    _ <= (Filter.map m <| Filter.comap m g) ⊓ Filter.map m (𝓟 s) := map_inf_le
    _ = (Filter.map m <| Filter.com

中文:
定理 ofComapInfPrincipal_eq_of_map
  条件: (h : m '' s in g)
  结论: (ofComapInfPrincipal h).map m = g
  证明: by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  apply eq_of_le
  calc
    Filter.map m (of f) <= Filter.map m f := map_mono (of_le _)
    _ <= (Filter.map m <| Filter.comap m g) ⊓ Filter.map m (𝓟 s) := map_inf_le
    _ = (Filter.map m <| Filter.com

Depends on / 依赖: Filter, Filter.comap, Filter.map, comap_inf_principal_neBot_of_image_mem, eq_of_le, f.NeBot, inf_le_inf_right, inf_of_le_left, le_principal_iff, le_principal_iff.mpr, map_comap_le, map_inf_le, map_mono, map_principal, of_le
-/
theorem ofComapInfPrincipal_eq_of_map (h : m '' s in g) : (ofComapInfPrincipal h).map m = g := by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  apply eq_of_le
  calc
    Filter.map m (of f) <= Filter.map m f := map_mono (of_le _)
    _ <= (Filter.map m <| Filter.comap m g) ⊓ Filter.map m (𝓟 s) := map_inf_le
    _ = (Filter.map m <| Filter.comap m g) ⊓ (𝓟 <| m '' s) := by rw [map_principal]
    _ <= ↑g ⊓ (𝓟 <| m '' s) := inf_le_inf_right _ map_comap_le
    _ = ↑g := inf_of_le_left (le_principal_iff.mpr h)

/--
theorem `eq_of_le_pure` / 定理 `eq_of_le_pure`

English:
theorem eq_of_le_pure
  statement: {X : Type _} {α : Filter X} (hα : α.NeBot) {x y : X}
  proof: Filter.pure_injective (hα.le_pure_iff.mp hx ▸ hα.le_pure_iff.mp hy)

中文:
定理 eq_of_le_pure
  结论: {X : 类型 _} {α : 滤子 X} (hα : α.NeBot) {x y : X}
  证明: Filter.pure_injective (hα.le_pure_iff.mp hx ▸ hα.le_pure_iff.mp hy)

Depends on / 依赖: Filter, Filter.pure_injective, le_pure_iff, le_pure_iff.mp, pure_injective
-/
theorem eq_of_le_pure {X : Type _} {α : Filter X} (hα : α.NeBot) {x y : X}
    (hx : α <= pure x) (hy : α <= pure y) : x = y :=
  Filter.pure_injective (hα.le_pure_iff.mp hx ▸ hα.le_pure_iff.mp hy)

end Ultrafilter
