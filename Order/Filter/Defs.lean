/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Order.SetNotation
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Bounds.Defs

/-!
# Definitions about filters

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. Filters are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

* `Filter` : filters on a set;
* `Filter.principal`, `𝓟 s` : filter of all sets containing a given set;
* `Filter.map`, `Filter.comap` : operations on filters;
* `Filter.Tendsto` : limit with respect to filters;
* `Filter.Eventually` : `f.Eventually p` means `{x | p x} ∈ f`;
* `Filter.Frequently` : `f.Frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` :
  a tactic that takes a list of proofs `hᵢ : sᵢ ∈ f`,
  and replaces a goal `s ∈ f` with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `Filter.NeBot f` : a utility class stating that `f` is a non-trivial filter.
* `Filter.IsBounded r f`: the filter `f` is eventually bounded w.r.t. the relation `r`,
  i.e. eventually, it is bounded by some uniform bound.
  `r` will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.
* `Filter.IsCobounded r f` states that the filter `f` does not tend to infinity w.r.t. `r`.
  This is also called frequently bounded. Will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.

## Notation

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## Implementation Notes

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`,
which we do *not* require.
This gives `Filter X` better formal properties,
in particular a bottom element `⊥` for its lattice structure,
at the cost of including the assumption `[NeBot f]` in a number of lemmas and definitions.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
-/

@[expose] public section

assert_not_exists RelIso

open Set

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
@[to_dual_dont_translate]
/--
Definition of `Filter` / `Filter` 的定义

English:
structure Filter
  parameters: (α : Type*)
  axioms and operations (4):
    - sets : Set (Set α)
    - univ_sets : Set.univ in sets
    - sets_of_superset({x y}) : x in sets -> x subseteq y -> y in sets
    - inter_sets({x y}) : x in sets -> y in sets -> x inter y in sets

中文:
结构 Filter
  参数: (α : 类型)
  公理与运算 (4 个):
    - sets : Set (Set α)
    - univ_sets : Set.univ in sets
    - sets_of_superset({x y}) : x in sets -> x subseteq y -> y in sets
    - inter_sets({x y}) : x in sets -> y in sets -> x inter y in sets
-/
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ in sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x in sets -> x subseteq y -> y in sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x in sets -> y in sets -> x inter y in sets

namespace Filter

variable {α β : Type*} {f g : Filter α} {s t : Set α}

/--
theorem `filter_eq` / 定理 `filter_eq`

English:
theorem filter_eq
  statement: forall {f g : Filter α}, f.sets = g.sets -> f = g

中文:
定理 filter_eq
  结论: 对任意 {f g : Filter α}, f.sets = g.sets -> f = g
-/
theorem filter_eq : forall {f g : Filter α}, f.sets = g.sets -> f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/--
Instance `instMembership` / 实例 `instMembership`

English:
instance instMembership
  signature: : Membership (Set α) (Filter α)
  body: ⟨fun F U => U in F.sets⟩

@[ext]

中文:
实例 instMembership
  签名: : Membership (Set α) (Filter α)
  定义体: ⟨fun F U => U in F.sets⟩

@[ext]

Depends on / 依赖: F.sets
-/
instance instMembership : Membership (Set α) (Filter α) := ⟨fun F U => U in F.sets⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall s, s in f ↔ s in g)
  statement: f = g
  proof: filter_eq Set.ext h

@[simp]

中文:
定理 ext
  条件: (h : 对任意 s, s in f ↔ s in g)
  结论: f = g
  证明: filter_eq Set.ext h

@[simp]
-/
protected theorem ext (h : forall s, s in f ↔ s in g) : f = g := filter_eq Set.ext h

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {t : Set (Set α)} {h₁ h₂ h₃}
  statement: s in mk t h₁ h₂ h₃ ↔ s in t
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk
  条件: {t : Set (Set α)} {h₁ h₂ h₃}
  结论: s in mk t h₁ h₂ h₃ ↔ s in t
  证明: Iff.rfl

@[simp]
-/
protected theorem mem_mk {t : Set (Set α)} {h₁ h₂ h₃} : s in mk t h₁ h₂ h₃ ↔ s in t :=
  Iff.rfl

@[simp]
/--
theorem `mem_sets` / 定理 `mem_sets`

English:
theorem mem_sets
  statement: s in f.sets ↔ s in f
  proof: Iff.rfl

@[simp]

中文:
定理 mem_sets
  结论: s in f.sets ↔ s in f
  证明: Iff.rfl

@[simp]
-/
protected theorem mem_sets : s in f.sets ↔ s in f :=
  Iff.rfl

@[simp]
/--
theorem `univ_mem` / 定理 `univ_mem`

English:
theorem univ_mem
  statement: univ in f
  proof: f.univ_sets

@[gcongr]

中文:
定理 univ_mem
  结论: univ in f
  证明: f.univ_sets

@[gcongr]

Depends on / 依赖: f.univ_sets, univ_sets
-/
theorem univ_mem : univ in f :=
  f.univ_sets

@[gcongr]
/--
theorem `mem_of_superset` / 定理 `mem_of_superset`

English:
theorem mem_of_superset
  given: {x y : Set α} (hx : x in f) (hxy : x subseteq y)
  statement: y in f
  proof: f.sets_of_superset hx hxy

中文:
定理 mem_of_superset
  条件: {x y : Set α} (hx : x in f) (hxy : x subseteq y)
  结论: y in f
  证明: f.sets_of_superset hx hxy

Depends on / 依赖: f.sets_of_superset, sets_of_superset
-/
theorem mem_of_superset {x y : Set α} (hx : x in f) (hxy : x subseteq y) : y in f :=
  f.sets_of_superset hx hxy

/--
theorem `univ_mem'` / 定理 `univ_mem'`

English:
theorem univ_mem'
  given: (h : forall a, a in s)
  statement: s in f
  proof: mem_of_superset univ_mem fun x _ => h x

中文:
定理 univ_mem'
  条件: (h : 对任意 a, a in s)
  结论: s in f
  证明: mem_of_superset univ_mem fun x _ => h x

Depends on / 依赖: mem_of_superset, univ_mem
-/
theorem univ_mem' (h : forall a, a in s) : s in f :=
  mem_of_superset univ_mem fun x _ => h x

/--
theorem `inter_mem` / 定理 `inter_mem`

English:
theorem inter_mem
  given: (hs : s in f) (ht : t in f)
  statement: s inter t in f
  proof: f.inter_sets hs ht

中文:
定理 inter_mem
  条件: (hs : s in f) (ht : t in f)
  结论: s inter t in f
  证明: f.inter_sets hs ht

Depends on / 依赖: f.inter_sets, inter_sets
-/
theorem inter_mem (hs : s in f) (ht : t in f) : s inter t in f :=
  f.inter_sets hs ht

/--
theorem `mp_mem` / 定理 `mp_mem`

English:
theorem mp_mem
  given: (hs : s in f) (h : { x | x in s -> x in t } in f)
  statement: t in f
  proof: mem_of_superset (inter_mem hs h) fun _ ⟨h₁, h₂⟩ => h₂ h₁

中文:
定理 mp_mem
  条件: (hs : s in f) (h : { x | x in s -> x in t } in f)
  结论: t in f
  证明: mem_of_superset (inter_mem hs h) fun _ ⟨h₁, h₂⟩ => h₂ h₁

Depends on / 依赖: inter_mem, mem_of_superset
-/
theorem mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) : t in f :=
  mem_of_superset (inter_mem hs h) fun _ ⟨h₁, h₂⟩ => h₂ h₁

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : Filter α) (S : Set (Set α)) (hmem : forall s, s in S ↔ s in f)
  body: S
  univ_sets := (hmem _).2 univ_mem
sets_of_superset h hsub := (hmem _).2 mem_of_superset ((hmem _).1 h) hsub
inter_sets h₁ h₂ := (hmem _).2 inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)

中文:
定义 copy
  签名: (f : Filter α) (S : Set (Set α)) (hmem : 对任意 s, s in S ↔ s in f)
  定义体: S
  univ_sets := (hmem _).2 univ_mem
sets_of_superset h hsub := (hmem _).2 mem_of_superset ((hmem _).1 h) hsub
inter_sets h₁ h₂ := (hmem _).2 inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)
-/
protected def copy (f : Filter α) (S : Set (Set α)) (hmem : forall s, s in S ↔ s in f) : Filter α where
  sets := S
  univ_sets := (hmem _).2 univ_mem
sets_of_superset h hsub := (hmem _).2 mem_of_superset ((hmem _).1 h) hsub
inter_sets h₁ h₂ := (hmem _).2 inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)

/--
theorem `mem_copy` / 定理 `mem_copy`

English:
theorem mem_copy
  given: {S hmem}
  statement: s in f.copy S hmem ↔ s in S
  proof: Iff.rfl

中文:
定理 mem_copy
  条件: {S hmem}
  结论: s in f.copy S hmem ↔ s in S
  证明: Iff.rfl
-/
@[simp] theorem mem_copy {S hmem} : s in f.copy S hmem ↔ s in S := Iff.rfl

/--
Definition of `comk` / `comk` 的定义

English:
definition comk
  signature: (p : Set α -> Prop) (he : p ∅) (hmono : forall t, p t -> forall s subseteq t, p s)
  body: {t | p tᶜ}
  univ_sets := by simpa
  sets_of_superset := fun ht₁ ht => hmono _ ht₁ _ (compl_subset_compl.2 ht)
  inter_sets := fun ht₁ ht₂ => by simp [compl_inter, hunion _ ht₁ _ ht₂]

@[simp]

中文:
定义 comk
  签名: (p : Set α -> 命题) (he : p ∅) (hmono : 对任意 t, p t -> 对任意 s subseteq t, p s)
  定义体: {t | p tᶜ}
  univ_sets := by simpa
  sets_of_superset := fun ht₁ ht => hmono _ ht₁ _ (compl_subset_compl.2 ht)
  inter_sets := fun ht₁ ht₂ => by simp [compl_inter, hunion _ ht₁ _ ht₂]

@[simp]
-/
def comk (p : Set α -> Prop) (he : p ∅) (hmono : forall t, p t -> forall s subseteq t, p s)
    (hunion : forall s, p s -> forall t, p t -> p (s union t)) : Filter α where
  sets := {t | p tᶜ}
  univ_sets := by simpa
  sets_of_superset := fun ht₁ ht => hmono _ ht₁ _ (compl_subset_compl.2 ht)
  inter_sets := fun ht₁ ht₂ => by simp [compl_inter, hunion _ ht₁ _ ht₂]

@[simp]
/--
lemma `mem_comk` / 引理 `mem_comk`

English:
lemma mem_comk
  given: {p : Set α -> Prop} {he hmono hunion s}
  proof: .rfl

中文:
引理 mem_comk
  条件: {p : Set α -> 命题} {he hmono hunion s}
  证明: .rfl
-/
lemma mem_comk {p : Set α -> Prop} {he hmono hunion s} :
    s in comk p he hmono hunion ↔ p sᶜ :=
  .rfl

/--
Definition of `principal` / `principal` 的定义

English:
definition principal
  signature: (s : Set α)
  body: { t | s subseteq t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

中文:
定义 principal
  签名: (s : Set α)
  定义体: { t | s subseteq t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

Depends on / 依赖: subseteq
-/
def principal (s : Set α) : Filter α where
  sets := { t | s subseteq t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

/--
theorem `mem_principal` / 定理 `mem_principal`

English:
theorem mem_principal
  statement: s in 𝓟 t ↔ t subseteq s
  proof: Iff.rfl

中文:
定理 mem_principal
  结论: s in 𝓟 t ↔ t subseteq s
  证明: Iff.rfl
-/
@[simp] theorem mem_principal : s in 𝓟 t ↔ t subseteq s := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pure Filter
  body: .copy (𝓟 {x}) {s | x in s} fun _ => by simp

@[simp]

中文:
实例 :
  签名: Pure Filter
  定义体: .copy (𝓟 {x}) {s | x in s} fun _ => by simp

@[simp]
-/
instance : Pure Filter where
  pure x := .copy (𝓟 {x}) {s | x in s} fun _ => by simp

@[simp]
/--
theorem `mem_pure` / 定理 `mem_pure`

English:
theorem mem_pure
  given: {a : α} {s : Set α}
  statement: s in (pure a : Filter α) ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_pure
  条件: {a : α} {s : Set α}
  结论: s in (pure a : Filter α) ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_pure {a : α} {s : Set α} : s in (pure a : Filter α) ↔ a in s :=
  Iff.rfl

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : Filter α)
  body: ⋂₀ f.sets

中文:
定义 ker
  签名: (f : Filter α)
  定义体: ⋂₀ f.sets

Depends on / 依赖: f.sets
-/
def ker (f : Filter α) : Set α := ⋂₀ f.sets

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: (f : Filter (Filter α))
  body: { s | { t : Filter α | s in t } in f }
  univ_sets := by simp only [mem_ofPred_eq, univ_mem, ofPred_true]
  sets_of_superset hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂

@[simp]

中文:
定义 join
  签名: (f : Filter (Filter α))
  定义体: { s | { t : Filter α | s in t } in f }
  univ_sets := by simp only [mem_ofPred_eq, univ_mem, ofPred_true]
  sets_of_superset hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂

@[simp]

Depends on / 依赖: Filter
-/
def join (f : Filter (Filter α)) : Filter α where
  sets := { s | { t : Filter α | s in t } in f }
  univ_sets := by simp only [mem_ofPred_eq, univ_mem, ofPred_true]
  sets_of_superset hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂

@[simp]
/--
theorem `mem_join` / 定理 `mem_join`

English:
theorem mem_join
  given: {s : Set α} {f : Filter (Filter α)}
  statement: s in join f ↔ { t | s in t } in f
  proof: Iff.rfl

中文:
定理 mem_join
  条件: {s : Set α} {f : Filter (Filter α)}
  结论: s in join f ↔ { t | s in t } in f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_join {s : Set α} {f : Filter (Filter α)} : s in join f ↔ { t | s in t } in f :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Filter α)
  body: forall ⦃U : Set α⦄, U in g -> U in f
le_antisymm a b h₁ h₂ := filter_eq Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

中文:
实例 :
  签名: PartialOrder (Filter α)
  定义体: forall ⦃U : Set α⦄, U in g -> U in f
le_antisymm a b h₁ h₂ := filter_eq Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁
-/
instance : PartialOrder (Filter α) where
  le f g := forall ⦃U : Set α⦄, U in g -> U in f
le_antisymm a b h₁ h₂ := filter_eq Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: f <= g ↔ forall x in g, x in f
  proof: Iff.rfl

中文:
定理 le_def
  结论: f <= g ↔ 对任意 x in g, x in f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def : f <= g ↔ forall x in g, x in f :=
  Iff.rfl

/--
Instance `instSupSet` / 实例 `instSupSet`

English:
instance instSupSet
  signature: : SupSet (Filter α) where
  body: join (𝓟 S)

中文:
实例 instSupSet
  签名: : SupSet (Filter α) where
  定义体: join (𝓟 S)
-/
instance instSupSet : SupSet (Filter α) where
  sSup S := join (𝓟 S)

/--
theorem `mem_sSup` / 定理 `mem_sSup`

English:
theorem mem_sSup
  given: {S : Set (Filter α)}
  statement: s in sSup S ↔ forall f in S, s in f
  proof: .rfl

中文:
定理 mem_sSup
  条件: {S : Set (Filter α)}
  结论: s in sSup S ↔ 对任意 f in S, s in f
  证明: .rfl
-/
@[simp] theorem mem_sSup {S : Set (Filter α)} : s in sSup S ↔ forall f in S, s in f := .rfl

/-- Infimum of a set of filters.
This definition is marked as irreducible
so that Lean doesn't try to unfold it when unifying expressions. -/
@[irreducible]
/--
Definition of `sInf` / `sInf` 的定义

English:
definition sInf
  signature: (s : Set (Filter α))
  body: sSup (lowerBounds s)

中文:
定义 sInf
  签名: (s : Set (Filter α))
  定义体: sSup (lowerBounds s)
-/
protected def sInf (s : Set (Filter α)) : Filter α := sSup (lowerBounds s)

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet (Filter α) where
  body: Filter.sInf

中文:
实例 instInfSet
  签名: : InfSet (Filter α) where
  定义体: Filter.sInf

Depends on / 依赖: Filter, Filter.sInf
-/
instance instInfSet : InfSet (Filter α) where
  sInf := Filter.sInf

/--
theorem `sSup_lowerBounds` / 定理 `sSup_lowerBounds`

English:
theorem sSup_lowerBounds
  given: (s : Set (Filter α))
  statement: sSup (lowerBounds s) = sInf s
  proof: by
  simp [sInf, Filter.sInf]

中文:
定理 sSup_lowerBounds
  条件: (s : Set (Filter α))
  结论: sSup (lowerBounds s) = sInf s
  证明: by
  simp [sInf, Filter.sInf]
-/
protected theorem sSup_lowerBounds (s : Set (Filter α)) : sSup (lowerBounds s) = sInf s := by
  simp [sInf, Filter.sInf]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Filter α)
  body: .copy (sSup (Set.range pure)) {s | forall x, x in s} by simp

中文:
实例 :
  签名: Top (Filter α)
  定义体: .copy (sSup (Set.range pure)) {s | forall x, x in s} by simp

Depends on / 依赖: Set.range
-/
instance : Top (Filter α) where
top := .copy (sSup (Set.range pure)) {s | forall x, x in s} by simp

/--
theorem `mem_top_iff_forall` / 定理 `mem_top_iff_forall`

English:
theorem mem_top_iff_forall
  given: {s : Set α}
  statement: s in (⊤ : Filter α) ↔ forall x, x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_top_iff_forall
  条件: {s : Set α}
  结论: s in (⊤ : Filter α) ↔ 对任意 x, x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_top_iff_forall {s : Set α} : s in (⊤ : Filter α) ↔ forall x, x in s :=
  Iff.rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {s : Set α}
  statement: s in (⊤ : Filter α) ↔ s = univ
  proof: by
  rw [mem_top_iff_forall]; rw [eq_univ_iff_forall]

中文:
定理 mem_top
  条件: {s : Set α}
  结论: s in (⊤ : Filter α) ↔ s = univ
  证明: by
  rw [mem_top_iff_forall]; rw [eq_univ_iff_forall]

Depends on / 依赖: eq_univ_iff_forall, mem_top_iff_forall
-/
theorem mem_top {s : Set α} : s in (⊤ : Filter α) ↔ s = univ := by
  rw [mem_top_iff_forall]; rw [eq_univ_iff_forall]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Filter α)
  body: .copy (sSup ∅) univ by simp

@[simp]

中文:
实例 :
  签名: Bot (Filter α)
  定义体: .copy (sSup ∅) univ by simp

@[simp]
-/
instance : Bot (Filter α) where
bot := .copy (sSup ∅) univ by simp

@[simp]
/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {s : Set α}
  statement: s in (⊥ : Filter α)
  proof: trivial

中文:
定理 mem_bot
  条件: {s : Set α}
  结论: s in (⊥ : Filter α)
  证明: trivial
-/
theorem mem_bot {s : Set α} : s in (⊥ : Filter α) :=
  trivial

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (Filter α)
  body: ⟨fun f g : Filter α =>
    { sets := { s | exists a in f, exists b in g, s = a inter b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine ⟨a union y, mem_of_superset ha subset_union_left, b union y,
         

中文:
实例 instInf
  签名: : Min (Filter α)
  定义体: ⟨fun f g : Filter α =>
    { sets := { s | exists a in f, exists b in g, s = a inter b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine ⟨a union y, mem_of_superset ha subset_union_left, b union y,
         

Depends on / 依赖: Filter, inter_mem, inter_sets, inter_union_distrib_right, mem_of_superset, sets_of_superset, subset_union_left, union_eq_self_of_subset_left, univ_mem, univ_sets
-/
instance instInf : Min (Filter α) :=
  ⟨fun f g : Filter α =>
    { sets := { s | exists a in f, exists b in g, s = a inter b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine ⟨a union y, mem_of_superset ha subset_union_left, b union y,
          mem_of_superset hb subset_union_left, ?_⟩
        rw [← inter_union_distrib_right]; rw [union_eq_self_of_subset_left xy]
      inter_sets := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine ⟨a inter c, inter_mem ha hc, b inter d, inter_mem hb hd, ?_⟩
        ac_rfl }⟩

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max (Filter α) where
  body: .copy (sSup {f, g}) {s | s in f ∧ s in g} by simp

中文:
实例 instSup
  签名: : Max (Filter α) where
  定义体: .copy (sSup {f, g}) {s | s in f ∧ s in g} by simp
-/
instance instSup : Max (Filter α) where
max f g := .copy (sSup {f, g}) {s | s in f ∧ s in g} by simp

/--
Instance `instSDiff` / 实例 `instSDiff`

English:
instance instSDiff
  signature: : SDiff (Filter α) where
  body: {
    sets := {s | forall ⦃t⦄, t in g -> s subseteq t -> t in f}
    univ_sets := by simp +contextual
    sets_of_superset hx hxy t ht hyt := hx ht (hxy.trans hyt)
    inter_sets hx hy t htg ht := by
      rw [← union_eq_right.2 ht]; rw [inter_union_distrib_right]
      apply inter_mem
      · exact

中文:
实例 instSDiff
  签名: : SDiff (Filter α) where
  定义体: {
    sets := {s | forall ⦃t⦄, t in g -> s subseteq t -> t in f}
    univ_sets := by simp +contextual
    sets_of_superset hx hxy t ht hyt := hx ht (hxy.trans hyt)
    inter_sets hx hy t htg ht := by
      rw [← union_eq_right.2 ht]; rw [inter_union_distrib_right]
      apply inter_mem
      · exact
-/
instance instSDiff : SDiff (Filter α) where
  sdiff f g := {
    sets := {s | forall ⦃t⦄, t in g -> s subseteq t -> t in f}
    univ_sets := by simp +contextual
    sets_of_superset hx hxy t ht hyt := hx ht (hxy.trans hyt)
    inter_sets hx hy t htg ht := by
      rw [← union_eq_right.2 ht]; rw [inter_union_distrib_right]
      apply inter_mem
      · exact hx (mem_of_superset htg subset_union_right) subset_union_left
      · exact hy (mem_of_superset htg subset_union_right) subset_union_left
  }

/--
Instance `instHNot` / 实例 `instHNot`

English:
instance instHNot
  signature: : HNot (Filter α) where
  body: 𝓟 f.kerᶜ

中文:
实例 instHNot
  签名: : HNot (Filter α) where
  定义体: 𝓟 f.kerᶜ

Depends on / 依赖: f.ker
-/
instance instHNot : HNot (Filter α) where
  hnot f := 𝓟 f.kerᶜ

/--
theorem `mem_sdiff` / 定理 `mem_sdiff`

English:
theorem mem_sdiff
  statement: s in f \ g ↔ forall t in g, s subseteq t -> t in f
  proof: .rfl

中文:
定理 mem_sdiff
  结论: s in f \ g ↔ 对任意 t in g, s subseteq t -> t in f
  证明: .rfl
-/
theorem mem_sdiff : s in f \ g ↔ forall t in g, s subseteq t -> t in f := .rfl

/--
theorem `hnot_def` / 定理 `hnot_def`

English:
theorem hnot_def
  statement: ￢f = 𝓟 f.kerᶜ
  proof: rfl

中文:
定理 hnot_def
  结论: ￢f = 𝓟 f.kerᶜ
  证明: rfl
-/
protected theorem hnot_def : ￢f = 𝓟 f.kerᶜ := rfl


/--
Definition of `NeBot` / `NeBot` 的定义

English:
class NeBot
  parameters: (f : Filter α)
  axioms and operations (1):
    - ne' : f != ⊥

中文:
类 NeBot
  参数: (f : Filter α)
  公理与运算 (1 个):
    - ne' : f != ⊥
-/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f != ⊥

@[push ←]
/--
theorem `neBot_iff` / 定理 `neBot_iff`

English:
theorem neBot_iff
  given: {f : Filter α}
  statement: NeBot f ↔ f != ⊥
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 neBot_iff
  条件: {f : Filter α}
  结论: NeBot f ↔ f != ⊥
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
Definition of `Eventually` / `Eventually` 的定义

English:
definition Eventually
  signature: (p : α -> Prop) (f : Filter α)
  body: { x | p x } in f

@[inherit_doc Filter.Eventually]
notation3 "forallᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

中文:
定义 Eventually
  签名: (p : α -> 命题) (f : Filter α)
  定义体: { x | p x } in f

@[inherit_doc Filter.Eventually]
notation3 "forallᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r
-/
protected def Eventually (p : α -> Prop) (f : Filter α) : Prop :=
  { x | p x } in f

@[inherit_doc Filter.Eventually]
notation3 "forallᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

/--
Definition of `Frequently` / `Frequently` 的定义

English:
definition Frequently
  signature: (p : α -> Prop) (f : Filter α)
  body: ¬forallᶠ x in f, ¬p x

@[inherit_doc Filter.Frequently]
notation3 "existsᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

中文:
定义 Frequently
  签名: (p : α -> 命题) (f : Filter α)
  定义体: ¬forallᶠ x in f, ¬p x

@[inherit_doc Filter.Frequently]
notation3 "existsᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r
-/
protected def Frequently (p : α -> Prop) (f : Filter α) : Prop :=
  ¬forallᶠ x in f, ¬p x

@[inherit_doc Filter.Frequently]
notation3 "existsᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

/--
Definition of `EventuallyEq` / `EventuallyEq` 的定义

English:
definition EventuallyEq
  signature: (l : Filter α) (f g : α -> β)
  body: forallᶠ x in l, f x = g x

@[inherit_doc]
notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g

中文:
定义 EventuallyEq
  签名: (l : Filter α) (f g : α -> β)
  定义体: forallᶠ x in l, f x = g x

@[inherit_doc]
notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g
-/
def EventuallyEq (l : Filter α) (f g : α -> β) : Prop :=
  forallᶠ x in l, f x = g x

@[inherit_doc]
notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g

/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`. -/
@[to_dual self (reorder := f g)]
/--
Definition of `EventuallyLE` / `EventuallyLE` 的定义

English:
definition EventuallyLE
  signature: [LE β] (l : Filter α) (f g : α -> β)
  body: forallᶠ x in l, f x <= g x

@[inherit_doc]
notation:50 f " <=ᶠ[" l:50 "] " g:50 => EventuallyLE l f g

中文:
定义 EventuallyLE
  签名: [LE β] (l : Filter α) (f g : α -> β)
  定义体: forallᶠ x in l, f x <= g x

@[inherit_doc]
notation:50 f " <=ᶠ[" l:50 "] " g:50 => EventuallyLE l f g
-/
def EventuallyLE [LE β] (l : Filter α) (f g : α -> β) : Prop :=
  forallᶠ x in l, f x <= g x

@[inherit_doc]
notation:50 f " <=ᶠ[" l:50 "] " g:50 => EventuallyLE l f g

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (m : α -> β) (f : Filter α)
  body: preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx => st hx
  inter_sets hs ht := inter_mem hs ht

中文:
定义 map
  签名: (m : α -> β) (f : Filter α)
  定义体: preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx => st hx
  inter_sets hs ht := inter_mem hs ht

Depends on / 依赖: f.sets, preimage
-/
def map (m : α -> β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx => st hx
  inter_sets hs ht := inter_mem hs ht

/--
Definition of `Tendsto` / `Tendsto` 的定义

English:
definition Tendsto
  signature: (f : α -> β) (l₁ : Filter α) (l₂ : Filter β)
  body: l₁.map f <= l₂

中文:
定义 Tendsto
  签名: (f : α -> β) (l₁ : Filter α) (l₂ : Filter β)
  定义体: l₁.map f <= l₂
-/
def Tendsto (f : α -> β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f <= l₂

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (m : α -> β) (f : Filter β)
  body: { s | exists t in f, m ⁻¹' t subseteq s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

中文:
定义 comap
  签名: (m : α -> β) (f : Filter β)
  定义体: { s | exists t in f, m ⁻¹' t subseteq s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

Depends on / 依赖: subseteq
-/
def comap (m : α -> β) (f : Filter β) : Filter α where
  sets := { s | exists t in f, m ⁻¹' t subseteq s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: (f : Filter α) (g : Filter β)
  body: f.comap Prod.fst ⊔ g.comap Prod.snd

中文:
定义 coprod
  签名: (f : Filter α) (g : Filter β)
  定义体: f.comap Prod.fst ⊔ g.comap Prod.snd
-/
protected def coprod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst ⊔ g.comap Prod.snd

/--
Instance `instSProd` / 实例 `instSProd`

English:
instance instSProd
  signature: : SProd (Filter α) (Filter β) (Filter (α × β)) where
  body: f.comap Prod.fst ⊓ g.comap Prod.snd

中文:
实例 instSProd
  签名: : SProd (Filter α) (Filter β) (Filter (α × β)) where
  定义体: f.comap Prod.fst ⊓ g.comap Prod.snd

Depends on / 依赖: Prod.fst, Prod.snd, f.comap, g.comap
-/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

/--
theorem `prod_eq_inf` / 定理 `prod_eq_inf`

English:
theorem prod_eq_inf
  given: (f : Filter α) (g : Filter β)
  statement: f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd
  proof: rfl

中文:
定理 prod_eq_inf
  条件: (f : Filter α) (g : Filter β)
  结论: f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd
  证明: rfl
-/
theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι : Type*} {α : ι -> Type*} (f : forall i, Filter (α i))
  body: ⨅ i, comap (Function.eval i) (f i)

中文:
定义 pi
  签名: {ι : 类型} {α : ι -> 类型} (f : 对任意 i, Filter (α i))
  定义体: ⨅ i, comap (Function.eval i) (f i)

Depends on / 依赖: Function, Function.eval
-/
def pi {ι : Type*} {α : ι -> Type*} (f : forall i, Filter (α i)) : Filter (forall i, α i) :=
  ⨅ i, comap (Function.eval i) (f i)

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (f : Filter α) (m : α -> Filter β)
  body: join (map m f)

中文:
定义 bind
  签名: (f : Filter α) (m : α -> Filter β)
  定义体: join (map m f)
-/
def bind (f : Filter α) (m : α -> Filter β) : Filter β :=
  join (map m f)

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (f : Filter (α -> β)) (g : Filter α)
  body: { s | exists u in f, exists t in g, forall m in u, forall x in t, (m : α -> β) x in s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht

中文:
定义 seq
  签名: (f : Filter (α -> β)) (g : Filter α)
  定义体: { s | exists u in f, exists t in g, forall m in u, forall x in t, (m : α -> β) x in s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht
-/
def seq (f : Filter (α -> β)) (g : Filter α) : Filter β where
  sets := { s | exists u in f, exists t in g, forall m in u, forall x in t, (m : α -> β) x in s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ inter u₀, inter_mem ht₀ hu₀, t₁ inter u₁, inter_mem ht₁ hu₁, fun _ ⟨hx₀, hx₁⟩ _ ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (f : Filter α) (g : Filter β)
  body: bind f fun a => map (a, ·) g

中文:
定义 curry
  签名: (f : Filter α) (g : Filter β)
  定义体: bind f fun a => map (a, ·) g
-/
def curry (f : Filter α) (g : Filter β) : Filter (α × β) :=
  bind f fun a => map (a, ·) g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bind Filter
  body: ⟨@Filter.bind⟩

中文:
实例 :
  签名: Bind Filter
  定义体: ⟨@Filter.bind⟩

Depends on / 依赖: Filter, Filter.bind
-/
instance : Bind Filter :=
  ⟨@Filter.bind⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor Filter
  body: @Filter.map

中文:
实例 :
  签名: Functor Filter
  定义体: @Filter.map

Depends on / 依赖: Filter, Filter.map
-/
instance : Functor Filter where map := @Filter.map

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : Filter α) (g : Set α -> Filter β)
  body: ⨅ s in f, g s

中文:
定义 lift
  签名: (f : Filter α) (g : Set α -> Filter β)
  定义体: ⨅ s in f, g s
-/
protected def lift (f : Filter α) (g : Set α -> Filter β) :=
  ⨅ s in f, g s

/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: (f : Filter α) (h : Set α -> Set β)
  body: f.lift (𝓟 ∘ h)

中文:
定义 lift'
  签名: (f : Filter α) (h : Set α -> Set β)
  定义体: f.lift (𝓟 ∘ h)
-/
protected def lift' (f : Filter α) (h : Set α -> Set β) :=
  f.lift (𝓟 ∘ h)

/--
Definition of `IsBounded` / `IsBounded` 的定义

English:
definition IsBounded
  signature: (r : α -> α -> Prop) (f : Filter α)
  body: exists b, forallᶠ x in f, r x b

中文:
定义 IsBounded
  签名: (r : α -> α -> 命题) (f : Filter α)
  定义体: exists b, forallᶠ x in f, r x b
-/
def IsBounded (r : α -> α -> Prop) (f : Filter α) :=
  exists b, forallᶠ x in f, r x b

/--
Definition of `IsBoundedUnder` / `IsBoundedUnder` 的定义

English:
definition IsBoundedUnder
  signature: (r : α -> α -> Prop) (f : Filter β) (u : β -> α)
  body: (map u f).IsBounded r

中文:
定义 IsBoundedUnder
  签名: (r : α -> α -> 命题) (f : Filter β) (u : β -> α)
  定义体: (map u f).IsBounded r

Depends on / 依赖: IsBounded
-/
def IsBoundedUnder (r : α -> α -> Prop) (f : Filter β) (u : β -> α) :=
  (map u f).IsBounded r

/--
Definition of `IsCobounded` / `IsCobounded` 的定义

English:
definition IsCobounded
  signature: (r : α -> α -> Prop) (f : Filter α)
  body: exists b, forall a, (forallᶠ x in f, r x a) -> r b a

中文:
定义 IsCobounded
  签名: (r : α -> α -> 命题) (f : Filter α)
  定义体: exists b, forall a, (forallᶠ x in f, r x a) -> r b a
-/
def IsCobounded (r : α -> α -> Prop) (f : Filter α) :=
  exists b, forall a, (forallᶠ x in f, r x a) -> r b a

/--
Definition of `IsCoboundedUnder` / `IsCoboundedUnder` 的定义

English:
definition IsCoboundedUnder
  signature: (r : α -> α -> Prop) (f : Filter β) (u : β -> α)
  body: (map u f).IsCobounded r

中文:
定义 IsCoboundedUnder
  签名: (r : α -> α -> 命题) (f : Filter β) (u : β -> α)
  定义体: (map u f).IsCobounded r

Depends on / 依赖: IsCobounded
-/
def IsCoboundedUnder (r : α -> α -> Prop) (f : Filter β) (u : β -> α) :=
  (map u f).IsCobounded r

end Filter

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/--
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intro a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/
syntax (name := filterUpwards) "filter_upwards" (" [" term,* "]")?
  (" with" (ppSpace colGt term:max)*)? (" using " term)? : tactic

elab_rules : tactic
| `(tactic| filter_upwards $[[$[$args],*]]? $[with $wth*]? $[using $usingArg]?) => do
  focus do
    let config : ApplyConfig := {newGoals := ApplyNewGoals.nonDependentOnly}
.reverse do for e in args.getD #[]
      let goal ← getMainGoal
replaceMainGoal ← goal.withContext runTermElab do
        let m ← mkFreshExprMVar none
        let lem ← Term.elabTermEnsuringType
          (← ``(Filter.mp_mem $e $(← Term.exprToSyntax m))) (← goal.getType)
        goal.assign lem
        return [m.mvarId!]
    liftMetaTactic fun goal => do
      goal.apply (← mkConstWithFreshMVarLevels ``Filter.univ_mem') config
evalTactic ← `(tactic| try dsimp -zeta only [Set.mem_ofPred_eq])
    if let some l := wth then
evalTactic ← `(tactic| intro $[$l]*)
    if let some e := usingArg then
evalTactic ← `(tactic| exact $e)

end Mathlib.Tactic
