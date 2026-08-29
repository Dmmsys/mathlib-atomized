/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.ToFun

/-!
# Theory of filters on sets

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

In this file, we endow `Filter α` it with a complete lattice structure.
This structure is lifted from the lattice structure on `Set (Set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `Filter` is a monadic functor, with a push-forward operation
`Filter.map` and a pull-back operation `Filter.comap` that form a Galois connections for the
order on filters.

The examples of filters appearing in the description of the two motivating ideas are:
* `(Filter.atTop : Filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in `Mathlib/Topology/UniformSpace/Basic.lean`)
* `MeasureTheory.ae` : made of sets whose complement has zero measure with respect to `μ`
  (defined in `Mathlib/MeasureTheory/OuterMeasure/AE`)

The predicate "happening eventually" is `Filter.Eventually`, and "happening often" is
`Filter.Frequently`, whose definitions are immediate after `Filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

## Notation

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `Filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[NeBot f]` in a number of lemmas and definitions.
-/

@[expose] public section

assert_not_exists IsOrderedRing Fintype

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

/--
Instance `inhabitedMem` / 实例 `inhabitedMem`

English:
instance inhabitedMem
  signature: : Inhabited { s : Set α // s in f }
  body: ⟨⟨univ, f.univ_sets⟩⟩

中文:
实例 inhabitedMem
  签名: : 可居 { s : 集合 α // s in f }
  定义体: ⟨⟨univ, f.univ_sets⟩⟩

Depends on / 依赖: f.univ_sets, univ_sets
-/
instance inhabitedMem : Inhabited { s : Set α // s in f } :=
  ⟨⟨univ, f.univ_sets⟩⟩

/--
theorem `filter_eq_iff` / 定理 `filter_eq_iff`

English:
theorem filter_eq_iff
  statement: f = g ↔ f.sets = g.sets
  proof: ⟨congr_arg _, filter_eq⟩

中文:
定理 filter_eq_iff
  结论: f = g ↔ f.sets = g.sets
  证明: ⟨congr_arg _, filter_eq⟩

Depends on / 依赖: congr_arg, filter_eq
-/
theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congr_arg _, filter_eq⟩

/--
theorem `sets_subset_sets` / 定理 `sets_subset_sets`

English:
theorem sets_subset_sets
  statement: f.sets subseteq g.sets ↔ g <= f
  proof: .rfl

中文:
定理 sets_subset_sets
  结论: f.sets subseteq g.sets ↔ g <= f
  证明: .rfl
-/
@[simp] theorem sets_subset_sets : f.sets subseteq g.sets ↔ g <= f := .rfl
/--
theorem `sets_ssubset_sets` / 定理 `sets_ssubset_sets`

English:
theorem sets_ssubset_sets
  statement: f.sets ⊂ g.sets ↔ g < f
  proof: .rfl

中文:
定理 sets_ssubset_sets
  结论: f.sets ⊂ g.sets ↔ g < f
  证明: .rfl
-/
@[simp] theorem sets_ssubset_sets : f.sets ⊂ g.sets ↔ g < f := .rfl

/--
theorem `coext` / 定理 `coext`

English:
theorem coext
  given: (h : forall s, sᶜ in f ↔ sᶜ in g)
  statement: f = g
  proof: Filter.ext compl_surjective.forall.2 h

中文:
定理 coext
  条件: (h : 对任意 s, sᶜ in f ↔ sᶜ in g)
  结论: f = g
  证明: Filter.ext compl_surjective.forall.2 h
-/
protected theorem coext (h : forall s, sᶜ in f ↔ sᶜ in g) : f = g :=
Filter.ext compl_surjective.forall.2 h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (· ⊇ ·) ((· in ·) : Set α -> Filter α -> Prop) (· in ·)
  body: mem_of_superset h₂ h₁

中文:
实例 :
  签名: Trans (· ⊇ ·) ((· in ·) : 集合 α -> 滤子 α -> 命题) (· in ·)
  定义体: mem_of_superset h₂ h₁

Depends on / 依赖: mem_of_superset
-/
instance : Trans (· ⊇ ·) ((· in ·) : Set α -> Filter α -> Prop) (· in ·) where
  trans h₁ h₂ := mem_of_superset h₂ h₁

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans Membership.mem (· subseteq ·) (Membership.mem : Filter α -> Set α -> Prop)
  body: mem_of_superset h₁ h₂

@[simp]

中文:
实例 :
  签名: Trans Membership.mem (· subseteq ·) (Membership.mem : 滤子 α -> 集合 α -> 命题)
  定义体: mem_of_superset h₁ h₂

@[simp]

Depends on / 依赖: mem_of_superset
-/
instance : Trans Membership.mem (· subseteq ·) (Membership.mem : Filter α -> Set α -> Prop) where
  trans h₁ h₂ := mem_of_superset h₁ h₂

@[simp]
/--
theorem `inter_mem_iff` / 定理 `inter_mem_iff`

English:
theorem inter_mem_iff
  given: {s t : Set α}
  statement: s inter t in f ↔ s in f ∧ t in f
  proof: ⟨fun h => ⟨mem_of_superset h inter_subset_left, mem_of_superset h inter_subset_right⟩,
    and_imp.2 inter_mem⟩

中文:
定理 inter_mem_iff
  条件: {s t : 集合 α}
  结论: s inter t in f ↔ s in f ∧ t in f
  证明: ⟨fun h => ⟨mem_of_superset h inter_subset_left, mem_of_superset h inter_subset_right⟩,
    and_imp.2 inter_mem⟩

Depends on / 依赖: and_imp, inter_mem, inter_subset_left, inter_subset_right, mem_of_superset
-/
theorem inter_mem_iff {s t : Set α} : s inter t in f ↔ s in f ∧ t in f :=
  ⟨fun h => ⟨mem_of_superset h inter_subset_left, mem_of_superset h inter_subset_right⟩,
    and_imp.2 inter_mem⟩

/--
theorem `sdiff_mem` / 定理 `sdiff_mem`

English:
theorem sdiff_mem
  given: {s t : Set α} (hs : s in f) (ht : tᶜ in f)
  statement: s \ t in f
  proof: inter_mem hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem := sdiff_mem

中文:
定理 sdiff_mem
  条件: {s t : 集合 α} (hs : s in f) (ht : tᶜ in f)
  结论: s \ t in f
  证明: inter_mem hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem := sdiff_mem

Depends on / 依赖: inter_mem
-/
theorem sdiff_mem {s t : Set α} (hs : s in f) (ht : tᶜ in f) : s \ t in f :=
  inter_mem hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem := sdiff_mem

/--
theorem `congr_sets` / 定理 `congr_sets`

English:
theorem congr_sets
  given: (h : { x | x in s ↔ x in t } in f)
  statement: s in f ↔ t in f
  proof: ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩

中文:
定理 congr_sets
  条件: (h : { x | x in s ↔ x in t } in f)
  结论: s in f ↔ t in f
  证明: ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩

Depends on / 依赖: Iff.mp, Iff.mpr, mem_of_superset, mp_mem
-/
theorem congr_sets (h : { x | x in s ↔ x in t } in f) : s in f ↔ t in f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: {S} (hmem : forall s, s in S ↔ s in f)
  statement: f.copy S hmem = f
  proof: Filter.ext hmem

中文:
引理 copy_eq
  条件: {S} (hmem : 对任意 s, s in S ↔ s in f)
  结论: f.copy S hmem = f
  证明: Filter.ext hmem

Depends on / 依赖: Filter, Filter.ext
-/
lemma copy_eq {S} (hmem : forall s, s in S ↔ s in f) : f.copy S hmem = f := Filter.ext hmem

/--
theorem `biInter_mem'` / 定理 `biInter_mem'`

English:
theorem biInter_mem'
  given: {β : Type v} {s : β -> Set α} {is : Set β} (hf : is.Subsingleton)
  proof: by
  apply Subsingleton.induction_on hf <;> simp

中文:
定理 bi整数er_mem'
  条件: {β : 类型v} {s : β -> 集合 α} {is : 集合 β} (hf : is.子单例)
  证明: by
  apply Subsingleton.induction_on hf <;> simp

Depends on / 依赖: Subsingleton, Subsingleton.induction_on, induction_on
-/
theorem biInter_mem' {β : Type v} {s : β -> Set α} {is : Set β} (hf : is.Subsingleton) :
    (⋂ i in is, s i) in f ↔ forall i in is, s i in f := by
  apply Subsingleton.induction_on hf <;> simp

/--
theorem `iInter_mem'` / 定理 `iInter_mem'`

English:
theorem iInter_mem'
  given: {β : Sort v} {s : β -> Set α} [Subsingleton β]
  proof: by
  rw [← sInter_range]; rw [sInter_eq_biInter]; rw [biInter_mem' (subsingleton_range s)]; rw [forall_mem_range]

中文:
定理 i整数er_mem'
  条件: {β : 类型层 v} {s : β -> 集合 α} [子单例 β]
  证明: by
  rw [← sInter_range]; rw [sInter_eq_biInter]; rw [biInter_mem' (subsingleton_range s)]; rw [forall_mem_range]

Depends on / 依赖: biInter_mem, forall_mem_range, sInter_eq_biInter, sInter_range, subsingleton_range
-/
theorem iInter_mem' {β : Sort v} {s : β -> Set α} [Subsingleton β] :
    (⋂ i, s i) in f ↔ forall i, s i in f := by
  rw [← sInter_range]; rw [sInter_eq_biInter]; rw [biInter_mem' (subsingleton_range s)]; rw [forall_mem_range]

/--
theorem `exists_mem_subset_iff` / 定理 `exists_mem_subset_iff`

English:
theorem exists_mem_subset_iff
  statement: (exists t in f, t subseteq s) ↔ s in f
  proof: ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩

中文:
定理 存在_mem_subset_iff
  结论: (存在 t in f, t subseteq s) ↔ s in f
  证明: ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩

Depends on / 依赖: Subset, Subset.rfl, mem_of_superset
-/
theorem exists_mem_subset_iff : (exists t in f, t subseteq s) ↔ s in f :=
  ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩

/--
theorem `monotone_mem` / 定理 `monotone_mem`

English:
theorem monotone_mem
  given: {f : Filter α}
  statement: Monotone fun s => s in f
  proof: fun _ _ hst h =>
  mem_of_superset h hst

中文:
定理 monotone_mem
  条件: {f : 滤子 α}
  结论: 递增 fun s => s in f
  证明: fun _ _ hst h =>
  mem_of_superset h hst
-/
theorem monotone_mem {f : Filter α} : Monotone fun s => s in f := fun _ _ hst h =>
  mem_of_superset h hst

/--
theorem `exists_mem_and_iff` / 定理 `exists_mem_and_iff`

English:
theorem exists_mem_and_iff
  statement: {P : Set α -> Prop} {Q : Set α -> Prop} (hP : Antitone P)
  proof: by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u inter v, inter_mem huf hvf, hP inter_subset_left hPu, hQ inter_subset_right hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩

中文:
定理 存在_mem_and_iff
  结论: {P : 集合 α -> 命题} {Q : 集合 α -> 命题} (hP : 递减 P)
  证明: by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u inter v, inter_mem huf hvf, hP inter_subset_left hPu, hQ inter_subset_right hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩

Depends on / 依赖: inter_mem, inter_subset_left, inter_subset_right
-/
theorem exists_mem_and_iff {P : Set α -> Prop} {Q : Set α -> Prop} (hP : Antitone P)
    (hQ : Antitone Q) : ((exists u in f, P u) ∧ exists u in f, Q u) ↔ exists u in f, P u ∧ Q u := by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u inter v, inter_mem huf hvf, hP inter_subset_left hPu, hQ inter_subset_right hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩

end Filter


namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

/--
theorem `mem_principal_self` / 定理 `mem_principal_self`

English:
theorem mem_principal_self
  given: (s : Set α)
  statement: s in 𝓟 s
  proof: Subset.rfl

中文:
定理 mem_principal_self
  条件: (s : 集合 α)
  结论: s in 𝓟 s
  证明: Subset.rfl

Depends on / 依赖: Subset, Subset.rfl
-/
theorem mem_principal_self (s : Set α) : s in 𝓟 s := Subset.rfl

/--
theorem `eventually_mem_principal` / 定理 `eventually_mem_principal`

English:
theorem eventually_mem_principal
  given: (s : Set α)
  statement: forallᶠ x in 𝓟 s, x in s
  proof: mem_principal_self s

中文:
定理 eventually_mem_principal
  条件: (s : 集合 α)
  结论: 对任意ᶠ x in 𝓟 s, x in s
  证明: mem_principal_self s

Depends on / 依赖: mem_principal_self
-/
theorem eventually_mem_principal (s : Set α) : forallᶠ x in 𝓟 s, x in s := mem_principal_self s

section Lattice

variable {f g : Filter α} {s t : Set α}

/--
theorem `not_le` / 定理 `not_le`

English:
theorem not_le
  statement: ¬f <= g ↔ exists s in g, s ∉ f
  proof: by simp_rw [le_def, not_forall, exists_prop]

中文:
定理 not_le
  结论: ¬f <= g ↔ 存在 s in g, s ∉ f
  证明: by simp_rw [le_def, not_forall, exists_prop]
-/
protected theorem not_le : ¬f <= g ↔ exists s in g, s ∉ f := by simp_rw [le_def, not_forall, exists_prop]

/--
Inductive type `GenerateSets` / 归纳类型 `GenerateSets`

English:
inductive GenerateSets
  parameters: (g : Set (Set α))
  constructors (4):
    - basic: {s : Set α} : s in g -> GenerateSets g s
    - univ: GenerateSets g univ
    - superset: {s t : Set α} : GenerateSets g s -> s subseteq t -> GenerateSets g t
    - inter: {s t : Set α} : GenerateSets g s -> GenerateSets g t -> GenerateSets g (s inter t)

中文:
归纳类型 GenerateSets
  参数: (g : 集合 (集合 α))
  构造子 (4 个):
    - basic: {s : 集合 α} : s in g -> GenerateSets g s
    - univ: GenerateSets g univ
    - superset: {s t : 集合 α} : GenerateSets g s -> s subseteq t -> GenerateSets g t
    - inter: {s t : 集合 α} : GenerateSets g s -> GenerateSets g t -> GenerateSets g (s inter t)
-/
inductive GenerateSets (g : Set (Set α)) : Set α -> Prop
  | basic {s : Set α} : s in g -> GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s -> s subseteq t -> GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s -> GenerateSets g t -> GenerateSets g (s inter t)

/--
Definition of `generate` / `generate` 的定义

English:
definition generate
  signature: (g : Set (Set α))
  body: {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

中文:
定义 generate
  签名: (g : 集合 (集合 α))
  定义体: {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

Depends on / 依赖: GenerateSets
-/
def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

/--
lemma `mem_generate_of_mem` / 引理 `mem_generate_of_mem`

English:
lemma mem_generate_of_mem
  given: {s : Set <| Set α} {U : Set α} (h : U in s)
  proof: GenerateSets.basic h

中文:
引理 mem_generate_of_mem
  条件: {s : 集合 <| 集合 α} {U : 集合 α} (h : U in s)
  证明: GenerateSets.basic h

Depends on / 依赖: GenerateSets, GenerateSets.basic
-/
lemma mem_generate_of_mem {s : Set <| Set α} {U : Set α} (h : U in s) :
    U in generate s := GenerateSets.basic h

/--
theorem `le_generate_iff` / 定理 `le_generate_iff`

English:
theorem le_generate_iff
  given: {s : Set (Set α)} {f : Filter α}
  statement: f <= generate s ↔ s subseteq f.sets
  proof: Iff.intro (fun h _ hu => h <| GenerateSets.basic <| hu) fun h _ hu =>
    hu.recOn (fun h' => h h') univ_mem (fun _ hxy => by gcongr) fun _ _ hx hy =>
      inter_mem hx hy

中文:
定理 le_generate_iff
  条件: {s : 集合 (集合 α)} {f : 滤子 α}
  结论: f <= generate s ↔ s subseteq f.sets
  证明: Iff.intro (fun h _ hu => h <| GenerateSets.basic <| hu) fun h _ hu =>
    hu.recOn (fun h' => h h') univ_mem (fun _ hxy => by gcongr) fun _ _ hx hy =>
      inter_mem hx hy

Depends on / 依赖: GenerateSets, GenerateSets.basic, Iff.intro, hu.recOn, inter_mem, univ_mem
-/
theorem le_generate_iff {s : Set (Set α)} {f : Filter α} : f <= generate s ↔ s subseteq f.sets :=
  Iff.intro (fun h _ hu => h <| GenerateSets.basic <| hu) fun h _ hu =>
    hu.recOn (fun h' => h h') univ_mem (fun _ hxy => by gcongr) fun _ _ hx hy =>
      inter_mem hx hy

/--
lemma `generate_singleton` / 引理 `generate_singleton`

English:
lemma generate_singleton
  given: (s : Set α)
  statement: generate {s} = 𝓟 s
  proof: le_antisymm (fun _t ht => mem_of_superset (mem_generate_of_mem <| mem_singleton _) ht)
le_generate_iff.2 singleton_subset_iff.2 Subset.rfl

中文:
引理 generate_singleton
  条件: (s : 集合 α)
  结论: generate {s} = 𝓟 s
  证明: le_antisymm (fun _t ht => mem_of_superset (mem_generate_of_mem <| mem_singleton _) ht)
le_generate_iff.2 singleton_subset_iff.2 Subset.rfl
-/
@[simp] lemma generate_singleton (s : Set α) : generate {s} = 𝓟 s :=
le_antisymm (fun _t ht => mem_of_superset (mem_generate_of_mem <| mem_singleton _) ht)
le_generate_iff.2 singleton_subset_iff.2 Subset.rfl

/--
Definition of `mkOfClosure` / `mkOfClosure` 的定义

English:
definition mkOfClosure
  signature: (s : Set (Set α)) (hs : (generate s).sets = s)
  body: s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem

中文:
定义 mkOfClosure
  签名: (s : 集合 (集合 α)) (hs : (generate s).sets = s)
  定义体: s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem
-/
protected def mkOfClosure (s : Set (Set α)) (hs : (generate s).sets = s) : Filter α where
  sets := s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem

/--
theorem `mkOfClosure_sets` / 定理 `mkOfClosure_sets`

English:
theorem mkOfClosure_sets
  given: {s : Set (Set α)} {hs : (generate s).sets = s}
  proof: Filter.ext fun u =>
    show u in (Filter.mkOfClosure s hs).sets ↔ u in (generate s).sets from hs.symm ▸ Iff.rfl

中文:
定理 mkOfClosure_sets
  条件: {s : 集合 (集合 α)} {hs : (generate s).sets = s}
  证明: Filter.ext fun u =>
    show u in (Filter.mkOfClosure s hs).sets ↔ u in (generate s).sets from hs.symm ▸ Iff.rfl

Depends on / 依赖: Filter, Filter.ext, Filter.mkOfClosure, Iff.rfl, generate, hs.symm, mkOfClosure
-/
theorem mkOfClosure_sets {s : Set (Set α)} {hs : (generate s).sets = s} :
    Filter.mkOfClosure s hs = generate s :=
  Filter.ext fun u =>
    show u in (Filter.mkOfClosure s hs).sets ↔ u in (generate s).sets from hs.symm ▸ Iff.rfl

/--
Definition of `giGenerate` / `giGenerate` 的定义

English:
definition giGenerate
  signature: (α : Type*)
  body: le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

中文:
定义 giGenerate
  签名: (α : 类型)
  定义体: le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

Depends on / 依赖: le_generate_iff
-/
def giGenerate (α : Type*) :
    @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.sets where
  gc _ _ := le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

/--
theorem `mem_inf_iff` / 定理 `mem_inf_iff`

English:
theorem mem_inf_iff
  given: {f g : Filter α} {s : Set α}
  statement: s in f ⊓ g ↔ exists t₁ in f, exists t₂ in g, s = t₁ inter t₂
  proof: Iff.rfl

中文:
定理 mem_inf_iff
  条件: {f g : 滤子 α} {s : 集合 α}
  结论: s in f ⊓ g ↔ 存在 t₁ in f, 存在 t₂ in g, s = t₁ inter t₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf_iff {f g : Filter α} {s : Set α} : s in f ⊓ g ↔ exists t₁ in f, exists t₂ in g, s = t₁ inter t₂ :=
  Iff.rfl

/--
theorem `mem_inf_of_left` / 定理 `mem_inf_of_left`

English:
theorem mem_inf_of_left
  given: {f g : Filter α} {s : Set α} (h : s in f)
  statement: s in f ⊓ g
  proof: ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩

中文:
定理 mem_inf_of_left
  条件: {f g : 滤子 α} {s : 集合 α} (h : s in f)
  结论: s in f ⊓ g
  证明: ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩

Depends on / 依赖: inter_univ, univ_mem
-/
theorem mem_inf_of_left {f g : Filter α} {s : Set α} (h : s in f) : s in f ⊓ g :=
  ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩

/--
theorem `mem_inf_of_right` / 定理 `mem_inf_of_right`

English:
theorem mem_inf_of_right
  given: {f g : Filter α} {s : Set α} (h : s in g)
  statement: s in f ⊓ g
  proof: ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩

中文:
定理 mem_inf_of_right
  条件: {f g : 滤子 α} {s : 集合 α} (h : s in g)
  结论: s in f ⊓ g
  证明: ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩

Depends on / 依赖: univ_inter, univ_mem
-/
theorem mem_inf_of_right {f g : Filter α} {s : Set α} (h : s in g) : s in f ⊓ g :=
  ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩

/--
theorem `inter_mem_inf` / 定理 `inter_mem_inf`

English:
theorem inter_mem_inf
  given: {α : Type u} {f g : Filter α} {s t : Set α} (hs : s in f) (ht : t in g)
  proof: ⟨s, hs, t, ht, rfl⟩

中文:
定理 inter_mem_inf
  条件: {α : 类型u} {f g : 滤子 α} {s t : 集合 α} (hs : s in f) (ht : t in g)
  证明: ⟨s, hs, t, ht, rfl⟩
-/
theorem inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s in f) (ht : t in g) :
    s inter t in f ⊓ g :=
  ⟨s, hs, t, ht, rfl⟩

/--
theorem `mem_inf_of_inter` / 定理 `mem_inf_of_inter`

English:
theorem mem_inf_of_inter
  statement: {f g : Filter α} {s t u : Set α} (hs : s in f) (ht : t in g)
  proof: mem_of_superset (inter_mem_inf hs ht) h

中文:
定理 mem_inf_of_inter
  结论: {f g : 滤子 α} {s t u : 集合 α} (hs : s in f) (ht : t in g)
  证明: mem_of_superset (inter_mem_inf hs ht) h

Depends on / 依赖: inter_mem_inf, mem_of_superset
-/
theorem mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s in f) (ht : t in g)
    (h : s inter t subseteq u) : u in f ⊓ g :=
  mem_of_superset (inter_mem_inf hs ht) h

/--
theorem `mem_inf_iff_superset` / 定理 `mem_inf_iff_superset`

English:
theorem mem_inf_iff_superset
  given: {f g : Filter α} {s : Set α}
  proof: ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨_, h₁, _, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩

中文:
定理 mem_inf_iff_superset
  条件: {f g : 滤子 α} {s : 集合 α}
  证明: ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨_, h₁, _, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩

Depends on / 依赖: Subset, Subset.rfl, mem_inf_of_inter
-/
theorem mem_inf_iff_superset {f g : Filter α} {s : Set α} :
    s in f ⊓ g ↔ exists t₁ in f, exists t₂ in g, t₁ inter t₂ subseteq s :=
  ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨_, h₁, _, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩

/--
theorem `mem_sdiff_iff_union` / 定理 `mem_sdiff_iff_union`

English:
theorem mem_sdiff_iff_union
  given: {f g : Filter α} {s : Set α}
  proof: ⟨fun hs _ ht => hs (mem_of_superset ht subset_union_right) subset_union_left,
    fun h t htg hst => union_eq_right.2 hst ▸ h t htg⟩

中文:
定理 mem_sdiff_iff_union
  条件: {f g : 滤子 α} {s : 集合 α}
  证明: ⟨fun hs _ ht => hs (mem_of_superset ht subset_union_right) subset_union_left,
    fun h t htg hst => union_eq_right.2 hst ▸ h t htg⟩

Depends on / 依赖: mem_of_superset, subset_union_left, subset_union_right, union_eq_right
-/
theorem mem_sdiff_iff_union {f g : Filter α} {s : Set α} :
    s in f \ g ↔ forall t in g, s union t in f :=
  ⟨fun hs _ ht => hs (mem_of_superset ht subset_union_right) subset_union_left,
    fun h t htg hst => union_eq_right.2 hst ▸ h t htg⟩

section CompleteLattice

/--
lemma `isLUB_sSup` / 引理 `isLUB_sSup`

English:
lemma isLUB_sSup
  given: (s : Set (Filter α))
  statement: IsLUB s (sSup s)
  proof: ⟨fun _ h₁ _ h₂ => h₂ h₁, fun _ h₁ _ h₂ _ h₃ => h₁ h₃ h₂⟩

中文:
引理 isLUB_sSup
  条件: (s : 集合 (滤子 α))
  结论: IsLUB s (sSup s)
  证明: ⟨fun _ h₁ _ h₂ => h₂ h₁, fun _ h₁ _ h₂ _ h₃ => h₁ h₃ h₂⟩
-/
protected lemma isLUB_sSup (s : Set (Filter α)) : IsLUB s (sSup s) :=
  ⟨fun _ h₁ _ h₂ => h₂ h₁, fun _ h₁ _ h₂ _ h₃ => h₁ h₃ h₂⟩

/--
lemma `isGLB_sInf` / 引理 `isGLB_sInf`

English:
lemma isGLB_sInf
  given: (s : Set (Filter α))
  statement: IsGLB s (sInf s)
  proof: isLUB_lowerBounds.mp (Filter.sSup_lowerBounds _ ▸ Filter.isLUB_sSup _)

中文:
引理 isGLB_sInf
  条件: (s : 集合 (滤子 α))
  结论: IsGLB s (sInf s)
  证明: isLUB_lowerBounds.mp (Filter.sSup_lowerBounds _ ▸ Filter.isLUB_sSup _)
-/
protected lemma isGLB_sInf (s : Set (Filter α)) : IsGLB s (sInf s) :=
  isLUB_lowerBounds.mp (Filter.sSup_lowerBounds _ ▸ Filter.isLUB_sSup _)

/--
Instance `instCompleteLatticeFilter` / 实例 `instCompleteLatticeFilter`

English:
instance instCompleteLatticeFilter
  signature: : CompleteLattice (Filter α) where
  body: min a b
  sup a b := max a b
  le_sup_left _ _ _ h := h.1
  le_sup_right _ _ _ h := h.2
  sup_le _ _ _ h₁ h₂ _ h := ⟨h₁ h, h₂ h⟩
  inf_le_left _ _ _ := mem_inf_of_left
  inf_le_right _ _ _ := mem_inf_of_right
  le_inf := fun _ _ _ h₁ h₂ _s ⟨_a, ha, _b, hb, hs⟩ => hs.symm ▸ inter_mem (h₁ ha) (h₂ hb)
  isLUB_sSup := Filter.isLUB_sSup
  isGLB_sInf := Filter.isGLB_sInf
  le_top _ _ := univ_mem'
  bot_le _ _ _ := trivial

中文:
实例 instCompleteLatticeFilter
  签名: : 完备格 (滤子 α) where
  定义体: min a b
  sup a b := max a b
  le_sup_left _ _ _ h := h.1
  le_sup_right _ _ _ h := h.2
  sup_le _ _ _ h₁ h₂ _ h := ⟨h₁ h, h₂ h⟩
  inf_le_left _ _ _ := mem_inf_of_left
  inf_le_right _ _ _ := mem_inf_of_right
  le_inf := fun _ _ _ h₁ h₂ _s ⟨_a, ha, _b, hb, hs⟩ => hs.symm ▸ inter_mem (h₁ ha) (h₂ hb)
  isLUB_sSup := Filter.isLUB_sSup
  isGLB_sInf := Filter.isGLB_sInf
  le_top _ _ := univ_mem'
  bot_le _ _ _ := trivial
-/
instance instCompleteLatticeFilter : CompleteLattice (Filter α) where
  inf a b := min a b
  sup a b := max a b
  le_sup_left _ _ _ h := h.1
  le_sup_right _ _ _ h := h.2
  sup_le _ _ _ h₁ h₂ _ h := ⟨h₁ h, h₂ h⟩
  inf_le_left _ _ _ := mem_inf_of_left
  inf_le_right _ _ _ := mem_inf_of_right
  le_inf := fun _ _ _ h₁ h₂ _s ⟨_a, ha, _b, hb, hs⟩ => hs.symm ▸ inter_mem (h₁ ha) (h₂ hb)
  isLUB_sSup := Filter.isLUB_sSup
  isGLB_sInf := Filter.isGLB_sInf
  le_top _ _ := univ_mem'
  bot_le _ _ _ := trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Filter α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (滤子 α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Filter α) := ⟨⊥⟩

end CompleteLattice

/--
theorem `NeBot.ne` / 定理 `NeBot.ne`

English:
theorem NeBot.ne
  given: {f : Filter α} (hf : NeBot f)
  statement: f != ⊥
  proof: hf.ne'

@[simp, push]

中文:
定理 NeBot.ne
  条件: {f : 滤子 α} (hf : NeBot f)
  结论: f != ⊥
  证明: hf.ne'

@[simp, push]

Depends on / 依赖: hf.ne
-/
theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f != ⊥ := hf.ne'

@[simp, push]
/--
theorem `not_neBot` / 定理 `not_neBot`

English:
theorem not_neBot
  given: {f : Filter α}
  statement: ¬f.NeBot ↔ f = ⊥
  proof: neBot_iff.not_left

@[gcongr]

中文:
定理 not_neBot
  条件: {f : 滤子 α}
  结论: ¬f.NeBot ↔ f = ⊥
  证明: neBot_iff.not_left

@[gcongr]

Depends on / 依赖: neBot_iff, neBot_iff.not_left, not_left
-/
theorem not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥ := neBot_iff.not_left

@[gcongr]
/--
theorem `NeBot.mono` / 定理 `NeBot.mono`

English:
theorem NeBot.mono
  given: {f g : Filter α} (hf : NeBot f) (hg : f <= g)
  statement: NeBot g
  proof: ⟨ne_bot_of_le_ne_bot hf.1 hg⟩

中文:
定理 NeBot.mono
  条件: {f g : 滤子 α} (hf : NeBot f) (hg : f <= g)
  结论: NeBot g
  证明: ⟨ne_bot_of_le_ne_bot hf.1 hg⟩

Depends on / 依赖: ne_bot_of_le_ne_bot
-/
theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f <= g) : NeBot g :=
  ⟨ne_bot_of_le_ne_bot hf.1 hg⟩

/--
theorem `neBot_of_le` / 定理 `neBot_of_le`

English:
theorem neBot_of_le
  given: {f g : Filter α} [hf : NeBot f] (hg : f <= g)
  statement: NeBot g
  proof: hf.mono hg

中文:
定理 neBot_of_le
  条件: {f g : 滤子 α} [hf : NeBot f] (hg : f <= g)
  结论: NeBot g
  证明: hf.mono hg

Depends on / 依赖: hf.mono
-/
theorem neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f <= g) : NeBot g :=
  hf.mono hg

/--
theorem `sup_neBot` / 定理 `sup_neBot`

English:
theorem sup_neBot
  given: {f g : Filter α}
  statement: NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g
  proof: by
  simp only [neBot_iff, not_and_or, Ne, sup_eq_bot_iff]

中文:
定理 sup_neBot
  条件: {f g : 滤子 α}
  结论: NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g
  证明: by
  simp only [neBot_iff, not_and_or, Ne, sup_eq_bot_iff]
-/
@[simp] theorem sup_neBot {f g : Filter α} : NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g := by
  simp only [neBot_iff, not_and_or, Ne, sup_eq_bot_iff]

/--
Instance `neBot_sup_of_left` / 实例 `neBot_sup_of_left`

English:
instance neBot_sup_of_left
  signature: {f g : Filter α} [f.NeBot]
  body: by simp [*]

中文:
实例 neBot_sup_of_left
  签名: {f g : 滤子 α} [f.NeBot]
  定义体: by simp [*]
-/
instance neBot_sup_of_left {f g : Filter α} [f.NeBot] : NeBot (f ⊔ g) := by simp [*]
/--
Instance `neBot_sup_of_right` / 实例 `neBot_sup_of_right`

English:
instance neBot_sup_of_right
  signature: {f g : Filter α} [g.NeBot]
  body: by simp [*]

中文:
实例 neBot_sup_of_right
  签名: {f g : 滤子 α} [g.NeBot]
  定义体: by simp [*]
-/
instance neBot_sup_of_right {f g : Filter α} [g.NeBot] : NeBot (f ⊔ g) := by simp [*]

/--
theorem `not_disjoint_self_iff` / 定理 `not_disjoint_self_iff`

English:
theorem not_disjoint_self_iff
  statement: ¬Disjoint f f ↔ f.NeBot
  proof: by rw [disjoint_self, neBot_iff]

中文:
定理 not_disjoint_self_iff
  结论: ¬Disjoint f f ↔ f.NeBot
  证明: by rw [disjoint_self, neBot_iff]

Depends on / 依赖: disjoint_self, neBot_iff
-/
theorem not_disjoint_self_iff : ¬Disjoint f f ↔ f.NeBot := by rw [disjoint_self, neBot_iff]

/--
theorem `bot_sets_eq` / 定理 `bot_sets_eq`

English:
theorem bot_sets_eq
  statement: (⊥ : Filter α).sets = univ
  proof: rfl

中文:
定理 bot_sets_eq
  结论: (⊥ : 滤子 α).sets = univ
  证明: rfl
-/
theorem bot_sets_eq : (⊥ : Filter α).sets = univ := rfl

/--
theorem `eq_or_neBot` / 定理 `eq_or_neBot`

English:
theorem eq_or_neBot
  given: (f : Filter α)
  statement: f = ⊥ ∨ NeBot f
  proof: (eq_or_ne f ⊥).imp_right NeBot.mk

中文:
定理 eq_or_neBot
  条件: (f : 滤子 α)
  结论: f = ⊥ ∨ NeBot f
  证明: (eq_or_ne f ⊥).imp_right NeBot.mk

Depends on / 依赖: NeBot.mk, eq_or_ne, imp_right
-/
theorem eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f := (eq_or_ne f ⊥).imp_right NeBot.mk

/--
theorem `sup_sets_eq` / 定理 `sup_sets_eq`

English:
theorem sup_sets_eq
  given: {f g : Filter α}
  statement: (f ⊔ g).sets = f.sets inter g.sets
  proof: (giGenerate α).gc.u_inf

中文:
定理 sup_sets_eq
  条件: {f g : 滤子 α}
  结论: (f ⊔ g).sets = f.sets inter g.sets
  证明: (giGenerate α).gc.u_inf

Depends on / 依赖: gc.u_inf, giGenerate, u_inf
-/
theorem sup_sets_eq {f g : Filter α} : (f ⊔ g).sets = f.sets inter g.sets :=
  (giGenerate α).gc.u_inf

/--
theorem `sSup_sets_eq` / 定理 `sSup_sets_eq`

English:
theorem sSup_sets_eq
  given: {s : Set (Filter α)}
  statement: (sSup s).sets = ⋂ f in s, (f : Filter α).sets
  proof: (giGenerate α).gc.u_sInf

中文:
定理 sSup_sets_eq
  条件: {s : 集合 (滤子 α)}
  结论: (sSup s).sets = ⋂ f in s, (f : 滤子 α).sets
  证明: (giGenerate α).gc.u_sInf

Depends on / 依赖: gc.u_sInf, giGenerate, u_sInf
-/
theorem sSup_sets_eq {s : Set (Filter α)} : (sSup s).sets = ⋂ f in s, (f : Filter α).sets :=
  (giGenerate α).gc.u_sInf

/--
theorem `iSup_sets_eq` / 定理 `iSup_sets_eq`

English:
theorem iSup_sets_eq
  given: {f : ι -> Filter α}
  statement: (iSup f).sets = ⋂ i, (f i).sets
  proof: (giGenerate α).gc.u_iInf

中文:
定理 iSup_sets_eq
  条件: {f : ι -> 滤子 α}
  结论: (iSup f).sets = ⋂ i, (f i).sets
  证明: (giGenerate α).gc.u_iInf

Depends on / 依赖: gc.u_iInf, giGenerate, u_iInf
-/
theorem iSup_sets_eq {f : ι -> Filter α} : (iSup f).sets = ⋂ i, (f i).sets :=
  (giGenerate α).gc.u_iInf

/--
theorem `generate_empty` / 定理 `generate_empty`

English:
theorem generate_empty
  statement: Filter.generate ∅ = (⊤ : Filter α)
  proof: (giGenerate α).gc.l_bot

中文:
定理 generate_empty
  结论: 滤子.generate ∅ = (⊤ : 滤子 α)
  证明: (giGenerate α).gc.l_bot

Depends on / 依赖: gc.l_bot, giGenerate, l_bot
-/
theorem generate_empty : Filter.generate ∅ = (⊤ : Filter α) :=
  (giGenerate α).gc.l_bot

/--
theorem `generate_univ` / 定理 `generate_univ`

English:
theorem generate_univ
  statement: Filter.generate univ = (⊥ : Filter α)
  proof: bot_unique fun _ _ => GenerateSets.basic (mem_univ _)

中文:
定理 generate_univ
  结论: 滤子.generate univ = (⊥ : 滤子 α)
  证明: bot_unique fun _ _ => GenerateSets.basic (mem_univ _)

Depends on / 依赖: GenerateSets, GenerateSets.basic, bot_unique, mem_univ
-/
theorem generate_univ : Filter.generate univ = (⊥ : Filter α) :=
  bot_unique fun _ _ => GenerateSets.basic (mem_univ _)

/--
theorem `generate_union` / 定理 `generate_union`

English:
theorem generate_union
  given: {s t : Set (Set α)}
  proof: (giGenerate α).gc.l_sup

中文:
定理 generate_union
  条件: {s t : 集合 (集合 α)}
  证明: (giGenerate α).gc.l_sup

Depends on / 依赖: gc.l_sup, giGenerate, l_sup
-/
theorem generate_union {s t : Set (Set α)} :
    Filter.generate (s union t) = Filter.generate s ⊓ Filter.generate t :=
  (giGenerate α).gc.l_sup

/--
theorem `generate_iUnion` / 定理 `generate_iUnion`

English:
theorem generate_iUnion
  given: {s : ι -> Set (Set α)}
  proof: (giGenerate α).gc.l_iSup

@[simp]

中文:
定理 generate_iUnion
  条件: {s : ι -> 集合 (集合 α)}
  证明: (giGenerate α).gc.l_iSup

@[simp]

Depends on / 依赖: gc.l_iSup, giGenerate, l_iSup
-/
theorem generate_iUnion {s : ι -> Set (Set α)} :
    Filter.generate (⋃ i, s i) = ⨅ i, Filter.generate (s i) :=
  (giGenerate α).gc.l_iSup

@[simp]
/--
theorem `mem_sup` / 定理 `mem_sup`

English:
theorem mem_sup
  given: {f g : Filter α} {s : Set α}
  statement: s in f ⊔ g ↔ s in f ∧ s in g
  proof: Iff.rfl

中文:
定理 mem_sup
  条件: {f g : 滤子 α} {s : 集合 α}
  结论: s in f ⊔ g ↔ s in f ∧ s in g
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in f ∧ s in g :=
  Iff.rfl

/--
theorem `union_mem_sup` / 定理 `union_mem_sup`

English:
theorem union_mem_sup
  given: {f g : Filter α} {s t : Set α} (hs : s in f) (ht : t in g)
  statement: s union t in f ⊔ g
  proof: ⟨mem_of_superset hs subset_union_left, mem_of_superset ht subset_union_right⟩

@[simp]

中文:
定理 union_mem_sup
  条件: {f g : 滤子 α} {s t : 集合 α} (hs : s in f) (ht : t in g)
  结论: s union t in f ⊔ g
  证明: ⟨mem_of_superset hs subset_union_left, mem_of_superset ht subset_union_right⟩

@[simp]

Depends on / 依赖: mem_of_superset, subset_union_left, subset_union_right
-/
theorem union_mem_sup {f g : Filter α} {s t : Set α} (hs : s in f) (ht : t in g) : s union t in f ⊔ g :=
  ⟨mem_of_superset hs subset_union_left, mem_of_superset ht subset_union_right⟩

@[simp]
/--
theorem `mem_iSup` / 定理 `mem_iSup`

English:
theorem mem_iSup
  given: {x : Set α} {f : ι -> Filter α}
  statement: x in iSup f ↔ forall i, x in f i
  proof: by
  simp only [← Filter.mem_sets, iSup_sets_eq, mem_iInter]

@[simp]

中文:
定理 mem_iSup
  条件: {x : 集合 α} {f : ι -> 滤子 α}
  结论: x in iSup f ↔ 对任意 i, x in f i
  证明: by
  simp only [← Filter.mem_sets, iSup_sets_eq, mem_iInter]

@[simp]

Depends on / 依赖: Filter, Filter.mem_sets, iSup_sets_eq, mem_iInter, mem_sets
-/
theorem mem_iSup {x : Set α} {f : ι -> Filter α} : x in iSup f ↔ forall i, x in f i := by
  simp only [← Filter.mem_sets, iSup_sets_eq, mem_iInter]

@[simp]
/--
theorem `iSup_neBot` / 定理 `iSup_neBot`

English:
theorem iSup_neBot
  given: {f : ι -> Filter α}
  statement: (⨆ i, f i).NeBot ↔ exists i, (f i).NeBot
  proof: by
  simp [neBot_iff]

中文:
定理 iSup_neBot
  条件: {f : ι -> 滤子 α}
  结论: (⨆ i, f i).NeBot ↔ 存在 i, (f i).NeBot
  证明: by
  simp [neBot_iff]

Depends on / 依赖: neBot_iff
-/
theorem iSup_neBot {f : ι -> Filter α} : (⨆ i, f i).NeBot ↔ exists i, (f i).NeBot := by
  simp [neBot_iff]

/--
theorem `iInf_eq_generate` / 定理 `iInf_eq_generate`

English:
theorem iInf_eq_generate
  given: (s : ι -> Filter α)
  statement: iInf s = generate (⋃ i, (s i).sets)
  proof: eq_of_forall_le_iff fun _ => by simp [le_generate_iff]

中文:
定理 iInf_eq_generate
  条件: (s : ι -> 滤子 α)
  结论: iInf s = generate (⋃ i, (s i).sets)
  证明: eq_of_forall_le_iff fun _ => by simp [le_generate_iff]

Depends on / 依赖: eq_of_forall_le_iff, le_generate_iff
-/
theorem iInf_eq_generate (s : ι -> Filter α) : iInf s = generate (⋃ i, (s i).sets) :=
  eq_of_forall_le_iff fun _ => by simp [le_generate_iff]

/--
theorem `mem_iInf_of_mem` / 定理 `mem_iInf_of_mem`

English:
theorem mem_iInf_of_mem
  given: {f : ι -> Filter α} (i : ι) {s} (hs : s in f i)
  statement: s in ⨅ i, f i
  proof: iInf_le f i hs

@[elab_as_elim]

中文:
定理 mem_iInf_of_mem
  条件: {f : ι -> 滤子 α} (i : ι) {s} (hs : s in f i)
  结论: s in ⨅ i, f i
  证明: iInf_le f i hs

@[elab_as_elim]

Depends on / 依赖: iInf_le
-/
theorem mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} (hs : s in f i) : s in ⨅ i, f i :=
  iInf_le f i hs

@[elab_as_elim]
/--
theorem `iInf_sets_induct` / 定理 `iInf_sets_induct`

English:
theorem iInf_sets_induct
  statement: {f : ι -> Filter α} {s : Set α} (hs : s in iInf f) {p : Set α -> Prop}
  proof: by
  have p_of_f : forall i, forall s in f i, p s := fun i s hs => by simpa using ins hs uni
  let q : Set α -> Prop := fun t => t in iInf f ∧ forall t', t subseteq t' -> p t'
  have q_mono : Monotone q := fun a b hab ha =>
    ⟨mem_of_superset ha.1 hab, fun t hbt => ha.2 _ (hab.trans hbt)⟩
  have A : forall i, forall s in f i, forall t, q t -> q (s inter t) := fun i s hs t ht => by
    use inter_mem (mem_iInf_of_mem _ hs) ht.1
    intro u hu
    have : u = (u union s) inter (u union t) := by
      rwa [← union_eq_left, union_inter_distrib_left, eq_comm] at hu
    rw [this]
    exact ins (mem_of_superset hs subset_union_right) (ht.2 _ subset_union_right)
  have B : forall s t, q s -> q t -> q (s inter t) := fun s t hqs hqt => by
    let 𝓕 : Filter α :=
    { sets := {s | forall t, q t -> q (s inter t)}
      univ_sets := by simp
      sets_of_superset ha hab t ht := q_mono (inter_subset_inter_left _ hab) (ha t ht)
      inter_sets ha hb t ht := by simpa [inter_assoc] using ha _ (hb _ ht) }
    exact (le_iInf_iff.mpr A : 𝓕 <= iInf f) hqs.1 _ hqt
  have C : forall i, forall s in f i, q s := fun i s hs =>
    ⟨mem_iInf_of_mem _ hs, fun t hst => p_of_f _ _ (mem_of_superset hs hst)⟩
  let 𝓖 : Filter α :=
  { sets := {t | q t}
    univ_sets := by simpa [q] using uni
    sets_of_superset ha hab :=
      ⟨mem_of_superset ha.1 hab, fun t hbt => ha.2 _ (hab.trans hbt)⟩
    inter_sets := B _ _ }
  have : 𝓖 <= iInf f := le_iInf_iff.mpr C
  exact (this hs).2 s subset_rfl

@[simp]

中文:
定理 iInf_sets_induct
  结论: {f : ι -> 滤子 α} {s : 集合 α} (hs : s in iInf f) {p : 集合 α -> 命题}
  证明: by
  have p_of_f : forall i, forall s in f i, p s := fun i s hs => by simpa using ins hs uni
  let q : Set α -> Prop := fun t => t in iInf f ∧ forall t', t subseteq t' -> p t'
  have q_mono : Monotone q := fun a b hab ha =>
    ⟨mem_of_superset ha.1 hab, fun t hbt => ha.2 _ (hab.trans hbt)⟩
  have A : forall i, forall s in f i, forall t, q t -> q (s inter t) := fun i s hs t ht => by
    use inter_mem (mem_iInf_of_mem _ hs) ht.1
    intro u hu
    have : u = (u union s) inter (u union t) := by
      rwa [← union_eq_left, union_inter_distrib_left, eq_comm] at hu
    rw [this]
    exact ins (mem_of_superset hs subset_union_right) (ht.2 _ subset_union_right)
  have B : forall s t, q s -> q t -> q (s inter t) := fun s t hqs hqt => by
    let 𝓕 : Filter α :=
    { sets := {s | forall t, q t -> q (s inter t)}
      univ_sets := by simp
      sets_of_superset ha hab t ht := q_mono (inter_subset_inter_left _ hab) (ha t ht)
      inter_sets ha hb t ht := by simpa [inter_assoc] using ha _ (hb _ ht) }
    exact (le_iInf_iff.mpr A : 𝓕 <= iInf f) hqs.1 _ hqt
  have C : forall i, forall s in f i, q s := fun i s hs =>
    ⟨mem_iInf_of_mem _ hs, fun t hst => p_of_f _ _ (mem_of_superset hs hst)⟩
  let 𝓖 : Filter α :=
  { sets := {t | q t}
    univ_sets := by simpa [q] using uni
    sets_of_superset ha hab :=
      ⟨mem_of_superset ha.1 hab, fun t hbt => ha.2 _ (hab.trans hbt)⟩
    inter_sets := B _ _ }
  have : 𝓖 <= iInf f := le_iInf_iff.mpr C
  exact (this hs).2 s subset_rfl

@[simp]

Depends on / 依赖: Monotone, hab.trans, inter_mem, mem_iInf_of_mem, mem_of_superset, p_of_f, q_mono, subseteq, union_eq_left
-/
theorem iInf_sets_induct {f : ι -> Filter α} {s : Set α} (hs : s in iInf f) {p : Set α -> Prop}
    (uni : p univ) (ins : forall {i s₁ s₂}, s₁ in f i -> p s₂ -> p (s₁ inter s₂)) : p s := by
  have p_of_f : forall i, forall s in f i, p s := fun i s hs => by simpa using ins hs uni
  let q : Set α -> Prop := fun t => t in iInf f ∧ forall t', t subseteq t' -> p t'
  have q_mono : Monotone q := fun a b hab ha =>
    ⟨mem_of_superset ha.1 hab, fun t hbt => ha.2 _ (hab.trans hbt)⟩
  have A : forall i, forall s in f i, forall t, q t -> q (s inter t) := fun i s hs t ht => by
    use inter_mem (mem_iInf_of_mem _ hs) ht.1
    intro u hu
    have : u = (u union s) inter (u union t) := by
      rwa [← union_eq_left, union_inter_distrib_left, eq_comm] at hu
    rw [this]
    exact ins (mem_of_superset hs subset_union_right) (ht.2 _ subset_union_right)
  have B : forall s t, q s -> q t -> q (s inter t) := fun s t hqs hqt => by
    let 𝓕 : Filter α :=
    { sets := {s | forall t, q t -> q (s inter t)}
      univ_sets := by simp
      sets_of_superset ha hab t ht := q_mono (inter_subset_inter_left _ hab) (ha t ht)
      inter_sets ha hb t ht := by simpa [inter_assoc] using ha _ (hb _ ht) }
    exact (le_iInf_iff.mpr A : 𝓕 <= iInf f) hqs.1 _ hqt
  have C : forall i, forall s in f i, q s := fun i s hs =>
    ⟨mem_iInf_of_mem _ hs, fun t hst => p_of_f _ _ (mem_of_superset hs hst)⟩
  let 𝓖 : Filter α :=
  { sets := {t | q t}
    univ_sets := by simpa [q] using uni
    sets_of_superset ha hab :=
      ⟨mem_of_superset ha.1 hab, fun t hbt => ha.2 _ (hab.trans hbt)⟩
    inter_sets := B _ _ }
  have : 𝓖 <= iInf f := le_iInf_iff.mpr C
  exact (this hs).2 s subset_rfl

@[simp]
/--
theorem `le_principal_iff` / 定理 `le_principal_iff`

English:
theorem le_principal_iff
  given: {s : Set α} {f : Filter α}
  statement: f <= 𝓟 s ↔ s in f
  proof: ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩

中文:
定理 le_principal_iff
  条件: {s : 集合 α} {f : 滤子 α}
  结论: f <= 𝓟 s ↔ s in f
  证明: ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩

Depends on / 依赖: Subset, Subset.rfl, mem_of_superset
-/
theorem le_principal_iff {s : Set α} {f : Filter α} : f <= 𝓟 s ↔ s in f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩

/--
theorem `Iic_principal` / 定理 `Iic_principal`

English:
theorem Iic_principal
  given: (s : Set α)
  statement: Iic (𝓟 s) = { l | s in l }
  proof: Set.ext fun _ => le_principal_iff

@[gcongr]

中文:
定理 Iic_principal
  条件: (s : 集合 α)
  结论: 左无界右闭区间 (𝓟 s) = { l | s in l }
  证明: Set.ext fun _ => le_principal_iff

@[gcongr]

Depends on / 依赖: Set.ext, le_principal_iff
-/
theorem Iic_principal (s : Set α) : Iic (𝓟 s) = { l | s in l } :=
  Set.ext fun _ => le_principal_iff

@[gcongr]
/--
theorem `principal_mono` / 定理 `principal_mono`

English:
theorem principal_mono
  given: {s t : Set α}
  statement: 𝓟 s <= 𝓟 t ↔ s subseteq t
  proof: by
  simp only [le_principal_iff, mem_principal]

@[mono]

中文:
定理 principal_mono
  条件: {s t : 集合 α}
  结论: 𝓟 s <= 𝓟 t ↔ s subseteq t
  证明: by
  simp only [le_principal_iff, mem_principal]

@[mono]

Depends on / 依赖: le_principal_iff, mem_principal
-/
theorem principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s subseteq t := by
  simp only [le_principal_iff, mem_principal]

@[mono]
/--
theorem `monotone_principal` / 定理 `monotone_principal`

English:
theorem monotone_principal
  statement: Monotone (𝓟 : Set α -> Filter α)
  proof: fun _ _ => principal_mono.2

中文:
定理 monotone_principal
  结论: 递增 (𝓟 : 集合 α -> 滤子 α)
  证明: fun _ _ => principal_mono.2

Depends on / 依赖: principal_mono
-/
theorem monotone_principal : Monotone (𝓟 : Set α -> Filter α) := fun _ _ => principal_mono.2

/--
theorem `principal_eq_iff_eq` / 定理 `principal_eq_iff_eq`

English:
theorem principal_eq_iff_eq
  given: {s t : Set α}
  statement: 𝓟 s = 𝓟 t ↔ s = t
  proof: by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal]

中文:
定理 principal_eq_iff_eq
  条件: {s t : 集合 α}
  结论: 𝓟 s = 𝓟 t ↔ s = t
  证明: by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal]
-/
@[simp] theorem principal_eq_iff_eq {s t : Set α} : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal]

/--
theorem `join_principal_eq_sSup` / 定理 `join_principal_eq_sSup`

English:
theorem join_principal_eq_sSup
  given: {s : Set (Filter α)}
  statement: join (𝓟 s) = sSup s
  proof: rfl

中文:
定理 join_principal_eq_sSup
  条件: {s : 集合 (滤子 α)}
  结论: join (𝓟 s) = sSup s
  证明: rfl
-/
@[simp] theorem join_principal_eq_sSup {s : Set (Filter α)} : join (𝓟 s) = sSup s := rfl

/--
theorem `principal_univ` / 定理 `principal_univ`

English:
theorem principal_univ
  statement: 𝓟 (univ : Set α) = ⊤
  proof: top_unique by simp only [le_principal_iff, mem_top]

@[simp]

中文:
定理 principal_univ
  结论: 𝓟 (univ : 集合 α) = ⊤
  证明: top_unique by simp only [le_principal_iff, mem_top]

@[simp]
-/
@[simp] theorem principal_univ : 𝓟 (univ : Set α) = ⊤ :=
top_unique by simp only [le_principal_iff, mem_top]

@[simp]
/--
theorem `principal_empty` / 定理 `principal_empty`

English:
theorem principal_empty
  statement: 𝓟 (∅ : Set α) = ⊥
  proof: bot_unique fun _ _ => empty_subset _

中文:
定理 principal_empty
  结论: 𝓟 (∅ : 集合 α) = ⊥
  证明: bot_unique fun _ _ => empty_subset _

Depends on / 依赖: bot_unique, empty_subset
-/
theorem principal_empty : 𝓟 (∅ : Set α) = ⊥ :=
  bot_unique fun _ _ => empty_subset _

/--
theorem `generate_eq_biInf` / 定理 `generate_eq_biInf`

English:
theorem generate_eq_biInf
  given: (S : Set (Set α))
  statement: generate S = ⨅ s in S, 𝓟 s
  proof: eq_of_forall_le_iff fun f => by simp [le_generate_iff, le_principal_iff, subset_def]

中文:
定理 generate_eq_biInf
  条件: (S : 集合 (集合 α))
  结论: generate S = ⨅ s in S, 𝓟 s
  证明: eq_of_forall_le_iff fun f => by simp [le_generate_iff, le_principal_iff, subset_def]

Depends on / 依赖: eq_of_forall_le_iff, le_generate_iff, le_principal_iff, subset_def
-/
theorem generate_eq_biInf (S : Set (Set α)) : generate S = ⨅ s in S, 𝓟 s :=
  eq_of_forall_le_iff fun f => by simp [le_generate_iff, le_principal_iff, subset_def]


/--
theorem `empty_mem_iff_bot` / 定理 `empty_mem_iff_bot`

English:
theorem empty_mem_iff_bot
  given: {f : Filter α}
  statement: ∅ in f ↔ f = ⊥
  proof: ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩

中文:
定理 empty_mem_iff_bot
  条件: {f : 滤子 α}
  结论: ∅ in f ↔ f = ⊥
  证明: ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩

Depends on / 依赖: bot_unique, empty_subset, h.symm, mem_bot, mem_of_superset
-/
theorem empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f = ⊥ :=
  ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩

/--
theorem `nonempty_of_mem` / 定理 `nonempty_of_mem`

English:
theorem nonempty_of_mem
  given: {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s in f)
  statement: s.Nonempty
  proof: s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id

中文:
定理 nonempty_of_mem
  条件: {f : 滤子 α} [hf : NeBot f] {s : 集合 α} (hs : s in f)
  结论: s.非空
  证明: s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id

Depends on / 依赖: absurd, empty_mem_iff_bot, empty_mem_iff_bot.mp, eq_empty_or_nonempty, h.symm, s.eq_empty_or_nonempty.elim
-/
theorem nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s in f) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id

/--
theorem `NeBot.nonempty_of_mem` / 定理 `NeBot.nonempty_of_mem`

English:
theorem NeBot.nonempty_of_mem
  given: {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s in f)
  statement: s.Nonempty
  proof: @Filter.nonempty_of_mem α f hf s hs

@[simp]

中文:
定理 NeBot.nonempty_of_mem
  条件: {f : 滤子 α} (hf : NeBot f) {s : 集合 α} (hs : s in f)
  结论: s.非空
  证明: @Filter.nonempty_of_mem α f hf s hs

@[simp]

Depends on / 依赖: Filter, Filter.nonempty_of_mem, nonempty_of_mem
-/
theorem NeBot.nonempty_of_mem {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s in f) : s.Nonempty :=
  @Filter.nonempty_of_mem α f hf s hs

@[simp]
/--
theorem `empty_notMem` / 定理 `empty_notMem`

English:
theorem empty_notMem
  given: (f : Filter α) [NeBot f]
  statement: ∅ ∉ f
  proof: fun h => (nonempty_of_mem h).ne_empty rfl

中文:
定理 empty_notMem
  条件: (f : 滤子 α) [NeBot f]
  结论: ∅ ∉ f
  证明: fun h => (nonempty_of_mem h).ne_empty rfl

Depends on / 依赖: ne_empty, nonempty_of_mem
-/
theorem empty_notMem (f : Filter α) [NeBot f] : ∅ ∉ f := fun h => (nonempty_of_mem h).ne_empty rfl

/--
theorem `nonempty_of_neBot` / 定理 `nonempty_of_neBot`

English:
theorem nonempty_of_neBot
  given: (f : Filter α) [NeBot f]
  statement: Nonempty α
  proof: Exists.nonempty nonempty_of_mem (univ_mem : univ in f)

中文:
定理 nonempty_of_neBot
  条件: (f : 滤子 α) [NeBot f]
  结论: 非空 α
  证明: Exists.nonempty nonempty_of_mem (univ_mem : univ in f)

Depends on / 依赖: Exists, Exists.nonempty, nonempty, nonempty_of_mem, univ_mem
-/
theorem nonempty_of_neBot (f : Filter α) [NeBot f] : Nonempty α :=
Exists.nonempty nonempty_of_mem (univ_mem : univ in f)

/--
theorem `compl_notMem` / 定理 `compl_notMem`

English:
theorem compl_notMem
  given: {f : Filter α} {s : Set α} [NeBot f] (h : s in f)
  statement: sᶜ ∉ f
  proof: fun hsc =>
(nonempty_of_mem (inter_mem h hsc)).ne_empty inter_compl_self s

中文:
定理 compl_notMem
  条件: {f : 滤子 α} {s : 集合 α} [NeBot f] (h : s in f)
  结论: sᶜ ∉ f
  证明: fun hsc =>
(nonempty_of_mem (inter_mem h hsc)).ne_empty inter_compl_self s

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, mkLinearMap, of_isLocalization
-/
theorem compl_notMem {f : Filter α} {s : Set α} [NeBot f] (h : s in f) : sᶜ ∉ f := fun hsc =>
(nonempty_of_mem (inter_mem h hsc)).ne_empty inter_compl_self s

/--
theorem `filter_eq_bot_of_isEmpty` / 定理 `filter_eq_bot_of_isEmpty`

English:
theorem filter_eq_bot_of_isEmpty
  given: [IsEmpty α] (f : Filter α)
  statement: f = ⊥
  proof: empty_mem_iff_bot.mp univ_mem' isEmptyElim

中文:
定理 filter_eq_bot_of_isEmpty
  条件: [是空 α] (f : 滤子 α)
  结论: f = ⊥
  证明: empty_mem_iff_bot.mp univ_mem' isEmptyElim

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, cancelBaseChange, empty_mem_iff_bot, empty_mem_iff_bot.mp, isEmptyElim, univ_mem
-/
theorem filter_eq_bot_of_isEmpty [IsEmpty α] (f : Filter α) : f = ⊥ :=
empty_mem_iff_bot.mp univ_mem' isEmptyElim

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: {f g : Filter α}
  statement: Disjoint f g ↔ exists s in f, exists t in g, Disjoint s t
  proof: by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]

中文:
引理 disjoint_iff
  条件: {f g : 滤子 α}
  结论: Disjoint f g ↔ 存在 s in f, 存在 t in g, Disjoint s t
  证明: by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]
-/
protected lemma disjoint_iff {f g : Filter α} : Disjoint f g ↔ exists s in f, exists t in g, Disjoint s t := by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]

/--
theorem `disjoint_of_disjoint_of_mem` / 定理 `disjoint_of_disjoint_of_mem`

English:
theorem disjoint_of_disjoint_of_mem
  statement: {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s in f)
  proof: Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩

中文:
定理 disjoint_of_disjoint_of_mem
  结论: {f g : 滤子 α} {s t : 集合 α} (h : Disjoint s t) (hs : s in f)
  证明: Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩

Depends on / 依赖: Filter, Filter.disjoint_iff.mpr, M.inv_mul, Quotient, Quotient.eq.mp, disjoint_iff, inv_mul, some.toLinearEquiv
-/
theorem disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s in f)
    (ht : t in g) : Disjoint f g :=
  Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩

/--
theorem `NeBot.not_disjoint` / 定理 `NeBot.not_disjoint`

English:
theorem NeBot.not_disjoint
  given: (hf : f.NeBot) (hs : s in f) (ht : t in f)
  statement: ¬Disjoint s t
  proof: fun h =>
not_disjoint_self_iff.2 hf Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩

中文:
定理 NeBot.not_disjoint
  条件: (hf : f.NeBot) (hs : s in f) (ht : t in f)
  结论: ¬Disjoint s t
  证明: fun h =>
not_disjoint_self_iff.2 hf Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩

Depends on / 依赖: M.inv_mul, Quotient, Quotient.eq.mp, inv_mul, some.toLinearEquiv, toLinearEquiv
-/
theorem NeBot.not_disjoint (hf : f.NeBot) (hs : s in f) (ht : t in f) : ¬Disjoint s t := fun h =>
not_disjoint_self_iff.2 hf Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩

/--
theorem `inf_eq_bot_iff` / 定理 `inf_eq_bot_iff`

English:
theorem inf_eq_bot_iff
  given: {f g : Filter α}
  statement: f ⊓ g = ⊥ ↔ exists U in f, exists V in g, U inter V = ∅
  proof: by
  simp only [← disjoint_iff, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty]

中文:
定理 inf_eq_bot_iff
  条件: {f g : 滤子 α}
  结论: f ⊓ g = ⊥ ↔ 存在 U in f, 存在 V in g, U inter V = ∅
  证明: by
  simp only [← disjoint_iff, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty]

Depends on / 依赖: Filter, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty, disjoint_iff, disjoint_iff_inter_eq_empty
-/
theorem inf_eq_bot_iff {f g : Filter α} : f ⊓ g = ⊥ ↔ exists U in f, exists V in g, U inter V = ∅ := by
  simp only [← disjoint_iff, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty]

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [IsEmpty α]
  body: ⊥
  uniq := filter_eq_bot_of_isEmpty

中文:
实例 unique
  签名: [是空 α]
  定义体: ⊥
  uniq := filter_eq_bot_of_isEmpty

Depends on / 依赖: ModuleCat, ModuleCat.equivalenceSemimoduleCat, Skeleton, Skeleton.mulEquiv, Units.mapEquiv, equivalenceSemimoduleCat, mapEquiv, mulEquiv, small_map, toEquiv
-/
instance unique [IsEmpty α] : Unique (Filter α) where
  default := ⊥
  uniq := filter_eq_bot_of_isEmpty

/--
theorem `NeBot.nonempty` / 定理 `NeBot.nonempty`

English:
theorem NeBot.nonempty
  given: (f : Filter α) [hf : f.NeBot]
  statement: Nonempty α
  proof: not_isEmpty_iff.mp fun _ => hf.ne (Subsingleton.elim _ _)

中文:
定理 NeBot.nonempty
  条件: (f : 滤子 α) [hf : f.NeBot]
  结论: 非空 α
  证明: not_isEmpty_iff.mp fun _ => hf.ne (Subsingleton.elim _ _)

Depends on / 依赖: Subsingleton, Subsingleton.elim, hf.ne, not_isEmpty_iff, not_isEmpty_iff.mp
-/
theorem NeBot.nonempty (f : Filter α) [hf : f.NeBot] : Nonempty α :=
  not_isEmpty_iff.mp fun _ => hf.ne (Subsingleton.elim _ _)

/--
theorem `eq_top_of_neBot` / 定理 `eq_top_of_neBot`

English:
theorem eq_top_of_neBot
  given: [Subsingleton α] (l : Filter α) [NeBot l]
  statement: l = ⊤
  proof: by
  refine top_unique fun s hs => ?_
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem

中文:
定理 eq_top_of_neBot
  条件: [子单例 α] (l : 滤子 α) [NeBot l]
  结论: l = ⊤
  证明: by
  refine top_unique fun s hs => ?_
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem

Depends on / 依赖: Subsingleton, Subsingleton.eq_univ_of_nonempty, eq_univ_of_nonempty, nonempty_of_mem, top_unique, univ_mem
-/
theorem eq_top_of_neBot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤ := by
  refine top_unique fun s hs => ?_
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem

/--
theorem `forall_mem_nonempty_iff_neBot` / 定理 `forall_mem_nonempty_iff_neBot`

English:
theorem forall_mem_nonempty_iff_neBot
  given: {f : Filter α}
  proof: ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩

中文:
定理 对任意_mem_nonempty_iff_neBot
  条件: {f : 滤子 α}
  证明: ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩

Depends on / 依赖: hf.symm, mem_bot, nonempty_of_mem, not_nonempty_empty
-/
theorem forall_mem_nonempty_iff_neBot {f : Filter α} :
    (forall s : Set α, s in f -> s.Nonempty) ↔ NeBot f :=
  ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩

/--
Instance `instNeBotTop` / 实例 `instNeBotTop`

English:
instance instNeBotTop
  signature: [Nonempty α]
  body: forall_mem_nonempty_iff_neBot.1 fun s hs => by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]

中文:
实例 instNeBotTop
  签名: [非空 α]
  定义体: forall_mem_nonempty_iff_neBot.1 fun s hs => by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]

Depends on / 依赖: forall_mem_nonempty_iff_neBot, mem_top, nonempty_iff_univ_nonempty
-/
instance instNeBotTop [Nonempty α] : NeBot (⊤ : Filter α) :=
  forall_mem_nonempty_iff_neBot.1 fun s hs => by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]

/--
Instance `instNontrivialFilter` / 实例 `instNontrivialFilter`

English:
instance instNontrivialFilter
  signature: [Nonempty α]
  body: ⟨⟨⊤, ⊥, instNeBotTop.ne⟩⟩

中文:
实例 instNontrivialFilter
  签名: [非空 α]
  定义体: ⟨⟨⊤, ⊥, instNeBotTop.ne⟩⟩

Depends on / 依赖: instNeBotTop, instNeBotTop.ne
-/
instance instNontrivialFilter [Nonempty α] : Nontrivial (Filter α) :=
  ⟨⟨⊤, ⊥, instNeBotTop.ne⟩⟩

/--
theorem `nontrivial_iff_nonempty` / 定理 `nontrivial_iff_nonempty`

English:
theorem nontrivial_iff_nonempty
  statement: Nontrivial (Filter α) ↔ Nonempty α
  proof: ⟨fun _ =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.instNontrivialFilter α⟩

中文:
定理 nontrivial_iff_nonempty
  结论: 非平凡 (滤子 α) ↔ 非空 α
  证明: ⟨fun _ =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.instNontrivialFilter α⟩

Depends on / 依赖: Filter, Filter.instNontrivialFilter, Module, Module.addCommMonoidToAddCommGroup, addCommMonoidToAddCommGroup, instNontrivialFilter, not_nonempty_iff, not_subsingleton
-/
theorem nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α :=
  ⟨fun _ =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.instNontrivialFilter α⟩

/--
theorem `eq_sInf_of_mem_iff_exists_mem` / 定理 `eq_sInf_of_mem_iff_exists_mem`

English:
theorem eq_sInf_of_mem_iff_exists_mem
  statement: {S : Set (Filter α)} {l : Filter α}
  proof: le_antisymm (le_sInf fun f hf _ hs => h.2 ⟨f, hf, hs⟩)
    fun _ hs => let ⟨_, hf, hs⟩ := h.1 hs; (sInf_le hf) hs

中文:
定理 eq_sInf_of_mem_iff_存在_mem
  结论: {S : 集合 (滤子 α)} {l : 滤子 α}
  证明: le_antisymm (le_sInf fun f hf _ hs => h.2 ⟨f, hf, hs⟩)
    fun _ hs => let ⟨_, hf, hs⟩ := h.1 hs; (sInf_le hf) hs

Depends on / 依赖: le_antisymm, le_sInf, sInf_le
-/
theorem eq_sInf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α}
    (h : forall {s}, s in l ↔ exists f in S, s in f) : l = sInf S :=
  le_antisymm (le_sInf fun f hf _ hs => h.2 ⟨f, hf, hs⟩)
    fun _ hs => let ⟨_, hf, hs⟩ := h.1 hs; (sInf_le hf) hs

/--
theorem `eq_iInf_of_mem_iff_exists_mem` / 定理 `eq_iInf_of_mem_iff_exists_mem`

English:
theorem eq_iInf_of_mem_iff_exists_mem
  statement: {f : ι -> Filter α} {l : Filter α}
  proof: eq_sInf_of_mem_iff_exists_mem h.trans (exists_range_iff (p := (_ in ·))).symm

中文:
定理 eq_iInf_of_mem_iff_存在_mem
  结论: {f : ι -> 滤子 α} {l : 滤子 α}
  证明: eq_sInf_of_mem_iff_exists_mem h.trans (exists_range_iff (p := (_ in ·))).symm

Depends on / 依赖: eq_sInf_of_mem_iff_exists_mem, exists_range_iff, h.trans
-/
theorem eq_iInf_of_mem_iff_exists_mem {f : ι -> Filter α} {l : Filter α}
    (h : forall {s}, s in l ↔ exists i, s in f i) : l = iInf f :=
eq_sInf_of_mem_iff_exists_mem h.trans (exists_range_iff (p := (_ in ·))).symm

/--
theorem `eq_biInf_of_mem_iff_exists_mem` / 定理 `eq_biInf_of_mem_iff_exists_mem`

English:
theorem eq_biInf_of_mem_iff_exists_mem
  statement: {f : ι -> Filter α} {p : ι -> Prop} {l : Filter α}
  proof: by
  rw [iInf_subtype']
  exact eq_iInf_of_mem_iff_exists_mem fun {_} => by simp only [Subtype.exists, h, exists_prop]

中文:
定理 eq_biInf_of_mem_iff_存在_mem
  结论: {f : ι -> 滤子 α} {p : ι -> 命题} {l : 滤子 α}
  证明: by
  rw [iInf_subtype']
  exact eq_iInf_of_mem_iff_exists_mem fun {_} => by simp only [Subtype.exists, h, exists_prop]

Depends on / 依赖: Subtype, Subtype.exists, eq_iInf_of_mem_iff_exists_mem, exists_prop, iInf_subtype
-/
theorem eq_biInf_of_mem_iff_exists_mem {f : ι -> Filter α} {p : ι -> Prop} {l : Filter α}
    (h : forall {s}, s in l ↔ exists i, p i ∧ s in f i) : l = ⨅ (i) (_ : p i), f i := by
  rw [iInf_subtype']
  exact eq_iInf_of_mem_iff_exists_mem fun {_} => by simp only [Subtype.exists, h, exists_prop]

/--
theorem `iInf_sets_eq` / 定理 `iInf_sets_eq`

English:
theorem iInf_sets_eq
  given: {f : ι -> Filter α} (h : Directed (· >= ·) f) [ne : Nonempty ι]
  proof: let ⟨i⟩ := ne
  let u :=
    { sets := ⋃ i, (f i).sets
      univ_sets := mem_iUnion.2 ⟨i, univ_mem⟩
      sets_of_superset := by
        simp only [mem_iUnion, exists_imp]
        exact fun i hx hxy => ⟨i, mem_of_superset hx hxy⟩
      inter_sets := by
        simp only [mem_iUnion, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = iInf f := eq_iInf_of_mem_iff_exists_mem mem_iUnion
  congr_arg Filter.sets this.symm

中文:
定理 iInf_sets_eq
  条件: {f : ι -> 滤子 α} (h : Directed (· >= ·) f) [ne : 非空 ι]
  证明: let ⟨i⟩ := ne
  let u :=
    { sets := ⋃ i, (f i).sets
      univ_sets := mem_iUnion.2 ⟨i, univ_mem⟩
      sets_of_superset := by
        simp only [mem_iUnion, exists_imp]
        exact fun i hx hxy => ⟨i, mem_of_superset hx hxy⟩
      inter_sets := by
        simp only [mem_iUnion, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = iInf f := eq_iInf_of_mem_iff_exists_mem mem_iUnion
  congr_arg Filter.sets this.symm

Depends on / 依赖: Filter, Filter.sets, congr_arg, eq_iInf_of_mem_iff_exists_mem, exists_imp, inter_mem, inter_sets, mem_iUnion, mem_of_superset, sets_of_superset, this.symm, univ_mem, univ_sets
-/
theorem iInf_sets_eq {f : ι -> Filter α} (h : Directed (· >= ·) f) [ne : Nonempty ι] :
    (iInf f).sets = ⋃ i, (f i).sets :=
  let ⟨i⟩ := ne
  let u :=
    { sets := ⋃ i, (f i).sets
      univ_sets := mem_iUnion.2 ⟨i, univ_mem⟩
      sets_of_superset := by
        simp only [mem_iUnion, exists_imp]
        exact fun i hx hxy => ⟨i, mem_of_superset hx hxy⟩
      inter_sets := by
        simp only [mem_iUnion, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = iInf f := eq_iInf_of_mem_iff_exists_mem mem_iUnion
  congr_arg Filter.sets this.symm

/--
theorem `mem_iInf_of_directed` / 定理 `mem_iInf_of_directed`

English:
theorem mem_iInf_of_directed
  given: {f : ι -> Filter α} (h : Directed (· >= ·) f) [Nonempty ι] (s)
  proof: by
  simp only [← Filter.mem_sets, iInf_sets_eq h, mem_iUnion]

中文:
定理 mem_iInf_of_directed
  条件: {f : ι -> 滤子 α} (h : Directed (· >= ·) f) [非空 ι] (s)
  证明: by
  simp only [← Filter.mem_sets, iInf_sets_eq h, mem_iUnion]

Depends on / 依赖: Filter, Filter.mem_sets, iInf_sets_eq, mem_iUnion, mem_sets
-/
theorem mem_iInf_of_directed {f : ι -> Filter α} (h : Directed (· >= ·) f) [Nonempty ι] (s) :
    s in iInf f ↔ exists i, s in f i := by
  simp only [← Filter.mem_sets, iInf_sets_eq h, mem_iUnion]

/--
theorem `mem_biInf_of_directed` / 定理 `mem_biInf_of_directed`

English:
theorem mem_biInf_of_directed
  statement: {f : β -> Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s)
  proof: by
  have := ne.to_subtype
  simp_rw [iInf_subtype', mem_iInf_of_directed h.directed_val, Subtype.exists, exists_prop]

中文:
定理 mem_biInf_of_directed
  结论: {f : β -> 滤子 α} {s : 集合 β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s)
  证明: by
  have := ne.to_subtype
  simp_rw [iInf_subtype', mem_iInf_of_directed h.directed_val, Subtype.exists, exists_prop]

Depends on / 依赖: Subtype, Subtype.exists, directed_val, exists_prop, h.directed_val, iInf_subtype, mem_iInf_of_directed, ne.to_subtype, simp_rw, to_subtype
-/
theorem mem_biInf_of_directed {f : β -> Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s)
    (ne : s.Nonempty) {t : Set α} : (t in ⨅ i in s, f i) ↔ exists i in s, t in f i := by
  have := ne.to_subtype
  simp_rw [iInf_subtype', mem_iInf_of_directed h.directed_val, Subtype.exists, exists_prop]

/--
theorem `biInf_sets_eq` / 定理 `biInf_sets_eq`

English:
theorem biInf_sets_eq
  statement: {f : β -> Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s)
  proof: ext fun t => by simp [mem_biInf_of_directed h ne]

@[simp]

中文:
定理 biInf_sets_eq
  结论: {f : β -> 滤子 α} {s : 集合 β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s)
  证明: ext fun t => by simp [mem_biInf_of_directed h ne]

@[simp]

Depends on / 依赖: mem_biInf_of_directed
-/
theorem biInf_sets_eq {f : β -> Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s)
    (ne : s.Nonempty) : (⨅ i in s, f i).sets = ⋃ i in s, (f i).sets :=
  ext fun t => by simp [mem_biInf_of_directed h ne]

@[simp]
/--
theorem `sup_join` / 定理 `sup_join`

English:
theorem sup_join
  given: {f₁ f₂ : Filter (Filter α)}
  statement: join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂)
  proof: Filter.ext fun x => by simp only [mem_sup, mem_join]

@[simp]

中文:
定理 sup_join
  条件: {f₁ f₂ : 滤子 (滤子 α)}
  结论: join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂)
  证明: Filter.ext fun x => by simp only [mem_sup, mem_join]

@[simp]

Depends on / 依赖: Filter, Filter.ext, mem_join, mem_sup
-/
theorem sup_join {f₁ f₂ : Filter (Filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂) :=
  Filter.ext fun x => by simp only [mem_sup, mem_join]

@[simp]
/--
theorem `iSup_join` / 定理 `iSup_join`

English:
theorem iSup_join
  given: {ι : Sort w} {f : ι -> Filter (Filter α)}
  statement: ⨆ x, join (f x) = join (⨆ x, f x)
  proof: Filter.ext fun x => by simp only [mem_iSup, mem_join]

中文:
定理 iSup_join
  条件: {ι : 类型层 w} {f : ι -> 滤子 (滤子 α)}
  结论: ⨆ x, join (f x) = join (⨆ x, f x)
  证明: Filter.ext fun x => by simp only [mem_iSup, mem_join]

Depends on / 依赖: Filter, Filter.ext, mem_iSup, mem_join
-/
theorem iSup_join {ι : Sort w} {f : ι -> Filter (Filter α)} : ⨆ x, join (f x) = join (⨆ x, f x) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_join]


/--
Instance `instCoframe` / 实例 `instCoframe`

English:
instance instCoframe
  signature: : Coframe (Filter α) where
  body: ⟨fun h s hs => h hs.right hs.left (subset_refl s),
      fun h s hsc t htb hst => h ⟨htb, mem_of_superset hsc hst⟩⟩
  top_sdiff f := by
    ext s
    simp only [mem_sdiff_iff_union, Filter.hnot_def, mem_principal, compl_subset_iff_union,
      mem_top_iff_forall, eq_univ_iff_forall, ker, mem_union, mem_sInter, Filter.mem_sets]
    grind

中文:
实例 instCoframe
  签名: : 余frame (滤子 α) where
  定义体: ⟨fun h s hs => h hs.right hs.left (subset_refl s),
      fun h s hsc t htb hst => h ⟨htb, mem_of_superset hsc hst⟩⟩
  top_sdiff f := by
    ext s
    simp only [mem_sdiff_iff_union, Filter.hnot_def, mem_principal, compl_subset_iff_union,
      mem_top_iff_forall, eq_univ_iff_forall, ker, mem_union, mem_sInter, Filter.mem_sets]
    grind

Depends on / 依赖: Filter, Filter.hnot_def, Filter.mem_sets, compl_subset_iff_union, eq_univ_iff_forall, hnot_def, hs.left, hs.right, mem_of_superset, mem_principal, mem_sInter, mem_sdiff_iff_union, mem_sets, mem_top_iff_forall, mem_union, subset_refl, top_sdiff
-/
instance instCoframe : Coframe (Filter α) where
  sdiff_le_iff a b c :=
    ⟨fun h s hs => h hs.right hs.left (subset_refl s),
      fun h s hsc t htb hst => h ⟨htb, mem_of_superset hsc hst⟩⟩
  top_sdiff f := by
    ext s
    simp only [mem_sdiff_iff_union, Filter.hnot_def, mem_principal, compl_subset_iff_union,
      mem_top_iff_forall, eq_univ_iff_forall, ker, mem_union, mem_sInter, Filter.mem_sets]
    grind

/--
theorem `iInf_neBot_of_directed'` / 定理 `iInf_neBot_of_directed'`

English:
theorem iInf_neBot_of_directed'
  given: {f : ι -> Filter α} [Nonempty ι] (hd : Directed (· >= ·) f)
  proof: not_imp_not.1 by simpa only [not_forall, not_neBot, ← empty_mem_iff_bot,
    mem_iInf_of_directed hd] using id

中文:
定理 iInf_neBot_of_directed'
  条件: {f : ι -> 滤子 α} [非空 ι] (hd : Directed (· >= ·) f)
  证明: not_imp_not.1 by simpa only [not_forall, not_neBot, ← empty_mem_iff_bot,
    mem_iInf_of_directed hd] using id

Depends on / 依赖: empty_mem_iff_bot, mem_iInf_of_directed, not_forall, not_imp_not, not_neBot
-/
theorem iInf_neBot_of_directed' {f : ι -> Filter α} [Nonempty ι] (hd : Directed (· >= ·) f) :
    (forall i, NeBot (f i)) -> NeBot (iInf f) :=
not_imp_not.1 by simpa only [not_forall, not_neBot, ← empty_mem_iff_bot,
    mem_iInf_of_directed hd] using id

/--
theorem `iInf_neBot_of_directed` / 定理 `iInf_neBot_of_directed`

English:
theorem iInf_neBot_of_directed
  statement: {f : ι -> Filter α} [hn : Nonempty α] (hd : Directed (· >= ·) f)
  proof: by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [iInf_of_empty f, top_ne_bot]
  · exact iInf_neBot_of_directed' hd hb

中文:
定理 iInf_neBot_of_directed
  结论: {f : ι -> 滤子 α} [hn : 非空 α] (hd : Directed (· >= ·) f)
  证明: by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [iInf_of_empty f, top_ne_bot]
  · exact iInf_neBot_of_directed' hd hb

Depends on / 依赖: iInf_neBot_of_directed, iInf_of_empty, isEmpty_or_nonempty, top_ne_bot
-/
theorem iInf_neBot_of_directed {f : ι -> Filter α} [hn : Nonempty α] (hd : Directed (· >= ·) f)
    (hb : forall i, NeBot (f i)) : NeBot (iInf f) := by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [iInf_of_empty f, top_ne_bot]
  · exact iInf_neBot_of_directed' hd hb

/--
theorem `sInf_neBot_of_directed'` / 定理 `sInf_neBot_of_directed'`

English:
theorem sInf_neBot_of_directed'
  statement: {s : Set (Filter α)} (hne : s.Nonempty) (hd : DirectedOn (· >= ·) s)
  proof: (sInf_eq_iInf' s).symm ▸
    @iInf_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨_, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩

中文:
定理 sInf_neBot_of_directed'
  结论: {s : 集合 (滤子 α)} (hne : s.非空) (hd : DirectedOn (· >= ·) s)
  证明: (sInf_eq_iInf' s).symm ▸
    @iInf_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨_, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩

Depends on / 依赖: directed_val, hd.directed_val, hne.to_subtype, iInf_neBot_of_directed, ne_of_mem_of_not_mem, sInf_eq_iInf, to_subtype
-/
theorem sInf_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : DirectedOn (· >= ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    @iInf_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨_, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩

/--
theorem `sInf_neBot_of_directed` / 定理 `sInf_neBot_of_directed`

English:
theorem sInf_neBot_of_directed
  statement: [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn (· >= ·) s)
  proof: (sInf_eq_iInf' s).symm ▸
    iInf_neBot_of_directed hd.directed_val fun ⟨_, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩

中文:
定理 sInf_neBot_of_directed
  结论: [非空 α] {s : 集合 (滤子 α)} (hd : DirectedOn (· >= ·) s)
  证明: (sInf_eq_iInf' s).symm ▸
    iInf_neBot_of_directed hd.directed_val fun ⟨_, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩

Depends on / 依赖: directed_val, hd.directed_val, iInf_neBot_of_directed, ne_of_mem_of_not_mem, sInf_eq_iInf
-/
theorem sInf_neBot_of_directed [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn (· >= ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    iInf_neBot_of_directed hd.directed_val fun ⟨_, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩

/--
theorem `iInf_neBot_iff_of_directed'` / 定理 `iInf_neBot_iff_of_directed'`

English:
theorem iInf_neBot_iff_of_directed'
  given: {f : ι -> Filter α} [Nonempty ι] (hd : Directed (· >= ·) f)
  proof: ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed' hd⟩

中文:
定理 iInf_neBot_iff_of_directed'
  条件: {f : ι -> 滤子 α} [非空 ι] (hd : Directed (· >= ·) f)
  证明: ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed' hd⟩

Depends on / 依赖: H.mono, iInf_le, iInf_neBot_of_directed
-/
theorem iInf_neBot_iff_of_directed' {f : ι -> Filter α} [Nonempty ι] (hd : Directed (· >= ·) f) :
    NeBot (iInf f) ↔ forall i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed' hd⟩

/--
theorem `iInf_neBot_iff_of_directed` / 定理 `iInf_neBot_iff_of_directed`

English:
theorem iInf_neBot_iff_of_directed
  given: {f : ι -> Filter α} [Nonempty α] (hd : Directed (· >= ·) f)
  proof: ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed hd⟩

中文:
定理 iInf_neBot_iff_of_directed
  条件: {f : ι -> 滤子 α} [非空 α] (hd : Directed (· >= ·) f)
  证明: ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed hd⟩

Depends on / 依赖: H.mono, iInf_le, iInf_neBot_of_directed
-/
theorem iInf_neBot_iff_of_directed {f : ι -> Filter α} [Nonempty α] (hd : Directed (· >= ·) f) :
    NeBot (iInf f) ↔ forall i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed hd⟩

/-! #### `principal` equations -/

@[simp]
/--
theorem `inf_principal` / 定理 `inf_principal`

English:
theorem inf_principal
  given: {s t : Set α}
  statement: 𝓟 s ⊓ 𝓟 t = 𝓟 (s inter t)
  proof: le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, Subset.rfl, t, Subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp]

中文:
定理 inf_principal
  条件: {s t : 集合 α}
  结论: 𝓟 s ⊓ 𝓟 t = 𝓟 (s inter t)
  证明: le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, Subset.rfl, t, Subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp]

Depends on / 依赖: Subset, Subset.rfl, inter_subset_left, inter_subset_right, le_antisymm, le_inf_iff, le_principal_iff, mem_inf_iff
-/
theorem inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s inter t) :=
  le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, Subset.rfl, t, Subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp]
/--
theorem `sup_principal` / 定理 `sup_principal`

English:
theorem sup_principal
  given: {s t : Set α}
  statement: 𝓟 s ⊔ 𝓟 t = 𝓟 (s union t)
  proof: Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]

@[simp]

中文:
定理 sup_principal
  条件: {s t : 集合 α}
  结论: 𝓟 s ⊔ 𝓟 t = 𝓟 (s union t)
  证明: Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]

@[simp]

Depends on / 依赖: Filter, Filter.ext, mem_principal, mem_sup, union_subset_iff
-/
theorem sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s union t) :=
  Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]

@[simp]
/--
theorem `iSup_principal` / 定理 `iSup_principal`

English:
theorem iSup_principal
  given: {ι : Sort w} {s : ι -> Set α}
  statement: ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i)
  proof: Filter.ext fun x => by simp only [mem_iSup, mem_principal, iUnion_subset_iff]

@[simp]

中文:
定理 iSup_principal
  条件: {ι : 类型层 w} {s : ι -> 集合 α}
  结论: ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i)
  证明: Filter.ext fun x => by simp only [mem_iSup, mem_principal, iUnion_subset_iff]

@[simp]

Depends on / 依赖: Filter, Filter.ext, Ideal.Quotient.field, Invertible, Invertible.finrank_eq_one, Quotient, finrank_eq_one, free_of_flat_of_finrank_eq, iUnion_subset_iff, mem_iSup, mem_principal, subsingleton_iff, subsingleton_iff.mpr
-/
theorem iSup_principal {ι : Sort w} {s : ι -> Set α} : ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_principal, iUnion_subset_iff]

@[simp]
/--
theorem `principal_sdiff_principal` / 定理 `principal_sdiff_principal`

English:
theorem principal_sdiff_principal
  given: {s t : Set α}
  statement: 𝓟 s \ 𝓟 t = 𝓟 (s \ t)
  proof: Filter.ext fun _ => by simp [← le_principal_iff, principal_mono]

@[simp]

中文:
定理 principal_sdiff_principal
  条件: {s t : 集合 α}
  结论: 𝓟 s \ 𝓟 t = 𝓟 (s \ t)
  证明: Filter.ext fun _ => by simp [← le_principal_iff, principal_mono]

@[simp]

Depends on / 依赖: Filter, Filter.ext, le_principal_iff, principal_mono
-/
theorem principal_sdiff_principal {s t : Set α} : 𝓟 s \ 𝓟 t = 𝓟 (s \ t) :=
  Filter.ext fun _ => by simp [← le_principal_iff, principal_mono]

@[simp]
/--
theorem `hnot_principal` / 定理 `hnot_principal`

English:
theorem hnot_principal
  given: {s : Set α}
  statement: ￢𝓟 s = 𝓟 sᶜ
  proof: by
  simpa [← compl_eq_univ_sdiff] using @principal_sdiff_principal _ univ s

@[simp]

中文:
定理 hnot_principal
  条件: {s : 集合 α}
  结论: ￢𝓟 s = 𝓟 sᶜ
  证明: by
  simpa [← compl_eq_univ_sdiff] using @principal_sdiff_principal _ univ s

@[simp]

Depends on / 依赖: compl_eq_univ_sdiff, principal_sdiff_principal
-/
theorem hnot_principal {s : Set α} : ￢𝓟 s = 𝓟 sᶜ := by
  simpa [← compl_eq_univ_sdiff] using @principal_sdiff_principal _ univ s

@[simp]
/--
theorem `principal_eq_bot_iff` / 定理 `principal_eq_bot_iff`

English:
theorem principal_eq_bot_iff
  given: {s : Set α}
  statement: 𝓟 s = ⊥ ↔ s = ∅
  proof: empty_mem_iff_bot.symm.trans mem_principal.trans subset_empty_iff

@[simp]

中文:
定理 principal_eq_bot_iff
  条件: {s : 集合 α}
  结论: 𝓟 s = ⊥ ↔ s = ∅
  证明: empty_mem_iff_bot.symm.trans mem_principal.trans subset_empty_iff

@[simp]

Depends on / 依赖: empty_mem_iff_bot, empty_mem_iff_bot.symm.trans, mem_principal, mem_principal.trans, subset_empty_iff
-/
theorem principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
empty_mem_iff_bot.symm.trans mem_principal.trans subset_empty_iff

@[simp]
/--
theorem `principal_neBot_iff` / 定理 `principal_neBot_iff`

English:
theorem principal_neBot_iff
  given: {s : Set α}
  statement: NeBot (𝓟 s) ↔ s.Nonempty
  proof: neBot_iff.trans (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm

alias ⟨_, _root_.Set.Nonempty.principal_neBot⟩ := principal_neBot_iff

中文:
定理 principal_neBot_iff
  条件: {s : 集合 α}
  结论: NeBot (𝓟 s) ↔ s.非空
  证明: neBot_iff.trans (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm

alias ⟨_, _root_.Set.Nonempty.principal_neBot⟩ := principal_neBot_iff

Depends on / 依赖: neBot_iff, neBot_iff.trans, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm, not_congr, principal_eq_bot_iff
-/
theorem principal_neBot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty :=
neBot_iff.trans (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm

alias ⟨_, _root_.Set.Nonempty.principal_neBot⟩ := principal_neBot_iff

/--
theorem `isCompl_principal` / 定理 `isCompl_principal`

English:
theorem isCompl_principal
  given: (s : Set α)
  statement: IsCompl (𝓟 s) (𝓟 sᶜ)
  proof: IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) by
    rw [sup_principal]; rw [union_compl_self]; rw [principal_univ]

中文:
定理 isCompl_principal
  条件: (s : 集合 α)
  结论: 是补集 (𝓟 s) (𝓟 sᶜ)
  证明: IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) by
    rw [sup_principal]; rw [union_compl_self]; rw [principal_univ]

Depends on / 依赖: IsCompl, IsCompl.of_eq, inf_principal, inter_compl_self, of_eq, principal_empty, principal_univ, sup_principal, union_compl_self
-/
theorem isCompl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 sᶜ) :=
IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) by
    rw [sup_principal]; rw [union_compl_self]; rw [principal_univ]

/--
theorem `mem_inf_principal'` / 定理 `mem_inf_principal'`

English:
theorem mem_inf_principal'
  given: {f : Filter α} {s t : Set α}
  statement: s in f ⊓ 𝓟 t ↔ tᶜ union s in f
  proof: by
  simp only [← le_principal_iff, (isCompl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (isCompl_principal (t inter sᶜ)).le_right_iff, compl_inter, compl_compl]

中文:
定理 mem_inf_principal'
  条件: {f : 滤子 α} {s t : 集合 α}
  结论: s in f ⊓ 𝓟 t ↔ tᶜ union s in f
  证明: by
  simp only [← le_principal_iff, (isCompl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (isCompl_principal (t inter sᶜ)).le_right_iff, compl_inter, compl_compl]

Depends on / 依赖: compl_compl, compl_inter, disjoint_assoc, inf_principal, isCompl_principal, le_left_iff, le_principal_iff, le_right_iff
-/
theorem mem_inf_principal' {f : Filter α} {s t : Set α} : s in f ⊓ 𝓟 t ↔ tᶜ union s in f := by
  simp only [← le_principal_iff, (isCompl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (isCompl_principal (t inter sᶜ)).le_right_iff, compl_inter, compl_compl]

/--
lemma `mem_inf_principal` / 引理 `mem_inf_principal`

English:
lemma mem_inf_principal
  given: {f : Filter α} {s t : Set α}
  statement: s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
  proof: by
  simp only [mem_inf_principal', imp_iff_not_or, ofPred_or, compl_def, ofPred_mem_eq]

中文:
引理 mem_inf_principal
  条件: {f : 滤子 α} {s t : 集合 α}
  结论: s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
  证明: by
  simp only [mem_inf_principal', imp_iff_not_or, ofPred_or, compl_def, ofPred_mem_eq]

Depends on / 依赖: compl_def, imp_iff_not_or, mem_inf_principal, ofPred_mem_eq, ofPred_or
-/
lemma mem_inf_principal {f : Filter α} {s t : Set α} : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f := by
  simp only [mem_inf_principal', imp_iff_not_or, ofPred_or, compl_def, ofPred_mem_eq]

/--
lemma `iSup_inf_principal` / 引理 `iSup_inf_principal`

English:
lemma iSup_inf_principal
  given: (f : ι -> Filter α) (s : Set α)
  statement: ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s
  proof: by
  ext
  simp only [mem_iSup, mem_inf_principal]

中文:
引理 iSup_inf_principal
  条件: (f : ι -> 滤子 α) (s : 集合 α)
  结论: ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s
  证明: by
  ext
  simp only [mem_iSup, mem_inf_principal]

Depends on / 依赖: mem_iSup, mem_inf_principal
-/
lemma iSup_inf_principal (f : ι -> Filter α) (s : Set α) : ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s := by
  ext
  simp only [mem_iSup, mem_inf_principal]

/--
theorem `inf_principal_eq_bot` / 定理 `inf_principal_eq_bot`

English:
theorem inf_principal_eq_bot
  given: {f : Filter α} {s : Set α}
  statement: f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f
  proof: by
  rw [← empty_mem_iff_bot]; rw [mem_inf_principal]
  simp only [mem_empty_iff_false, imp_false, compl_def]

中文:
定理 inf_principal_eq_bot
  条件: {f : 滤子 α} {s : 集合 α}
  结论: f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f
  证明: by
  rw [← empty_mem_iff_bot]; rw [mem_inf_principal]
  simp only [mem_empty_iff_false, imp_false, compl_def]

Depends on / 依赖: compl_def, empty_mem_iff_bot, imp_false, mem_empty_iff_false, mem_inf_principal
-/
theorem inf_principal_eq_bot {f : Filter α} {s : Set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f := by
  rw [← empty_mem_iff_bot]; rw [mem_inf_principal]
  simp only [mem_empty_iff_false, imp_false, compl_def]

/--
theorem `mem_of_eq_bot` / 定理 `mem_of_eq_bot`

English:
theorem mem_of_eq_bot
  given: {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 sᶜ = ⊥)
  statement: s in f
  proof: by
  rwa [inf_principal_eq_bot, compl_compl] at h

中文:
定理 mem_of_eq_bot
  条件: {f : 滤子 α} {s : 集合 α} (h : f ⊓ 𝓟 sᶜ = ⊥)
  结论: s in f
  证明: by
  rwa [inf_principal_eq_bot, compl_compl] at h

Depends on / 依赖: compl_compl, inf_principal_eq_bot
-/
theorem mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 sᶜ = ⊥) : s in f := by
  rwa [inf_principal_eq_bot, compl_compl] at h

/--
theorem `sdiff_mem_inf_principal_compl` / 定理 `sdiff_mem_inf_principal_compl`

English:
theorem sdiff_mem_inf_principal_compl
  given: {f : Filter α} {s : Set α} (hs : s in f) (t : Set α)
  proof: inter_mem_inf hs mem_principal_self tᶜ

@[deprecated (since := "2026-06-03")]
alias diff_mem_inf_principal_compl := sdiff_mem_inf_principal_compl

中文:
定理 sdiff_mem_inf_principal_compl
  条件: {f : 滤子 α} {s : 集合 α} (hs : s in f) (t : 集合 α)
  证明: inter_mem_inf hs mem_principal_self tᶜ

@[deprecated (since := "2026-06-03")]
alias diff_mem_inf_principal_compl := sdiff_mem_inf_principal_compl

Depends on / 依赖: inter_mem_inf, mem_principal_self
-/
theorem sdiff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s in f) (t : Set α) :
    s \ t in f ⊓ 𝓟 tᶜ :=
inter_mem_inf hs mem_principal_self tᶜ

@[deprecated (since := "2026-06-03")]
alias diff_mem_inf_principal_compl := sdiff_mem_inf_principal_compl

/--
theorem `principal_le_iff` / 定理 `principal_le_iff`

English:
theorem principal_le_iff
  given: {s : Set α} {f : Filter α}
  statement: 𝓟 s <= f ↔ forall V in f, s subseteq V
  proof: by
  simp_rw [le_def, mem_principal]

中文:
定理 principal_le_iff
  条件: {s : 集合 α} {f : 滤子 α}
  结论: 𝓟 s <= f ↔ 对任意 V in f, s subseteq V
  证明: by
  simp_rw [le_def, mem_principal]

Depends on / 依赖: le_def, mem_principal, simp_rw
-/
theorem principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s <= f ↔ forall V in f, s subseteq V := by
  simp_rw [le_def, mem_principal]

end Lattice

@[mono, gcongr]
/--
theorem `join_mono` / 定理 `join_mono`

English:
theorem join_mono
  given: {f₁ f₂ : Filter (Filter α)} (h : f₁ <= f₂)
  statement: join f₁ <= join f₂
  proof: fun _ hs => h hs

中文:
定理 join_mono
  条件: {f₁ f₂ : 滤子 (滤子 α)} (h : f₁ <= f₂)
  结论: join f₁ <= join f₂
  证明: fun _ hs => h hs
-/
theorem join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ <= f₂) : join f₁ <= join f₂ := fun _ hs => h hs


/--
theorem `eventually_iff` / 定理 `eventually_iff`

English:
theorem eventually_iff
  given: {f : Filter α} {P : α -> Prop}
  statement: (forallᶠ x in f, P x) ↔ { x | P x } in f
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_iff
  条件: {f : 滤子 α} {P : α -> 命题}
  结论: (对任意ᶠ x in f, P x) ↔ { x | P x } in f
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_iff {f : Filter α} {P : α -> Prop} : (forallᶠ x in f, P x) ↔ { x | P x } in f :=
  Iff.rfl

@[simp]
/--
theorem `eventually_mem_set` / 定理 `eventually_mem_set`

English:
theorem eventually_mem_set
  given: {s : Set α} {l : Filter α}
  statement: (forallᶠ x in l, x in s) ↔ s in l
  proof: Iff.rfl

中文:
定理 eventually_mem_set
  条件: {s : 集合 α} {l : 滤子 α}
  结论: (对任意ᶠ x in l, x in s) ↔ s in l
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventually_mem_set {s : Set α} {l : Filter α} : (forallᶠ x in l, x in s) ↔ s in l :=
  Iff.rfl

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: {f₁ f₂ : Filter α}
  proof: Filter.ext Set.ofPred_bijective.surjective.forall.mpr h

中文:
定理 ext'
  结论: {f₁ f₂ : 滤子 α}
  证明: Filter.ext Set.ofPred_bijective.surjective.forall.mpr h
-/
protected theorem ext' {f₁ f₂ : Filter α}
    (h : forall p : α -> Prop, (forallᶠ x in f₁, p x) ↔ forallᶠ x in f₂, p x) : f₁ = f₂ :=
Filter.ext Set.ofPred_bijective.surjective.forall.mpr h

/--
theorem `Eventually.filter_mono` / 定理 `Eventually.filter_mono`

English:
theorem Eventually.filter_mono
  statement: {f₁ f₂ : Filter α} (h : f₁ <= f₂) {p : α -> Prop}
  proof: h hp

中文:
定理 Eventually.filter_mono
  结论: {f₁ f₂ : 滤子 α} (h : f₁ <= f₂) {p : α -> 命题}
  证明: h hp
-/
theorem Eventually.filter_mono {f₁ f₂ : Filter α} (h : f₁ <= f₂) {p : α -> Prop}
    (hp : forallᶠ x in f₂, p x) : forallᶠ x in f₁, p x :=
  h hp

/--
theorem `eventually_of_mem` / 定理 `eventually_of_mem`

English:
theorem eventually_of_mem
  statement: {f : Filter α} {P : α -> Prop} {U : Set α} (hU : U in f)
  proof: mem_of_superset hU h

中文:
定理 eventually_of_mem
  结论: {f : 滤子 α} {P : α -> 命题} {U : 集合 α} (hU : U in f)
  证明: mem_of_superset hU h

Depends on / 依赖: mem_of_superset
-/
theorem eventually_of_mem {f : Filter α} {P : α -> Prop} {U : Set α} (hU : U in f)
    (h : forall x in U, P x) : forallᶠ x in f, P x :=
  mem_of_superset hU h

/--
theorem `Eventually.and` / 定理 `Eventually.and`

English:
theorem Eventually.and
  given: {p q : α -> Prop} {f : Filter α}
  proof: inter_mem

中文:
定理 Eventually.and
  条件: {p q : α -> 命题} {f : 滤子 α}
  证明: inter_mem
-/
protected theorem Eventually.and {p q : α -> Prop} {f : Filter α} :
    f.Eventually p -> f.Eventually q -> forallᶠ x in f, p x ∧ q x :=
  inter_mem

/--
theorem `eventually_true` / 定理 `eventually_true`

English:
theorem eventually_true
  given: (f : Filter α)
  statement: forallᶠ _ in f, True
  proof: univ_mem

中文:
定理 eventually_true
  条件: (f : 滤子 α)
  结论: 对任意ᶠ _ in f, 真
  证明: univ_mem
-/
@[simp] theorem eventually_true (f : Filter α) : forallᶠ _ in f, True := univ_mem

/--
theorem `Eventually.of_forall` / 定理 `Eventually.of_forall`

English:
theorem Eventually.of_forall
  given: {p : α -> Prop} {f : Filter α} (hp : forall x, p x)
  statement: forallᶠ x in f, p x
  proof: univ_mem' hp

@[simp]

中文:
定理 Eventually.of_对任意
  条件: {p : α -> 命题} {f : 滤子 α} (hp : 对任意 x, p x)
  结论: 对任意ᶠ x in f, p x
  证明: univ_mem' hp

@[simp]

Depends on / 依赖: univ_mem
-/
theorem Eventually.of_forall {p : α -> Prop} {f : Filter α} (hp : forall x, p x) : forallᶠ x in f, p x :=
  univ_mem' hp

@[simp]
/--
theorem `eventually_false_iff_eq_bot` / 定理 `eventually_false_iff_eq_bot`

English:
theorem eventually_false_iff_eq_bot
  given: {f : Filter α}
  statement: (forallᶠ _ in f, False) ↔ f = ⊥
  proof: empty_mem_iff_bot

@[simp]

中文:
定理 eventually_false_iff_eq_bot
  条件: {f : 滤子 α}
  结论: (对任意ᶠ _ in f, 假) ↔ f = ⊥
  证明: empty_mem_iff_bot

@[simp]

Depends on / 依赖: empty_mem_iff_bot
-/
theorem eventually_false_iff_eq_bot {f : Filter α} : (forallᶠ _ in f, False) ↔ f = ⊥ :=
  empty_mem_iff_bot

@[simp]
/--
theorem `eventually_const` / 定理 `eventually_const`

English:
theorem eventually_const
  given: {f : Filter α} [t : NeBot f] {p : Prop}
  statement: (forallᶠ _ in f, p) ↔ p
  proof: by
  by_cases h : p <;> simp [h, t.ne]

中文:
定理 eventually_const
  条件: {f : 滤子 α} [t : NeBot f] {p : 命题}
  结论: (对任意ᶠ _ in f, p) ↔ p
  证明: by
  by_cases h : p <;> simp [h, t.ne]

Depends on / 依赖: t.ne
-/
theorem eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (forallᶠ _ in f, p) ↔ p := by
  by_cases h : p <;> simp [h, t.ne]

/--
theorem `eventually_iff_exists_mem` / 定理 `eventually_iff_exists_mem`

English:
theorem eventually_iff_exists_mem
  given: {p : α -> Prop} {f : Filter α}
  proof: exists_mem_subset_iff.symm

中文:
定理 eventually_iff_存在_mem
  条件: {p : α -> 命题} {f : 滤子 α}
  证明: exists_mem_subset_iff.symm

Depends on / 依赖: exists_mem_subset_iff, exists_mem_subset_iff.symm
-/
theorem eventually_iff_exists_mem {p : α -> Prop} {f : Filter α} :
    (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y :=
  exists_mem_subset_iff.symm

/--
theorem `Eventually.exists_mem` / 定理 `Eventually.exists_mem`

English:
theorem Eventually.exists_mem
  given: {p : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
  proof: eventually_iff_exists_mem.1 hp

中文:
定理 Eventually.存在_mem
  条件: {p : α -> 命题} {f : 滤子 α} (hp : 对任意ᶠ x in f, p x)
  证明: eventually_iff_exists_mem.1 hp

Depends on / 依赖: eventually_iff_exists_mem
-/
theorem Eventually.exists_mem {p : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x) :
    exists v in f, forall y in v, p y :=
  eventually_iff_exists_mem.1 hp

/--
theorem `Eventually.mp` / 定理 `Eventually.mp`

English:
theorem Eventually.mp
  statement: {p q : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
  proof: mp_mem hp hq

@[gcongr]

中文:
定理 Eventually.mp
  结论: {p q : α -> 命题} {f : 滤子 α} (hp : 对任意ᶠ x in f, p x)
  证明: mp_mem hp hq

@[gcongr]

Depends on / 依赖: mp_mem
-/
theorem Eventually.mp {p q : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
    (hq : forallᶠ x in f, p x -> q x) : forallᶠ x in f, q x :=
  mp_mem hp hq

@[gcongr]
/--
theorem `Eventually.mono` / 定理 `Eventually.mono`

English:
theorem Eventually.mono
  statement: {p q : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
  proof: hp.mp (Eventually.of_forall hq)

中文:
定理 Eventually.mono
  结论: {p q : α -> 命题} {f : 滤子 α} (hp : 对任意ᶠ x in f, p x)
  证明: hp.mp (Eventually.of_forall hq)

Depends on / 依赖: Eventually, Eventually.of_forall, hp.mp, of_forall
-/
theorem Eventually.mono {p q : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
    (hq : forall x, p x -> q x) : forallᶠ x in f, q x :=
  hp.mp (Eventually.of_forall hq)

/--
theorem `forall_eventually_of_eventually_forall` / 定理 `forall_eventually_of_eventually_forall`

English:
theorem forall_eventually_of_eventually_forall
  statement: {f : Filter α} {p : α -> β -> Prop}
  proof: fun y => h.mono fun _ h => h y

@[simp]

中文:
定理 对任意_eventually_of_eventually_对任意
  结论: {f : 滤子 α} {p : α -> β -> 命题}
  证明: fun y => h.mono fun _ h => h y

@[simp]

Depends on / 依赖: h.mono
-/
theorem forall_eventually_of_eventually_forall {f : Filter α} {p : α -> β -> Prop}
    (h : forallᶠ x in f, forall y, p x y) : forall y, forallᶠ x in f, p x y :=
  fun y => h.mono fun _ h => h y

@[simp]
/--
theorem `eventually_and` / 定理 `eventually_and`

English:
theorem eventually_and
  given: {p q : α -> Prop} {f : Filter α}
  proof: inter_mem_iff

中文:
定理 eventually_and
  条件: {p q : α -> 命题} {f : 滤子 α}
  证明: inter_mem_iff

Depends on / 依赖: inter_mem_iff
-/
theorem eventually_and {p q : α -> Prop} {f : Filter α} :
    (forallᶠ x in f, p x ∧ q x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in f, q x :=
  inter_mem_iff

/--
theorem `Eventually.congr` / 定理 `Eventually.congr`

English:
theorem Eventually.congr
  statement: {f : Filter α} {p q : α -> Prop} (h' : forallᶠ x in f, p x)
  proof: h'.mp (h.mono fun _ hx => hx.mp)

中文:
定理 Eventually.congr
  结论: {f : 滤子 α} {p q : α -> 命题} (h' : 对任意ᶠ x in f, p x)
  证明: h'.mp (h.mono fun _ hx => hx.mp)

Depends on / 依赖: h.mono, hx.mp
-/
theorem Eventually.congr {f : Filter α} {p q : α -> Prop} (h' : forallᶠ x in f, p x)
    (h : forallᶠ x in f, p x ↔ q x) : forallᶠ x in f, q x :=
  h'.mp (h.mono fun _ hx => hx.mp)

/--
theorem `eventually_congr` / 定理 `eventually_congr`

English:
theorem eventually_congr
  given: {f : Filter α} {p q : α -> Prop} (h : forallᶠ x in f, p x ↔ q x)
  proof: ⟨fun hp => hp.congr h, fun hq => hq.congr by simpa only [Iff.comm] using h⟩

@[simp]

中文:
定理 eventually_congr
  条件: {f : 滤子 α} {p q : α -> 命题} (h : 对任意ᶠ x in f, p x ↔ q x)
  证明: ⟨fun hp => hp.congr h, fun hq => hq.congr by simpa only [Iff.comm] using h⟩

@[simp]

Depends on / 依赖: Iff.comm, hp.congr, hq.congr
-/
theorem eventually_congr {f : Filter α} {p q : α -> Prop} (h : forallᶠ x in f, p x ↔ q x) :
    (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x :=
⟨fun hp => hp.congr h, fun hq => hq.congr by simpa only [Iff.comm] using h⟩

@[simp]
/--
theorem `eventually_or_distrib_left` / 定理 `eventually_or_distrib_left`

English:
theorem eventually_or_distrib_left
  given: {f : Filter α} {p : Prop} {q : α -> Prop}
  proof: by_cases (fun h : p => by simp [h]) fun h => by simp [h]

@[simp]

中文:
定理 eventually_or_distrib_left
  条件: {f : 滤子 α} {p : 命题} {q : α -> 命题}
  证明: by_cases (fun h : p => by simp [h]) fun h => by simp [h]

@[simp]
-/
theorem eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α -> Prop} :
    (forallᶠ x in f, p ∨ q x) ↔ p ∨ forallᶠ x in f, q x :=
  by_cases (fun h : p => by simp [h]) fun h => by simp [h]

@[simp]
/--
theorem `eventually_or_distrib_right` / 定理 `eventually_or_distrib_right`

English:
theorem eventually_or_distrib_right
  given: {f : Filter α} {p : α -> Prop} {q : Prop}
  proof: by
  simp only [@or_comm _ q, eventually_or_distrib_left]

中文:
定理 eventually_or_distrib_right
  条件: {f : 滤子 α} {p : α -> 命题} {q : 命题}
  证明: by
  simp only [@or_comm _ q, eventually_or_distrib_left]

Depends on / 依赖: eventually_or_distrib_left, or_comm
-/
theorem eventually_or_distrib_right {f : Filter α} {p : α -> Prop} {q : Prop} :
    (forallᶠ x in f, p x ∨ q) ↔ (forallᶠ x in f, p x) ∨ q := by
  simp only [@or_comm _ q, eventually_or_distrib_left]

/--
theorem `eventually_imp_distrib_left` / 定理 `eventually_imp_distrib_left`

English:
theorem eventually_imp_distrib_left
  given: {f : Filter α} {p : Prop} {q : α -> Prop}
  proof: by
  simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]

中文:
定理 eventually_imp_distrib_left
  条件: {f : 滤子 α} {p : 命题} {q : α -> 命题}
  证明: by
  simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]

Depends on / 依赖: eventually_or_distrib_left, imp_iff_not_or
-/
theorem eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α -> Prop} :
    (forallᶠ x in f, p -> q x) ↔ p -> forallᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]
/--
theorem `eventually_bot` / 定理 `eventually_bot`

English:
theorem eventually_bot
  given: {p : α -> Prop}
  statement: forallᶠ x in ⊥, p x
  proof: ⟨⟩

@[simp]

中文:
定理 eventually_bot
  条件: {p : α -> 命题}
  结论: 对任意ᶠ x in ⊥, p x
  证明: ⟨⟩

@[simp]

Depends on / 依赖: ClassGroup, ClassGroup.equivPic, Equiv.subsingleton, equivPic, subsingleton, toEquiv, toEquiv.symm
-/
theorem eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, p x :=
  ⟨⟩

@[simp]
/--
theorem `eventually_top` / 定理 `eventually_top`

English:
theorem eventually_top
  given: {p : α -> Prop}
  statement: (forallᶠ x in ⊤, p x) ↔ forall x, p x
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_top
  条件: {p : α -> 命题}
  结论: (对任意ᶠ x in ⊤, p x) ↔ 对任意 x, p x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_top {p : α -> Prop} : (forallᶠ x in ⊤, p x) ↔ forall x, p x :=
  Iff.rfl

@[simp]
/--
theorem `eventually_sup` / 定理 `eventually_sup`

English:
theorem eventually_sup
  given: {p : α -> Prop} {f g : Filter α}
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_sup
  条件: {p : α -> 命题} {f g : 滤子 α}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_sup {p : α -> Prop} {f g : Filter α} :
    (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x :=
  Iff.rfl

@[simp]
/--
theorem `eventually_sSup` / 定理 `eventually_sSup`

English:
theorem eventually_sSup
  given: {p : α -> Prop} {fs : Set (Filter α)}
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_sSup
  条件: {p : α -> 命题} {fs : 集合 (滤子 α)}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_sSup {p : α -> Prop} {fs : Set (Filter α)} :
    (forallᶠ x in sSup fs, p x) ↔ forall f in fs, forallᶠ x in f, p x :=
  Iff.rfl

@[simp]
/--
theorem `eventually_iSup` / 定理 `eventually_iSup`

English:
theorem eventually_iSup
  given: {p : α -> Prop} {fs : ι -> Filter α}
  proof: mem_iSup

@[simp]

中文:
定理 eventually_iSup
  条件: {p : α -> 命题} {fs : ι -> 滤子 α}
  证明: mem_iSup

@[simp]

Depends on / 依赖: mem_iSup
-/
theorem eventually_iSup {p : α -> Prop} {fs : ι -> Filter α} :
    (forallᶠ x in ⨆ b, fs b, p x) ↔ forall b, forallᶠ x in fs b, p x :=
  mem_iSup

@[simp]
/--
theorem `eventually_principal` / 定理 `eventually_principal`

English:
theorem eventually_principal
  given: {a : Set α} {p : α -> Prop}
  statement: (forallᶠ x in 𝓟 a, p x) ↔ forall x in a, p x
  proof: Iff.rfl

中文:
定理 eventually_principal
  条件: {a : 集合 α} {p : α -> 命题}
  结论: (对任意ᶠ x in 𝓟 a, p x) ↔ 对任意 x in a, p x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventually_principal {a : Set α} {p : α -> Prop} : (forallᶠ x in 𝓟 a, p x) ↔ forall x in a, p x :=
  Iff.rfl

/--
theorem `Eventually.forall_mem` / 定理 `Eventually.forall_mem`

English:
theorem Eventually.forall_mem
  statement: {α : Type*} {f : Filter α} {s : Set α} {P : α -> Prop}
  proof: Filter.eventually_principal.mp (hP.filter_mono hf)

中文:
定理 Eventually.对任意_mem
  结论: {α : 类型} {f : 滤子 α} {s : 集合 α} {P : α -> 命题}
  证明: Filter.eventually_principal.mp (hP.filter_mono hf)

Depends on / 依赖: Filter, Filter.eventually_principal.mp, eventually_principal, filter_mono, hP.filter_mono
-/
theorem Eventually.forall_mem {α : Type*} {f : Filter α} {s : Set α} {P : α -> Prop}
    (hP : forallᶠ x in f, P x) (hf : 𝓟 s <= f) : forall x in s, P x :=
  Filter.eventually_principal.mp (hP.filter_mono hf)

/--
theorem `eventually_inf` / 定理 `eventually_inf`

English:
theorem eventually_inf
  given: {f g : Filter α} {p : α -> Prop}
  proof: mem_inf_iff_superset

中文:
定理 eventually_inf
  条件: {f g : 滤子 α} {p : α -> 命题}
  证明: mem_inf_iff_superset

Depends on / 依赖: mem_inf_iff_superset
-/
theorem eventually_inf {f g : Filter α} {p : α -> Prop} :
    (forallᶠ x in f ⊓ g, p x) ↔ exists s in f, exists t in g, forall x in s inter t, p x :=
  mem_inf_iff_superset

/--
theorem `eventually_inf_principal` / 定理 `eventually_inf_principal`

English:
theorem eventually_inf_principal
  given: {f : Filter α} {p : α -> Prop} {s : Set α}
  proof: mem_inf_principal

中文:
定理 eventually_inf_principal
  条件: {f : 滤子 α} {p : α -> 命题} {s : 集合 α}
  证明: mem_inf_principal

Depends on / 依赖: mem_inf_principal
-/
theorem eventually_inf_principal {f : Filter α} {p : α -> Prop} {s : Set α} :
    (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x in s -> p x :=
  mem_inf_principal

/--
theorem `eventually_iff_all_subsets` / 定理 `eventually_iff_all_subsets`

English:
theorem eventually_iff_all_subsets
  given: {f : Filter α} {p : α -> Prop}
  proof: by filter_upwards [h] with _ pa _ using pa
  mpr h := by filter_upwards [h univ] with _ pa using pa (by simp)

中文:
定理 eventually_iff_all_subsets
  条件: {f : 滤子 α} {p : α -> 命题}
  证明: by filter_upwards [h] with _ pa _ using pa
  mpr h := by filter_upwards [h univ] with _ pa using pa (by simp)

Depends on / 依赖: filter_upwards
-/
theorem eventually_iff_all_subsets {f : Filter α} {p : α -> Prop} :
    (forallᶠ x in f, p x) ↔ forall (s : Set α), forallᶠ x in f, x in s -> p x where
  mp h _ := by filter_upwards [h] with _ pa _ using pa
  mpr h := by filter_upwards [h univ] with _ pa using pa (by simp)


/--
theorem `Eventually.frequently` / 定理 `Eventually.frequently`

English:
theorem Eventually.frequently
  given: {f : Filter α} [NeBot f] {p : α -> Prop} (h : forallᶠ x in f, p x)
  proof: compl_notMem h

中文:
定理 Eventually.frequently
  条件: {f : 滤子 α} [NeBot f] {p : α -> 命题} (h : 对任意ᶠ x in f, p x)
  证明: compl_notMem h

Depends on / 依赖: compl_notMem
-/
theorem Eventually.frequently {f : Filter α} [NeBot f] {p : α -> Prop} (h : forallᶠ x in f, p x) :
    existsᶠ x in f, p x :=
  compl_notMem h

/--
theorem `Frequently.of_forall` / 定理 `Frequently.of_forall`

English:
theorem Frequently.of_forall
  given: {f : Filter α} [NeBot f] {p : α -> Prop} (h : forall x, p x)
  proof: Eventually.frequently (Eventually.of_forall h)

中文:
定理 Frequently.of_对任意
  条件: {f : 滤子 α} [NeBot f] {p : α -> 命题} (h : 对任意 x, p x)
  证明: Eventually.frequently (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.frequently, Eventually.of_forall, frequently, of_forall
-/
theorem Frequently.of_forall {f : Filter α} [NeBot f] {p : α -> Prop} (h : forall x, p x) :
    existsᶠ x in f, p x :=
  Eventually.frequently (Eventually.of_forall h)

/--
theorem `Frequently.mp` / 定理 `Frequently.mp`

English:
theorem Frequently.mp
  statement: {p q : α -> Prop} {f : Filter α} (h : existsᶠ x in f, p x)
  proof: mt (fun hq => hq.mp <| hpq.mono fun _ => mt) h

中文:
定理 Frequently.mp
  结论: {p q : α -> 命题} {f : 滤子 α} (h : 存在ᶠ x in f, p x)
  证明: mt (fun hq => hq.mp <| hpq.mono fun _ => mt) h

Depends on / 依赖: hpq.mono, hq.mp
-/
theorem Frequently.mp {p q : α -> Prop} {f : Filter α} (h : existsᶠ x in f, p x)
    (hpq : forallᶠ x in f, p x -> q x) : existsᶠ x in f, q x :=
  mt (fun hq => hq.mp <| hpq.mono fun _ => mt) h

/--
lemma `frequently_congr` / 引理 `frequently_congr`

English:
lemma frequently_congr
  given: {p q : α -> Prop} {f : Filter α} (h : forallᶠ x in f, p x ↔ q x)
  proof: ⟨fun h' => h'.mp (h.mono fun _ => Iff.mp), fun h' => h'.mp (h.mono fun _ => Iff.mpr)⟩

中文:
引理 frequently_congr
  条件: {p q : α -> 命题} {f : 滤子 α} (h : 对任意ᶠ x in f, p x ↔ q x)
  证明: ⟨fun h' => h'.mp (h.mono fun _ => Iff.mp), fun h' => h'.mp (h.mono fun _ => Iff.mpr)⟩

Depends on / 依赖: Iff.mp, Iff.mpr, h.mono
-/
lemma frequently_congr {p q : α -> Prop} {f : Filter α} (h : forallᶠ x in f, p x ↔ q x) :
    (existsᶠ x in f, p x) ↔ existsᶠ x in f, q x :=
  ⟨fun h' => h'.mp (h.mono fun _ => Iff.mp), fun h' => h'.mp (h.mono fun _ => Iff.mpr)⟩

/--
theorem `Frequently.filter_mono` / 定理 `Frequently.filter_mono`

English:
theorem Frequently.filter_mono
  given: {p : α -> Prop} {f g : Filter α} (h : existsᶠ x in f, p x) (hle : f <= g)
  proof: mt (fun h' => h'.filter_mono hle) h

@[gcongr]

中文:
定理 Frequently.filter_mono
  条件: {p : α -> 命题} {f g : 滤子 α} (h : 存在ᶠ x in f, p x) (hle : f <= g)
  证明: mt (fun h' => h'.filter_mono hle) h

@[gcongr]

Depends on / 依赖: filter_mono
-/
theorem Frequently.filter_mono {p : α -> Prop} {f g : Filter α} (h : existsᶠ x in f, p x) (hle : f <= g) :
    existsᶠ x in g, p x :=
  mt (fun h' => h'.filter_mono hle) h

@[gcongr]
/--
theorem `Frequently.mono` / 定理 `Frequently.mono`

English:
theorem Frequently.mono
  statement: {p q : α -> Prop} {f : Filter α} (h : existsᶠ x in f, p x)
  proof: h.mp (Eventually.of_forall hpq)

中文:
定理 Frequently.mono
  结论: {p q : α -> 命题} {f : 滤子 α} (h : 存在ᶠ x in f, p x)
  证明: h.mp (Eventually.of_forall hpq)

Depends on / 依赖: Eventually, Eventually.of_forall, h.mp, of_forall
-/
theorem Frequently.mono {p q : α -> Prop} {f : Filter α} (h : existsᶠ x in f, p x)
    (hpq : forall x, p x -> q x) : existsᶠ x in f, q x :=
  h.mp (Eventually.of_forall hpq)

/--
theorem `Frequently.and_eventually` / 定理 `Frequently.and_eventually`

English:
theorem Frequently.and_eventually
  statement: {p q : α -> Prop} {f : Filter α} (hp : existsᶠ x in f, p x)
  proof: by
  refine mt (fun h => hq.mp <| h.mono ?_) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩

中文:
定理 Frequently.and_eventually
  结论: {p q : α -> 命题} {f : 滤子 α} (hp : 存在ᶠ x in f, p x)
  证明: by
  refine mt (fun h => hq.mp <| h.mono ?_) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩

Depends on / 依赖: h.mono, hq.mp
-/
theorem Frequently.and_eventually {p q : α -> Prop} {f : Filter α} (hp : existsᶠ x in f, p x)
    (hq : forallᶠ x in f, q x) : existsᶠ x in f, p x ∧ q x := by
  refine mt (fun h => hq.mp <| h.mono ?_) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩

/--
theorem `Eventually.and_frequently` / 定理 `Eventually.and_frequently`

English:
theorem Eventually.and_frequently
  statement: {p q : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
  proof: by
  simpa only [and_comm] using hq.and_eventually hp

中文:
定理 Eventually.and_frequently
  结论: {p q : α -> 命题} {f : 滤子 α} (hp : 对任意ᶠ x in f, p x)
  证明: by
  simpa only [and_comm] using hq.and_eventually hp

Depends on / 依赖: and_comm, and_eventually, hq.and_eventually
-/
theorem Eventually.and_frequently {p q : α -> Prop} {f : Filter α} (hp : forallᶠ x in f, p x)
    (hq : existsᶠ x in f, q x) : existsᶠ x in f, p x ∧ q x := by
  simpa only [and_comm] using hq.and_eventually hp

/--
theorem `Frequently.exists` / 定理 `Frequently.exists`

English:
theorem Frequently.exists
  given: {p : α -> Prop} {f : Filter α} (hp : existsᶠ x in f, p x)
  statement: exists x, p x
  proof: by
  by_contra H
  replace H : forallᶠ x in f, ¬p x := Eventually.of_forall (not_exists.1 H)
  exact hp H

中文:
定理 Frequently.存在
  条件: {p : α -> 命题} {f : 滤子 α} (hp : 存在ᶠ x in f, p x)
  结论: 存在 x, p x
  证明: by
  by_contra H
  replace H : forallᶠ x in f, ¬p x := Eventually.of_forall (not_exists.1 H)
  exact hp H

Depends on / 依赖: Eventually, Eventually.of_forall, not_exists, of_forall, replace
-/
theorem Frequently.exists {p : α -> Prop} {f : Filter α} (hp : existsᶠ x in f, p x) : exists x, p x := by
  by_contra H
  replace H : forallᶠ x in f, ¬p x := Eventually.of_forall (not_exists.1 H)
  exact hp H

/--
theorem `Eventually.exists` / 定理 `Eventually.exists`

English:
theorem Eventually.exists
  given: {p : α -> Prop} {f : Filter α} [NeBot f] (hp : forallᶠ x in f, p x)
  proof: hp.frequently.exists

中文:
定理 Eventually.存在
  条件: {p : α -> 命题} {f : 滤子 α} [NeBot f] (hp : 对任意ᶠ x in f, p x)
  证明: hp.frequently.exists

Depends on / 依赖: frequently, hp.frequently.exists
-/
theorem Eventually.exists {p : α -> Prop} {f : Filter α} [NeBot f] (hp : forallᶠ x in f, p x) :
    exists x, p x :=
  hp.frequently.exists

/--
lemma `frequently_iff_neBot` / 引理 `frequently_iff_neBot`

English:
lemma frequently_iff_neBot
  given: {l : Filter α} {p : α -> Prop}
  proof: by
  rw [neBot_iff]; rw [Ne]; rw [inf_principal_eq_bot]; rfl

中文:
引理 frequently_iff_neBot
  条件: {l : 滤子 α} {p : α -> 命题}
  证明: by
  rw [neBot_iff]; rw [Ne]; rw [inf_principal_eq_bot]; rfl

Depends on / 依赖: inf_principal_eq_bot, neBot_iff
-/
lemma frequently_iff_neBot {l : Filter α} {p : α -> Prop} :
    (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x}) := by
  rw [neBot_iff]; rw [Ne]; rw [inf_principal_eq_bot]; rfl

/--
lemma `frequently_mem_iff_neBot` / 引理 `frequently_mem_iff_neBot`

English:
lemma frequently_mem_iff_neBot
  given: {l : Filter α} {s : Set α}
  statement: (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
  proof: frequently_iff_neBot

中文:
引理 frequently_mem_iff_neBot
  条件: {l : 滤子 α} {s : 集合 α}
  结论: (存在ᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
  证明: frequently_iff_neBot

Depends on / 依赖: frequently_iff_neBot
-/
lemma frequently_mem_iff_neBot {l : Filter α} {s : Set α} : (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s) :=
  frequently_iff_neBot

/--
theorem `frequently_iff_forall_eventually_exists_and` / 定理 `frequently_iff_forall_eventually_exists_and`

English:
theorem frequently_iff_forall_eventually_exists_and
  given: {p : α -> Prop} {f : Filter α}
  proof: ⟨fun hp _ hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩

中文:
定理 frequently_iff_对任意_eventually_存在_and
  条件: {p : α -> 命题} {f : 滤子 α}
  证明: ⟨fun hp _ hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩

Depends on / 依赖: and_eventually, and_not_self_iff, exists_false, hp.and_eventually
-/
theorem frequently_iff_forall_eventually_exists_and {p : α -> Prop} {f : Filter α} :
    (existsᶠ x in f, p x) ↔ forall {q : α -> Prop}, (forallᶠ x in f, q x) -> exists x, p x ∧ q x :=
  ⟨fun hp _ hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩

/--
theorem `frequently_iff` / 定理 `frequently_iff`

English:
theorem frequently_iff
  given: {f : Filter α} {P : α -> Prop}
  proof: by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _),
    Set.ofPred_bijective.surjective.forall, Filter.Eventually, mem_ofPred]

@[simp, push]

中文:
定理 frequently_iff
  条件: {f : 滤子 α} {P : α -> 命题}
  证明: by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _),
    Set.ofPred_bijective.surjective.forall, Filter.Eventually, mem_ofPred]

@[simp, push]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Set.ofPred_bijective.surjective.forall, and_comm, frequently_iff_forall_eventually_exists_and, mem_ofPred, ofPred_bijective, surjective
-/
theorem frequently_iff {f : Filter α} {P : α -> Prop} :
    (existsᶠ x in f, P x) ↔ forall {U}, U in f -> exists x in U, P x := by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _),
    Set.ofPred_bijective.surjective.forall, Filter.Eventually, mem_ofPred]

@[simp, push]
/--
theorem `not_eventually` / 定理 `not_eventually`

English:
theorem not_eventually
  given: {p : α -> Prop} {f : Filter α}
  statement: (¬forallᶠ x in f, p x) ↔ existsᶠ x in f, ¬p x
  proof: by
  simp [Filter.Frequently]

@[simp, push]

中文:
定理 not_eventually
  条件: {p : α -> 命题} {f : 滤子 α}
  结论: (¬对任意ᶠ x in f, p x) ↔ 存在ᶠ x in f, ¬p x
  证明: by
  simp [Filter.Frequently]

@[simp, push]

Depends on / 依赖: Filter, Filter.Frequently, Frequently
-/
theorem not_eventually {p : α -> Prop} {f : Filter α} : (¬forallᶠ x in f, p x) ↔ existsᶠ x in f, ¬p x := by
  simp [Filter.Frequently]

@[simp, push]
/--
theorem `not_frequently` / 定理 `not_frequently`

English:
theorem not_frequently
  given: {p : α -> Prop} {f : Filter α}
  statement: (¬existsᶠ x in f, p x) ↔ forallᶠ x in f, ¬p x
  proof: by
  simp only [Filter.Frequently, not_not]

@[simp]

中文:
定理 not_frequently
  条件: {p : α -> 命题} {f : 滤子 α}
  结论: (¬存在ᶠ x in f, p x) ↔ 对任意ᶠ x in f, ¬p x
  证明: by
  simp only [Filter.Frequently, not_not]

@[simp]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, not_not
-/
theorem not_frequently {p : α -> Prop} {f : Filter α} : (¬existsᶠ x in f, p x) ↔ forallᶠ x in f, ¬p x := by
  simp only [Filter.Frequently, not_not]

@[simp]
/--
theorem `frequently_true_iff_neBot` / 定理 `frequently_true_iff_neBot`

English:
theorem frequently_true_iff_neBot
  given: (f : Filter α)
  statement: (existsᶠ _ in f, True) ↔ NeBot f
  proof: by
  simp [frequently_iff_neBot]

@[simp]

中文:
定理 frequently_true_iff_neBot
  条件: (f : 滤子 α)
  结论: (存在ᶠ _ in f, 真) ↔ NeBot f
  证明: by
  simp [frequently_iff_neBot]

@[simp]

Depends on / 依赖: frequently_iff_neBot
-/
theorem frequently_true_iff_neBot (f : Filter α) : (existsᶠ _ in f, True) ↔ NeBot f := by
  simp [frequently_iff_neBot]

@[simp]
/--
theorem `frequently_false` / 定理 `frequently_false`

English:
theorem frequently_false
  given: (f : Filter α)
  statement: ¬existsᶠ _ in f, False
  proof: by simp

@[simp]

中文:
定理 frequently_false
  条件: (f : 滤子 α)
  结论: ¬存在ᶠ _ in f, 假
  证明: by simp

@[simp]
-/
theorem frequently_false (f : Filter α) : ¬existsᶠ _ in f, False := by simp

@[simp]
/--
theorem `frequently_const` / 定理 `frequently_const`

English:
theorem frequently_const
  given: {f : Filter α} [NeBot f] {p : Prop}
  statement: (existsᶠ _ in f, p) ↔ p
  proof: by
  by_cases p <;> simp [*]

@[simp]

中文:
定理 frequently_const
  条件: {f : 滤子 α} [NeBot f] {p : 命题}
  结论: (存在ᶠ _ in f, p) ↔ p
  证明: by
  by_cases p <;> simp [*]

@[simp]
-/
theorem frequently_const {f : Filter α} [NeBot f] {p : Prop} : (existsᶠ _ in f, p) ↔ p := by
  by_cases p <;> simp [*]

@[simp]
/--
theorem `frequently_or_distrib` / 定理 `frequently_or_distrib`

English:
theorem frequently_or_distrib
  given: {f : Filter α} {p q : α -> Prop}
  proof: by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]

中文:
定理 frequently_or_distrib
  条件: {f : 滤子 α} {p q : α -> 命题}
  证明: by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_and, not_and_or, not_or
-/
theorem frequently_or_distrib {f : Filter α} {p q : α -> Prop} :
    (existsᶠ x in f, p x ∨ q x) ↔ (existsᶠ x in f, p x) ∨ existsᶠ x in f, q x := by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]

/--
theorem `frequently_or_distrib_left` / 定理 `frequently_or_distrib_left`

English:
theorem frequently_or_distrib_left
  given: {f : Filter α} [NeBot f] {p : Prop} {q : α -> Prop}
  proof: by simp

中文:
定理 frequently_or_distrib_left
  条件: {f : 滤子 α} [NeBot f] {p : 命题} {q : α -> 命题}
  证明: by simp
-/
theorem frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α -> Prop} :
    (existsᶠ x in f, p ∨ q x) ↔ p ∨ existsᶠ x in f, q x := by simp

/--
theorem `frequently_or_distrib_right` / 定理 `frequently_or_distrib_right`

English:
theorem frequently_or_distrib_right
  given: {f : Filter α} [NeBot f] {p : α -> Prop} {q : Prop}
  proof: by simp

中文:
定理 frequently_or_distrib_right
  条件: {f : 滤子 α} [NeBot f] {p : α -> 命题} {q : 命题}
  证明: by simp
-/
theorem frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α -> Prop} {q : Prop} :
    (existsᶠ x in f, p x ∨ q) ↔ (existsᶠ x in f, p x) ∨ q := by simp

/--
theorem `frequently_imp_distrib` / 定理 `frequently_imp_distrib`

English:
theorem frequently_imp_distrib
  given: {f : Filter α} {p q : α -> Prop}
  proof: by
  simp [imp_iff_not_or]

中文:
定理 frequently_imp_distrib
  条件: {f : 滤子 α} {p q : α -> 命题}
  证明: by
  simp [imp_iff_not_or]

Depends on / 依赖: imp_iff_not_or
-/
theorem frequently_imp_distrib {f : Filter α} {p q : α -> Prop} :
    (existsᶠ x in f, p x -> q x) ↔ (forallᶠ x in f, p x) -> existsᶠ x in f, q x := by
  simp [imp_iff_not_or]

/--
theorem `frequently_imp_distrib_left` / 定理 `frequently_imp_distrib_left`

English:
theorem frequently_imp_distrib_left
  given: {f : Filter α} [NeBot f] {p : Prop} {q : α -> Prop}
  proof: by simp [frequently_imp_distrib]

中文:
定理 frequently_imp_distrib_left
  条件: {f : 滤子 α} [NeBot f] {p : 命题} {q : α -> 命题}
  证明: by simp [frequently_imp_distrib]

Depends on / 依赖: frequently_imp_distrib
-/
theorem frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α -> Prop} :
    (existsᶠ x in f, p -> q x) ↔ p -> existsᶠ x in f, q x := by simp [frequently_imp_distrib]

/--
theorem `frequently_imp_distrib_right` / 定理 `frequently_imp_distrib_right`

English:
theorem frequently_imp_distrib_right
  given: {f : Filter α} [NeBot f] {p : α -> Prop} {q : Prop}
  proof: by
  simp only [frequently_imp_distrib, frequently_const]

中文:
定理 frequently_imp_distrib_right
  条件: {f : 滤子 α} [NeBot f] {p : α -> 命题} {q : 命题}
  证明: by
  simp only [frequently_imp_distrib, frequently_const]

Depends on / 依赖: frequently_const, frequently_imp_distrib
-/
theorem frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α -> Prop} {q : Prop} :
    (existsᶠ x in f, p x -> q) ↔ (forallᶠ x in f, p x) -> q := by
  simp only [frequently_imp_distrib, frequently_const]

/--
theorem `eventually_imp_distrib_right` / 定理 `eventually_imp_distrib_right`

English:
theorem eventually_imp_distrib_right
  given: {f : Filter α} {p : α -> Prop} {q : Prop}
  proof: by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp]

中文:
定理 eventually_imp_distrib_right
  条件: {f : 滤子 α} {p : α -> 命题} {q : 命题}
  证明: by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp]

Depends on / 依赖: eventually_or_distrib_right, imp_iff_not_or, not_frequently
-/
theorem eventually_imp_distrib_right {f : Filter α} {p : α -> Prop} {q : Prop} :
    (forallᶠ x in f, p x -> q) ↔ (existsᶠ x in f, p x) -> q := by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp]
/--
theorem `frequently_and_distrib_left` / 定理 `frequently_and_distrib_left`

English:
theorem frequently_and_distrib_left
  given: {f : Filter α} {p : Prop} {q : α -> Prop}
  proof: by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, Classical.not_imp]

@[simp]

中文:
定理 frequently_and_distrib_left
  条件: {f : 滤子 α} {p : 命题} {q : α -> 命题}
  证明: by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, Classical.not_imp]

@[simp]

Depends on / 依赖: Classical, Classical.not_imp, Filter, Filter.Frequently, Frequently, eventually_imp_distrib_left, not_and, not_imp
-/
theorem frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α -> Prop} :
    (existsᶠ x in f, p ∧ q x) ↔ p ∧ existsᶠ x in f, q x := by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, Classical.not_imp]

@[simp]
/--
theorem `frequently_and_distrib_right` / 定理 `frequently_and_distrib_right`

English:
theorem frequently_and_distrib_right
  given: {f : Filter α} {p : α -> Prop} {q : Prop}
  proof: by
  simp only [@and_comm _ q, frequently_and_distrib_left]

@[simp]

中文:
定理 frequently_and_distrib_right
  条件: {f : 滤子 α} {p : α -> 命题} {q : 命题}
  证明: by
  simp only [@and_comm _ q, frequently_and_distrib_left]

@[simp]

Depends on / 依赖: and_comm, frequently_and_distrib_left
-/
theorem frequently_and_distrib_right {f : Filter α} {p : α -> Prop} {q : Prop} :
    (existsᶠ x in f, p x ∧ q) ↔ (existsᶠ x in f, p x) ∧ q := by
  simp only [@and_comm _ q, frequently_and_distrib_left]

@[simp]
/--
theorem `frequently_bot` / 定理 `frequently_bot`

English:
theorem frequently_bot
  given: {p : α -> Prop}
  statement: ¬existsᶠ x in ⊥, p x
  proof: by simp

@[simp]

中文:
定理 frequently_bot
  条件: {p : α -> 命题}
  结论: ¬存在ᶠ x in ⊥, p x
  证明: by simp

@[simp]
-/
theorem frequently_bot {p : α -> Prop} : ¬existsᶠ x in ⊥, p x := by simp

@[simp]
/--
theorem `frequently_top` / 定理 `frequently_top`

English:
theorem frequently_top
  given: {p : α -> Prop}
  statement: (existsᶠ x in ⊤, p x) ↔ exists x, p x
  proof: by simp [Filter.Frequently]

@[simp]

中文:
定理 frequently_top
  条件: {p : α -> 命题}
  结论: (存在ᶠ x in ⊤, p x) ↔ 存在 x, p x
  证明: by simp [Filter.Frequently]

@[simp]

Depends on / 依赖: Filter, Filter.Frequently, Frequently
-/
theorem frequently_top {p : α -> Prop} : (existsᶠ x in ⊤, p x) ↔ exists x, p x := by simp [Filter.Frequently]

@[simp]
/--
theorem `frequently_principal` / 定理 `frequently_principal`

English:
theorem frequently_principal
  given: {a : Set α} {p : α -> Prop}
  statement: (existsᶠ x in 𝓟 a, p x) ↔ exists x in a, p x
  proof: by
  simp [Filter.Frequently, not_forall]

中文:
定理 frequently_principal
  条件: {a : 集合 α} {p : α -> 命题}
  结论: (存在ᶠ x in 𝓟 a, p x) ↔ 存在 x in a, p x
  证明: by
  simp [Filter.Frequently, not_forall]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, not_forall
-/
theorem frequently_principal {a : Set α} {p : α -> Prop} : (existsᶠ x in 𝓟 a, p x) ↔ exists x in a, p x := by
  simp [Filter.Frequently, not_forall]

/--
theorem `frequently_inf_principal` / 定理 `frequently_inf_principal`

English:
theorem frequently_inf_principal
  given: {f : Filter α} {s : Set α} {p : α -> Prop}
  proof: by
  simp only [Filter.Frequently, eventually_inf_principal, not_and]

alias ⟨Frequently.of_inf_principal, Frequently.inf_principal⟩ := frequently_inf_principal

中文:
定理 frequently_inf_principal
  条件: {f : 滤子 α} {s : 集合 α} {p : α -> 命题}
  证明: by
  simp only [Filter.Frequently, eventually_inf_principal, not_and]

alias ⟨Frequently.of_inf_principal, Frequently.inf_principal⟩ := frequently_inf_principal

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_inf_principal, not_and
-/
theorem frequently_inf_principal {f : Filter α} {s : Set α} {p : α -> Prop} :
    (existsᶠ x in f ⊓ 𝓟 s, p x) ↔ existsᶠ x in f, x in s ∧ p x := by
  simp only [Filter.Frequently, eventually_inf_principal, not_and]

alias ⟨Frequently.of_inf_principal, Frequently.inf_principal⟩ := frequently_inf_principal

/--
theorem `frequently_sup` / 定理 `frequently_sup`

English:
theorem frequently_sup
  given: {p : α -> Prop} {f g : Filter α}
  proof: by
  simp only [Filter.Frequently, eventually_sup, not_and_or]

@[simp]

中文:
定理 frequently_sup
  条件: {p : α -> 命题} {f g : 滤子 α}
  证明: by
  simp only [Filter.Frequently, eventually_sup, not_and_or]

@[simp]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_sup, not_and_or
-/
theorem frequently_sup {p : α -> Prop} {f g : Filter α} :
    (existsᶠ x in f ⊔ g, p x) ↔ (existsᶠ x in f, p x) ∨ existsᶠ x in g, p x := by
  simp only [Filter.Frequently, eventually_sup, not_and_or]

@[simp]
/--
theorem `frequently_sSup` / 定理 `frequently_sSup`

English:
theorem frequently_sSup
  given: {p : α -> Prop} {fs : Set (Filter α)}
  proof: by
  simp only [Filter.Frequently, not_forall, eventually_sSup, exists_prop]

@[simp]

中文:
定理 frequently_sSup
  条件: {p : α -> 命题} {fs : 集合 (滤子 α)}
  证明: by
  simp only [Filter.Frequently, not_forall, eventually_sSup, exists_prop]

@[simp]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_sSup, exists_prop, not_forall
-/
theorem frequently_sSup {p : α -> Prop} {fs : Set (Filter α)} :
    (existsᶠ x in sSup fs, p x) ↔ exists f in fs, existsᶠ x in f, p x := by
  simp only [Filter.Frequently, not_forall, eventually_sSup, exists_prop]

@[simp]
/--
theorem `frequently_iSup` / 定理 `frequently_iSup`

English:
theorem frequently_iSup
  given: {p : α -> Prop} {fs : β -> Filter α}
  proof: by
  simp only [Filter.Frequently, eventually_iSup, not_forall]

中文:
定理 frequently_iSup
  条件: {p : α -> 命题} {fs : β -> 滤子 α}
  证明: by
  simp only [Filter.Frequently, eventually_iSup, not_forall]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_iSup, not_forall
-/
theorem frequently_iSup {p : α -> Prop} {fs : β -> Filter α} :
    (existsᶠ x in ⨆ b, fs b, p x) ↔ exists b, existsᶠ x in fs b, p x := by
  simp only [Filter.Frequently, eventually_iSup, not_forall]

/--
theorem `Eventually.choice` / 定理 `Eventually.choice`

English:
theorem Eventually.choice
  given: {r : α -> β -> Prop} {l : Filter α} [l.NeBot] (h : forallᶠ x in l, exists y, r x y)
  proof: by
  have : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : exists y, r x y) => hx
  exact ⟨f, h.mono hf⟩

中文:
定理 Eventually.choice
  条件: {r : α -> β -> 命题} {l : 滤子 α} [l.NeBot] (h : 对任意ᶠ x in l, 存在 y, r x y)
  证明: by
  have : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : exists y, r x y) => hx
  exact ⟨f, h.mono hf⟩

Depends on / 依赖: Nonempty, h.exists, h.mono, hx.nonempty, nonempty
-/
theorem Eventually.choice {r : α -> β -> Prop} {l : Filter α} [l.NeBot] (h : forallᶠ x in l, exists y, r x y) :
    exists f : α -> β, forallᶠ x in l, r x (f x) := by
  have : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : exists y, r x y) => hx
  exact ⟨f, h.mono hf⟩

/--
lemma `skolem` / 引理 `skolem`

English:
lemma skolem
  statement: {ι : Type*} {α : ι -> Type*} [forall i, Nonempty (α i)]
  proof: by
  classical
  refine ⟨fun H => ?_, fun ⟨b, hb⟩ => hb.mp (.of_forall fun x a => ⟨_, a⟩)⟩
  refine ⟨fun i => if h : exists b, P i b then h.choose else Nonempty.some inferInstance, ?_⟩
  filter_upwards [H] with i hi
  exact dif_pos hi ▸ hi.choose_spec

中文:
引理 skolem
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, 非空 (α i)]
  证明: by
  classical
  refine ⟨fun H => ?_, fun ⟨b, hb⟩ => hb.mp (.of_forall fun x a => ⟨_, a⟩)⟩
  refine ⟨fun i => if h : exists b, P i b then h.choose else Nonempty.some inferInstance, ?_⟩
  filter_upwards [H] with i hi
  exact dif_pos hi ▸ hi.choose_spec

Depends on / 依赖: Nonempty, Nonempty.some, choose_spec, classical, dif_pos, filter_upwards, h.choose, hb.mp, hi.choose_spec, of_forall
-/
lemma skolem {ι : Type*} {α : ι -> Type*} [forall i, Nonempty (α i)]
    {P : forall i : ι, α i -> Prop} {F : Filter ι} :
    (forallᶠ i in F, exists b, P i b) ↔ exists b : (Π i, α i), forallᶠ i in F, P i (b i) := by
  classical
  refine ⟨fun H => ?_, fun ⟨b, hb⟩ => hb.mp (.of_forall fun x a => ⟨_, a⟩)⟩
  refine ⟨fun i => if h : exists b, P i b then h.choose else Nonempty.some inferInstance, ?_⟩
  filter_upwards [H] with i hi
  exact dif_pos hi ▸ hi.choose_spec

/-!
### Relation “eventually equal”
-/

section EventuallyEq
variable {l : Filter α} {f g : α -> β}

/--
theorem `EventuallyEq.eventually` / 定理 `EventuallyEq.eventually`

English:
theorem EventuallyEq.eventually
  given: (h : f =ᶠ[l] g)
  statement: forallᶠ x in l, f x = g x
  proof: h

中文:
定理 EventuallyEq.eventually
  条件: (h : f =ᶠ[l] g)
  结论: 对任意ᶠ x in l, f x = g x
  证明: h
-/
theorem EventuallyEq.eventually (h : f =ᶠ[l] g) : forallᶠ x in l, f x = g x := h

/--
lemma `eventuallyEq_top` / 引理 `eventuallyEq_top`

English:
lemma eventuallyEq_top
  statement: f =ᶠ[⊤] g ↔ f = g
  proof: by simp [EventuallyEq, funext_iff]

中文:
引理 eventuallyEq_top
  结论: f =ᶠ[⊤] g ↔ f = g
  证明: by simp [EventuallyEq, funext_iff]
-/
@[simp] lemma eventuallyEq_top : f =ᶠ[⊤] g ↔ f = g := by simp [EventuallyEq, funext_iff]

/--
theorem `EventuallyEq.rw` / 定理 `EventuallyEq.rw`

English:
theorem EventuallyEq.rw
  statement: {l : Filter α} {f g : α -> β} (h : f =ᶠ[l] g) (p : α -> β -> Prop)
  proof: hf.congr h.mono fun _ hx => hx ▸ Iff.rfl

中文:
定理 EventuallyEq.rw
  结论: {l : 滤子 α} {f g : α -> β} (h : f =ᶠ[l] g) (p : α -> β -> 命题)
  证明: hf.congr h.mono fun _ hx => hx ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, h.mono, hf.congr
-/
theorem EventuallyEq.rw {l : Filter α} {f g : α -> β} (h : f =ᶠ[l] g) (p : α -> β -> Prop)
    (hf : forallᶠ x in l, p x (f x)) : forallᶠ x in l, p x (g x) :=
hf.congr h.mono fun _ hx => hx ▸ Iff.rfl

/--
theorem `eventuallyEq_set` / 定理 `eventuallyEq_set`

English:
theorem eventuallyEq_set
  given: {s t : Set α} {l : Filter α}
  statement: s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
  proof: eventually_congr Eventually.of_forall fun _ => eq_iff_iff

alias ⟨EventuallyEq.mem_iff, Eventually.set_eq⟩ := eventuallyEq_set

@[simp]

中文:
定理 eventuallyEq_set
  条件: {s t : 集合 α} {l : 滤子 α}
  结论: s =ᶠ[l] t ↔ 对任意ᶠ x in l, x in s ↔ x in t
  证明: eventually_congr Eventually.of_forall fun _ => eq_iff_iff

alias ⟨EventuallyEq.mem_iff, Eventually.set_eq⟩ := eventuallyEq_set

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, eq_iff_iff, eventually_congr, of_forall
-/
theorem eventuallyEq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t :=
eventually_congr Eventually.of_forall fun _ => eq_iff_iff

alias ⟨EventuallyEq.mem_iff, Eventually.set_eq⟩ := eventuallyEq_set

@[simp]
/--
theorem `eventuallyEq_univ` / 定理 `eventuallyEq_univ`

English:
theorem eventuallyEq_univ
  given: {s : Set α} {l : Filter α}
  statement: s =ᶠ[l] univ ↔ s in l
  proof: by
  simp [eventuallyEq_set]

中文:
定理 eventuallyEq_univ
  条件: {s : 集合 α} {l : 滤子 α}
  结论: s =ᶠ[l] univ ↔ s in l
  证明: by
  simp [eventuallyEq_set]

Depends on / 依赖: eventuallyEq_set
-/
theorem eventuallyEq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s in l := by
  simp [eventuallyEq_set]

/--
theorem `EventuallyEq.exists_mem` / 定理 `EventuallyEq.exists_mem`

English:
theorem EventuallyEq.exists_mem
  given: {l : Filter α} {f g : α -> β} (h : f =ᶠ[l] g)
  proof: Eventually.exists_mem h

中文:
定理 EventuallyEq.存在_mem
  条件: {l : 滤子 α} {f g : α -> β} (h : f =ᶠ[l] g)
  证明: Eventually.exists_mem h

Depends on / 依赖: Eventually, Eventually.exists_mem, exists_mem
-/
theorem EventuallyEq.exists_mem {l : Filter α} {f g : α -> β} (h : f =ᶠ[l] g) :
    exists s in l, EqOn f g s :=
  Eventually.exists_mem h

/--
theorem `eventuallyEq_of_mem` / 定理 `eventuallyEq_of_mem`

English:
theorem eventuallyEq_of_mem
  given: {l : Filter α} {f g : α -> β} {s : Set α} (hs : s in l) (h : EqOn f g s)
  proof: eventually_of_mem hs h

中文:
定理 eventuallyEq_of_mem
  条件: {l : 滤子 α} {f g : α -> β} {s : 集合 α} (hs : s in l) (h : EqOn f g s)
  证明: eventually_of_mem hs h

Depends on / 依赖: eventually_of_mem
-/
theorem eventuallyEq_of_mem {l : Filter α} {f g : α -> β} {s : Set α} (hs : s in l) (h : EqOn f g s) :
    f =ᶠ[l] g :=
  eventually_of_mem hs h

/--
theorem `eventuallyEq_iff_exists_mem` / 定理 `eventuallyEq_iff_exists_mem`

English:
theorem eventuallyEq_iff_exists_mem
  given: {l : Filter α} {f g : α -> β}
  proof: eventually_iff_exists_mem

中文:
定理 eventuallyEq_iff_存在_mem
  条件: {l : 滤子 α} {f g : α -> β}
  证明: eventually_iff_exists_mem

Depends on / 依赖: eventually_iff_exists_mem
-/
theorem eventuallyEq_iff_exists_mem {l : Filter α} {f g : α -> β} :
    f =ᶠ[l] g ↔ exists s in l, EqOn f g s :=
  eventually_iff_exists_mem

/--
theorem `EventuallyEq.filter_mono` / 定理 `EventuallyEq.filter_mono`

English:
theorem EventuallyEq.filter_mono
  given: {l l' : Filter α} {f g : α -> β} (h₁ : f =ᶠ[l] g) (h₂ : l' <= l)
  proof: h₂ h₁

@[refl, simp]

中文:
定理 EventuallyEq.filter_mono
  条件: {l l' : 滤子 α} {f g : α -> β} (h₁ : f =ᶠ[l] g) (h₂ : l' <= l)
  证明: h₂ h₁

@[refl, simp]
-/
theorem EventuallyEq.filter_mono {l l' : Filter α} {f g : α -> β} (h₁ : f =ᶠ[l] g) (h₂ : l' <= l) :
    f =ᶠ[l'] g :=
  h₂ h₁

@[refl, simp]
/--
theorem `EventuallyEq.refl` / 定理 `EventuallyEq.refl`

English:
theorem EventuallyEq.refl
  given: (l : Filter α) (f : α -> β)
  statement: f =ᶠ[l] f
  proof: Eventually.of_forall fun _ => rfl

中文:
定理 EventuallyEq.refl
  条件: (l : 滤子 α) (f : α -> β)
  结论: f =ᶠ[l] f
  证明: Eventually.of_forall fun _ => rfl

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
theorem EventuallyEq.refl (l : Filter α) (f : α -> β) : f =ᶠ[l] f :=
  Eventually.of_forall fun _ => rfl

/--
theorem `EventuallyEq.rfl` / 定理 `EventuallyEq.rfl`

English:
theorem EventuallyEq.rfl
  given: {l : Filter α} {f : α -> β}
  statement: f =ᶠ[l] f
  proof: EventuallyEq.refl l f

中文:
定理 EventuallyEq.rfl
  条件: {l : 滤子 α} {f : α -> β}
  结论: f =ᶠ[l] f
  证明: EventuallyEq.refl l f
-/
protected theorem EventuallyEq.rfl {l : Filter α} {f : α -> β} : f =ᶠ[l] f :=
  EventuallyEq.refl l f

/--
theorem `EventuallyEq.of_eq` / 定理 `EventuallyEq.of_eq`

English:
theorem EventuallyEq.of_eq
  given: {l : Filter α} {f g : α -> β} (h : f = g)
  statement: f =ᶠ[l] g
  proof: h ▸ .rfl
alias _root_.Eq.eventuallyEq := EventuallyEq.of_eq

@[symm]

中文:
定理 EventuallyEq.of_eq
  条件: {l : 滤子 α} {f g : α -> β} (h : f = g)
  结论: f =ᶠ[l] g
  证明: h ▸ .rfl
alias _root_.Eq.eventuallyEq := EventuallyEq.of_eq

@[symm]
-/
theorem EventuallyEq.of_eq {l : Filter α} {f g : α -> β} (h : f = g) : f =ᶠ[l] g := h ▸ .rfl
alias _root_.Eq.eventuallyEq := EventuallyEq.of_eq

@[symm]
/--
theorem `EventuallyEq.symm` / 定理 `EventuallyEq.symm`

English:
theorem EventuallyEq.symm
  given: {f g : α -> β} {l : Filter α} (H : f =ᶠ[l] g)
  statement: g =ᶠ[l] f
  proof: H.mono fun _ => Eq.symm

中文:
定理 EventuallyEq.symm
  条件: {f g : α -> β} {l : 滤子 α} (H : f =ᶠ[l] g)
  结论: g =ᶠ[l] f
  证明: H.mono fun _ => Eq.symm

Depends on / 依赖: Eq.symm, H.mono
-/
theorem EventuallyEq.symm {f g : α -> β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
  H.mono fun _ => Eq.symm

/--
lemma `eventuallyEq_comm` / 引理 `eventuallyEq_comm`

English:
lemma eventuallyEq_comm
  given: {f g : α -> β} {l : Filter α}
  statement: f =ᶠ[l] g ↔ g =ᶠ[l] f
  proof: ⟨.symm, .symm⟩

@[trans]

中文:
引理 eventuallyEq_comm
  条件: {f g : α -> β} {l : 滤子 α}
  结论: f =ᶠ[l] g ↔ g =ᶠ[l] f
  证明: ⟨.symm, .symm⟩

@[trans]
-/
lemma eventuallyEq_comm {f g : α -> β} {l : Filter α} : f =ᶠ[l] g ↔ g =ᶠ[l] f := ⟨.symm, .symm⟩

@[trans]
/--
theorem `EventuallyEq.trans` / 定理 `EventuallyEq.trans`

English:
theorem EventuallyEq.trans
  given: {l : Filter α} {f g h : α -> β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h)
  proof: H₂.rw (fun x y => f x = y) H₁

中文:
定理 EventuallyEq.trans
  条件: {l : 滤子 α} {f g h : α -> β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h)
  证明: H₂.rw (fun x y => f x = y) H₁
-/
theorem EventuallyEq.trans {l : Filter α} {f g h : α -> β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
    f =ᶠ[l] h :=
  H₂.rw (fun x y => f x = y) H₁

/--
theorem `EventuallyEq.congr_left` / 定理 `EventuallyEq.congr_left`

English:
theorem EventuallyEq.congr_left
  given: {l : Filter α} {f g h : α -> β} (H : f =ᶠ[l] g)
  proof: ⟨H.symm.trans, H.trans⟩

中文:
定理 EventuallyEq.congr_left
  条件: {l : 滤子 α} {f g h : α -> β} (H : f =ᶠ[l] g)
  证明: ⟨H.symm.trans, H.trans⟩

Depends on / 依赖: H.symm.trans, H.trans
-/
theorem EventuallyEq.congr_left {l : Filter α} {f g h : α -> β} (H : f =ᶠ[l] g) :
    f =ᶠ[l] h ↔ g =ᶠ[l] h :=
  ⟨H.symm.trans, H.trans⟩

/--
theorem `EventuallyEq.congr_right` / 定理 `EventuallyEq.congr_right`

English:
theorem EventuallyEq.congr_right
  given: {l : Filter α} {f g h : α -> β} (H : g =ᶠ[l] h)
  proof: ⟨(·.trans H), (·.trans H.symm)⟩

中文:
定理 EventuallyEq.congr_right
  条件: {l : 滤子 α} {f g h : α -> β} (H : g =ᶠ[l] h)
  证明: ⟨(·.trans H), (·.trans H.symm)⟩

Depends on / 依赖: H.symm
-/
theorem EventuallyEq.congr_right {l : Filter α} {f g h : α -> β} (H : g =ᶠ[l] h) :
    f =ᶠ[l] g ↔ f =ᶠ[l] h :=
  ⟨(·.trans H), (·.trans H.symm)⟩

instance {l : Filter α} :
    Trans ((· =ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· =ᶠ[l] ·) (· =ᶠ[l] ·) where
  trans := EventuallyEq.trans

/--
theorem `EventuallyEq.prodMk` / 定理 `EventuallyEq.prodMk`

English:
theorem EventuallyEq.prodMk
  given: {l} {f f' : α -> β} (hf : f =ᶠ[l] f') {g g' : α -> γ} (hg : g =ᶠ[l] g')
  proof: hf.mp
hg.mono by
      intros
      simp only [*]

中文:
定理 EventuallyEq.prodMk
  条件: {l} {f f' : α -> β} (hf : f =ᶠ[l] f') {g g' : α -> γ} (hg : g =ᶠ[l] g')
  证明: hf.mp
hg.mono by
      intros
      simp only [*]

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.ofEquiv, hf.mp, hg.mono, intros, liftEquiv, ofEquiv, pb.liftEquiv
-/
theorem EventuallyEq.prodMk {l} {f f' : α -> β} (hf : f =ᶠ[l] f') {g g' : α -> γ} (hg : g =ᶠ[l] g') :
    (fun x => (f x, g x)) =ᶠ[l] fun x => (f' x, g' x) :=
hf.mp
hg.mono by
      intros
      simp only [*]

/-- See `EventuallyEq.comp_tendsto` in Mathlib.Order.Filter.Tendsto for a similar statement w.r.t.
composition on the right. -/
@[gcongr]
/--
theorem `EventuallyEq.fun_comp` / 定理 `EventuallyEq.fun_comp`

English:
theorem EventuallyEq.fun_comp
  given: {f g : α -> β} {l : Filter α} (H : f =ᶠ[l] g) (h : β -> γ)
  proof: H.mono fun _ hx => congr_arg h hx

中文:
定理 EventuallyEq.fun_comp
  条件: {f g : α -> β} {l : 滤子 α} (H : f =ᶠ[l] g) (h : β -> γ)
  证明: H.mono fun _ hx => congr_arg h hx

Depends on / 依赖: H.mono, congr_arg
-/
theorem EventuallyEq.fun_comp {f g : α -> β} {l : Filter α} (H : f =ᶠ[l] g) (h : β -> γ) :
    h ∘ f =ᶠ[l] h ∘ g :=
  H.mono fun _ hx => congr_arg h hx

/--
theorem `EventuallyEq.comp₂` / 定理 `EventuallyEq.comp₂`

English:
theorem EventuallyEq.comp₂
  statement: {δ} {f f' : α -> β} {g g' : α -> γ} {l} (Hf : f =ᶠ[l] f') (h : β -> γ -> δ)
  proof: (Hf.prodMk Hg).fun_comp (uncurry h)

@[to_additive (attr := gcongr, to_fun)]

中文:
定理 EventuallyEq.comp₂
  结论: {δ} {f f' : α -> β} {g g' : α -> γ} {l} (Hf : f =ᶠ[l] f') (h : β -> γ -> δ)
  证明: (Hf.prodMk Hg).fun_comp (uncurry h)

@[to_additive (attr := gcongr, to_fun)]

Depends on / 依赖: Hf.prodMk, fun_comp, prodMk, uncurry
-/
theorem EventuallyEq.comp₂ {δ} {f f' : α -> β} {g g' : α -> γ} {l} (Hf : f =ᶠ[l] f') (h : β -> γ -> δ)
    (Hg : g =ᶠ[l] g') : (fun x => h (f x) (g x)) =ᶠ[l] fun x => h (f' x) (g' x) :=
  (Hf.prodMk Hg).fun_comp (uncurry h)

@[to_additive (attr := gcongr, to_fun)]
/--
theorem `EventuallyEq.mul` / 定理 `EventuallyEq.mul`

English:
theorem EventuallyEq.mul
  statement: [Mul β] {f f' g g' : α -> β} {l : Filter α} (h : f =ᶠ[l] g)
  proof: h.comp₂ (· * ·) h'

@[to_additive]

中文:
定理 EventuallyEq.mul
  结论: [乘法 β] {f f' g g' : α -> β} {l : 滤子 α} (h : f =ᶠ[l] g)
  证明: h.comp₂ (· * ·) h'

@[to_additive]

Depends on / 依赖: h.comp
-/
theorem EventuallyEq.mul [Mul β] {f f' g g' : α -> β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : f * f' =ᶠ[l] g * g' :=
  h.comp₂ (· * ·) h'

@[to_additive]
/--
lemma `EventuallyEq.mul_left` / 引理 `EventuallyEq.mul_left`

English:
lemma EventuallyEq.mul_left
  given: [Mul β] {f₁ f₂ f₃ : α -> β} (h : f₁ =ᶠ[l] f₂)
  proof: EventuallyEq.mul (by rfl) h

@[to_additive]

中文:
引理 EventuallyEq.mul_left
  条件: [乘法 β] {f₁ f₂ f₃ : α -> β} (h : f₁ =ᶠ[l] f₂)
  证明: EventuallyEq.mul (by rfl) h

@[to_additive]

Depends on / 依赖: EventuallyEq, EventuallyEq.mul
-/
lemma EventuallyEq.mul_left [Mul β] {f₁ f₂ f₃ : α -> β} (h : f₁ =ᶠ[l] f₂) :
    f₃ * f₁ =ᶠ[l] f₃ * f₂ := EventuallyEq.mul (by rfl) h

@[to_additive]
/--
lemma `EventuallyEq.mul_right` / 引理 `EventuallyEq.mul_right`

English:
lemma EventuallyEq.mul_right
  given: [Mul β] {f₁ f₂ f₃ : α -> β} (h : f₁ =ᶠ[l] f₂)
  proof: EventuallyEq.mul h (by rfl)

@[to_additive (attr := gcongr, to_fun, to_additive) const_smul]

中文:
引理 EventuallyEq.mul_right
  条件: [乘法 β] {f₁ f₂ f₃ : α -> β} (h : f₁ =ᶠ[l] f₂)
  证明: EventuallyEq.mul h (by rfl)

@[to_additive (attr := gcongr, to_fun, to_additive) const_smul]

Depends on / 依赖: EventuallyEq, EventuallyEq.mul
-/
lemma EventuallyEq.mul_right [Mul β] {f₁ f₂ f₃ : α -> β} (h : f₁ =ᶠ[l] f₂) :
    f₁ * f₃ =ᶠ[l] f₂ * f₃ := EventuallyEq.mul h (by rfl)

@[to_additive (attr := gcongr, to_fun, to_additive) const_smul]
/--
theorem `EventuallyEq.pow_const` / 定理 `EventuallyEq.pow_const`

English:
theorem EventuallyEq.pow_const
  given: {γ} [Pow β γ] {f g : α -> β} {l : Filter α} (h : f =ᶠ[l] g) (c : γ)
  proof: h.fun_comp (· ^ c)

@[to_additive (attr := gcongr, to_fun)]

中文:
定理 EventuallyEq.pow_const
  条件: {γ} [幂 β γ] {f g : α -> β} {l : 滤子 α} (h : f =ᶠ[l] g) (c : γ)
  证明: h.fun_comp (· ^ c)

@[to_additive (attr := gcongr, to_fun)]

Depends on / 依赖: fun_comp, h.fun_comp
-/
theorem EventuallyEq.pow_const {γ} [Pow β γ] {f g : α -> β} {l : Filter α} (h : f =ᶠ[l] g) (c : γ) :
    f ^ c =ᶠ[l] g ^ c :=
  h.fun_comp (· ^ c)

@[to_additive (attr := gcongr, to_fun)]
/--
theorem `EventuallyEq.inv` / 定理 `EventuallyEq.inv`

English:
theorem EventuallyEq.inv
  given: [Inv β] {f g : α -> β} {l : Filter α} (h : f =ᶠ[l] g)
  statement: f⁻¹ =ᶠ[l] g⁻¹
  proof: h.fun_comp Inv.inv

@[to_additive (attr := gcongr, to_fun)]

中文:
定理 EventuallyEq.inv
  条件: [取逆 β] {f g : α -> β} {l : 滤子 α} (h : f =ᶠ[l] g)
  结论: f⁻¹ =ᶠ[l] g⁻¹
  证明: h.fun_comp Inv.inv

@[to_additive (attr := gcongr, to_fun)]

Depends on / 依赖: Inv.inv, fun_comp, h.fun_comp
-/
theorem EventuallyEq.inv [Inv β] {f g : α -> β} {l : Filter α} (h : f =ᶠ[l] g) : f⁻¹ =ᶠ[l] g⁻¹ :=
  h.fun_comp Inv.inv

@[to_additive (attr := gcongr, to_fun)]
/--
theorem `EventuallyEq.div` / 定理 `EventuallyEq.div`

English:
theorem EventuallyEq.div
  statement: [Div β] {f f' g g' : α -> β} {l : Filter α} (h : f =ᶠ[l] g)
  proof: h.comp₂ (· / ·) h'

@[to_additive]

中文:
定理 EventuallyEq.div
  结论: [除法 β] {f f' g g' : α -> β} {l : 滤子 α} (h : f =ᶠ[l] g)
  证明: h.comp₂ (· / ·) h'

@[to_additive]

Depends on / 依赖: h.comp
-/
theorem EventuallyEq.div [Div β] {f f' g g' : α -> β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : f / f' =ᶠ[l] g / g' :=
  h.comp₂ (· / ·) h'

@[to_additive]
/--
theorem `EventuallyEq.smul` / 定理 `EventuallyEq.smul`

English:
theorem EventuallyEq.smul
  statement: {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α -> 𝕜} {g g' : α -> β}
  proof: hf.comp₂ (· • ·) hg

@[gcongr, to_fun]

中文:
定理 EventuallyEq.smul
  结论: {𝕜} [标量乘法 𝕜 β] {l : 滤子 α} {f f' : α -> 𝕜} {g g' : α -> β}
  证明: hf.comp₂ (· • ·) hg

@[gcongr, to_fun]

Depends on / 依赖: hf.comp
-/
theorem EventuallyEq.smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α -> 𝕜} {g g' : α -> β}
    (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : (fun x => f x • g x) =ᶠ[l] fun x => f' x • g' x :=
  hf.comp₂ (· • ·) hg

@[gcongr, to_fun]
/--
theorem `EventuallyEq.star` / 定理 `EventuallyEq.star`

English:
theorem EventuallyEq.star
  statement: {R : Type*} [Star R]
  proof: h.fun_comp Star.star

@[gcongr]

中文:
定理 EventuallyEq.star
  结论: {R : 类型} [对合 R]
  证明: h.fun_comp Star.star

@[gcongr]
-/
protected theorem EventuallyEq.star {R : Type*} [Star R]
    {f g : α -> R} {l : Filter α} (h : f =ᶠ[l] g) : star f =ᶠ[l] star g := h.fun_comp Star.star

@[gcongr]
/--
theorem `EventuallyEq.sup` / 定理 `EventuallyEq.sup`

English:
theorem EventuallyEq.sup
  statement: [Max β] {l : Filter α} {f f' g g' : α -> β} (hf : f =ᶠ[l] f')
  proof: hf.comp₂ (· ⊔ ·) hg

@[gcongr]

中文:
定理 EventuallyEq.上确界
  结论: [最大值 β] {l : 滤子 α} {f f' g g' : α -> β} (hf : f =ᶠ[l] f')
  证明: hf.comp₂ (· ⊔ ·) hg

@[gcongr]

Depends on / 依赖: hf.comp
-/
theorem EventuallyEq.sup [Max β] {l : Filter α} {f f' g g' : α -> β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : f ⊔ g =ᶠ[l] f' ⊔ g' :=
  hf.comp₂ (· ⊔ ·) hg

@[gcongr]
/--
theorem `EventuallyEq.inf` / 定理 `EventuallyEq.inf`

English:
theorem EventuallyEq.inf
  statement: [Min β] {l : Filter α} {f f' g g' : α -> β} (hf : f =ᶠ[l] f')
  proof: hf.comp₂ (· ⊓ ·) hg

@[gcongr]

中文:
定理 EventuallyEq.下确界
  结论: [最小值 β] {l : 滤子 α} {f f' g g' : α -> β} (hf : f =ᶠ[l] f')
  证明: hf.comp₂ (· ⊓ ·) hg

@[gcongr]

Depends on / 依赖: hf.comp
-/
theorem EventuallyEq.inf [Min β] {l : Filter α} {f f' g g' : α -> β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : f ⊓ g =ᶠ[l] f' ⊓ g' :=
  hf.comp₂ (· ⊓ ·) hg

@[gcongr]
/--
theorem `EventuallyEq.preimage` / 定理 `EventuallyEq.preimage`

English:
theorem EventuallyEq.preimage
  given: {l : Filter α} {f g : α -> β} (h : f =ᶠ[l] g) (s : Set β)
  proof: h.fun_comp s

@[gcongr]

中文:
定理 EventuallyEq.原像
  条件: {l : 滤子 α} {f g : α -> β} (h : f =ᶠ[l] g) (s : 集合 β)
  证明: h.fun_comp s

@[gcongr]

Depends on / 依赖: fun_comp, h.fun_comp
-/
theorem EventuallyEq.preimage {l : Filter α} {f g : α -> β} (h : f =ᶠ[l] g) (s : Set β) :
    f ⁻¹' s =ᶠ[l] g ⁻¹' s :=
  h.fun_comp s

@[gcongr]
/--
theorem `EventuallyEq.inter` / 定理 `EventuallyEq.inter`

English:
theorem EventuallyEq.inter
  given: {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t')
  proof: h.comp₂ (· ∧ ·) h'

@[gcongr]

中文:
定理 EventuallyEq.inter
  条件: {s t s' t' : 集合 α} {l : 滤子 α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t')
  证明: h.comp₂ (· ∧ ·) h'

@[gcongr]

Depends on / 依赖: h.comp
-/
theorem EventuallyEq.inter {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s inter s' : Set α) =ᶠ[l] (t inter t' : Set α) :=
  h.comp₂ (· ∧ ·) h'

@[gcongr]
/--
theorem `EventuallyEq.union` / 定理 `EventuallyEq.union`

English:
theorem EventuallyEq.union
  given: {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t')
  proof: h.comp₂ (· ∨ ·) h'

@[gcongr]

中文:
定理 EventuallyEq.union
  条件: {s t s' t' : 集合 α} {l : 滤子 α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t')
  证明: h.comp₂ (· ∨ ·) h'

@[gcongr]

Depends on / 依赖: h.comp
-/
theorem EventuallyEq.union {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s union s' : Set α) =ᶠ[l] (t union t' : Set α) :=
  h.comp₂ (· ∨ ·) h'

@[gcongr]
/--
theorem `EventuallyEq.compl` / 定理 `EventuallyEq.compl`

English:
theorem EventuallyEq.compl
  given: {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t)
  proof: h.fun_comp Not

@[gcongr]

中文:
定理 EventuallyEq.compl
  条件: {s t : 集合 α} {l : 滤子 α} (h : s =ᶠ[l] t)
  证明: h.fun_comp Not

@[gcongr]

Depends on / 依赖: fun_comp, h.fun_comp
-/
theorem EventuallyEq.compl {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t) :
    (sᶜ : Set α) =ᶠ[l] (tᶜ : Set α) :=
  h.fun_comp Not

@[gcongr]
/--
theorem `EventuallyEq.diff` / 定理 `EventuallyEq.diff`

English:
theorem EventuallyEq.diff
  given: {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t')
  proof: h.inter h'.compl

@[gcongr]

中文:
定理 EventuallyEq.diff
  条件: {s t s' t' : 集合 α} {l : 滤子 α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t')
  证明: h.inter h'.compl

@[gcongr]

Depends on / 依赖: h.inter
-/
theorem EventuallyEq.diff {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s \ s' : Set α) =ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

@[gcongr]
/--
theorem `EventuallyEq.symmDiff` / 定理 `EventuallyEq.symmDiff`

English:
theorem EventuallyEq.symmDiff
  statement: {s t s' t' : Set α} {l : Filter α}
  proof: (h.diff h').union (h'.diff h)

中文:
定理 EventuallyEq.symmDiff
  结论: {s t s' t' : 集合 α} {l : 滤子 α}
  证明: (h.diff h').union (h'.diff h)
-/
protected theorem EventuallyEq.symmDiff {s t s' t' : Set α} {l : Filter α}
    (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') : (s ∆ s' : Set α) =ᶠ[l] (t ∆ t' : Set α) :=
  (h.diff h').union (h'.diff h)

/--
theorem `eventuallyEq_empty` / 定理 `eventuallyEq_empty`

English:
theorem eventuallyEq_empty
  given: {s : Set α} {l : Filter α}
  statement: s =ᶠ[l] (∅ : Set α) ↔ forallᶠ x in l, x ∉ s
  proof: eventuallyEq_set.trans by simp

中文:
定理 eventuallyEq_empty
  条件: {s : 集合 α} {l : 滤子 α}
  结论: s =ᶠ[l] (∅ : 集合 α) ↔ 对任意ᶠ x in l, x ∉ s
  证明: eventuallyEq_set.trans by simp

Depends on / 依赖: eventuallyEq_set, eventuallyEq_set.trans
-/
theorem eventuallyEq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ forallᶠ x in l, x ∉ s :=
eventuallyEq_set.trans by simp

/--
theorem `inter_eventuallyEq_left` / 定理 `inter_eventuallyEq_left`

English:
theorem inter_eventuallyEq_left
  given: {s t : Set α} {l : Filter α}
  proof: by
  simp only [eventuallyEq_set, mem_inter_iff, and_iff_left_iff_imp]

中文:
定理 inter_eventuallyEq_left
  条件: {s t : 集合 α} {l : 滤子 α}
  证明: by
  simp only [eventuallyEq_set, mem_inter_iff, and_iff_left_iff_imp]

Depends on / 依赖: and_iff_left_iff_imp, eventuallyEq_set, mem_inter_iff
-/
theorem inter_eventuallyEq_left {s t : Set α} {l : Filter α} :
    (s inter t : Set α) =ᶠ[l] s ↔ forallᶠ x in l, x in s -> x in t := by
  simp only [eventuallyEq_set, mem_inter_iff, and_iff_left_iff_imp]

/--
theorem `inter_eventuallyEq_right` / 定理 `inter_eventuallyEq_right`

English:
theorem inter_eventuallyEq_right
  given: {s t : Set α} {l : Filter α}
  proof: by
  rw [inter_comm]; rw [inter_eventuallyEq_left]

@[simp]

中文:
定理 inter_eventuallyEq_right
  条件: {s t : 集合 α} {l : 滤子 α}
  证明: by
  rw [inter_comm]; rw [inter_eventuallyEq_left]

@[simp]

Depends on / 依赖: inter_comm, inter_eventuallyEq_left
-/
theorem inter_eventuallyEq_right {s t : Set α} {l : Filter α} :
    (s inter t : Set α) =ᶠ[l] t ↔ forallᶠ x in l, x in t -> x in s := by
  rw [inter_comm]; rw [inter_eventuallyEq_left]

@[simp]
/--
theorem `eventuallyEq_principal` / 定理 `eventuallyEq_principal`

English:
theorem eventuallyEq_principal
  given: {s : Set α} {f g : α -> β}
  statement: f =ᶠ[𝓟 s] g ↔ EqOn f g s
  proof: Iff.rfl

中文:
定理 eventuallyEq_principal
  条件: {s : 集合 α} {f g : α -> β}
  结论: f =ᶠ[𝓟 s] g ↔ EqOn f g s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventuallyEq_principal {s : Set α} {f g : α -> β} : f =ᶠ[𝓟 s] g ↔ EqOn f g s :=
  Iff.rfl

/--
theorem `eventuallyEq_inf_principal_iff` / 定理 `eventuallyEq_inf_principal_iff`

English:
theorem eventuallyEq_inf_principal_iff
  given: {F : Filter α} {s : Set α} {f g : α -> β}
  proof: eventually_inf_principal

中文:
定理 eventuallyEq_inf_principal_iff
  条件: {F : 滤子 α} {s : 集合 α} {f g : α -> β}
  证明: eventually_inf_principal

Depends on / 依赖: IsBezout, IsBezout.of_isPrincipalIdealRing, IsPrincipalIdealRing, eventually_inf_principal, of_isPrincipalIdealRing
-/
theorem eventuallyEq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α -> β} :
    f =ᶠ[F ⊓ 𝓟 s] g ↔ forallᶠ x in F, x in s -> f x = g x :=
  eventually_inf_principal

/--
theorem `EventuallyEq.sub_eq` / 定理 `EventuallyEq.sub_eq`

English:
theorem EventuallyEq.sub_eq
  given: [AddGroup β] {f g : α -> β} {l : Filter α} (h : f =ᶠ[l] g)
  proof: by simpa using ((EventuallyEq.refl l f).sub h).symm

中文:
定理 EventuallyEq.sub_eq
  条件: [加法群 β] {f g : α -> β} {l : 滤子 α} (h : f =ᶠ[l] g)
  证明: by simpa using ((EventuallyEq.refl l f).sub h).symm

Depends on / 依赖: DivisionSemiring, DivisionSemiring.isPrincipalIdealRing, EventuallyEq, EventuallyEq.refl, isPrincipalIdealRing
-/
theorem EventuallyEq.sub_eq [AddGroup β] {f g : α -> β} {l : Filter α} (h : f =ᶠ[l] g) :
    f - g =ᶠ[l] 0 := by simpa using ((EventuallyEq.refl l f).sub h).symm

/--
theorem `eventuallyEq_iff_sub` / 定理 `eventuallyEq_iff_sub`

English:
theorem eventuallyEq_iff_sub
  given: [AddGroup β] {f g : α -> β} {l : Filter α}
  proof: ⟨fun h => h.sub_eq, fun h => by simpa using h.add (EventuallyEq.refl l g)⟩

中文:
定理 eventuallyEq_iff_sub
  条件: [加法群 β] {f g : α -> β} {l : 滤子 α}
  证明: ⟨fun h => h.sub_eq, fun h => by simpa using h.add (EventuallyEq.refl l g)⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.refl, h.add, h.sub_eq, sub_eq
-/
theorem eventuallyEq_iff_sub [AddGroup β] {f g : α -> β} {l : Filter α} :
    f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
  ⟨fun h => h.sub_eq, fun h => by simpa using h.add (EventuallyEq.refl l g)⟩

/--
theorem `eventuallyEq_iff_all_subsets` / 定理 `eventuallyEq_iff_all_subsets`

English:
theorem eventuallyEq_iff_all_subsets
  given: {f g : α -> β} {l : Filter α}
  proof: eventually_iff_all_subsets

中文:
定理 eventuallyEq_iff_all_subsets
  条件: {f g : α -> β} {l : 滤子 α}
  证明: eventually_iff_all_subsets

Depends on / 依赖: eventually_iff_all_subsets
-/
theorem eventuallyEq_iff_all_subsets {f g : α -> β} {l : Filter α} :
    f =ᶠ[l] g ↔ forall s : Set α, forallᶠ x in l, x in s -> f x = g x :=
  eventually_iff_all_subsets

section LE

variable [LE β] {l : Filter α}

@[to_dual self (reorder := f g, f' g', hf hg)]
/--
theorem `EventuallyLE.congr` / 定理 `EventuallyLE.congr`

English:
theorem EventuallyLE.congr
  given: {f f' g g' : α -> β} (H : f <=ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g')
  proof: H.mp hg.mp hf.mono fun x hf hg H => by rwa [hf, hg] at H

@[to_dual self (reorder := f g, f' g', hf hg)]

中文:
定理 EventuallyLE.congr
  条件: {f f' g g' : α -> β} (H : f <=ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g')
  证明: H.mp hg.mp hf.mono fun x hf hg H => by rwa [hf, hg] at H

@[to_dual self (reorder := f g, f' g', hf hg)]

Depends on / 依赖: H.mp, hf.mono, hg.mp
-/
theorem EventuallyLE.congr {f f' g g' : α -> β} (H : f <=ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f' <=ᶠ[l] g' :=
H.mp hg.mp hf.mono fun x hf hg H => by rwa [hf, hg] at H

@[to_dual self (reorder := f g, f' g', hf hg)]
/--
theorem `eventuallyLE_congr` / 定理 `eventuallyLE_congr`

English:
theorem eventuallyLE_congr
  given: {f f' g g' : α -> β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g')
  proof: ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩

@[to_dual self]

中文:
定理 eventuallyLE_congr
  条件: {f f' g g' : α -> β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g')
  证明: ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩

@[to_dual self]

Depends on / 依赖: H.congr, hf.symm, hg.symm
-/
theorem eventuallyLE_congr {f f' g g' : α -> β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f <=ᶠ[l] g ↔ f' <=ᶠ[l] g' :=
  ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩

@[to_dual self]
/--
theorem `eventuallyLE_iff_all_subsets` / 定理 `eventuallyLE_iff_all_subsets`

English:
theorem eventuallyLE_iff_all_subsets
  given: {f g : α -> β} {l : Filter α}
  proof: eventually_iff_all_subsets

中文:
定理 eventuallyLE_iff_all_subsets
  条件: {f g : α -> β} {l : 滤子 α}
  证明: eventually_iff_all_subsets

Depends on / 依赖: eventually_iff_all_subsets
-/
theorem eventuallyLE_iff_all_subsets {f g : α -> β} {l : Filter α} :
    f <=ᶠ[l] g ↔ forall s : Set α, forallᶠ x in l, x in s -> f x <= g x :=
  eventually_iff_all_subsets

end LE

section Preorder

variable [Preorder β] {l : Filter α} {f g h : α -> β}

@[to_dual ge]
/--
theorem `EventuallyEq.le` / 定理 `EventuallyEq.le`

English:
theorem EventuallyEq.le
  given: (h : f =ᶠ[l] g)
  statement: f <=ᶠ[l] g
  proof: h.mono fun _ => le_of_eq

@[refl]

中文:
定理 EventuallyEq.le
  条件: (h : f =ᶠ[l] g)
  结论: f <=ᶠ[l] g
  证明: h.mono fun _ => le_of_eq

@[refl]

Depends on / 依赖: IsPrincipalIdealRing, PrincipalIdealRing, _root_, _root_.PrincipalIdealRing.isNoetherianRing, h.mono, isNoetherianRing, le_of_eq
-/
theorem EventuallyEq.le (h : f =ᶠ[l] g) : f <=ᶠ[l] g :=
  h.mono fun _ => le_of_eq

@[refl]
/--
theorem `EventuallyLE.refl` / 定理 `EventuallyLE.refl`

English:
theorem EventuallyLE.refl
  given: (l : Filter α) (f : α -> β)
  statement: f <=ᶠ[l] f
  proof: EventuallyEq.rfl.le

中文:
定理 EventuallyLE.refl
  条件: (l : 滤子 α) (f : α -> β)
  结论: f <=ᶠ[l] f
  证明: EventuallyEq.rfl.le

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl.le, IsPrincipalIdealRing, _root_, _root_.IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout, of_isNoetherianRing_of_isBezout
-/
theorem EventuallyLE.refl (l : Filter α) (f : α -> β) : f <=ᶠ[l] f :=
  EventuallyEq.rfl.le

/--
theorem `EventuallyLE.rfl` / 定理 `EventuallyLE.rfl`

English:
theorem EventuallyLE.rfl
  statement: f <=ᶠ[l] f
  proof: EventuallyLE.refl l f

@[trans, to_dual self (reorder := f h, H₁ H₂)]

中文:
定理 EventuallyLE.rfl
  结论: f <=ᶠ[l] f
  证明: EventuallyLE.refl l f

@[trans, to_dual self (reorder := f h, H₁ H₂)]

Depends on / 依赖: EventuallyLE, EventuallyLE.refl
-/
theorem EventuallyLE.rfl : f <=ᶠ[l] f :=
  EventuallyLE.refl l f

@[trans, to_dual self (reorder := f h, H₁ H₂)]
/--
theorem `EventuallyLE.trans` / 定理 `EventuallyLE.trans`

English:
theorem EventuallyLE.trans
  given: (H₁ : f <=ᶠ[l] g) (H₂ : g <=ᶠ[l] h)
  statement: f <=ᶠ[l] h
  proof: H₂.mp H₁.mono fun _ => le_trans

中文:
定理 EventuallyLE.trans
  条件: (H₁ : f <=ᶠ[l] g) (H₂ : g <=ᶠ[l] h)
  结论: f <=ᶠ[l] h
  证明: H₂.mp H₁.mono fun _ => le_trans

Depends on / 依赖: le_trans
-/
theorem EventuallyLE.trans (H₁ : f <=ᶠ[l] g) (H₂ : g <=ᶠ[l] h) : f <=ᶠ[l] h :=
H₂.mp H₁.mono fun _ => le_trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans ((· <=ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· <=ᶠ[l] ·) (· <=ᶠ[l] ·)
  body: EventuallyLE.trans

中文:
实例 :
  签名: Trans ((· <=ᶠ[l] ·) : (α -> β) -> (α -> β) -> 命题) (· <=ᶠ[l] ·) (· <=ᶠ[l] ·)
  定义体: EventuallyLE.trans

Depends on / 依赖: EventuallyLE, EventuallyLE.trans
-/
instance : Trans ((· <=ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· <=ᶠ[l] ·) (· <=ᶠ[l] ·) where
  trans := EventuallyLE.trans

/--
theorem `EventuallyEq.trans_le` / 定理 `EventuallyEq.trans_le`

English:
theorem EventuallyEq.trans_le
  given: (H₁ : f =ᶠ[l] g) (H₂ : g <=ᶠ[l] h)
  statement: f <=ᶠ[l] h
  proof: H₁.le.trans H₂

中文:
定理 EventuallyEq.trans_le
  条件: (H₁ : f =ᶠ[l] g) (H₂ : g <=ᶠ[l] h)
  结论: f <=ᶠ[l] h
  证明: H₁.le.trans H₂

Depends on / 依赖: le.trans
-/
theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g <=ᶠ[l] h) : f <=ᶠ[l] h :=
  H₁.le.trans H₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans ((· =ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· <=ᶠ[l] ·) (· <=ᶠ[l] ·)
  body: EventuallyEq.trans_le

中文:
实例 :
  签名: Trans ((· =ᶠ[l] ·) : (α -> β) -> (α -> β) -> 命题) (· <=ᶠ[l] ·) (· <=ᶠ[l] ·)
  定义体: EventuallyEq.trans_le

Depends on / 依赖: EventuallyEq, EventuallyEq.trans_le, trans_le
-/
instance : Trans ((· =ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· <=ᶠ[l] ·) (· <=ᶠ[l] ·) where
  trans := EventuallyEq.trans_le

/--
theorem `EventuallyLE.trans_eq` / 定理 `EventuallyLE.trans_eq`

English:
theorem EventuallyLE.trans_eq
  given: (H₁ : f <=ᶠ[l] g) (H₂ : g =ᶠ[l] h)
  statement: f <=ᶠ[l] h
  proof: H₁.trans H₂.le

中文:
定理 EventuallyLE.trans_eq
  条件: (H₁ : f <=ᶠ[l] g) (H₂ : g =ᶠ[l] h)
  结论: f <=ᶠ[l] h
  证明: H₁.trans H₂.le
-/
theorem EventuallyLE.trans_eq (H₁ : f <=ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f <=ᶠ[l] h :=
  H₁.trans H₂.le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans ((· <=ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· =ᶠ[l] ·) (· <=ᶠ[l] ·)
  body: EventuallyLE.trans_eq

中文:
实例 :
  签名: Trans ((· <=ᶠ[l] ·) : (α -> β) -> (α -> β) -> 命题) (· =ᶠ[l] ·) (· <=ᶠ[l] ·)
  定义体: EventuallyLE.trans_eq

Depends on / 依赖: EventuallyLE, EventuallyLE.trans_eq, trans_eq
-/
instance : Trans ((· <=ᶠ[l] ·) : (α -> β) -> (α -> β) -> Prop) (· =ᶠ[l] ·) (· <=ᶠ[l] ·) where
  trans := EventuallyLE.trans_eq

end Preorder

variable {l : Filter α}

@[to_dual self (reorder := h₁ h₂)]
/--
theorem `EventuallyLE.antisymm` / 定理 `EventuallyLE.antisymm`

English:
theorem EventuallyLE.antisymm
  statement: [PartialOrder β] {l : Filter α} {f g : α -> β} (h₁ : f <=ᶠ[l] g)
  proof: h₂.mp h₁.mono fun _ => le_antisymm

@[to_dual none]

中文:
定理 EventuallyLE.antisymm
  结论: [偏序 β] {l : 滤子 α} {f g : α -> β} (h₁ : f <=ᶠ[l] g)
  证明: h₂.mp h₁.mono fun _ => le_antisymm

@[to_dual none]

Depends on / 依赖: le_antisymm
-/
theorem EventuallyLE.antisymm [PartialOrder β] {l : Filter α} {f g : α -> β} (h₁ : f <=ᶠ[l] g)
    (h₂ : g <=ᶠ[l] f) : f =ᶠ[l] g :=
h₂.mp h₁.mono fun _ => le_antisymm

@[to_dual none]
/--
theorem `eventuallyLE_antisymm_iff` / 定理 `eventuallyLE_antisymm_iff`

English:
theorem eventuallyLE_antisymm_iff
  given: [PartialOrder β] {l : Filter α} {f g : α -> β}
  proof: by
  simp only [EventuallyEq, EventuallyLE, le_antisymm_iff, eventually_and]

@[to_dual ge_iff_eq']

中文:
定理 eventuallyLE_antisymm_iff
  条件: [偏序 β] {l : 滤子 α} {f g : α -> β}
  证明: by
  simp only [EventuallyEq, EventuallyLE, le_antisymm_iff, eventually_and]

@[to_dual ge_iff_eq']

Depends on / 依赖: EventuallyEq, EventuallyLE, eventually_and, le_antisymm_iff
-/
theorem eventuallyLE_antisymm_iff [PartialOrder β] {l : Filter α} {f g : α -> β} :
    f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f := by
  simp only [EventuallyEq, EventuallyLE, le_antisymm_iff, eventually_and]

@[to_dual ge_iff_eq']
/--
theorem `EventuallyLE.ge_iff_eq` / 定理 `EventuallyLE.ge_iff_eq`

English:
theorem EventuallyLE.ge_iff_eq
  given: [PartialOrder β] {l : Filter α} {f g : α -> β} (h : f <=ᶠ[l] g)
  proof: ⟨fun h' => h.antisymm h', EventuallyEq.ge⟩

@[to_dual ne_of_gt]

中文:
定理 EventuallyLE.ge_iff_eq
  条件: [偏序 β] {l : 滤子 α} {f g : α -> β} (h : f <=ᶠ[l] g)
  证明: ⟨fun h' => h.antisymm h', EventuallyEq.ge⟩

@[to_dual ne_of_gt]

Depends on / 依赖: EventuallyEq, EventuallyEq.ge, antisymm, h.antisymm
-/
theorem EventuallyLE.ge_iff_eq [PartialOrder β] {l : Filter α} {f g : α -> β} (h : f <=ᶠ[l] g) :
    g <=ᶠ[l] f ↔ f =ᶠ[l] g :=
  ⟨fun h' => h.antisymm h', EventuallyEq.ge⟩

@[to_dual ne_of_gt]
/--
theorem `Eventually.ne_of_lt` / 定理 `Eventually.ne_of_lt`

English:
theorem Eventually.ne_of_lt
  given: [Preorder β] {l : Filter α} {f g : α -> β} (h : forallᶠ x in l, f x < g x)
  proof: h.mono fun _ hx => hx.ne

@[to_dual ne_bot_of_gt]

中文:
定理 Eventually.ne_of_lt
  条件: [预序 β] {l : 滤子 α} {f g : α -> β} (h : 对任意ᶠ x in l, f x < g x)
  证明: h.mono fun _ hx => hx.ne

@[to_dual ne_bot_of_gt]

Depends on / 依赖: h.mono, hx.ne
-/
theorem Eventually.ne_of_lt [Preorder β] {l : Filter α} {f g : α -> β} (h : forallᶠ x in l, f x < g x) :
    forallᶠ x in l, f x != g x :=
  h.mono fun _ hx => hx.ne

@[to_dual ne_bot_of_gt]
/--
theorem `Eventually.ne_top_of_lt` / 定理 `Eventually.ne_top_of_lt`

English:
theorem Eventually.ne_top_of_lt
  statement: [Preorder β] [OrderTop β] {l : Filter α} {f g : α -> β}
  proof: h.mono fun _ hx => hx.ne_top

@[to_dual bot_lt_of_ne]

中文:
定理 Eventually.ne_top_of_lt
  结论: [预序 β] [有顶序 β] {l : 滤子 α} {f g : α -> β}
  证明: h.mono fun _ hx => hx.ne_top

@[to_dual bot_lt_of_ne]

Depends on / 依赖: h.mono, hx.ne_top, ne_top
-/
theorem Eventually.ne_top_of_lt [Preorder β] [OrderTop β] {l : Filter α} {f g : α -> β}
    (h : forallᶠ x in l, f x < g x) : forallᶠ x in l, f x != ⊤ :=
  h.mono fun _ hx => hx.ne_top

@[to_dual bot_lt_of_ne]
/--
theorem `Eventually.lt_top_of_ne` / 定理 `Eventually.lt_top_of_ne`

English:
theorem Eventually.lt_top_of_ne
  statement: [PartialOrder β] [OrderTop β] {l : Filter α} {f : α -> β}
  proof: h.mono fun _ hx => hx.lt_top

@[to_dual bot_lt_iff_ne_bot]

中文:
定理 Eventually.lt_top_of_ne
  结论: [偏序 β] [有顶序 β] {l : 滤子 α} {f : α -> β}
  证明: h.mono fun _ hx => hx.lt_top

@[to_dual bot_lt_iff_ne_bot]

Depends on / 依赖: h.mono, hx.lt_top, lt_top
-/
theorem Eventually.lt_top_of_ne [PartialOrder β] [OrderTop β] {l : Filter α} {f : α -> β}
    (h : forallᶠ x in l, f x != ⊤) : forallᶠ x in l, f x < ⊤ :=
  h.mono fun _ hx => hx.lt_top

@[to_dual bot_lt_iff_ne_bot]
/--
theorem `Eventually.lt_top_iff_ne_top` / 定理 `Eventually.lt_top_iff_ne_top`

English:
theorem Eventually.lt_top_iff_ne_top
  given: [PartialOrder β] [OrderTop β] {l : Filter α} {f : α -> β}
  proof: ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩

@[gcongr, mono]

中文:
定理 Eventually.lt_top_iff_ne_top
  条件: [偏序 β] [有顶序 β] {l : 滤子 α} {f : α -> β}
  证明: ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩

@[gcongr, mono]

Depends on / 依赖: Eventually, Eventually.lt_top_of_ne, Eventually.ne_of_lt, lt_top_of_ne, ne_of_lt
-/
theorem Eventually.lt_top_iff_ne_top [PartialOrder β] [OrderTop β] {l : Filter α} {f : α -> β} :
    (forallᶠ x in l, f x < ⊤) ↔ forallᶠ x in l, f x != ⊤ :=
  ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩

@[gcongr, mono]
/--
theorem `EventuallyLE.inter` / 定理 `EventuallyLE.inter`

English:
theorem EventuallyLE.inter
  given: {s t s' t' : Set α} {l : Filter α} (h : s <=ᶠ[l] t) (h' : s' <=ᶠ[l] t')
  proof: h'.mp h.mono fun _ => And.imp

@[gcongr, mono]

中文:
定理 EventuallyLE.inter
  条件: {s t s' t' : 集合 α} {l : 滤子 α} (h : s <=ᶠ[l] t) (h' : s' <=ᶠ[l] t')
  证明: h'.mp h.mono fun _ => And.imp

@[gcongr, mono]

Depends on / 依赖: And.imp, h.mono
-/
theorem EventuallyLE.inter {s t s' t' : Set α} {l : Filter α} (h : s <=ᶠ[l] t) (h' : s' <=ᶠ[l] t') :
    (s inter s' : Set α) <=ᶠ[l] (t inter t' : Set α) :=
h'.mp h.mono fun _ => And.imp

@[gcongr, mono]
/--
theorem `EventuallyLE.union` / 定理 `EventuallyLE.union`

English:
theorem EventuallyLE.union
  given: {s t s' t' : Set α} {l : Filter α} (h : s <=ᶠ[l] t) (h' : s' <=ᶠ[l] t')
  proof: h'.mp h.mono fun _ => Or.imp

@[gcongr, mono]

中文:
定理 EventuallyLE.union
  条件: {s t s' t' : 集合 α} {l : 滤子 α} (h : s <=ᶠ[l] t) (h' : s' <=ᶠ[l] t')
  证明: h'.mp h.mono fun _ => Or.imp

@[gcongr, mono]

Depends on / 依赖: Or.imp, h.mono
-/
theorem EventuallyLE.union {s t s' t' : Set α} {l : Filter α} (h : s <=ᶠ[l] t) (h' : s' <=ᶠ[l] t') :
    (s union s' : Set α) <=ᶠ[l] (t union t' : Set α) :=
h'.mp h.mono fun _ => Or.imp

@[gcongr, mono]
/--
theorem `EventuallyLE.compl` / 定理 `EventuallyLE.compl`

English:
theorem EventuallyLE.compl
  given: {s t : Set α} {l : Filter α} (h : s <=ᶠ[l] t)
  proof: h.mono fun _ => mt

@[gcongr, mono]

中文:
定理 EventuallyLE.compl
  条件: {s t : 集合 α} {l : 滤子 α} (h : s <=ᶠ[l] t)
  证明: h.mono fun _ => mt

@[gcongr, mono]

Depends on / 依赖: h.mono
-/
theorem EventuallyLE.compl {s t : Set α} {l : Filter α} (h : s <=ᶠ[l] t) :
    (tᶜ : Set α) <=ᶠ[l] (sᶜ : Set α) :=
  h.mono fun _ => mt

@[gcongr, mono]
/--
theorem `EventuallyLE.diff` / 定理 `EventuallyLE.diff`

English:
theorem EventuallyLE.diff
  given: {s t s' t' : Set α} {l : Filter α} (h : s <=ᶠ[l] t) (h' : t' <=ᶠ[l] s')
  proof: h.inter h'.compl

中文:
定理 EventuallyLE.diff
  条件: {s t s' t' : 集合 α} {l : 滤子 α} (h : s <=ᶠ[l] t) (h' : t' <=ᶠ[l] s')
  证明: h.inter h'.compl

Depends on / 依赖: h.inter
-/
theorem EventuallyLE.diff {s t s' t' : Set α} {l : Filter α} (h : s <=ᶠ[l] t) (h' : t' <=ᶠ[l] s') :
    (s \ s' : Set α) <=ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

/--
theorem `set_eventuallyLE_iff_mem_inf_principal` / 定理 `set_eventuallyLE_iff_mem_inf_principal`

English:
theorem set_eventuallyLE_iff_mem_inf_principal
  given: {s t : Set α} {l : Filter α}
  proof: eventually_inf_principal.symm

中文:
定理 set_eventuallyLE_iff_mem_inf_principal
  条件: {s t : 集合 α} {l : 滤子 α}
  证明: eventually_inf_principal.symm

Depends on / 依赖: eventually_inf_principal, eventually_inf_principal.symm
-/
theorem set_eventuallyLE_iff_mem_inf_principal {s t : Set α} {l : Filter α} :
    s <=ᶠ[l] t ↔ t in l ⊓ 𝓟 s :=
  eventually_inf_principal.symm

/--
theorem `set_eventuallyLE_iff_inf_principal_le` / 定理 `set_eventuallyLE_iff_inf_principal_le`

English:
theorem set_eventuallyLE_iff_inf_principal_le
  given: {s t : Set α} {l : Filter α}
  proof: set_eventuallyLE_iff_mem_inf_principal.trans by
    simp only [le_inf_iff, inf_le_left, true_and, le_principal_iff]

中文:
定理 set_eventuallyLE_iff_inf_principal_le
  条件: {s t : 集合 α} {l : 滤子 α}
  证明: set_eventuallyLE_iff_mem_inf_principal.trans by
    simp only [le_inf_iff, inf_le_left, true_and, le_principal_iff]

Depends on / 依赖: inf_le_left, le_inf_iff, le_principal_iff, set_eventuallyLE_iff_mem_inf_principal, set_eventuallyLE_iff_mem_inf_principal.trans, true_and
-/
theorem set_eventuallyLE_iff_inf_principal_le {s t : Set α} {l : Filter α} :
    s <=ᶠ[l] t ↔ l ⊓ 𝓟 s <= l ⊓ 𝓟 t :=
set_eventuallyLE_iff_mem_inf_principal.trans by
    simp only [le_inf_iff, inf_le_left, true_and, le_principal_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `set_eventuallyEq_iff_inf_principal` / 定理 `set_eventuallyEq_iff_inf_principal`

English:
theorem set_eventuallyEq_iff_inf_principal
  given: {s t : Set α} {l : Filter α}
  proof: by
  simp only [eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le]

@[to_dual (attr := gcongr)]

中文:
定理 set_eventuallyEq_iff_inf_principal
  条件: {s t : 集合 α} {l : 滤子 α}
  证明: by
  simp only [eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le]

@[to_dual (attr := gcongr)]

Depends on / 依赖: eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le
-/
theorem set_eventuallyEq_iff_inf_principal {s t : Set α} {l : Filter α} :
    s =ᶠ[l] t ↔ l ⊓ 𝓟 s = l ⊓ 𝓟 t := by
  simp only [eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le]

@[to_dual (attr := gcongr)]
/--
theorem `EventuallyLE.sup` / 定理 `EventuallyLE.sup`

English:
theorem EventuallyLE.sup
  statement: [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α -> β} (hf : f₁ <=ᶠ[l] f₂)
  proof: by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx

@[to_dual le_inf]

中文:
定理 EventuallyLE.上确界
  结论: [SemilatticeSup β] {l : 滤子 α} {f₁ f₂ g₁ g₂ : α -> β} (hf : f₁ <=ᶠ[l] f₂)
  证明: by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx

@[to_dual le_inf]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.to_principal_ideal_domain, IsPrincipalIdealRing, filter_upwards, sup_le_sup, to_principal_ideal_domain
-/
theorem EventuallyLE.sup [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α -> β} (hf : f₁ <=ᶠ[l] f₂)
    (hg : g₁ <=ᶠ[l] g₂) : f₁ ⊔ g₁ <=ᶠ[l] f₂ ⊔ g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx

@[to_dual le_inf]
/--
theorem `EventuallyLE.sup_le` / 定理 `EventuallyLE.sup_le`

English:
theorem EventuallyLE.sup_le
  statement: [SemilatticeSup β] {l : Filter α} {f g h : α -> β} (hf : f <=ᶠ[l] h)
  proof: by
  filter_upwards [hf, hg] with x hfx hgx using _root_.sup_le hfx hgx

@[to_dual inf_le_of_left_le]

中文:
定理 EventuallyLE.sup_le
  结论: [SemilatticeSup β] {l : 滤子 α} {f g h : α -> β} (hf : f <=ᶠ[l] h)
  证明: by
  filter_upwards [hf, hg] with x hfx hgx using _root_.sup_le hfx hgx

@[to_dual inf_le_of_left_le]

Depends on / 依赖: _root_, _root_.sup_le, filter_upwards, sup_le
-/
theorem EventuallyLE.sup_le [SemilatticeSup β] {l : Filter α} {f g h : α -> β} (hf : f <=ᶠ[l] h)
    (hg : g <=ᶠ[l] h) : f ⊔ g <=ᶠ[l] h := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.sup_le hfx hgx

@[to_dual inf_le_of_left_le]
/--
theorem `EventuallyLE.le_sup_of_le_left` / 定理 `EventuallyLE.le_sup_of_le_left`

English:
theorem EventuallyLE.le_sup_of_le_left
  statement: [SemilatticeSup β] {l : Filter α} {f g h : α -> β}
  proof: hf.mono fun _ => _root_.le_sup_of_le_left

@[to_dual inf_le_of_right_le]

中文:
定理 EventuallyLE.le_sup_of_le_left
  结论: [SemilatticeSup β] {l : 滤子 α} {f g h : α -> β}
  证明: hf.mono fun _ => _root_.le_sup_of_le_left

@[to_dual inf_le_of_right_le]

Depends on / 依赖: _root_, _root_.le_sup_of_le_left, hf.mono, le_sup_of_le_left
-/
theorem EventuallyLE.le_sup_of_le_left [SemilatticeSup β] {l : Filter α} {f g h : α -> β}
    (hf : h <=ᶠ[l] f) : h <=ᶠ[l] f ⊔ g :=
  hf.mono fun _ => _root_.le_sup_of_le_left

@[to_dual inf_le_of_right_le]
/--
theorem `EventuallyLE.le_sup_of_le_right` / 定理 `EventuallyLE.le_sup_of_le_right`

English:
theorem EventuallyLE.le_sup_of_le_right
  statement: [SemilatticeSup β] {l : Filter α} {f g h : α -> β}
  proof: hg.mono fun _ => _root_.le_sup_of_le_right

中文:
定理 EventuallyLE.le_sup_of_le_right
  结论: [SemilatticeSup β] {l : 滤子 α} {f g h : α -> β}
  证明: hg.mono fun _ => _root_.le_sup_of_le_right

Depends on / 依赖: _root_, _root_.le_sup_of_le_right, hg.mono, le_sup_of_le_right
-/
theorem EventuallyLE.le_sup_of_le_right [SemilatticeSup β] {l : Filter α} {f g h : α -> β}
    (hg : h <=ᶠ[l] g) : h <=ᶠ[l] f ⊔ g :=
  hg.mono fun _ => _root_.le_sup_of_le_right

/--
theorem `join_le` / 定理 `join_le`

English:
theorem join_le
  given: {f : Filter (Filter α)} {l : Filter α} (h : forallᶠ m in f, m <= l)
  statement: join f <= l
  proof: fun _ hs => h.mono fun _ hm => hm hs

中文:
定理 join_le
  条件: {f : 滤子 (滤子 α)} {l : 滤子 α} (h : 对任意ᶠ m in f, m <= l)
  结论: join f <= l
  证明: fun _ hs => h.mono fun _ hm => hm hs

Depends on / 依赖: h.mono
-/
theorem join_le {f : Filter (Filter α)} {l : Filter α} (h : forallᶠ m in f, m <= l) : join f <= l :=
  fun _ hs => h.mono fun _ hm => hm hs

end EventuallyEq

end Filter

open Filter

/--
theorem `Set.EqOn.eventuallyEq` / 定理 `Set.EqOn.eventuallyEq`

English:
theorem Set.EqOn.eventuallyEq
  given: {α β} {s : Set α} {f g : α -> β} (h : EqOn f g s)
  statement: f =ᶠ[𝓟 s] g
  proof: h

中文:
定理 集合.EqOn.eventuallyEq
  条件: {α β} {s : 集合 α} {f g : α -> β} (h : EqOn f g s)
  结论: f =ᶠ[𝓟 s] g
  证明: h
-/
theorem Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α -> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g :=
  h

/--
theorem `Set.EqOn.eventuallyEq_of_mem` / 定理 `Set.EqOn.eventuallyEq_of_mem`

English:
theorem Set.EqOn.eventuallyEq_of_mem
  statement: {α β} {s : Set α} {l : Filter α} {f g : α -> β} (h : EqOn f g s)
  proof: h.eventuallyEq.filter_mono Filter.le_principal_iff.2 hl

中文:
定理 集合.EqOn.eventuallyEq_of_mem
  结论: {α β} {s : 集合 α} {l : 滤子 α} {f g : α -> β} (h : EqOn f g s)
  证明: h.eventuallyEq.filter_mono Filter.le_principal_iff.2 hl

Depends on / 依赖: Filter, Filter.le_principal_iff, eventuallyEq, filter_mono, h.eventuallyEq.filter_mono, le_principal_iff
-/
theorem Set.EqOn.eventuallyEq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α -> β} (h : EqOn f g s)
    (hl : s in l) : f =ᶠ[l] g :=
h.eventuallyEq.filter_mono Filter.le_principal_iff.2 hl

/--
theorem `LE.le.eventuallyLE` / 定理 `LE.le.eventuallyLE`

English:
theorem LE.le.eventuallyLE
  given: {α} {l : Filter α} {s t : Set α} (h : s subseteq t)
  statement: s <=ᶠ[l] t
  proof: Filter.Eventually.of_forall h

@[deprecated (since := "2026-03-16")] alias HasSubset.Subset.eventuallyLE := LE.le.eventuallyLE

中文:
定理 LE.le.eventuallyLE
  条件: {α} {l : 滤子 α} {s t : 集合 α} (h : s subseteq t)
  结论: s <=ᶠ[l] t
  证明: Filter.Eventually.of_forall h

@[deprecated (since := "2026-03-16")] alias HasSubset.Subset.eventuallyLE := LE.le.eventuallyLE

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, of_forall
-/
theorem LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} (h : s subseteq t) : s <=ᶠ[l] t :=
  Filter.Eventually.of_forall h

@[deprecated (since := "2026-03-16")] alias HasSubset.Subset.eventuallyLE := LE.le.eventuallyLE

variable {α β : Type*} {F : Filter α} {G : Filter β}

namespace Filter

/--
lemma `compl_mem_comk` / 引理 `compl_mem_comk`

English:
lemma compl_mem_comk
  given: {p : Set α -> Prop} {he hmono hunion s}
  proof: by
  simp

中文:
引理 compl_mem_comk
  条件: {p : 集合 α -> 命题} {he hmono hunion s}
  证明: by
  simp
-/
lemma compl_mem_comk {p : Set α -> Prop} {he hmono hunion s} :
    sᶜ in comk p he hmono hunion ↔ p s := by
  simp

end Filter
