/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Ker
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Heyting.Boundary

/-!
# The cofinite filter

In this file we define

`Filter.cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `Filter.atTop`.

## TODO

Define filters for other cardinalities of the complement.
-/

@[expose] public section

open Set Function

variable {ι α β : Type*} {l : Filter α}

namespace Filter

/--
Definition of `cofinite` / `cofinite` 的定义

English:
definition cofinite
  signature: : Filter α
  body: comk Set.Finite finite_empty (fun _t ht _s hsub => ht.subset hsub) fun _ h _ => h.union

@[simp]

中文:
定义 cofinite
  签名: : 滤子 α
  定义体: comk Set.Finite finite_empty (fun _t ht _s hsub => ht.subset hsub) fun _ h _ => h.union

@[simp]

Depends on / 依赖: Finite, Set.Finite, finite_empty, h.union, ht.subset, subset
-/
def cofinite : Filter α :=
  comk Set.Finite finite_empty (fun _t ht _s hsub => ht.subset hsub) fun _ h _ => h.union

@[simp]
/--
theorem `mem_cofinite` / 定理 `mem_cofinite`

English:
theorem mem_cofinite
  given: {s : Set α}
  statement: s in @cofinite α ↔ sᶜ.Finite
  proof: Iff.rfl

@[simp]

中文:
定理 mem_cofinite
  条件: {s : 集合 α}
  结论: s in @cofinite α ↔ sᶜ.有限
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_cofinite {s : Set α} : s in @cofinite α ↔ sᶜ.Finite :=
  Iff.rfl

@[simp]
/--
theorem `eventually_cofinite` / 定理 `eventually_cofinite`

English:
theorem eventually_cofinite
  given: {p : α -> Prop}
  statement: (forallᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
  proof: Iff.rfl

中文:
定理 eventually_cofinite
  条件: {p : α -> 命题}
  结论: (对任意ᶠ x in cofinite, p x) ↔ { x | ¬p x }.有限
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventually_cofinite {p : α -> Prop} : (forallᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite :=
  Iff.rfl

/--
theorem `hasBasis_cofinite` / 定理 `hasBasis_cofinite`

English:
theorem hasBasis_cofinite
  statement: HasBasis cofinite (fun s : Set α => s.Finite) compl
  proof: ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ =>
htf.subset compl_subset_comm.2 hts⟩⟩

中文:
定理 hasBasis_cofinite
  结论: 有基 cofinite (fun s : 集合 α => s.有限) compl
  证明: ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ =>
htf.subset compl_subset_comm.2 hts⟩⟩

Depends on / 依赖: compl_compl, compl_subset_comm, htf.subset, subset
-/
theorem hasBasis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ =>
htf.subset compl_subset_comm.2 hts⟩⟩

/--
Instance `cofinite_neBot` / 实例 `cofinite_neBot`

English:
instance cofinite_neBot
  signature: [Infinite α]
  body: hasBasis_cofinite.neBot_iff.2 fun hs => hs.infinite_compl.nonempty

@[simp]

中文:
实例 cofinite_neBot
  签名: [无限 α]
  定义体: hasBasis_cofinite.neBot_iff.2 fun hs => hs.infinite_compl.nonempty

@[simp]

Depends on / 依赖: hasBasis_cofinite, hasBasis_cofinite.neBot_iff, hs.infinite_compl.nonempty, infinite_compl, neBot_iff, nonempty
-/
instance cofinite_neBot [Infinite α] : NeBot (@cofinite α) :=
  hasBasis_cofinite.neBot_iff.2 fun hs => hs.infinite_compl.nonempty

@[simp]
/--
theorem `cofinite_eq_bot_iff` / 定理 `cofinite_eq_bot_iff`

English:
theorem cofinite_eq_bot_iff
  statement: @cofinite α = ⊥ ↔ Finite α
  proof: by
  simp [← empty_mem_iff_bot, finite_univ_iff]

@[simp]

中文:
定理 cofinite_eq_bot_iff
  结论: @cofinite α = ⊥ ↔ 有限 α
  证明: by
  simp [← empty_mem_iff_bot, finite_univ_iff]

@[simp]

Depends on / 依赖: empty_mem_iff_bot, finite_univ_iff
-/
theorem cofinite_eq_bot_iff : @cofinite α = ⊥ ↔ Finite α := by
  simp [← empty_mem_iff_bot, finite_univ_iff]

@[simp]
/--
theorem `cofinite_eq_bot` / 定理 `cofinite_eq_bot`

English:
theorem cofinite_eq_bot
  given: [Finite α]
  statement: @cofinite α = ⊥
  proof: cofinite_eq_bot_iff.2 ‹_›

中文:
定理 cofinite_eq_bot
  条件: [有限 α]
  结论: @cofinite α = ⊥
  证明: cofinite_eq_bot_iff.2 ‹_›

Depends on / 依赖: cofinite_eq_bot_iff
-/
theorem cofinite_eq_bot [Finite α] : @cofinite α = ⊥ := cofinite_eq_bot_iff.2 ‹_›

/--
theorem `frequently_cofinite_iff_infinite` / 定理 `frequently_cofinite_iff_infinite`

English:
theorem frequently_cofinite_iff_infinite
  given: {p : α -> Prop}
  proof: by
  simp only [Filter.Frequently, eventually_cofinite, not_not, Set.Infinite]

中文:
定理 frequently_cofinite_iff_infinite
  条件: {p : α -> 命题}
  证明: by
  simp only [Filter.Frequently, eventually_cofinite, not_not, Set.Infinite]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, Infinite, Set.Infinite, eventually_cofinite, not_not
-/
theorem frequently_cofinite_iff_infinite {p : α -> Prop} :
    (existsᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x } := by
  simp only [Filter.Frequently, eventually_cofinite, not_not, Set.Infinite]

/--
lemma `frequently_cofinite_mem_iff_infinite` / 引理 `frequently_cofinite_mem_iff_infinite`

English:
lemma frequently_cofinite_mem_iff_infinite
  given: {s : Set α}
  statement: (existsᶠ x in cofinite, x in s) ↔ s.Infinite
  proof: frequently_cofinite_iff_infinite

alias ⟨_, _root_.Set.Infinite.frequently_cofinite⟩ := frequently_cofinite_mem_iff_infinite

@[simp]

中文:
引理 frequently_cofinite_mem_iff_infinite
  条件: {s : 集合 α}
  结论: (存在ᶠ x in cofinite, x in s) ↔ s.无限
  证明: frequently_cofinite_iff_infinite

alias ⟨_, _root_.Set.Infinite.frequently_cofinite⟩ := frequently_cofinite_mem_iff_infinite

@[simp]

Depends on / 依赖: frequently_cofinite_iff_infinite
-/
lemma frequently_cofinite_mem_iff_infinite {s : Set α} : (existsᶠ x in cofinite, x in s) ↔ s.Infinite :=
  frequently_cofinite_iff_infinite

alias ⟨_, _root_.Set.Infinite.frequently_cofinite⟩ := frequently_cofinite_mem_iff_infinite

@[simp]
/--
lemma `cofinite_inf_principal_neBot_iff` / 引理 `cofinite_inf_principal_neBot_iff`

English:
lemma cofinite_inf_principal_neBot_iff
  given: {s : Set α}
  statement: (cofinite ⊓ 𝓟 s).NeBot ↔ s.Infinite
  proof: frequently_mem_iff_neBot.symm.trans frequently_cofinite_mem_iff_infinite

alias ⟨_, _root_.Set.Infinite.cofinite_inf_principal_neBot⟩ := cofinite_inf_principal_neBot_iff

中文:
引理 cofinite_inf_principal_neBot_iff
  条件: {s : 集合 α}
  结论: (cofinite ⊓ 𝓟 s).NeBot ↔ s.无限
  证明: frequently_mem_iff_neBot.symm.trans frequently_cofinite_mem_iff_infinite

alias ⟨_, _root_.Set.Infinite.cofinite_inf_principal_neBot⟩ := cofinite_inf_principal_neBot_iff

Depends on / 依赖: frequently_cofinite_mem_iff_infinite, frequently_mem_iff_neBot, frequently_mem_iff_neBot.symm.trans
-/
lemma cofinite_inf_principal_neBot_iff {s : Set α} : (cofinite ⊓ 𝓟 s).NeBot ↔ s.Infinite :=
  frequently_mem_iff_neBot.symm.trans frequently_cofinite_mem_iff_infinite

alias ⟨_, _root_.Set.Infinite.cofinite_inf_principal_neBot⟩ := cofinite_inf_principal_neBot_iff

/--
theorem `_root_.Set.Finite.compl_mem_cofinite` / 定理 `_root_.Set.Finite.compl_mem_cofinite`

English:
theorem _root_.Set.Finite.compl_mem_cofinite
  given: {s : Set α} (hs : s.Finite)
  statement: sᶜ in @cofinite α
  proof: mem_cofinite.2 (compl_compl s).symm ▸ hs

中文:
定理 _root_.集合.有限.compl_mem_cofinite
  条件: {s : 集合 α} (hs : s.有限)
  结论: sᶜ in @cofinite α
  证明: mem_cofinite.2 (compl_compl s).symm ▸ hs

Depends on / 依赖: compl_compl, mem_cofinite
-/
theorem _root_.Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.Finite) : sᶜ in @cofinite α :=
mem_cofinite.2 (compl_compl s).symm ▸ hs

/--
theorem `_root_.Set.Finite.eventually_cofinite_notMem` / 定理 `_root_.Set.Finite.eventually_cofinite_notMem`

English:
theorem _root_.Set.Finite.eventually_cofinite_notMem
  given: {s : Set α} (hs : s.Finite)
  proof: hs.compl_mem_cofinite

中文:
定理 _root_.集合.有限.eventually_cofinite_notMem
  条件: {s : 集合 α} (hs : s.有限)
  证明: hs.compl_mem_cofinite

Depends on / 依赖: compl_mem_cofinite, hs.compl_mem_cofinite
-/
theorem _root_.Set.Finite.eventually_cofinite_notMem {s : Set α} (hs : s.Finite) :
    forallᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite

/--
theorem `_root_.Finset.eventually_cofinite_notMem` / 定理 `_root_.Finset.eventually_cofinite_notMem`

English:
theorem _root_.Finset.eventually_cofinite_notMem
  given: (s : Finset α)
  statement: forallᶠ x in cofinite, x ∉ s
  proof: s.finite_toSet.eventually_cofinite_notMem

中文:
定理 _root_.有限集.eventually_cofinite_notMem
  条件: (s : 有限集 α)
  结论: 对任意ᶠ x in cofinite, x ∉ s
  证明: s.finite_toSet.eventually_cofinite_notMem

Depends on / 依赖: eventually_cofinite_notMem, finite_toSet, s.finite_toSet.eventually_cofinite_notMem
-/
theorem _root_.Finset.eventually_cofinite_notMem (s : Finset α) : forallᶠ x in cofinite, x ∉ s :=
  s.finite_toSet.eventually_cofinite_notMem

/--
theorem `_root_.Set.infinite_iff_frequently_cofinite` / 定理 `_root_.Set.infinite_iff_frequently_cofinite`

English:
theorem _root_.Set.infinite_iff_frequently_cofinite
  given: {s : Set α}
  proof: frequently_cofinite_iff_infinite.symm

中文:
定理 _root_.集合.infinite_iff_frequently_cofinite
  条件: {s : 集合 α}
  证明: frequently_cofinite_iff_infinite.symm

Depends on / 依赖: frequently_cofinite_iff_infinite, frequently_cofinite_iff_infinite.symm
-/
theorem _root_.Set.infinite_iff_frequently_cofinite {s : Set α} :
    Set.Infinite s ↔ existsᶠ x in cofinite, x in s :=
  frequently_cofinite_iff_infinite.symm

/--
theorem `eventually_cofinite_ne` / 定理 `eventually_cofinite_ne`

English:
theorem eventually_cofinite_ne
  given: (x : α)
  statement: forallᶠ a in cofinite, a != x
  proof: (Set.finite_singleton x).eventually_cofinite_notMem

中文:
定理 eventually_cofinite_ne
  条件: (x : α)
  结论: 对任意ᶠ a in cofinite, a != x
  证明: (Set.finite_singleton x).eventually_cofinite_notMem

Depends on / 依赖: Algebra, Algebra.TensorProduct.productMap, Algebra.smul_def, IsBaseChange, IsBaseChange.equiv_tmul, IsScalarTower, IsScalarTower.toAlgHom, Set.finite_singleton, TensorProduct, convert, e.toLinearMap.restrictScalars, equiv_t, equiv_tmul, eventually_cofinite_notMem, finite_singleton, h.symm, introv, map_mul, productMap, restrictScalars
-/
theorem eventually_cofinite_ne (x : α) : forallᶠ a in cofinite, a != x :=
  (Set.finite_singleton x).eventually_cofinite_notMem

/--
theorem `le_cofinite_iff_compl_singleton_mem` / 定理 `le_cofinite_iff_compl_singleton_mem`

English:
theorem le_cofinite_iff_compl_singleton_mem
  statement: l <= cofinite ↔ forall x, {x}ᶜ in l
  proof: by
  refine ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => ?_⟩
  rw [← compl_compl s]; rw [← biUnion_of_singleton sᶜ]; rw [compl_iUnion₂]; rw [Filter.biInter_mem hs]
  exact fun x _ => h x

中文:
定理 le_cofinite_iff_compl_singleton_mem
  结论: l <= cofinite ↔ 对任意 x, {x}ᶜ in l
  证明: by
  refine ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => ?_⟩
  rw [← compl_compl s]; rw [← biUnion_of_singleton sᶜ]; rw [compl_iUnion₂]; rw [Filter.biInter_mem hs]
  exact fun x _ => h x

Depends on / 依赖: Filter, Filter.biInter_mem, Finite, biInter_mem, biUnion_of_singleton, compl_compl, compl_mem_cofinite, finite_singleton
-/
theorem le_cofinite_iff_compl_singleton_mem : l <= cofinite ↔ forall x, {x}ᶜ in l := by
  refine ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => ?_⟩
  rw [← compl_compl s]; rw [← biUnion_of_singleton sᶜ]; rw [compl_iUnion₂]; rw [Filter.biInter_mem hs]
  exact fun x _ => h x

/--
theorem `le_cofinite_iff_eventually_ne` / 定理 `le_cofinite_iff_eventually_ne`

English:
theorem le_cofinite_iff_eventually_ne
  statement: l <= cofinite ↔ forall x, forallᶠ y in l, y != x
  proof: le_cofinite_iff_compl_singleton_mem

中文:
定理 le_cofinite_iff_eventually_ne
  结论: l <= cofinite ↔ 对任意 x, 对任意ᶠ y in l, y != x
  证明: le_cofinite_iff_compl_singleton_mem

Depends on / 依赖: le_cofinite_iff_compl_singleton_mem
-/
theorem le_cofinite_iff_eventually_ne : l <= cofinite ↔ forall x, forallᶠ y in l, y != x :=
  le_cofinite_iff_compl_singleton_mem

/--
theorem `atTop_le_cofinite` / 定理 `atTop_le_cofinite`

English:
theorem atTop_le_cofinite
  given: [Preorder α] [NoTopOrder α]
  statement: (atTop : Filter α) <= cofinite
  proof: le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop

中文:
定理 atTop_le_cofinite
  条件: [预序 α] [无顶序 α]
  结论: (atTop : 滤子 α) <= cofinite
  证明: le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop

Depends on / 依赖: eventually_ne_atTop, le_cofinite_iff_eventually_ne, le_cofinite_iff_eventually_ne.mpr
-/
theorem atTop_le_cofinite [Preorder α] [NoTopOrder α] : (atTop : Filter α) <= cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop

/--
theorem `atBot_le_cofinite` / 定理 `atBot_le_cofinite`

English:
theorem atBot_le_cofinite
  given: [Preorder α] [NoBotOrder α]
  statement: (atBot : Filter α) <= cofinite
  proof: le_cofinite_iff_eventually_ne.mpr eventually_ne_atBot

中文:
定理 atBot_le_cofinite
  条件: [预序 α] [无底序 α]
  结论: (atBot : 滤子 α) <= cofinite
  证明: le_cofinite_iff_eventually_ne.mpr eventually_ne_atBot

Depends on / 依赖: eventually_ne_atBot, le_cofinite_iff_eventually_ne, le_cofinite_iff_eventually_ne.mpr
-/
theorem atBot_le_cofinite [Preorder α] [NoBotOrder α] : (atBot : Filter α) <= cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atBot

/--
theorem `comap_cofinite_le` / 定理 `comap_cofinite_le`

English:
theorem comap_cofinite_le
  given: (f : α -> β)
  statement: comap f cofinite <= cofinite
  proof: le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun _ => ne_of_apply_ne f⟩

中文:
定理 comap_cofinite_le
  条件: (f : α -> β)
  结论: comap f cofinite <= cofinite
  证明: le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun _ => ne_of_apply_ne f⟩

Depends on / 依赖: compl_mem_cofinite, finite_singleton, le_cofinite_iff_eventually_ne, le_cofinite_iff_eventually_ne.mpr, mem_comap, ne_of_apply_ne
-/
theorem comap_cofinite_le (f : α -> β) : comap f cofinite <= cofinite :=
  le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun _ => ne_of_apply_ne f⟩

/--
theorem `coprod_cofinite` / 定理 `coprod_cofinite`

English:
theorem coprod_cofinite
  statement: (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite
  proof: Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]

中文:
定理 coprod_cofinite
  结论: (cofinite : 滤子 α).coprod (cofinite : 滤子 β) = cofinite
  证明: Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]

Depends on / 依赖: Filter, Filter.coext, compl_compl, compl_mem_coprod, finite_image_fst_and_snd_iff, mem_cofinite
-/
theorem coprod_cofinite : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]

/--
theorem `coprodᵢ_cofinite` / 定理 `coprodᵢ_cofinite`

English:
theorem coprodᵢ_cofinite
  given: {α : ι -> Type*} [Finite ι]
  proof: Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cofinite, compl_compl, forall_finite_image_eval_iff]

中文:
定理 coprodᵢ_cofinite
  条件: {α : ι -> 类型} [有限 ι]
  证明: Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cofinite, compl_compl, forall_finite_image_eval_iff]

Depends on / 依赖: Filter, Filter.coext, compl_compl, forall_finite_image_eval_iff, mem_cofinite
-/
theorem coprodᵢ_cofinite {α : ι -> Type*} [Finite ι] :
    (Filter.coprodᵢ fun i => (cofinite : Filter (α i))) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cofinite, compl_compl, forall_finite_image_eval_iff]

/--
theorem `disjoint_cofinite_left` / 定理 `disjoint_cofinite_left`

English:
theorem disjoint_cofinite_left
  statement: Disjoint cofinite l ↔ exists s in l, Set.Finite s
  proof: by
  simp [l.basis_sets.disjoint_iff_right]

中文:
定理 disjoint_cofinite_left
  结论: Disjoint cofinite l ↔ 存在 s in l, 集合.有限 s
  证明: by
  simp [l.basis_sets.disjoint_iff_right]

Depends on / 依赖: basis_sets, disjoint_iff_right, l.basis_sets.disjoint_iff_right
-/
theorem disjoint_cofinite_left : Disjoint cofinite l ↔ exists s in l, Set.Finite s := by
  simp [l.basis_sets.disjoint_iff_right]

/--
theorem `disjoint_cofinite_right` / 定理 `disjoint_cofinite_right`

English:
theorem disjoint_cofinite_right
  statement: Disjoint l cofinite ↔ exists s in l, Set.Finite s
  proof: disjoint_comm.trans disjoint_cofinite_left

中文:
定理 disjoint_cofinite_right
  结论: Disjoint l cofinite ↔ 存在 s in l, 集合.有限 s
  证明: disjoint_comm.trans disjoint_cofinite_left

Depends on / 依赖: disjoint_cofinite_left, disjoint_comm, disjoint_comm.trans
-/
theorem disjoint_cofinite_right : Disjoint l cofinite ↔ exists s in l, Set.Finite s :=
  disjoint_comm.trans disjoint_cofinite_left

/--
theorem `countable_compl_ker` / 定理 `countable_compl_ker`

English:
theorem countable_compl_ker
  given: [l.IsCountablyGenerated] (h : cofinite <= l)
  statement: Set.Countable l.kerᶜ
  proof: by
  rcases exists_antitone_basis l with ⟨s, hs⟩
  simp only [hs.ker, iInter_true, compl_iInter]
exact countable_iUnion fun n => Set.Finite.countable h hs.mem _

中文:
定理 countable_compl_ker
  条件: [l.是余untablyGenerated] (h : cofinite <= l)
  结论: 集合.可数 l.kerᶜ
  证明: by
  rcases exists_antitone_basis l with ⟨s, hs⟩
  simp only [hs.ker, iInter_true, compl_iInter]
exact countable_iUnion fun n => Set.Finite.countable h hs.mem _

Depends on / 依赖: Finite, Set.Finite.countable, compl_iInter, countable, countable_iUnion, exists_antitone_basis, hs.ker, hs.mem, iInter_true
-/
theorem countable_compl_ker [l.IsCountablyGenerated] (h : cofinite <= l) : Set.Countable l.kerᶜ := by
  rcases exists_antitone_basis l with ⟨s, hs⟩
  simp only [hs.ker, iInter_true, compl_iInter]
exact countable_iUnion fun n => Set.Finite.countable h hs.mem _

/--
theorem `Tendsto.countable_compl_preimage_ker` / 定理 `Tendsto.countable_compl_preimage_ker`

English:
theorem Tendsto.countable_compl_preimage_ker
  statement: {f : α -> β}
  proof: by rw [← ker_comap]; exact countable_compl_ker h.le_comap

中文:
定理 收敛.countable_compl_preimage_ker
  结论: {f : α -> β}
  证明: by rw [← ker_comap]; exact countable_compl_ker h.le_comap

Depends on / 依赖: countable_compl_ker, h.le_comap, ker_comap, le_comap
-/
theorem Tendsto.countable_compl_preimage_ker {f : α -> β}
    {l : Filter β} [l.IsCountablyGenerated] (h : Tendsto f cofinite l) :
    Set.Countable (f ⁻¹' l.ker)ᶜ := by rw [← ker_comap]; exact countable_compl_ker h.le_comap

/--
theorem `univ_pi_mem_pi` / 定理 `univ_pi_mem_pi`

English:
theorem univ_pi_mem_pi
  statement: {α : ι -> Type*} {s : forall i, Set (α i)} {l : forall i, Filter (α i)}
  proof: by
  filter_upwards [pi_mem_pi hfin fun i _ => h i] with a ha i _
  if hi : s i = univ then
    simp [hi]
  else
    exact ha i hi

中文:
定理 univ_pi_mem_pi
  结论: {α : ι -> 类型} {s : 对任意 i, 集合 (α i)} {l : 对任意 i, 滤子 (α i)}
  证明: by
  filter_upwards [pi_mem_pi hfin fun i _ => h i] with a ha i _
  if hi : s i = univ then
    simp [hi]
  else
    exact ha i hi

Depends on / 依赖: filter_upwards, pi_mem_pi
-/
theorem univ_pi_mem_pi {α : ι -> Type*} {s : forall i, Set (α i)} {l : forall i, Filter (α i)}
    (h : forall i, s i in l i) (hfin : forallᶠ i in cofinite, s i = univ) : univ.pi s in pi l := by
  filter_upwards [pi_mem_pi hfin fun i _ => h i] with a ha i _
  if hi : s i = univ then
    simp [hi]
  else
    exact ha i hi

/--
theorem `map_piMap_pi` / 定理 `map_piMap_pi`

English:
theorem map_piMap_pi
  statement: {α β : ι -> Type*} {f : forall i, α i -> β i}
  proof: by
  refine le_antisymm (tendsto_piMap_pi fun _ => tendsto_map) ?_
  refine ((hasBasis_pi fun i => (l i).basis_sets).map _).ge_iff.2 ?_
  rintro ⟨I, s⟩ ⟨hI : I.Finite, hs : forall i in I, s i in l i⟩
  classical
  rw [← univ_pi_piecewise_univ]; rw [piMap_image_univ_pi]
  refine univ_pi_mem_pi (fun i => ?_) ?_
  · by_cases hi : i in I
    · simpa [hi] using image_mem_map (hs i hi)
    · simp [hi]
  · filter_upwards [hf, hI.compl_mem_cofinite] with i hsurj (hiI : i ∉ I)
    simp [hiI, hsurj.range_eq]

中文:
定理 map_piMap_pi
  结论: {α β : ι -> 类型} {f : 对任意 i, α i -> β i}
  证明: by
  refine le_antisymm (tendsto_piMap_pi fun _ => tendsto_map) ?_
  refine ((hasBasis_pi fun i => (l i).basis_sets).map _).ge_iff.2 ?_
  rintro ⟨I, s⟩ ⟨hI : I.Finite, hs : forall i in I, s i in l i⟩
  classical
  rw [← univ_pi_piecewise_univ]; rw [piMap_image_univ_pi]
  refine univ_pi_mem_pi (fun i => ?_) ?_
  · by_cases hi : i in I
    · simpa [hi] using image_mem_map (hs i hi)
    · simp [hi]
  · filter_upwards [hf, hI.compl_mem_cofinite] with i hsurj (hiI : i ∉ I)
    simp [hiI, hsurj.range_eq]

Depends on / 依赖: Finite, I.Finite, basis_sets, classical, compl_mem_cofinite, filter_upwards, ge_iff, hI.compl_mem_cofinite, hasBasis_pi, hsurj.range_eq, image_mem_map, le_antisymm, piMap_image_univ_pi, range_eq, tendsto_map, tendsto_piMap_pi, univ_pi_mem_pi, univ_pi_piecewise_univ
-/
theorem map_piMap_pi {α β : ι -> Type*} {f : forall i, α i -> β i}
    (hf : forallᶠ i in cofinite, Surjective (f i)) (l : forall i, Filter (α i)) :
    map (Pi.map f) (pi l) = pi fun i => map (f i) (l i) := by
  refine le_antisymm (tendsto_piMap_pi fun _ => tendsto_map) ?_
  refine ((hasBasis_pi fun i => (l i).basis_sets).map _).ge_iff.2 ?_
  rintro ⟨I, s⟩ ⟨hI : I.Finite, hs : forall i in I, s i in l i⟩
  classical
  rw [← univ_pi_piecewise_univ]; rw [piMap_image_univ_pi]
  refine univ_pi_mem_pi (fun i => ?_) ?_
  · by_cases hi : i in I
    · simpa [hi] using image_mem_map (hs i hi)
    · simp [hi]
  · filter_upwards [hf, hI.compl_mem_cofinite] with i hsurj (hiI : i ∉ I)
    simp [hiI, hsurj.range_eq]

/--
theorem `map_piMap_pi_finite` / 定理 `map_piMap_pi_finite`

English:
theorem map_piMap_pi_finite
  statement: {α β : ι -> Type*} [Finite ι]
  proof: map_piMap_pi (by simp) l

中文:
定理 map_piMap_pi_finite
  结论: {α β : ι -> 类型} [有限 ι]
  证明: map_piMap_pi (by simp) l

Depends on / 依赖: map_piMap_pi
-/
theorem map_piMap_pi_finite {α β : ι -> Type*} [Finite ι]
    (f : forall i, α i -> β i) (l : forall i, Filter (α i)) :
    map (Pi.map f) (pi l) = pi fun i => map (f i) (l i) :=
  map_piMap_pi (by simp) l

end Filter

open Filter

/--
lemma `Set.Finite.cofinite_inf_principal_compl` / 引理 `Set.Finite.cofinite_inf_principal_compl`

English:
lemma Set.Finite.cofinite_inf_principal_compl
  given: {s : Set α} (hs : s.Finite)
  proof: by
  simpa using hs.compl_mem_cofinite

中文:
引理 集合.有限.cofinite_inf_principal_compl
  条件: {s : 集合 α} (hs : s.有限)
  证明: by
  simpa using hs.compl_mem_cofinite

Depends on / 依赖: compl_mem_cofinite, hs.compl_mem_cofinite
-/
lemma Set.Finite.cofinite_inf_principal_compl {s : Set α} (hs : s.Finite) :
    cofinite ⊓ 𝓟 sᶜ = cofinite := by
  simpa using hs.compl_mem_cofinite

/--
lemma `Set.Finite.cofinite_inf_principal_sdiff` / 引理 `Set.Finite.cofinite_inf_principal_sdiff`

English:
lemma Set.Finite.cofinite_inf_principal_sdiff
  given: {s t : Set α} (ht : t.Finite)
  proof: by
  rw [sdiff_eq]; rw [← inf_principal]; rw [← inf_assoc]; rw [inf_right_comm]; rw [ht.cofinite_inf_principal_compl]

@[deprecated (since := "2026-06-03")]
alias Set.Finite.cofinite_inf_principal_diff := Set.Finite.cofinite_inf_principal_sdiff

中文:
引理 集合.有限.cofinite_inf_principal_sdiff
  条件: {s t : 集合 α} (ht : t.有限)
  证明: by
  rw [sdiff_eq]; rw [← inf_principal]; rw [← inf_assoc]; rw [inf_right_comm]; rw [ht.cofinite_inf_principal_compl]

@[deprecated (since := "2026-06-03")]
alias Set.Finite.cofinite_inf_principal_diff := Set.Finite.cofinite_inf_principal_sdiff

Depends on / 依赖: cofinite_inf_principal_compl, ht.cofinite_inf_principal_compl, inf_assoc, inf_principal, inf_right_comm, sdiff_eq
-/
lemma Set.Finite.cofinite_inf_principal_sdiff {s t : Set α} (ht : t.Finite) :
    cofinite ⊓ 𝓟 (s \ t) = cofinite ⊓ 𝓟 s := by
  rw [sdiff_eq]; rw [← inf_principal]; rw [← inf_assoc]; rw [inf_right_comm]; rw [ht.cofinite_inf_principal_compl]

@[deprecated (since := "2026-06-03")]
alias Set.Finite.cofinite_inf_principal_diff := Set.Finite.cofinite_inf_principal_sdiff

/--
theorem `Nat.cofinite_eq_atTop` / 定理 `Nat.cofinite_eq_atTop`

English:
theorem Nat.cofinite_eq_atTop
  statement: @cofinite Nat = atTop
  proof: by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun N _ => ?_
  simpa only [mem_cofinite, compl_Ici] using! finite_lt_nat N

中文:
定理 自然数.cofinite_eq_atTop
  结论: @cofinite 自然数 = atTop
  证明: by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun N _ => ?_
  simpa only [mem_cofinite, compl_Ici] using! finite_lt_nat N

Depends on / 依赖: atTop_basis, atTop_basis.ge_iff, atTop_le_cofinite, compl_Ici, finite_lt_nat, ge_iff, le_antisymm, mem_cofinite
-/
theorem Nat.cofinite_eq_atTop : @cofinite Nat = atTop := by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun N _ => ?_
  simpa only [mem_cofinite, compl_Ici] using! finite_lt_nat N

/--
theorem `Nat.frequently_atTop_iff_infinite` / 定理 `Nat.frequently_atTop_iff_infinite`

English:
theorem Nat.frequently_atTop_iff_infinite
  given: {p : Nat -> Prop}
  proof: by
  rw [← Nat.cofinite_eq_atTop]; rw [frequently_cofinite_iff_infinite]

中文:
定理 自然数.frequently_atTop_iff_infinite
  条件: {p : 自然数 -> 命题}
  证明: by
  rw [← Nat.cofinite_eq_atTop]; rw [frequently_cofinite_iff_infinite]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, frequently_cofinite_iff_infinite
-/
theorem Nat.frequently_atTop_iff_infinite {p : Nat -> Prop} :
    (existsᶠ n in atTop, p n) ↔ Set.Infinite { n | p n } := by
  rw [← Nat.cofinite_eq_atTop]; rw [frequently_cofinite_iff_infinite]

/--
lemma `Nat.eventually_pos` / 引理 `Nat.eventually_pos`

English:
lemma Nat.eventually_pos
  statement: forallᶠ (k : Nat) in Filter.atTop, 0 < k
  proof: Filter.eventually_of_mem (Filter.mem_atTop_sets.mpr ⟨1, fun _ hx => hx⟩) (fun _ hx => hx)

中文:
引理 自然数.eventually_pos
  结论: 对任意ᶠ (k : 自然数) in 滤子.atTop, 0 < k
  证明: Filter.eventually_of_mem (Filter.mem_atTop_sets.mpr ⟨1, fun _ hx => hx⟩) (fun _ hx => hx)

Depends on / 依赖: Filter, Filter.eventually_of_mem, Filter.mem_atTop_sets.mpr, eventually_of_mem, mem_atTop_sets
-/
lemma Nat.eventually_pos : forallᶠ (k : Nat) in Filter.atTop, 0 < k :=
  Filter.eventually_of_mem (Filter.mem_atTop_sets.mpr ⟨1, fun _ hx => hx⟩) (fun _ hx => hx)

/--
theorem `Filter.Tendsto.exists_within_forall_le` / 定理 `Filter.Tendsto.exists_within_forall_le`

English:
theorem Filter.Tendsto.exists_within_forall_le
  statement: {α β : Type*} [LinearOrder β] {s : Set α}
  proof: by
  by_cases! all_top : exists y in s, exists x, f y < x
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    rcases all_top with ⟨y, hys, x, hx⟩
    have : { y | ¬x <= f y }.Finite := Filter.eventually_cofinite.mp (tendsto_atTop.1 hf x)
    simp only [not_le] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine ⟨a₀, ha₀s, fun a has => (lt_or_ge (f a) x).elim ?_ (le_trans ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
  · -- in this case, f is constant because all values are at top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => all_top a ha (f a₀)⟩

中文:
定理 滤子.收敛.存在_within_对任意_le
  结论: {α β : 类型} [线性序 β] {s : 集合 α}
  证明: by
  by_cases! all_top : exists y in s, exists x, f y < x
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    rcases all_top with ⟨y, hys, x, hx⟩
    have : { y | ¬x <= f y }.Finite := Filter.eventually_cofinite.mp (tendsto_atTop.1 hf x)
    simp only [not_le] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine ⟨a₀, ha₀s, fun a has => (lt_or_ge (f a) x).elim ?_ (le_trans ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
  · -- in this case, f is constant because all values are at top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => all_top a ha (f a₀)⟩

Depends on / 依赖: Filter, Filter.eventually_cofinite.mp, Finite, all_top, eventually_cofinite, exists_min_image, finite, inter_of_left, le_trans, lt_or_ge, nonempty, not_le, others_bigger, points, tendsto_atTop, this.inter_of_left
-/
theorem Filter.Tendsto.exists_within_forall_le {α β : Type*} [LinearOrder β] {s : Set α}
    (hs : s.Nonempty) {f : α -> β} (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) :
    exists a₀ in s, forall a in s, f a₀ <= f a := by
  by_cases! all_top : exists y in s, exists x, f y < x
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    rcases all_top with ⟨y, hys, x, hx⟩
    have : { y | ¬x <= f y }.Finite := Filter.eventually_cofinite.mp (tendsto_atTop.1 hf x)
    simp only [not_le] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine ⟨a₀, ha₀s, fun a has => (lt_or_ge (f a) x).elim ?_ (le_trans ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
  · -- in this case, f is constant because all values are at top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => all_top a ha (f a₀)⟩

/--
theorem `Filter.Tendsto.exists_forall_le` / 定理 `Filter.Tendsto.exists_forall_le`

English:
theorem Filter.Tendsto.exists_forall_le
  statement: [Nonempty α] [LinearOrder β] {f : α -> β}
  proof: let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

中文:
定理 滤子.收敛.存在_对任意_le
  结论: [非空 α] [线性序 β] {f : α -> β}
  证明: let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

Depends on / 依赖: exists_within_forall_le, hf.exists_within_forall_le, mem_univ, univ_nonempty
-/
theorem Filter.Tendsto.exists_forall_le [Nonempty α] [LinearOrder β] {f : α -> β}
    (hf : Tendsto f cofinite atTop) : exists a₀, forall a, f a₀ <= f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

/--
theorem `Filter.Tendsto.exists_within_forall_ge` / 定理 `Filter.Tendsto.exists_within_forall_ge`

English:
theorem Filter.Tendsto.exists_within_forall_ge
  statement: [LinearOrder β] {s : Set α} (hs : s.Nonempty)
  proof: @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf

中文:
定理 滤子.收敛.存在_within_对任意_ge
  结论: [线性序 β] {s : 集合 α} (hs : s.非空)
  证明: @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf

Depends on / 依赖: Filter, Filter.Tendsto.exists_within_forall_le, Tendsto, exists_within_forall_le
-/
theorem Filter.Tendsto.exists_within_forall_ge [LinearOrder β] {s : Set α} (hs : s.Nonempty)
    {f : α -> β} (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) :
    exists a₀ in s, forall a in s, f a <= f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf

/--
theorem `Filter.Tendsto.exists_forall_ge` / 定理 `Filter.Tendsto.exists_forall_ge`

English:
theorem Filter.Tendsto.exists_forall_ge
  statement: [Nonempty α] [LinearOrder β] {f : α -> β}
  proof: @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf

中文:
定理 滤子.收敛.存在_对任意_ge
  结论: [非空 α] [线性序 β] {f : α -> β}
  证明: @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf

Depends on / 依赖: Filter, Filter.Tendsto.exists_forall_le, Tendsto, exists_forall_le
-/
theorem Filter.Tendsto.exists_forall_ge [Nonempty α] [LinearOrder β] {f : α -> β}
    (hf : Tendsto f cofinite atBot) : exists a₀, forall a, f a <= f a₀ :=
  @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf

/--
theorem `Function.Surjective.le_map_cofinite` / 定理 `Function.Surjective.le_map_cofinite`

English:
theorem Function.Surjective.le_map_cofinite
  given: {f : α -> β} (hf : Surjective f)
  proof: fun _ h => .of_preimage h hf

中文:
定理 函数.满射.le_map_cofinite
  条件: {f : α -> β} (hf : 满射 f)
  证明: fun _ h => .of_preimage h hf

Depends on / 依赖: of_preimage
-/
theorem Function.Surjective.le_map_cofinite {f : α -> β} (hf : Surjective f) :
    cofinite <= map f cofinite := fun _ h => .of_preimage h hf

/--
theorem `Function.Injective.tendsto_cofinite` / 定理 `Function.Injective.tendsto_cofinite`

English:
theorem Function.Injective.tendsto_cofinite
  given: {f : α -> β} (hf : Injective f)
  proof: fun _ h => h.preimage hf.injOn

中文:
定理 函数.单射.tendsto_cofinite
  条件: {f : α -> β} (hf : 单射 f)
  证明: fun _ h => h.preimage hf.injOn

Depends on / 依赖: h.preimage, hf.injOn, preimage
-/
theorem Function.Injective.tendsto_cofinite {f : α -> β} (hf : Injective f) :
    Tendsto f cofinite cofinite := fun _ h => h.preimage hf.injOn

/--
theorem `Filter.Tendsto.cofinite_of_finite_preimage_singleton` / 定理 `Filter.Tendsto.cofinite_of_finite_preimage_singleton`

English:
theorem Filter.Tendsto.cofinite_of_finite_preimage_singleton
  statement: {f : α -> β}
  proof: fun _ h => h.preimage' fun b _ => hf b

中文:
定理 滤子.收敛.cofinite_of_finite_preimage_singleton
  结论: {f : α -> β}
  证明: fun _ h => h.preimage' fun b _ => hf b

Depends on / 依赖: h.preimage, preimage
-/
theorem Filter.Tendsto.cofinite_of_finite_preimage_singleton {f : α -> β}
    (hf : forall b, Finite (f ⁻¹' {b})) : Tendsto f cofinite cofinite :=
  fun _ h => h.preimage' fun b _ => hf b

/--
theorem `Function.Injective.comap_cofinite_eq` / 定理 `Function.Injective.comap_cofinite_eq`

English:
theorem Function.Injective.comap_cofinite_eq
  given: {f : α -> β} (hf : Injective f)
  proof: (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

中文:
定理 函数.单射.comap_cofinite_eq
  条件: {f : α -> β} (hf : 单射 f)
  证明: (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

Depends on / 依赖: antisymm, comap_cofinite_le, hf.tendsto_cofinite.le_comap, le_comap, tendsto_cofinite
-/
theorem Function.Injective.comap_cofinite_eq {f : α -> β} (hf : Injective f) :
    comap f cofinite = cofinite :=
  (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

/--
theorem `Function.Injective.nat_tendsto_atTop` / 定理 `Function.Injective.nat_tendsto_atTop`

English:
theorem Function.Injective.nat_tendsto_atTop
  given: {f : Nat -> Nat} (hf : Injective f)
  proof: Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite

中文:
定理 函数.单射.nat_tendsto_atTop
  条件: {f : 自然数 -> 自然数} (hf : 单射 f)
  证明: Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, hf.tendsto_cofinite, tendsto_cofinite
-/
theorem Function.Injective.nat_tendsto_atTop {f : Nat -> Nat} (hf : Injective f) :
    Tendsto f atTop atTop :=
  Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite

/--
lemma `Function.update_eventuallyEq` / 引理 `Function.update_eventuallyEq`

English:
lemma Function.update_eventuallyEq
  given: [DecidableEq α] (f : α -> β) (a : α) (b : β)
  proof: by
  filter_upwards [mem_principal_self _] with u hu using Function.update_of_ne hu _ _

中文:
引理 函数.update_eventuallyEq
  条件: [DecidableEq α] (f : α -> β) (a : α) (b : β)
  证明: by
  filter_upwards [mem_principal_self _] with u hu using Function.update_of_ne hu _ _

Depends on / 依赖: Function, Function.update_of_ne, filter_upwards, mem_principal_self, update_of_ne
-/
lemma Function.update_eventuallyEq [DecidableEq α] (f : α -> β) (a : α) (b : β) :
    Function.update f a b =ᶠ[𝓟 {a}ᶜ] f := by
  filter_upwards [mem_principal_self _] with u hu using Function.update_of_ne hu _ _

/--
lemma `Function.update_eventuallyEq_cofinite` / 引理 `Function.update_eventuallyEq_cofinite`

English:
lemma Function.update_eventuallyEq_cofinite
  given: [DecidableEq α] (f : α -> β) (a : α) (b : β)
  proof: (Function.update_eventuallyEq f a b).filter_mono (by simp)

中文:
引理 函数.update_eventuallyEq_cofinite
  条件: [DecidableEq α] (f : α -> β) (a : α) (b : β)
  证明: (Function.update_eventuallyEq f a b).filter_mono (by simp)

Depends on / 依赖: Function, Function.update_eventuallyEq, filter_mono, update_eventuallyEq
-/
lemma Function.update_eventuallyEq_cofinite [DecidableEq α] (f : α -> β) (a : α) (b : β) :
    Function.update f a b =ᶠ[cofinite] f :=
  (Function.update_eventuallyEq f a b).filter_mono (by simp)

/--
lemma `tendsto_cofinite_pure_iff` / 引理 `tendsto_cofinite_pure_iff`

English:
lemma tendsto_cofinite_pure_iff
  given: {f : α -> β} [Zero β]
  proof: by
  simp [Function.HasFiniteSupport, Function.support]

中文:
引理 tendsto_cofinite_pure_iff
  条件: {f : α -> β} [零 β]
  证明: by
  simp [Function.HasFiniteSupport, Function.support]

Depends on / 依赖: Function, Function.HasFiniteSupport, Function.support, HasFiniteSupport, support
-/
lemma tendsto_cofinite_pure_iff {f : α -> β} [Zero β] :
    Tendsto f cofinite (pure 0) ↔ f.HasFiniteSupport := by
  simp [Function.HasFiniteSupport, Function.support]

variable {f : Filter α}

/--
theorem `le_cofinite_iff_ker` / 定理 `le_cofinite_iff_ker`

English:
theorem le_cofinite_iff_ker
  statement: f <= cofinite ↔ f.ker = ∅
  proof: by
  rw [le_cofinite_iff_compl_singleton_mem]; rw [ker_def]; rw [iInter₂_eq_empty_iff]
  exact forall_congr' fun x => ⟨fun h => ⟨{x}ᶜ, h, by simp⟩,
    fun ⟨s, hs, hx⟩ => mem_of_superset hs (by simpa using hx)⟩

中文:
定理 le_cofinite_iff_ker
  结论: f <= cofinite ↔ f.ker = ∅
  证明: by
  rw [le_cofinite_iff_compl_singleton_mem]; rw [ker_def]; rw [iInter₂_eq_empty_iff]
  exact forall_congr' fun x => ⟨fun h => ⟨{x}ᶜ, h, by simp⟩,
    fun ⟨s, hs, hx⟩ => mem_of_superset hs (by simpa using hx)⟩

Depends on / 依赖: forall_congr, ker_def, le_cofinite_iff_compl_singleton_mem, mem_of_superset
-/
theorem le_cofinite_iff_ker : f <= cofinite ↔ f.ker = ∅ := by
  rw [le_cofinite_iff_compl_singleton_mem]; rw [ker_def]; rw [iInter₂_eq_empty_iff]
  exact forall_congr' fun x => ⟨fun h => ⟨{x}ᶜ, h, by simp⟩,
    fun ⟨s, hs, hx⟩ => mem_of_superset hs (by simpa using hx)⟩

/--
theorem `le_cofinite_iff_boundary` / 定理 `le_cofinite_iff_boundary`

English:
theorem le_cofinite_iff_boundary
  statement: f <= cofinite ↔ Coheyting.boundary f = f
  proof: by
  rw [← Coheyting.inf_hnot_self]; rw [inf_eq_left]; rw [le_cofinite_iff_ker]; rw [Filter.hnot_def]; rw [le_principal_iff]
  constructor
  · intro h
    simp [h]
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    exact hx f.kerᶜ h hx

中文:
定理 le_cofinite_iff_boundary
  结论: f <= cofinite ↔ Coheyting.boundary f = f
  证明: by
  rw [← Coheyting.inf_hnot_self]; rw [inf_eq_left]; rw [le_cofinite_iff_ker]; rw [Filter.hnot_def]; rw [le_principal_iff]
  constructor
  · intro h
    simp [h]
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    exact hx f.kerᶜ h hx

Depends on / 依赖: Coheyting, Coheyting.inf_hnot_self, Filter, Filter.hnot_def, eq_empty_iff_forall_notMem, f.ker, hnot_def, inf_eq_left, inf_hnot_self, le_cofinite_iff_ker, le_principal_iff
-/
theorem le_cofinite_iff_boundary : f <= cofinite ↔ Coheyting.boundary f = f := by
  rw [← Coheyting.inf_hnot_self]; rw [inf_eq_left]; rw [le_cofinite_iff_ker]; rw [Filter.hnot_def]; rw [le_principal_iff]
  constructor
  · intro h
    simp [h]
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    exact hx f.kerᶜ h hx

variable (f)

/--
theorem `boundary_le_cofinite` / 定理 `boundary_le_cofinite`

English:
theorem boundary_le_cofinite
  statement: Coheyting.boundary f <= cofinite
  proof: le_cofinite_iff_boundary.2 (Coheyting.boundary_boundary f)

@[simp]

中文:
定理 boundary_le_cofinite
  结论: Coheyting.boundary f <= cofinite
  证明: le_cofinite_iff_boundary.2 (Coheyting.boundary_boundary f)

@[simp]

Depends on / 依赖: Coheyting, Coheyting.boundary_boundary, boundary_boundary, le_cofinite_iff_boundary
-/
theorem boundary_le_cofinite : Coheyting.boundary f <= cofinite :=
  le_cofinite_iff_boundary.2 (Coheyting.boundary_boundary f)

@[simp]
/--
theorem `boundary_principal` / 定理 `boundary_principal`

English:
theorem boundary_principal
  given: (s : Set α)
  statement: Coheyting.boundary (𝓟 s) = ⊥
  proof: by
  simp [← Coheyting.inf_hnot_self]

中文:
定理 boundary_principal
  条件: (s : 集合 α)
  结论: Coheyting.boundary (𝓟 s) = ⊥
  证明: by
  simp [← Coheyting.inf_hnot_self]

Depends on / 依赖: Coheyting, Coheyting.inf_hnot_self, inf_hnot_self
-/
theorem boundary_principal (s : Set α) : Coheyting.boundary (𝓟 s) = ⊥ := by
  simp [← Coheyting.inf_hnot_self]

/--
theorem `existsUnique_eq_principal_sup_free` / 定理 `existsUnique_eq_principal_sup_free`

English:
theorem existsUnique_eq_principal_sup_free
  proof: by
  refine ⟨(f.ker, Coheyting.boundary f), ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
  · exact boundary_le_cofinite f
  · rw [disjoint_principal_left]
    exact mem_inf_of_right (mem_principal_self f.kerᶜ)
  · rw [← compl_compl f.ker, ← hnot_principal, ← Filter.hnot_def,
      Coheyting.hnot_hnot_sup_boundary]
  · have hqk := congrArg Filter.ker hq.2.2
    rw [ker_sup]; rw [ker_principal]; rw [le_cofinite_iff_ker.mp hq.1]; rw [union_empty] at hqk
    refine congrArg₂ Prod.mk hqk.symm (le_antisymm (le_inf ?_ ?_) ?_)
    · rw [hq.2.2]
      exact le_sup_right
    · rw [Filter.hnot_def, le_principal_iff, ← disjoint_principal_left, hqk]
      exact hq.2.1
    · grw [hq.2.2, Coheyting.boundary_sup_le, boundary_principal, bot_sup_eq]
      exact Coheyting.boundary_le

中文:
定理 存在Unique_eq_principal_sup_free
  证明: by
  refine ⟨(f.ker, Coheyting.boundary f), ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
  · exact boundary_le_cofinite f
  · rw [disjoint_principal_left]
    exact mem_inf_of_right (mem_principal_self f.kerᶜ)
  · rw [← compl_compl f.ker, ← hnot_principal, ← Filter.hnot_def,
      Coheyting.hnot_hnot_sup_boundary]
  · have hqk := congrArg Filter.ker hq.2.2
    rw [ker_sup]; rw [ker_principal]; rw [le_cofinite_iff_ker.mp hq.1]; rw [union_empty] at hqk
    refine congrArg₂ Prod.mk hqk.symm (le_antisymm (le_inf ?_ ?_) ?_)
    · rw [hq.2.2]
      exact le_sup_right
    · rw [Filter.hnot_def, le_principal_iff, ← disjoint_principal_left, hqk]
      exact hq.2.1
    · grw [hq.2.2, Coheyting.boundary_sup_le, boundary_principal, bot_sup_eq]
      exact Coheyting.boundary_le

Depends on / 依赖: Coheyting, Coheyting.boundary, Coheyting.hnot_hnot_sup_boundary, Filter, Filter.hnot_def, Filter.ker, Prod.mk, boundary, boundary_le_cofinite, compl_compl, disjoint_principal_left, f.ker, hnot_def, hnot_hnot_sup_boundary, hnot_principal, hqk.symm, ker_principal, ker_sup, le_antisymm, le_cofinite_iff_ker
-/
theorem existsUnique_eq_principal_sup_free :
    exists! p : Set α × Filter α, p.2 <= cofinite ∧ Disjoint (𝓟 p.1) p.2 ∧ f = 𝓟 p.1 ⊔ p.2 := by
  refine ⟨(f.ker, Coheyting.boundary f), ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
  · exact boundary_le_cofinite f
  · rw [disjoint_principal_left]
    exact mem_inf_of_right (mem_principal_self f.kerᶜ)
  · rw [← compl_compl f.ker, ← hnot_principal, ← Filter.hnot_def,
      Coheyting.hnot_hnot_sup_boundary]
  · have hqk := congrArg Filter.ker hq.2.2
    rw [ker_sup]; rw [ker_principal]; rw [le_cofinite_iff_ker.mp hq.1]; rw [union_empty] at hqk
    refine congrArg₂ Prod.mk hqk.symm (le_antisymm (le_inf ?_ ?_) ?_)
    · rw [hq.2.2]
      exact le_sup_right
    · rw [Filter.hnot_def, le_principal_iff, ← disjoint_principal_left, hqk]
      exact hq.2.1
    · grw [hq.2.2, Coheyting.boundary_sup_le, boundary_principal, bot_sup_eq]
      exact Coheyting.boundary_le

/--
theorem `exists_eq_principal_sup_free` / 定理 `exists_eq_principal_sup_free`

English:
theorem exists_eq_principal_sup_free
  proof: Prod.exists.mp (existsUnique_eq_principal_sup_free f).exists

中文:
定理 存在_eq_principal_sup_free
  证明: Prod.exists.mp (existsUnique_eq_principal_sup_free f).exists

Depends on / 依赖: Prod.exists.mp, existsUnique_eq_principal_sup_free
-/
theorem exists_eq_principal_sup_free :
    exists s g, g <= cofinite ∧ Disjoint (𝓟 s) g ∧ f = 𝓟 s ⊔ g :=
  Prod.exists.mp (existsUnique_eq_principal_sup_free f).exists
