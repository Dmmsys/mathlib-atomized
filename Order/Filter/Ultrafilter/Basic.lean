/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.ZornAtoms

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `hyperfilter`: the ultrafilter extending the cofinite filter.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

open Set Filter

namespace Ultrafilter

variable {f : Ultrafilter α} {s : Set α}

/--
theorem `finite_sUnion_mem_iff` / 定理 `finite_sUnion_mem_iff`

English:
theorem finite_sUnion_mem_iff
  given: {s : Set (Set α)} (hs : s.Finite)
  statement: ⋃₀ s in f ↔ exists t in s, t in f
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ his => simp [union_mem_iff, his, or_and_right, exists_or]

中文:
定理 finite_sUnion_mem_iff
  条件: {s : 集合 (集合 α)} (hs : s.有限)
  结论: ⋃₀ s in f ↔ 存在 t in s, t in f
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ his => simp [union_mem_iff, his, or_and_right, exists_or]

Depends on / 依赖: Finite, Set.Finite.induction_on, exists_or, induction_on, insert, or_and_right, union_mem_iff
-/
theorem finite_sUnion_mem_iff {s : Set (Set α)} (hs : s.Finite) : ⋃₀ s in f ↔ exists t in s, t in f := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ his => simp [union_mem_iff, his, or_and_right, exists_or]

/--
theorem `finite_biUnion_mem_iff` / 定理 `finite_biUnion_mem_iff`

English:
theorem finite_biUnion_mem_iff
  given: {is : Set β} {s : β -> Set α} (his : is.Finite)
  proof: by
  simp only [← sUnion_image, finite_sUnion_mem_iff (his.image s), exists_mem_image]

中文:
定理 finite_biUnion_mem_iff
  条件: {is : 集合 β} {s : β -> 集合 α} (his : is.有限)
  证明: by
  simp only [← sUnion_image, finite_sUnion_mem_iff (his.image s), exists_mem_image]

Depends on / 依赖: exists_mem_image, finite_sUnion_mem_iff, his.image, sUnion_image
-/
theorem finite_biUnion_mem_iff {is : Set β} {s : β -> Set α} (his : is.Finite) :
    (⋃ i in is, s i) in f ↔ exists i in is, s i in f := by
  simp only [← sUnion_image, finite_sUnion_mem_iff (his.image s), exists_mem_image]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_exists_mem_iff` / 引理 `eventually_exists_mem_iff`

English:
lemma eventually_exists_mem_iff
  given: {is : Set β} {P : β -> α -> Prop} (his : is.Finite)
  proof: by
  simp only [Filter.Eventually, Ultrafilter.mem_coe]
  convert! f.finite_biUnion_mem_iff his (s := P) with i
  aesop

中文:
引理 eventually_存在_mem_iff
  条件: {is : 集合 β} {P : β -> α -> 命题} (his : is.有限)
  证明: by
  simp only [Filter.Eventually, Ultrafilter.mem_coe]
  convert! f.finite_biUnion_mem_iff his (s := P) with i
  aesop

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Ultrafilter, Ultrafilter.mem_coe, convert, f.finite_biUnion_mem_iff, finite_biUnion_mem_iff, mem_coe
-/
lemma eventually_exists_mem_iff {is : Set β} {P : β -> α -> Prop} (his : is.Finite) :
    (forallᶠ i in f, exists a in is, P a i) ↔ exists a in is, forallᶠ i in f, P a i := by
  simp only [Filter.Eventually, Ultrafilter.mem_coe]
  convert! f.finite_biUnion_mem_iff his (s := P) with i
  aesop

/--
lemma `eventually_exists_iff` / 引理 `eventually_exists_iff`

English:
lemma eventually_exists_iff
  given: [Finite β] {P : β -> α -> Prop}
  proof: by
  simpa using eventually_exists_mem_iff (f := f) (P := P) Set.finite_univ

中文:
引理 eventually_存在_iff
  条件: [有限 β] {P : β -> α -> 命题}
  证明: by
  simpa using eventually_exists_mem_iff (f := f) (P := P) Set.finite_univ

Depends on / 依赖: Set.finite_univ, eventually_exists_mem_iff, finite_univ
-/
lemma eventually_exists_iff [Finite β] {P : β -> α -> Prop} :
    (forallᶠ i in f, exists a, P a i) ↔ exists a, forallᶠ i in f, P a i := by
  simpa using eventually_exists_mem_iff (f := f) (P := P) Set.finite_univ

/--
theorem `eq_pure_of_finite_mem` / 定理 `eq_pure_of_finite_mem`

English:
theorem eq_pure_of_finite_mem
  given: (h : s.Finite) (h' : s in f)
  statement: exists x in s, f = pure x
  proof: by
  rw [← biUnion_of_singleton s] at h'
  rcases (Ultrafilter.finite_biUnion_mem_iff h).mp h' with ⟨a, has, haf⟩
  exact ⟨a, has, eq_of_le (Filter.le_pure_iff.2 haf)⟩

中文:
定理 eq_pure_of_finite_mem
  条件: (h : s.有限) (h' : s in f)
  结论: 存在 x in s, f = pure x
  证明: by
  rw [← biUnion_of_singleton s] at h'
  rcases (Ultrafilter.finite_biUnion_mem_iff h).mp h' with ⟨a, has, haf⟩
  exact ⟨a, has, eq_of_le (Filter.le_pure_iff.2 haf)⟩

Depends on / 依赖: Filter, Filter.le_pure_iff, Ultrafilter, Ultrafilter.finite_biUnion_mem_iff, biUnion_of_singleton, eq_of_le, finite_biUnion_mem_iff, le_pure_iff
-/
theorem eq_pure_of_finite_mem (h : s.Finite) (h' : s in f) : exists x in s, f = pure x := by
  rw [← biUnion_of_singleton s] at h'
  rcases (Ultrafilter.finite_biUnion_mem_iff h).mp h' with ⟨a, has, haf⟩
  exact ⟨a, has, eq_of_le (Filter.le_pure_iff.2 haf)⟩

/--
theorem `eq_pure_of_finite` / 定理 `eq_pure_of_finite`

English:
theorem eq_pure_of_finite
  given: [Finite α] (f : Ultrafilter α)
  statement: exists a, f = pure a
  proof: (eq_pure_of_finite_mem finite_univ univ_mem).imp fun _ ⟨_, ha⟩ => ha

中文:
定理 eq_pure_of_finite
  条件: [有限 α] (f : Ultrafilter α)
  结论: 存在 a, f = pure a
  证明: (eq_pure_of_finite_mem finite_univ univ_mem).imp fun _ ⟨_, ha⟩ => ha

Depends on / 依赖: eq_pure_of_finite_mem, finite_univ, univ_mem
-/
theorem eq_pure_of_finite [Finite α] (f : Ultrafilter α) : exists a, f = pure a :=
  (eq_pure_of_finite_mem finite_univ univ_mem).imp fun _ ⟨_, ha⟩ => ha

/--
theorem `le_cofinite_or_eq_pure` / 定理 `le_cofinite_or_eq_pure`

English:
theorem le_cofinite_or_eq_pure
  given: (f : Ultrafilter α)
  statement: (f : Filter α) <= cofinite ∨ exists a, f = pure a
  proof: or_iff_not_imp_left.2 fun h =>
    let ⟨_, hs, hfin⟩ := Filter.disjoint_cofinite_right.1 (disjoint_iff_not_le.2 h)
    let ⟨a, _, hf⟩ := eq_pure_of_finite_mem hfin hs
    ⟨a, hf⟩

中文:
定理 le_cofinite_or_eq_pure
  条件: (f : Ultrafilter α)
  结论: (f : 滤子 α) <= cofinite ∨ 存在 a, f = pure a
  证明: or_iff_not_imp_left.2 fun h =>
    let ⟨_, hs, hfin⟩ := Filter.disjoint_cofinite_right.1 (disjoint_iff_not_le.2 h)
    let ⟨a, _, hf⟩ := eq_pure_of_finite_mem hfin hs
    ⟨a, hf⟩

Depends on / 依赖: Filter, Filter.disjoint_cofinite_right, disjoint_cofinite_right, disjoint_iff_not_le, eq_pure_of_finite_mem, or_iff_not_imp_left
-/
theorem le_cofinite_or_eq_pure (f : Ultrafilter α) : (f : Filter α) <= cofinite ∨ exists a, f = pure a :=
  or_iff_not_imp_left.2 fun h =>
    let ⟨_, hs, hfin⟩ := Filter.disjoint_cofinite_right.1 (disjoint_iff_not_le.2 h)
    let ⟨a, _, hf⟩ := eq_pure_of_finite_mem hfin hs
    ⟨a, hf⟩

/--
theorem `exists_ultrafilter_of_finite_inter_nonempty` / 定理 `exists_ultrafilter_of_finite_inter_nonempty`

English:
theorem exists_ultrafilter_of_finite_inter_nonempty
  statement: (S : Set (Set α))
  proof: haveI : NeBot (generate S) :=
    generate_neBot_iff.2 fun _ hts ht =>
      ht.coe_toFinset ▸ cond ht.toFinset (ht.coe_toFinset.symm ▸ hts)
⟨of (generate S), fun _ ht => (of_le <| generate S) GenerateSets.basic ht⟩

中文:
定理 存在_ultrafilter_of_finite_inter_nonempty
  结论: (S : 集合 (集合 α))
  证明: haveI : NeBot (generate S) :=
    generate_neBot_iff.2 fun _ hts ht =>
      ht.coe_toFinset ▸ cond ht.toFinset (ht.coe_toFinset.symm ▸ hts)
⟨of (generate S), fun _ ht => (of_le <| generate S) GenerateSets.basic ht⟩

Depends on / 依赖: GenerateSets, GenerateSets.basic, coe_toFinset, generate, generate_neBot_iff, ht.coe_toFinset, ht.coe_toFinset.symm, ht.toFinset, of_le, toFinset
-/
theorem exists_ultrafilter_of_finite_inter_nonempty (S : Set (Set α))
    (cond : forall T : Finset (Set α), (↑T : Set (Set α)) subseteq S -> (⋂₀ (↑T : Set (Set α))).Nonempty) :
    exists F : Ultrafilter α, S subseteq F.sets :=
  haveI : NeBot (generate S) :=
    generate_neBot_iff.2 fun _ hts ht =>
      ht.coe_toFinset ▸ cond ht.toFinset (ht.coe_toFinset.symm ▸ hts)
⟨of (generate S), fun _ ht => (of_le <| generate S) GenerateSets.basic ht⟩

end Ultrafilter

namespace Filter

open Ultrafilter

@[to_dual]
/--
lemma `atTop_eq_pure_of_isTop` / 引理 `atTop_eq_pure_of_isTop`

English:
lemma atTop_eq_pure_of_isTop
  given: [PartialOrder α] {x : α} (hx : IsTop x)
  proof: { top := x, le_top := hx : OrderTop α }.atTop_eq

中文:
引理 atTop_eq_pure_of_isTop
  条件: [偏序 α] {x : α} (hx : IsTop x)
  证明: { top := x, le_top := hx : OrderTop α }.atTop_eq

Depends on / 依赖: OrderTop, atTop_eq, le_top
-/
lemma atTop_eq_pure_of_isTop [PartialOrder α] {x : α} (hx : IsTop x) :
    (atTop : Filter α) = pure x :=
  { top := x, le_top := hx : OrderTop α }.atTop_eq

/--
theorem `tendsto_iff_ultrafilter` / 定理 `tendsto_iff_ultrafilter`

English:
theorem tendsto_iff_ultrafilter
  given: (f : α -> β) (l₁ : Filter α) (l₂ : Filter β)
  proof: by
  simpa only [tendsto_iff_comap] using le_iff_ultrafilter

中文:
定理 tendsto_iff_ultrafilter
  条件: (f : α -> β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  证明: by
  simpa only [tendsto_iff_comap] using le_iff_ultrafilter

Depends on / 依赖: le_iff_ultrafilter, tendsto_iff_comap
-/
theorem tendsto_iff_ultrafilter (f : α -> β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ forall g : Ultrafilter α, ↑g <= l₁ -> Tendsto f g l₂ := by
  simpa only [tendsto_iff_comap] using le_iff_ultrafilter

section Hyperfilter

variable (α) [Infinite α]

/--
Definition of `hyperfilter` / `hyperfilter` 的定义

English:
definition hyperfilter
  signature: : Ultrafilter α
  body: Ultrafilter.of cofinite

中文:
定义 hyperfilter
  签名: : Ultrafilter α
  定义体: Ultrafilter.of cofinite

Depends on / 依赖: Ultrafilter, Ultrafilter.of, cofinite
-/
noncomputable def hyperfilter : Ultrafilter α :=
  Ultrafilter.of cofinite

variable {α}

/--
theorem `hyperfilter_le_cofinite` / 定理 `hyperfilter_le_cofinite`

English:
theorem hyperfilter_le_cofinite
  statement: ↑(hyperfilter α) <= @cofinite α
  proof: Ultrafilter.of_le cofinite

中文:
定理 hyperfilter_le_cofinite
  结论: ↑(hyperfilter α) <= @cofinite α
  证明: Ultrafilter.of_le cofinite

Depends on / 依赖: Ultrafilter, Ultrafilter.of_le, cofinite, of_le
-/
theorem hyperfilter_le_cofinite : ↑(hyperfilter α) <= @cofinite α :=
  Ultrafilter.of_le cofinite

/--
theorem `_root_.Nat.hyperfilter_le_atTop` / 定理 `_root_.Nat.hyperfilter_le_atTop`

English:
theorem _root_.Nat.hyperfilter_le_atTop
  statement: (hyperfilter Nat).toFilter <= atTop
  proof: hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop

@[simp]

中文:
定理 _root_.自然数.hyperfilter_le_atTop
  结论: (hyperfilter 自然数).toFilter <= atTop
  证明: hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop

@[simp]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, hyperfilter_le_cofinite, hyperfilter_le_cofinite.trans_eq, trans_eq
-/
theorem _root_.Nat.hyperfilter_le_atTop : (hyperfilter Nat).toFilter <= atTop :=
  hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop

@[simp]
/--
theorem `bot_ne_hyperfilter` / 定理 `bot_ne_hyperfilter`

English:
theorem bot_ne_hyperfilter
  statement: (⊥ : Filter α) != hyperfilter α
  proof: (NeBot.ne inferInstance).symm

中文:
定理 bot_ne_hyperfilter
  结论: (⊥ : 滤子 α) != hyperfilter α
  证明: (NeBot.ne inferInstance).symm

Depends on / 依赖: NeBot.ne
-/
theorem bot_ne_hyperfilter : (⊥ : Filter α) != hyperfilter α :=
  (NeBot.ne inferInstance).symm

/--
theorem `notMem_hyperfilter_of_finite` / 定理 `notMem_hyperfilter_of_finite`

English:
theorem notMem_hyperfilter_of_finite
  given: {s : Set α} (hf : s.Finite)
  statement: s ∉ hyperfilter α
  proof: fun hy =>
compl_notMem hy hyperfilter_le_cofinite hf.compl_mem_cofinite

alias _root_.Set.Finite.notMem_hyperfilter := notMem_hyperfilter_of_finite

中文:
定理 notMem_hyperfilter_of_finite
  条件: {s : 集合 α} (hf : s.有限)
  结论: s ∉ hyperfilter α
  证明: fun hy =>
compl_notMem hy hyperfilter_le_cofinite hf.compl_mem_cofinite

alias _root_.Set.Finite.notMem_hyperfilter := notMem_hyperfilter_of_finite
-/
theorem notMem_hyperfilter_of_finite {s : Set α} (hf : s.Finite) : s ∉ hyperfilter α := fun hy =>
compl_notMem hy hyperfilter_le_cofinite hf.compl_mem_cofinite

alias _root_.Set.Finite.notMem_hyperfilter := notMem_hyperfilter_of_finite

/--
theorem `compl_mem_hyperfilter_of_finite` / 定理 `compl_mem_hyperfilter_of_finite`

English:
theorem compl_mem_hyperfilter_of_finite
  given: {s : Set α} (hf : Set.Finite s)
  statement: sᶜ in hyperfilter α
  proof: compl_mem_iff_notMem.2 hf.notMem_hyperfilter

alias _root_.Set.Finite.compl_mem_hyperfilter := compl_mem_hyperfilter_of_finite

中文:
定理 compl_mem_hyperfilter_of_finite
  条件: {s : 集合 α} (hf : 集合.有限 s)
  结论: sᶜ in hyperfilter α
  证明: compl_mem_iff_notMem.2 hf.notMem_hyperfilter

alias _root_.Set.Finite.compl_mem_hyperfilter := compl_mem_hyperfilter_of_finite

Depends on / 依赖: compl_mem_iff_notMem, hf.notMem_hyperfilter, notMem_hyperfilter
-/
theorem compl_mem_hyperfilter_of_finite {s : Set α} (hf : Set.Finite s) : sᶜ in hyperfilter α :=
  compl_mem_iff_notMem.2 hf.notMem_hyperfilter

alias _root_.Set.Finite.compl_mem_hyperfilter := compl_mem_hyperfilter_of_finite

/--
theorem `mem_hyperfilter_of_finite_compl` / 定理 `mem_hyperfilter_of_finite_compl`

English:
theorem mem_hyperfilter_of_finite_compl
  given: {s : Set α} (hf : Set.Finite sᶜ)
  statement: s in hyperfilter α
  proof: compl_compl s ▸ hf.compl_mem_hyperfilter

中文:
定理 mem_hyperfilter_of_finite_compl
  条件: {s : 集合 α} (hf : 集合.有限 sᶜ)
  结论: s in hyperfilter α
  证明: compl_compl s ▸ hf.compl_mem_hyperfilter

Depends on / 依赖: compl_compl, compl_mem_hyperfilter, hf.compl_mem_hyperfilter
-/
theorem mem_hyperfilter_of_finite_compl {s : Set α} (hf : Set.Finite sᶜ) : s in hyperfilter α :=
  compl_compl s ▸ hf.compl_mem_hyperfilter

end Hyperfilter

end Filter
