/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.SupIndep

/-!
# Partitions

A `Partition` of an element `a` in a complete lattice is an independent family of nontrivial
elements whose supremum is `a`.

An important special case is where `s : Set α`, where a `Partition s` corresponds to a partition
of the elements of `s` into a family of nonempty sets.
This is equivalent to a transitive and symmetric binary relation `r : α → α → Prop`
where `s` is the set of all `x` for which `r x x`.

Partitions are ordered by refinement: `P ≤ Q` if every part of `P` is less than or equal to a part
of `Q`.

## Main declarations

* `Partition s`: For `[CompleteLattice α]` and `s : α`, a `Partition s` is an independent
  collection of nontrivial elements whose supremum is `s`.
* `Partition.removeBot`: A constructor for `Partition s` that removes `⊥` from a set of parts.
* `Partition.instOrderTop`: `Partition s` has a top element, consisting of just `s` if `s ≠ ⊥` or
  nothing otherwise.
* `Partition.instSemilatticeInf`: `Partition s` has finite meets `P ⊓ Q` when `α` is a frame,
  given by the collection of all non-bottom infima `p ⊓ q` of parts of the two partitions.
* `Partition.Rel`: The partial equivalence relation induced by a partition of a set.
* `Partition.IsRepFun`: A predicate characterizing a representative function for a partition.

## Representative functions (`IsRepFun`)

`IsRepFun P f` means that `f` sends each element of the support to a representative in its
`Partition.Rel`-class, agrees on related elements, and is the identity outside the support.

This is useful whenever a construction must pick one distinguished element per part of a partition.
For example, in graph theory one may partition edges into parallel classes or vertices into
connected components; a representative function can specify which edge remains when simplifying
parallel edges, or how supervertices are labeled after contraction. Similar uses arise in matroid
theory and in the definition of minors.

Tempting alternatives are to use `Classical.choice` or fix a global well-order and take minimal
representatives. However, these lead to issues with inconsistencies: independent choices need not
respect relations between different instances (e.g. monotonicity of simplifications with respect
to subgraph order), a global order can clash with structure already carried by the type, and maps
between different types need not intertwine two separate canonical choices. Stating hypotheses with
`IsRepFun` keeps the chosen representatives explicit; existence under suitable conditions can be
proved separately.

## TODO

* Link this to `Finpartition`.
* Show that when `α` is a frame `Partition α` also has finite joins, i.e. that it is a lattice.

-/

@[expose] public section
variable {α : Type*} {s t x y z : α} {S : Set α}

open Set

/--
Definition of `Partition` / `Partition` 的定义

English:
structure Partition
  parameters: [CompleteLattice α] (s : α)
  axioms and operations (4):
    - parts : Set α
    - sSupIndep' : sSupIndep parts
    - bot_notMem' : ⊥ ∉ parts
    - sSup_eq' : sSup parts = s

中文:
结构 分拆
  参数: [完备格 α] (s : α)
  公理与运算 (4 个):
    - parts : 集合 α
    - sSupIndep' : sSupIndep parts
    - bot_notMem' : ⊥ ∉ parts
    - sSup_eq' : sSup parts = s
-/
structure Partition [CompleteLattice α] (s : α) where
  /-- The collection of parts -/
  parts : Set α
  /-- The parts are `sSupIndep`. -/
  sSupIndep' : sSupIndep parts
  /-- The bottom element is not a part. -/
  bot_notMem' : ⊥ ∉ parts
  /-- The supremum of all parts is `s`. -/
  sSup_eq' : sSup parts = s

namespace Partition

section Basic

variable [CompleteLattice α] {P Q : Partition s}

instance {s : α} : SetLike (Partition s) α where
  coe := Partition.parts
  coe_injective p p' h := by cases p; cases p'; simpa using h

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: {s : α} (P : Partition s)
  body: P

initialize_simps_projections Partition (parts -> coe, as_prefix coe)

中文:
定义 Simps.coe
  签名: {s : α} (P : 分拆 s)
  定义体: P

initialize_simps_projections Partition (parts -> coe, as_prefix coe)
-/
def Simps.coe {s : α} (P : Partition s) : Set α := P

initialize_simps_projections Partition (parts -> coe, as_prefix coe)

/--
lemma `coe_parts` / 引理 `coe_parts`

English:
lemma coe_parts
  statement: P.parts = P
  proof: rfl

中文:
引理 coe_parts
  结论: P.parts = P
  证明: rfl
-/
@[simp] lemma coe_parts : P.parts = P := rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (hP : forall x, x in P ↔ x in Q)
  statement: P = Q
  proof: SetLike.ext hP

@[simp]

中文:
引理 ext
  条件: (hP : 对任意 x, x in P ↔ x in Q)
  结论: P = Q
  证明: SetLike.ext hP

@[simp]
-/
@[ext] lemma ext (hP : forall x, x in P ↔ x in Q) : P = Q :=
  SetLike.ext hP

@[simp]
/--
lemma `sSupIndep` / 引理 `sSupIndep`

English:
lemma sSupIndep
  given: (P : Partition s)
  statement: sSupIndep (P : Set α)
  proof: P.sSupIndep'

中文:
引理 sSupIndep
  条件: (P : 分拆 s)
  结论: sSupIndep (P : 集合 α)
  证明: P.sSupIndep'

Depends on / 依赖: P.sSupIndep, sSupIndep
-/
lemma sSupIndep (P : Partition s) : sSupIndep (P : Set α) :=
  P.sSupIndep'

/--
lemma `disjoint` / 引理 `disjoint`

English:
lemma disjoint
  given: (hx : x in P) (hy : y in P) (hxy : x != y)
  statement: Disjoint x y
  proof: P.sSupIndep.pairwiseDisjoint hx hy hxy

中文:
引理 disjoint
  条件: (hx : x in P) (hy : y in P) (hxy : x != y)
  结论: Disjoint x y
  证明: P.sSupIndep.pairwiseDisjoint hx hy hxy

Depends on / 依赖: P.sSupIndep.pairwiseDisjoint, pairwiseDisjoint, sSupIndep
-/
lemma disjoint (hx : x in P) (hy : y in P) (hxy : x != y) : Disjoint x y :=
  P.sSupIndep.pairwiseDisjoint hx hy hxy

/--
lemma `pairwiseDisjoint` / 引理 `pairwiseDisjoint`

English:
lemma pairwiseDisjoint
  statement: Set.PairwiseDisjoint (P : Set α) id
  proof: P.sSupIndep'.pairwiseDisjoint

中文:
引理 pairwiseDisjoint
  结论: 集合.PairwiseDisjoint (P : 集合 α) id
  证明: P.sSupIndep'.pairwiseDisjoint

Depends on / 依赖: P.sSupIndep, pairwiseDisjoint, sSupIndep
-/
lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  P.sSupIndep'.pairwiseDisjoint

/--
lemma `eq_or_disjoint` / 引理 `eq_or_disjoint`

English:
lemma eq_or_disjoint
  given: (hx : x in P) (hy : y in P)
  statement: x = y ∨ Disjoint x y
  proof: or_iff_not_imp_left.mpr (P.disjoint hx hy)

中文:
引理 eq_or_disjoint
  条件: (hx : x in P) (hy : y in P)
  结论: x = y ∨ Disjoint x y
  证明: or_iff_not_imp_left.mpr (P.disjoint hx hy)

Depends on / 依赖: P.disjoint, disjoint, or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
lemma eq_or_disjoint (hx : x in P) (hy : y in P) : x = y ∨ Disjoint x y :=
  or_iff_not_imp_left.mpr (P.disjoint hx hy)

/--
lemma `eq_of_not_disjoint` / 引理 `eq_of_not_disjoint`

English:
lemma eq_of_not_disjoint
  given: (hx : x in P) (hy : y in P) (hxy : ¬ Disjoint x y)
  statement: x = y
  proof: (P.eq_or_disjoint hx hy).resolve_right hxy

@[simp]

中文:
引理 eq_of_not_disjoint
  条件: (hx : x in P) (hy : y in P) (hxy : ¬ Disjoint x y)
  结论: x = y
  证明: (P.eq_or_disjoint hx hy).resolve_right hxy

@[simp]

Depends on / 依赖: P.eq_or_disjoint, eq_or_disjoint, resolve_right
-/
lemma eq_of_not_disjoint (hx : x in P) (hy : y in P) (hxy : ¬ Disjoint x y) : x = y :=
  (P.eq_or_disjoint hx hy).resolve_right hxy

@[simp]
/--
lemma `sSup_eq` / 引理 `sSup_eq`

English:
lemma sSup_eq
  given: (P : Partition s)
  statement: sSup P = s
  proof: P.sSup_eq'

@[simp]

中文:
引理 sSup_eq
  条件: (P : 分拆 s)
  结论: sSup P = s
  证明: P.sSup_eq'

@[simp]

Depends on / 依赖: P.sSup_eq, sSup_eq
-/
lemma sSup_eq (P : Partition s) : sSup P = s :=
  P.sSup_eq'

@[simp]
/--
lemma `iSup_eq` / 引理 `iSup_eq`

English:
lemma iSup_eq
  given: (P : Partition s)
  statement: ⨆ x in P, x = s
  proof: by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

中文:
引理 iSup_eq
  条件: (P : 分拆 s)
  结论: ⨆ x in P, x = s
  证明: by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

Depends on / 依赖: P.sSup_eq, sSup_eq, sSup_eq_iSup, simp_rw
-/
lemma iSup_eq (P : Partition s) : ⨆ x in P, x = s := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

/--
lemma `le_of_mem` / 引理 `le_of_mem`

English:
lemma le_of_mem
  given: (P : Partition s) (hx : x in P)
  statement: x <= s
  proof: (le_sSup hx).trans_eq P.sSup_eq

中文:
引理 le_of_mem
  条件: (P : 分拆 s) (hx : x in P)
  结论: x <= s
  证明: (le_sSup hx).trans_eq P.sSup_eq

Depends on / 依赖: P.sSup_eq, le_sSup, sSup_eq, trans_eq
-/
lemma le_of_mem (P : Partition s) (hx : x in P) : x <= s :=
  (le_sSup hx).trans_eq P.sSup_eq

/--
lemma `parts_nonempty` / 引理 `parts_nonempty`

English:
lemma parts_nonempty
  given: (P : Partition s) (hs : s != ⊥)
  statement: (P : Set α).Nonempty
  proof: nonempty_iff_ne_empty.2 fun hP => by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]

中文:
引理 parts_nonempty
  条件: (P : 分拆 s) (hs : s != ⊥)
  结论: (P : 集合 α).非空
  证明: nonempty_iff_ne_empty.2 fun hP => by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]

Depends on / 依赖: P.sSup_eq, nonempty_iff_ne_empty, sSup_empty, sSup_eq
-/
lemma parts_nonempty (P : Partition s) (hs : s != ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP => by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]
/--
lemma `bot_notMem` / 引理 `bot_notMem`

English:
lemma bot_notMem
  given: (P : Partition s)
  statement: ⊥ ∉ P
  proof: P.bot_notMem'

中文:
引理 bot_notMem
  条件: (P : 分拆 s)
  结论: ⊥ ∉ P
  证明: P.bot_notMem'

Depends on / 依赖: P.bot_notMem, bot_notMem
-/
lemma bot_notMem (P : Partition s) : ⊥ ∉ P :=
  P.bot_notMem'

/--
lemma `ne_bot_of_mem` / 引理 `ne_bot_of_mem`

English:
lemma ne_bot_of_mem
  given: (hx : x in P)
  statement: x != ⊥
  proof: fun h => P.bot_notMem h ▸ hx

中文:
引理 ne_bot_of_mem
  条件: (hx : x in P)
  结论: x != ⊥
  证明: fun h => P.bot_notMem h ▸ hx

Depends on / 依赖: P.bot_notMem, bot_notMem
-/
lemma ne_bot_of_mem (hx : x in P) : x != ⊥ :=
fun h => P.bot_notMem h ▸ hx

/--
lemma `bot_lt_of_mem` / 引理 `bot_lt_of_mem`

English:
lemma bot_lt_of_mem
  given: (hx : x in P)
  statement: ⊥ < x
  proof: bot_lt_iff_ne_bot.2 P.ne_bot_of_mem hx

中文:
引理 bot_lt_of_mem
  条件: (hx : x in P)
  结论: ⊥ < x
  证明: bot_lt_iff_ne_bot.2 P.ne_bot_of_mem hx

Depends on / 依赖: P.ne_bot_of_mem, bot_lt_iff_ne_bot, ne_bot_of_mem
-/
lemma bot_lt_of_mem (hx : x in P) : ⊥ < x :=
bot_lt_iff_ne_bot.2 P.ne_bot_of_mem hx

/-- Convert a `Partition s` into a `Partition t` via an equality `s = t`. -/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (P : Partition s) (hst : s = t)
  body: P
  sSupIndep' := P.sSupIndep
  bot_notMem' := P.bot_notMem
  sSup_eq' := hst ▸ P.sSup_eq

@[simp]

中文:
定义 copy
  签名: (P : 分拆 s) (hst : s = t)
  定义体: P
  sSupIndep' := P.sSupIndep
  bot_notMem' := P.bot_notMem
  sSup_eq' := hst ▸ P.sSup_eq

@[simp]
-/
protected def copy (P : Partition s) (hst : s = t) : Partition t where
  parts := P
  sSupIndep' := P.sSupIndep
  bot_notMem' := P.bot_notMem
  sSup_eq' := hst ▸ P.sSup_eq

@[simp]
/--
lemma `mem_copy_iff` / 引理 `mem_copy_iff`

English:
lemma mem_copy_iff
  given: (hst : s = t)
  statement: x in P.copy hst ↔ x in P
  proof: Iff.rfl

中文:
引理 mem_copy_iff
  条件: (hst : s = t)
  结论: x in P.copy hst ↔ x in P
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_copy_iff (hst : s = t) : x in P.copy hst ↔ x in P := Iff.rfl

/-- The natural equivalence between the subtype of parts and the subtype of parts of a copy. -/
@[simps!]
/--
Definition of `partscopyEquiv` / `partscopyEquiv` 的定义

English:
definition partscopyEquiv
  signature: (P : Partition s) (hst : s = t)
  body: Equiv.setCongr rfl

中文:
定义 partscopyEquiv
  签名: (P : 分拆 s) (hst : s = t)
  定义体: Equiv.setCongr rfl

Depends on / 依赖: Equiv.setCongr, setCongr
-/
def partscopyEquiv (P : Partition s) (hst : s = t) : ↥(P.copy hst) ≃ ↥P :=
  Equiv.setCongr rfl

/-- A constructor for `Partition s` that removes `⊥` from the set of parts. -/
@[simps]
/--
Definition of `removeBot` / `removeBot` 的定义

English:
definition removeBot
  signature: (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s)
  body: P \ {⊥}
  sSupIndep' := indep.mono sdiff_subset
  bot_notMem' := by simp
  sSup_eq' := by simp [← hsSup]

@[simp]

中文:
定义 removeBot
  签名: (P : 集合 α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s)
  定义体: P \ {⊥}
  sSupIndep' := indep.mono sdiff_subset
  bot_notMem' := by simp
  sSup_eq' := by simp [← hsSup]

@[simp]
-/
def removeBot (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s) : Partition s where
  parts := P \ {⊥}
  sSupIndep' := indep.mono sdiff_subset
  bot_notMem' := by simp
  sSup_eq' := by simp [← hsSup]

@[simp]
/--
lemma `mem_removeBot` / 引理 `mem_removeBot`

English:
lemma mem_removeBot
  given: (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s)
  proof: Iff.rfl

@[simp]

中文:
引理 mem_removeBot
  条件: (P : 集合 α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_removeBot (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s) :
    x in removeBot P indep hsSup ↔ x in P ∧ x != ⊥ := Iff.rfl

@[simp]
/--
lemma `notMem_of_bot` / 引理 `notMem_of_bot`

English:
lemma notMem_of_bot
  given: (P : Partition (⊥ : α)) (x : α)
  statement: x ∉ P
  proof: by
  rintro hxP
obtain rfl := le_bot_iff.mp P.le_of_mem hxP
  exact P.bot_notMem hxP

中文:
引理 notMem_of_bot
  条件: (P : 分拆 (⊥ : α)) (x : α)
  结论: x ∉ P
  证明: by
  rintro hxP
obtain rfl := le_bot_iff.mp P.le_of_mem hxP
  exact P.bot_notMem hxP

Depends on / 依赖: P.bot_notMem, P.le_of_mem, bot_notMem, le_bot_iff, le_bot_iff.mp, le_of_mem
-/
lemma notMem_of_bot (P : Partition (⊥ : α)) (x : α) : x ∉ P := by
  rintro hxP
obtain rfl := le_bot_iff.mp P.le_of_mem hxP
  exact P.bot_notMem hxP

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (Partition (⊥ : α))
  body: removeBot (∅ : Set α) sSupIndep_empty sSup_empty
  uniq P := by ext; simp

中文:
实例 :
  签名: 唯一 (分拆 (⊥ : α))
  定义体: removeBot (∅ : Set α) sSupIndep_empty sSup_empty
  uniq P := by ext; simp

Depends on / 依赖: removeBot, sSupIndep_empty, sSup_empty
-/
instance : Unique (Partition (⊥ : α)) where
  default := removeBot (∅ : Set α) sSupIndep_empty sSup_empty
  uniq P := by ext; simp

/--
lemma `ne_bot_of_mem'` / 引理 `ne_bot_of_mem'`

English:
lemma ne_bot_of_mem'
  given: (hxP : x in P)
  statement: s != ⊥
  proof: by
  rintro rfl
  exact P.notMem_of_bot _ hxP

中文:
引理 ne_bot_of_mem'
  条件: (hxP : x in P)
  结论: s != ⊥
  证明: by
  rintro rfl
  exact P.notMem_of_bot _ hxP

Depends on / 依赖: P.notMem_of_bot, notMem_of_bot
-/
lemma ne_bot_of_mem' (hxP : x in P) : s != ⊥ := by
  rintro rfl
  exact P.notMem_of_bot _ hxP

end Basic

section Order

variable [CompleteLattice α] {P Q : Partition s}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Partition s)
  body: forall ⦃x⦄, x in P -> exists y in Q, x <= y
  lt := _
  le_refl P x hx := ⟨x, hx, le_rfl⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ hxP
    obtain ⟨z, hz, hyz⟩ := hQR hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x => ⟨fun h 

中文:
实例 :
  签名: 偏序 (分拆 s)
  定义体: forall ⦃x⦄, x in P -> exists y in Q, x <= y
  lt := _
  le_refl P x hx := ⟨x, hx, le_rfl⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ hxP
    obtain ⟨z, hz, hyz⟩ := hQR hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x => ⟨fun h 
-/
instance : PartialOrder (Partition s) where
  le P Q := forall ⦃x⦄, x in P -> exists y in Q, x <= y
  lt := _
  le_refl P x hx := ⟨x, hx, le_rfl⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ hxP
    obtain ⟨z, hz, hyz⟩ := hQR hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp h
      obtain ⟨x', hx', hyx'⟩ := hq hy
      obtain rfl := P.pairwiseDisjoint.eq_of_le h hx' (P.ne_bot_of_mem h) (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq h
    obtain ⟨x', hx', hyx'⟩ := hp hy
    obtain rfl := Q.pairwiseDisjoint.eq_of_le h hx' (Q.ne_bot_of_mem h) (hxy.trans hyx')
    rwa [hxy.antisymm hyx']

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  statement: P <= Q ↔ forall x in P, exists y in Q, x <= y
  proof: .rfl

中文:
引理 le_def
  结论: P <= Q ↔ 对任意 x in P, 存在 y in Q, x <= y
  证明: .rfl
-/
lemma le_def : P <= Q ↔ forall x in P, exists y in Q, x <= y := .rfl

/--
lemma `exists_le_of_mem_le` / 引理 `exists_le_of_mem_le`

English:
lemma exists_le_of_mem_le
  given: (h : P <= Q) (hx : x in P)
  statement: exists y in Q, x <= y
  proof: h hx

中文:
引理 存在_le_of_mem_le
  条件: (h : P <= Q) (hx : x in P)
  结论: 存在 y in Q, x <= y
  证明: h hx
-/
lemma exists_le_of_mem_le (h : P <= Q) (hx : x in P) : exists y in Q, x <= y := h hx

/--
lemma `existsUnique_of_mem_le` / 引理 `existsUnique_of_mem_le`

English:
lemma existsUnique_of_mem_le
  given: (h : P <= Q) (hx : x in P)
  statement: exists! y in Q, x <= y
  proof: by
  obtain ⟨y, hy, hxy⟩ := h hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ => Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose this
  exact le_bot_iff.mp (this hxz hxy)

中文:
引理 存在Unique_of_mem_le
  条件: (h : P <= Q) (hx : x in P)
  结论: 存在! y in Q, x <= y
  证明: by
  obtain ⟨y, hy, hxy⟩ := h hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ => Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose this
  exact le_bot_iff.mp (this hxz hxy)

Depends on / 依赖: P.ne_bot_of_mem, Q.eq_of_not_disjoint, contrapose, eq_of_not_disjoint, le_bot_iff, le_bot_iff.mp, ne_bot_of_mem
-/
lemma existsUnique_of_mem_le (h : P <= Q) (hx : x in P) : exists! y in Q, x <= y := by
  obtain ⟨y, hy, hxy⟩ := h hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ => Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose this
  exact le_bot_iff.mp (this hxz hxy)

/--
Instance `instOrderTop` / 实例 `instOrderTop`

English:
instance instOrderTop
  signature: : OrderTop (Partition s) where
  body: removeBot {s} (sSupIndep_singleton s) sSup_singleton
  le_top P x hxP := by simp [P.ne_bot_of_mem' hxP, P.le_of_mem hxP]

中文:
实例 instOrderTop
  签名: : 有顶序 (分拆 s) where
  定义体: removeBot {s} (sSupIndep_singleton s) sSup_singleton
  le_top P x hxP := by simp [P.ne_bot_of_mem' hxP, P.le_of_mem hxP]

Depends on / 依赖: removeBot, sSupIndep_singleton, sSup_singleton
-/
instance instOrderTop : OrderTop (Partition s) where
  top := removeBot {s} (sSupIndep_singleton s) sSup_singleton
  le_top P x hxP := by simp [P.ne_bot_of_mem' hxP, P.le_of_mem hxP]

/--
lemma `top_def` / 引理 `top_def`

English:
lemma top_def
  statement: (⊤ : Partition s) = removeBot {s} (sSupIndep_singleton s) sSup_singleton
  proof: rfl

中文:
引理 top_def
  结论: (⊤ : 分拆 s) = removeBot {s} (sSupIndep_singleton s) sSup_singleton
  证明: rfl
-/
lemma top_def : (⊤ : Partition s) = removeBot {s} (sSupIndep_singleton s) sSup_singleton := rfl

/--
lemma `parts_top` / 引理 `parts_top`

English:
lemma parts_top
  given: (hs : s != ⊥)
  statement: ((⊤ : Partition s) : Set α) = {s}
  proof: by
  simpa [top_def]

中文:
引理 parts_top
  条件: (hs : s != ⊥)
  结论: ((⊤ : 分拆 s) : 集合 α) = {s}
  证明: by
  simpa [top_def]
-/
@[simp] lemma parts_top (hs : s != ⊥) : ((⊤ : Partition s) : Set α) = {s} := by
  simpa [top_def]

/--
lemma `mem_top_iff` / 引理 `mem_top_iff`

English:
lemma mem_top_iff
  given: {a : α}
  statement: a in (⊤ : Partition s) ↔ a = s ∧ a != ⊥
  proof: by
  rw [top_def]; rw [mem_removeBot]; rw [mem_singleton_iff]

中文:
引理 mem_top_iff
  条件: {a : α}
  结论: a in (⊤ : 分拆 s) ↔ a = s ∧ a != ⊥
  证明: by
  rw [top_def]; rw [mem_removeBot]; rw [mem_singleton_iff]
-/
@[simp] lemma mem_top_iff {a : α} : a in (⊤ : Partition s) ↔ a = s ∧ a != ⊥ := by
  rw [top_def]; rw [mem_removeBot]; rw [mem_singleton_iff]

/--
lemma `parts_top_subset` / 引理 `parts_top_subset`

English:
lemma parts_top_subset
  statement: ((⊤ : Partition s) : Set α) subseteq {s}
  proof: by simp

中文:
引理 parts_top_subset
  结论: ((⊤ : 分拆 s) : 集合 α) subseteq {s}
  证明: by simp
-/
lemma parts_top_subset : ((⊤ : Partition s) : Set α) subseteq {s} := by simp

/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: {α : Type*} [Order.Frame α] (s : α)
  body: removeBot {a | exists p in P, exists q in Q, a = p ⊓ q} (by
      rw [sSupIndep_iff_pairwiseDisjoint]
      intro a ha a' ha' h
      grind [Partition.eq_or_disjoint, Disjoint.inf_left, Disjoint.inf_left'])
    (by
      suffices sSup {a | exists p in P, exists q in Q, a = p ⊓ q} = sSup P ⊓ sSup Q b

中文:
实例 instSemilatticeInf
  签名: {α : 类型} [Order.框架 α] (s : α)
  定义体: removeBot {a | exists p in P, exists q in Q, a = p ⊓ q} (by
      rw [sSupIndep_iff_pairwiseDisjoint]
      intro a ha a' ha' h
      grind [Partition.eq_or_disjoint, Disjoint.inf_left, Disjoint.inf_left'])
    (by
      suffices sSup {a | exists p in P, exists q in Q, a = p ⊓ q} = sSup P ⊓ sSup Q b

Depends on / 依赖: Disjoint, Disjoint.inf_left, Partition, Partition.eq_or_disjoint, eq_or_disjoint, inf_le_, inf_left, le_antisymm, le_sSup_of_le, removeBot, sSupIndep_iff_pairwiseDisjoint, sSup_inf_sSup, sSup_le
-/
instance instSemilatticeInf {α : Type*} [Order.Frame α] (s : α) : SemilatticeInf (Partition s) where
  inf P Q := removeBot {a | exists p in P, exists q in Q, a = p ⊓ q} (by
      rw [sSupIndep_iff_pairwiseDisjoint]
      intro a ha a' ha' h
      grind [Partition.eq_or_disjoint, Disjoint.inf_left, Disjoint.inf_left'])
    (by
      suffices sSup {a | exists p in P, exists q in Q, a = p ⊓ q} = sSup P ⊓ sSup Q by simpa
      rw [sSup_inf_sSup]
      refine le_antisymm ?_ ?_
· exact sSup_le fun a ⟨p, hp, q, hq, ha⟩ => le_iSup₂_of_le (p, q) ⟨hp, hq⟩ by grind
      · exact iSup₂_le fun (p, q) ⟨hp, hq⟩ => le_sSup_of_le ⟨p, hp, q, hq, rfl⟩ (by simp))
  inf_le_left P Q a ha := by
    obtain ⟨⟨p, hp, q, hq, rfl⟩, h⟩ := ha
    grind [inf_le_left]
  inf_le_right P Q a ha := by
    obtain ⟨⟨p, hp, q, hq, rfl⟩, h⟩ := ha
    grind [inf_le_right]
  le_inf P Q R hQ hR a ha := by
    have ⟨q, hq⟩ := hQ ha
    have ⟨r, hr⟩ := hR ha
    refine ⟨q ⊓ r, ⟨?_, ?_⟩, ?_⟩ <;> grind [le_inf_iff, P.ne_bot_of_mem ha]

@[simp]
/--
lemma `mem_inf_iff` / 引理 `mem_inf_iff`

English:
lemma mem_inf_iff
  given: {α : Type*} [Order.Frame α] {s a : α} {P Q : Partition s}
  proof: and_comm

中文:
引理 mem_inf_iff
  条件: {α : 类型} [Order.框架 α] {s a : α} {P Q : 分拆 s}
  证明: and_comm

Depends on / 依赖: and_comm
-/
lemma mem_inf_iff {α : Type*} [Order.Frame α] {s a : α} {P Q : Partition s} :
    a in P ⊓ Q ↔ a != ⊥ ∧ exists p in P, exists q in Q, a = p ⊓ q :=
  and_comm

end Order

variable {S : Set (Set α)} {u s t : Set α} {a b c : α} {P Q : Partition u}

section Set

/--
lemma `sUnion_eq` / 引理 `sUnion_eq`

English:
lemma sUnion_eq
  given: (P : Partition s)
  statement: ⋃₀ P = s
  proof: P.sSup_eq

中文:
引理 sUnion_eq
  条件: (P : 分拆 s)
  结论: ⋃₀ P = s
  证明: P.sSup_eq
-/
@[simp] protected lemma sUnion_eq (P : Partition s) : ⋃₀ P = s := P.sSup_eq

/--
lemma `nonempty_of_mem` / 引理 `nonempty_of_mem`

English:
lemma nonempty_of_mem
  given: (ht : t in P)
  statement: t.Nonempty
  proof: notMem_singleton_empty.1 P.ne_bot_of_mem ht

中文:
引理 nonempty_of_mem
  条件: (ht : t in P)
  结论: t.非空
  证明: notMem_singleton_empty.1 P.ne_bot_of_mem ht

Depends on / 依赖: P.ne_bot_of_mem, ne_bot_of_mem, notMem_singleton_empty
-/
lemma nonempty_of_mem (ht : t in P) : t.Nonempty := notMem_singleton_empty.1 P.ne_bot_of_mem ht

/--
lemma `empty_notMem` / 引理 `empty_notMem`

English:
lemma empty_notMem
  statement: ∅ ∉ P
  proof: P.bot_notMem

中文:
引理 empty_notMem
  结论: ∅ ∉ P
  证明: P.bot_notMem

Depends on / 依赖: P.bot_notMem, bot_notMem
-/
lemma empty_notMem : ∅ ∉ P := P.bot_notMem

/--
lemma `subset_of_mem` / 引理 `subset_of_mem`

English:
lemma subset_of_mem
  given: (ht : t in P)
  statement: t subseteq u
  proof: P.le_of_mem ht

中文:
引理 subset_of_mem
  条件: (ht : t in P)
  结论: t subseteq u
  证明: P.le_of_mem ht

Depends on / 依赖: P.le_of_mem, le_of_mem
-/
lemma subset_of_mem (ht : t in P) : t subseteq u := P.le_of_mem ht

/--
lemma `mem_iff_exists` / 引理 `mem_iff_exists`

English:
lemma mem_iff_exists
  statement: x in u ↔ exists t in P, x in t
  proof: by
  refine ⟨fun hx => ?_, fun ⟨t, htP, hxt⟩ => subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

中文:
引理 mem_iff_存在
  结论: x in u ↔ 存在 t in P, x in t
  证明: by
  refine ⟨fun hx => ?_, fun ⟨t, htP, hxt⟩ => subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

Depends on / 依赖: P.sUnion_eq, mem_sUnion, sUnion_eq, subset_of_mem
-/
lemma mem_iff_exists : x in u ↔ exists t in P, x in t := by
  refine ⟨fun hx => ?_, fun ⟨t, htP, hxt⟩ => subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

/--
lemma `eq_of_mem_inter` / 引理 `eq_of_mem_inter`

English:
lemma eq_of_mem_inter
  given: (ht : t in P) (hs : s in P) (hx : x in t inter s)
  statement: t = s
  proof: P.pairwiseDisjoint.elim ht hs fun (hdj : Disjoint t s) => by simp [hdj.inter_eq] at hx

中文:
引理 eq_of_mem_inter
  条件: (ht : t in P) (hs : s in P) (hx : x in t inter s)
  结论: t = s
  证明: P.pairwiseDisjoint.elim ht hs fun (hdj : Disjoint t s) => by simp [hdj.inter_eq] at hx

Depends on / 依赖: Disjoint, P.pairwiseDisjoint.elim, hdj.inter_eq, inter_eq, pairwiseDisjoint
-/
lemma eq_of_mem_inter (ht : t in P) (hs : s in P) (hx : x in t inter s) : t = s :=
  P.pairwiseDisjoint.elim ht hs fun (hdj : Disjoint t s) => by simp [hdj.inter_eq] at hx

/--
lemma `eq_of_mem_of_mem` / 引理 `eq_of_mem_of_mem`

English:
lemma eq_of_mem_of_mem
  given: (ht : t in P) (hus : s in P) (hxt : x in t) (hxs : x in s)
  statement: t = s
  proof: eq_of_mem_inter ht hus ⟨hxt, hxs⟩

中文:
引理 eq_of_mem_of_mem
  条件: (ht : t in P) (hus : s in P) (hxt : x in t) (hxs : x in s)
  结论: t = s
  证明: eq_of_mem_inter ht hus ⟨hxt, hxs⟩

Depends on / 依赖: eq_of_mem_inter
-/
lemma eq_of_mem_of_mem (ht : t in P) (hus : s in P) (hxt : x in t) (hxs : x in s) : t = s :=
  eq_of_mem_inter ht hus ⟨hxt, hxs⟩

/--
lemma `mem_iff_unique` / 引理 `mem_iff_unique`

English:
lemma mem_iff_unique
  statement: x in u ↔ exists! t, t in P ∧ x in t
  proof: by
  refine ⟨fun hx => ?_, fun ⟨_, ⟨htP, hxt⟩, _⟩ => subset_of_mem htP hxt⟩
  rw [← P.sUnion_eq]; rw [mem_sUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ⟨ht, hxt⟩, fun s ⟨hsP, hxs⟩ => P.eq_of_mem_of_mem hsP ht hxs hxt⟩

中文:
引理 mem_iff_unique
  结论: x in u ↔ 存在! t, t in P ∧ x in t
  证明: by
  refine ⟨fun hx => ?_, fun ⟨_, ⟨htP, hxt⟩, _⟩ => subset_of_mem htP hxt⟩
  rw [← P.sUnion_eq]; rw [mem_sUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ⟨ht, hxt⟩, fun s ⟨hsP, hxs⟩ => P.eq_of_mem_of_mem hsP ht hxs hxt⟩

Depends on / 依赖: P.eq_of_mem_of_mem, P.sUnion_eq, eq_of_mem_of_mem, mem_sUnion, sUnion_eq, subset_of_mem
-/
lemma mem_iff_unique : x in u ↔ exists! t, t in P ∧ x in t := by
  refine ⟨fun hx => ?_, fun ⟨_, ⟨htP, hxt⟩, _⟩ => subset_of_mem htP hxt⟩
  rw [← P.sUnion_eq]; rw [mem_sUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ⟨ht, hxt⟩, fun s ⟨hsP, hxs⟩ => P.eq_of_mem_of_mem hsP ht hxs hxt⟩

/--
lemma `subset_sUnion_and_mem_iff_mem` / 引理 `subset_sUnion_and_mem_iff_mem`

English:
lemma subset_sUnion_and_mem_iff_mem
  given: (hSP : S subseteq P)
  statement: t subseteq ⋃₀ S ∧ t in P ↔ t in S
  proof: by
  refine ⟨fun ⟨htsu, htP⟩ => ?_, fun htS => ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  exact eq_of_mem_of_mem htP (hSP hsS) hxt hxs ▸ hsS

中文:
引理 subset_sUnion_and_mem_iff_mem
  条件: (hSP : S subseteq P)
  结论: t subseteq ⋃₀ S ∧ t in P ↔ t in S
  证明: by
  refine ⟨fun ⟨htsu, htP⟩ => ?_, fun htS => ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  exact eq_of_mem_of_mem htP (hSP hsS) hxt hxs ▸ hsS

Depends on / 依赖: eq_of_mem_of_mem, nonempty_of_mem, subset_sUnion_of_mem
-/
lemma subset_sUnion_and_mem_iff_mem (hSP : S subseteq P) : t subseteq ⋃₀ S ∧ t in P ↔ t in S := by
  refine ⟨fun ⟨htsu, htP⟩ => ?_, fun htS => ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  exact eq_of_mem_of_mem htP (hSP hsS) hxt hxs ▸ hsS

/--
lemma `subset_sUnion_iff_mem` / 引理 `subset_sUnion_iff_mem`

English:
lemma subset_sUnion_iff_mem
  given: (ht : t in P) (hSP : S subseteq P.parts)
  statement: t subseteq ⋃₀ S ↔ t in S
  proof: by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

中文:
引理 subset_sUnion_iff_mem
  条件: (ht : t in P) (hSP : S subseteq P.parts)
  结论: t subseteq ⋃₀ S ↔ t in S
  证明: by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

Depends on / 依赖: subset_sUnion_and_mem_iff_mem
-/
lemma subset_sUnion_iff_mem (ht : t in P) (hSP : S subseteq P.parts) : t subseteq ⋃₀ S ↔ t in S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

/--
Definition of `rep` / `rep` 的定义

English:
definition rep
  signature: (P : Partition u) (ht : t in P)
  body: (P.nonempty_of_mem ht).some

中文:
定义 rep
  签名: (P : 分拆 u) (ht : t in P)
  定义体: (P.nonempty_of_mem ht).some

Depends on / 依赖: P.nonempty_of_mem, nonempty_of_mem
-/
noncomputable def rep (P : Partition u) (ht : t in P) : α := (P.nonempty_of_mem ht).some

/--
lemma `rep_mem` / 引理 `rep_mem`

English:
lemma rep_mem
  given: (ht : t in P)
  statement: P.rep ht in t
  proof: (P.nonempty_of_mem ht).some_mem

中文:
引理 rep_mem
  条件: (ht : t in P)
  结论: P.rep ht in t
  证明: (P.nonempty_of_mem ht).some_mem
-/
@[simp] lemma rep_mem (ht : t in P) : P.rep ht in t := (P.nonempty_of_mem ht).some_mem

/--
lemma `rep_mem_supp` / 引理 `rep_mem_supp`

English:
lemma rep_mem_supp
  given: (ht : t in P)
  statement: P.rep ht in u
  proof: P.subset_of_mem ht rep_mem ht

中文:
引理 rep_mem_supp
  条件: (ht : t in P)
  结论: P.rep ht in u
  证明: P.subset_of_mem ht rep_mem ht
-/
@[simp] lemma rep_mem_supp (ht : t in P) : P.rep ht in u := P.subset_of_mem ht rep_mem ht

end Set

/-! ### Induced relation -/

section Rel

/--
Definition of `Rel` / `Rel` 的定义

English:
definition Rel
  signature: (P : Partition s) (a b : α)
  body: exists t in P, a in t ∧ b in t

中文:
定义 关系
  签名: (P : 分拆 s) (a b : α)
  定义体: exists t in P, a in t ∧ b in t
-/
def Rel (P : Partition s) (a b : α) : Prop :=
  exists t in P, a in t ∧ b in t

/--
lemma `rel_le_iff_le` / 引理 `rel_le_iff_le`

English:
lemma rel_le_iff_le
  statement: P.Rel <= Q.Rel ↔ P <= Q
  proof: by
  refine ⟨fun h S hS => ?_, fun h a b ⟨t, ht, ha, hb⟩ => ?_⟩
  · obtain ⟨x, hxS⟩ := nonempty_of_mem hS
    obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
    refine ⟨T, hT, fun a haS => ?_⟩
    obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
    exact eq_of_mem_of_mem hT hT' hxT hxT' ▸

中文:
引理 rel_le_iff_le
  结论: P.关系 <= Q.关系 ↔ P <= Q
  证明: by
  refine ⟨fun h S hS => ?_, fun h a b ⟨t, ht, ha, hb⟩ => ?_⟩
  · obtain ⟨x, hxS⟩ := nonempty_of_mem hS
    obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
    refine ⟨T, hT, fun a haS => ?_⟩
    obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
    exact eq_of_mem_of_mem hT hT' hxT hxT' ▸

Depends on / 依赖: eq_of_mem_of_mem, nonempty_of_mem
-/
lemma rel_le_iff_le : P.Rel <= Q.Rel ↔ P <= Q := by
  refine ⟨fun h S hS => ?_, fun h a b ⟨t, ht, ha, hb⟩ => ?_⟩
  · obtain ⟨x, hxS⟩ := nonempty_of_mem hS
    obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
    refine ⟨T, hT, fun a haS => ?_⟩
    obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
    exact eq_of_mem_of_mem hT hT' hxT hxT' ▸ haT'
  obtain ⟨t', ht', htt'⟩ := h ht
  use t', ht', htt' ha, htt' hb

/--
lemma `Rel.exists` / 引理 `Rel.exists`

English:
lemma Rel.exists
  given: (h : P.Rel x y)
  statement: exists t in P, x in t ∧ y in t
  proof: h

中文:
引理 关系.存在
  条件: (h : P.关系 x y)
  结论: 存在 t in P, x in t ∧ y in t
  证明: h
-/
lemma Rel.exists (h : P.Rel x y) : exists t in P, x in t ∧ y in t := h

/--
lemma `Rel.forall` / 引理 `Rel.forall`

English:
lemma Rel.forall
  given: (h : P.Rel x y) (ht : t in P)
  statement: x in t ↔ y in t
  proof: by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h => by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h => by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

@[simp]

中文:
引理 关系.对任意
  条件: (h : P.关系 x y) (ht : t in P)
  结论: x in t ↔ y in t
  证明: by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h => by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h => by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

@[simp]

Depends on / 依赖: P.eq_of_mem_of_mem, eq_of_mem_of_mem
-/
lemma Rel.forall (h : P.Rel x y) (ht : t in P) : x in t ↔ y in t := by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h => by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h => by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

@[simp]
/--
lemma `rel_rfl_iff` / 引理 `rel_rfl_iff`

English:
lemma rel_rfl_iff
  statement: P.Rel x x ↔ x in u
  proof: by
  refine ⟨fun ⟨t, ht, hxP, _⟩ => subset_of_mem ht hxP, fun hx => ?_⟩
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.mem_iff_unique.mp hx
  exact ⟨t, ht, hxt, hxt⟩

中文:
引理 rel_rfl_iff
  结论: P.关系 x x ↔ x in u
  证明: by
  refine ⟨fun ⟨t, ht, hxP, _⟩ => subset_of_mem ht hxP, fun hx => ?_⟩
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.mem_iff_unique.mp hx
  exact ⟨t, ht, hxt, hxt⟩

Depends on / 依赖: P.mem_iff_unique.mp, mem_iff_unique, subset_of_mem
-/
lemma rel_rfl_iff : P.Rel x x ↔ x in u := by
  refine ⟨fun ⟨t, ht, hxP, _⟩ => subset_of_mem ht hxP, fun hx => ?_⟩
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.mem_iff_unique.mp hx
  exact ⟨t, ht, hxt, hxt⟩

instance (P : Partition u) : Std.Symm P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ => ⟨t, ht, hb, ha⟩

instance (P : Partition u) : IsTrans α P.Rel where
  trans _ _ _ := fun ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩ =>
    ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩

/--
lemma `Rel.symm` / 引理 `Rel.symm`

English:
lemma Rel.symm
  given: (h : P.Rel x y)
  statement: P.Rel y x
  proof: symm_of P.Rel h

中文:
引理 关系.symm
  条件: (h : P.关系 x y)
  结论: P.关系 y x
  证明: symm_of P.Rel h
-/
@[symm] lemma Rel.symm (h : P.Rel x y) : P.Rel y x := symm_of P.Rel h

/--
lemma `rel_comm` / 引理 `rel_comm`

English:
lemma rel_comm
  statement: P.Rel x y ↔ P.Rel y x
  proof: ⟨Rel.symm, Rel.symm⟩

中文:
引理 rel_comm
  结论: P.关系 x y ↔ P.关系 y x
  证明: ⟨Rel.symm, Rel.symm⟩

Depends on / 依赖: Rel.symm
-/
lemma rel_comm : P.Rel x y ↔ P.Rel y x := ⟨Rel.symm, Rel.symm⟩

/--
lemma `Rel.trans` / 引理 `Rel.trans`

English:
lemma Rel.trans
  given: (hxy : P.Rel x y) (hyz : P.Rel y z)
  statement: P.Rel x z
  proof: trans_of P.Rel hxy hyz

中文:
引理 关系.trans
  条件: (hxy : P.关系 x y) (hyz : P.关系 y z)
  结论: P.关系 x z
  证明: trans_of P.Rel hxy hyz
-/
lemma Rel.trans (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z := trans_of P.Rel hxy hyz

/--
lemma `Rel.left_mem` / 引理 `Rel.left_mem`

English:
lemma Rel.left_mem
  given: (h : P.Rel x y)
  statement: x in u
  proof: by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

中文:
引理 关系.left_mem
  条件: (h : P.关系 x y)
  结论: x in u
  证明: by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

Depends on / 依赖: subset_of_mem
-/
lemma Rel.left_mem (h : P.Rel x y) : x in u := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

/--
lemma `Rel.right_mem` / 引理 `Rel.right_mem`

English:
lemma Rel.right_mem
  given: (h : P.Rel x y)
  statement: y in u
  proof: h.symm.left_mem

中文:
引理 关系.right_mem
  条件: (h : P.关系 x y)
  结论: y in u
  证明: h.symm.left_mem

Depends on / 依赖: h.symm.left_mem, left_mem
-/
lemma Rel.right_mem (h : P.Rel x y) : y in u := h.symm.left_mem

/--
lemma `rep_rel` / 引理 `rep_rel`

English:
lemma rep_rel
  given: (ht : t in P) (hx : x in t)
  statement: P.Rel x (P.rep ht)
  proof: ⟨t, ht, hx, P.rep_mem ht⟩

中文:
引理 rep_rel
  条件: (ht : t in P) (hx : x in t)
  结论: P.关系 x (P.rep ht)
  证明: ⟨t, ht, hx, P.rep_mem ht⟩

Depends on / 依赖: P.rep_mem, rep_mem
-/
lemma rep_rel (ht : t in P) (hx : x in t) : P.Rel x (P.rep ht) := ⟨t, ht, hx, P.rep_mem ht⟩

end Rel

section partOf

/--
Definition of `partOf` / `partOf` 的定义

English:
definition partOf
  signature: (P : Partition u) (a : α)
  body: {b | P.Rel a b}

中文:
定义 partOf
  签名: (P : 分拆 u) (a : α)
  定义体: {b | P.Rel a b}

Depends on / 依赖: P.Rel
-/
def partOf (P : Partition u) (a : α) : Set α := {b | P.Rel a b}

/--
lemma `partOf_subset` / 引理 `partOf_subset`

English:
lemma partOf_subset
  statement: P.partOf x subseteq u
  proof: fun _ ⟨_, ht, _, hyt⟩ => subset_of_mem ht hyt

中文:
引理 partOf_subset
  结论: P.partOf x subseteq u
  证明: fun _ ⟨_, ht, _, hyt⟩ => subset_of_mem ht hyt

Depends on / 依赖: subset_of_mem
-/
lemma partOf_subset : P.partOf x subseteq u := fun _ ⟨_, ht, _, hyt⟩ => subset_of_mem ht hyt

/--
lemma `mem_partOf_iff` / 引理 `mem_partOf_iff`

English:
lemma mem_partOf_iff
  statement: x in P.partOf y ↔ P.Rel y x
  proof: Iff.rfl

中文:
引理 mem_partOf_iff
  结论: x in P.partOf y ↔ P.关系 y x
  证明: Iff.rfl
-/
@[simp] lemma mem_partOf_iff : x in P.partOf y ↔ P.Rel y x := Iff.rfl

/--
lemma `eq_partOf_of_mem` / 引理 `eq_partOf_of_mem`

English:
lemma eq_partOf_of_mem
  given: (ht : t in P) (hxt : x in t)
  statement: t = P.partOf x
  proof: by
  ext y
  exact ⟨(⟨t, ht, hxt, ·⟩), fun ⟨s, hsP, hxs, hys⟩ => (P.eq_of_mem_of_mem ht hsP hxt hxs) ▸ hys⟩

中文:
引理 eq_partOf_of_mem
  条件: (ht : t in P) (hxt : x in t)
  结论: t = P.partOf x
  证明: by
  ext y
  exact ⟨(⟨t, ht, hxt, ·⟩), fun ⟨s, hsP, hxs, hys⟩ => (P.eq_of_mem_of_mem ht hsP hxt hxs) ▸ hys⟩

Depends on / 依赖: P.eq_of_mem_of_mem, eq_of_mem_of_mem
-/
lemma eq_partOf_of_mem (ht : t in P) (hxt : x in t) : t = P.partOf x := by
  ext y
  exact ⟨(⟨t, ht, hxt, ·⟩), fun ⟨s, hsP, hxs, hys⟩ => (P.eq_of_mem_of_mem ht hsP hxt hxs) ▸ hys⟩

/--
lemma `mem_iff_mem_partOf_mem` / 引理 `mem_iff_mem_partOf_mem`

English:
lemma mem_iff_mem_partOf_mem
  statement: x in u ↔ x in P.partOf x ∧ P.partOf x in P
  proof: by
  refine ⟨fun hx => ?_, fun ⟨hx, hP⟩ => subset_of_mem hP hx⟩
  obtain ⟨t, htP, hxt⟩ := P.mem_iff_exists.mp hx
  exact P.eq_partOf_of_mem htP hxt ▸ ⟨hxt, htP⟩

中文:
引理 mem_iff_mem_partOf_mem
  结论: x in u ↔ x in P.partOf x ∧ P.partOf x in P
  证明: by
  refine ⟨fun hx => ?_, fun ⟨hx, hP⟩ => subset_of_mem hP hx⟩
  obtain ⟨t, htP, hxt⟩ := P.mem_iff_exists.mp hx
  exact P.eq_partOf_of_mem htP hxt ▸ ⟨hxt, htP⟩

Depends on / 依赖: P.eq_partOf_of_mem, P.mem_iff_exists.mp, eq_partOf_of_mem, mem_iff_exists, subset_of_mem
-/
lemma mem_iff_mem_partOf_mem : x in u ↔ x in P.partOf x ∧ P.partOf x in P := by
  refine ⟨fun hx => ?_, fun ⟨hx, hP⟩ => subset_of_mem hP hx⟩
  obtain ⟨t, htP, hxt⟩ := P.mem_iff_exists.mp hx
  exact P.eq_partOf_of_mem htP hxt ▸ ⟨hxt, htP⟩

/--
lemma `mem_partOf` / 引理 `mem_partOf`

English:
lemma mem_partOf
  given: (hxu : x in u)
  statement: x in P.partOf x
  proof: (P.mem_iff_mem_partOf_mem.mp hxu).1

中文:
引理 mem_partOf
  条件: (hxu : x in u)
  结论: x in P.partOf x
  证明: (P.mem_iff_mem_partOf_mem.mp hxu).1

Depends on / 依赖: P.mem_iff_mem_partOf_mem.mp, mem_iff_mem_partOf_mem
-/
lemma mem_partOf (hxu : x in u) : x in P.partOf x := (P.mem_iff_mem_partOf_mem.mp hxu).1

/--
lemma `partOf_mem` / 引理 `partOf_mem`

English:
lemma partOf_mem
  given: (hxu : x in u)
  statement: P.partOf x in P
  proof: (P.mem_iff_mem_partOf_mem.mp hxu).2

@[simp]

中文:
引理 partOf_mem
  条件: (hxu : x in u)
  结论: P.partOf x in P
  证明: (P.mem_iff_mem_partOf_mem.mp hxu).2

@[simp]

Depends on / 依赖: P.mem_iff_mem_partOf_mem.mp, mem_iff_mem_partOf_mem
-/
lemma partOf_mem (hxu : x in u) : P.partOf x in P := (P.mem_iff_mem_partOf_mem.mp hxu).2

@[simp]
/--
lemma `partOf_rep` / 引理 `partOf_rep`

English:
lemma partOf_rep
  given: (hs : s in P)
  statement: P.partOf (P.rep hs) = s
  proof: .symm eq_partOf_of_mem hs (rep_mem hs)

中文:
引理 partOf_rep
  条件: (hs : s in P)
  结论: P.partOf (P.rep hs) = s
  证明: .symm eq_partOf_of_mem hs (rep_mem hs)

Depends on / 依赖: eq_partOf_of_mem, rep_mem
-/
lemma partOf_rep (hs : s in P) : P.partOf (P.rep hs) = s :=
.symm eq_partOf_of_mem hs (rep_mem hs)

/--
lemma `mem_iff_exists_partOf` / 引理 `mem_iff_exists_partOf`

English:
lemma mem_iff_exists_partOf
  statement: s in P ↔ exists x in u, partOf P x = s
  proof: ⟨fun hs => ⟨P.rep hs, rep_mem_supp hs, partOf_rep hs⟩, fun ⟨_, hxu, h⟩ => h ▸ partOf_mem hxu⟩

中文:
引理 mem_iff_存在_partOf
  结论: s in P ↔ 存在 x in u, partOf P x = s
  证明: ⟨fun hs => ⟨P.rep hs, rep_mem_supp hs, partOf_rep hs⟩, fun ⟨_, hxu, h⟩ => h ▸ partOf_mem hxu⟩

Depends on / 依赖: P.rep, partOf_mem, partOf_rep, rep_mem_supp
-/
lemma mem_iff_exists_partOf : s in P ↔ exists x in u, partOf P x = s :=
  ⟨fun hs => ⟨P.rep hs, rep_mem_supp hs, partOf_rep hs⟩, fun ⟨_, hxu, h⟩ => h ▸ partOf_mem hxu⟩

/--
lemma `partOf_nonempty_iff` / 引理 `partOf_nonempty_iff`

English:
lemma partOf_nonempty_iff
  statement: (P.partOf x).Nonempty ↔ x in u
  proof: by
  refine ⟨fun ⟨y, hy⟩ => hy.left_mem, fun h => ?_⟩
  simpa [nonempty_iff_ne_empty] using P.ne_bot_of_mem (partOf_mem h)

@[simp]

中文:
引理 partOf_nonempty_iff
  结论: (P.partOf x).非空 ↔ x in u
  证明: by
  refine ⟨fun ⟨y, hy⟩ => hy.left_mem, fun h => ?_⟩
  simpa [nonempty_iff_ne_empty] using P.ne_bot_of_mem (partOf_mem h)

@[simp]

Depends on / 依赖: P.ne_bot_of_mem, hy.left_mem, left_mem, ne_bot_of_mem, nonempty_iff_ne_empty, partOf_mem
-/
lemma partOf_nonempty_iff : (P.partOf x).Nonempty ↔ x in u := by
  refine ⟨fun ⟨y, hy⟩ => hy.left_mem, fun h => ?_⟩
  simpa [nonempty_iff_ne_empty] using P.ne_bot_of_mem (partOf_mem h)

@[simp]
/--
lemma `partOf_eq_empty_iff` / 引理 `partOf_eq_empty_iff`

English:
lemma partOf_eq_empty_iff
  statement: P.partOf x = ∅ ↔ x ∉ u
  proof: by
  rw [← partOf_nonempty_iff]; rw [not_nonempty_iff_eq_empty]

中文:
引理 partOf_eq_empty_iff
  结论: P.partOf x = ∅ ↔ x ∉ u
  证明: by
  rw [← partOf_nonempty_iff]; rw [not_nonempty_iff_eq_empty]

Depends on / 依赖: not_nonempty_iff_eq_empty, partOf_nonempty_iff
-/
lemma partOf_eq_empty_iff : P.partOf x = ∅ ↔ x ∉ u := by
  rw [← partOf_nonempty_iff]; rw [not_nonempty_iff_eq_empty]

/--
lemma `rel_iff_partOf_eq_partOf_of_mem` / 引理 `rel_iff_partOf_eq_partOf_of_mem`

English:
lemma rel_iff_partOf_eq_partOf_of_mem
  given: (P : Partition u) (hx : x in u) (hy : y in u)
  proof: by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ => eq_partOf_of_mem (P.partOf_mem hx) ?_,
    fun h => ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, h ▸ mem_partOf hy⟩⟩
  rwa [← eq_partOf_of_mem htP hxt]

中文:
引理 rel_iff_partOf_eq_partOf_of_mem
  条件: (P : 分拆 u) (hx : x in u) (hy : y in u)
  证明: by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ => eq_partOf_of_mem (P.partOf_mem hx) ?_,
    fun h => ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, h ▸ mem_partOf hy⟩⟩
  rwa [← eq_partOf_of_mem htP hxt]

Depends on / 依赖: P.mem_partOf, P.partOf, P.partOf_mem, eq_partOf_of_mem, mem_partOf, partOf, partOf_mem
-/
lemma rel_iff_partOf_eq_partOf_of_mem (P : Partition u) (hx : x in u) (hy : y in u) :
    P.Rel x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ => eq_partOf_of_mem (P.partOf_mem hx) ?_,
    fun h => ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, h ▸ mem_partOf hy⟩⟩
  rwa [← eq_partOf_of_mem htP hxt]

/--
lemma `rel_iff_partOf_eq_partOf` / 引理 `rel_iff_partOf_eq_partOf`

English:
lemma rel_iff_partOf_eq_partOf
  given: (P : Partition u)
  proof: by
  grind [rel_iff_partOf_eq_partOf_of_mem, Rel.left_mem, Rel.right_mem]

中文:
引理 rel_iff_partOf_eq_partOf
  条件: (P : 分拆 u)
  证明: by
  grind [rel_iff_partOf_eq_partOf_of_mem, Rel.left_mem, Rel.right_mem]

Depends on / 依赖: Rel.left_mem, Rel.right_mem, left_mem, rel_iff_partOf_eq_partOf_of_mem, right_mem
-/
lemma rel_iff_partOf_eq_partOf (P : Partition u) :
    P.Rel x y ↔ exists (_ : x in u) (_ : y in u), P.partOf x = P.partOf y := by
  grind [rel_iff_partOf_eq_partOf_of_mem, Rel.left_mem, Rel.right_mem]

end partOf

/-! ### Representative functions

See the module docstring for motivation (graph simplification, minors, and why we use an explicit
`IsRepFun` hypothesis rather than a global choice of representatives).
-/

section IsRepFun

/--
Definition of `IsRepFun` / `IsRepFun` 的定义

English:
structure IsRepFun
  parameters: {u : Set α} (P : Partition u) (f : α -> α)
  axioms and operations (3):
    - apply_of_notMem : forall ⦃a⦄, a ∉ u -> f a = a
    - rel_apply : forall ⦃a⦄, a in u -> P.Rel a (f a)
    - apply_eq_apply : forall ⦃a b⦄, P.Rel a b -> f a = f b

中文:
结构 是RepFun
  参数: {u : 集合 α} (P : 分拆 u) (f : α -> α)
  公理与运算 (3 个):
    - apply_of_notMem : 对任意 ⦃a⦄, a ∉ u -> f a = a
    - rel_apply : 对任意 ⦃a⦄, a in u -> P.关系 a (f a)
    - apply_eq_apply : 对任意 ⦃a b⦄, P.关系 a b -> f a = f b
-/
structure IsRepFun {u : Set α} (P : Partition u) (f : α -> α) : Prop where
  /-- The function is the identity outside the support. -/
  apply_of_notMem : forall ⦃a⦄, a ∉ u -> f a = a
  /-- The function maps each element in the support to a related element. -/
  rel_apply : forall ⦃a⦄, a in u -> P.Rel a (f a)
  /-- The function maps related elements to the same representative. -/
  apply_eq_apply : forall ⦃a b⦄, P.Rel a b -> f a = f b

namespace IsRepFun

variable {u : Set α} {P : Partition u} {f g : α -> α} {a b c : α}

/--
lemma `apply_mem` / 引理 `apply_mem`

English:
lemma apply_mem
  given: (hf : IsRepFun P f) (ha : a in u)
  statement: f a in u
  proof: (hf.rel_apply ha).right_mem

中文:
引理 apply_mem
  条件: (hf : 是RepFun P f) (ha : a in u)
  结论: f a in u
  证明: (hf.rel_apply ha).right_mem

Depends on / 依赖: hf.rel_apply, rel_apply, right_mem
-/
lemma apply_mem (hf : IsRepFun P f) (ha : a in u) : f a in u := (hf.rel_apply ha).right_mem

/--
lemma `image_subset` / 引理 `image_subset`

English:
lemma image_subset
  given: (hf : IsRepFun P f) (hs : u subseteq s)
  statement: f '' s subseteq s
  proof: by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a in u
· exact hs hf.apply_mem ha
  exact (hf.apply_of_notMem ha).symm ▸ haS

中文:
引理 image_subset
  条件: (hf : 是RepFun P f) (hs : u subseteq s)
  结论: f '' s subseteq s
  证明: by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a in u
· exact hs hf.apply_mem ha
  exact (hf.apply_of_notMem ha).symm ▸ haS

Depends on / 依赖: apply_mem, apply_of_notMem, hf.apply_mem, hf.apply_of_notMem
-/
lemma image_subset (hf : IsRepFun P f) (hs : u subseteq s) : f '' s subseteq s := by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a in u
· exact hs hf.apply_mem ha
  exact (hf.apply_of_notMem ha).symm ▸ haS

/--
lemma `mapsTo` / 引理 `mapsTo`

English:
lemma mapsTo
  given: (hf : IsRepFun P f) (hs : u subseteq s)
  statement: Set.MapsTo f s s
  proof: fun x h => hf.image_subset hs ⟨x, h, rfl⟩

中文:
引理 mapsTo
  条件: (hf : 是RepFun P f) (hs : u subseteq s)
  结论: 集合.映射到 f s s
  证明: fun x h => hf.image_subset hs ⟨x, h, rfl⟩

Depends on / 依赖: hf.image_subset, image_subset
-/
lemma mapsTo (hf : IsRepFun P f) (hs : u subseteq s) : Set.MapsTo f s s :=
  fun x h => hf.image_subset hs ⟨x, h, rfl⟩

/--
lemma `mapsTo_of_disjoint` / 引理 `mapsTo_of_disjoint`

English:
lemma mapsTo_of_disjoint
  given: (hf : IsRepFun P f) (hs : Disjoint u s)
  statement: Set.MapsTo f s s
  proof: fun _ h => (hf.apply_of_notMem <| hs.notMem_of_mem_right h).symm ▸ h

中文:
引理 mapsTo_of_disjoint
  条件: (hf : 是RepFun P f) (hs : Disjoint u s)
  结论: 集合.映射到 f s s
  证明: fun _ h => (hf.apply_of_notMem <| hs.notMem_of_mem_right h).symm ▸ h

Depends on / 依赖: apply_of_notMem, hf.apply_of_notMem, hs.notMem_of_mem_right, notMem_of_mem_right
-/
lemma mapsTo_of_disjoint (hf : IsRepFun P f) (hs : Disjoint u s) : Set.MapsTo f s s :=
  fun _ h => (hf.apply_of_notMem <| hs.notMem_of_mem_right h).symm ▸ h

/--
lemma `apply_mem_iff` / 引理 `apply_mem_iff`

English:
lemma apply_mem_iff
  given: (hf : IsRepFun P f) (hs : u subseteq s)
  statement: f a in s ↔ a in s
  proof: .mem_iff mapsTo_of_disjoint hf hs.disjoint_compl_right hf.mapsTo hs

中文:
引理 apply_mem_iff
  条件: (hf : 是RepFun P f) (hs : u subseteq s)
  结论: f a in s ↔ a in s
  证明: .mem_iff mapsTo_of_disjoint hf hs.disjoint_compl_right hf.mapsTo hs

Depends on / 依赖: disjoint_compl_right, hf.mapsTo, hs.disjoint_compl_right, mapsTo, mapsTo_of_disjoint, mem_iff
-/
lemma apply_mem_iff (hf : IsRepFun P f) (hs : u subseteq s) : f a in s ↔ a in s :=
.mem_iff mapsTo_of_disjoint hf hs.disjoint_compl_right hf.mapsTo hs

/--
lemma `apply_eq_apply_iff_rel` / 引理 `apply_eq_apply_iff_rel`

English:
lemma apply_eq_apply_iff_rel
  given: (hf : IsRepFun P f) (ha : a in u)
  statement: f a = f b ↔ P.Rel a b
  proof: by
  refine ⟨fun hab => (hf.rel_apply ha).trans ?_, (hf.apply_eq_apply ·)⟩
  rw [hab]; rw [P.rel_comm]
refine hf.rel_apply by_contra fun hb => ?_
  rw [hf.apply_of_notMem hb] at hab
exact hab ▸ hb hf.apply_mem ha

中文:
引理 apply_eq_apply_iff_rel
  条件: (hf : 是RepFun P f) (ha : a in u)
  结论: f a = f b ↔ P.关系 a b
  证明: by
  refine ⟨fun hab => (hf.rel_apply ha).trans ?_, (hf.apply_eq_apply ·)⟩
  rw [hab]; rw [P.rel_comm]
refine hf.rel_apply by_contra fun hb => ?_
  rw [hf.apply_of_notMem hb] at hab
exact hab ▸ hb hf.apply_mem ha

Depends on / 依赖: P.rel_comm, apply_eq_apply, apply_mem, apply_of_notMem, hf.apply_eq_apply, hf.apply_mem, hf.apply_of_notMem, hf.rel_apply, rel_apply, rel_comm
-/
lemma apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a in u) : f a = f b ↔ P.Rel a b := by
  refine ⟨fun hab => (hf.rel_apply ha).trans ?_, (hf.apply_eq_apply ·)⟩
  rw [hab]; rw [P.rel_comm]
refine hf.rel_apply by_contra fun hb => ?_
  rw [hf.apply_of_notMem hb] at hab
exact hab ▸ hb hf.apply_mem ha

/--
lemma `apply_eq_apply_iff` / 引理 `apply_eq_apply_iff`

English:
lemma apply_eq_apply_iff
  given: (hf : IsRepFun P f)
  statement: f a = f b ↔ a = b ∨ P.Rel a b
  proof: by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne => ?_, fun h => ?_⟩
  · obtain (ha | ha) := em (a in u)
.mp hab · exact hf.apply_eq_apply_iff_rel ha
    obtain (hb | hb) := em (b in u)
    · exact (hf.apply_eq_apply_iff_rel hb |>.mp hab.symm).symm
    rw [hf.apply_of_notMem ha]; 

中文:
引理 apply_eq_apply_iff
  条件: (hf : 是RepFun P f)
  结论: f a = f b ↔ a = b ∨ P.关系 a b
  证明: by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne => ?_, fun h => ?_⟩
  · obtain (ha | ha) := em (a in u)
.mp hab · exact hf.apply_eq_apply_iff_rel ha
    obtain (hb | hb) := em (b in u)
    · exact (hf.apply_eq_apply_iff_rel hb |>.mp hab.symm).symm
    rw [hf.apply_of_notMem ha]; 

Depends on / 依赖: apply_eq_apply, apply_eq_apply_iff_rel, apply_of_notMem, eq_or_ne, hab.symm, hf.apply_eq_apply, hf.apply_eq_apply_iff_rel, hf.apply_of_notMem, ne_eq, or_iff_not_imp_left
-/
lemma apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P.Rel a b := by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne => ?_, fun h => ?_⟩
  · obtain (ha | ha) := em (a in u)
.mp hab · exact hf.apply_eq_apply_iff_rel ha
    obtain (hb | hb) := em (b in u)
    · exact (hf.apply_eq_apply_iff_rel hb |>.mp hab.symm).symm
    rw [hf.apply_of_notMem ha]; rw [hf.apply_of_notMem hb] at hab
    contradiction
  obtain rfl | hne := eq_or_ne a b
  · rfl
  exact hf.apply_eq_apply (h hne)

/--
lemma `forall_apply_eq_apply_iff` / 引理 `forall_apply_eq_apply_iff`

English:
lemma forall_apply_eq_apply_iff
  given: (hf : IsRepFun P f) (a)
  proof: by
  refine (em (a in u)).elim (fun ha => Or.inr fun b => ?_) (fun ha => Or.inl fun b => ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
· exact hf.apply_of_notMem .not.mp ha hf.apply_mem_iff le_rfl
.symm exact hf.apply_of_notMem ha

中文:
引理 对任意_apply_eq_apply_iff
  条件: (hf : 是RepFun P f) (a)
  证明: by
  refine (em (a in u)).elim (fun ha => Or.inr fun b => ?_) (fun ha => Or.inl fun b => ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
· exact hf.apply_of_notMem .not.mp ha hf.apply_mem_iff le_rfl
.symm exact hf.apply_of_notMem ha

Depends on / 依赖: KaehlerDifferential, KaehlerDifferential.mvPolynomialBasis, Or.inl, Or.inr, apply_eq_apply_iff_rel, apply_mem_iff, apply_of_notMem, hf.apply_eq_apply_iff_rel, hf.apply_mem_iff, hf.apply_of_notMem, le_rfl, mvPolynomialBasis, not.mp, of_basis
-/
lemma forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) :
    (forall (x : α), f a = f x ↔ a = x) ∨ (forall (x : α), f a = f x ↔ P.Rel a x) := by
  refine (em (a in u)).elim (fun ha => Or.inr fun b => ?_) (fun ha => Or.inl fun b => ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
· exact hf.apply_of_notMem .not.mp ha hf.apply_mem_iff le_rfl
.symm exact hf.apply_of_notMem ha

/--
lemma `apply_eq_apply_iff'` / 引理 `apply_eq_apply_iff'`

English:
lemma apply_eq_apply_iff'
  given: (hf : IsRepFun P f)
  proof: by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind

中文:
引理 apply_eq_apply_iff'
  条件: (hf : 是RepFun P f)
  证明: by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind

Depends on / 依赖: apply_eq_apply, forall_apply_eq_apply_iff, hf.apply_eq_apply, hf.forall_apply_eq_apply_iff
-/
lemma apply_eq_apply_iff' (hf : IsRepFun P f) :
    f a = f b ↔ (a = b ∧ forall c, f a = f c ↔ a = c) ∨ P.Rel a b := by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind

/--
lemma `idem` / 引理 `idem`

English:
lemma idem
  given: (hf : IsRepFun P f)
  statement: f (f a) = f a
  proof: by
  obtain (ha | ha) := em (a in u)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]

中文:
引理 idem
  条件: (hf : 是RepFun P f)
  结论: f (f a) = f a
  证明: by
  obtain (ha | ha) := em (a in u)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]

Depends on / 依赖: apply_eq_apply_iff_rel, apply_of_notMem, eq_comm, hf.apply_eq_apply_iff_rel, hf.apply_of_notMem, hf.rel_apply, rel_apply, simp_rw
-/
lemma idem (hf : IsRepFun P f) : f (f a) = f a := by
  obtain (ha | ha) := em (a in u)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]

/--
theorem `apply_apply` / 定理 `apply_apply`

English:
theorem apply_apply
  given: (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α)
  statement: f (g x) = f x
  proof: by
  obtain (hx | hx) := em (x in u)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx]; rw [hf.apply_of_notMem hx]

中文:
定理 apply_apply
  条件: (hf : 是RepFun P f) (hg : 是RepFun P g) (x : α)
  结论: f (g x) = f x
  证明: by
  obtain (hx | hx) := em (x in u)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx]; rw [hf.apply_of_notMem hx]

Depends on / 依赖: apply_eq_apply, apply_of_notMem, hf.apply_eq_apply, hf.apply_of_notMem, hg.apply_of_notMem, hg.rel_apply, rel_apply
-/
theorem apply_apply (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f x := by
  obtain (hx | hx) := em (x in u)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx]; rw [hf.apply_of_notMem hx]

/--
lemma `exists_extend_partial` / 引理 `exists_extend_partial`

English:
lemma exists_extend_partial
  statement: (P : Partition u) (f₀ : t -> α)
  proof: by
  classical
  set f : α -> α := fun a => if ha : a in u then
    (if hb : exists b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha => by simp [hfdef, ha], fun a ha => ?_, fun a b hab => ?_⟩, fun a => ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte

中文:
引理 存在_extend_partial
  结论: (P : 分拆 u) (f₀ : t -> α)
  证明: by
  classical
  set f : α -> α := fun a => if ha : a in u then
    (if hb : exists b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha => by simp [hfdef, ha], fun a ha => ?_, fun a b hab => ?_⟩, fun a => ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte

Depends on / 依赖: P.Rel, P.mem_partOf, P.partOf_mem, P.rep, P.rep_rel, choose_spec, classical, dif_pos, h.choose, h.choose_spec.right_mem, h.choose_spec.trans, h_mem, hab.left_mem, hab.right_me, hb.choose, left_mem, mem_partOf, partOf_mem, reduceDIte, rep_rel
-/
lemma exists_extend_partial (P : Partition u) (f₀ : t -> α)
    (h_notMem : forall x : t, x.1 ∉ u -> f₀ x = x) (h_mem : forall x : t, x.1 in u -> P.Rel x (f₀ x))
    (h_eq : forall x y : t, P.Rel x y -> f₀ x = f₀ y) : exists f, IsRepFun P f ∧ forall x : t, f x = f₀ x := by
  classical
  set f : α -> α := fun a => if ha : a in u then
    (if hb : exists b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha => by simp [hfdef, ha], fun a ha => ?_, fun a b hab => ?_⟩, fun a => ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte]
    split_ifs with h
· exact h.choose_spec.trans h_mem h.choose h.choose_spec.right_mem
    push Not at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hfdef, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂
· exact h_eq _ _ (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
.elim · exact h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩
.elim · exact h₁ ⟨_, hab.trans h₂.choose_spec⟩
    congr 1
    rwa [← rel_iff_partOf_eq_partOf_of_mem _ hab.left_mem hab.right_mem]
.symm obtain (ha | ha) := em (a.1 in u)
  · simp [hfdef, ha, h_notMem _ ha]
  simp only [hfdef, ha, ↓reduceDIte]
  split_ifs with h
.symm · exact h_eq _ _ h.choose_spec
.elim exact h ⟨a, rel_rfl_iff.mpr ha⟩

/--
lemma `exists_extend_partial'` / 引理 `exists_extend_partial'`

English:
lemma exists_extend_partial'
  statement: (P : Partition u)
  proof: by
  simpa using! exists_extend_partial P (fun x : t => x) (by simp) (by simp) (fun x y => h x.2 y.2)

中文:
引理 存在_extend_partial'
  结论: (P : 分拆 u)
  证明: by
  simpa using! exists_extend_partial P (fun x : t => x) (by simp) (by simp) (fun x y => h x.2 y.2)

Depends on / 依赖: exists_extend_partial
-/
lemma exists_extend_partial' (P : Partition u)
    (h : forall ⦃x y⦄, x in t -> y in t -> P.Rel x y -> x = y) : exists f, IsRepFun P f ∧ EqOn f id t := by
  simpa using! exists_extend_partial P (fun x : t => x) (by simp) (by simp) (fun x y => h x.2 y.2)

/--
lemma `nonempty` / 引理 `nonempty`

English:
lemma nonempty
  given: (P : Partition u)
  statement: exists f, IsRepFun P f
  proof: by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

中文:
引理 nonempty
  条件: (P : 分拆 u)
  结论: 存在 f, 是RepFun P f
  证明: by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

Depends on / 依赖: exists_extend_partial
-/
lemma nonempty (P : Partition u) : exists f, IsRepFun P f := by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

end IsRepFun
end Partition.IsRepFun
