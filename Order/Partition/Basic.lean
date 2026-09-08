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

/-- A `Partition` of an element `s` of a `CompleteLattice` is a collection of
independent nontrivial elements whose supremum is `s`. -/
/-
**Partition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [CompleteLattice α] → α → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Partition` of an element `s` of a `CompleteLattice` is a collection of
independent nontrivial elements whose supremum is `s`.
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

/-
**Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : α} : SetLike (Partition s) α where
  coe := Partition.parts
  coe_injective p p' h := by cases p; cases p'; simpa using h

/-- See Note [custom simps projection]. -/
/-
**Partition.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `Partition.Simps`。
形式化陈述：{α : Type u_1} → [inst : CompleteLattice α] → {s : α} → Partition s → Set 
α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe {s : α} (P : Partition s) : Set α := P

initialize_simps_projections Partition (parts → coe, as_prefix coe)
/-
**Partition.coe_parts** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {s : α} [inst : CompleteLattice α] {P : Partition s}, P.p
arts = ↑P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_parts : P.parts = P := rfl
/-
**Partition.ext** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {s : α} [inst : CompleteLattice α] {P Q : Partition s}, (
∀ (x : α), x ∈ P ↔ x ∈ Q) → P = Q
参数：∀ (x : α), x ∈ P ↔ x ∈ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
@[ext] lemma ext (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q :=
  SetLike.ext hP

@[simp]
/-
**Partition.sSupIndep** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：sSupIndep (P : Partition s) : sSupIndep (P : Set α)
参数：P : Partition s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.sSupIndep'`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : α
} (self : Partition s), sSupIndep self.parts
-/
lemma sSupIndep (P : Partition s) : sSupIndep (P : Set α) :=
  P.sSupIndep'
/-
**Partition.disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：disjoint (hx : x in P) (hy : y in P) (hxy : x != y) : Disjoint x y
参数：hx : x in P；hy : y in P；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep.pairwiseDisjoint`：sSupIndep.pairwiseDisjoint : s.PairwiseDisjo
int id
· 使用引理 `Partition.sSupIndep`：sSupIndep (P : Partition s) : sSupIndep (P : Set α)
-/
lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) : Disjoint x y :=
  P.sSupIndep.pairwiseDisjoint hx hy hxy
/-
**Partition.pairwiseDisjoint** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep.pairwiseDisjoint`：sSupIndep.pairwiseDisjoint : s.PairwiseDisjo
int id
· 使用定理 `Partition.sSupIndep'`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : α
} (self : Partition s), sSupIndep self.parts
-/
lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  P.sSupIndep'.pairwiseDisjoint
/-
**Partition.eq_or_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：eq_or_disjoint (hx : x in P) (hy : y in P) : x = y ∨ Disjoint x y
参数：hx : x in P；hy : y in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `Partition.disjoint`：disjoint (hx : x in P) (hy : y in P) (hxy : x != y) 
: Disjoint x y
-/
lemma eq_or_disjoint (hx : x ∈ P) (hy : y ∈ P) : x = y ∨ Disjoint x y :=
  or_iff_not_imp_left.mpr (P.disjoint hx hy)
/-
**Partition.eq_of_not_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：eq_of_not_disjoint (hx : x in P) (hy : y in P) (hxy : ¬ Disjoint x y) : x 
= y
参数：hx : x in P；hy : y in P；hxy : ¬ Disjoint x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `Partition.eq_or_disjoint`：eq_or_disjoint (hx : x in P) (hy : y in P) : x
 = y ∨ Disjoint x y
-/
lemma eq_of_not_disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : ¬ Disjoint x y) : x = y :=
  (P.eq_or_disjoint hx hy).resolve_right hxy

@[simp]
/-
**Partition.sSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：sSup_eq (P : Partition s) : sSup P = s
参数：P : Partition s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.sSup_eq'`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : α} 
(self : Partition s), sSup self.parts = s
-/
lemma sSup_eq (P : Partition s) : sSup P = s :=
  P.sSup_eq'

@[simp]
/-
**Partition.iSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：iSup_eq (P : Partition s) : ⨆ x in P, x = s
参数：P : Partition s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.sSup_eq`：sSup_eq (P : Partition s) : sSup P = s
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
-/
lemma iSup_eq (P : Partition s) : ⨆ x ∈ P, x = s := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl
/-
**Partition.le_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：le_of_mem (P : Partition s) (hx : x in P) : x <= s
参数：P : Partition s；hx : x in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用引理 `Partition.sSup_eq`：sSup_eq (P : Partition s) : sSup P = s
-/
lemma le_of_mem (P : Partition s) (hx : x ∈ P) : x ≤ s :=
  (le_sSup hx).trans_eq P.sSup_eq
/-
**Partition.parts_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：parts_nonempty (P : Partition s) (hs : s != ⊥) : (P : Set α).Nonempty
参数：P : Partition s；hs : s != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.sSup_eq`：sSup_eq (P : Partition s) : sSup P = s
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma parts_nonempty (P : Partition s) (hs : s ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]
/-
**Partition.bot_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：bot_notMem (P : Partition s) : ⊥ ∉ P
参数：P : Partition s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.bot_notMem'`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : 
α} (self : Partition s), ⊥ ∉ self.parts
-/
lemma bot_notMem (P : Partition s) : ⊥ ∉ P :=
  P.bot_notMem'
/-
**Partition.ne_bot_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：ne_bot_of_mem (hx : x in P) : x != ⊥
参数：hx : x in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.bot_notMem`：bot_notMem (P : Partition s) : ⊥ ∉ P
-/
lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_notMem <| h ▸ hx
/-
**Partition.bot_lt_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：bot_lt_of_mem (hx : x in P) : ⊥ < x
参数：hx : x in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用引理 `Partition.ne_bot_of_mem`：ne_bot_of_mem (hx : x in P) : x != ⊥
-/
lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

/-- Convert a `Partition s` into a `Partition t` via an equality `s = t`. -/
@[simps]
/-
**Partition.copy** 是 Mathlib 中的一个定义，位于命名空间 `Partition`。
形式化陈述：{α : Type u_1} → {s t : α} → [inst : CompleteLattice α] → Partition s → s 
= t → Partition t
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.sSupIndep`：sSupIndep (P : Partition s) : sSupIndep (P : Set α)
· 使用引理 `Partition.bot_notMem`：bot_notMem (P : Partition s) : ⊥ ∉ P

--- 原说明 ---
Convert a `Partition s` into a `Partition t` via an equality `s = t`.
-/
protected def copy (P : Partition s) (hst : s = t) : Partition t where
  parts := P
  sSupIndep' := P.sSupIndep
  bot_notMem' := P.bot_notMem
  sSup_eq' := hst ▸ P.sSup_eq

@[simp]
/-
**Partition.mem_copy_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_copy_iff (hst : s = t) : x in P.copy hst ↔ x in P
参数：hst : s = t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_copy_iff (hst : s = t) : x ∈ P.copy hst ↔ x ∈ P := Iff.rfl

/-- The natural equivalence between the subtype of parts and the subtype of parts of a copy. -/
@[simps!]
/-
**Partition.partscopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Partition`。
形式化陈述：partscopyEquiv (P : Partition s) (hst : s = t) : ↥(P.copy hst) ≃ ↥P
参数：P : Partition s；hst : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between the subtype of parts and the subtype of parts of
 a copy.
-/
def partscopyEquiv (P : Partition s) (hst : s = t) : ↥(P.copy hst) ≃ ↥P :=
  Equiv.setCongr rfl

/-- A constructor for `Partition s` that removes `⊥` from the set of parts. -/
@[simps]
/-
**Partition.removeBot** 是 Mathlib 中的一个定义，位于命名空间 `Partition`。
形式化陈述：removeBot (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s) : 
Partition s where parts
参数：P : Set α；indep : _root_.sSupIndep P；hsSup : sSup P = s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for `Partition s` that removes `⊥` from the set of parts.
-/
def removeBot (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s) : Partition s where
  parts := P \ {⊥}
  sSupIndep' := indep.mono sdiff_subset
  bot_notMem' := by simp
  sSup_eq' := by simp [← hsSup]

@[simp]
/-
**Partition.mem_removeBot** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_removeBot (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s
) : x in removeBot P indep hsSup ↔ x in P ∧ x != ⊥
参数：P : Set α；indep : _root_.sSupIndep P；hsSup : sSup P = s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_removeBot (P : Set α) (indep : _root_.sSupIndep P) (hsSup : sSup P = s) :
    x ∈ removeBot P indep hsSup ↔ x ∈ P ∧ x ≠ ⊥ := Iff.rfl

@[simp]
/-
**Partition.notMem_of_bot** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：notMem_of_bot (P : Partition (⊥ : α)) (x : α) : x ∉ P
参数：P : Partition (⊥ : α)；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.bot_notMem`：bot_notMem (P : Partition s) : ⊥ ∉ P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用引理 `Partition.le_of_mem`：le_of_mem (P : Partition s) (hx : x in P) : x <= s
-/
lemma notMem_of_bot (P : Partition (⊥ : α)) (x : α) : x ∉ P := by
  rintro hxP
  obtain rfl := le_bot_iff.mp <| P.le_of_mem hxP
  exact P.bot_notMem hxP

/-- There is a unique partition of `⊥`. -/
/-
**Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique partition of `⊥`.
-/
instance : Unique (Partition (⊥ : α)) where
  default := removeBot (∅ : Set α) sSupIndep_empty sSup_empty
  uniq P := by ext; simp
/-
**Partition.ne_bot_of_mem'** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：ne_bot_of_mem' (hxP : x in P) : s != ⊥
参数：hxP : x in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.notMem_of_bot`：notMem_of_bot (P : Partition (⊥ : α)) (x : α) :
 x ∉ P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_bot_of_mem' (hxP : x ∈ P) : s ≠ ⊥ := by
  rintro rfl
  exact P.notMem_of_bot _ hxP

end Basic

section Order

variable [CompleteLattice α] {P Q : Partition s}

/-- Partitions on `s` are ordered by refinement: `P ≤ Q` if every part of `P` is contained in a part
of `Q`. -/
/-
**Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partitions on `s` are ordered by refinement: `P ≤ Q` if every part of `P` is con
tained in a part
of `Q`.
-/
instance : PartialOrder (Partition s) where
  le P Q := ∀ ⦃x⦄, x ∈ P → ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := ⟨x, hx, le_rfl⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ hxP
    obtain ⟨z, hz, hyz⟩ := hQR hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp h
      obtain ⟨x', hx', hyx'⟩ := hq hy
      obtain rfl := P.pairwiseDisjoint.eq_of_le h hx' (P.ne_bot_of_mem h) (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq h
    obtain ⟨x', hx', hyx'⟩ := hp hy
    obtain rfl := Q.pairwiseDisjoint.eq_of_le h hx' (Q.ne_bot_of_mem h) (hxy.trans hyx')
    rwa [hxy.antisymm hyx']
/-
**Partition.le_def** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：le_def : P <= Q ↔ forall x in P, exists y in Q, x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def : P ≤ Q ↔ ∀ x ∈ P, ∃ y ∈ Q, x ≤ y := .rfl
/-
**Partition.exists_le_of_mem_le** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：exists_le_of_mem_le (h : P <= Q) (hx : x in P) : exists y in Q, x <= y
参数：h : P <= Q；hx : x in P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_le_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃ y ∈ Q, x ≤ y := h hx
/-
**Partition.existsUnique_of_mem_le** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：existsUnique_of_mem_le (h : P <= Q) (hx : x in P) : exists! y in Q, x <= y
参数：h : P <= Q；hx : x in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.eq_of_not_disjoint`：eq_of_not_disjoint (hx : x in P) (hy : y i
n P) (hxy : ¬ Disjoint x y) : x = y
· 使用引理 `Partition.ne_bot_of_mem`：ne_bot_of_mem (hx : x in P) : x != ⊥
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
lemma existsUnique_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃! y ∈ Q, x ≤ y := by
  obtain ⟨y, hy, hxy⟩ := h hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ ↦ Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose this
  exact le_bot_iff.mp (this hxz hxy)

/-- The top partition of `s` is the partition with the single part `s`, or no parts if `s` is the
bottom element. -/
/-
**Partition.instOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
形式化陈述：instOrderTop : OrderTop (Partition s) where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep_singleton`：sSupIndep_singleton (a : α) : sSupIndep ({a} : Set 
α)

--- 原说明 ---
The top partition of `s` is the partition with the single part `s`, or no parts 
if `s` is the
bottom element.
-/
instance instOrderTop : OrderTop (Partition s) where
  top := removeBot {s} (sSupIndep_singleton s) sSup_singleton
  le_top P x hxP := by simp [P.ne_bot_of_mem' hxP, P.le_of_mem hxP]
/-
**Partition.top_def** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：top_def : (⊤ : Partition s) = removeBot {s} (sSupIndep_singleton s) sSup_s
ingleton
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_def : (⊤ : Partition s) = removeBot {s} (sSupIndep_singleton s) sSup_singleton := rfl
/-
**Partition.parts_top** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {s : α} [inst : CompleteLattice α], s ≠ ⊥ → ↑⊤ = {s}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Partition.coe_removeBot`：∀ {α : Type u_1} {s : α} [inst : CompleteLattic
e α] (P : Set α) (indep : sSupIndep P) (hsSup : sSup P = s),   ↑(Partition.remov
eBot P indep …
· 使用定理 `sSupIndep_singleton`：sSupIndep_singleton (a : α) : sSupIndep ({a} : Set 
α)
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
-/
@[simp] lemma parts_top (hs : s ≠ ⊥) : ((⊤ : Partition s) : Set α) = {s} := by
  simpa [top_def]
/-
**Partition.mem_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {s : α} [inst : CompleteLattice α] {a : α}, a ∈ ⊤ ↔ a = s
 ∧ a ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep_singleton`：sSupIndep_singleton (a : α) : sSupIndep ({a} : Set 
α)
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Partition.top_def`：top_def : (⊤ : Partition s) = removeBot {s} (sSupInde
p_singleton s) sSup_singleton
· 使用引理 `Partition.mem_removeBot`：mem_removeBot (P : Set α) (indep : _root_.sSupI
ndep P) (hsSup : sSup P = s) : x in removeBot P indep hsSup ↔ x in P ∧ x != ⊥
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_top_iff {a : α} : a ∈ (⊤ : Partition s) ↔ a = s ∧ a ≠ ⊥ := by
  rw [top_def, mem_removeBot, mem_singleton_iff]
/-
**Partition.parts_top_subset** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：parts_top_subset : ((⊤ : Partition s) : Set α) subseteq {s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma parts_top_subset : ((⊤ : Partition s) : Set α) ⊆ {s} := by simp

/-- When `α` is a frame, the meet `P ⊓ Q` of two partitions is the partition consisting of all
non-bottom meets `p ⊓ q` for `p ∈ P` and `q ∈ Q`.

Note that while finite meets of partitions can be constructed in this way, arbitrary meets generally
do not exist: for example when `α` is the frame of open subsets of the Cantor space, `Partition α`
has no bottom element. -/
/-
**Partition.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
形式化陈述：instSemilatticeInf {α : Type*} [Order.Frame α] (s : α) : SemilatticeInf (P
artition s) where inf P Q
参数：s : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is a frame, the meet `P ⊓ Q` of two partitions is the partition consist
ing of all
non-bottom meets `p ⊓ q` for `p ∈ P` and `q ∈ Q`.

Note that while finite meets of partitions can be constructed in this way, arbit
rary meets generally
do not exist: for example when `α` is the frame of open subsets of the Cantor sp
ace, `Partition α`
has no bottom element.
-/
instance instSemilatticeInf {α : Type*} [Order.Frame α] (s : α) : SemilatticeInf (Partition s) where
  inf P Q := removeBot {a | ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q} (by
      rw [sSupIndep_iff_pairwiseDisjoint]
      intro a ha a' ha' h
      grind [Partition.eq_or_disjoint, Disjoint.inf_left, Disjoint.inf_left'])
    (by
      suffices sSup {a | ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q} = sSup P ⊓ sSup Q by simpa
      rw [sSup_inf_sSup]
      refine le_antisymm ?_ ?_
      · exact sSup_le fun a ⟨p, hp, q, hq, ha⟩ ↦ le_iSup₂_of_le (p, q) ⟨hp, hq⟩ <| by grind
      · exact iSup₂_le fun (p, q) ⟨hp, hq⟩ ↦ le_sSup_of_le ⟨p, hp, q, hq, rfl⟩ (by simp))
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
/-
**Partition.mem_inf_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_inf_iff {α : Type*} [Order.Frame α] {s a : α} {P Q : Partition s} : a 
in P ⊓ Q ↔ a != ⊥ ∧ exists p in P, exists q in Q, a = p ⊓ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
lemma mem_inf_iff {α : Type*} [Order.Frame α] {s a : α} {P Q : Partition s} :
    a ∈ P ⊓ Q ↔ a ≠ ⊥ ∧ ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q :=
  and_comm

end Order

variable {S : Set (Set α)} {u s t : Set α} {a b c : α} {P Q : Partition u}

section Set

/-
**Partition.sUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {s : Set α} (P : Partition s), ⋃₀ ↑P = s
参数：P : Partition s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.sSup_eq`：sSup_eq (P : Partition s) : sSup P = s
-/
@[simp] protected lemma sUnion_eq (P : Partition s) : ⋃₀ P = s := P.sSup_eq
/-
**Partition.nonempty_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：nonempty_of_mem (ht : t in P) : t.Nonempty
参数：ht : t in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.notMem_singleton_empty`：notMem_singleton_empty {s : Set α} : s ∉ ({∅
} : Set (Set α)) ↔ s.Nonempty
· 使用引理 `Partition.ne_bot_of_mem`：ne_bot_of_mem (hx : x in P) : x != ⊥
-/
lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty := notMem_singleton_empty.1 <| P.ne_bot_of_mem ht
/-
**Partition.empty_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：empty_notMem : ∅ ∉ P
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.bot_notMem`：bot_notMem (P : Partition s) : ⊥ ∉ P
-/
lemma empty_notMem : ∅ ∉ P := P.bot_notMem
/-
**Partition.subset_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：subset_of_mem (ht : t in P) : t subseteq u
参数：ht : t in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.le_of_mem`：le_of_mem (P : Partition s) (hx : x in P) : x <= s
-/
lemma subset_of_mem (ht : t ∈ P) : t ⊆ u := P.le_of_mem ht
/-
**Partition.mem_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_iff_exists : x in u ↔ exists t in P, x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Partition.sUnion_eq`：∀ {α : Type u_1} {s : Set α} (P : Partition s), ⋃₀ 
↑P = s
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
-/
lemma mem_iff_exists : x ∈ u ↔ ∃ t ∈ P, x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨t, htP, hxt⟩ ↦ subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx
/-
**Partition.eq_of_mem_inter** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：eq_of_mem_inter (ht : t in P) (hs : s in P) (hx : x in t inter s) : t = s
参数：ht : t in P；hs : s in P；hx : x in t inter s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用引理 `Partition.pairwiseDisjoint`：pairwiseDisjoint : Set.PairwiseDisjoint (P :
 Set α) id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
-/
lemma eq_of_mem_inter (ht : t ∈ P) (hs : s ∈ P) (hx : x ∈ t ∩ s) : t = s :=
  P.pairwiseDisjoint.elim ht hs fun (hdj : Disjoint t s) ↦ by simp [hdj.inter_eq] at hx
/-
**Partition.eq_of_mem_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：eq_of_mem_of_mem (ht : t in P) (hus : s in P) (hxt : x in t) (hxs : x in s
) : t = s
参数：ht : t in P；hus : s in P；hxt : x in t；hxs : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.eq_of_mem_inter`：eq_of_mem_inter (ht : t in P) (hs : s in P) (
hx : x in t inter s) : t = s
-/
lemma eq_of_mem_of_mem (ht : t ∈ P) (hus : s ∈ P) (hxt : x ∈ t) (hxs : x ∈ s) : t = s :=
  eq_of_mem_inter ht hus ⟨hxt, hxs⟩
/-
**Partition.mem_iff_unique** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_iff_unique : x in u ↔ exists! t, t in P ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Partition.sUnion_eq`：∀ {α : Type u_1} {s : Set α} (P : Partition s), ⋃₀ 
↑P = s
· 使用引理 `Partition.eq_of_mem_of_mem`：eq_of_mem_of_mem (ht : t in P) (hus : s in P
) (hxt : x in t) (hxs : x in s) : t = s
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
-/
lemma mem_iff_unique : x ∈ u ↔ ∃! t, t ∈ P ∧ x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, ⟨htP, hxt⟩, _⟩ ↦ subset_of_mem htP hxt⟩
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ⟨ht, hxt⟩, fun s ⟨hsP, hxs⟩ ↦ P.eq_of_mem_of_mem hsP ht hxs hxt⟩
/-
**Partition.subset_sUnion_and_mem_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：subset_sUnion_and_mem_iff_mem (hSP : S subseteq P) : t subseteq ⋃₀ S ∧ t i
n P ↔ t in S
参数：hSP : S subseteq P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.nonempty_of_mem`：nonempty_of_mem (ht : t in P) : t.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.eq_of_mem_of_mem`：eq_of_mem_of_mem (ht : t in P) (hus : s in P
) (hxt : x in t) (hxs : x in s) : t = s
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
lemma subset_sUnion_and_mem_iff_mem (hSP : S ⊆ P) : t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  exact eq_of_mem_of_mem htP (hSP hsS) hxt hxs ▸ hsS
/-
**Partition.subset_sUnion_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：subset_sUnion_iff_mem (ht : t in P) (hSP : S subseteq P.parts) : t subsete
q ⋃₀ S ↔ t in S
参数：ht : t in P；hSP : S subseteq P.parts。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.subset_sUnion_and_mem_iff_mem`：subset_sUnion_and_mem_iff_mem (
hSP : S subseteq P) : t subseteq ⋃₀ S ∧ t in P ↔ t in S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subset_sUnion_iff_mem (ht : t ∈ P) (hSP : S ⊆ P.parts) : t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

/-- Noncomputably choose a representative from an equivalence class. -/
/-
**Partition.rep** 是 Mathlib 中的一个定义，位于命名空间 `Partition`。
形式化陈述：rep (P : Partition u) (ht : t in P) : α
参数：P : Partition u；ht : t in P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.nonempty_of_mem`：nonempty_of_mem (ht : t in P) : t.Nonempty

--- 原说明 ---
Noncomputably choose a representative from an equivalence class.
-/
noncomputable def rep (P : Partition u) (ht : t ∈ P) : α := (P.nonempty_of_mem ht).some

/-- The representative of a part belongs to that part. -/
/-
**Partition.rep_mem** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {u t : Set α} {P : Partition u} (ht : t ∈ P), P.rep ht ∈ 
t
参数：ht : t ∈ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用引理 `Partition.nonempty_of_mem`：nonempty_of_mem (ht : t in P) : t.Nonempty

--- 原说明 ---
The representative of a part belongs to that part.
-/
@[simp] lemma rep_mem (ht : t ∈ P) : P.rep ht ∈ t := (P.nonempty_of_mem ht).some_mem

/-- The representative of a part belongs to the underlying set. -/
/-
**Partition.rep_mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {u t : Set α} {P : Partition u} (ht : t ∈ P), P.rep ht ∈ 
u
参数：ht : t ∈ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
· 使用定理 `Partition.rep_mem`：∀ {α : Type u_1} {u t : Set α} {P : Partition u} (ht 
: t ∈ P), P.rep ht ∈ t

--- 原说明 ---
The representative of a part belongs to the underlying set.
-/
@[simp] lemma rep_mem_supp (ht : t ∈ P) : P.rep ht ∈ u := P.subset_of_mem ht <| rep_mem ht

end Set

/-! ### Induced relation -/

section Rel

/-- Every partition of `s : Set α` induces a transitive, symmetric binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`. -/
/-
**Partition.Rel** 是 Mathlib 中的一个定义，位于命名空间 `Partition`。
形式化陈述：Rel (P : Partition s) (a b : α) : Prop
参数：P : Partition s；a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every partition of `s : Set α` induces a transitive, symmetric binary relation o
n `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive ou
tside `s`.
-/
def Rel (P : Partition s) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t
/-
**Partition.rel_le_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：rel_le_iff_le : P.Rel <= Q.Rel ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.nonempty_of_mem`：nonempty_of_mem (ht : t in P) : t.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.eq_of_mem_of_mem`：eq_of_mem_of_mem (ht : t in P) (hus : s in P
) (hxt : x in t) (hxs : x in s) : t = s
-/
lemma rel_le_iff_le : P.Rel ≤ Q.Rel ↔ P ≤ Q := by
  refine ⟨fun h S hS ↦ ?_, fun h a b ⟨t, ht, ha, hb⟩ ↦ ?_⟩
  · obtain ⟨x, hxS⟩ := nonempty_of_mem hS
    obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
    refine ⟨T, hT, fun a haS ↦ ?_⟩
    obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
    exact eq_of_mem_of_mem hT hT' hxT hxT' ▸ haT'
  obtain ⟨t', ht', htt'⟩ := h ht
  use t', ht', htt' ha, htt' hb
/-
**Partition.Rel.exists** 是 Mathlib 中的一个定理，位于命名空间 `Partition.Rel`。
形式化陈述：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partition u}, P.Rel x y → ∃ t 
∈ P, x ∈ t ∧ y ∈ t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Rel.exists (h : P.Rel x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t := h
/-
**Partition.Rel.forall** 是 Mathlib 中的一个定理，位于命名空间 `Partition.Rel`。
形式化陈述：∀ {α : Type u_1} {x y : α} {u t : Set α} {P : Partition u}, P.Rel x y → t 
∈ P → (x ∈ t ↔ y ∈ t)
参数：x ∈ t ↔ y ∈ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Partition.eq_of_mem_of_mem`：eq_of_mem_of_mem (ht : t in P) (hus : s in P
) (hxt : x in t) (hxs : x in s) : t = s
-/
lemma Rel.forall (h : P.Rel x y) (ht : t ∈ P) : x ∈ t ↔ y ∈ t := by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

@[simp]
/-
**Partition.rel_rfl_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：rel_rfl_iff : P.Rel x x ↔ x in u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Partition.mem_iff_unique`：mem_iff_unique : x in u ↔ exists! t, t in P ∧ 
x in t
-/
lemma rel_rfl_iff : P.Rel x x ↔ x ∈ u := by
  refine ⟨fun ⟨t, ht, hxP, _⟩ ↦ subset_of_mem ht hxP, fun hx ↦ ?_⟩
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.mem_iff_unique.mp hx
  exact ⟨t, ht, hxt, hxt⟩
/-
**Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Partition u) : Std.Symm P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩
/-
**Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Partition u) : IsTrans α P.Rel where
  trans _ _ _ := fun ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩ ↦
    ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩
/-
**Partition.Rel.symm** 是 Mathlib 中的一个定理，位于命名空间 `Partition.Rel`。
形式化陈述：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partition u}, P.Rel x y → P.Re
l y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
· 使用定理 `Partition.instSymmRel`：∀ {α : Type u_1} {u : Set α} (P : Partition u), S
td.Symm P.Rel
-/
@[symm] lemma Rel.symm (h : P.Rel x y) : P.Rel y x := symm_of P.Rel h
/-
**Partition.rel_comm** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：rel_comm : P.Rel x y ↔ P.Rel y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.Rel.symm`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partitio
n u}, P.Rel x y → P.Rel y x
-/
lemma rel_comm : P.Rel x y ↔ P.Rel y x := ⟨Rel.symm, Rel.symm⟩
/-
**Partition.Rel.trans** 是 Mathlib 中的一个定理，位于命名空间 `Partition.Rel`。
形式化陈述：∀ {α : Type u_1} {x y z : α} {u : Set α} {P : Partition u}, P.Rel x y → P.
Rel y z → P.Rel x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `Partition.instIsTransRel`：∀ {α : Type u_1} {u : Set α} (P : Partition u)
, IsTrans α P.Rel
-/
lemma Rel.trans (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z := trans_of P.Rel hxy hyz
/-
**Partition.Rel.left_mem** 是 Mathlib 中的一个定理，位于命名空间 `Partition.Rel`。
形式化陈述：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partition u}, P.Rel x y → x ∈ 
u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
-/
lemma Rel.left_mem (h : P.Rel x y) : x ∈ u := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt
/-
**Partition.Rel.right_mem** 是 Mathlib 中的一个定理，位于命名空间 `Partition.Rel`。
形式化陈述：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partition u}, P.Rel x y → y ∈ 
u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.Rel.left_mem`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Part
ition u}, P.Rel x y → x ∈ u
· 使用定理 `Partition.Rel.symm`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partitio
n u}, P.Rel x y → P.Rel y x
-/
lemma Rel.right_mem (h : P.Rel x y) : y ∈ u := h.symm.left_mem

/-- Any element of a part is related to the representative of that part. -/
/-
**Partition.rep_rel** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：rep_rel (ht : t in P) (hx : x in t) : P.Rel x (P.rep ht)
参数：ht : t in P；hx : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.rep_mem`：∀ {α : Type u_1} {u t : Set α} {P : Partition u} (ht 
: t ∈ P), P.rep ht ∈ t

--- 原说明 ---
Any element of a part is related to the representative of that part.
-/
lemma rep_rel (ht : t ∈ P) (hx : x ∈ t) : P.Rel x (P.rep ht) := ⟨t, ht, hx, P.rep_mem ht⟩

end Rel

section partOf

/-- The part of a partition containing a given element. If the element is not in the
underlying set, this is empty. -/
/-
**Partition.partOf** 是 Mathlib 中的一个定义，位于命名空间 `Partition`。
形式化陈述：partOf (P : Partition u) (a : α) : Set α
参数：P : Partition u；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The part of a partition containing a given element. If the element is not in the
underlying set, this is empty.
-/
def partOf (P : Partition u) (a : α) : Set α := {b | P.Rel a b}
/-
**Partition.partOf_subset** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：partOf_subset : P.partOf x subseteq u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
-/
lemma partOf_subset : P.partOf x ⊆ u := fun _ ⟨_, ht, _, hyt⟩ ↦ subset_of_mem ht hyt
/-
**Partition.mem_partOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Partition`。
形式化陈述：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partition u}, x ∈ P.partOf y ↔
 P.Rel y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_partOf_iff : x ∈ P.partOf y ↔ P.Rel y x := Iff.rfl
/-
**Partition.eq_partOf_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：eq_partOf_of_mem (ht : t in P) (hxt : x in t) : t = P.partOf x
参数：ht : t in P；hxt : x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.eq_of_mem_of_mem`：eq_of_mem_of_mem (ht : t in P) (hus : s in P
) (hxt : x in t) (hxs : x in s) : t = s
-/
lemma eq_partOf_of_mem (ht : t ∈ P) (hxt : x ∈ t) : t = P.partOf x := by
  ext y
  exact ⟨(⟨t, ht, hxt, ·⟩), fun ⟨s, hsP, hxs, hys⟩ ↦ (P.eq_of_mem_of_mem ht hsP hxt hxs) ▸ hys⟩
/-
**Partition.mem_iff_mem_partOf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_iff_mem_partOf_mem : x in u ↔ x in P.partOf x ∧ P.partOf x in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Partition.mem_iff_exists`：mem_iff_exists : x in u ↔ exists t in P, x in 
t
· 使用引理 `Partition.eq_partOf_of_mem`：eq_partOf_of_mem (ht : t in P) (hxt : x in t
) : t = P.partOf x
· 使用引理 `Partition.subset_of_mem`：subset_of_mem (ht : t in P) : t subseteq u
-/
lemma mem_iff_mem_partOf_mem : x ∈ u ↔ x ∈ P.partOf x ∧ P.partOf x ∈ P := by
  refine ⟨fun hx ↦ ?_, fun ⟨hx, hP⟩ ↦ subset_of_mem hP hx⟩
  obtain ⟨t, htP, hxt⟩ := P.mem_iff_exists.mp hx
  exact P.eq_partOf_of_mem htP hxt ▸ ⟨hxt, htP⟩
/-
**Partition.mem_partOf** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_partOf (hxu : x in u) : x in P.partOf x
参数：hxu : x in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Partition.mem_iff_mem_partOf_mem`：mem_iff_mem_partOf_mem : x in u ↔ x in
 P.partOf x ∧ P.partOf x in P
-/
lemma mem_partOf (hxu : x ∈ u) : x ∈ P.partOf x := (P.mem_iff_mem_partOf_mem.mp hxu).1
/-
**Partition.partOf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：partOf_mem (hxu : x in u) : P.partOf x in P
参数：hxu : x in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Partition.mem_iff_mem_partOf_mem`：mem_iff_mem_partOf_mem : x in u ↔ x in
 P.partOf x ∧ P.partOf x in P
-/
lemma partOf_mem (hxu : x ∈ u) : P.partOf x ∈ P := (P.mem_iff_mem_partOf_mem.mp hxu).2

@[simp]
/-
**Partition.partOf_rep** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：partOf_rep (hs : s in P) : P.partOf (P.rep hs) = s
参数：hs : s in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.eq_partOf_of_mem`：eq_partOf_of_mem (ht : t in P) (hxt : x in t
) : t = P.partOf x
· 使用定理 `Partition.rep_mem`：∀ {α : Type u_1} {u t : Set α} {P : Partition u} (ht 
: t ∈ P), P.rep ht ∈ t
-/
lemma partOf_rep (hs : s ∈ P) : P.partOf (P.rep hs) = s :=
  eq_partOf_of_mem hs (rep_mem hs) |>.symm
/-
**Partition.mem_iff_exists_partOf** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：mem_iff_exists_partOf : s in P ↔ exists x in u, partOf P x = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.rep_mem_supp`：∀ {α : Type u_1} {u t : Set α} {P : Partition u}
 (ht : t ∈ P), P.rep ht ∈ u
· 使用引理 `Partition.partOf_rep`：partOf_rep (hs : s in P) : P.partOf (P.rep hs) = s
· 使用引理 `Partition.partOf_mem`：partOf_mem (hxu : x in u) : P.partOf x in P
-/
lemma mem_iff_exists_partOf : s ∈ P ↔ ∃ x ∈ u, partOf P x = s :=
  ⟨fun hs ↦ ⟨P.rep hs, rep_mem_supp hs, partOf_rep hs⟩, fun ⟨_, hxu, h⟩ ↦ h ▸ partOf_mem hxu⟩
/-
**Partition.partOf_nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：partOf_nonempty_iff : (P.partOf x).Nonempty ↔ x in u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.Rel.left_mem`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Part
ition u}, P.Rel x y → x ∈ u
· 使用引理 `Partition.ne_bot_of_mem`：ne_bot_of_mem (hx : x in P) : x != ⊥
· 使用引理 `Partition.partOf_mem`：partOf_mem (hxu : x in u) : P.partOf x in P
-/
lemma partOf_nonempty_iff : (P.partOf x).Nonempty ↔ x ∈ u := by
  refine ⟨fun ⟨y, hy⟩ ↦ hy.left_mem, fun h ↦ ?_⟩
  simpa [nonempty_iff_ne_empty] using P.ne_bot_of_mem (partOf_mem h)

@[simp]
/-
**Partition.partOf_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：partOf_eq_empty_iff : P.partOf x = ∅ ↔ x ∉ u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.partOf_nonempty_iff`：partOf_nonempty_iff : (P.partOf x).Nonemp
ty ↔ x in u
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma partOf_eq_empty_iff : P.partOf x = ∅ ↔ x ∉ u := by
  rw [← partOf_nonempty_iff, not_nonempty_iff_eq_empty]
/-
**Partition.rel_iff_partOf_eq_partOf_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition
`。
形式化陈述：rel_iff_partOf_eq_partOf_of_mem (P : Partition u) (hx : x in u) (hy : y in
 u) : P.Rel x y ↔ P.partOf x = P.partOf y
参数：P : Partition u；hx : x in u；hy : y in u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.eq_partOf_of_mem`：eq_partOf_of_mem (ht : t in P) (hxt : x in t
) : t = P.partOf x
· 使用引理 `Partition.partOf_mem`：partOf_mem (hxu : x in u) : P.partOf x in P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.mem_partOf`：mem_partOf (hxu : x in u) : x in P.partOf x
-/
lemma rel_iff_partOf_eq_partOf_of_mem (P : Partition u) (hx : x ∈ u) (hy : y ∈ u) :
    P.Rel x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ eq_partOf_of_mem (P.partOf_mem hx) ?_,
    fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, h ▸ mem_partOf hy⟩⟩
  rwa [← eq_partOf_of_mem htP hxt]
/-
**Partition.rel_iff_partOf_eq_partOf** 是 Mathlib 中的一个引理，位于命名空间 `Partition`。
形式化陈述：rel_iff_partOf_eq_partOf (P : Partition u) : P.Rel x y ↔ exists (_ : x in 
u) (_ : y in u), P.partOf x = P.partOf y
参数：P : Partition u。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rel_iff_partOf_eq_partOf (P : Partition u) :
    P.Rel x y ↔ ∃ (_ : x ∈ u) (_ : y ∈ u), P.partOf x = P.partOf y := by
  grind [rel_iff_partOf_eq_partOf_of_mem, Rel.left_mem, Rel.right_mem]

end partOf

/-! ### Representative functions

See the module docstring for motivation (graph simplification, minors, and why we use an explicit
`IsRepFun` hypothesis rather than a global choice of representatives).
-/

section IsRepFun

/-- A predicate characterizing when a function `f : α → α` is a representative function for a
partition `P`. A representative function maps each element to a canonical representative in its
equivalence class, is the identity outside the support, and maps related elements to the same
representative. -/
/-
**Partition.IsRepFun** 是 Mathlib 中的一个归纳类型，位于命名空间 `Partition`。
形式化陈述：{α : Type u_1} → {u : Set α} → Partition u → (α → α) → Prop
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate characterizing when a function `f : α → α` is a representative funct
ion for a
partition `P`. A representative function maps each element to a canonical repres
entative in its
equivalence class, is the identity outside the support, and maps related element
s to the same
representative.
-/
structure IsRepFun {u : Set α} (P : Partition u) (f : α → α) : Prop where
  /-- The function is the identity outside the support. -/
  apply_of_notMem : ∀ ⦃a⦄, a ∉ u → f a = a
  /-- The function maps each element in the support to a related element. -/
  rel_apply : ∀ ⦃a⦄, a ∈ u → P.Rel a (f a)
  /-- The function maps related elements to the same representative. -/
  apply_eq_apply : ∀ ⦃a b⦄, P.Rel a b → f a = f b

namespace IsRepFun

variable {u : Set α} {P : Partition u} {f g : α → α} {a b c : α}

/-
**Partition.IsRepFun.apply_mem** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsRepFun`。
形式化陈述：apply_mem (hf : IsRepFun P f) (ha : a in u) : f a in u
参数：hf : IsRepFun P f；ha : a in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.Rel.right_mem`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Par
tition u}, P.Rel x y → y ∈ u
· 使用定理 `Partition.IsRepFun.rel_apply`：∀ {α : Type u_1} {u : Set α} {P : Partitio
n u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∈ u → P.Rel a (f a)
-/
lemma apply_mem (hf : IsRepFun P f) (ha : a ∈ u) : f a ∈ u := (hf.rel_apply ha).right_mem
/-
**Partition.IsRepFun.image_subset** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsRepFun`
。
形式化陈述：image_subset (hf : IsRepFun P f) (hs : u subseteq s) : f '' s subseteq s
参数：hf : IsRepFun P f；hs : u subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.IsRepFun.apply_mem`：apply_mem (hf : IsRepFun P f) (ha : a in u
) : f a in u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
-/
lemma image_subset (hf : IsRepFun P f) (hs : u ⊆ s) : f '' s ⊆ s := by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a ∈ u
  · exact hs <| hf.apply_mem ha
  exact (hf.apply_of_notMem ha).symm ▸ haS
/-
**Partition.IsRepFun.mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsRepFun`。
形式化陈述：mapsTo (hf : IsRepFun P f) (hs : u subseteq s) : Set.MapsTo f s s
参数：hf : IsRepFun P f；hs : u subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.IsRepFun.image_subset`：image_subset (hf : IsRepFun P f) (hs : 
u subseteq s) : f '' s subseteq s
-/
lemma mapsTo (hf : IsRepFun P f) (hs : u ⊆ s) : Set.MapsTo f s s :=
  fun x h ↦ hf.image_subset hs ⟨x, h, rfl⟩
/-
**Partition.IsRepFun.mapsTo_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsR
epFun`。
形式化陈述：mapsTo_of_disjoint (hf : IsRepFun P f) (hs : Disjoint u s) : Set.MapsTo f 
s s
参数：hf : IsRepFun P f；hs : Disjoint u s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
· 使用定理 `Disjoint.notMem_of_mem_right`：∀ {α : Type u} {s t : Set α}, Disjoint s t
 → ∀ ⦃a : α⦄, a ∈ t → a ∉ s
-/
lemma mapsTo_of_disjoint (hf : IsRepFun P f) (hs : Disjoint u s) : Set.MapsTo f s s :=
  fun _ h ↦ (hf.apply_of_notMem <| hs.notMem_of_mem_right h).symm ▸ h
/-
**Partition.IsRepFun.apply_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsRepFun
`。
形式化陈述：apply_mem_iff (hf : IsRepFun P f) (hs : u subseteq s) : f a in s ↔ a in s
参数：hf : IsRepFun P f；hs : u subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.mem_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β},   Set.MapsTo f s t → Set.MapsTo f sᶜ tᶜ → ∀ {x : α}, f x ∈ t ↔ 
x ∈ s
· 使用引理 `Partition.IsRepFun.mapsTo`：mapsTo (hf : IsRepFun P f) (hs : u subseteq s
) : Set.MapsTo f s s
· 使用引理 `Partition.IsRepFun.mapsTo_of_disjoint`：mapsTo_of_disjoint (hf : IsRepFun
 P f) (hs : Disjoint u s) : Set.MapsTo f s s
· 使用定理 `LE.le.disjoint_compl_right`：LE.le.disjoint_compl_right (h : a <= b) : Di
sjoint a bᶜ
-/
lemma apply_mem_iff (hf : IsRepFun P f) (hs : u ⊆ s) : f a ∈ s ↔ a ∈ s :=
  hf.mapsTo hs |>.mem_iff <| mapsTo_of_disjoint hf hs.disjoint_compl_right
/-
**Partition.IsRepFun.apply_eq_apply_iff_rel** 是 Mathlib 中的一个引理，位于命名空间 `Partition
.IsRepFun`。
形式化陈述：apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a in u) : f a = f b ↔ P.R
el a b
参数：hf : IsRepFun P f；ha : a in u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partition.Rel.trans`：∀ {α : Type u_1} {x y z : α} {u : Set α} {P : Parti
tion u}, P.Rel x y → P.Rel y z → P.Rel x z
· 使用定理 `Partition.IsRepFun.rel_apply`：∀ {α : Type u_1} {u : Set α} {P : Partitio
n u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∈ u → P.Rel a (f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Partition.rel_comm`：rel_comm : P.Rel x y ↔ P.Rel y x
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
· 使用引理 `Partition.IsRepFun.apply_mem`：apply_mem (hf : IsRepFun P f) (ha : a in u
) : f a in u
· 使用定理 `Partition.IsRepFun.apply_eq_apply`：∀ {α : Type u_1} {u : Set α} {P : Par
tition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a b : α⦄, P.Rel a b → f a = f b
-/
lemma apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a ∈ u) : f a = f b ↔ P.Rel a b := by
  refine ⟨fun hab ↦ (hf.rel_apply ha).trans ?_, (hf.apply_eq_apply ·)⟩
  rw [hab, P.rel_comm]
  refine hf.rel_apply <| by_contra fun hb ↦ ?_
  rw [hf.apply_of_notMem hb] at hab
  exact hab ▸ hb <| hf.apply_mem ha
/-
**Partition.IsRepFun.apply_eq_apply_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsR
epFun`。
形式化陈述：apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P.Rel a b
参数：hf : IsRepFun P f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Partition.IsRepFun.apply_eq_apply_iff_rel`：apply_eq_apply_iff_rel (hf : 
IsRepFun P f) (ha : a in u) : f a = f b ↔ P.Rel a b
· 使用定理 `Partition.Rel.symm`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partitio
n u}, P.Rel x y → P.Rel y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Partition.IsRepFun.apply_eq_apply`：∀ {α : Type u_1} {u : Set α} {P : Par
tition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a b : α⦄, P.Rel a b → f a = f b
-/
lemma apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P.Rel a b := by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne ↦ ?_, fun h ↦ ?_⟩
  · obtain (ha | ha) := em (a ∈ u)
    · exact hf.apply_eq_apply_iff_rel ha |>.mp hab
    obtain (hb | hb) := em (b ∈ u)
    · exact (hf.apply_eq_apply_iff_rel hb |>.mp hab.symm).symm
    rw [hf.apply_of_notMem ha, hf.apply_of_notMem hb] at hab
    contradiction
  obtain rfl | hne := eq_or_ne a b
  · rfl
  exact hf.apply_eq_apply (h hne)
/-
**Partition.IsRepFun.forall_apply_eq_apply_iff** 是 Mathlib 中的一个引理，位于命名空间 `Partit
ion.IsRepFun`。
形式化陈述：forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) : (forall (x : α), f a =
 f x ↔ a = x) ∨ (forall (x : α), f a = f x ↔ P.Rel a x)
参数：hf : IsRepFun P f；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Partition.IsRepFun.apply_eq_apply_iff_rel`：apply_eq_apply_iff_rel (hf : 
IsRepFun P f) (ha : a in u) : f a = f b ↔ P.Rel a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Partition.IsRepFun.apply_mem_iff`：apply_mem_iff (hf : IsRepFun P f) (hs 
: u subseteq s) : f a in s ↔ a in s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) :
    (∀ (x : α), f a = f x ↔ a = x) ∨ (∀ (x : α), f a = f x ↔ P.Rel a x) := by
  refine (em (a ∈ u)).elim (fun ha ↦ Or.inr fun b ↦ ?_) (fun ha ↦ Or.inl fun b ↦ ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
  · exact hf.apply_of_notMem <| hf.apply_mem_iff le_rfl |>.not.mp ha
  exact hf.apply_of_notMem ha |>.symm
/-
**Partition.IsRepFun.apply_eq_apply_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Partition.Is
RepFun`。
形式化陈述：apply_eq_apply_iff' (hf : IsRepFun P f) : f a = f b ↔ (a = b ∧ forall c, f
 a = f c ↔ a = c) ∨ P.Rel a b
参数：hf : IsRepFun P f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.IsRepFun.forall_apply_eq_apply_iff`：forall_apply_eq_apply_iff 
(hf : IsRepFun P f) (a) : (forall (x : α), f a = f x ↔ a = x) ∨ (forall (x : α),
 f a = f x ↔ P.Rel a x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Partition.IsRepFun.apply_eq_apply`：∀ {α : Type u_1} {u : Set α} {P : Par
tition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a b : α⦄, P.Rel a b → f a = f b
-/
lemma apply_eq_apply_iff' (hf : IsRepFun P f) :
    f a = f b ↔ (a = b ∧ ∀ c, f a = f c ↔ a = c) ∨ P.Rel a b := by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind
/-
**Partition.IsRepFun.idem** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsRepFun`。
形式化陈述：idem (hf : IsRepFun P f) : f (f a) = f a
参数：hf : IsRepFun P f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Partition.IsRepFun.apply_eq_apply_iff_rel`：apply_eq_apply_iff_rel (hf : 
IsRepFun P f) (ha : a in u) : f a = f b ↔ P.Rel a b
· 使用定理 `Partition.IsRepFun.rel_apply`：∀ {α : Type u_1} {u : Set α} {P : Partitio
n u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∈ u → P.Rel a (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma idem (hf : IsRepFun P f) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ u)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]
/-
**Partition.IsRepFun.apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Partition.IsRepFun`。
形式化陈述：apply_apply (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f 
x
参数：hf : IsRepFun P f；hg : IsRepFun P g；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Partition.IsRepFun.apply_eq_apply`：∀ {α : Type u_1} {u : Set α} {P : Par
tition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a b : α⦄, P.Rel a b → f a = f b
· 使用定理 `Partition.Rel.symm`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partitio
n u}, P.Rel x y → P.Rel y x
· 使用定理 `Partition.IsRepFun.rel_apply`：∀ {α : Type u_1} {u : Set α} {P : Partitio
n u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∈ u → P.Rel a (f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Partition.IsRepFun.apply_of_notMem`：∀ {α : Type u_1} {u : Set α} {P : Pa
rtition u} {f : α → α}, P.IsRepFun f → ∀ ⦃a : α⦄, a ∉ u → f a = a
-/
theorem apply_apply (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f x := by
  obtain (hx | hx) := em (x ∈ u)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx, hf.apply_of_notMem hx]

/-- Any partially defined representative function extends to a complete one. -/
/-
**Partition.IsRepFun.exists_extend_partial** 是 Mathlib 中的一个引理，位于命名空间 `Partition.
IsRepFun`。
形式化陈述：exists_extend_partial (P : Partition u) (f₀ : t -> α) (h_notMem : forall x
 : t, x.1 ∉ u -> f₀ x = x) (h_mem : forall x : t, x.1 in u -> P.Rel x (f₀ x)) (h
_eq : forall x y : t, P.Rel x y -> f₀ x = f₀ y) : exists f, IsRepFun P f ∧ foral
l x : t, f x = f₀ x
参数：P : Partition u；f₀ : t -> α；h_notMem : forall x : t, x.1 ∉ u -> f₀ x = x；h_me
m : forall x : t, x.1 in u -> P.Rel x (f₀ x)；h_eq : forall x y : t, P.Rel x y ->
 f₀ x = f₀ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.partOf_mem`：partOf_mem (hxu : x in u) : P.partOf x in P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Partition.Rel.trans`：∀ {α : Type u_1} {x y z : α} {u : Set α} {P : Parti
tion u}, P.Rel x y → P.Rel y z → P.Rel x z
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Partition.Rel.right_mem`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Par
tition u}, P.Rel x y → y ∈ u
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Partition.rep_rel`：rep_rel (ht : t in P) (hx : x in t) : P.Rel x (P.rep 
ht)
· 使用引理 `Partition.mem_partOf`：mem_partOf (hxu : x in u) : x in P.partOf x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Partition.Rel.left_mem`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Part
ition u}, P.Rel x y → x ∈ u
· 使用定理 `Partition.Rel.symm`：∀ {α : Type u_1} {x y : α} {u : Set α} {P : Partitio
n u}, P.Rel x y → P.Rel y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Partition.rel_iff_partOf_eq_partOf_of_mem`：rel_iff_partOf_eq_partOf_of_m
em (P : Partition u) (hx : x in u) (hy : y in u) : P.Rel x y ↔ P.partOf x = P.pa
rtOf y
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Any partially defined representative function extends to a complete one.
-/
lemma exists_extend_partial (P : Partition u) (f₀ : t → α)
    (h_notMem : ∀ x : t, x.1 ∉ u → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ u → P.Rel x (f₀ x))
    (h_eq : ∀ x y : t, P.Rel x y → f₀ x = f₀ y) : ∃ f, IsRepFun P f ∧ ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ u then
    (if hb : ∃ b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha ↦ by simp [hfdef, ha], fun a ha ↦ ?_, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.right_mem
    push Not at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hfdef, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩ |>.elim
    · exact h₁ ⟨_, hab.trans h₂.choose_spec⟩ |>.elim
    congr 1
    rwa [← rel_iff_partOf_eq_partOf_of_mem _ hab.left_mem hab.right_mem]
  obtain (ha | ha) := em (a.1 ∈ u) |>.symm
  · simp [hfdef, ha, h_notMem _ ha]
  simp only [hfdef, ha, ↓reduceDIte]
  split_ifs with h
  · exact h_eq _ _ h.choose_spec |>.symm
  exact h ⟨a, rel_rfl_iff.mpr ha⟩ |>.elim

/-- For any set `t` containing no two distinct related elements, there is a representative function
equal to the identity on `t`. -/
/-
**Partition.IsRepFun.exists_extend_partial'** 是 Mathlib 中的一个引理，位于命名空间 `Partition
.IsRepFun`。
形式化陈述：exists_extend_partial' (P : Partition u) (h : forall ⦃x y⦄, x in t -> y in
 t -> P.Rel x y -> x = y) : exists f, IsRepFun P f ∧ EqOn f id t
参数：P : Partition u；h : forall ⦃x y⦄, x in t -> y in t -> P.Rel x y -> x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Partition.IsRepFun.exists_extend_partial`：exists_extend_partial (P : Par
tition u) (f₀ : t -> α) (h_notMem : forall x : t, x.1 ∉ u -> f₀ x = x) (h_mem : 
forall x : t, x.1 in u -> P.Re…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
For any set `t` containing no two distinct related elements, there is a represen
tative function
equal to the identity on `t`.
-/
lemma exists_extend_partial' (P : Partition u)
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P.Rel x y → x = y) : ∃ f, IsRepFun P f ∧ EqOn f id t := by
  simpa using! exists_extend_partial P (fun x : t ↦ x) (by simp) (by simp) (fun x y ↦ h x.2 y.2)

/-- Every partition has a representative function. -/
/-
**Partition.IsRepFun.nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Partition.IsRepFun`。
形式化陈述：nonempty (P : Partition u) : exists f, IsRepFun P f
参数：P : Partition u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partition.IsRepFun.exists_extend_partial'`：exists_extend_partial' (P : P
artition u) (h : forall ⦃x y⦄, x in t -> y in t -> P.Rel x y -> x = y) : exists 
f, IsRepFun P f ∧ EqOn f id t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Every partition has a representative function.
-/
lemma nonempty (P : Partition u) : ∃ f, IsRepFun P f := by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

end IsRepFun
end Partition.IsRepFun

