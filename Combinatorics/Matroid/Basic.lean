/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.UpperLower.Closure

/-!
# Matroids

A `Matroid` is a structure that combinatorially abstracts
the notion of linear independence and dependence;
matroids have connections with graph theory, discrete optimization,
additive combinatorics and algebraic geometry.
Mathematically, a matroid `M` is a structure on a set `E` comprising a
collection of subsets of `E` called the bases of `M`,
where the bases are required to obey certain axioms.

This file gives a definition of a matroid `M` in terms of its bases,
and some API relating independent sets (subsets of bases) and the notion of a
basis of a set `X` (a maximal independent subset of `X`).

## Main definitions

* a `Matroid α` on a type `α` is a structure comprising a 'ground set'
  and a suitably behaved 'base' predicate.

Given `M : Matroid α` ...

* `M.E` denotes the ground set of `M`, which has type `Set α`
* For `B : Set α`, `M.IsBase B` means that `B` is a base of `M`.
* For `I : Set α`, `M.Indep I` means that `I` is independent in `M`
    (that is, `I` is contained in a base of `M`).
* For `D : Set α`, `M.Dep D` means that `D` is contained in the ground set of `M`
    but isn't independent.
* For `I : Set α` and `X : Set α`, `M.IsBasis I X` means that `I` is a maximal independent
    subset of `X`.
* `M.Finite` means that `M` has finite ground set.
* `M.Nonempty` means that the ground set of `M` is nonempty.
* `RankFinite M` means that the bases of `M` are finite.
* `RankInfinite M` means that the bases of `M` are infinite.
* `RankPos M` means that the bases of `M` are nonempty.
* `Finitary M` means that a set is independent if and only if all its finite subsets are
    independent.

* `aesop_mat` : a tactic designed to prove `X ⊆ M.E` for some set `X` and matroid `M`.

## Implementation details

There are a few design decisions worth discussing.

### Finiteness
  The first is that our matroids are allowed to be infinite.
  Unlike with many mathematical structures, this isn't such an obvious choice.
  Finite matroids have been studied since the 1930's,
  and there was never controversy as to what is and isn't an example of a finite matroid -
  in fact, surprisingly many apparently different definitions of a matroid
  give rise to the same class of objects.

  However, generalizing different definitions of a finite matroid
  to the infinite in the obvious way (i.e. by simply allowing the ground set to be infinite)
  gives a number of different notions of 'infinite matroid' that disagree with each other,
  and that all lack nice properties.
  Many different competing notions of infinite matroid were studied through the years;
  in fact, the problem of which definition is the best was only really solved in 2013,
  when Bruhn et al. [2] showed that there is a unique 'reasonable' notion of an infinite matroid
  (these objects had previously defined by Higgs under the name 'B-matroid').
  These are defined by adding one carefully chosen axiom to the standard set,
  and adapting existing axioms to not mention set cardinalities;
  they enjoy nearly all the nice properties of standard finite matroids.

  Even though at least 90% of the literature is on finite matroids,
  B-matroids are the definition we use, because they allow for additional generality,
  nearly all theorems are still true and just as easy to state,
  and (hopefully) the more general definition will prevent the need for a costly future refactor.
  The disadvantage is that developing API for the finite case is harder work
  (for instance, it is harder to prove that something is a matroid in the first place,
  and one must deal with `ℕ∞` rather than `ℕ`).
  For serious work on finite matroids, we provide the typeclasses
  `[M.Finite]` and `[RankFinite M]` and associated API.

### Cardinality
  Just as with bases of a vector space,
  all bases of a finite matroid `M` are finite and have the same cardinality;
  this cardinality is an important invariant known as the 'rank' of `M`.
  For infinite matroids, bases are not in general equicardinal;
  in fact the equicardinality of bases of infinite matroids is independent of ZFC [3].
  What is still true is that either all bases are finite and equicardinal,
  or all bases are infinite. This means that the natural notion of 'size'
  for a set in matroid theory is given by the function `Set.encard`, which
  is the cardinality as a term in `ℕ∞`. We use this function extensively
  in building the API; it is preferable to both `Set.ncard` and `Finset.card`
  because it allows infinite sets to be handled without splitting into cases.

### The ground `Set`
  A last place where we make a consequential choice is making the ground set of a matroid
  a structure field of type `Set α` (where `α` is the type of 'possible matroid elements')
  rather than just having a type `α` of all the matroid elements.
  This is because of how common it is to simultaneously consider
  a number of matroids on different but related ground sets.
  For example, a matroid `M` on ground set `E` can have its structure
  'restricted' to some subset `R ⊆ E` to give a smaller matroid `M ↾ R` with ground set `R`.
  A statement like `(M ↾ R₁) ↾ R₂ = M ↾ R₂` is mathematically obvious.
  But if the ground set of a matroid is a type, this doesn't typecheck,
  and is only true up to canonical isomorphism.
  Restriction is just the tip of the iceberg here;
  one can also 'contract' and 'delete' elements and sets of elements
  in a matroid to give a smaller matroid,
  and in practice it is common to make statements like `M₁.E = M₂.E ∩ M₃.E` and
  `((M ⟋ e) ↾ R) ⟋ C = M ⟋ (C ∪ {e}) ↾ R`.
  Such things are a nightmare to work with unless `=` is actually propositional equality
  (especially because the relevant coercions are usually between sets and not just elements).

  So the solution is that the ground set `M.E` has type `Set α`,
  and there are elements of type `α` that aren't in the matroid.
  The tradeoff is that for many statements, one now has to add
  hypotheses of the form `X ⊆ M.E` to make sure than `X` is actually 'in the matroid',
  rather than letting a 'type of matroid elements' take care of this invisibly.
  It still seems that this is worth it.
  The tactic `aesop_mat` exists specifically to discharge such goals
  with minimal fuss (using default values).
  The tactic works fairly well, but has room for improvement.

  A related decision is to not have matroids themselves be a typeclass.
  This would make things be notationally simpler
  (having `Base` in the presence of `[Matroid α]` rather than `M.Base` for a term `M : Matroid α`)
  but is again just too awkward when one has multiple matroids on the same type.
  In fact, in regular written mathematics,
  it is normal to explicitly indicate which matroid something is happening in,
  so our notation mirrors common practice.

### Notation
  We use a few nonstandard conventions in theorem names that are related to the above.
  First, we mirror common informal practice by referring explicitly to the `ground` set rather
  than the notation `E`. (Writing `ground` everywhere in a proof term would be unwieldy, and
  writing `E` in theorem names would be unnatural to read.)

  Second, because we are typically interested in subsets of the ground set `M.E`,
  using `Set.compl` is inconvenient, since `Xᶜ ⊆ M.E` is typically false for `X ⊆ M.E`.
  On the other hand (especially when duals arise), it is common to complement
  a set `X ⊆ M.E` *within* the ground set, giving `M.E \ X`.
  For this reason, we use the term `compl` in theorem names to refer to taking a set difference
  with respect to the ground set, rather than a complement within a type. The lemma
  `compl_isBase_dual` is one of the many examples of this.

  Finally, in theorem names, matroid predicates that apply to sets
  (such as `Base`, `Indep`, `IsBasis`) are typically used as suffixes rather than prefixes.
  For instance, we have `ground_indep_iff_isBase` rather than `indep_ground_iff_isBase`.

## References

* [J. Oxley, Matroid Theory][oxley2011]
* [H. Bruhn, R. Diestel, M. Kriesell, R. Pendavingh, P. Wollan, Axioms for infinite matroids,
  Adv. Math 239 (2013), 18-46][bruhnDiestelKriesellPendavinghWollan2013]
* [N. Bowler, S. Geschke, Self-dual uniform matroids on infinite sets,
  Proc. Amer. Math. Soc. 144 (2016), 459-471][bowlerGeschke2015]
-/

@[expose] public section

assert_not_exists Field

open Set

/--
Definition of `Matroid.ExchangeProperty` / `Matroid.ExchangeProperty` 的定义

English:
definition Matroid.ExchangeProperty
  signature: {α : Type*} (P : Set α -> Prop)
  body: forall X Y, P X -> P Y -> forall a in X \ Y, exists b in Y \ X, P (insert b (X \ {a}))

中文:
定义 拟阵.ExchangeProperty
  签名: {α : 类型} (P : 集合 α -> 命题)
  定义体: forall X Y, P X -> P Y -> forall a in X \ Y, exists b in Y \ X, P (insert b (X \ {a}))

Depends on / 依赖: insert
-/
def Matroid.ExchangeProperty {α : Type*} (P : Set α -> Prop) : Prop :=
  forall X Y, P X -> P Y -> forall a in X \ Y, exists b in Y \ X, P (insert b (X \ {a}))

/--
Definition of `Matroid.ExistsMaximalSubsetProperty` / `Matroid.ExistsMaximalSubsetProperty` 的定义

English:
definition Matroid.ExistsMaximalSubsetProperty
  signature: {α : Type*} (P : Set α -> Prop) (X : Set α)
  body: forall I, P I -> I subseteq X -> exists J, I subseteq J ∧ Maximal (fun K => P K ∧ K subseteq X) J

中文:
定义 拟阵.ExistsMaximalSubsetProperty
  签名: {α : 类型} (P : 集合 α -> 命题) (X : 集合 α)
  定义体: forall I, P I -> I subseteq X -> exists J, I subseteq J ∧ Maximal (fun K => P K ∧ K subseteq X) J

Depends on / 依赖: Maximal, subseteq
-/
def Matroid.ExistsMaximalSubsetProperty {α : Type*} (P : Set α -> Prop) (X : Set α) : Prop :=
  forall I, P I -> I subseteq X -> exists J, I subseteq J ∧ Maximal (fun K => P K ∧ K subseteq X) J

/--
Definition of `Matroid` / `Matroid` 的定义

English:
structure Matroid
  parameters: (α : Type*)
  axioms and operations (8):
    - (E : Set α)
    - (IsBase : Set α -> Prop)
    - (Indep : Set α -> Prop)
    - (indep_iff' : forall ⦃I⦄, Indep I ↔ exists B, IsBase B ∧ I subseteq B)
    - (exists_isBase : exists B, IsBase B)
    - (isBase_exchange : Matroid.ExchangeProperty IsBase)
    - (maximality : forall X, X subseteq E -> Matroid.ExistsMaximalSubsetProperty Indep X)
    - (subset_ground : forall B, IsBase B -> B subseteq E)

中文:
结构 拟阵
  参数: (α : 类型)
  公理与运算 (8 个):
    - (E : 集合 α)
    - (IsBase : 集合 α -> 命题)
    - (Indep : 集合 α -> 命题)
    - (indep_iff' : 对任意 ⦃I⦄, Indep I ↔ 存在 B, IsBase B ∧ I subseteq B)
    - (exists_isBase : 存在 B, IsBase B)
    - (isBase_exchange : 拟阵.ExchangeProperty IsBase)
    - (maximality : 对任意 X, X subseteq E -> 拟阵.ExistsMaximalSubsetProperty Indep X)
    - (subset_ground : 对任意 B, IsBase B -> B subseteq E)

Depends on / 依赖: FinEnum, Fintype
-/
structure Matroid (α : Type*) where
  /-- `M` has a ground set `E`. -/
  (E : Set α)
  /-- `M` has a predicate `Base` defining its bases. -/
  (IsBase : Set α -> Prop)
  /-- `M` has a predicate `Indep` defining its independent sets. -/
  (Indep : Set α -> Prop)
  /-- The `Indep`endent sets are those contained in `Base`s. -/
  (indep_iff' : forall ⦃I⦄, Indep I ↔ exists B, IsBase B ∧ I subseteq B)
  /-- There is at least one `Base`. -/
  (exists_isBase : exists B, IsBase B)
  /-- For any bases `B`, `B'` and `e ∈ B \ B'`, there is some `f ∈ B' \ B` for which `B-e+f`
  is a base. -/
  (isBase_exchange : Matroid.ExchangeProperty IsBase)
  /-- Every independent subset `I` of a set `X` for is contained in a maximal independent
  subset of `X`. -/
  (maximality : forall X, X subseteq E -> Matroid.ExistsMaximalSubsetProperty Indep X)
  /-- Every base is contained in the ground set. -/
  (subset_ground : forall B, IsBase B -> B subseteq E)

attribute [local ext] Matroid

namespace Matroid

variable {α : Type*} {M : Matroid α}

instance (M : Matroid α) : Nonempty {B // M.IsBase B} :=
  nonempty_subtype.2 M.exists_isBase

/--
Definition of `Finite` / `Finite` 的定义

English:
class Finite
  parameters: (M : Matroid α)
  axioms and operations (1):
    - (ground_finite : M.E.Finite)

中文:
类 有限
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - (ground_finite : M.E.有限)
-/
@[mk_iff] protected class Finite (M : Matroid α) : Prop where
  /-- The ground set is finite -/
  (ground_finite : M.E.Finite)

/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
class Nonempty
  parameters: (M : Matroid α)
  axioms and operations (1):
    - (ground_nonempty : M.E.Nonempty)

中文:
类 非空
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - (ground_nonempty : M.E.非空)
-/
protected class Nonempty (M : Matroid α) : Prop where
  /-- The ground set is nonempty -/
  (ground_nonempty : M.E.Nonempty)

/--
theorem `ground_nonempty` / 定理 `ground_nonempty`

English:
theorem ground_nonempty
  given: (M : Matroid α) [M.Nonempty]
  statement: M.E.Nonempty
  proof: Nonempty.ground_nonempty

中文:
定理 ground_nonempty
  条件: (M : 拟阵 α) [M.非空]
  结论: M.E.非空
  证明: Nonempty.ground_nonempty

Depends on / 依赖: Nonempty, Nonempty.ground_nonempty, ground_nonempty
-/
theorem ground_nonempty (M : Matroid α) [M.Nonempty] : M.E.Nonempty :=
  Nonempty.ground_nonempty

/--
theorem `ground_nonempty_iff` / 定理 `ground_nonempty_iff`

English:
theorem ground_nonempty_iff
  given: (M : Matroid α)
  statement: M.E.Nonempty ↔ M.Nonempty
  proof: ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

中文:
定理 ground_nonempty_iff
  条件: (M : 拟阵 α)
  结论: M.E.非空 ↔ M.非空
  证明: ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩
-/
theorem ground_nonempty_iff (M : Matroid α) : M.E.Nonempty ↔ M.Nonempty :=
  ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

/--
lemma `nonempty_type` / 引理 `nonempty_type`

English:
lemma nonempty_type
  given: (M : Matroid α) [h : M.Nonempty]
  statement: Nonempty α
  proof: ⟨M.ground_nonempty.some⟩

中文:
引理 nonempty_type
  条件: (M : 拟阵 α) [h : M.非空]
  结论: 非空 α
  证明: ⟨M.ground_nonempty.some⟩

Depends on / 依赖: M.ground_nonempty.some, ground_nonempty
-/
lemma nonempty_type (M : Matroid α) [h : M.Nonempty] : Nonempty α :=
  ⟨M.ground_nonempty.some⟩

/--
theorem `ground_finite` / 定理 `ground_finite`

English:
theorem ground_finite
  given: (M : Matroid α) [M.Finite]
  statement: M.E.Finite
  proof: Finite.ground_finite

中文:
定理 ground_finite
  条件: (M : 拟阵 α) [M.有限]
  结论: M.E.有限
  证明: Finite.ground_finite

Depends on / 依赖: Finite, Finite.ground_finite, ground_finite
-/
theorem ground_finite (M : Matroid α) [M.Finite] : M.E.Finite :=
  Finite.ground_finite

/--
theorem `set_finite` / 定理 `set_finite`

English:
theorem set_finite
  given: (M : Matroid α) [M.Finite] (X : Set α) (hX : X subseteq M.E := by aesop)
  statement: X.Finite
  proof: M.ground_finite.subset hX

中文:
定理 set_finite
  条件: (M : 拟阵 α) [M.有限] (X : 集合 α) (hX : X subseteq M.E := by aesop)
  结论: X.有限
  证明: M.ground_finite.subset hX

Depends on / 依赖: Finite, M.ground_finite.subset, X.Finite, ground_finite, subset
-/
theorem set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X subseteq M.E := by aesop) : X.Finite :=
  M.ground_finite.subset hX

/--
Instance `finite_of_finite` / 实例 `finite_of_finite`

English:
instance finite_of_finite
  signature: [Finite α] {M : Matroid α}
  body: ⟨Set.toFinite _⟩

中文:
实例 finite_of_finite
  签名: [有限 α] {M : 拟阵 α}
  定义体: ⟨Set.toFinite _⟩

Depends on / 依赖: Set.toFinite, toFinite
-/
instance finite_of_finite [Finite α] {M : Matroid α} : M.Finite :=
  ⟨Set.toFinite _⟩

/--
Definition of `RankFinite` / `RankFinite` 的定义

English:
class RankFinite
  parameters: (M : Matroid α)
  axioms and operations (1):
    - exists_finite_isBase : exists B, M.IsBase B ∧ B.Finite

中文:
类 RankFinite
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - exists_finite_isBase : 存在 B, M.IsBase B ∧ B.有限
-/
@[mk_iff] class RankFinite (M : Matroid α) : Prop where
  /-- There is a finite base -/
  exists_finite_isBase : exists B, M.IsBase B ∧ B.Finite

/--
Instance `rankFinite_of_finite` / 实例 `rankFinite_of_finite`

English:
instance rankFinite_of_finite
  signature: (M : Matroid α) [M.Finite]
  body: ⟨M.exists_isBase.imp (fun B hB => ⟨hB, M.set_finite B (M.subset_ground _ hB)⟩)⟩

中文:
实例 rankFinite_of_finite
  签名: (M : 拟阵 α) [M.有限]
  定义体: ⟨M.exists_isBase.imp (fun B hB => ⟨hB, M.set_finite B (M.subset_ground _ hB)⟩)⟩

Depends on / 依赖: M.exists_isBase.imp, M.set_finite, M.subset_ground, exists_isBase, set_finite, subset_ground
-/
instance rankFinite_of_finite (M : Matroid α) [M.Finite] : RankFinite M :=
  ⟨M.exists_isBase.imp (fun B hB => ⟨hB, M.set_finite B (M.subset_ground _ hB)⟩)⟩

/--
Definition of `RankInfinite` / `RankInfinite` 的定义

English:
class RankInfinite
  parameters: (M : Matroid α)
  axioms and operations (1):
    - exists_infinite_isBase : exists B, M.IsBase B ∧ B.Infinite

中文:
类 RankInfinite
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - exists_infinite_isBase : 存在 B, M.IsBase B ∧ B.无限
-/
@[mk_iff] class RankInfinite (M : Matroid α) : Prop where
  /-- There is an infinite base -/
  exists_infinite_isBase : exists B, M.IsBase B ∧ B.Infinite

/--
Definition of `RankPos` / `RankPos` 的定义

English:
class RankPos
  parameters: (M : Matroid α)
  axioms and operations (1):
    - empty_not_isBase : ¬M.IsBase ∅

中文:
类 RankPos
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - empty_not_isBase : ¬M.IsBase ∅
-/
@[mk_iff] class RankPos (M : Matroid α) : Prop where
  /-- The empty set isn't a base -/
  empty_not_isBase : ¬M.IsBase ∅

/--
Instance `rankPos_nonempty` / 实例 `rankPos_nonempty`

English:
instance rankPos_nonempty
  signature: {M : Matroid α} [M.RankPos]
  body: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | ⟨e, heB⟩ := B.eq_empty_or_nonempty
· exact False.elim RankPos.empty_not_isBase hB
  exact ⟨e, M.subset_ground B hB heB ⟩

中文:
实例 rankPos_nonempty
  签名: {M : 拟阵 α} [M.RankPos]
  定义体: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | ⟨e, heB⟩ := B.eq_empty_or_nonempty
· exact False.elim RankPos.empty_not_isBase hB
  exact ⟨e, M.subset_ground B hB heB ⟩

Depends on / 依赖: B.eq_empty_or_nonempty, False.elim, M.exists_isBase, M.subset_ground, RankPos, RankPos.empty_not_isBase, empty_not_isBase, eq_empty_or_nonempty, exists_isBase, subset_ground
-/
instance rankPos_nonempty {M : Matroid α} [M.RankPos] : M.Nonempty := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | ⟨e, heB⟩ := B.eq_empty_or_nonempty
· exact False.elim RankPos.empty_not_isBase hB
  exact ⟨e, M.subset_ground B hB heB ⟩

section exchange
namespace ExchangeProperty

variable {IsBase : Set α -> Prop} {B B' : Set α}

/--
theorem `antichain` / 定理 `antichain`

English:
theorem antichain
  given: (exch : ExchangeProperty IsBase) (hB : IsBase B) (hB' : IsBase B') (h : B subseteq B')
  proof: h.antisymm (fun x hx => by_contra
    (fun hxB => let ⟨_, hy, _⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; hy.2 <| h hy.1))

中文:
定理 antichain
  条件: (exch : ExchangeProperty IsBase) (hB : IsBase B) (hB' : IsBase B') (h : B subseteq B')
  证明: h.antisymm (fun x hx => by_contra
    (fun hxB => let ⟨_, hy, _⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; hy.2 <| h hy.1))

Depends on / 依赖: antisymm, h.antisymm
-/
theorem antichain (exch : ExchangeProperty IsBase) (hB : IsBase B) (hB' : IsBase B') (h : B subseteq B') :
    B = B' :=
  h.antisymm (fun x hx => by_contra
    (fun hxB => let ⟨_, hy, _⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; hy.2 <| h hy.1))

/--
theorem `encard_sdiff_le_aux` / 定理 `encard_sdiff_le_aux`

English:
theorem encard_sdiff_le_aux
  statement: {B₁ B₂ : Set α}
  proof: by
  obtain (he | hinf | ⟨e, he, hcard⟩) :=
    (B₂ \ B₁).eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · rw [exch.antichain hB₂ hB₁ (sdiff_eq_empty.mp he)]
  · exact le_top.trans_eq hinf.symm
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  have : encard (insert f (B₂ \ {e}) \ B₁) < encard (B₂ \ B₁) := by
    rw [insert_sdiff_of_mem _ hf.1]; rw [sdiff_sdiff_comm]; exact hcard
  have hencard := encard_sdiff_le_aux exch hB₁ hB'
  rw [insert_sdiff_of_mem _ hf.1]; rw [sdiff_sdiff_comm]; rw [← union_singleton]; rw [← sdiff_sdiff]; rw [sdiff_sdiff_right]; rw [inter_singleton_eq_empty.mpr he.2]; rw [union_empty] at hencard
  rw [← encard_sdiff_singleton_add_one he]; rw [← encard_sdiff_singleton_add_one hf]
  gcongr
termination_by (B₂ \ B₁).encard

@[deprecated (since := "2026-06-03")] alias encard_diff_le_aux := encard_sdiff_le_aux

中文:
定理 encard_sdiff_le_aux
  结论: {B₁ B₂ : 集合 α}
  证明: by
  obtain (he | hinf | ⟨e, he, hcard⟩) :=
    (B₂ \ B₁).eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · rw [exch.antichain hB₂ hB₁ (sdiff_eq_empty.mp he)]
  · exact le_top.trans_eq hinf.symm
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  have : encard (insert f (B₂ \ {e}) \ B₁) < encard (B₂ \ B₁) := by
    rw [insert_sdiff_of_mem _ hf.1]; rw [sdiff_sdiff_comm]; exact hcard
  have hencard := encard_sdiff_le_aux exch hB₁ hB'
  rw [insert_sdiff_of_mem _ hf.1]; rw [sdiff_sdiff_comm]; rw [← union_singleton]; rw [← sdiff_sdiff]; rw [sdiff_sdiff_right]; rw [inter_singleton_eq_empty.mpr he.2]; rw [union_empty] at hencard
  rw [← encard_sdiff_singleton_add_one he]; rw [← encard_sdiff_singleton_add_one hf]
  gcongr
termination_by (B₂ \ B₁).encard

@[deprecated (since := "2026-06-03")] alias encard_diff_le_aux := encard_sdiff_le_aux

Depends on / 依赖: antichain, encard, encard_sdiff_le_aux, eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt, exch.antichain, hencard, hinf.symm, insert, insert_sdiff_of_mem, le_top, le_top.trans_eq, sdiff_eq_empty, sdiff_eq_empty.mp, sdiff_sdiff_comm, trans_eq, union_singleto
-/
theorem encard_sdiff_le_aux {B₁ B₂ : Set α}
    (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    (B₁ \ B₂).encard <= (B₂ \ B₁).encard := by
  obtain (he | hinf | ⟨e, he, hcard⟩) :=
    (B₂ \ B₁).eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · rw [exch.antichain hB₂ hB₁ (sdiff_eq_empty.mp he)]
  · exact le_top.trans_eq hinf.symm
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  have : encard (insert f (B₂ \ {e}) \ B₁) < encard (B₂ \ B₁) := by
    rw [insert_sdiff_of_mem _ hf.1]; rw [sdiff_sdiff_comm]; exact hcard
  have hencard := encard_sdiff_le_aux exch hB₁ hB'
  rw [insert_sdiff_of_mem _ hf.1]; rw [sdiff_sdiff_comm]; rw [← union_singleton]; rw [← sdiff_sdiff]; rw [sdiff_sdiff_right]; rw [inter_singleton_eq_empty.mpr he.2]; rw [union_empty] at hencard
  rw [← encard_sdiff_singleton_add_one he]; rw [← encard_sdiff_singleton_add_one hf]
  gcongr
termination_by (B₂ \ B₁).encard

@[deprecated (since := "2026-06-03")] alias encard_diff_le_aux := encard_sdiff_le_aux

variable {B₁ B₂ : Set α}

/--
theorem `encard_sdiff_eq` / 定理 `encard_sdiff_eq`

English:
theorem encard_sdiff_eq
  given: (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂)
  proof: (encard_sdiff_le_aux exch hB₁ hB₂).antisymm (encard_sdiff_le_aux exch hB₂ hB₁)

@[deprecated (since := "2026-06-03")] alias encard_diff_eq := encard_sdiff_eq

中文:
定理 encard_sdiff_eq
  条件: (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂)
  证明: (encard_sdiff_le_aux exch hB₁ hB₂).antisymm (encard_sdiff_le_aux exch hB₂ hB₁)

@[deprecated (since := "2026-06-03")] alias encard_diff_eq := encard_sdiff_eq

Depends on / 依赖: antisymm, encard_sdiff_le_aux
-/
theorem encard_sdiff_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  (encard_sdiff_le_aux exch hB₁ hB₂).antisymm (encard_sdiff_le_aux exch hB₂ hB₁)

@[deprecated (since := "2026-06-03")] alias encard_diff_eq := encard_sdiff_eq

/--
theorem `encard_isBase_eq` / 定理 `encard_isBase_eq`

English:
theorem encard_isBase_eq
  given: (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂)
  proof: by
  rw [← encard_sdiff_add_encard_inter B₁ B₂]; rw [exch.encard_sdiff_eq hB₁ hB₂]; rw [inter_comm]; rw [encard_sdiff_add_encard_inter]

中文:
定理 encard_isBase_eq
  条件: (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂)
  证明: by
  rw [← encard_sdiff_add_encard_inter B₁ B₂]; rw [exch.encard_sdiff_eq hB₁ hB₂]; rw [inter_comm]; rw [encard_sdiff_add_encard_inter]

Depends on / 依赖: encard_sdiff_add_encard_inter, encard_sdiff_eq, exch.encard_sdiff_eq, inter_comm
-/
theorem encard_isBase_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    B₁.encard = B₂.encard := by
  rw [← encard_sdiff_add_encard_inter B₁ B₂]; rw [exch.encard_sdiff_eq hB₁ hB₂]; rw [inter_comm]; rw [encard_sdiff_add_encard_inter]

end ExchangeProperty

end exchange

section aesop

-- This is necessary as `aesop` uses private lemmas for its proof terms: without this option,
-- the aesop proofs will not work, and any `aesop` auto-params will not fire.
set_option backward.privateInPublic true

/-- The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid.
  It uses a `[Matroid]` ruleset, and is allowed to fail. -/
macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
aesop c* (config := {terminal := true})
  (rule_sets := [$(Lean.mkIdent `Matroid):ident]))

/- We add a number of trivial lemmas (deliberately specialized to statements in terms of the
  ground set of a matroid) to the ruleset `Matroid` for `aesop`. -/

variable {X Y : Set α} {e : α}

@[aesop unsafe 5% (rule_sets := [Matroid])]
/--
theorem `inter_right_subset_ground` / 定理 `inter_right_subset_ground`

English:
theorem inter_right_subset_ground
  given: (hX : X subseteq M.E)
  proof: inter_subset_left.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]

中文:
定理 inter_right_subset_ground
  条件: (hX : X subseteq M.E)
  证明: inter_subset_left.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
-/
private theorem inter_right_subset_ground (hX : X subseteq M.E) :
    X inter Y subseteq M.E := inter_subset_left.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
/--
theorem `inter_left_subset_ground` / 定理 `inter_left_subset_ground`

English:
theorem inter_left_subset_ground
  given: (hX : X subseteq M.E)
  proof: inter_subset_right.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]

中文:
定理 inter_left_subset_ground
  条件: (hX : X subseteq M.E)
  证明: inter_subset_right.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
-/
private theorem inter_left_subset_ground (hX : X subseteq M.E) :
    Y inter X subseteq M.E := inter_subset_right.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
/--
theorem `sdiff_subset_ground` / 定理 `sdiff_subset_ground`

English:
theorem sdiff_subset_ground
  given: (hX : X subseteq M.E)
  statement: X \ Y subseteq M.E
  proof: sdiff_subset.trans hX

@[deprecated (since := "2026-06-03")] alias diff_subset_ground := sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
定理 sdiff_subset_ground
  条件: (hX : X subseteq M.E)
  结论: X \ Y subseteq M.E
  证明: sdiff_subset.trans hX

@[deprecated (since := "2026-06-03")] alias diff_subset_ground := sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
-/
private theorem sdiff_subset_ground (hX : X subseteq M.E) : X \ Y subseteq M.E :=
  sdiff_subset.trans hX

@[deprecated (since := "2026-06-03")] alias diff_subset_ground := sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
theorem `ground_sdiff_subset_ground` / 定理 `ground_sdiff_subset_ground`

English:
theorem ground_sdiff_subset_ground
  statement: M.E \ X subseteq M.E
  proof: sdiff_subset_ground rfl.subset

@[deprecated (since := "2026-06-03")] alias ground_diff_subset_ground := ground_sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
定理 ground_sdiff_subset_ground
  结论: M.E \ X subseteq M.E
  证明: sdiff_subset_ground rfl.subset

@[deprecated (since := "2026-06-03")] alias ground_diff_subset_ground := ground_sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
-/
private theorem ground_sdiff_subset_ground : M.E \ X subseteq M.E :=
  sdiff_subset_ground rfl.subset

@[deprecated (since := "2026-06-03")] alias ground_diff_subset_ground := ground_sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
theorem `singleton_subset_ground` / 定理 `singleton_subset_ground`

English:
theorem singleton_subset_ground
  given: (he : e in M.E)
  statement: {e} subseteq M.E
  proof: singleton_subset_iff.mpr he

@[aesop unsafe 5% (rule_sets := [Matroid])]

中文:
定理 singleton_subset_ground
  条件: (he : e in M.E)
  结论: {e} subseteq M.E
  证明: singleton_subset_iff.mpr he

@[aesop unsafe 5% (rule_sets := [Matroid])]
-/
private theorem singleton_subset_ground (he : e in M.E) : {e} subseteq M.E :=
  singleton_subset_iff.mpr he

@[aesop unsafe 5% (rule_sets := [Matroid])]
/--
theorem `subset_ground_of_subset` / 定理 `subset_ground_of_subset`

English:
theorem subset_ground_of_subset
  given: (hXY : X subseteq Y) (hY : Y subseteq M.E)
  statement: X subseteq M.E
  proof: hXY.trans hY

@[aesop unsafe 5% (rule_sets := [Matroid])]

中文:
定理 subset_ground_of_subset
  条件: (hXY : X subseteq Y) (hY : Y subseteq M.E)
  结论: X subseteq M.E
  证明: hXY.trans hY

@[aesop unsafe 5% (rule_sets := [Matroid])]
-/
private theorem subset_ground_of_subset (hXY : X subseteq Y) (hY : Y subseteq M.E) : X subseteq M.E :=
  hXY.trans hY

@[aesop unsafe 5% (rule_sets := [Matroid])]
/--
theorem `mem_ground_of_mem_of_subset` / 定理 `mem_ground_of_mem_of_subset`

English:
theorem mem_ground_of_mem_of_subset
  given: (hX : X subseteq M.E) (heX : e in X)
  statement: e in M.E
  proof: hX heX

@[aesop safe (rule_sets := [Matroid])]

中文:
定理 mem_ground_of_mem_of_subset
  条件: (hX : X subseteq M.E) (heX : e in X)
  结论: e in M.E
  证明: hX heX

@[aesop safe (rule_sets := [Matroid])]
-/
private theorem mem_ground_of_mem_of_subset (hX : X subseteq M.E) (heX : e in X) : e in M.E :=
  hX heX

@[aesop safe (rule_sets := [Matroid])]
/--
theorem `insert_subset_ground` / 定理 `insert_subset_ground`

English:
theorem insert_subset_ground
  statement: {e : α} {X : Set α} {M : Matroid α}
  proof: insert_subset he hX

@[aesop safe (rule_sets := [Matroid])]

中文:
定理 insert_subset_ground
  结论: {e : α} {X : 集合 α} {M : 拟阵 α}
  证明: insert_subset he hX

@[aesop safe (rule_sets := [Matroid])]
-/
private theorem insert_subset_ground {e : α} {X : Set α} {M : Matroid α}
    (he : e in M.E) (hX : X subseteq M.E) : insert e X subseteq M.E :=
  insert_subset he hX

@[aesop safe (rule_sets := [Matroid])]
/--
theorem `ground_subset_ground` / 定理 `ground_subset_ground`

English:
theorem ground_subset_ground
  given: {M : Matroid α}
  statement: M.E subseteq M.E
  proof: rfl.subset

中文:
定理 ground_subset_ground
  条件: {M : 拟阵 α}
  结论: M.E subseteq M.E
  证明: rfl.subset
-/
private theorem ground_subset_ground {M : Matroid α} : M.E subseteq M.E :=
  rfl.subset

attribute [aesop safe (rule_sets := [Matroid])] empty_subset union_subset iUnion_subset

end aesop

section IsBase

variable {B B₁ B₂ : Set α}

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
theorem `IsBase.subset_ground` / 定理 `IsBase.subset_ground`

English:
theorem IsBase.subset_ground
  given: (hB : M.IsBase B)
  statement: B subseteq M.E
  proof: M.subset_ground B hB

中文:
定理 IsBase.subset_ground
  条件: (hB : M.IsBase B)
  结论: B subseteq M.E
  证明: M.subset_ground B hB

Depends on / 依赖: M.subset_ground, subset_ground
-/
theorem IsBase.subset_ground (hB : M.IsBase B) : B subseteq M.E :=
  M.subset_ground B hB

/--
theorem `IsBase.exchange` / 定理 `IsBase.exchange`

English:
theorem IsBase.exchange
  given: {e : α} (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hx : e in B₁ \ B₂)
  proof: M.isBase_exchange B₁ B₂ hB₁ hB₂ _ hx

中文:
定理 IsBase.exchange
  条件: {e : α} (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hx : e in B₁ \ B₂)
  证明: M.isBase_exchange B₁ B₂ hB₁ hB₂ _ hx

Depends on / 依赖: M.isBase_exchange, isBase_exchange
-/
theorem IsBase.exchange {e : α} (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hx : e in B₁ \ B₂) :
    exists y in B₂ \ B₁, M.IsBase (insert y (B₁ \ {e})) :=
  M.isBase_exchange B₁ B₂ hB₁ hB₂ _ hx

/--
theorem `IsBase.exchange_mem` / 定理 `IsBase.exchange_mem`

English:
theorem IsBase.exchange_mem
  statement: {e : α}
  proof: by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

中文:
定理 IsBase.exchange_mem
  结论: {e : α}
  证明: by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

Depends on / 依赖: exchange
-/
theorem IsBase.exchange_mem {e : α}
    (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hxB₁ : e in B₁) (hxB₂ : e ∉ B₂) :
    exists y, (y in B₂ ∧ y ∉ B₁) ∧ M.IsBase (insert y (B₁ \ {e})) := by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

/--
theorem `IsBase.eq_of_subset_isBase` / 定理 `IsBase.eq_of_subset_isBase`

English:
theorem IsBase.eq_of_subset_isBase
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hB₁B₂ : B₁ subseteq B₂)
  proof: M.isBase_exchange.antichain hB₁ hB₂ hB₁B₂

中文:
定理 IsBase.eq_of_subset_isBase
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hB₁B₂ : B₁ subseteq B₂)
  证明: M.isBase_exchange.antichain hB₁ hB₂ hB₁B₂

Depends on / 依赖: M.isBase_exchange.antichain, antichain, isBase_exchange
-/
theorem IsBase.eq_of_subset_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hB₁B₂ : B₁ subseteq B₂) :
    B₁ = B₂ :=
  M.isBase_exchange.antichain hB₁ hB₂ hB₁B₂

/--
theorem `IsBase.not_isBase_of_ssubset` / 定理 `IsBase.not_isBase_of_ssubset`

English:
theorem IsBase.not_isBase_of_ssubset
  given: {X : Set α} (hB : M.IsBase B) (hX : X ⊂ B)
  statement: ¬ M.IsBase X
  proof: fun h => hX.ne (h.eq_of_subset_isBase hB hX.subset)

中文:
定理 IsBase.not_isBase_of_ssubset
  条件: {X : 集合 α} (hB : M.IsBase B) (hX : X ⊂ B)
  结论: ¬ M.IsBase X
  证明: fun h => hX.ne (h.eq_of_subset_isBase hB hX.subset)

Depends on / 依赖: eq_of_subset_isBase, h.eq_of_subset_isBase, hX.ne, hX.subset, subset
-/
theorem IsBase.not_isBase_of_ssubset {X : Set α} (hB : M.IsBase B) (hX : X ⊂ B) : ¬ M.IsBase X :=
  fun h => hX.ne (h.eq_of_subset_isBase hB hX.subset)

/--
theorem `IsBase.insert_not_isBase` / 定理 `IsBase.insert_not_isBase`

English:
theorem IsBase.insert_not_isBase
  given: {e : α} (hB : M.IsBase B) (heB : e ∉ B)
  proof: fun h => h.not_isBase_of_ssubset (ssubset_insert heB) hB

中文:
定理 IsBase.insert_not_isBase
  条件: {e : α} (hB : M.IsBase B) (heB : e ∉ B)
  证明: fun h => h.not_isBase_of_ssubset (ssubset_insert heB) hB

Depends on / 依赖: h.not_isBase_of_ssubset, not_isBase_of_ssubset, ssubset_insert
-/
theorem IsBase.insert_not_isBase {e : α} (hB : M.IsBase B) (heB : e ∉ B) :
    ¬ M.IsBase (insert e B) :=
  fun h => h.not_isBase_of_ssubset (ssubset_insert heB) hB

/--
theorem `IsBase.encard_sdiff_comm` / 定理 `IsBase.encard_sdiff_comm`

English:
theorem IsBase.encard_sdiff_comm
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  proof: M.isBase_exchange.encard_sdiff_eq hB₁ hB₂

@[deprecated (since := "2026-06-03")] alias IsBase.encard_diff_comm := IsBase.encard_sdiff_comm

中文:
定理 IsBase.encard_sdiff_comm
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  证明: M.isBase_exchange.encard_sdiff_eq hB₁ hB₂

@[deprecated (since := "2026-06-03")] alias IsBase.encard_diff_comm := IsBase.encard_sdiff_comm

Depends on / 依赖: M.isBase_exchange.encard_sdiff_eq, encard_sdiff_eq, isBase_exchange
-/
theorem IsBase.encard_sdiff_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  M.isBase_exchange.encard_sdiff_eq hB₁ hB₂

@[deprecated (since := "2026-06-03")] alias IsBase.encard_diff_comm := IsBase.encard_sdiff_comm

/--
theorem `IsBase.ncard_sdiff_comm` / 定理 `IsBase.ncard_sdiff_comm`

English:
theorem IsBase.ncard_sdiff_comm
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  proof: by
  rw [ncard_def]; rw [hB₁.encard_sdiff_comm hB₂]; rw [← ncard_def]

@[deprecated (since := "2026-06-03")] alias IsBase.ncard_diff_comm := IsBase.ncard_sdiff_comm

中文:
定理 IsBase.ncard_sdiff_comm
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  证明: by
  rw [ncard_def]; rw [hB₁.encard_sdiff_comm hB₂]; rw [← ncard_def]

@[deprecated (since := "2026-06-03")] alias IsBase.ncard_diff_comm := IsBase.ncard_sdiff_comm

Depends on / 依赖: encard_sdiff_comm, ncard_def
-/
theorem IsBase.ncard_sdiff_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [ncard_def]; rw [hB₁.encard_sdiff_comm hB₂]; rw [← ncard_def]

@[deprecated (since := "2026-06-03")] alias IsBase.ncard_diff_comm := IsBase.ncard_sdiff_comm

/--
theorem `IsBase.encard_eq_encard_of_isBase` / 定理 `IsBase.encard_eq_encard_of_isBase`

English:
theorem IsBase.encard_eq_encard_of_isBase
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  proof: by
  rw [M.isBase_exchange.encard_isBase_eq hB₁ hB₂]

中文:
定理 IsBase.encard_eq_encard_of_isBase
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  证明: by
  rw [M.isBase_exchange.encard_isBase_eq hB₁ hB₂]

Depends on / 依赖: M.isBase_exchange.encard_isBase_eq, encard_isBase_eq, isBase_exchange
-/
theorem IsBase.encard_eq_encard_of_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    B₁.encard = B₂.encard := by
  rw [M.isBase_exchange.encard_isBase_eq hB₁ hB₂]

/--
theorem `IsBase.ncard_eq_ncard_of_isBase` / 定理 `IsBase.ncard_eq_ncard_of_isBase`

English:
theorem IsBase.ncard_eq_ncard_of_isBase
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  proof: by
  rw [ncard_def B₁]; rw [hB₁.encard_eq_encard_of_isBase hB₂]; rw [← ncard_def]

中文:
定理 IsBase.ncard_eq_ncard_of_isBase
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  证明: by
  rw [ncard_def B₁]; rw [hB₁.encard_eq_encard_of_isBase hB₂]; rw [← ncard_def]

Depends on / 依赖: encard_eq_encard_of_isBase, ncard_def
-/
theorem IsBase.ncard_eq_ncard_of_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    B₁.ncard = B₂.ncard := by
  rw [ncard_def B₁]; rw [hB₁.encard_eq_encard_of_isBase hB₂]; rw [← ncard_def]

/--
theorem `IsBase.finite_of_finite` / 定理 `IsBase.finite_of_finite`

English:
theorem IsBase.finite_of_finite
  statement: {B' : Set α}
  proof: (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_isBase hB')).mp h

中文:
定理 IsBase.finite_of_finite
  结论: {B' : 集合 α}
  证明: (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_isBase hB')).mp h

Depends on / 依赖: encard_eq_encard_of_isBase, finite_iff_finite_of_encard_eq_encard, hB.encard_eq_encard_of_isBase
-/
theorem IsBase.finite_of_finite {B' : Set α}
    (hB : M.IsBase B) (h : B.Finite) (hB' : M.IsBase B') : B'.Finite :=
  (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_isBase hB')).mp h

/--
theorem `IsBase.infinite_of_infinite` / 定理 `IsBase.infinite_of_infinite`

English:
theorem IsBase.infinite_of_infinite
  given: (hB : M.IsBase B) (h : B.Infinite) (hB₁ : M.IsBase B₁)
  proof: by
  contrapose! h; exact hB₁.finite_of_finite h hB

中文:
定理 IsBase.infinite_of_infinite
  条件: (hB : M.IsBase B) (h : B.无限) (hB₁ : M.IsBase B₁)
  证明: by
  contrapose! h; exact hB₁.finite_of_finite h hB

Depends on / 依赖: contrapose, finite_of_finite
-/
theorem IsBase.infinite_of_infinite (hB : M.IsBase B) (h : B.Infinite) (hB₁ : M.IsBase B₁) :
    B₁.Infinite := by
  contrapose! h; exact hB₁.finite_of_finite h hB

/--
theorem `IsBase.finite` / 定理 `IsBase.finite`

English:
theorem IsBase.finite
  given: [RankFinite M] (hB : M.IsBase B)
  statement: B.Finite
  proof: let ⟨_, hB₀⟩ := ‹RankFinite M›.exists_finite_isBase
  hB₀.1.finite_of_finite hB₀.2 hB

中文:
定理 IsBase.finite
  条件: [RankFinite M] (hB : M.IsBase B)
  结论: B.有限
  证明: let ⟨_, hB₀⟩ := ‹RankFinite M›.exists_finite_isBase
  hB₀.1.finite_of_finite hB₀.2 hB

Depends on / 依赖: RankFinite, exists_finite_isBase, finite_of_finite
-/
theorem IsBase.finite [RankFinite M] (hB : M.IsBase B) : B.Finite :=
  let ⟨_, hB₀⟩ := ‹RankFinite M›.exists_finite_isBase
  hB₀.1.finite_of_finite hB₀.2 hB

/--
theorem `IsBase.infinite` / 定理 `IsBase.infinite`

English:
theorem IsBase.infinite
  given: [RankInfinite M] (hB : M.IsBase B)
  statement: B.Infinite
  proof: let ⟨_, hB₀⟩ := ‹RankInfinite M›.exists_infinite_isBase
  hB₀.1.infinite_of_infinite hB₀.2 hB

中文:
定理 IsBase.infinite
  条件: [RankInfinite M] (hB : M.IsBase B)
  结论: B.无限
  证明: let ⟨_, hB₀⟩ := ‹RankInfinite M›.exists_infinite_isBase
  hB₀.1.infinite_of_infinite hB₀.2 hB

Depends on / 依赖: RankInfinite, exists_infinite_isBase, infinite_of_infinite
-/
theorem IsBase.infinite [RankInfinite M] (hB : M.IsBase B) : B.Infinite :=
  let ⟨_, hB₀⟩ := ‹RankInfinite M›.exists_infinite_isBase
  hB₀.1.infinite_of_infinite hB₀.2 hB

/--
theorem `empty_not_isBase` / 定理 `empty_not_isBase`

English:
theorem empty_not_isBase
  given: [h : RankPos M]
  statement: ¬M.IsBase ∅
  proof: h.empty_not_isBase

中文:
定理 empty_not_isBase
  条件: [h : RankPos M]
  结论: ¬M.IsBase ∅
  证明: h.empty_not_isBase

Depends on / 依赖: empty_not_isBase, h.empty_not_isBase
-/
theorem empty_not_isBase [h : RankPos M] : ¬M.IsBase ∅ :=
  h.empty_not_isBase

/--
theorem `IsBase.nonempty` / 定理 `IsBase.nonempty`

English:
theorem IsBase.nonempty
  given: [RankPos M] (hB : M.IsBase B)
  statement: B.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact M.empty_not_isBase hB

中文:
定理 IsBase.nonempty
  条件: [RankPos M] (hB : M.IsBase B)
  结论: B.非空
  证明: by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact M.empty_not_isBase hB

Depends on / 依赖: M.empty_not_isBase, empty_not_isBase, nonempty_iff_ne_empty
-/
theorem IsBase.nonempty [RankPos M] (hB : M.IsBase B) : B.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact M.empty_not_isBase hB

/--
theorem `IsBase.rankPos_of_nonempty` / 定理 `IsBase.rankPos_of_nonempty`

English:
theorem IsBase.rankPos_of_nonempty
  given: (hB : M.IsBase B) (h : B.Nonempty)
  statement: M.RankPos
  proof: by
  rw [rankPos_iff]
  intro he
  obtain rfl := he.eq_of_subset_isBase hB (empty_subset B)
  simp at h

中文:
定理 IsBase.rankPos_of_nonempty
  条件: (hB : M.IsBase B) (h : B.非空)
  结论: M.RankPos
  证明: by
  rw [rankPos_iff]
  intro he
  obtain rfl := he.eq_of_subset_isBase hB (empty_subset B)
  simp at h

Depends on / 依赖: empty_subset, eq_of_subset_isBase, he.eq_of_subset_isBase, rankPos_iff
-/
theorem IsBase.rankPos_of_nonempty (hB : M.IsBase B) (h : B.Nonempty) : M.RankPos := by
  rw [rankPos_iff]
  intro he
  obtain rfl := he.eq_of_subset_isBase hB (empty_subset B)
  simp at h

/--
theorem `IsBase.rankFinite_of_finite` / 定理 `IsBase.rankFinite_of_finite`

English:
theorem IsBase.rankFinite_of_finite
  given: (hB : M.IsBase B) (hfin : B.Finite)
  statement: RankFinite M
  proof: ⟨⟨B, hB, hfin⟩⟩

中文:
定理 IsBase.rankFinite_of_finite
  条件: (hB : M.IsBase B) (hfin : B.有限)
  结论: RankFinite M
  证明: ⟨⟨B, hB, hfin⟩⟩
-/
theorem IsBase.rankFinite_of_finite (hB : M.IsBase B) (hfin : B.Finite) : RankFinite M :=
  ⟨⟨B, hB, hfin⟩⟩

/--
theorem `IsBase.rankInfinite_of_infinite` / 定理 `IsBase.rankInfinite_of_infinite`

English:
theorem IsBase.rankInfinite_of_infinite
  given: (hB : M.IsBase B) (h : B.Infinite)
  statement: RankInfinite M
  proof: ⟨⟨B, hB, h⟩⟩

中文:
定理 IsBase.rankInfinite_of_infinite
  条件: (hB : M.IsBase B) (h : B.无限)
  结论: RankInfinite M
  证明: ⟨⟨B, hB, h⟩⟩
-/
theorem IsBase.rankInfinite_of_infinite (hB : M.IsBase B) (h : B.Infinite) : RankInfinite M :=
  ⟨⟨B, hB, h⟩⟩

/--
theorem `not_rankFinite` / 定理 `not_rankFinite`

English:
theorem not_rankFinite
  given: (M : Matroid α) [RankInfinite M]
  statement: ¬ RankFinite M
  proof: by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

中文:
定理 not_rankFinite
  条件: (M : 拟阵 α) [RankInfinite M]
  结论: ¬ RankFinite M
  证明: by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

Depends on / 依赖: M.exists_isBase, exists_isBase, finite, hB.finite, hB.infinite, infinite
-/
theorem not_rankFinite (M : Matroid α) [RankInfinite M] : ¬ RankFinite M := by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

/--
theorem `not_rankInfinite` / 定理 `not_rankInfinite`

English:
theorem not_rankInfinite
  given: (M : Matroid α) [RankFinite M]
  statement: ¬ RankInfinite M
  proof: by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

中文:
定理 not_rankInfinite
  条件: (M : 拟阵 α) [RankFinite M]
  结论: ¬ RankInfinite M
  证明: by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

Depends on / 依赖: M.exists_isBase, exists_isBase, finite, hB.finite, hB.infinite, infinite
-/
theorem not_rankInfinite (M : Matroid α) [RankFinite M] : ¬ RankInfinite M := by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

/--
theorem `rankFinite_or_rankInfinite` / 定理 `rankFinite_or_rankInfinite`

English:
theorem rankFinite_or_rankInfinite
  given: (M : Matroid α)
  statement: RankFinite M ∨ RankInfinite M
  proof: let ⟨B, hB⟩ := M.exists_isBase
  B.finite_or_infinite.imp hB.rankFinite_of_finite hB.rankInfinite_of_infinite

@[simp]

中文:
定理 rankFinite_or_rankInfinite
  条件: (M : 拟阵 α)
  结论: RankFinite M ∨ RankInfinite M
  证明: let ⟨B, hB⟩ := M.exists_isBase
  B.finite_or_infinite.imp hB.rankFinite_of_finite hB.rankInfinite_of_infinite

@[simp]

Depends on / 依赖: B.finite_or_infinite.imp, M.exists_isBase, exists_isBase, finite_or_infinite, hB.rankFinite_of_finite, hB.rankInfinite_of_infinite, rankFinite_of_finite, rankInfinite_of_infinite
-/
theorem rankFinite_or_rankInfinite (M : Matroid α) : RankFinite M ∨ RankInfinite M :=
  let ⟨B, hB⟩ := M.exists_isBase
  B.finite_or_infinite.imp hB.rankFinite_of_finite hB.rankInfinite_of_infinite

@[simp]
/--
theorem `not_rankFinite_iff` / 定理 `not_rankFinite_iff`

English:
theorem not_rankFinite_iff
  given: (M : Matroid α)
  statement: ¬ RankFinite M ↔ RankInfinite M
  proof: M.rankFinite_or_rankInfinite.elim (fun h => iff_of_false (by simpa) M.not_rankInfinite)
    fun h => iff_of_true M.not_rankFinite h

@[simp]

中文:
定理 not_rankFinite_iff
  条件: (M : 拟阵 α)
  结论: ¬ RankFinite M ↔ RankInfinite M
  证明: M.rankFinite_or_rankInfinite.elim (fun h => iff_of_false (by simpa) M.not_rankInfinite)
    fun h => iff_of_true M.not_rankFinite h

@[simp]

Depends on / 依赖: M.not_rankFinite, M.not_rankInfinite, M.rankFinite_or_rankInfinite.elim, iff_of_false, iff_of_true, not_rankFinite, not_rankInfinite, rankFinite_or_rankInfinite
-/
theorem not_rankFinite_iff (M : Matroid α) : ¬ RankFinite M ↔ RankInfinite M :=
  M.rankFinite_or_rankInfinite.elim (fun h => iff_of_false (by simpa) M.not_rankInfinite)
    fun h => iff_of_true M.not_rankFinite h

@[simp]
/--
theorem `not_rankInfinite_iff` / 定理 `not_rankInfinite_iff`

English:
theorem not_rankInfinite_iff
  given: (M : Matroid α)
  statement: ¬ RankInfinite M ↔ RankFinite M
  proof: by
  rw [← not_rankFinite_iff]; rw [not_not]

中文:
定理 not_rankInfinite_iff
  条件: (M : 拟阵 α)
  结论: ¬ RankInfinite M ↔ RankFinite M
  证明: by
  rw [← not_rankFinite_iff]; rw [not_not]

Depends on / 依赖: not_not, not_rankFinite_iff
-/
theorem not_rankInfinite_iff (M : Matroid α) : ¬ RankInfinite M ↔ RankFinite M := by
  rw [← not_rankFinite_iff]; rw [not_not]

/--
theorem `IsBase.sdiff_finite_comm` / 定理 `IsBase.sdiff_finite_comm`

English:
theorem IsBase.sdiff_finite_comm
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  proof: finite_iff_finite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_finite_comm := IsBase.sdiff_finite_comm

中文:
定理 IsBase.sdiff_finite_comm
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  证明: finite_iff_finite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_finite_comm := IsBase.sdiff_finite_comm

Depends on / 依赖: encard_sdiff_comm, finite_iff_finite_of_encard_eq_encard
-/
theorem IsBase.sdiff_finite_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite :=
  finite_iff_finite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_finite_comm := IsBase.sdiff_finite_comm

/--
theorem `IsBase.sdiff_infinite_comm` / 定理 `IsBase.sdiff_infinite_comm`

English:
theorem IsBase.sdiff_infinite_comm
  given: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  proof: infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_infinite_comm := IsBase.sdiff_infinite_comm

中文:
定理 IsBase.sdiff_infinite_comm
  条件: (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
  证明: infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_infinite_comm := IsBase.sdiff_infinite_comm

Depends on / 依赖: encard_sdiff_comm, infinite_iff_infinite_of_encard_eq_encard
-/
theorem IsBase.sdiff_infinite_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite :=
  infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_infinite_comm := IsBase.sdiff_infinite_comm

/--
theorem `ext_isBase` / 定理 `ext_isBase`

English:
theorem ext_isBase
  statement: {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
  proof: by
  have h' : forall B, M₁.IsBase B ↔ M₂.IsBase B :=
    fun B => ⟨fun hB => (h hB.subset_ground).1 hB,
      fun hB => (h <| hB.subset_ground.trans_eq hE.symm).2 hB⟩
  ext <;> simp [hE, M₁.indep_iff', M₂.indep_iff', h']

中文:
定理 ext_isBase
  结论: {M₁ M₂ : 拟阵 α} (hE : M₁.E = M₂.E)
  证明: by
  have h' : forall B, M₁.IsBase B ↔ M₂.IsBase B :=
    fun B => ⟨fun hB => (h hB.subset_ground).1 hB,
      fun hB => (h <| hB.subset_ground.trans_eq hE.symm).2 hB⟩
  ext <;> simp [hE, M₁.indep_iff', M₂.indep_iff', h']

Depends on / 依赖: IsBase, hB.subset_ground, hB.subset_ground.trans_eq, hE.symm, indep_iff, subset_ground, trans_eq
-/
theorem ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂ := by
  have h' : forall B, M₁.IsBase B ↔ M₂.IsBase B :=
    fun B => ⟨fun hB => (h hB.subset_ground).1 hB,
      fun hB => (h <| hB.subset_ground.trans_eq hE.symm).2 hB⟩
  ext <;> simp [hE, M₁.indep_iff', M₂.indep_iff', h']

/--
theorem `ext_iff_isBase` / 定理 `ext_iff_isBase`

English:
theorem ext_iff_isBase
  given: {M₁ M₂ : Matroid α}
  proof: ⟨fun h => by simp [h], fun ⟨hE, h⟩ => ext_isBase hE h⟩

中文:
定理 ext_iff_isBase
  条件: {M₁ M₂ : 拟阵 α}
  证明: ⟨fun h => by simp [h], fun ⟨hE, h⟩ => ext_isBase hE h⟩

Depends on / 依赖: ext_isBase
-/
theorem ext_iff_isBase {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B) :=
  ⟨fun h => by simp [h], fun ⟨hE, h⟩ => ext_isBase hE h⟩

/--
theorem `isBase_compl_iff_maximal_disjoint_isBase` / 定理 `isBase_compl_iff_maximal_disjoint_isBase`

English:
theorem isBase_compl_iff_maximal_disjoint_isBase
  given: (hB : B subseteq M.E := by aesop_mat)
  proof: by
  simp_rw [maximal_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine ⟨fun h => ⟨⟨_, h, disjoint_sdiff_right⟩,
    fun I hI B' ⟨hB', hIB'⟩ hBI => hBI.antisymm ?_⟩, fun ⟨⟨B', hB', hBB'⟩,h⟩ => ?_⟩
  · rw [hB'.eq_of_subset_isBase h, ← subset_compl_iff_disjoint_right, sdiff_eq, compl_inter,
      compl_compl] at hIB'
    · exact fun e he => (hIB' he).elim (fun h' => (h' (hI he)).elim) id
    rw [subset_sdiff]; rw [and_iff_right hB'.subset_ground]; rw [disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h sdiff_subset B' ⟨hB']; rw [disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_sdiff, hB, hBB']

中文:
定理 isBase_compl_iff_maximal_disjoint_isBase
  条件: (hB : B subseteq M.E := by aesop_mat)
  证明: by
  simp_rw [maximal_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine ⟨fun h => ⟨⟨_, h, disjoint_sdiff_right⟩,
    fun I hI B' ⟨hB', hIB'⟩ hBI => hBI.antisymm ?_⟩, fun ⟨⟨B', hB', hBB'⟩,h⟩ => ?_⟩
  · rw [hB'.eq_of_subset_isBase h, ← subset_compl_iff_disjoint_right, sdiff_eq, compl_inter,
      compl_compl] at hIB'
    · exact fun e he => (hIB' he).elim (fun h' => (h' (hI he)).elim) id
    rw [subset_sdiff]; rw [and_iff_right hB'.subset_ground]; rw [disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h sdiff_subset B' ⟨hB']; rw [disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_sdiff, hB, hBB']

Depends on / 依赖: Disjoint, IsBase, M.IsBase, Maximal, aesop_mat, and_iff_right, and_imp, antisymm, compl_compl, compl_inter, disjoint_sdiff_right, eq_of_subset_isBase, forall_exists_index, hBI.antisymm, maximal_iff, sdiff_eq, simp_rw, subset_compl_iff_disjoint_right, subseteq
-/
theorem isBase_compl_iff_maximal_disjoint_isBase (hB : B subseteq M.E := by aesop_mat) :
    M.IsBase (M.E \ B) ↔ Maximal (fun I => I subseteq M.E ∧ exists B, M.IsBase B ∧ Disjoint I B) B := by
  simp_rw [maximal_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine ⟨fun h => ⟨⟨_, h, disjoint_sdiff_right⟩,
    fun I hI B' ⟨hB', hIB'⟩ hBI => hBI.antisymm ?_⟩, fun ⟨⟨B', hB', hBB'⟩,h⟩ => ?_⟩
  · rw [hB'.eq_of_subset_isBase h, ← subset_compl_iff_disjoint_right, sdiff_eq, compl_inter,
      compl_compl] at hIB'
    · exact fun e he => (hIB' he).elim (fun h' => (h' (hI he)).elim) id
    rw [subset_sdiff]; rw [and_iff_right hB'.subset_ground]; rw [disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h sdiff_subset B' ⟨hB']; rw [disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_sdiff, hB, hBB']

end IsBase
section dep_indep

/--
Definition of `Dep` / `Dep` 的定义

English:
definition Dep
  signature: (M : Matroid α) (D : Set α)
  body: ¬M.Indep D ∧ D subseteq M.E

中文:
定义 Dep
  签名: (M : 拟阵 α) (D : 集合 α)
  定义体: ¬M.Indep D ∧ D subseteq M.E

Depends on / 依赖: M.Indep, subseteq
-/
def Dep (M : Matroid α) (D : Set α) : Prop := ¬M.Indep D ∧ D subseteq M.E

variable {B B' I J D X : Set α} {e f : α}

/--
theorem `indep_iff` / 定理 `indep_iff`

English:
theorem indep_iff
  statement: M.Indep I ↔ exists B, M.IsBase B ∧ I subseteq B
  proof: M.indep_iff' (I := I)

中文:
定理 indep_iff
  结论: M.Indep I ↔ 存在 B, M.IsBase B ∧ I subseteq B
  证明: M.indep_iff' (I := I)

Depends on / 依赖: M.indep_iff, indep_iff
-/
theorem indep_iff : M.Indep I ↔ exists B, M.IsBase B ∧ I subseteq B :=
  M.indep_iff' (I := I)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `setOfPred_indep_eq` / 定理 `setOfPred_indep_eq`

English:
theorem setOfPred_indep_eq
  given: (M : Matroid α)
  statement: {I | M.Indep I} = lowerClosure ({B | M.IsBase B})
  proof: by
  simp_rw [indep_iff, lowerClosure, LowerSet.coe_mk, mem_ofPred]

@[deprecated (since := "2026-07-09")]
alias setOf_indep_eq := setOfPred_indep_eq

中文:
定理 setOfPred_indep_eq
  条件: (M : 拟阵 α)
  结论: {I | M.Indep I} = lowerClosure ({B | M.IsBase B})
  证明: by
  simp_rw [indep_iff, lowerClosure, LowerSet.coe_mk, mem_ofPred]

@[deprecated (since := "2026-07-09")]
alias setOf_indep_eq := setOfPred_indep_eq

Depends on / 依赖: LowerSet, LowerSet.coe_mk, coe_mk, indep_iff, lowerClosure, mem_ofPred, simp_rw
-/
theorem setOfPred_indep_eq (M : Matroid α) : {I | M.Indep I} = lowerClosure ({B | M.IsBase B}) := by
  simp_rw [indep_iff, lowerClosure, LowerSet.coe_mk, mem_ofPred]

@[deprecated (since := "2026-07-09")]
alias setOf_indep_eq := setOfPred_indep_eq

/--
theorem `Indep.exists_isBase_superset` / 定理 `Indep.exists_isBase_superset`

English:
theorem Indep.exists_isBase_superset
  given: (hI : M.Indep I)
  statement: exists B, M.IsBase B ∧ I subseteq B
  proof: indep_iff.1 hI

中文:
定理 Indep.存在_isBase_superset
  条件: (hI : M.Indep I)
  结论: 存在 B, M.IsBase B ∧ I subseteq B
  证明: indep_iff.1 hI

Depends on / 依赖: indep_iff
-/
theorem Indep.exists_isBase_superset (hI : M.Indep I) : exists B, M.IsBase B ∧ I subseteq B :=
  indep_iff.1 hI

/--
theorem `dep_iff` / 定理 `dep_iff`

English:
theorem dep_iff
  statement: M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
  proof: Iff.rfl

中文:
定理 dep_iff
  结论: M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E := Iff.rfl

/--
theorem `setOfPred_dep_eq` / 定理 `setOfPred_dep_eq`

English:
theorem setOfPred_dep_eq
  given: (M : Matroid α)
  statement: {D | M.Dep D} = {I | M.Indep I}ᶜ inter Iic M.E
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias setOf_dep_eq := setOfPred_dep_eq

@[aesop unsafe 30% (rule_sets := [Matroid])]

中文:
定理 setOfPred_dep_eq
  条件: (M : 拟阵 α)
  结论: {D | M.Dep D} = {I | M.Indep I}ᶜ inter 左无界右闭区间 M.E
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias setOf_dep_eq := setOfPred_dep_eq

@[aesop unsafe 30% (rule_sets := [Matroid])]
-/
theorem setOfPred_dep_eq (M : Matroid α) : {D | M.Dep D} = {I | M.Indep I}ᶜ inter Iic M.E := rfl

@[deprecated (since := "2026-07-09")]
alias setOf_dep_eq := setOfPred_dep_eq

@[aesop unsafe 30% (rule_sets := [Matroid])]
/--
theorem `Indep.subset_ground` / 定理 `Indep.subset_ground`

English:
theorem Indep.subset_ground
  given: (hI : M.Indep I)
  statement: I subseteq M.E
  proof: by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hIB.trans hB.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]

中文:
定理 Indep.subset_ground
  条件: (hI : M.Indep I)
  结论: I subseteq M.E
  证明: by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hIB.trans hB.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]

Depends on / 依赖: exists_isBase_superset, hB.subset_ground, hI.exists_isBase_superset, hIB.trans, subset_ground
-/
theorem Indep.subset_ground (hI : M.Indep I) : I subseteq M.E := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hIB.trans hB.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
/--
theorem `Dep.subset_ground` / 定理 `Dep.subset_ground`

English:
theorem Dep.subset_ground
  given: (hD : M.Dep D)
  statement: D subseteq M.E
  proof: hD.2

中文:
定理 Dep.subset_ground
  条件: (hD : M.Dep D)
  结论: D subseteq M.E
  证明: hD.2
-/
theorem Dep.subset_ground (hD : M.Dep D) : D subseteq M.E :=
  hD.2

/--
theorem `indep_or_dep` / 定理 `indep_or_dep`

English:
theorem indep_or_dep
  given: (hX : X subseteq M.E := by aesop_mat)
  statement: M.Indep X ∨ M.Dep X
  proof: by
  rw [Dep]; rw [and_iff_left hX]
  apply em

中文:
定理 indep_or_dep
  条件: (hX : X subseteq M.E := by aesop_mat)
  结论: M.Indep X ∨ M.Dep X
  证明: by
  rw [Dep]; rw [and_iff_left hX]
  apply em

Depends on / 依赖: M.Dep, M.Indep, aesop_mat, and_iff_left
-/
theorem indep_or_dep (hX : X subseteq M.E := by aesop_mat) : M.Indep X ∨ M.Dep X := by
  rw [Dep]; rw [and_iff_left hX]
  apply em

/--
theorem `Indep.not_dep` / 定理 `Indep.not_dep`

English:
theorem Indep.not_dep
  given: (hI : M.Indep I)
  statement: ¬ M.Dep I
  proof: fun h => h.1 hI

中文:
定理 Indep.not_dep
  条件: (hI : M.Indep I)
  结论: ¬ M.Dep I
  证明: fun h => h.1 hI
-/
theorem Indep.not_dep (hI : M.Indep I) : ¬ M.Dep I :=
  fun h => h.1 hI

/--
theorem `Dep.not_indep` / 定理 `Dep.not_indep`

English:
theorem Dep.not_indep
  given: (hD : M.Dep D)
  statement: ¬ M.Indep D
  proof: hD.1

中文:
定理 Dep.not_indep
  条件: (hD : M.Dep D)
  结论: ¬ M.Indep D
  证明: hD.1
-/
theorem Dep.not_indep (hD : M.Dep D) : ¬ M.Indep D :=
  hD.1

/--
theorem `dep_of_not_indep` / 定理 `dep_of_not_indep`

English:
theorem dep_of_not_indep
  given: (hD : ¬ M.Indep D) (hDE : D subseteq M.E := by aesop_mat)
  statement: M.Dep D
  proof: ⟨hD, hDE⟩

中文:
定理 dep_of_not_indep
  条件: (hD : ¬ M.Indep D) (hDE : D subseteq M.E := by aesop_mat)
  结论: M.Dep D
  证明: ⟨hD, hDE⟩

Depends on / 依赖: M.Dep, aesop_mat
-/
theorem dep_of_not_indep (hD : ¬ M.Indep D) (hDE : D subseteq M.E := by aesop_mat) : M.Dep D :=
  ⟨hD, hDE⟩

/--
theorem `indep_of_not_dep` / 定理 `indep_of_not_dep`

English:
theorem indep_of_not_dep
  given: (hI : ¬ M.Dep I) (hIE : I subseteq M.E := by aesop_mat)
  statement: M.Indep I
  proof: by_contra (fun h => hI ⟨h, hIE⟩)

中文:
定理 indep_of_not_dep
  条件: (hI : ¬ M.Dep I) (hIE : I subseteq M.E := by aesop_mat)
  结论: M.Indep I
  证明: by_contra (fun h => hI ⟨h, hIE⟩)

Depends on / 依赖: M.Indep, aesop_mat
-/
theorem indep_of_not_dep (hI : ¬ M.Dep I) (hIE : I subseteq M.E := by aesop_mat) : M.Indep I :=
  by_contra (fun h => hI ⟨h, hIE⟩)

/--
theorem `not_dep_iff` / 定理 `not_dep_iff`

English:
theorem not_dep_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  statement: ¬ M.Dep X ↔ M.Indep X
  proof: by
  rw [Dep]; rw [and_iff_left hX]; rw [not_not]

中文:
定理 not_dep_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  结论: ¬ M.Dep X ↔ M.Indep X
  证明: by
  rw [Dep]; rw [and_iff_left hX]; rw [not_not]
-/
@[simp] theorem not_dep_iff (hX : X subseteq M.E := by aesop_mat) : ¬ M.Dep X ↔ M.Indep X := by
  rw [Dep]; rw [and_iff_left hX]; rw [not_not]

/--
theorem `not_indep_iff` / 定理 `not_indep_iff`

English:
theorem not_indep_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  statement: ¬ M.Indep X ↔ M.Dep X
  proof: by
  rw [Dep]; rw [and_iff_left hX]

中文:
定理 not_indep_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  结论: ¬ M.Indep X ↔ M.Dep X
  证明: by
  rw [Dep]; rw [and_iff_left hX]
-/
@[simp] theorem not_indep_iff (hX : X subseteq M.E := by aesop_mat) : ¬ M.Indep X ↔ M.Dep X := by
  rw [Dep]; rw [and_iff_left hX]

/--
theorem `indep_iff_not_dep` / 定理 `indep_iff_not_dep`

English:
theorem indep_iff_not_dep
  statement: M.Indep I ↔ ¬M.Dep I ∧ I subseteq M.E
  proof: by
  rw [dep_iff]; rw [not_and]; rw [not_imp_not]
  exact ⟨fun h => ⟨fun _ => h, h.subset_ground⟩, fun h => h.1 h.2⟩

中文:
定理 indep_iff_not_dep
  结论: M.Indep I ↔ ¬M.Dep I ∧ I subseteq M.E
  证明: by
  rw [dep_iff]; rw [not_and]; rw [not_imp_not]
  exact ⟨fun h => ⟨fun _ => h, h.subset_ground⟩, fun h => h.1 h.2⟩

Depends on / 依赖: dep_iff, h.subset_ground, not_and, not_imp_not, subset_ground
-/
theorem indep_iff_not_dep : M.Indep I ↔ ¬M.Dep I ∧ I subseteq M.E := by
  rw [dep_iff]; rw [not_and]; rw [not_imp_not]
  exact ⟨fun h => ⟨fun _ => h, h.subset_ground⟩, fun h => h.1 h.2⟩

/--
theorem `Indep.subset` / 定理 `Indep.subset`

English:
theorem Indep.subset
  given: (hJ : M.Indep J) (hIJ : I subseteq J)
  statement: M.Indep I
  proof: by
  obtain ⟨B, hB, hJB⟩ := hJ.exists_isBase_superset
  exact indep_iff.2 ⟨B, hB, hIJ.trans hJB⟩

中文:
定理 Indep.subset
  条件: (hJ : M.Indep J) (hIJ : I subseteq J)
  结论: M.Indep I
  证明: by
  obtain ⟨B, hB, hJB⟩ := hJ.exists_isBase_superset
  exact indep_iff.2 ⟨B, hB, hIJ.trans hJB⟩

Depends on / 依赖: exists_isBase_superset, hIJ.trans, hJ.exists_isBase_superset, indep_iff
-/
theorem Indep.subset (hJ : M.Indep J) (hIJ : I subseteq J) : M.Indep I := by
  obtain ⟨B, hB, hJB⟩ := hJ.exists_isBase_superset
  exact indep_iff.2 ⟨B, hB, hIJ.trans hJB⟩

/--
theorem `Dep.superset` / 定理 `Dep.superset`

English:
theorem Dep.superset
  given: (hD : M.Dep D) (hDX : D subseteq X) (hXE : X subseteq M.E := by aesop_mat)
  statement: M.Dep X
  proof: dep_of_not_indep (fun hI => (hI.subset hDX).not_dep hD)

中文:
定理 Dep.superset
  条件: (hD : M.Dep D) (hDX : D subseteq X) (hXE : X subseteq M.E := by aesop_mat)
  结论: M.Dep X
  证明: dep_of_not_indep (fun hI => (hI.subset hDX).not_dep hD)

Depends on / 依赖: M.Dep, aesop_mat, decidable_of_iff, dep_of_not_indep, hI.subset, lookup_isSome, not_dep, subset
-/
theorem Dep.superset (hD : M.Dep D) (hDX : D subseteq X) (hXE : X subseteq M.E := by aesop_mat) : M.Dep X :=
  dep_of_not_indep (fun hI => (hI.subset hDX).not_dep hD)

/--
theorem `IsBase.indep` / 定理 `IsBase.indep`

English:
theorem IsBase.indep
  given: (hB : M.IsBase B)
  statement: M.Indep B
  proof: indep_iff.2 ⟨B, hB, subset_rfl⟩

中文:
定理 IsBase.indep
  条件: (hB : M.IsBase B)
  结论: M.Indep B
  证明: indep_iff.2 ⟨B, hB, subset_rfl⟩

Depends on / 依赖: indep_iff, subset_rfl
-/
theorem IsBase.indep (hB : M.IsBase B) : M.Indep B :=
  indep_iff.2 ⟨B, hB, subset_rfl⟩

/--
theorem `empty_indep` / 定理 `empty_indep`

English:
theorem empty_indep
  given: (M : Matroid α)
  statement: M.Indep ∅
  proof: Exists.elim M.exists_isBase (fun _ hB => hB.indep.subset (empty_subset _))

中文:
定理 empty_indep
  条件: (M : 拟阵 α)
  结论: M.Indep ∅
  证明: Exists.elim M.exists_isBase (fun _ hB => hB.indep.subset (empty_subset _))
-/
@[simp] theorem empty_indep (M : Matroid α) : M.Indep ∅ :=
  Exists.elim M.exists_isBase (fun _ hB => hB.indep.subset (empty_subset _))

/--
theorem `Dep.nonempty` / 定理 `Dep.nonempty`

English:
theorem Dep.nonempty
  given: (hD : M.Dep D)
  statement: D.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep

中文:
定理 Dep.nonempty
  条件: (hD : M.Dep D)
  结论: D.非空
  证明: by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep

Depends on / 依赖: M.empty_indep, empty_indep, hD.not_indep, nonempty_iff_ne_empty, not_indep
-/
theorem Dep.nonempty (hD : M.Dep D) : D.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep

/--
theorem `Indep.finite` / 定理 `Indep.finite`

English:
theorem Indep.finite
  given: [RankFinite M] (hI : M.Indep I)
  statement: I.Finite
  proof: let ⟨_, hB, hIB⟩ := hI.exists_isBase_superset
  hB.finite.subset hIB

中文:
定理 Indep.finite
  条件: [RankFinite M] (hI : M.Indep I)
  结论: I.有限
  证明: let ⟨_, hB, hIB⟩ := hI.exists_isBase_superset
  hB.finite.subset hIB

Depends on / 依赖: exists_isBase_superset, finite, hB.finite.subset, hI.exists_isBase_superset, subset
-/
theorem Indep.finite [RankFinite M] (hI : M.Indep I) : I.Finite :=
  let ⟨_, hB, hIB⟩ := hI.exists_isBase_superset
  hB.finite.subset hIB

/--
theorem `Indep.rankPos_of_nonempty` / 定理 `Indep.rankPos_of_nonempty`

English:
theorem Indep.rankPos_of_nonempty
  given: (hI : M.Indep I) (hne : I.Nonempty)
  statement: M.RankPos
  proof: by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hB.rankPos_of_nonempty (hne.mono hIB)

中文:
定理 Indep.rankPos_of_nonempty
  条件: (hI : M.Indep I) (hne : I.非空)
  结论: M.RankPos
  证明: by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hB.rankPos_of_nonempty (hne.mono hIB)

Depends on / 依赖: exists_isBase_superset, hB.rankPos_of_nonempty, hI.exists_isBase_superset, hne.mono, rankPos_of_nonempty
-/
theorem Indep.rankPos_of_nonempty (hI : M.Indep I) (hne : I.Nonempty) : M.RankPos := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hB.rankPos_of_nonempty (hne.mono hIB)

/--
theorem `Indep.inter_right` / 定理 `Indep.inter_right`

English:
theorem Indep.inter_right
  given: (hI : M.Indep I) (X : Set α)
  statement: M.Indep (I inter X)
  proof: hI.subset inter_subset_left

中文:
定理 Indep.inter_right
  条件: (hI : M.Indep I) (X : 集合 α)
  结论: M.Indep (I inter X)
  证明: hI.subset inter_subset_left

Depends on / 依赖: hI.subset, inter_subset_left, subset
-/
theorem Indep.inter_right (hI : M.Indep I) (X : Set α) : M.Indep (I inter X) :=
  hI.subset inter_subset_left

/--
theorem `Indep.inter_left` / 定理 `Indep.inter_left`

English:
theorem Indep.inter_left
  given: (hI : M.Indep I) (X : Set α)
  statement: M.Indep (X inter I)
  proof: hI.subset inter_subset_right

中文:
定理 Indep.inter_left
  条件: (hI : M.Indep I) (X : 集合 α)
  结论: M.Indep (X inter I)
  证明: hI.subset inter_subset_right

Depends on / 依赖: hI.subset, inter_subset_right, subset
-/
theorem Indep.inter_left (hI : M.Indep I) (X : Set α) : M.Indep (X inter I) :=
  hI.subset inter_subset_right

/--
theorem `Indep.sdiff` / 定理 `Indep.sdiff`

English:
theorem Indep.sdiff
  given: (hI : M.Indep I) (X : Set α)
  statement: M.Indep (I \ X)
  proof: hI.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Indep.diff := Indep.sdiff

中文:
定理 Indep.sdiff
  条件: (hI : M.Indep I) (X : 集合 α)
  结论: M.Indep (I \ X)
  证明: hI.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Indep.diff := Indep.sdiff

Depends on / 依赖: hI.subset, sdiff_subset, subset
-/
theorem Indep.sdiff (hI : M.Indep I) (X : Set α) : M.Indep (I \ X) :=
  hI.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Indep.diff := Indep.sdiff

/--
theorem `IsBase.eq_of_subset_indep` / 定理 `IsBase.eq_of_subset_indep`

English:
theorem IsBase.eq_of_subset_indep
  given: (hB : M.IsBase B) (hI : M.Indep I) (hBI : B subseteq I)
  statement: B = I
  proof: let ⟨B', hB', hB'I⟩ := hI.exists_isBase_superset
  hBI.antisymm (by rwa [hB.eq_of_subset_isBase hB' (hBI.trans hB'I)])

中文:
定理 IsBase.eq_of_subset_indep
  条件: (hB : M.IsBase B) (hI : M.Indep I) (hBI : B subseteq I)
  结论: B = I
  证明: let ⟨B', hB', hB'I⟩ := hI.exists_isBase_superset
  hBI.antisymm (by rwa [hB.eq_of_subset_isBase hB' (hBI.trans hB'I)])

Depends on / 依赖: antisymm, eq_of_subset_isBase, exists_isBase_superset, hB.eq_of_subset_isBase, hBI.antisymm, hBI.trans, hI.exists_isBase_superset
-/
theorem IsBase.eq_of_subset_indep (hB : M.IsBase B) (hI : M.Indep I) (hBI : B subseteq I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI.exists_isBase_superset
  hBI.antisymm (by rwa [hB.eq_of_subset_isBase hB' (hBI.trans hB'I)])

/--
theorem `isBase_iff_maximal_indep` / 定理 `isBase_iff_maximal_indep`

English:
theorem isBase_iff_maximal_indep
  statement: M.IsBase B ↔ Maximal M.Indep B
  proof: by
  rw [maximal_subset_iff]
  refine ⟨fun h => ⟨h.indep, fun _ => h.eq_of_subset_indep⟩, fun ⟨h, h'⟩ => ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_superset
  rwa [h' hB'.indep hBB']

中文:
定理 isBase_iff_maximal_indep
  结论: M.IsBase B ↔ 极大 M.Indep B
  证明: by
  rw [maximal_subset_iff]
  refine ⟨fun h => ⟨h.indep, fun _ => h.eq_of_subset_indep⟩, fun ⟨h, h'⟩ => ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_superset
  rwa [h' hB'.indep hBB']

Depends on / 依赖: eq_of_subset_indep, exists_isBase_superset, h.eq_of_subset_indep, h.exists_isBase_superset, h.indep, maximal_subset_iff
-/
theorem isBase_iff_maximal_indep : M.IsBase B ↔ Maximal M.Indep B := by
  rw [maximal_subset_iff]
  refine ⟨fun h => ⟨h.indep, fun _ => h.eq_of_subset_indep⟩, fun ⟨h, h'⟩ => ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_superset
  rwa [h' hB'.indep hBB']

/--
theorem `Indep.isBase_of_maximal` / 定理 `Indep.isBase_of_maximal`

English:
theorem Indep.isBase_of_maximal
  given: (hI : M.Indep I) (h : forall ⦃J⦄, M.Indep J -> I subseteq J -> I = J)
  proof: by
  rwa [isBase_iff_maximal_indep, maximal_subset_iff, and_iff_right hI]

中文:
定理 Indep.isBase_of_maximal
  条件: (hI : M.Indep I) (h : 对任意 ⦃J⦄, M.Indep J -> I subseteq J -> I = J)
  证明: by
  rwa [isBase_iff_maximal_indep, maximal_subset_iff, and_iff_right hI]

Depends on / 依赖: and_iff_right, isBase_iff_maximal_indep, maximal_subset_iff
-/
theorem Indep.isBase_of_maximal (hI : M.Indep I) (h : forall ⦃J⦄, M.Indep J -> I subseteq J -> I = J) :
    M.IsBase I := by
  rwa [isBase_iff_maximal_indep, maximal_subset_iff, and_iff_right hI]

/--
theorem `IsBase.dep_of_ssubset` / 定理 `IsBase.dep_of_ssubset`

English:
theorem IsBase.dep_of_ssubset
  given: (hB : M.IsBase B) (h : B ⊂ X) (hX : X subseteq M.E := by aesop_mat)
  proof: ⟨fun hX => h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

中文:
定理 IsBase.dep_of_ssubset
  条件: (hB : M.IsBase B) (h : B ⊂ X) (hX : X subseteq M.E := by aesop_mat)
  证明: ⟨fun hX => h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

Depends on / 依赖: M.Dep, aesop_mat, eq_of_subset_indep, h.ne, h.subset, hB.eq_of_subset_indep, subset
-/
theorem IsBase.dep_of_ssubset (hB : M.IsBase B) (h : B ⊂ X) (hX : X subseteq M.E := by aesop_mat) :
    M.Dep X :=
  ⟨fun hX => h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

/--
theorem `IsBase.dep_of_insert` / 定理 `IsBase.dep_of_insert`

English:
theorem IsBase.dep_of_insert
  given: (hB : M.IsBase B) (heB : e ∉ B) (he : e in M.E := by aesop_mat)
  proof: hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)

中文:
定理 IsBase.dep_of_insert
  条件: (hB : M.IsBase B) (heB : e ∉ B) (he : e in M.E := by aesop_mat)
  证明: hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)

Depends on / 依赖: M.Dep, aesop_mat, dep_of_ssubset, hB.dep_of_ssubset, hB.subset_ground, insert, insert_subset, ssubset_insert, subset_ground
-/
theorem IsBase.dep_of_insert (hB : M.IsBase B) (heB : e ∉ B) (he : e in M.E := by aesop_mat) :
    M.Dep (insert e B) := hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)

/--
theorem `IsBase.mem_of_insert_indep` / 定理 `IsBase.mem_of_insert_indep`

English:
theorem IsBase.mem_of_insert_indep
  given: (hB : M.IsBase B) (heB : M.Indep (insert e B))
  statement: e in B
  proof: by_contra fun he => (hB.dep_of_insert he (heB.subset_ground (mem_insert _ _))).not_indep heB

中文:
定理 IsBase.mem_of_insert_indep
  条件: (hB : M.IsBase B) (heB : M.Indep (insert e B))
  结论: e in B
  证明: by_contra fun he => (hB.dep_of_insert he (heB.subset_ground (mem_insert _ _))).not_indep heB

Depends on / 依赖: dep_of_insert, hB.dep_of_insert, heB.subset_ground, mem_insert, not_indep, subset_ground
-/
theorem IsBase.mem_of_insert_indep (hB : M.IsBase B) (heB : M.Indep (insert e B)) : e in B :=
  by_contra fun he => (hB.dep_of_insert he (heB.subset_ground (mem_insert _ _))).not_indep heB

/--
theorem `IsBase.eq_exchange_of_sdiff_eq_singleton` / 定理 `IsBase.eq_exchange_of_sdiff_eq_singleton`

English:
theorem IsBase.eq_exchange_of_sdiff_eq_singleton
  statement: (hB : M.IsBase B) (hB' : M.IsBase B')
  proof: by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f != e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_sdiff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_isBase hB' ?_).symm⟩
  rw [sdiff_subset_iff]; rw [insert_subset_iff]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [h]; rw [and_iff_left rfl.subset]
  exact Or.inl hf.1

@[deprecated (since := "2026-06-03")]
alias IsBase.eq_exchange_of_diff_eq_singleton := IsBase.eq_exchange_of_sdiff_eq_singleton

中文:
定理 IsBase.eq_exchange_of_sdiff_eq_singleton
  结论: (hB : M.IsBase B) (hB' : M.IsBase B')
  证明: by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f != e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_sdiff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_isBase hB' ?_).symm⟩
  rw [sdiff_subset_iff]; rw [insert_subset_iff]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [h]; rw [and_iff_left rfl.subset]
  exact Or.inl hf.1

@[deprecated (since := "2026-06-03")]
alias IsBase.eq_exchange_of_diff_eq_singleton := IsBase.eq_exchange_of_sdiff_eq_singleton

Depends on / 依赖: Or.inl, and_iff_left, eq_of_subset_isBase, exchange, h.symm.subset, hB.exchange, hb.eq_of_subset_isBase, insert_sdiff_singleton_comm, insert_subset_iff, mem_singleton, rfl.subset, sdiff_subset_iff, subset, union_comm
-/
theorem IsBase.eq_exchange_of_sdiff_eq_singleton (hB : M.IsBase B) (hB' : M.IsBase B')
    (h : B \ B' = {e}) : exists f in B' \ B, B' = (insert f B) \ {e} := by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f != e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_sdiff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_isBase hB' ?_).symm⟩
  rw [sdiff_subset_iff]; rw [insert_subset_iff]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [h]; rw [and_iff_left rfl.subset]
  exact Or.inl hf.1

@[deprecated (since := "2026-06-03")]
alias IsBase.eq_exchange_of_diff_eq_singleton := IsBase.eq_exchange_of_sdiff_eq_singleton

/--
theorem `IsBase.exchange_isBase_of_indep` / 定理 `IsBase.exchange_isBase_of_indep`

English:
theorem IsBase.exchange_isBase_of_indep
  statement: (hB : M.IsBase B) (hf : f ∉ B)
  proof: by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hcard := hB'.encard_sdiff_comm hB
  rw [insert_subset_iff]; rw [← sdiff_eq_empty]; rw [sdiff_sdiff_comm]; rw [sdiff_eq_empty]; rw [subset_singleton_iff_eq] at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_notMem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h]; rw [encard_singleton]; rw [encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [← h, ← singleton_union, ← hx, _root_.sdiff_sdiff_right_self, inf_eq_inter, inter_comm B,
    sdiff_union_inter]
  exact hB'

中文:
定理 IsBase.exchange_isBase_of_indep
  结论: (hB : M.IsBase B) (hf : f ∉ B)
  证明: by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hcard := hB'.encard_sdiff_comm hB
  rw [insert_subset_iff]; rw [← sdiff_eq_empty]; rw [sdiff_sdiff_comm]; rw [sdiff_eq_empty]; rw [subset_singleton_iff_eq] at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_notMem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h]; rw [encard_singleton]; rw [encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [← h, ← singleton_union, ← hx, _root_.sdiff_sdiff_right_self, inf_eq_inter, inter_comm B,
    sdiff_union_inter]
  exact hB'

Depends on / 依赖: encard_empty, encard_eq_one, encard_eq_zero, encard_sdiff_comm, encard_singleton, eq_empty_iff_forall_notMem, exists_isBase_superset, hI.exists_isBase_superset, hx.subset, insert_subset_iff, sdiff_eq_empty, sdiff_sdiff_comm, simp_rw, subset, subset_singleton_iff_eq
-/
theorem IsBase.exchange_isBase_of_indep (hB : M.IsBase B) (hf : f ∉ B)
    (hI : M.Indep (insert f (B \ {e}))) : M.IsBase (insert f (B \ {e})) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hcard := hB'.encard_sdiff_comm hB
  rw [insert_subset_iff]; rw [← sdiff_eq_empty]; rw [sdiff_sdiff_comm]; rw [sdiff_eq_empty]; rw [subset_singleton_iff_eq] at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_notMem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h]; rw [encard_singleton]; rw [encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [← h, ← singleton_union, ← hx, _root_.sdiff_sdiff_right_self, inf_eq_inter, inter_comm B,
    sdiff_union_inter]
  exact hB'

/--
theorem `IsBase.exchange_isBase_of_indep'` / 定理 `IsBase.exchange_isBase_of_indep'`

English:
theorem IsBase.exchange_isBase_of_indep'
  statement: (hB : M.IsBase B) (he : e in B) (hf : f ∉ B)
  proof: by
.symm have hfe : f != e := ne_of_mem_of_not_mem he hf
  rw [← insert_sdiff_singleton_comm hfe] at *
  exact hB.exchange_isBase_of_indep hf hI

中文:
定理 IsBase.exchange_isBase_of_indep'
  结论: (hB : M.IsBase B) (he : e in B) (hf : f ∉ B)
  证明: by
.symm have hfe : f != e := ne_of_mem_of_not_mem he hf
  rw [← insert_sdiff_singleton_comm hfe] at *
  exact hB.exchange_isBase_of_indep hf hI

Depends on / 依赖: exchange_isBase_of_indep, hB.exchange_isBase_of_indep, insert_sdiff_singleton_comm, ne_of_mem_of_not_mem
-/
theorem IsBase.exchange_isBase_of_indep' (hB : M.IsBase B) (he : e in B) (hf : f ∉ B)
    (hI : M.Indep (insert f B \ {e})) : M.IsBase (insert f B \ {e}) := by
.symm have hfe : f != e := ne_of_mem_of_not_mem he hf
  rw [← insert_sdiff_singleton_comm hfe] at *
  exact hB.exchange_isBase_of_indep hf hI

/--
lemma `insert_isBase_of_insert_indep` / 引理 `insert_isBase_of_insert_indep`

English:
lemma insert_isBase_of_insert_indep
  statement: {M : Matroid α} {I : Set α} {e f : α}
  proof: by
  obtain rfl | hef := eq_or_ne e f
  · assumption
  simpa [sdiff_singleton_eq_self he, hfI]
    using heI.exchange_isBase_of_indep (e := e) (f := f) (by simp [hef.symm, hf])

中文:
引理 insert_isBase_of_insert_indep
  结论: {M : 拟阵 α} {I : 集合 α} {e f : α}
  证明: by
  obtain rfl | hef := eq_or_ne e f
  · assumption
  simpa [sdiff_singleton_eq_self he, hfI]
    using heI.exchange_isBase_of_indep (e := e) (f := f) (by simp [hef.symm, hf])

Depends on / 依赖: eq_or_ne, exchange_isBase_of_indep, heI.exchange_isBase_of_indep, hef.symm, sdiff_singleton_eq_self
-/
lemma insert_isBase_of_insert_indep {M : Matroid α} {I : Set α} {e f : α}
    (he : e ∉ I) (hf : f ∉ I) (heI : M.IsBase (insert e I)) (hfI : M.Indep (insert f I)) :
    M.IsBase (insert f I) := by
  obtain rfl | hef := eq_or_ne e f
  · assumption
  simpa [sdiff_singleton_eq_self he, hfI]
    using heI.exchange_isBase_of_indep (e := e) (f := f) (by simp [hef.symm, hf])

/--
theorem `IsBase.insert_dep` / 定理 `IsBase.insert_dep`

English:
theorem IsBase.insert_dep
  given: (hB : M.IsBase B) (h : e in M.E \ B)
  statement: M.Dep (insert e B)
  proof: by
  rw [← not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi => insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)

中文:
定理 IsBase.insert_dep
  条件: (hB : M.IsBase B) (h : e in M.E \ B)
  结论: M.Dep (insert e B)
  证明: by
  rw [← not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi => insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)

Depends on / 依赖: eq_of_subset_indep, hB.eq_of_subset_indep, hB.subset_ground, insert_eq_self, insert_eq_self.mp, insert_subset, not_indep_iff, subset_ground, subset_insert
-/
theorem IsBase.insert_dep (hB : M.IsBase B) (h : e in M.E \ B) : M.Dep (insert e B) := by
  rw [← not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi => insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)

/--
theorem `Indep.exists_insert_of_not_isBase` / 定理 `Indep.exists_insert_of_not_isBase`

English:
theorem Indep.exists_insert_of_not_isBase
  given: (hI : M.Indep I) (hI' : ¬M.IsBase I) (hB : M.IsBase B)
  proof: by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB')))
  by_cases hxB : x in B
  · exact ⟨x, ⟨hxB, hx⟩, hB'.indep.subset (insert_subset hxB' hIB')⟩
  obtain ⟨e, he, hBase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact ⟨e, ⟨he.1, notMem_subset hIB' he.2⟩,
    indep_iff.2 ⟨_, hBase, insert_subset_insert (subset_sdiff_singleton hIB' hx)⟩⟩

中文:
定理 Indep.存在_insert_of_not_isBase
  条件: (hI : M.Indep I) (hI' : ¬M.IsBase I) (hB : M.IsBase B)
  证明: by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB')))
  by_cases hxB : x in B
  · exact ⟨x, ⟨hxB, hx⟩, hB'.indep.subset (insert_subset hxB' hIB')⟩
  obtain ⟨e, he, hBase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact ⟨e, ⟨he.1, notMem_subset hIB' he.2⟩,
    indep_iff.2 ⟨_, hBase, insert_subset_insert (subset_sdiff_singleton hIB' hx)⟩⟩

Depends on / 依赖: exchange, exists_isBase_superset, exists_of_ssubset, hI.exists_isBase_superset, indep.subset, indep_iff, insert_subset, insert_subset_insert, notMem_subset, ssubset_of_ne, subset, subset_sdiff_singleton
-/
theorem Indep.exists_insert_of_not_isBase (hI : M.Indep I) (hI' : ¬M.IsBase I) (hB : M.IsBase B) :
    exists e in B \ I, M.Indep (insert e I) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB')))
  by_cases hxB : x in B
  · exact ⟨x, ⟨hxB, hx⟩, hB'.indep.subset (insert_subset hxB' hIB')⟩
  obtain ⟨e, he, hBase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact ⟨e, ⟨he.1, notMem_subset hIB' he.2⟩,
    indep_iff.2 ⟨_, hBase, insert_subset_insert (subset_sdiff_singleton hIB' hx)⟩⟩

/--
theorem `Indep.exists_insert_of_not_maximal` / 定理 `Indep.exists_insert_of_not_maximal`

English:
theorem Indep.exists_insert_of_not_maximal
  given: (M : Matroid α) ⦃I B
  statement: Set α⦄ (hI : M.Indep I)
  proof: by
  simp only [maximal_subset_iff, hI, not_and, not_forall, exists_prop, true_imp_iff] at hB hInotmax
  refine hI.exists_insert_of_not_isBase (fun hIb => ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hInotmax
exact hne hIb.eq_of_subset_indep hII' hI'
  exact hB.1.isBase_of_maximal fun J hJ hBJ => hB.2 hJ hBJ

中文:
定理 Indep.存在_insert_of_not_maximal
  条件: (M : 拟阵 α) ⦃I B
  结论: 集合 α⦄ (hI : M.Indep I)
  证明: by
  simp only [maximal_subset_iff, hI, not_and, not_forall, exists_prop, true_imp_iff] at hB hInotmax
  refine hI.exists_insert_of_not_isBase (fun hIb => ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hInotmax
exact hne hIb.eq_of_subset_indep hII' hI'
  exact hB.1.isBase_of_maximal fun J hJ hBJ => hB.2 hJ hBJ

Depends on / 依赖: eq_of_subset_indep, exists_insert_of_not_isBase, exists_prop, hI.exists_insert_of_not_isBase, hIb.eq_of_subset_indep, hInotmax, isBase_of_maximal, maximal_subset_iff, not_and, not_forall, true_imp_iff
-/
theorem Indep.exists_insert_of_not_maximal (M : Matroid α) ⦃I B : Set α⦄ (hI : M.Indep I)
    (hInotmax : ¬ Maximal M.Indep I) (hB : Maximal M.Indep B) :
    exists x in B \ I, M.Indep (insert x I) := by
  simp only [maximal_subset_iff, hI, not_and, not_forall, exists_prop, true_imp_iff] at hB hInotmax
  refine hI.exists_insert_of_not_isBase (fun hIb => ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hInotmax
exact hne hIb.eq_of_subset_indep hII' hI'
  exact hB.1.isBase_of_maximal fun J hJ hBJ => hB.2 hJ hBJ

/--
theorem `Indep.isBase_of_forall_insert` / 定理 `Indep.isBase_of_forall_insert`

English:
theorem Indep.isBase_of_forall_insert
  statement: (hB : M.Indep B)
  proof: by
  by_contra hnb
  obtain ⟨B', hB'⟩ := M.exists_isBase
  obtain ⟨e, he, h⟩ := hB.exists_insert_of_not_isBase hnb hB'
  exact hBmax e ⟨hB'.subset_ground he.1, he.2⟩ h

中文:
定理 Indep.isBase_of_对任意_insert
  结论: (hB : M.Indep B)
  证明: by
  by_contra hnb
  obtain ⟨B', hB'⟩ := M.exists_isBase
  obtain ⟨e, he, h⟩ := hB.exists_insert_of_not_isBase hnb hB'
  exact hBmax e ⟨hB'.subset_ground he.1, he.2⟩ h

Depends on / 依赖: M.exists_isBase, exists_insert_of_not_isBase, exists_isBase, hB.exists_insert_of_not_isBase, subset_ground
-/
theorem Indep.isBase_of_forall_insert (hB : M.Indep B)
    (hBmax : forall e in M.E \ B, ¬ M.Indep (insert e B)) : M.IsBase B := by
  by_contra hnb
  obtain ⟨B', hB'⟩ := M.exists_isBase
  obtain ⟨e, he, h⟩ := hB.exists_insert_of_not_isBase hnb hB'
  exact hBmax e ⟨hB'.subset_ground he.1, he.2⟩ h

/--
theorem `ground_indep_iff_isBase` / 定理 `ground_indep_iff_isBase`

English:
theorem ground_indep_iff_isBase
  statement: M.Indep M.E ↔ M.IsBase M.E
  proof: ⟨fun h => h.isBase_of_maximal (fun _ hJ hEJ => hEJ.antisymm hJ.subset_ground), IsBase.indep⟩

中文:
定理 ground_indep_iff_isBase
  结论: M.Indep M.E ↔ M.IsBase M.E
  证明: ⟨fun h => h.isBase_of_maximal (fun _ hJ hEJ => hEJ.antisymm hJ.subset_ground), IsBase.indep⟩

Depends on / 依赖: IsBase, IsBase.indep, antisymm, h.isBase_of_maximal, hEJ.antisymm, hJ.subset_ground, isBase_of_maximal, subset_ground
-/
theorem ground_indep_iff_isBase : M.Indep M.E ↔ M.IsBase M.E :=
  ⟨fun h => h.isBase_of_maximal (fun _ hJ hEJ => hEJ.antisymm hJ.subset_ground), IsBase.indep⟩

/--
theorem `IsBase.exists_insert_of_ssubset` / 定理 `IsBase.exists_insert_of_ssubset`

English:
theorem IsBase.exists_insert_of_ssubset
  given: (hB : M.IsBase B) (hIB : I ⊂ B) (hB' : M.IsBase B')
  proof: (hB.indep.subset hIB.subset).exists_insert_of_not_isBase
    (fun hI => hIB.ne (hI.eq_of_subset_isBase hB hIB.subset)) hB'

中文:
定理 IsBase.存在_insert_of_ssubset
  条件: (hB : M.IsBase B) (hIB : I ⊂ B) (hB' : M.IsBase B')
  证明: (hB.indep.subset hIB.subset).exists_insert_of_not_isBase
    (fun hI => hIB.ne (hI.eq_of_subset_isBase hB hIB.subset)) hB'

Depends on / 依赖: eq_of_subset_isBase, exists_insert_of_not_isBase, hB.indep.subset, hI.eq_of_subset_isBase, hIB.ne, hIB.subset, subset
-/
theorem IsBase.exists_insert_of_ssubset (hB : M.IsBase B) (hIB : I ⊂ B) (hB' : M.IsBase B') :
    exists e in B' \ I, M.Indep (insert e I) :=
  (hB.indep.subset hIB.subset).exists_insert_of_not_isBase
    (fun hI => hIB.ne (hI.eq_of_subset_isBase hB hIB.subset)) hB'

/--
theorem `ext_indep` / 定理 `ext_indep`

English:
theorem ext_indep
  statement: {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
  proof: have h' : M₁.Indep = M₂.Indep := by
    ext I
    by_cases hI : I subseteq M₁.E
    · rwa [h]
    exact iff_of_false (fun hi => hI hi.subset_ground)
      (fun hi => hI (hi.subset_ground.trans_eq hE.symm))
  ext_isBase hE (fun B _ => by simp_rw [isBase_iff_maximal_indep, h'])

中文:
定理 ext_indep
  结论: {M₁ M₂ : 拟阵 α} (hE : M₁.E = M₂.E)
  证明: have h' : M₁.Indep = M₂.Indep := by
    ext I
    by_cases hI : I subseteq M₁.E
    · rwa [h]
    exact iff_of_false (fun hi => hI hi.subset_ground)
      (fun hi => hI (hi.subset_ground.trans_eq hE.symm))
  ext_isBase hE (fun B _ => by simp_rw [isBase_iff_maximal_indep, h'])
-/
@[ext] theorem ext_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : forall ⦃I⦄, I subseteq M₁.E -> (M₁.Indep I ↔ M₂.Indep I)) : M₁ = M₂ :=
  have h' : M₁.Indep = M₂.Indep := by
    ext I
    by_cases hI : I subseteq M₁.E
    · rwa [h]
    exact iff_of_false (fun hi => hI hi.subset_ground)
      (fun hi => hI (hi.subset_ground.trans_eq hE.symm))
  ext_isBase hE (fun B _ => by simp_rw [isBase_iff_maximal_indep, h'])

/--
theorem `ext_iff_indep` / 定理 `ext_iff_indep`

English:
theorem ext_iff_indep
  given: {M₁ M₂ : Matroid α}
  proof: ⟨fun h => by (subst h; simp), fun h => ext_indep h.1 h.2⟩

中文:
定理 ext_iff_indep
  条件: {M₁ M₂ : 拟阵 α}
  证明: ⟨fun h => by (subst h; simp), fun h => ext_indep h.1 h.2⟩

Depends on / 依赖: ext_indep
-/
theorem ext_iff_indep {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ forall ⦃I⦄, I subseteq M₁.E -> (M₁.Indep I ↔ M₂.Indep I) :=
  ⟨fun h => by (subst h; simp), fun h => ext_indep h.1 h.2⟩

/--
lemma `ext_isBase_indep` / 引理 `ext_isBase_indep`

English:
lemma ext_isBase_indep
  statement: {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
  proof: by
  refine ext_indep hE fun I hIE => ⟨fun hI => ?_, fun hI => ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    exact (hM₁ hB).subset hIB
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact (hM₂ hB).subset hIB

中文:
引理 ext_isBase_indep
  结论: {M₁ M₂ : 拟阵 α} (hE : M₁.E = M₂.E)
  证明: by
  refine ext_indep hE fun I hIE => ⟨fun hI => ?_, fun hI => ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    exact (hM₁ hB).subset hIB
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact (hM₂ hB).subset hIB

Depends on / 依赖: exists_isBase_superset, ext_indep, hI.exists_isBase_superset, subset
-/
lemma ext_isBase_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hM₁ : forall ⦃B⦄, M₁.IsBase B -> M₂.Indep B) (hM₂ : forall ⦃B⦄, M₂.IsBase B -> M₁.Indep B) : M₁ = M₂ := by
  refine ext_indep hE fun I hIE => ⟨fun hI => ?_, fun hI => ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    exact (hM₁ hB).subset hIB
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact (hM₂ hB).subset hIB

/--
Definition of `Finitary` / `Finitary` 的定义

English:
class Finitary
  parameters: (M : Matroid α)
  axioms and operations (1):
    - indep_of_forall_finite : forall I, (forall J, J subseteq I -> J.Finite -> M.Indep J) -> M.Indep I

中文:
类 Finitary
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - indep_of_forall_finite : 对任意 I, (对任意 J, J subseteq I -> J.有限 -> M.Indep J) -> M.Indep I
-/
@[mk_iff] class Finitary (M : Matroid α) : Prop where
  /-- `I` is independent if all its finite subsets are independent. -/
  indep_of_forall_finite : forall I, (forall J, J subseteq I -> J.Finite -> M.Indep J) -> M.Indep I

/--
theorem `indep_of_forall_finite_subset_indep` / 定理 `indep_of_forall_finite_subset_indep`

English:
theorem indep_of_forall_finite_subset_indep
  statement: {M : Matroid α} [Finitary M] (I : Set α)
  proof: Finitary.indep_of_forall_finite I h

中文:
定理 indep_of_对任意_finite_subset_indep
  结论: {M : 拟阵 α} [Finitary M] (I : 集合 α)
  证明: Finitary.indep_of_forall_finite I h

Depends on / 依赖: Finitary, Finitary.indep_of_forall_finite, indep_of_forall_finite
-/
theorem indep_of_forall_finite_subset_indep {M : Matroid α} [Finitary M] (I : Set α)
    (h : forall J, J subseteq I -> J.Finite -> M.Indep J) : M.Indep I :=
  Finitary.indep_of_forall_finite I h

/--
theorem `indep_iff_forall_finite_subset_indep` / 定理 `indep_iff_forall_finite_subset_indep`

English:
theorem indep_iff_forall_finite_subset_indep
  given: {M : Matroid α} [Finitary M]
  proof: ⟨fun h _ hJI _ => h.subset hJI, Finitary.indep_of_forall_finite I⟩

中文:
定理 indep_iff_对任意_finite_subset_indep
  条件: {M : 拟阵 α} [Finitary M]
  证明: ⟨fun h _ hJI _ => h.subset hJI, Finitary.indep_of_forall_finite I⟩

Depends on / 依赖: Finitary, Finitary.indep_of_forall_finite, h.subset, indep_of_forall_finite, subset
-/
theorem indep_iff_forall_finite_subset_indep {M : Matroid α} [Finitary M] :
    M.Indep I ↔ forall J, J subseteq I -> J.Finite -> M.Indep J :=
  ⟨fun h _ hJI _ => h.subset hJI, Finitary.indep_of_forall_finite I⟩

/--
Instance `finitary_of_rankFinite` / 实例 `finitary_of_rankFinite`

English:
instance finitary_of_rankFinite
  signature: {M : Matroid α} [RankFinite M]
  body: by
    refine I.finite_or_infinite.elim (hI _ Subset.rfl) (fun h => False.elim ?_)
    obtain ⟨B, hB⟩ := M.exists_isBase
    obtain ⟨I₀, hI₀I, hI₀fin, hI₀card⟩ := h.exists_subset_ncard_eq (B.ncard + 1)
    obtain ⟨B', hB', hI₀B'⟩ := (hI _ hI₀I hI₀fin).exists_isBase_superset
    have hle := ncard_le_ncard hI₀B' hB'.finite
    rw [hI₀card]; rw [hB'.ncard_eq_ncard_of_isBase hB]; rw [Nat.add_one_le_iff] at hle
    exact hle.ne rfl

中文:
实例 finitary_of_rankFinite
  签名: {M : 拟阵 α} [RankFinite M]
  定义体: by
    refine I.finite_or_infinite.elim (hI _ Subset.rfl) (fun h => False.elim ?_)
    obtain ⟨B, hB⟩ := M.exists_isBase
    obtain ⟨I₀, hI₀I, hI₀fin, hI₀card⟩ := h.exists_subset_ncard_eq (B.ncard + 1)
    obtain ⟨B', hB', hI₀B'⟩ := (hI _ hI₀I hI₀fin).exists_isBase_superset
    have hle := ncard_le_ncard hI₀B' hB'.finite
    rw [hI₀card]; rw [hB'.ncard_eq_ncard_of_isBase hB]; rw [Nat.add_one_le_iff] at hle
    exact hle.ne rfl

Depends on / 依赖: B.ncard, False.elim, I.finite_or_infinite.elim, M.exists_isBase, Nat.add_one_le_iff, Subset, Subset.rfl, add_one_le_iff, exists_isBase, exists_isBase_superset, exists_subset_ncard_eq, finite, finite_or_infinite, h.exists_subset_ncard_eq, hle.ne, ncard_eq_ncard_of_isBase, ncard_le_ncard
-/
instance finitary_of_rankFinite {M : Matroid α} [RankFinite M] : Finitary M where
  indep_of_forall_finite I hI := by
    refine I.finite_or_infinite.elim (hI _ Subset.rfl) (fun h => False.elim ?_)
    obtain ⟨B, hB⟩ := M.exists_isBase
    obtain ⟨I₀, hI₀I, hI₀fin, hI₀card⟩ := h.exists_subset_ncard_eq (B.ncard + 1)
    obtain ⟨B', hB', hI₀B'⟩ := (hI _ hI₀I hI₀fin).exists_isBase_superset
    have hle := ncard_le_ncard hI₀B' hB'.finite
    rw [hI₀card]; rw [hB'.ncard_eq_ncard_of_isBase hB]; rw [Nat.add_one_le_iff] at hle
    exact hle.ne rfl

/--
theorem `existsMaximalSubsetProperty_indep` / 定理 `existsMaximalSubsetProperty_indep`

English:
theorem existsMaximalSubsetProperty_indep
  given: (M : Matroid α)
  proof: M.maximality

中文:
定理 存在MaximalSubsetProperty_indep
  条件: (M : 拟阵 α)
  证明: M.maximality

Depends on / 依赖: M.maximality, maximality
-/
theorem existsMaximalSubsetProperty_indep (M : Matroid α) :
    forall X, X subseteq M.E -> ExistsMaximalSubsetProperty M.Indep X :=
  M.maximality

end dep_indep

section copy

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (M : Matroid α) (E : Set α) (IsBase Indep : Set α -> Prop) (hE : E = M.E)
  body: E
  IsBase := IsBase
  Indep := Indep
  indep_iff' _ := by simp_rw [hI, hB, M.indep_iff]
  exists_isBase := by
    simp_rw [hB]
    exact M.exists_isBase
  isBase_exchange := by
    simp_rw [show IsBase = M.IsBase from funext (by simp [hB])]
    exact M.isBase_exchange
  maximality := by
    simp_rw [hE, show Indep = M.Indep from funext (by simp [hI])]
    exact M.maximality
  subset_ground := by
    simp_rw [hE, hB]
    exact M.subset_ground

中文:
定义 copy
  签名: (M : 拟阵 α) (E : 集合 α) (IsBase Indep : 集合 α -> 命题) (hE : E = M.E)
  定义体: E
  IsBase := IsBase
  Indep := Indep
  indep_iff' _ := by simp_rw [hI, hB, M.indep_iff]
  exists_isBase := by
    simp_rw [hB]
    exact M.exists_isBase
  isBase_exchange := by
    simp_rw [show IsBase = M.IsBase from funext (by simp [hB])]
    exact M.isBase_exchange
  maximality := by
    simp_rw [hE, show Indep = M.Indep from funext (by simp [hI])]
    exact M.maximality
  subset_ground := by
    simp_rw [hE, hB]
    exact M.subset_ground
-/
@[simps] def copy (M : Matroid α) (E : Set α) (IsBase Indep : Set α -> Prop) (hE : E = M.E)
    (hB : forall B, IsBase B ↔ M.IsBase B) (hI : forall I, Indep I ↔ M.Indep I) : Matroid α where
  E := E
  IsBase := IsBase
  Indep := Indep
  indep_iff' _ := by simp_rw [hI, hB, M.indep_iff]
  exists_isBase := by
    simp_rw [hB]
    exact M.exists_isBase
  isBase_exchange := by
    simp_rw [show IsBase = M.IsBase from funext (by simp [hB])]
    exact M.isBase_exchange
  maximality := by
    simp_rw [hE, show Indep = M.Indep from funext (by simp [hI])]
    exact M.maximality
  subset_ground := by
    simp_rw [hE, hB]
    exact M.subset_ground

/--
Definition of `copyIndep` / `copyIndep` 的定义

English:
definition copyIndep
  signature: (M : Matroid α) (E : Set α) (Indep : Set α -> Prop)
  body: M.copy E M.IsBase Indep hE (fun _ => Iff.rfl) h

中文:
定义 copyIndep
  签名: (M : 拟阵 α) (E : 集合 α) (Indep : 集合 α -> 命题)
  定义体: M.copy E M.IsBase Indep hE (fun _ => Iff.rfl) h
-/
@[simps!] def copyIndep (M : Matroid α) (E : Set α) (Indep : Set α -> Prop)
    (hE : E = M.E) (h : forall I, Indep I ↔ M.Indep I) : Matroid α :=
  M.copy E M.IsBase Indep hE (fun _ => Iff.rfl) h

/--
Definition of `copyBase` / `copyBase` 的定义

English:
definition copyBase
  signature: (M : Matroid α) (E : Set α) (IsBase : Set α -> Prop)
  body: M.copy E IsBase M.Indep hE h (fun _ => Iff.rfl)

中文:
定义 copyBase
  签名: (M : 拟阵 α) (E : 集合 α) (IsBase : 集合 α -> 命题)
  定义体: M.copy E IsBase M.Indep hE h (fun _ => Iff.rfl)
-/
@[simps!] def copyBase (M : Matroid α) (E : Set α) (IsBase : Set α -> Prop)
    (hE : E = M.E) (h : forall B, IsBase B ↔ M.IsBase B) : Matroid α :=
  M.copy E IsBase M.Indep hE h (fun _ => Iff.rfl)

end copy

section IsBasis

/--
Definition of `IsBasis` / `IsBasis` 的定义

English:
definition IsBasis
  signature: (M : Matroid α) (I X : Set α)
  body: Maximal (fun A => M.Indep A ∧ A subseteq X) I ∧ X subseteq M.E

中文:
定义 是基
  签名: (M : 拟阵 α) (I X : 集合 α)
  定义体: Maximal (fun A => M.Indep A ∧ A subseteq X) I ∧ X subseteq M.E

Depends on / 依赖: M.Indep, Maximal, subseteq
-/
def IsBasis (M : Matroid α) (I X : Set α) : Prop :=
  Maximal (fun A => M.Indep A ∧ A subseteq X) I ∧ X subseteq M.E

/--
Definition of `IsBasis'` / `IsBasis'` 的定义

English:
definition IsBasis'
  signature: (M : Matroid α) (I X : Set α)
  body: Maximal (fun A => M.Indep A ∧ A subseteq X) I

中文:
定义 是基'
  签名: (M : 拟阵 α) (I X : 集合 α)
  定义体: Maximal (fun A => M.Indep A ∧ A subseteq X) I

Depends on / 依赖: M.Indep, Maximal, subseteq
-/
def IsBasis' (M : Matroid α) (I X : Set α) : Prop :=
  Maximal (fun A => M.Indep A ∧ A subseteq X) I

variable {B I J X Y : Set α} {e : α}

/--
theorem `IsBasis'.indep` / 定理 `IsBasis'.indep`

English:
theorem IsBasis'.indep
  given: (hI : M.IsBasis' I X)
  statement: M.Indep I
  proof: hI.1.1

中文:
定理 是基'.indep
  条件: (hI : M.是基' I X)
  结论: M.Indep I
  证明: hI.1.1
-/
theorem IsBasis'.indep (hI : M.IsBasis' I X) : M.Indep I :=
  hI.1.1

/--
theorem `IsBasis.indep` / 定理 `IsBasis.indep`

English:
theorem IsBasis.indep
  given: (hI : M.IsBasis I X)
  statement: M.Indep I
  proof: hI.1.1.1

中文:
定理 是基.indep
  条件: (hI : M.是基 I X)
  结论: M.Indep I
  证明: hI.1.1.1
-/
theorem IsBasis.indep (hI : M.IsBasis I X) : M.Indep I :=
  hI.1.1.1

/--
theorem `IsBasis.subset` / 定理 `IsBasis.subset`

English:
theorem IsBasis.subset
  given: (hI : M.IsBasis I X)
  statement: I subseteq X
  proof: hI.1.1.2

中文:
定理 是基.subset
  条件: (hI : M.是基 I X)
  结论: I subseteq X
  证明: hI.1.1.2
-/
theorem IsBasis.subset (hI : M.IsBasis I X) : I subseteq X :=
  hI.1.1.2

/--
theorem `IsBasis.isBasis'` / 定理 `IsBasis.isBasis'`

English:
theorem IsBasis.isBasis'
  given: (hI : M.IsBasis I X)
  statement: M.IsBasis' I X
  proof: hI.1

中文:
定理 是基.isBasis'
  条件: (hI : M.是基 I X)
  结论: M.是基' I X
  证明: hI.1
-/
theorem IsBasis.isBasis' (hI : M.IsBasis I X) : M.IsBasis' I X :=
  hI.1

/--
theorem `IsBasis'.isBasis` / 定理 `IsBasis'.isBasis`

English:
theorem IsBasis'.isBasis
  given: (hI : M.IsBasis' I X) (hX : X subseteq M.E := by aesop_mat)
  statement: M.IsBasis I X
  proof: ⟨hI, hX⟩

中文:
定理 是基'.isBasis
  条件: (hI : M.是基' I X) (hX : X subseteq M.E := by aesop_mat)
  结论: M.是基 I X
  证明: ⟨hI, hX⟩
-/
theorem IsBasis'.isBasis (hI : M.IsBasis' I X) (hX : X subseteq M.E := by aesop_mat) : M.IsBasis I X :=
  ⟨hI, hX⟩

/--
theorem `IsBasis'.subset` / 定理 `IsBasis'.subset`

English:
theorem IsBasis'.subset
  given: (hI : M.IsBasis' I X)
  statement: I subseteq X
  proof: hI.1.2


@[aesop unsafe 15% (rule_sets := [Matroid])]

中文:
定理 是基'.subset
  条件: (hI : M.是基' I X)
  结论: I subseteq X
  证明: hI.1.2


@[aesop unsafe 15% (rule_sets := [Matroid])]
-/
theorem IsBasis'.subset (hI : M.IsBasis' I X) : I subseteq X :=
  hI.1.2


@[aesop unsafe 15% (rule_sets := [Matroid])]
/--
theorem `IsBasis.subset_ground` / 定理 `IsBasis.subset_ground`

English:
theorem IsBasis.subset_ground
  given: (hI : M.IsBasis I X)
  statement: X subseteq M.E
  proof: hI.2

中文:
定理 是基.subset_ground
  条件: (hI : M.是基 I X)
  结论: X subseteq M.E
  证明: hI.2
-/
theorem IsBasis.subset_ground (hI : M.IsBasis I X) : X subseteq M.E :=
  hI.2

/--
theorem `IsBasis.isBasis_inter_ground` / 定理 `IsBasis.isBasis_inter_ground`

English:
theorem IsBasis.isBasis_inter_ground
  given: (hI : M.IsBasis I X)
  statement: M.IsBasis I (X inter M.E)
  proof: by
  convert! hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets := [Matroid])]

中文:
定理 是基.isBasis_inter_ground
  条件: (hI : M.是基 I X)
  结论: M.是基 I (X inter M.E)
  证明: by
  convert! hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets := [Matroid])]

Depends on / 依赖: convert, hI.subset_ground, inter_eq_self_of_subset_left, subset_ground
-/
theorem IsBasis.isBasis_inter_ground (hI : M.IsBasis I X) : M.IsBasis I (X inter M.E) := by
  convert! hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets := [Matroid])]
/--
theorem `IsBasis.left_subset_ground` / 定理 `IsBasis.left_subset_ground`

English:
theorem IsBasis.left_subset_ground
  given: (hI : M.IsBasis I X)
  statement: I subseteq M.E
  proof: hI.indep.subset_ground

中文:
定理 是基.left_subset_ground
  条件: (hI : M.是基 I X)
  结论: I subseteq M.E
  证明: hI.indep.subset_ground

Depends on / 依赖: hI.indep.subset_ground, subset_ground
-/
theorem IsBasis.left_subset_ground (hI : M.IsBasis I X) : I subseteq M.E :=
  hI.indep.subset_ground

/--
theorem `IsBasis.eq_of_subset_indep` / 定理 `IsBasis.eq_of_subset_indep`

English:
theorem IsBasis.eq_of_subset_indep
  statement: (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I subseteq J)
  proof: hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

中文:
定理 是基.eq_of_subset_indep
  结论: (hI : M.是基 I X) (hJ : M.Indep J) (hIJ : I subseteq J)
  证明: hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

Depends on / 依赖: antisymm, hIJ.antisymm
-/
theorem IsBasis.eq_of_subset_indep (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I subseteq J)
    (hJX : J subseteq X) : I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

/--
theorem `IsBasis.Finite` / 定理 `IsBasis.Finite`

English:
theorem IsBasis.Finite
  given: (hI : M.IsBasis I X) [RankFinite M]
  statement: I.Finite
  proof: hI.indep.finite

中文:
定理 是基.有限
  条件: (hI : M.是基 I X) [RankFinite M]
  结论: I.有限
  证明: hI.indep.finite

Depends on / 依赖: finite, hI.indep.finite
-/
theorem IsBasis.Finite (hI : M.IsBasis I X) [RankFinite M] : I.Finite := hI.indep.finite

/--
theorem `isBasis_iff'` / 定理 `isBasis_iff'`

English:
theorem isBasis_iff'
  proof: by
  rw [IsBasis]; rw [maximal_subset_iff]
  tauto

中文:
定理 isBasis_iff'
  证明: by
  rw [IsBasis]; rw [maximal_subset_iff]
  tauto

Depends on / 依赖: IsBasis, maximal_subset_iff
-/
theorem isBasis_iff' :
    M.IsBasis I X ↔ (M.Indep I ∧ I subseteq X ∧ forall ⦃J⦄, M.Indep J -> I subseteq J -> J subseteq X -> I = J) ∧ X subseteq M.E := by
  rw [IsBasis]; rw [maximal_subset_iff]
  tauto

/--
theorem `isBasis_iff` / 定理 `isBasis_iff`

English:
theorem isBasis_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [isBasis_iff']; rw [and_iff_left hX]

中文:
定理 isBasis_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [isBasis_iff']; rw [and_iff_left hX]

Depends on / 依赖: IsBasis, M.Indep, M.IsBasis, aesop_mat, and_iff_left, isBasis_iff, subseteq
-/
theorem isBasis_iff (hX : X subseteq M.E := by aesop_mat) :
    M.IsBasis I X ↔ (M.Indep I ∧ I subseteq X ∧ forall J, M.Indep J -> I subseteq J -> J subseteq X -> I = J) := by
  rw [isBasis_iff']; rw [and_iff_left hX]

/--
theorem `isBasis'_iff_isBasis_inter_ground` / 定理 `isBasis'_iff_isBasis_inter_ground`

English:
theorem isBasis'_iff_isBasis_inter_ground
  statement: M.IsBasis' I X ↔ M.IsBasis I (X inter M.E)
  proof: by
  rw [IsBasis']; rw [IsBasis]; rw [and_iff_left inter_subset_right]; rw [maximal_iff_maximal_of_imp_of_forall]
  · exact fun I hI => ⟨hI.1, hI.2.trans inter_subset_left⟩
  exact fun I hI => ⟨I, rfl.le, hI.1, subset_inter hI.2 hI.1.subset_ground⟩

中文:
定理 isBasis'_iff_isBasis_inter_ground
  结论: M.是基' I X ↔ M.是基 I (X inter M.E)
  证明: by
  rw [IsBasis']; rw [IsBasis]; rw [and_iff_left inter_subset_right]; rw [maximal_iff_maximal_of_imp_of_forall]
  · exact fun I hI => ⟨hI.1, hI.2.trans inter_subset_left⟩
  exact fun I hI => ⟨I, rfl.le, hI.1, subset_inter hI.2 hI.1.subset_ground⟩

Depends on / 依赖: IsBasis, and_iff_left, inter_subset_left, inter_subset_right, maximal_iff_maximal_of_imp_of_forall, rfl.le, subset_ground, subset_inter
-/
theorem isBasis'_iff_isBasis_inter_ground : M.IsBasis' I X ↔ M.IsBasis I (X inter M.E) := by
  rw [IsBasis']; rw [IsBasis]; rw [and_iff_left inter_subset_right]; rw [maximal_iff_maximal_of_imp_of_forall]
  · exact fun I hI => ⟨hI.1, hI.2.trans inter_subset_left⟩
  exact fun I hI => ⟨I, rfl.le, hI.1, subset_inter hI.2 hI.1.subset_ground⟩

/--
theorem `isBasis'_iff_isBasis` / 定理 `isBasis'_iff_isBasis`

English:
theorem isBasis'_iff_isBasis
  given: (hX : X subseteq M.E := by aesop_mat)
  statement: M.IsBasis' I X ↔ M.IsBasis I X
  proof: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [inter_eq_self_of_subset_left hX]

中文:
定理 isBasis'_iff_isBasis
  条件: (hX : X subseteq M.E := by aesop_mat)
  结论: M.是基' I X ↔ M.是基 I X
  证明: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [inter_eq_self_of_subset_left hX]
-/
theorem isBasis'_iff_isBasis (hX : X subseteq M.E := by aesop_mat) : M.IsBasis' I X ↔ M.IsBasis I X := by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [inter_eq_self_of_subset_left hX]

/--
theorem `isBasis_iff_isBasis'_subset_ground` / 定理 `isBasis_iff_isBasis'_subset_ground`

English:
theorem isBasis_iff_isBasis'_subset_ground
  statement: M.IsBasis I X ↔ M.IsBasis' I X ∧ X subseteq M.E
  proof: ⟨fun h => ⟨h.isBasis', h.subset_ground⟩, fun h => (isBasis'_iff_isBasis h.2).mp h.1⟩

中文:
定理 isBasis_iff_isBasis'_subset_ground
  结论: M.是基 I X ↔ M.是基' I X ∧ X subseteq M.E
  证明: ⟨fun h => ⟨h.isBasis', h.subset_ground⟩, fun h => (isBasis'_iff_isBasis h.2).mp h.1⟩

Depends on / 依赖: _iff_isBasis, h.isBasis, h.subset_ground, isBasis, subset_ground
-/
theorem isBasis_iff_isBasis'_subset_ground : M.IsBasis I X ↔ M.IsBasis' I X ∧ X subseteq M.E :=
  ⟨fun h => ⟨h.isBasis', h.subset_ground⟩, fun h => (isBasis'_iff_isBasis h.2).mp h.1⟩

/--
theorem `IsBasis'.isBasis_inter_ground` / 定理 `IsBasis'.isBasis_inter_ground`

English:
theorem IsBasis'.isBasis_inter_ground
  given: (hIX : M.IsBasis' I X)
  statement: M.IsBasis I (X inter M.E)
  proof: isBasis'_iff_isBasis_inter_ground.mp hIX

中文:
定理 是基'.isBasis_inter_ground
  条件: (hIX : M.是基' I X)
  结论: M.是基 I (X inter M.E)
  证明: isBasis'_iff_isBasis_inter_ground.mp hIX
-/
theorem IsBasis'.isBasis_inter_ground (hIX : M.IsBasis' I X) : M.IsBasis I (X inter M.E) :=
  isBasis'_iff_isBasis_inter_ground.mp hIX

/--
theorem `IsBasis'.eq_of_subset_indep` / 定理 `IsBasis'.eq_of_subset_indep`

English:
theorem IsBasis'.eq_of_subset_indep
  statement: (hI : M.IsBasis' I X) (hJ : M.Indep J) (hIJ : I subseteq J)
  proof: hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

中文:
定理 是基'.eq_of_subset_indep
  结论: (hI : M.是基' I X) (hJ : M.Indep J) (hIJ : I subseteq J)
  证明: hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)
-/
theorem IsBasis'.eq_of_subset_indep (hI : M.IsBasis' I X) (hJ : M.Indep J) (hIJ : I subseteq J)
    (hJX : J subseteq X) : I = J :=
  hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

/--
theorem `IsBasis'.insert_not_indep` / 定理 `IsBasis'.insert_not_indep`

English:
theorem IsBasis'.insert_not_indep
  given: (hI : M.IsBasis' I X) (he : e in X \ I)
  statement: ¬ M.Indep (insert e I)
  proof: fun hi => he.2 insert_eq_self.1 Eq.symm
    hI.eq_of_subset_indep hi (subset_insert _ _) (insert_subset he.1 hI.subset)

中文:
定理 是基'.insert_not_indep
  条件: (hI : M.是基' I X) (he : e in X \ I)
  结论: ¬ M.Indep (insert e I)
  证明: fun hi => he.2 insert_eq_self.1 Eq.symm
    hI.eq_of_subset_indep hi (subset_insert _ _) (insert_subset he.1 hI.subset)
-/
theorem IsBasis'.insert_not_indep (hI : M.IsBasis' I X) (he : e in X \ I) : ¬ M.Indep (insert e I) :=
fun hi => he.2 insert_eq_self.1 Eq.symm
    hI.eq_of_subset_indep hi (subset_insert _ _) (insert_subset he.1 hI.subset)

/--
theorem `isBasis_iff_maximal` / 定理 `isBasis_iff_maximal`

English:
theorem isBasis_iff_maximal
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [IsBasis]; rw [and_iff_left hX]

中文:
定理 isBasis_iff_maximal
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [IsBasis]; rw [and_iff_left hX]

Depends on / 依赖: IsBasis, M.Indep, M.IsBasis, Maximal, aesop_mat, and_iff_left, subseteq
-/
theorem isBasis_iff_maximal (hX : X subseteq M.E := by aesop_mat) :
    M.IsBasis I X ↔ Maximal (fun I => M.Indep I ∧ I subseteq X) I := by
  rw [IsBasis]; rw [and_iff_left hX]

/--
theorem `Indep.isBasis_of_maximal_subset` / 定理 `Indep.isBasis_of_maximal_subset`

English:
theorem Indep.isBasis_of_maximal_subset
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: by
  rw [isBasis_iff (by aesop_mat : X subseteq M.E)]; rw [and_iff_right hI]; rw [and_iff_right hIX]
  exact fun J hJ hIJ hJX => hIJ.antisymm (hmax hJ hIJ hJX)

中文:
定理 Indep.isBasis_of_maximal_subset
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: by
  rw [isBasis_iff (by aesop_mat : X subseteq M.E)]; rw [and_iff_right hI]; rw [and_iff_right hIX]
  exact fun J hJ hIJ hJX => hIJ.antisymm (hmax hJ hIJ hJX)

Depends on / 依赖: IsBasis, M.IsBasis, aesop_mat, and_iff_right, antisymm, hIJ.antisymm, isBasis_iff, subseteq
-/
theorem Indep.isBasis_of_maximal_subset (hI : M.Indep I) (hIX : I subseteq X)
    (hmax : forall ⦃J⦄, M.Indep J -> I subseteq J -> J subseteq X -> J subseteq I) (hX : X subseteq M.E := by aesop_mat) :
    M.IsBasis I X := by
  rw [isBasis_iff (by aesop_mat : X subseteq M.E)]; rw [and_iff_right hI]; rw [and_iff_right hIX]
  exact fun J hJ hIJ hJX => hIJ.antisymm (hmax hJ hIJ hJX)

/--
theorem `IsBasis.isBasis_subset` / 定理 `IsBasis.isBasis_subset`

English:
theorem IsBasis.isBasis_subset
  given: (hI : M.IsBasis I X) (hIY : I subseteq Y) (hYX : Y subseteq X)
  proof: by
  rw [isBasis_iff (hYX.trans hI.subset_ground)]; rw [and_iff_right hI.indep]; rw [and_iff_right hIY]
  exact fun J hJ hIJ hJY => hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)

中文:
定理 是基.isBasis_subset
  条件: (hI : M.是基 I X) (hIY : I subseteq Y) (hYX : Y subseteq X)
  证明: by
  rw [isBasis_iff (hYX.trans hI.subset_ground)]; rw [and_iff_right hI.indep]; rw [and_iff_right hIY]
  exact fun J hJ hIJ hJY => hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)

Depends on / 依赖: and_iff_right, eq_of_subset_indep, hI.eq_of_subset_indep, hI.indep, hI.subset_ground, hJY.trans, hYX.trans, isBasis_iff, subset_ground
-/
theorem IsBasis.isBasis_subset (hI : M.IsBasis I X) (hIY : I subseteq Y) (hYX : Y subseteq X) :
    M.IsBasis I Y := by
  rw [isBasis_iff (hYX.trans hI.subset_ground)]; rw [and_iff_right hI.indep]; rw [and_iff_right hIY]
  exact fun J hJ hIJ hJY => hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)

/--
theorem `isBasis_self_iff_indep` / 定理 `isBasis_self_iff_indep`

English:
theorem isBasis_self_iff_indep
  statement: M.IsBasis I I ↔ M.Indep I
  proof: by
  rw [isBasis_iff']; rw [and_iff_right rfl.subset]; rw [and_assoc]; rw [and_iff_left_iff_imp]
  exact fun hi => ⟨fun _ _ => subset_antisymm, hi.subset_ground⟩

中文:
定理 isBasis_self_iff_indep
  结论: M.是基 I I ↔ M.Indep I
  证明: by
  rw [isBasis_iff']; rw [and_iff_right rfl.subset]; rw [and_assoc]; rw [and_iff_left_iff_imp]
  exact fun hi => ⟨fun _ _ => subset_antisymm, hi.subset_ground⟩
-/
@[simp] theorem isBasis_self_iff_indep : M.IsBasis I I ↔ M.Indep I := by
  rw [isBasis_iff']; rw [and_iff_right rfl.subset]; rw [and_assoc]; rw [and_iff_left_iff_imp]
  exact fun hi => ⟨fun _ _ => subset_antisymm, hi.subset_ground⟩

/--
theorem `Indep.isBasis_self` / 定理 `Indep.isBasis_self`

English:
theorem Indep.isBasis_self
  given: (h : M.Indep I)
  statement: M.IsBasis I I
  proof: isBasis_self_iff_indep.mpr h

中文:
定理 Indep.isBasis_self
  条件: (h : M.Indep I)
  结论: M.是基 I I
  证明: isBasis_self_iff_indep.mpr h

Depends on / 依赖: isBasis_self_iff_indep, isBasis_self_iff_indep.mpr
-/
theorem Indep.isBasis_self (h : M.Indep I) : M.IsBasis I I :=
  isBasis_self_iff_indep.mpr h

/--
theorem `isBasis_empty_iff` / 定理 `isBasis_empty_iff`

English:
theorem isBasis_empty_iff
  given: (M : Matroid α)
  statement: M.IsBasis I ∅ ↔ I = ∅
  proof: ⟨fun h => subset_empty_iff.mp h.subset, fun h => by (rw [h]; exact M.empty_indep.isBasis_self)⟩

中文:
定理 isBasis_empty_iff
  条件: (M : 拟阵 α)
  结论: M.是基 I ∅ ↔ I = ∅
  证明: ⟨fun h => subset_empty_iff.mp h.subset, fun h => by (rw [h]; exact M.empty_indep.isBasis_self)⟩
-/
@[simp] theorem isBasis_empty_iff (M : Matroid α) : M.IsBasis I ∅ ↔ I = ∅ :=
  ⟨fun h => subset_empty_iff.mp h.subset, fun h => by (rw [h]; exact M.empty_indep.isBasis_self)⟩

/--
theorem `IsBasis.dep_of_ssubset` / 定理 `IsBasis.dep_of_ssubset`

English:
theorem IsBasis.dep_of_ssubset
  given: (hI : M.IsBasis I X) (hIY : I ⊂ Y) (hYX : Y subseteq X)
  statement: M.Dep Y
  proof: by
  have : X subseteq M.E := hI.subset_ground
  rw [← not_indep_iff]
  exact fun hY => hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

中文:
定理 是基.dep_of_ssubset
  条件: (hI : M.是基 I X) (hIY : I ⊂ Y) (hYX : Y subseteq X)
  结论: M.Dep Y
  证明: by
  have : X subseteq M.E := hI.subset_ground
  rw [← not_indep_iff]
  exact fun hY => hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

Depends on / 依赖: eq_of_subset_indep, hI.eq_of_subset_indep, hI.subset_ground, hIY.ne, hIY.subset, not_indep_iff, subset, subset_ground, subseteq
-/
theorem IsBasis.dep_of_ssubset (hI : M.IsBasis I X) (hIY : I ⊂ Y) (hYX : Y subseteq X) : M.Dep Y := by
  have : X subseteq M.E := hI.subset_ground
  rw [← not_indep_iff]
  exact fun hY => hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

/--
theorem `IsBasis.insert_dep` / 定理 `IsBasis.insert_dep`

English:
theorem IsBasis.insert_dep
  given: (hI : M.IsBasis I X) (he : e in X \ I)
  statement: M.Dep (insert e I)
  proof: hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)

中文:
定理 是基.insert_dep
  条件: (hI : M.是基 I X) (he : e in X \ I)
  结论: M.Dep (insert e I)
  证明: hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)

Depends on / 依赖: dep_of_ssubset, hI.dep_of_ssubset, hI.subset, insert_subset, ssubset_insert, subset
-/
theorem IsBasis.insert_dep (hI : M.IsBasis I X) (he : e in X \ I) : M.Dep (insert e I) :=
  hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)

/--
theorem `IsBasis.mem_of_insert_indep` / 定理 `IsBasis.mem_of_insert_indep`

English:
theorem IsBasis.mem_of_insert_indep
  given: (hI : M.IsBasis I X) (he : e in X) (hIe : M.Indep (insert e I))
  proof: by_contra (fun heI => (hI.insert_dep ⟨he, heI⟩).not_indep hIe)

中文:
定理 是基.mem_of_insert_indep
  条件: (hI : M.是基 I X) (he : e in X) (hIe : M.Indep (insert e I))
  证明: by_contra (fun heI => (hI.insert_dep ⟨he, heI⟩).not_indep hIe)

Depends on / 依赖: hI.insert_dep, insert_dep, not_indep
-/
theorem IsBasis.mem_of_insert_indep (hI : M.IsBasis I X) (he : e in X) (hIe : M.Indep (insert e I)) :
    e in I :=
  by_contra (fun heI => (hI.insert_dep ⟨he, heI⟩).not_indep hIe)

/--
theorem `IsBasis'.mem_of_insert_indep` / 定理 `IsBasis'.mem_of_insert_indep`

English:
theorem IsBasis'.mem_of_insert_indep
  statement: (hI : M.IsBasis' I X) (he : e in X)
  proof: hI.isBasis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe

中文:
定理 是基'.mem_of_insert_indep
  结论: (hI : M.是基' I X) (he : e in X)
  证明: hI.isBasis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe
-/
theorem IsBasis'.mem_of_insert_indep (hI : M.IsBasis' I X) (he : e in X)
    (hIe : M.Indep (insert e I)) : e in I :=
  hI.isBasis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe

/--
theorem `IsBasis.not_isBasis_of_ssubset` / 定理 `IsBasis.not_isBasis_of_ssubset`

English:
theorem IsBasis.not_isBasis_of_ssubset
  given: (hI : M.IsBasis I X) (hJI : J ⊂ I)
  statement: ¬ M.IsBasis J X
  proof: fun h => hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

中文:
定理 是基.not_isBasis_of_ssubset
  条件: (hI : M.是基 I X) (hJI : J ⊂ I)
  结论: ¬ M.是基 J X
  证明: fun h => hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

Depends on / 依赖: eq_of_subset_indep, h.eq_of_subset_indep, hI.indep, hI.subset, hJI.ne, hJI.subset, subset
-/
theorem IsBasis.not_isBasis_of_ssubset (hI : M.IsBasis I X) (hJI : J ⊂ I) : ¬ M.IsBasis J X :=
  fun h => hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

/--
theorem `Indep.subset_isBasis_of_subset` / 定理 `Indep.subset_isBasis_of_subset`

English:
theorem Indep.subset_isBasis_of_subset
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: by
  obtain ⟨J, hJ, hJmax⟩ := M.maximality X hX I hI hIX
  exact ⟨J, ⟨hJmax, hX⟩, hJ⟩

中文:
定理 Indep.subset_isBasis_of_subset
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: by
  obtain ⟨J, hJ, hJmax⟩ := M.maximality X hX I hI hIX
  exact ⟨J, ⟨hJmax, hX⟩, hJ⟩

Depends on / 依赖: IsBasis, M.IsBasis, M.maximality, aesop_mat, maximality, subseteq
-/
theorem Indep.subset_isBasis_of_subset (hI : M.Indep I) (hIX : I subseteq X)
    (hX : X subseteq M.E := by aesop_mat) : exists J, M.IsBasis J X ∧ I subseteq J := by
  obtain ⟨J, hJ, hJmax⟩ := M.maximality X hX I hI hIX
  exact ⟨J, ⟨hJmax, hX⟩, hJ⟩

/--
theorem `Indep.subset_isBasis'_of_subset` / 定理 `Indep.subset_isBasis'_of_subset`

English:
theorem Indep.subset_isBasis'_of_subset
  given: (hI : M.Indep I) (hIX : I subseteq X)
  proof: by
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  exact hI.subset_isBasis_of_subset (subset_inter hIX hI.subset_ground)

中文:
定理 Indep.subset_isBasis'_of_subset
  条件: (hI : M.Indep I) (hIX : I subseteq X)
  证明: by
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  exact hI.subset_isBasis_of_subset (subset_inter hIX hI.subset_ground)

Depends on / 依赖: _iff_isBasis_inter_ground, hI.subset_ground, hI.subset_isBasis_of_subset, isBasis, simp_rw, subset_ground, subset_inter, subset_isBasis_of_subset
-/
theorem Indep.subset_isBasis'_of_subset (hI : M.Indep I) (hIX : I subseteq X) :
    exists J, M.IsBasis' J X ∧ I subseteq J := by
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  exact hI.subset_isBasis_of_subset (subset_inter hIX hI.subset_ground)

/--
theorem `exists_isBasis` / 定理 `exists_isBasis`

English:
theorem exists_isBasis
  given: (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat)
  proof: let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis_of_subset (empty_subset X)
  ⟨_, hI⟩

中文:
定理 存在_isBasis
  条件: (M : 拟阵 α) (X : 集合 α) (hX : X subseteq M.E := by aesop_mat)
  证明: let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis_of_subset (empty_subset X)
  ⟨_, hI⟩

Depends on / 依赖: IsBasis, M.IsBasis, M.empty_indep.subset_isBasis_of_subset, aesop_mat, empty_indep, empty_subset, subset_isBasis_of_subset
-/
theorem exists_isBasis (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat) :
    exists I, M.IsBasis I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis_of_subset (empty_subset X)
  ⟨_, hI⟩

/--
theorem `exists_isBasis'` / 定理 `exists_isBasis'`

English:
theorem exists_isBasis'
  given: (M : Matroid α) (X : Set α)
  statement: exists I, M.IsBasis' I X
  proof: let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis'_of_subset (empty_subset X)
  ⟨_, hI⟩

中文:
定理 存在_isBasis'
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: 存在 I, M.是基' I X
  证明: let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis'_of_subset (empty_subset X)
  ⟨_, hI⟩

Depends on / 依赖: M.empty_indep.subset_isBasis, _of_subset, empty_indep, empty_subset, subset_isBasis
-/
theorem exists_isBasis' (M : Matroid α) (X : Set α) : exists I, M.IsBasis' I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis'_of_subset (empty_subset X)
  ⟨_, hI⟩

/--
theorem `exists_isBasis_subset_isBasis` / 定理 `exists_isBasis_subset_isBasis`

English:
theorem exists_isBasis_subset_isBasis
  given: (M : Matroid α) (hXY : X subseteq Y) (hY : Y subseteq M.E := by aesop_mat)
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩

中文:
定理 存在_isBasis_subset_isBasis
  条件: (M : 拟阵 α) (hXY : X subseteq Y) (hY : Y subseteq M.E := by aesop_mat)
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩

Depends on / 依赖: IsBasis, M.IsBasis, M.exists_isBasis, aesop_mat, exists_isBasis, hI.indep.subset_isBasis_of_subset, hI.subset.trans, hXY.trans, subset, subset_isBasis_of_subset, subseteq
-/
theorem exists_isBasis_subset_isBasis (M : Matroid α) (hXY : X subseteq Y) (hY : Y subseteq M.E := by aesop_mat) :
    exists I J, M.IsBasis I X ∧ M.IsBasis J Y ∧ I subseteq J := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩

/--
theorem `IsBasis.exists_isBasis_inter_eq_of_superset` / 定理 `IsBasis.exists_isBasis_inter_eq_of_superset`

English:
theorem IsBasis.exists_isBasis_inter_eq_of_superset
  statement: (hI : M.IsBasis I X) (hXY : X subseteq Y)
  proof: by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he => hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))

中文:
定理 是基.存在_isBasis_inter_eq_of_superset
  结论: (hI : M.是基 I X) (hXY : X subseteq Y)
  证明: by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he => hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))

Depends on / 依赖: IsBasis, M.IsBasis, aesop_mat, hI.indep.subset_isBasis_of_subset, hI.mem_of_insert_indep, hI.subset, hI.subset.trans, hJ.indep.subset, insert_subset, mem_of_insert_indep, subset, subset_antisymm, subset_inter, subset_isBasis_of_subset
-/
theorem IsBasis.exists_isBasis_inter_eq_of_superset (hI : M.IsBasis I X) (hXY : X subseteq Y)
    (hY : Y subseteq M.E := by aesop_mat) : exists J, M.IsBasis J Y ∧ J inter X = I := by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he => hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))

/--
theorem `exists_isBasis_union_inter_isBasis` / 定理 `exists_isBasis_union_inter_isBasis`

English:
theorem exists_isBasis_union_inter_isBasis
  statement: (M : Matroid α) (X Y : Set α)
  proof: let ⟨J, hJ⟩ := M.exists_isBasis Y
  (hJ.exists_isBasis_inter_eq_of_superset subset_union_right).imp
  (fun I hI => ⟨hI.1, by rwa [hI.2]⟩)

中文:
定理 存在_isBasis_union_inter_isBasis
  结论: (M : 拟阵 α) (X Y : 集合 α)
  证明: let ⟨J, hJ⟩ := M.exists_isBasis Y
  (hJ.exists_isBasis_inter_eq_of_superset subset_union_right).imp
  (fun I hI => ⟨hI.1, by rwa [hI.2]⟩)

Depends on / 依赖: IsBasis, M.IsBasis, M.exists_isBasis, aesop_mat, exists_isBasis, exists_isBasis_inter_eq_of_superset, hJ.exists_isBasis_inter_eq_of_superset, subset_union_right, subseteq
-/
theorem exists_isBasis_union_inter_isBasis (M : Matroid α) (X Y : Set α)
    (hX : X subseteq M.E := by aesop_mat) (hY : Y subseteq M.E := by aesop_mat) :
    exists I, M.IsBasis I (X union Y) ∧ M.IsBasis (I inter Y) Y :=
  let ⟨J, hJ⟩ := M.exists_isBasis Y
  (hJ.exists_isBasis_inter_eq_of_superset subset_union_right).imp
  (fun I hI => ⟨hI.1, by rwa [hI.2]⟩)

/--
theorem `Indep.eq_of_isBasis` / 定理 `Indep.eq_of_isBasis`

English:
theorem Indep.eq_of_isBasis
  given: (hI : M.Indep I) (hJ : M.IsBasis J I)
  statement: J = I
  proof: hJ.eq_of_subset_indep hI hJ.subset rfl.subset

中文:
定理 Indep.eq_of_isBasis
  条件: (hI : M.Indep I) (hJ : M.是基 J I)
  结论: J = I
  证明: hJ.eq_of_subset_indep hI hJ.subset rfl.subset

Depends on / 依赖: eq_of_subset_indep, hJ.eq_of_subset_indep, hJ.subset, rfl.subset, subset
-/
theorem Indep.eq_of_isBasis (hI : M.Indep I) (hJ : M.IsBasis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.subset rfl.subset

/--
theorem `IsBasis.exists_isBase` / 定理 `IsBasis.exists_isBase`

English:
theorem IsBasis.exists_isBase
  given: (hI : M.IsBasis I X)
  statement: exists B, M.IsBase B ∧ I = B inter X
  proof: let ⟨B,hB, hIB⟩ := hI.indep.exists_isBase_superset
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset)
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    inter_subset_right])⟩

中文:
定理 是基.存在_isBase
  条件: (hI : M.是基 I X)
  结论: 存在 B, M.IsBase B ∧ I = B inter X
  证明: let ⟨B,hB, hIB⟩ := hI.indep.exists_isBase_superset
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset)
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    inter_subset_right])⟩

Depends on / 依赖: eq_of_subset_indep, exists_isBase_superset, hB.indep.inter_right, hI.eq_of_subset_indep, hI.indep.exists_isBase_superset, hI.subset, inter_right, inter_subset_right, subset, subset_antisymm, subset_inter
-/
theorem IsBasis.exists_isBase (hI : M.IsBasis I X) : exists B, M.IsBase B ∧ I = B inter X :=
  let ⟨B,hB, hIB⟩ := hI.indep.exists_isBase_superset
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset)
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    inter_subset_right])⟩

/--
theorem `isBasis_ground_iff` / 定理 `isBasis_ground_iff`

English:
theorem isBasis_ground_iff
  statement: M.IsBasis B M.E ↔ M.IsBase B
  proof: by
  rw [IsBasis]; rw [and_iff_left rfl.subset]; rw [isBase_iff_maximal_indep]; rw [maximal_and_iff_right_of_imp (fun _ h => h.subset_ground)]; rw [and_iff_left_of_imp (fun h => h.1.subset_ground)]

中文:
定理 isBasis_ground_iff
  结论: M.是基 B M.E ↔ M.IsBase B
  证明: by
  rw [IsBasis]; rw [and_iff_left rfl.subset]; rw [isBase_iff_maximal_indep]; rw [maximal_and_iff_right_of_imp (fun _ h => h.subset_ground)]; rw [and_iff_left_of_imp (fun h => h.1.subset_ground)]
-/
@[simp] theorem isBasis_ground_iff : M.IsBasis B M.E ↔ M.IsBase B := by
  rw [IsBasis]; rw [and_iff_left rfl.subset]; rw [isBase_iff_maximal_indep]; rw [maximal_and_iff_right_of_imp (fun _ h => h.subset_ground)]; rw [and_iff_left_of_imp (fun h => h.1.subset_ground)]

/--
theorem `IsBase.isBasis_ground` / 定理 `IsBase.isBasis_ground`

English:
theorem IsBase.isBasis_ground
  given: (hB : M.IsBase B)
  statement: M.IsBasis B M.E
  proof: isBasis_ground_iff.mpr hB

中文:
定理 IsBase.isBasis_ground
  条件: (hB : M.IsBase B)
  结论: M.是基 B M.E
  证明: isBasis_ground_iff.mpr hB

Depends on / 依赖: isBasis_ground_iff, isBasis_ground_iff.mpr
-/
theorem IsBase.isBasis_ground (hB : M.IsBase B) : M.IsBasis B M.E :=
  isBasis_ground_iff.mpr hB

/--
theorem `Indep.isBasis_iff_forall_insert_dep` / 定理 `Indep.isBasis_iff_forall_insert_dep`

English:
theorem Indep.isBasis_iff_forall_insert_dep
  given: (hI : M.Indep I) (hIX : I subseteq X)
  proof: by
  rw [IsBasis]; rw [maximal_iff_forall_insert (fun I J hI hIJ => ⟨hI.1.subset hIJ]; rw [hIJ.trans hI.2⟩)]
  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, mem_sdiff, and_imp,
    Dep, hI.subset_ground]
  exact ⟨fun h e heX heI => ⟨fun hi => h.1 e heI hi heX, h.2 heX⟩,
    fun h => ⟨fun e heI hi heX => (h e heX heI).1 hi,
      fun e heX => (em (e in I)).elim (fun h => hI.subset_ground h) fun heI => (h _ heX heI).2 ⟩⟩

中文:
定理 Indep.isBasis_iff_对任意_insert_dep
  条件: (hI : M.Indep I) (hIX : I subseteq X)
  证明: by
  rw [IsBasis]; rw [maximal_iff_forall_insert (fun I J hI hIJ => ⟨hI.1.subset hIJ]; rw [hIJ.trans hI.2⟩)]
  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, mem_sdiff, and_imp,
    Dep, hI.subset_ground]
  exact ⟨fun h e heX heI => ⟨fun hi => h.1 e heI hi heX, h.2 heX⟩,
    fun h => ⟨fun e heI hi heX => (h e heX heI).1 hi,
      fun e heX => (em (e in I)).elim (fun h => hI.subset_ground h) fun heI => (h _ heX heI).2 ⟩⟩

Depends on / 依赖: IsBasis, and_imp, and_self, and_true, hI.subset_ground, hIJ.trans, insert_subset_iff, maximal_iff_forall_insert, mem_sdiff, not_and, subset, subset_ground, true_and
-/
theorem Indep.isBasis_iff_forall_insert_dep (hI : M.Indep I) (hIX : I subseteq X) :
    M.IsBasis I X ↔ forall e in X \ I, M.Dep (insert e I) := by
  rw [IsBasis]; rw [maximal_iff_forall_insert (fun I J hI hIJ => ⟨hI.1.subset hIJ]; rw [hIJ.trans hI.2⟩)]
  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, mem_sdiff, and_imp,
    Dep, hI.subset_ground]
  exact ⟨fun h e heX heI => ⟨fun hi => h.1 e heI hi heX, h.2 heX⟩,
    fun h => ⟨fun e heI hi heX => (h e heX heI).1 hi,
      fun e heX => (em (e in I)).elim (fun h => hI.subset_ground h) fun heI => (h _ heX heI).2 ⟩⟩

/--
theorem `Indep.isBasis_of_forall_insert` / 定理 `Indep.isBasis_of_forall_insert`

English:
theorem Indep.isBasis_of_forall_insert
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: (hI.isBasis_iff_forall_insert_dep hIX).mpr he

中文:
定理 Indep.isBasis_of_对任意_insert
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: (hI.isBasis_iff_forall_insert_dep hIX).mpr he

Depends on / 依赖: hI.isBasis_iff_forall_insert_dep, isBasis_iff_forall_insert_dep
-/
theorem Indep.isBasis_of_forall_insert (hI : M.Indep I) (hIX : I subseteq X)
    (he : forall e in X \ I, M.Dep (insert e I)) : M.IsBasis I X :=
  (hI.isBasis_iff_forall_insert_dep hIX).mpr he

/--
theorem `Indep.isBasis_insert_iff` / 定理 `Indep.isBasis_insert_iff`

English:
theorem Indep.isBasis_insert_iff
  given: (hI : M.Indep I)
  proof: by
  simp_rw [hI.isBasis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff,
    and_iff_left hI.subset_ground, mem_sdiff, mem_insert_iff, or_and_right, and_not_self,
    or_false, and_imp, forall_eq]
  tauto

中文:
定理 Indep.isBasis_insert_iff
  条件: (hI : M.Indep I)
  证明: by
  simp_rw [hI.isBasis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff,
    and_iff_left hI.subset_ground, mem_sdiff, mem_insert_iff, or_and_right, and_not_self,
    or_false, and_imp, forall_eq]
  tauto

Depends on / 依赖: and_iff_left, and_imp, and_not_self, dep_iff, forall_eq, hI.isBasis_iff_forall_insert_dep, hI.subset_ground, insert_subset_iff, isBasis_iff_forall_insert_dep, mem_insert_iff, mem_sdiff, or_and_right, or_false, simp_rw, subset_ground, subset_insert
-/
theorem Indep.isBasis_insert_iff (hI : M.Indep I) :
    M.IsBasis I (insert e I) ↔ M.Dep (insert e I) ∨ e in I := by
  simp_rw [hI.isBasis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff,
    and_iff_left hI.subset_ground, mem_sdiff, mem_insert_iff, or_and_right, and_not_self,
    or_false, and_imp, forall_eq]
  tauto

/--
theorem `IsBasis.iUnion_isBasis_iUnion` / 定理 `IsBasis.iUnion_isBasis_iUnion`

English:
theorem IsBasis.iUnion_isBasis_iUnion
  statement: {ι : Type _} (X I : ι -> Set α)
  proof: by
  refine h_ind.isBasis_of_forall_insert
    (iUnion_subset (fun i => (hI i).subset.trans (subset_iUnion _ _))) ?_
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e in X i)⟩⟩, he'⟩
  rw [mem_iUnion]; rw [not_exists] at he'
  refine ((hI i).insert_dep ⟨hes, he' _⟩).superset (insert_subset_insert (subset_iUnion _ _)) ?_
  rw [insert_subset_iff]; rw [iUnion_subset_iff]; rw [and_iff_left (fun i => (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes

中文:
定理 是基.iUnion_isBasis_iUnion
  结论: {ι : 类型 _} (X I : ι -> 集合 α)
  证明: by
  refine h_ind.isBasis_of_forall_insert
    (iUnion_subset (fun i => (hI i).subset.trans (subset_iUnion _ _))) ?_
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e in X i)⟩⟩, he'⟩
  rw [mem_iUnion]; rw [not_exists] at he'
  refine ((hI i).insert_dep ⟨hes, he' _⟩).superset (insert_subset_insert (subset_iUnion _ _)) ?_
  rw [insert_subset_iff]; rw [iUnion_subset_iff]; rw [and_iff_left (fun i => (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes

Depends on / 依赖: and_iff_left, h_ind, h_ind.isBasis_of_forall_insert, iUnion_subset, iUnion_subset_iff, indep.subset_ground, insert_dep, insert_subset_iff, insert_subset_insert, isBasis_of_forall_insert, mem_iUnion, not_exists, subset, subset.trans, subset_ground, subset_iUnion, superset
-/
theorem IsBasis.iUnion_isBasis_iUnion {ι : Type _} (X I : ι -> Set α)
    (hI : forall i, M.IsBasis (I i) (X i)) (h_ind : M.Indep (⋃ i, I i)) :
    M.IsBasis (⋃ i, I i) (⋃ i, X i) := by
  refine h_ind.isBasis_of_forall_insert
    (iUnion_subset (fun i => (hI i).subset.trans (subset_iUnion _ _))) ?_
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e in X i)⟩⟩, he'⟩
  rw [mem_iUnion]; rw [not_exists] at he'
  refine ((hI i).insert_dep ⟨hes, he' _⟩).superset (insert_subset_insert (subset_iUnion _ _)) ?_
  rw [insert_subset_iff]; rw [iUnion_subset_iff]; rw [and_iff_left (fun i => (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes

/--
theorem `IsBasis.isBasis_iUnion` / 定理 `IsBasis.isBasis_iUnion`

English:
theorem IsBasis.isBasis_iUnion
  statement: {ι : Type _} [Nonempty ι] (X : ι -> Set α)
  proof: by
  convert! IsBasis.iUnion_isBasis_iUnion X (fun _ => I) (fun i => hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep

中文:
定理 是基.isBasis_iUnion
  结论: {ι : 类型 _} [非空 ι] (X : ι -> 集合 α)
  证明: by
  convert! IsBasis.iUnion_isBasis_iUnion X (fun _ => I) (fun i => hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep

Depends on / 依赖: Classical, Classical.arbitrary, IsBasis, IsBasis.iUnion_isBasis_iUnion, arbitrary, convert, iUnion_const, iUnion_isBasis_iUnion
-/
theorem IsBasis.isBasis_iUnion {ι : Type _} [Nonempty ι] (X : ι -> Set α)
    (hI : forall i, M.IsBasis I (X i)) : M.IsBasis I (⋃ i, X i) := by
  convert! IsBasis.iUnion_isBasis_iUnion X (fun _ => I) (fun i => hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep

/--
theorem `IsBasis.isBasis_sUnion` / 定理 `IsBasis.isBasis_sUnion`

English:
theorem IsBasis.isBasis_sUnion
  statement: {Xs : Set (Set α)} (hne : Xs.Nonempty)
  proof: by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact IsBasis.isBasis_iUnion _ fun X => h X X.prop

中文:
定理 是基.isBasis_sUnion
  结论: {Xs : 集合 (集合 α)} (hne : Xs.非空)
  证明: by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact IsBasis.isBasis_iUnion _ fun X => h X X.prop

Depends on / 依赖: Iff.mpr, IsBasis, IsBasis.isBasis_iUnion, X.prop, isBasis_iUnion, nonempty_coe_sort, sUnion_eq_iUnion
-/
theorem IsBasis.isBasis_sUnion {Xs : Set (Set α)} (hne : Xs.Nonempty)
    (h : forall X in Xs, M.IsBasis I X) : M.IsBasis I (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact IsBasis.isBasis_iUnion _ fun X => h X X.prop

/--
theorem `Indep.isBasis_setOfPred_insert_isBasis` / 定理 `Indep.isBasis_setOfPred_insert_isBasis`

English:
theorem Indep.isBasis_setOfPred_insert_isBasis
  given: (hI : M.Indep I)
  proof: by
  refine hI.isBasis_of_forall_insert (fun e he => (?_ : M.IsBasis _ _))
    (fun e he => ⟨fun hu => he.2 ?_, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.isBasis_self
  simpa using (hu.eq_of_isBasis he.1).symm

@[deprecated (since := "2026-07-09")]
alias Indep.isBasis_setOf_insert_isBasis := Indep.isBasis_setOfPred_insert_isBasis

中文:
定理 Indep.isBasis_setOfPred_insert_isBasis
  条件: (hI : M.Indep I)
  证明: by
  refine hI.isBasis_of_forall_insert (fun e he => (?_ : M.IsBasis _ _))
    (fun e he => ⟨fun hu => he.2 ?_, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.isBasis_self
  simpa using (hu.eq_of_isBasis he.1).symm

@[deprecated (since := "2026-07-09")]
alias Indep.isBasis_setOf_insert_isBasis := Indep.isBasis_setOfPred_insert_isBasis

Depends on / 依赖: IsBasis, M.IsBasis, eq_of_isBasis, hI.isBasis_of_forall_insert, hI.isBasis_self, hu.eq_of_isBasis, insert_eq_of_mem, isBasis_of_forall_insert, isBasis_self, subset_ground
-/
theorem Indep.isBasis_setOfPred_insert_isBasis (hI : M.Indep I) :
    M.IsBasis I {x | M.IsBasis I (insert x I)} := by
  refine hI.isBasis_of_forall_insert (fun e he => (?_ : M.IsBasis _ _))
    (fun e he => ⟨fun hu => he.2 ?_, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.isBasis_self
  simpa using (hu.eq_of_isBasis he.1).symm

@[deprecated (since := "2026-07-09")]
alias Indep.isBasis_setOf_insert_isBasis := Indep.isBasis_setOfPred_insert_isBasis

/--
theorem `IsBasis.union_isBasis_union` / 定理 `IsBasis.union_isBasis_union`

English:
theorem IsBasis.union_isBasis_union
  statement: (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
  proof: by
  rw [union_eq_iUnion]; rw [union_eq_iUnion]
  refine IsBasis.iUnion_isBasis_iUnion _ _ ?_ ?_
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_iUnion]

中文:
定理 是基.union_isBasis_union
  结论: (hIX : M.是基 I X) (hJY : M.是基 J Y)
  证明: by
  rw [union_eq_iUnion]; rw [union_eq_iUnion]
  refine IsBasis.iUnion_isBasis_iUnion _ _ ?_ ?_
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_iUnion]

Depends on / 依赖: Bool.forall_bool, IsBasis, IsBasis.iUnion_isBasis_iUnion, cond_false, cond_true, forall_bool, iUnion_isBasis_iUnion, union_eq_iUnion
-/
theorem IsBasis.union_isBasis_union (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
    (h : M.Indep (I union J)) : M.IsBasis (I union J) (X union Y) := by
  rw [union_eq_iUnion]; rw [union_eq_iUnion]
  refine IsBasis.iUnion_isBasis_iUnion _ _ ?_ ?_
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_iUnion]

/--
theorem `IsBasis.isBasis_union` / 定理 `IsBasis.isBasis_union`

English:
theorem IsBasis.isBasis_union
  given: (hIX : M.IsBasis I X) (hIY : M.IsBasis I Y)
  proof: by
  convert! hIX.union_isBasis_union hIY _ <;> rw [union_self]; exact hIX.indep

中文:
定理 是基.isBasis_union
  条件: (hIX : M.是基 I X) (hIY : M.是基 I Y)
  证明: by
  convert! hIX.union_isBasis_union hIY _ <;> rw [union_self]; exact hIX.indep

Depends on / 依赖: convert, hIX.indep, hIX.union_isBasis_union, union_isBasis_union, union_self
-/
theorem IsBasis.isBasis_union (hIX : M.IsBasis I X) (hIY : M.IsBasis I Y) :
    M.IsBasis I (X union Y) := by
  convert! hIX.union_isBasis_union hIY _ <;> rw [union_self]; exact hIX.indep

/--
theorem `IsBasis.isBasis_union_of_subset` / 定理 `IsBasis.isBasis_union_of_subset`

English:
theorem IsBasis.isBasis_union_of_subset
  given: (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I subseteq J)
  proof: by
  convert! hJ.isBasis_self.union_isBasis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption

中文:
定理 是基.isBasis_union_of_subset
  条件: (hI : M.是基 I X) (hJ : M.Indep J) (hIJ : I subseteq J)
  证明: by
  convert! hJ.isBasis_self.union_isBasis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption

Depends on / 依赖: convert, hJ.isBasis_self.union_isBasis_union, isBasis_self, union_eq_self_of_subset_right, union_isBasis_union
-/
theorem IsBasis.isBasis_union_of_subset (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I subseteq J) :
    M.IsBasis J (J union X) := by
  convert! hJ.isBasis_self.union_isBasis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption

/--
theorem `IsBasis.insert_isBasis_insert` / 定理 `IsBasis.insert_isBasis_insert`

English:
theorem IsBasis.insert_isBasis_insert
  given: (hI : M.IsBasis I X) (h : M.Indep (insert e I))
  proof: by
  simp_rw [← union_singleton] at *
  exact hI.union_isBasis_union (h.subset subset_union_right).isBasis_self h

中文:
定理 是基.insert_isBasis_insert
  条件: (hI : M.是基 I X) (h : M.Indep (insert e I))
  证明: by
  simp_rw [← union_singleton] at *
  exact hI.union_isBasis_union (h.subset subset_union_right).isBasis_self h

Depends on / 依赖: h.subset, hI.union_isBasis_union, isBasis_self, simp_rw, subset, subset_union_right, union_isBasis_union, union_singleton
-/
theorem IsBasis.insert_isBasis_insert (hI : M.IsBasis I X) (h : M.Indep (insert e I)) :
    M.IsBasis (insert e I) (insert e X) := by
  simp_rw [← union_singleton] at *
  exact hI.union_isBasis_union (h.subset subset_union_right).isBasis_self h

/--
theorem `IsBase.isBase_of_isBasis_superset` / 定理 `IsBase.isBase_of_isBasis_superset`

English:
theorem IsBase.isBase_of_isBasis_superset
  given: (hB : M.IsBase B) (hBX : B subseteq X) (hIX : M.IsBasis I X)
  proof: by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_isBase h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

中文:
定理 IsBase.isBase_of_isBasis_superset
  条件: (hB : M.IsBase B) (hBX : B subseteq X) (hIX : M.是基 I X)
  证明: by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_isBase h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

Depends on / 依赖: exists_insert_of_not_isBase, hIX.indep.exists_insert_of_not_isBase, hIX.mem_of_insert_indep, mem_of_insert_indep
-/
theorem IsBase.isBase_of_isBasis_superset (hB : M.IsBase B) (hBX : B subseteq X) (hIX : M.IsBasis I X) :
    M.IsBase I := by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_isBase h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

/--
theorem `Indep.exists_isBase_subset_union_isBase` / 定理 `Indep.exists_isBase_subset_union_isBase`

English:
theorem Indep.exists_isBase_subset_union_isBase
  given: (hI : M.Indep I) (hB : M.IsBase B)
  proof: by
obtain ⟨B', hB', hIB'⟩ := hI.subset_isBasis_of_subset subset_union_left (t := B)
  exact ⟨B', hB.isBase_of_isBasis_superset subset_union_right hB', hIB', hB'.subset⟩

中文:
定理 Indep.存在_isBase_subset_union_isBase
  条件: (hI : M.Indep I) (hB : M.IsBase B)
  证明: by
obtain ⟨B', hB', hIB'⟩ := hI.subset_isBasis_of_subset subset_union_left (t := B)
  exact ⟨B', hB.isBase_of_isBasis_superset subset_union_right hB', hIB', hB'.subset⟩

Depends on / 依赖: hB.isBase_of_isBasis_superset, hI.subset_isBasis_of_subset, isBase_of_isBasis_superset, subset, subset_isBasis_of_subset, subset_union_left, subset_union_right
-/
theorem Indep.exists_isBase_subset_union_isBase (hI : M.Indep I) (hB : M.IsBase B) :
    exists B', M.IsBase B' ∧ I subseteq B' ∧ B' subseteq I union B := by
obtain ⟨B', hB', hIB'⟩ := hI.subset_isBasis_of_subset subset_union_left (t := B)
  exact ⟨B', hB.isBase_of_isBasis_superset subset_union_right hB', hIB', hB'.subset⟩

/--
theorem `IsBasis.inter_eq_of_subset_indep` / 定理 `IsBasis.inter_eq_of_subset_indep`

English:
theorem IsBasis.inter_eq_of_subset_indep
  given: (hIX : M.IsBasis I X) (hIJ : I subseteq J) (hJ : M.Indep J)
  proof: (subset_inter hIJ hIX.subset).antisymm'
  (fun _ he => hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ)))

中文:
定理 是基.inter_eq_of_subset_indep
  条件: (hIX : M.是基 I X) (hIJ : I subseteq J) (hJ : M.Indep J)
  证明: (subset_inter hIJ hIX.subset).antisymm'
  (fun _ he => hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ)))

Depends on / 依赖: antisymm, hIX.mem_of_insert_indep, hIX.subset, hJ.subset, insert_subset, mem_of_insert_indep, subset, subset_inter
-/
theorem IsBasis.inter_eq_of_subset_indep (hIX : M.IsBasis I X) (hIJ : I subseteq J) (hJ : M.Indep J) :
    J inter X = I :=
(subset_inter hIJ hIX.subset).antisymm'
  (fun _ he => hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ)))

/--
theorem `IsBasis'.inter_eq_of_subset_indep` / 定理 `IsBasis'.inter_eq_of_subset_indep`

English:
theorem IsBasis'.inter_eq_of_subset_indep
  given: (hI : M.IsBasis' I X) (hIJ : I subseteq J) (hJ : M.Indep J)
  proof: by
  rw [← hI.isBasis_inter_ground.inter_eq_of_subset_indep hIJ hJ]; rw [inter_comm X]; rw [← inter_assoc]; rw [inter_eq_self_of_subset_left hJ.subset_ground]

中文:
定理 是基'.inter_eq_of_subset_indep
  条件: (hI : M.是基' I X) (hIJ : I subseteq J) (hJ : M.Indep J)
  证明: by
  rw [← hI.isBasis_inter_ground.inter_eq_of_subset_indep hIJ hJ]; rw [inter_comm X]; rw [← inter_assoc]; rw [inter_eq_self_of_subset_left hJ.subset_ground]
-/
theorem IsBasis'.inter_eq_of_subset_indep (hI : M.IsBasis' I X) (hIJ : I subseteq J) (hJ : M.Indep J) :
    J inter X = I := by
  rw [← hI.isBasis_inter_ground.inter_eq_of_subset_indep hIJ hJ]; rw [inter_comm X]; rw [← inter_assoc]; rw [inter_eq_self_of_subset_left hJ.subset_ground]

/--
theorem `IsBase.isBasis_of_subset` / 定理 `IsBase.isBasis_of_subset`

English:
theorem IsBase.isBasis_of_subset
  given: (hX : X subseteq M.E := by aesop_mat) (hB : M.IsBase B) (hBX : B subseteq X)
  proof: by
  rw [isBasis_iff]; rw [and_iff_right hB.indep]; rw [and_iff_right hBX]
  exact fun J hJ hBJ _ => hB.eq_of_subset_indep hJ hBJ

中文:
定理 IsBase.isBasis_of_subset
  条件: (hX : X subseteq M.E := by aesop_mat) (hB : M.IsBase B) (hBX : B subseteq X)
  证明: by
  rw [isBasis_iff]; rw [and_iff_right hB.indep]; rw [and_iff_right hBX]
  exact fun J hJ hBJ _ => hB.eq_of_subset_indep hJ hBJ

Depends on / 依赖: IsBase, IsBasis, M.IsBase, M.IsBasis, aesop_mat, and_iff_right, eq_of_subset_indep, hB.eq_of_subset_indep, hB.indep, isBasis_iff, subseteq
-/
theorem IsBase.isBasis_of_subset (hX : X subseteq M.E := by aesop_mat) (hB : M.IsBase B) (hBX : B subseteq X) :
    M.IsBasis B X := by
  rw [isBasis_iff]; rw [and_iff_right hB.indep]; rw [and_iff_right hBX]
  exact fun J hJ hBJ _ => hB.eq_of_subset_indep hJ hBJ

/--
theorem `exists_isBasis_disjoint_isBasis_of_subset` / 定理 `exists_isBasis_disjoint_isBasis_of_subset`

English:
theorem exists_isBasis_disjoint_isBasis_of_subset
  statement: (M : Matroid α) {X Y : Set α} (hXY : X subseteq Y)
  proof: by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_isBasis_subset_isBasis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_sdiff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
exact heI hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

中文:
定理 存在_isBasis_disjoint_isBasis_of_subset
  结论: (M : 拟阵 α) {X Y : 集合 α} (hXY : X subseteq Y)
  证明: by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_isBasis_subset_isBasis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_sdiff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
exact heI hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

Depends on / 依赖: Disjoint, IsBasis, M.IsBasis, M.exists_isBasis_subset_isBasis, aesop_mat, disjoint_iff_forall_ne, exists_isBasis_subset_isBasis, hI.mem_of_insert_indep, indep.subset, insert_subset, mem_of_insert_indep, subset, union_eq_self_of_subset_left, union_sdiff_self
-/
theorem exists_isBasis_disjoint_isBasis_of_subset (M : Matroid α) {X Y : Set α} (hXY : X subseteq Y)
    (hY : Y subseteq M.E := by aesop_mat) : exists I J, M.IsBasis I X ∧ M.IsBasis (I union J) Y ∧ Disjoint X J := by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_isBasis_subset_isBasis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_sdiff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
exact heI hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

end IsBasis

section Finite

/--
theorem `finite_setOfPred_matroid` / 定理 `finite_setOfPred_matroid`

English:
theorem finite_setOfPred_matroid
  given: {E : Set α} (hE : E.Finite)
  proof: by
  set f : Matroid α -> Set α × (Set (Set α)) := fun M => ⟨M.E, {B | M.IsBase B}⟩
  have hf : f.Injective := by
    refine fun M M' hMM' => ?_
    rw [Prod.mk.injEq]; rw [and_comm]; rw [Set.ext_iff]; rw [and_comm] at hMM'
    exact ext_isBase hMM'.1 (fun B _ => hMM'.2 B)
  rw [← Set.finite_image_iff hf.injOn]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E subseteq E, rfl⟩
  simp only [Set.mem_prod, Set.mem_ofPred_eq]
  exact ⟨hE, fun B hB => hB.subset_ground.trans hE⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid := finite_setOfPred_matroid

中文:
定理 finite_setOfPred_matroid
  条件: {E : 集合 α} (hE : E.有限)
  证明: by
  set f : Matroid α -> Set α × (Set (Set α)) := fun M => ⟨M.E, {B | M.IsBase B}⟩
  have hf : f.Injective := by
    refine fun M M' hMM' => ?_
    rw [Prod.mk.injEq]; rw [and_comm]; rw [Set.ext_iff]; rw [and_comm] at hMM'
    exact ext_isBase hMM'.1 (fun B _ => hMM'.2 B)
  rw [← Set.finite_image_iff hf.injOn]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E subseteq E, rfl⟩
  simp only [Set.mem_prod, Set.mem_ofPred_eq]
  exact ⟨hE, fun B hB => hB.subset_ground.trans hE⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid := finite_setOfPred_matroid

Depends on / 依赖: Injective, IsBase, M.IsBase, Matroid, Prod.mk.injEq, Set.ext_iff, Set.finite_image_iff, Set.mem_ofPred_eq, Set.mem_prod, and_comm, ext_iff, ext_isBase, f.Injective, finite_image_iff, finite_subsets, hB.subset_ground.trans, hE.finite_subsets.finite_subsets, hE.finite_subsets.prod, hf.injOn, mem_ofPred_eq
-/
theorem finite_setOfPred_matroid {E : Set α} (hE : E.Finite) :
    {M : Matroid α | M.E subseteq E}.Finite := by
  set f : Matroid α -> Set α × (Set (Set α)) := fun M => ⟨M.E, {B | M.IsBase B}⟩
  have hf : f.Injective := by
    refine fun M M' hMM' => ?_
    rw [Prod.mk.injEq]; rw [and_comm]; rw [Set.ext_iff]; rw [and_comm] at hMM'
    exact ext_isBase hMM'.1 (fun B _ => hMM'.2 B)
  rw [← Set.finite_image_iff hf.injOn]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E subseteq E, rfl⟩
  simp only [Set.mem_prod, Set.mem_ofPred_eq]
  exact ⟨hE, fun B hB => hB.subset_ground.trans hE⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid := finite_setOfPred_matroid

/--
theorem `finite_setOfPred_matroid'` / 定理 `finite_setOfPred_matroid'`

English:
theorem finite_setOfPred_matroid'
  given: {E : Set α} (hE : E.Finite)
  statement: {M : Matroid α | M.E = E}.Finite
  proof: (finite_setOfPred_matroid hE).subset (fun M => by rintro rfl; exact subset_refl M.E)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid' := finite_setOfPred_matroid'

中文:
定理 finite_setOfPred_matroid'
  条件: {E : 集合 α} (hE : E.有限)
  结论: {M : 拟阵 α | M.E = E}.有限
  证明: (finite_setOfPred_matroid hE).subset (fun M => by rintro rfl; exact subset_refl M.E)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid' := finite_setOfPred_matroid'

Depends on / 依赖: finite_setOfPred_matroid, subset, subset_refl
-/
theorem finite_setOfPred_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E = E}.Finite :=
  (finite_setOfPred_matroid hE).subset (fun M => by rintro rfl; exact subset_refl M.E)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid' := finite_setOfPred_matroid'

end Finite

end Matroid
