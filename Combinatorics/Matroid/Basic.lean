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

/-- A predicate `P` on sets satisfies the **exchange property** if,
for all `X` and `Y` satisfying `P` and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that
swapping `a` for `b` in `X` maintains `P`. -/
/-
**Matroid.ExchangeProperty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matroid.ExchangeProperty {α : Type*} (P : Set α -> Prop) : Prop
参数：P : Set α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate `P` on sets satisfies the **exchange property** if,
for all `X` and `Y` satisfying `P` and all `a ∈ X \ Y`, there exists `b ∈ Y \ X`
 so that
swapping `a` for `b` in `X` maintains `P`.
-/
def Matroid.ExchangeProperty {α : Type*} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A set `X` has the maximal subset property for a predicate `P` if every subset of `X` satisfying
`P` is contained in a maximal subset of `X` satisfying `P`. -/
/-
**Matroid.ExistsMaximalSubsetProperty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matroid.ExistsMaximalSubsetProperty {α : Type*} (P : Set α -> Prop) (X : S
et α) : Prop
参数：P : Set α -> Prop；X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `X` has the maximal subset property for a predicate `P` if every subset of
 `X` satisfying
`P` is contained in a maximal subset of `X` satisfying `P`.
-/
def Matroid.ExistsMaximalSubsetProperty {α : Type*} (P : Set α → Prop) (X : Set α) : Prop :=
  ∀ I, P I → I ⊆ X → ∃ J, I ⊆ J ∧ Maximal (fun K ↦ P K ∧ K ⊆ X) J

/-- A `Matroid α` is a ground set `E` of type `Set α`, and a nonempty collection of its subsets
satisfying the exchange property and the maximal subset property. Each such set is called a
`Base` of `M`. An `Indep`endent set is just a set contained in a base, but we include this
predicate as a structure field for better definitional properties.

In most cases, using this definition directly is not the best way to construct a matroid,
since it requires specifying both the bases and independent sets. If the bases are known,
use `Matroid.ofBase` or a variant. If just the independent sets are known,
define an `IndepMatroid`, and then use `IndepMatroid.matroid`.
-/
/-
**Matroid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Matroid α` is a ground set `E` of type `Set α`, and a nonempty collection of 
its subsets
satisfying the exchange property and the maximal subset property. Each such set 
is called a
`Base` of `M`. An `Indep`endent set is just a set contained in a base, but we in
clude this
predicate as a structure field for better definitional properties.

In most cases, using this definition directly is not the best way to construct a
 matroid,
since it requires specifying both the bases and independent sets. If the bases a
re known,
use `Matroid.ofBase` or a variant. If just the independent sets are known,
define an `IndepMatroid`, and then use `IndepMatroid.matroid`.
-/
structure Matroid (α : Type*) where
  /-- `M` has a ground set `E`. -/
  (E : Set α)
  /-- `M` has a predicate `Base` defining its bases. -/
  (IsBase : Set α → Prop)
  /-- `M` has a predicate `Indep` defining its independent sets. -/
  (Indep : Set α → Prop)
  /-- The `Indep`endent sets are those contained in `Base`s. -/
  (indep_iff' : ∀ ⦃I⦄, Indep I ↔ ∃ B, IsBase B ∧ I ⊆ B)
  /-- There is at least one `Base`. -/
  (exists_isBase : ∃ B, IsBase B)
  /-- For any bases `B`, `B'` and `e ∈ B \ B'`, there is some `f ∈ B' \ B` for which `B-e+f`
  is a base. -/
  (isBase_exchange : Matroid.ExchangeProperty IsBase)
  /-- Every independent subset `I` of a set `X` for is contained in a maximal independent
  subset of `X`. -/
  (maximality : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  /-- Every base is contained in the ground set. -/
  (subset_ground : ∀ B, IsBase B → B ⊆ E)

attribute [local ext] Matroid

namespace Matroid

variable {α : Type*} {M : Matroid α}

/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Matroid α) : Nonempty {B // M.IsBase B} :=
  nonempty_subtype.2 M.exists_isBase

/-- Typeclass for a matroid having finite ground set. Just a wrapper for `M.E.Finite`. -/
/-
**Matroid.Finite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a matroid having finite ground set. Just a wrapper for `M.E.Finite
`.
-/
@[mk_iff] protected class Finite (M : Matroid α) : Prop where
  /-- The ground set is finite -/
  (ground_finite : M.E.Finite)

/-- Typeclass for a matroid having nonempty ground set. Just a wrapper for `M.E.Nonempty`. -/
/-
**Matroid.Nonempty** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a matroid having nonempty ground set. Just a wrapper for `M.E.None
mpty`.
-/
protected class Nonempty (M : Matroid α) : Prop where
  /-- The ground set is nonempty -/
  (ground_nonempty : M.E.Nonempty)
/-
**Matroid.ground_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_nonempty (M : Matroid α) [M.Nonempty] : M.E.Nonempty
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Nonempty.ground_nonempty`：∀ {α : Type u_1} {M : Matroid α} [self
 : M.Nonempty], M.E.Nonempty
-/
theorem ground_nonempty (M : Matroid α) [M.Nonempty] : M.E.Nonempty :=
  Nonempty.ground_nonempty
/-
**Matroid.ground_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_nonempty_iff (M : Matroid α) : M.E.Nonempty ↔ M.Nonempty
参数：M : Matroid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ground_nonempty_iff (M : Matroid α) : M.E.Nonempty ↔ M.Nonempty :=
  ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩
/-
**Matroid.nonempty_type** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：nonempty_type (M : Matroid α) [h : M.Nonempty] : Nonempty α
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ground_nonempty`：ground_nonempty (M : Matroid α) [M.Nonempty] : 
M.E.Nonempty
-/
lemma nonempty_type (M : Matroid α) [h : M.Nonempty] : Nonempty α :=
  ⟨M.ground_nonempty.some⟩
/-
**Matroid.ground_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_finite (M : Matroid α) [M.Finite] : M.E.Finite
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Finite.ground_finite`：∀ {α : Type u_1} {M : Matroid α} [self : M
.Finite], M.E.Finite
-/
theorem ground_finite (M : Matroid α) [M.Finite] : M.E.Finite :=
  Finite.ground_finite
/-
**Matroid.set_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X subseteq M.E
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.ground_finite`：ground_finite (M : Matroid α) [M.Finite] : M.E.Fi
nite
-/
theorem set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E := by aesop) : X.Finite :=
  M.ground_finite.subset hX
/-
**Matroid.finite_of_finite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：finite_of_finite [Finite α] {M : Matroid α} : M.Finite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
instance finite_of_finite [Finite α] {M : Matroid α} : M.Finite :=
  ⟨Set.toFinite _⟩

/-- A `RankFinite` matroid is one whose bases are finite -/
/-
**Matroid.RankFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `RankFinite` matroid is one whose bases are finite
-/
@[mk_iff] class RankFinite (M : Matroid α) : Prop where
  /-- There is a finite base -/
  exists_finite_isBase : ∃ B, M.IsBase B ∧ B.Finite
/-
**Matroid.rankFinite_of_finite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：rankFinite_of_finite (M : Matroid α) [M.Finite] : RankFinite M
参数：M : Matroid α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Matroid.set_finite`：set_finite (M : Matroid α) [M.Finite] (X : Set α) (h
X : X subseteq M.E
· 使用定理 `Matroid.subset_ground`：∀ {α : Type u_1} (self : Matroid α) (B : Set α), 
self.IsBase B → B ⊆ self.E
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
-/
instance rankFinite_of_finite (M : Matroid α) [M.Finite] : RankFinite M :=
  ⟨M.exists_isBase.imp (fun B hB ↦ ⟨hB, M.set_finite B (M.subset_ground _ hB)⟩)⟩

/-- An `RankInfinite` matroid is one whose bases are infinite. -/
/-
**Matroid.RankInfinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `RankInfinite` matroid is one whose bases are infinite.
-/
@[mk_iff] class RankInfinite (M : Matroid α) : Prop where
  /-- There is an infinite base -/
  exists_infinite_isBase : ∃ B, M.IsBase B ∧ B.Infinite

/-- A `RankPos` matroid is one whose bases are nonempty. -/
/-
**Matroid.RankPos** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `RankPos` matroid is one whose bases are nonempty.
-/
@[mk_iff] class RankPos (M : Matroid α) : Prop where
  /-- The empty set isn't a base -/
  empty_not_isBase : ¬M.IsBase ∅
/-
**Matroid.rankPos_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：rankPos_nonempty {M : Matroid α} [M.RankPos] : M.Nonempty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Matroid.RankPos.empty_not_isBase`：∀ {α : Type u_1} {M : Matroid α} [self
 : M.RankPos], ¬M.IsBase ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.subset_ground`：∀ {α : Type u_1} (self : Matroid α) (B : Set α), 
self.IsBase B → B ⊆ self.E
-/
instance rankPos_nonempty {M : Matroid α} [M.RankPos] : M.Nonempty := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | ⟨e, heB⟩ := B.eq_empty_or_nonempty
  · exact False.elim <| RankPos.empty_not_isBase hB
  exact ⟨e, M.subset_ground B hB heB ⟩

section exchange
namespace ExchangeProperty

variable {IsBase : Set α → Prop} {B B' : Set α}

/-- A family of sets with the exchange property is an antichain. -/
/-
**Matroid.ExchangeProperty.antichain** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Exchange
Property`。
形式化陈述：antichain (exch : ExchangeProperty IsBase) (hB : IsBase B) (hB' : IsBase B
') (h : B subseteq B') : B = B'
参数：exch : ExchangeProperty IsBase；hB : IsBase B；hB' : IsBase B'；h : B subseteq B
'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A family of sets with the exchange property is an antichain.
-/
theorem antichain (exch : ExchangeProperty IsBase) (hB : IsBase B) (hB' : IsBase B') (h : B ⊆ B') :
    B = B' :=
  h.antisymm (fun x hx ↦ by_contra
    (fun hxB ↦ let ⟨_, hy, _⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; hy.2 <| h hy.1))
/-
**Matroid.ExchangeProperty.encard_sdiff_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.ExchangeProperty`。
形式化陈述：encard_sdiff_le_aux {B₁ B₂ : Set α} (exch : ExchangeProperty IsBase) (hB₁ 
: IsBase B₁) (hB₂ : IsBase B₂) : (B₁ \ B₂).encard <= (B₂ \ B₁).encard
参数：exch : ExchangeProperty IsBase；hB₁ : IsBase B₁；hB₂ : IsBase B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ExchangeProperty.encard_sdiff_le_aux._unary`：∀ {α : Type u_1} {I
sBase : Set α → Prop} {B₁ : Set α},   Matroid.ExchangeProperty IsBase →     IsBa
se B₁ → ∀ (_x : (B₂ : Set α) ×' IsBase B₂…
-/
theorem encard_sdiff_le_aux {B₁ B₂ : Set α}
    (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    (B₁ \ B₂).encard ≤ (B₂ \ B₁).encard := by
  obtain (he | hinf | ⟨e, he, hcard⟩) :=
    (B₂ \ B₁).eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · rw [exch.antichain hB₂ hB₁ (sdiff_eq_empty.mp he)]
  · exact le_top.trans_eq hinf.symm
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  have : encard (insert f (B₂ \ {e}) \ B₁) < encard (B₂ \ B₁) := by
    rw [insert_sdiff_of_mem _ hf.1, sdiff_sdiff_comm]; exact hcard
  have hencard := encard_sdiff_le_aux exch hB₁ hB'
  rw [insert_sdiff_of_mem _ hf.1, sdiff_sdiff_comm, ← union_singleton, ← sdiff_sdiff,
    sdiff_sdiff_right, inter_singleton_eq_empty.mpr he.2, union_empty] at hencard
  rw [← encard_sdiff_singleton_add_one he, ← encard_sdiff_singleton_add_one hf]
  gcongr
termination_by (B₂ \ B₁).encard

@[deprecated (since := "2026-06-03")] alias encard_diff_le_aux := encard_sdiff_le_aux

variable {B₁ B₂ : Set α}

/-- For any two sets `B₁`, `B₂` in a family with the exchange property, the differences `B₁ \ B₂`
and `B₂ \ B₁` have the same `ℕ∞`-cardinality. -/
/-
**Matroid.ExchangeProperty.encard_sdiff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Ex
changeProperty`。
形式化陈述：encard_sdiff_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : 
IsBase B₂) : (B₁ \ B₂).encard = (B₂ \ B₁).encard
参数：exch : ExchangeProperty IsBase；hB₁ : IsBase B₁；hB₂ : IsBase B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Matroid.ExchangeProperty.encard_sdiff_le_aux`：encard_sdiff_le_aux {B₁ B₂
 : Set α} (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
 (B₁ \ B₂).encard <= (B₂ \ B₁).enc…

--- 原说明 ---
For any two sets `B₁`, `B₂` in a family with the exchange property, the differen
ces `B₁ \ B₂`
and `B₂ \ B₁` have the same `ℕ∞`-cardinality.
-/
theorem encard_sdiff_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  (encard_sdiff_le_aux exch hB₁ hB₂).antisymm (encard_sdiff_le_aux exch hB₂ hB₁)

@[deprecated (since := "2026-06-03")] alias encard_diff_eq := encard_sdiff_eq

/-- Any two sets `B₁`, `B₂` in a family with the exchange property have the same
`ℕ∞`-cardinality. -/
/-
**Matroid.ExchangeProperty.encard_isBase_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.E
xchangeProperty`。
形式化陈述：encard_isBase_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ :
 IsBase B₂) : B₁.encard = B₂.encard
参数：exch : ExchangeProperty IsBase；hB₁ : IsBase B₁；hB₂ : IsBase B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_sdiff_add_encard_inter`：encard_sdiff_add_encard_inter (s t : 
Set α) : (s \ t).encard + (s inter t).encard = s.encard
· 使用定理 `Matroid.ExchangeProperty.encard_sdiff_eq`：encard_sdiff_eq (exch : Exchan
geProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) : (B₁ \ B₂).encard = (B₂ 
\ B₁).encard
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
Any two sets `B₁`, `B₂` in a family with the exchange property have the same
`ℕ∞`-cardinality.
-/
theorem encard_isBase_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    B₁.encard = B₂.encard := by
  rw [← encard_sdiff_add_encard_inter B₁ B₂, exch.encard_sdiff_eq hB₁ hB₂, inter_comm,
    encard_sdiff_add_encard_inter]

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
  aesop $c* (config := {terminal := true})
  (rule_sets := [$(Lean.mkIdent `Matroid):ident]))

/- We add a number of trivial lemmas (deliberately specialized to statements in terms of the
  ground set of a matroid) to the ruleset `Matroid` for `aesop`. -/

variable {X Y : Set α} {e : α}

@[aesop unsafe 5% (rule_sets := [Matroid])]
/-
**Matroid.inter_right_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inter_right_subset_ground (hX : X ⊆ M.E) :
    X ∩ Y ⊆ M.E := inter_subset_left.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
/-
**Matroid.inter_left_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inter_left_subset_ground (hX : X ⊆ M.E) :
    Y ∩ X ⊆ M.E := inter_subset_right.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
/-
**Matroid.sdiff_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sdiff_subset_ground (hX : X ⊆ M.E) : X \ Y ⊆ M.E :=
  sdiff_subset.trans hX

@[deprecated (since := "2026-06-03")] alias diff_subset_ground := sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.ground_sdiff_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ground_sdiff_subset_ground : M.E \ X ⊆ M.E :=
  sdiff_subset_ground rfl.subset

@[deprecated (since := "2026-06-03")] alias ground_diff_subset_ground := ground_sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.singleton_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem singleton_subset_ground (he : e ∈ M.E) : {e} ⊆ M.E :=
  singleton_subset_iff.mpr he

@[aesop unsafe 5% (rule_sets := [Matroid])]
/-
**Matroid.subset_ground_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem subset_ground_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : X ⊆ M.E :=
  hXY.trans hY

@[aesop unsafe 5% (rule_sets := [Matroid])]
/-
**Matroid.mem_ground_of_mem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_ground_of_mem_of_subset (hX : X ⊆ M.E) (heX : e ∈ X) : e ∈ M.E :=
  hX heX

@[aesop safe (rule_sets := [Matroid])]
/-
**Matroid.insert_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem insert_subset_ground {e : α} {X : Set α} {M : Matroid α}
    (he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E :=
  insert_subset he hX

@[aesop safe (rule_sets := [Matroid])]
/-
**Matroid.ground_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ground_subset_ground {M : Matroid α} : M.E ⊆ M.E :=
  rfl.subset

attribute [aesop safe (rule_sets := [Matroid])] empty_subset union_subset iUnion_subset

end aesop

section IsBase

variable {B B₁ B₂ : Set α}

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.IsBase.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → B ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.subset_ground`：∀ {α : Type u_1} (self : Matroid α) (B : Set α), 
self.IsBase B → B ⊆ self.E
-/
theorem IsBase.subset_ground (hB : M.IsBase B) : B ⊆ M.E :=
  M.subset_ground B hB
/-
**Matroid.IsBase.exchange** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α} {e : α},   M.IsBase B₁ → 
M.IsBase B₂ → e ∈ B₁ \ B₂ → ∃ y ∈ B₂ \ B₁, M.IsBase (insert y (B₁ \ {e}))
参数：insert y (B₁ \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.isBase_exchange`：∀ {α : Type u_1} (self : Matroid α), Matroid.Ex
changeProperty self.IsBase
-/
theorem IsBase.exchange {e : α} (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.IsBase (insert y (B₁ \ {e})) :=
  M.isBase_exchange B₁ B₂ hB₁ hB₂ _ hx
/-
**Matroid.IsBase.exchange_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α} {e : α},   M.IsBase B₁ → 
M.IsBase B₂ → e ∈ B₁ → e ∉ B₂ → ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.IsBase (insert y (B₁ 
\ {e}))
参数：y ∈ B₂ ∧ y ∉ B₁；insert y (B₁ \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.IsBase.exchange`：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α
} {e : α},   M.IsBase B₁ → M.IsBase B₂ → e ∈ B₁ \ B₂ → ∃ y ∈ B₂ \ B₁, M.IsBase (
insert y (B₁ …
-/
theorem IsBase.exchange_mem {e : α}
    (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.IsBase (insert y (B₁ \ {e})) := by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩
/-
**Matroid.IsBase.eq_of_subset_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → B₁ ⊆ B₂ → B₁ = B₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ExchangeProperty.antichain`：antichain (exch : ExchangeProperty I
sBase) (hB : IsBase B) (hB' : IsBase B') (h : B subseteq B') : B = B'
· 使用定理 `Matroid.isBase_exchange`：∀ {α : Type u_1} (self : Matroid α), Matroid.Ex
changeProperty self.IsBase
-/
theorem IsBase.eq_of_subset_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hB₁B₂ : B₁ ⊆ B₂) :
    B₁ = B₂ :=
  M.isBase_exchange.antichain hB₁ hB₂ hB₁B₂
/-
**Matroid.IsBase.not_isBase_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B X : Set α}, M.IsBase B → X ⊂ B → ¬M.Is
Base X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
-/
theorem IsBase.not_isBase_of_ssubset {X : Set α} (hB : M.IsBase B) (hX : X ⊂ B) : ¬ M.IsBase X :=
  fun h ↦ hX.ne (h.eq_of_subset_isBase hB hX.subset)
/-
**Matroid.IsBase.insert_not_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e : α}, M.IsBase B → e ∉ B →
 ¬M.IsBase (insert e B)
参数：insert e B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.not_isBase_of_ssubset`：∀ {α : Type u_1} {M : Matroid α} {
B X : Set α}, M.IsBase B → X ⊂ B → ¬M.IsBase X
· 使用定理 `Set.ssubset_insert`：ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂
 insert a s
-/
theorem IsBase.insert_not_isBase {e : α} (hB : M.IsBase B) (heB : e ∉ B) :
    ¬ M.IsBase (insert e B) :=
  fun h ↦ h.not_isBase_of_ssubset (ssubset_insert heB) hB
/-
**Matroid.IsBase.encard_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → (B₁ \ B₂).encard = (B₂ \ B₁).encard
参数：B₁ \ B₂；B₂ \ B₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ExchangeProperty.encard_sdiff_eq`：encard_sdiff_eq (exch : Exchan
geProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) : (B₁ \ B₂).encard = (B₂ 
\ B₁).encard
· 使用定理 `Matroid.isBase_exchange`：∀ {α : Type u_1} (self : Matroid α), Matroid.Ex
changeProperty self.IsBase
-/
theorem IsBase.encard_sdiff_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  M.isBase_exchange.encard_sdiff_eq hB₁ hB₂

@[deprecated (since := "2026-06-03")] alias IsBase.encard_diff_comm := IsBase.encard_sdiff_comm
/-
**Matroid.IsBase.ncard_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → (B₁ \ B₂).ncard = (B₂ \ B₁).ncard
参数：B₁ \ B₂；B₂ \ B₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `Matroid.IsBase.encard_sdiff_comm`：∀ {α : Type u_1} {M : Matroid α} {B₁ B
₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → (B₁ \ B₂).encard = (B₂ \ B₁).encard
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBase.ncard_sdiff_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [ncard_def, hB₁.encard_sdiff_comm hB₂, ← ncard_def]

@[deprecated (since := "2026-06-03")] alias IsBase.ncard_diff_comm := IsBase.ncard_sdiff_comm
/-
**Matroid.IsBase.encard_eq_encard_of_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → B₁.encard = B₂.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.ExchangeProperty.encard_isBase_eq`：encard_isBase_eq (exch : Exch
angeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) : B₁.encard = B₂.encard
· 使用定理 `Matroid.isBase_exchange`：∀ {α : Type u_1} (self : Matroid α), Matroid.Ex
changeProperty self.IsBase
-/
theorem IsBase.encard_eq_encard_of_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    B₁.encard = B₂.encard := by
  rw [M.isBase_exchange.encard_isBase_eq hB₁ hB₂]
/-
**Matroid.IsBase.ncard_eq_ncard_of_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
ase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → B₁.ncard = B₂.ncard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `Matroid.IsBase.encard_eq_encard_of_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁.encard = B₂.encard
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBase.ncard_eq_ncard_of_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    B₁.ncard = B₂.ncard := by
  rw [ncard_def B₁, hB₁.encard_eq_encard_of_isBase hB₂, ← ncard_def]
/-
**Matroid.IsBase.finite_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B B' : Set α}, M.IsBase B → B.Finite → M
.IsBase B' → B'.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_iff_finite_of_encard_eq_encard`：finite_iff_finite_of_encard_e
q_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite
· 使用定理 `Matroid.IsBase.encard_eq_encard_of_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁.encard = B₂.encard
-/
theorem IsBase.finite_of_finite {B' : Set α}
    (hB : M.IsBase B) (h : B.Finite) (hB' : M.IsBase B') : B'.Finite :=
  (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_isBase hB')).mp h
/-
**Matroid.IsBase.infinite_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B B₁ : Set α}, M.IsBase B → B.Infinite →
 M.IsBase B₁ → B₁.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matroid.IsBase.finite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B B' 
: Set α}, M.IsBase B → B.Finite → M.IsBase B' → B'.Finite
-/
theorem IsBase.infinite_of_infinite (hB : M.IsBase B) (h : B.Infinite) (hB₁ : M.IsBase B₁) :
    B₁.Infinite := by
  contrapose! h; exact hB₁.finite_of_finite h hB
/-
**Matroid.IsBase.finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.RankFinite], M.IsBase B → 
B.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.RankFinite.exists_finite_isBase`：∀ {α : Type u_1} {M : Matroid α
} [self : M.RankFinite], ∃ B, M.IsBase B ∧ B.Finite
· 使用定理 `Matroid.IsBase.finite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B B' 
: Set α}, M.IsBase B → B.Finite → M.IsBase B' → B'.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsBase.finite [RankFinite M] (hB : M.IsBase B) : B.Finite :=
  let ⟨_, hB₀⟩ := ‹RankFinite M›.exists_finite_isBase
  hB₀.1.finite_of_finite hB₀.2 hB
/-
**Matroid.IsBase.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.RankInfinite], M.IsBase B 
→ B.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.RankInfinite.exists_infinite_isBase`：∀ {α : Type u_1} {M : Matro
id α} [self : M.RankInfinite], ∃ B, M.IsBase B ∧ B.Infinite
· 使用定理 `Matroid.IsBase.infinite_of_infinite`：∀ {α : Type u_1} {M : Matroid α} {B
 B₁ : Set α}, M.IsBase B → B.Infinite → M.IsBase B₁ → B₁.Infinite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsBase.infinite [RankInfinite M] (hB : M.IsBase B) : B.Infinite :=
  let ⟨_, hB₀⟩ := ‹RankInfinite M›.exists_infinite_isBase
  hB₀.1.infinite_of_infinite hB₀.2 hB
/-
**Matroid.empty_not_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：empty_not_isBase [h : RankPos M] : ¬M.IsBase ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.RankPos.empty_not_isBase`：∀ {α : Type u_1} {M : Matroid α} [self
 : M.RankPos], ¬M.IsBase ∅
-/
theorem empty_not_isBase [h : RankPos M] : ¬M.IsBase ∅ :=
  h.empty_not_isBase
/-
**Matroid.IsBase.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.RankPos], M.IsBase B → B.N
onempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Matroid.empty_not_isBase`：empty_not_isBase [h : RankPos M] : ¬M.IsBase ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBase.nonempty [RankPos M] (hB : M.IsBase B) : B.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact M.empty_not_isBase hB
/-
**Matroid.IsBase.rankPos_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → B.Nonempty → M.
RankPos
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.rankPos_iff`：∀ {α : Type u_1} (M : Matroid α), M.RankPos ↔ ¬M.Is
Base ∅
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem IsBase.rankPos_of_nonempty (hB : M.IsBase B) (h : B.Nonempty) : M.RankPos := by
  rw [rankPos_iff]
  intro he
  obtain rfl := he.eq_of_subset_isBase hB (empty_subset B)
  simp at h
/-
**Matroid.IsBase.rankFinite_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → B.Finite → M.Ra
nkFinite
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBase.rankFinite_of_finite (hB : M.IsBase B) (hfin : B.Finite) : RankFinite M :=
  ⟨⟨B, hB, hfin⟩⟩
/-
**Matroid.IsBase.rankInfinite_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
ase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → B.Infinite → M.
RankInfinite
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBase.rankInfinite_of_infinite (hB : M.IsBase B) (h : B.Infinite) : RankInfinite M :=
  ⟨⟨B, hB, h⟩⟩
/-
**Matroid.not_rankFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：not_rankFinite (M : Matroid α) [RankInfinite M] : ¬ RankFinite M
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.IsBase.infinite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M
.RankInfinite], M.IsBase B → B.Infinite
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
-/
theorem not_rankFinite (M : Matroid α) [RankInfinite M] : ¬ RankFinite M := by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite
/-
**Matroid.not_rankInfinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：not_rankInfinite (M : Matroid α) [RankFinite M] : ¬ RankInfinite M
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.IsBase.infinite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M
.RankInfinite], M.IsBase B → B.Infinite
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
-/
theorem not_rankInfinite (M : Matroid α) [RankFinite M] : ¬ RankInfinite M := by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite
/-
**Matroid.rankFinite_or_rankInfinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：rankFinite_or_rankInfinite (M : Matroid α) : RankFinite M ∨ RankInfinite M
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Matroid.IsBase.rankFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M.IsBase B → B.Finite → M.RankFinite
· 使用定理 `Matroid.IsBase.rankInfinite_of_infinite`：∀ {α : Type u_1} {M : Matroid α
} {B : Set α}, M.IsBase B → B.Infinite → M.RankInfinite
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
-/
theorem rankFinite_or_rankInfinite (M : Matroid α) : RankFinite M ∨ RankInfinite M :=
  let ⟨B, hB⟩ := M.exists_isBase
  B.finite_or_infinite.imp hB.rankFinite_of_finite hB.rankInfinite_of_infinite

@[simp]
/-
**Matroid.not_rankFinite_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：not_rankFinite_iff (M : Matroid α) : ¬ RankFinite M ↔ RankInfinite M
参数：M : Matroid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Matroid.rankFinite_or_rankInfinite`：rankFinite_or_rankInfinite (M : Matr
oid α) : RankFinite M ∨ RankInfinite M
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.not_rankInfinite`：not_rankInfinite (M : Matroid α) [RankFinite M
] : ¬ RankInfinite M
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Matroid.not_rankFinite`：not_rankFinite (M : Matroid α) [RankInfinite M] 
: ¬ RankFinite M
-/
theorem not_rankFinite_iff (M : Matroid α) : ¬ RankFinite M ↔ RankInfinite M :=
  M.rankFinite_or_rankInfinite.elim (fun h ↦ iff_of_false (by simpa) M.not_rankInfinite)
    fun h ↦ iff_of_true M.not_rankFinite h

@[simp]
/-
**Matroid.not_rankInfinite_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：not_rankInfinite_iff (M : Matroid α) : ¬ RankInfinite M ↔ RankFinite M
参数：M : Matroid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_rankFinite_iff`：not_rankFinite_iff (M : Matroid α) : ¬ RankF
inite M ↔ RankInfinite M
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_rankInfinite_iff (M : Matroid α) : ¬ RankInfinite M ↔ RankFinite M := by
  rw [← not_rankFinite_iff, not_not]
/-
**Matroid.IsBase.sdiff_finite_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → ((B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite)
参数：(B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_iff_finite_of_encard_eq_encard`：finite_iff_finite_of_encard_e
q_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite
· 使用定理 `Matroid.IsBase.encard_sdiff_comm`：∀ {α : Type u_1} {M : Matroid α} {B₁ B
₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → (B₁ \ B₂).encard = (B₂ \ B₁).encard
-/
theorem IsBase.sdiff_finite_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite :=
  finite_iff_finite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_finite_comm := IsBase.sdiff_finite_comm
/-
**Matroid.IsBase.sdiff_infinite_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B
₂ → ((B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite)
参数：(B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_iff_infinite_of_encard_eq_encard`：infinite_iff_infinite_of_
encard_eq_encard (h : s.encard = t.encard) : s.Infinite ↔ t.Infinite
· 使用定理 `Matroid.IsBase.encard_sdiff_comm`：∀ {α : Type u_1} {M : Matroid α} {B₁ B
₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → (B₁ \ B₂).encard = (B₂ \ B₁).encard
-/
theorem IsBase.sdiff_infinite_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite :=
  infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_infinite_comm := IsBase.sdiff_infinite_comm
/-
**Matroid.ext_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h : forall ⦃B⦄, B subse
teq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
参数：hE : M₁.E = M₂.E；h : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase 
B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ext`：∀ {α : Type u_1} {x y : Matroid α}, x.E = y.E → x.IsBase = 
y.IsBase → x.Indep = y.Indep → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.indep_iff'`：∀ {α : Type u_1} (self : Matroid α) ⦃I : Set α⦄, sel
f.Indep I ↔ ∃ B, self.IsBase B ∧ I ⊆ B
-/
theorem ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂ := by
  have h' : ∀ B, M₁.IsBase B ↔ M₂.IsBase B :=
    fun B ↦ ⟨fun hB ↦ (h hB.subset_ground).1 hB,
      fun hB ↦ (h <| hB.subset_ground.trans_eq hE.symm).2 hB⟩
  ext <;> simp [hE, M₁.indep_iff', M₂.indep_iff', h']
/-
**Matroid.ext_iff_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ext_iff_isBase {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ M₁.E = M₂.E ∧ forall ⦃B⦄, B
 subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
-/
theorem ext_iff_isBase {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.IsBase B ↔ M₂.IsBase B) :=
  ⟨fun h ↦ by simp [h], fun ⟨hE, h⟩ ↦ ext_isBase hE h⟩
/-
**Matroid.isBase_compl_iff_maximal_disjoint_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid`。
形式化陈述：isBase_compl_iff_maximal_disjoint_isBase (hB : B subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem isBase_compl_iff_maximal_disjoint_isBase (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase (M.E \ B) ↔ Maximal (fun I ↦ I ⊆ M.E ∧ ∃ B, M.IsBase B ∧ Disjoint I B) B := by
  simp_rw [maximal_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine ⟨fun h ↦ ⟨⟨_, h, disjoint_sdiff_right⟩,
    fun I hI B' ⟨hB', hIB'⟩ hBI ↦ hBI.antisymm ?_⟩, fun ⟨⟨B', hB', hBB'⟩,h⟩ ↦ ?_⟩
  · rw [hB'.eq_of_subset_isBase h, ← subset_compl_iff_disjoint_right, sdiff_eq, compl_inter,
      compl_compl] at hIB'
    · exact fun e he ↦ (hIB' he).elim (fun h' ↦ (h' (hI he)).elim) id
    rw [subset_sdiff, and_iff_right hB'.subset_ground, disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h sdiff_subset B' ⟨hB', disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_sdiff, hB, hBB']

end IsBase
section dep_indep

/-- A subset of `M.E` is `Dep`endent if it is not `Indep`endent . -/
/-
**Matroid.Dep** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：Dep (M : Matroid α) (D : Set α) : Prop
参数：M : Matroid α；D : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of `M.E` is `Dep`endent if it is not `Indep`endent .
-/
def Dep (M : Matroid α) (D : Set α) : Prop := ¬M.Indep D ∧ D ⊆ M.E

variable {B B' I J D X : Set α} {e f : α}
/-
**Matroid.indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：indep_iff : M.Indep I ↔ exists B, M.IsBase B ∧ I subseteq B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.indep_iff'`：∀ {α : Type u_1} (self : Matroid α) ⦃I : Set α⦄, sel
f.Indep I ↔ ∃ B, self.IsBase B ∧ I ⊆ B
-/
theorem indep_iff : M.Indep I ↔ ∃ B, M.IsBase B ∧ I ⊆ B :=
  M.indep_iff' (I := I)

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.setOfPred_indep_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：setOfPred_indep_eq (M : Matroid α) : {I | M.Indep I} = lowerClosure ({B | 
M.IsBase B})
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setOfPred_indep_eq (M : Matroid α) : {I | M.Indep I} = lowerClosure ({B | M.IsBase B}) := by
  simp_rw [indep_iff, lowerClosure, LowerSet.coe_mk, mem_ofPred]

@[deprecated (since := "2026-07-09")]
alias setOf_indep_eq := setOfPred_indep_eq
/-
**Matroid.Indep.exists_isBase_superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → ∃ B, M.IsBase B 
∧ I ⊆ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.indep_iff`：indep_iff : M.Indep I ↔ exists B, M.IsBase B ∧ I subs
eteq B
-/
theorem Indep.exists_isBase_superset (hI : M.Indep I) : ∃ B, M.IsBase B ∧ I ⊆ B :=
  indep_iff.1 hI
/-
**Matroid.dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D ⊆ M.E := Iff.rfl
/-
**Matroid.setOfPred_dep_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：setOfPred_dep_eq (M : Matroid α) : {D | M.Dep D} = {I | M.Indep I}ᶜ inter 
Iic M.E
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setOfPred_dep_eq (M : Matroid α) : {D | M.Dep D} = {I | M.Indep I}ᶜ ∩ Iic M.E := rfl

@[deprecated (since := "2026-07-09")]
alias setOf_dep_eq := setOfPred_dep_eq

@[aesop unsafe 30% (rule_sets := [Matroid])]
/-
**Matroid.Indep.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → I ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
theorem Indep.subset_ground (hI : M.Indep I) : I ⊆ M.E := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hIB.trans hB.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
/-
**Matroid.Dep.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.Dep D → D ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Dep.subset_ground (hD : M.Dep D) : D ⊆ M.E :=
  hD.2
/-
**Matroid.indep_or_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：indep_or_dep (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem indep_or_dep (hX : X ⊆ M.E := by aesop_mat) : M.Indep X ∨ M.Dep X := by
  rw [Dep, and_iff_left hX]
  apply em
/-
**Matroid.Indep.not_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → ¬M.Dep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Indep.not_dep (hI : M.Indep I) : ¬ M.Dep I :=
  fun h ↦ h.1 hI
/-
**Matroid.Dep.not_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.Dep D → ¬M.Indep D
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Dep.not_indep (hD : M.Dep D) : ¬ M.Indep D :=
  hD.1
/-
**Matroid.dep_of_not_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dep_of_not_indep (hD : ¬ M.Indep D) (hDE : D subseteq M.E
参数：hD : ¬ M.Indep D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dep_of_not_indep (hD : ¬ M.Indep D) (hDE : D ⊆ M.E := by aesop_mat) : M.Dep D :=
  ⟨hD, hDE⟩
/-
**Matroid.indep_of_not_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：indep_of_not_dep (hI : ¬ M.Dep I) (hIE : I subseteq M.E
参数：hI : ¬ M.Dep I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
-/
theorem indep_of_not_dep (hI : ¬ M.Dep I) (hIE : I ⊆ M.E := by aesop_mat) : M.Indep I :=
  by_contra (fun h ↦ hI ⟨h, hIE⟩)
/-
**Matroid.not_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, autoParam (X ⊆ M.E) Matroid.
not_dep_iff._auto_1 → (¬M.Dep X ↔ M.Indep X)
参数：X ⊆ M.E；¬M.Dep X ↔ M.Indep X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem not_dep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Dep X ↔ M.Indep X := by
  rw [Dep, and_iff_left hX, not_not]
/-
**Matroid.not_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, autoParam (X ⊆ M.E) Matroid.
not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
参数：X ⊆ M.E；¬M.Indep X ↔ M.Dep X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem not_indep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Indep X ↔ M.Dep X := by
  rw [Dep, and_iff_left hX]
/-
**Matroid.indep_iff_not_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：indep_iff_not_dep : M.Indep I ↔ ¬M.Dep I ∧ I subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem indep_iff_not_dep : M.Indep I ↔ ¬M.Dep I ∧ I ⊆ M.E := by
  rw [dep_iff, not_and, not_imp_not]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, h.subset_ground⟩, fun h ↦ h.1 h.2⟩
/-
**Matroid.Indep.subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.Indep J → I ⊆ J → M.Inde
p I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.indep_iff`：indep_iff : M.Indep I ↔ exists B, M.IsBase B ∧ I subs
eteq B
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Indep.subset (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I := by
  obtain ⟨B, hB, hJB⟩ := hJ.exists_isBase_superset
  exact indep_iff.2 ⟨B, hB, hIJ.trans hJB⟩
/-
**Matroid.Dep.superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   M.Dep D → D ⊆ X → autoPa
ram (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.dep_of_not_indep`：dep_of_not_indep (hD : ¬ M.Indep D) (hDE : D s
ubseteq M.E
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
-/
theorem Dep.superset (hD : M.Dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  dep_of_not_indep (fun hI ↦ (hI.subset hDX).not_dep hD)
/-
**Matroid.IsBase.indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → M.Indep B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.indep_iff`：indep_iff : M.Indep I ↔ exists B, M.IsBase B ∧ I subs
eteq B
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem IsBase.indep (hB : M.IsBase B) : M.Indep B :=
  indep_iff.2 ⟨B, hB, subset_rfl⟩
/-
**Matroid.empty_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
@[simp] theorem empty_indep (M : Matroid α) : M.Indep ∅ :=
  Exists.elim M.exists_isBase (fun _ hB ↦ hB.indep.subset (empty_subset _))
/-
**Matroid.Dep.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.Dep D → D.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Dep.nonempty (hD : M.Dep D) : D.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep
/-
**Matroid.Indep.finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.RankFinite], M.Indep I → I
.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
-/
theorem Indep.finite [RankFinite M] (hI : M.Indep I) : I.Finite :=
  let ⟨_, hB, hIB⟩ := hI.exists_isBase_superset
  hB.finite.subset hIB
/-
**Matroid.Indep.rankPos_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → I.Nonempty → M.R
ankPos
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Matroid.IsBase.rankPos_of_nonempty`：∀ {α : Type u_1} {M : Matroid α} {B 
: Set α}, M.IsBase B → B.Nonempty → M.RankPos
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
-/
theorem Indep.rankPos_of_nonempty (hI : M.Indep I) (hne : I.Nonempty) : M.RankPos := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hB.rankPos_of_nonempty (hne.mono hIB)
/-
**Matroid.Indep.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → ∀ (X : Set α), M
.Indep (I ∩ X)
参数：X : Set α；I ∩ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem Indep.inter_right (hI : M.Indep I) (X : Set α) : M.Indep (I ∩ X) :=
  hI.subset inter_subset_left
/-
**Matroid.Indep.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → ∀ (X : Set α), M
.Indep (X ∩ I)
参数：X : Set α；X ∩ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem Indep.inter_left (hI : M.Indep I) (X : Set α) : M.Indep (X ∩ I) :=
  hI.subset inter_subset_right
/-
**Matroid.Indep.sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → ∀ (X : Set α), M
.Indep (I \ X)
参数：X : Set α；I \ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem Indep.sdiff (hI : M.Indep I) (X : Set α) : M.Indep (I \ X) :=
  hI.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Indep.diff := Indep.sdiff
/-
**Matroid.IsBase.eq_of_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B I : Set α}, M.IsBase B → M.Indep I → B
 ⊆ I → B = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsBase.eq_of_subset_indep (hB : M.IsBase B) (hI : M.Indep I) (hBI : B ⊆ I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI.exists_isBase_superset
  hBI.antisymm (by rwa [hB.eq_of_subset_isBase hB' (hBI.trans hB'I)])
/-
**Matroid.isBase_iff_maximal_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBase_iff_maximal_indep : M.IsBase B ↔ Maximal M.Indep B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `maximal_subset_iff`：maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> s subseteq t -> s = t
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
-/
theorem isBase_iff_maximal_indep : M.IsBase B ↔ Maximal M.Indep B := by
  rw [maximal_subset_iff]
  refine ⟨fun h ↦ ⟨h.indep, fun _ ↦ h.eq_of_subset_indep⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_superset
  rwa [h' hB'.indep hBB']
/-
**Matroid.Indep.isBase_of_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → (∀ ⦃J : Set α⦄, 
M.Indep J → I ⊆ J → I = J) → M.IsBase I
参数：∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → I = J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_iff_maximal_indep`：isBase_iff_maximal_indep : M.IsBase B 
↔ Maximal M.Indep B
· 使用定理 `maximal_subset_iff`：maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> s subseteq t -> s = t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
theorem Indep.isBase_of_maximal (hI : M.Indep I) (h : ∀ ⦃J⦄, M.Indep J → I ⊆ J → I = J) :
    M.IsBase I := by
  rwa [isBase_iff_maximal_indep, maximal_subset_iff, and_iff_right hI]
/-
**Matroid.IsBase.dep_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B X : Set α},   M.IsBase B → B ⊂ X → aut
oParam (X ⊆ M.E) Matroid.IsBase.dep_of_ssubset._auto_1 → M.Dep X
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
-/
theorem IsBase.dep_of_ssubset (hB : M.IsBase B) (h : B ⊂ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X :=
  ⟨fun hX ↦ h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩
/-
**Matroid.IsBase.dep_of_insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e : α},   M.IsBase B → e ∉ B
 → autoParam (e ∈ M.E) Matroid.IsBase.dep_of_insert._auto_1 → M.Dep (insert e B)
参数：e ∈ M.E；insert e B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.dep_of_ssubset`：∀ {α : Type u_1} {M : Matroid α} {B X : S
et α},   M.IsBase B → B ⊂ X → autoParam (X ⊆ M.E) Matroid.IsBase.dep_of_ssubset.
_auto_1 → M.Dep X
· 使用定理 `Set.ssubset_insert`：ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂
 insert a s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
theorem IsBase.dep_of_insert (hB : M.IsBase B) (heB : e ∉ B) (he : e ∈ M.E := by aesop_mat) :
    M.Dep (insert e B) := hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)
/-
**Matroid.IsBase.mem_of_insert_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e : α}, M.IsBase B → M.Indep
 (insert e B) → e ∈ B
参数：insert e B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsBase.dep_of_insert`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α} {e : α},   M.IsBase B → e ∉ B → autoParam (e ∈ M.E) Matroid.IsBase.dep_of_ins
ert._auto_1 → M.De…
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem IsBase.mem_of_insert_indep (hB : M.IsBase B) (heB : M.Indep (insert e B)) : e ∈ B :=
  by_contra fun he ↦ (hB.dep_of_insert he (heB.subset_ground (mem_insert _ _))).not_indep heB

/-- If the difference of two IsBases is a singleton, then they differ by an insertion/removal -/
/-
**Matroid.IsBase.eq_exchange_of_sdiff_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B B' : Set α} {e : α},   M.IsBase B → M.
IsBase B' → B \ B' = {e} → ∃ f ∈ B' \ B, B' = insert f B \ {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.exchange`：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α
} {e : α},   M.IsBase B₁ → M.IsBase B₂ → e ∈ B₁ \ B₂ → ∃ y ∈ B₂ \ B₁, M.IsBase (
insert y (B₁ …
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_singleton_comm`：insert_sdiff_singleton_comm (hab : a !=
 b) (s : Set α) : insert a (s \ {b}) = insert a s \ {b}
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)

--- 原说明 ---
If the difference of two IsBases is a singleton, then they differ by an insertio
n/removal
-/
theorem IsBase.eq_exchange_of_sdiff_eq_singleton (hB : M.IsBase B) (hB' : M.IsBase B')
    (h : B \ B' = {e}) : ∃ f ∈ B' \ B, B' = (insert f B) \ {e} := by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_sdiff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_isBase hB' ?_).symm⟩
  rw [sdiff_subset_iff, insert_subset_iff, union_comm, ← sdiff_subset_iff, h,
    and_iff_left rfl.subset]
  exact Or.inl hf.1

@[deprecated (since := "2026-06-03")]
alias IsBase.eq_exchange_of_diff_eq_singleton := IsBase.eq_exchange_of_sdiff_eq_singleton
/-
**Matroid.IsBase.exchange_isBase_of_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
ase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e f : α},   M.IsBase B → f ∉
 B → M.Indep (insert f (B \ {e})) → M.IsBase (insert f (B \ {e}))
参数：insert f (B \ {e})；insert f (B \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Matroid.IsBase.encard_sdiff_comm`：∀ {α : Type u_1} {M : Matroid α} {B₁ B
₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → (B₁ \ B₂).encard = (B₂ \ B₁).encard
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.sdiff_sdiff_comm`：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (
s \ u) \ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `Set.encard_eq_one`：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem IsBase.exchange_isBase_of_indep (hB : M.IsBase B) (hf : f ∉ B)
    (hI : M.Indep (insert f (B \ {e}))) : M.IsBase (insert f (B \ {e})) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hcard := hB'.encard_sdiff_comm hB
  rw [insert_subset_iff, ← sdiff_eq_empty, sdiff_sdiff_comm, sdiff_eq_empty,
    subset_singleton_iff_eq] at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_notMem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h, encard_singleton, encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [← h, ← singleton_union, ← hx, _root_.sdiff_sdiff_right_self, inf_eq_inter, inter_comm B,
    sdiff_union_inter]
  exact hB'
/-
**Matroid.IsBase.exchange_isBase_of_indep'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Base`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e f : α},   M.IsBase B → e ∈
 B → f ∉ B → M.Indep (insert f B \ {e}) → M.IsBase (insert f B \ {e})
参数：insert f B \ {e}；insert f B \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton_comm`：insert_sdiff_singleton_comm (hab : a !=
 b) (s : Set α) : insert a (s \ {b}) = insert a s \ {b}
· 使用定理 `Matroid.IsBase.exchange_isBase_of_indep`：∀ {α : Type u_1} {M : Matroid α
} {B : Set α} {e f : α},   M.IsBase B → f ∉ B → M.Indep (insert f (B \ {e})) → M
.IsBase (insert f (B \ {e}))
-/
theorem IsBase.exchange_isBase_of_indep' (hB : M.IsBase B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.Indep (insert f B \ {e})) : M.IsBase (insert f B \ {e}) := by
  have hfe : f ≠ e := ne_of_mem_of_not_mem he hf |>.symm
  rw [← insert_sdiff_singleton_comm hfe] at *
  exact hB.exchange_isBase_of_indep hf hI
/-
**Matroid.insert_isBase_of_insert_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：insert_isBase_of_insert_indep {M : Matroid α} {I : Set α} {e f : α} (he : 
e ∉ I) (hf : f ∉ I) (heI : M.IsBase (insert e I)) (hfI : M.Indep (insert f I)) :
 M.IsBase (insert f I)
参数：he : e ∉ I；hf : f ∉ I；heI : M.IsBase (insert e I)；hfI : M.Indep (insert f I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Matroid.IsBase.exchange_isBase_of_indep`：∀ {α : Type u_1} {M : Matroid α
} {B : Set α} {e f : α},   M.IsBase B → f ∉ B → M.Indep (insert f (B \ {e})) → M
.IsBase (insert f (B \ {e}))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma insert_isBase_of_insert_indep {M : Matroid α} {I : Set α} {e f : α}
    (he : e ∉ I) (hf : f ∉ I) (heI : M.IsBase (insert e I)) (hfI : M.Indep (insert f I)) :
    M.IsBase (insert f I) := by
  obtain rfl | hef := eq_or_ne e f
  · assumption
  simpa [sdiff_singleton_eq_self he, hfI]
    using heI.exchange_isBase_of_indep (e := e) (f := f) (by simp [hef.symm, hf])
/-
**Matroid.IsBase.insert_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e : α}, M.IsBase B → e ∈ M.E
 \ B → M.Dep (insert e B)
参数：insert e B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.insert_eq_self`：insert_eq_self : insert a s = s ↔ a in s
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem IsBase.insert_dep (hB : M.IsBase B) (h : e ∈ M.E \ B) : M.Dep (insert e B) := by
  rw [← not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi ↦ insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)
/-
**Matroid.Indep.exists_insert_of_not_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
ndep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B I : Set α}, M.Indep I → ¬M.IsBase I → 
M.IsBase B → ∃ e ∈ B \ I, M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.IsBase.exchange`：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α
} {e : α},   M.IsBase B₁ → M.IsBase B₂ → e ∈ B₁ \ B₂ → ∃ y ∈ B₂ \ B₁, M.IsBase (
insert y (B₁ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.indep_iff`：indep_iff : M.Indep I ↔ exists B, M.IsBase B ∧ I subs
eteq B
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
-/
theorem Indep.exists_insert_of_not_isBase (hI : M.Indep I) (hI' : ¬M.IsBase I) (hB : M.IsBase B) :
    ∃ e ∈ B \ I, M.Indep (insert e I) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB')))
  by_cases hxB : x ∈ B
  · exact ⟨x, ⟨hxB, hx⟩, hB'.indep.subset (insert_subset hxB' hIB')⟩
  obtain ⟨e, he, hBase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact ⟨e, ⟨he.1, notMem_subset hIB' he.2⟩,
    indep_iff.2 ⟨_, hBase, insert_subset_insert (subset_sdiff_singleton hIB' hx)⟩⟩

/-- This is the same as `Indep.exists_insert_of_not_isBase`, but phrased so that
  it is defeq to the augmentation axiom for independent sets. -/
/-
**Matroid.Indep.exists_insert_of_not_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Indep`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) ⦃I B : Set α⦄,   M.Indep I → ¬Maximal M.I
ndep I → Maximal M.Indep B → ∃ x ∈ B \ I, M.Indep (insert x I)
参数：M : Matroid α。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_insert_of_not_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B I : Set α}, M.Indep I → ¬M.IsBase I → M.IsBase B → ∃ e ∈ B \ I, M.Indep (
insert e I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
· 使用定理 `Matroid.Indep.isBase_of_maximal`：∀ {α : Type u_1} {M : Matroid α} {I : S
et α}, M.Indep I → (∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → I = J) → M.IsBase I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
This is the same as `Indep.exists_insert_of_not_isBase`, but phrased so that
  it is defeq to the augmentation axiom for independent sets.
-/
theorem Indep.exists_insert_of_not_maximal (M : Matroid α) ⦃I B : Set α⦄ (hI : M.Indep I)
    (hInotmax : ¬ Maximal M.Indep I) (hB : Maximal M.Indep B) :
    ∃ x ∈ B \ I, M.Indep (insert x I) := by
  simp only [maximal_subset_iff, hI, not_and, not_forall, exists_prop, true_imp_iff] at hB hInotmax
  refine hI.exists_insert_of_not_isBase (fun hIb ↦ ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hInotmax
    exact hne <| hIb.eq_of_subset_indep hII' hI'
  exact hB.1.isBase_of_maximal fun J hJ hBJ ↦ hB.2 hJ hBJ
/-
**Matroid.Indep.isBase_of_forall_insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Indep B → (∀ e ∈ M.E \ B, 
¬M.Indep (insert e B)) → M.IsBase B
参数：∀ e ∈ M.E \ B, ¬M.Indep (insert e B)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.Indep.exists_insert_of_not_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B I : Set α}, M.Indep I → ¬M.IsBase I → M.IsBase B → ∃ e ∈ B \ I, M.Indep (
insert e I)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Indep.isBase_of_forall_insert (hB : M.Indep B)
    (hBmax : ∀ e ∈ M.E \ B, ¬ M.Indep (insert e B)) : M.IsBase B := by
  by_contra hnb
  obtain ⟨B', hB'⟩ := M.exists_isBase
  obtain ⟨e, he, h⟩ := hB.exists_insert_of_not_isBase hnb hB'
  exact hBmax e ⟨hB'.subset_ground he.1, he.2⟩ h
/-
**Matroid.ground_indep_iff_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_indep_iff_isBase : M.Indep M.E ↔ M.IsBase M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBase_of_maximal`：∀ {α : Type u_1} {M : Matroid α} {I : S
et α}, M.Indep I → (∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → I = J) → M.IsBase I
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
-/
theorem ground_indep_iff_isBase : M.Indep M.E ↔ M.IsBase M.E :=
  ⟨fun h ↦ h.isBase_of_maximal (fun _ hJ hEJ ↦ hEJ.antisymm hJ.subset_ground), IsBase.indep⟩
/-
**Matroid.IsBase.exists_insert_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
ase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B B' I : Set α}, M.IsBase B → I ⊂ B → M.
IsBase B' → ∃ e ∈ B' \ I, M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_insert_of_not_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B I : Set α}, M.Indep I → ¬M.IsBase I → M.IsBase B → ∃ e ∈ B \ I, M.Indep (
insert e I)
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
-/
theorem IsBase.exists_insert_of_ssubset (hB : M.IsBase B) (hIB : I ⊂ B) (hB' : M.IsBase B') :
    ∃ e ∈ B' \ I, M.Indep (insert e I) :=
  (hB.indep.subset hIB.subset).exists_insert_of_not_isBase
    (fun hI ↦ hIB.ne (hI.eq_of_subset_isBase hB hIB.subset)) hB'
/-
**Matroid.ext_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (∀ ⦃I : Set α⦄, I ⊆ M₁
.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
参数：∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[ext] theorem ext_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃I⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) : M₁ = M₂ :=
  have h' : M₁.Indep = M₂.Indep := by
    ext I
    by_cases hI : I ⊆ M₁.E
    · rwa [h]
    exact iff_of_false (fun hi ↦ hI hi.subset_ground)
      (fun hi ↦ hI (hi.subset_ground.trans_eq hE.symm))
  ext_isBase hE (fun B _ ↦ by simp_rw [isBase_iff_maximal_indep, h'])
/-
**Matroid.ext_iff_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ext_iff_indep {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ forall ⦃I⦄, 
I subseteq M₁.E -> (M₁.Indep I ↔ M₂.Indep I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ext_iff_indep {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ ⦃I⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I) :=
  ⟨fun h ↦ by (subst h; simp), fun h ↦ ext_indep h.1 h.2⟩

/-- If every base of `M₁` is independent in `M₂` and vice versa, then `M₁ = M₂`. -/
/-
**Matroid.ext_isBase_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_isBase_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (hM₁ : forall ⦃B⦄,
 M₁.IsBase B -> M₂.Indep B) (hM₂ : forall ⦃B⦄, M₂.IsBase B -> M₁.Indep B) : M₁ =
 M₂
参数：hE : M₁.E = M₂.E；hM₁ : forall ⦃B⦄, M₁.IsBase B -> M₂.Indep B；hM₂ : forall ⦃B⦄
, M₂.IsBase B -> M₁.Indep B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I

--- 原说明 ---
If every base of `M₁` is independent in `M₂` and vice versa, then `M₁ = M₂`.
-/
lemma ext_isBase_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hM₁ : ∀ ⦃B⦄, M₁.IsBase B → M₂.Indep B) (hM₂ : ∀ ⦃B⦄, M₂.IsBase B → M₁.Indep B) : M₁ = M₂ := by
  refine ext_indep hE fun I hIE ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    exact (hM₁ hB).subset hIB
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact (hM₂ hB).subset hIB

/-- A `Finitary` matroid is one where a set is independent if and only if it all
  its finite subsets are independent, or equivalently a matroid whose circuits are finite. -/
/-
**Matroid.Finitary** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finitary` matroid is one where a set is independent if and only if it all
  its finite subsets are independent, or equivalently a matroid whose circuits a
re finite.
-/
@[mk_iff] class Finitary (M : Matroid α) : Prop where
  /-- `I` is independent if all its finite subsets are independent. -/
  indep_of_forall_finite : ∀ I, (∀ J, J ⊆ I → J.Finite → M.Indep J) → M.Indep I
/-
**Matroid.indep_of_forall_finite_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
`。
形式化陈述：indep_of_forall_finite_subset_indep {M : Matroid α} [Finitary M] (I : Set 
α) (h : forall J, J subseteq I -> J.Finite -> M.Indep J) : M.Indep I
参数：I : Set α；h : forall J, J subseteq I -> J.Finite -> M.Indep J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Finitary.indep_of_forall_finite`：∀ {α : Type u_1} {M : Matroid α
} [self : M.Finitary] (I : Set α), (∀ J ⊆ I, J.Finite → M.Indep J) → M.Indep I
-/
theorem indep_of_forall_finite_subset_indep {M : Matroid α} [Finitary M] (I : Set α)
    (h : ∀ J, J ⊆ I → J.Finite → M.Indep J) : M.Indep I :=
  Finitary.indep_of_forall_finite I h
/-
**Matroid.indep_iff_forall_finite_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d`。
形式化陈述：indep_iff_forall_finite_subset_indep {M : Matroid α} [Finitary M] : M.Inde
p I ↔ forall J, J subseteq I -> J.Finite -> M.Indep J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.Finitary.indep_of_forall_finite`：∀ {α : Type u_1} {M : Matroid α
} [self : M.Finitary] (I : Set α), (∀ J ⊆ I, J.Finite → M.Indep J) → M.Indep I
-/
theorem indep_iff_forall_finite_subset_indep {M : Matroid α} [Finitary M] :
    M.Indep I ↔ ∀ J, J ⊆ I → J.Finite → M.Indep J :=
  ⟨fun h _ hJI _ ↦ h.subset hJI, Finitary.indep_of_forall_finite I⟩
/-
**Matroid.finitary_of_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：finitary_of_rankFinite {M : Matroid α} [RankFinite M] : Finitary M where i
ndep_of_forall_finite I hI
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Set.Infinite.exists_subset_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Inf
inite → ∀ (k : ℕ), ∃ t ⊆ s, t.Finite ∧ t.ncard = k
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Matroid.IsBase.ncard_eq_ncard_of_isBase`：∀ {α : Type u_1} {M : Matroid α
} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁.ncard = B₂.ncard
-/
instance finitary_of_rankFinite {M : Matroid α} [RankFinite M] : Finitary M where
  indep_of_forall_finite I hI := by
    refine I.finite_or_infinite.elim (hI _ Subset.rfl) (fun h ↦ False.elim ?_)
    obtain ⟨B, hB⟩ := M.exists_isBase
    obtain ⟨I₀, hI₀I, hI₀fin, hI₀card⟩ := h.exists_subset_ncard_eq (B.ncard + 1)
    obtain ⟨B', hB', hI₀B'⟩ := (hI _ hI₀I hI₀fin).exists_isBase_superset
    have hle := ncard_le_ncard hI₀B' hB'.finite
    rw [hI₀card, hB'.ncard_eq_ncard_of_isBase hB, Nat.add_one_le_iff] at hle
    exact hle.ne rfl

/-- Matroids obey the maximality axiom -/
/-
**Matroid.existsMaximalSubsetProperty_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：existsMaximalSubsetProperty_indep (M : Matroid α) : forall X, X subseteq M
.E -> ExistsMaximalSubsetProperty M.Indep X
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.maximality`：∀ {α : Type u_1} (self : Matroid α), ∀ X ⊆ self.E, M
atroid.ExistsMaximalSubsetProperty self.Indep X

--- 原说明 ---
Matroids obey the maximality axiom
-/
theorem existsMaximalSubsetProperty_indep (M : Matroid α) :
    ∀ X, X ⊆ M.E → ExistsMaximalSubsetProperty M.Indep X :=
  M.maximality

end dep_indep

section copy

/-- create a copy of `M : Matroid α` with independence and base predicates and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
/-
**Matroid.copy** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} →   (M : Matroid α) →     (E : Set α) →       (IsBase Indep
 : Set α → Prop) →         E = M.E → (∀ (B : Set α), IsBase B ↔ M.IsBase B) → (∀
 (I : Set α), Indep I ↔ M.Indep I) → Matroid α
参数：M : Matroid α；E : Set α；IsBase Indep : Set α → Prop；∀ (B : Set α), IsBase B ↔
 M.IsBase B；∀ (I : Set α), Indep I ↔ M.Indep I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a copy of `M : Matroid α` with independence and base predicates and groun
d set defeq
to supplied arguments that are provably equal to those of `M`.
-/
@[simps] def copy (M : Matroid α) (E : Set α) (IsBase Indep : Set α → Prop) (hE : E = M.E)
    (hB : ∀ B, IsBase B ↔ M.IsBase B) (hI : ∀ I, Indep I ↔ M.Indep I) : Matroid α where
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

/-- create a copy of `M : Matroid α` with an independence predicate and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
/-
**Matroid.copyIndep** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} →   (M : Matroid α) → (E : Set α) → (Indep : Set α → Prop) 
→ E = M.E → (∀ (I : Set α), Indep I ↔ M.Indep I) → Matroid α
参数：M : Matroid α；E : Set α；Indep : Set α → Prop；∀ (I : Set α), Indep I ↔ M.Indep
 I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a copy of `M : Matroid α` with an independence predicate and ground set d
efeq
to supplied arguments that are provably equal to those of `M`.
-/
@[simps!] def copyIndep (M : Matroid α) (E : Set α) (Indep : Set α → Prop)
    (hE : E = M.E) (h : ∀ I, Indep I ↔ M.Indep I) : Matroid α :=
  M.copy E M.IsBase Indep hE (fun _ ↦ Iff.rfl) h

/-- create a copy of `M : Matroid α` with a base predicate and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
/-
**Matroid.copyBase** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} →   (M : Matroid α) → (E : Set α) → (IsBase : Set α → Prop)
 → E = M.E → (∀ (B : Set α), IsBase B ↔ M.IsBase B) → Matroid α
参数：M : Matroid α；E : Set α；IsBase : Set α → Prop；∀ (B : Set α), IsBase B ↔ M.IsB
ase B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a copy of `M : Matroid α` with a base predicate and ground set defeq
to supplied arguments that are provably equal to those of `M`.
-/
@[simps!] def copyBase (M : Matroid α) (E : Set α) (IsBase : Set α → Prop)
    (hE : E = M.E) (h : ∀ B, IsBase B ↔ M.IsBase B) : Matroid α :=
  M.copy E IsBase M.Indep hE h (fun _ ↦ Iff.rfl)

end copy

section IsBasis

/-- A Basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'Basis' is used to refer to what we call a 'Base'). -/
/-
**Matroid.IsBasis** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsBasis (M : Matroid α) (I X : Set α) : Prop
参数：M : Matroid α；I X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'Basis' is used to refer to what we call a 
'Base').
-/
def IsBasis (M : Matroid α) (I X : Set α) : Prop :=
  Maximal (fun A ↦ M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E

/-- `Matroid.IsBasis' I X` is the same as `Matroid.IsBasis I X`,
without the requirement that `X ⊆ M.E`. This is convenient for some
API building, especially when working with rank and closure. -/
/-
**Matroid.IsBasis'** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsBasis' (M : Matroid α) (I X : Set α) : Prop
参数：M : Matroid α；I X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matroid.IsBasis' I X` is the same as `Matroid.IsBasis I X`,
without the requirement that `X ⊆ M.E`. This is convenient for some
API building, especially when working with rank and closure.
-/
def IsBasis' (M : Matroid α) (I X : Set α) : Prop :=
  Maximal (fun A ↦ M.Indep A ∧ A ⊆ X) I

variable {B I J X Y : Set α} {e : α}
/-
**Matroid.IsBasis'.indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → M.Indep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis'.indep (hI : M.IsBasis' I X) : M.Indep I :=
  hI.1.1
/-
**Matroid.IsBasis.indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → M.Indep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis.indep (hI : M.IsBasis I X) : M.Indep I :=
  hI.1.1.1
/-
**Matroid.IsBasis.subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → I ⊆ X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis.subset (hI : M.IsBasis I X) : I ⊆ X :=
  hI.1.1.2
/-
**Matroid.IsBasis.isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → M.IsBasis'
 I X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis.isBasis' (hI : M.IsBasis I X) : M.IsBasis' I X :=
  hI.1
/-
**Matroid.IsBasis'.isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.IsBasis' I X → autoPar
am (X ⊆ M.E) Matroid.IsBasis'.isBasis._auto_1 → M.IsBasis I X
参数：X ⊆ M.E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBasis'.isBasis (hI : M.IsBasis' I X) (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis I X :=
  ⟨hI, hX⟩
/-
**Matroid.IsBasis'.subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → I ⊆ X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis'.subset (hI : M.IsBasis' I X) : I ⊆ X :=
  hI.1.2


@[aesop unsafe 15% (rule_sets := [Matroid])]
/-
**Matroid.IsBasis.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → X ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsBasis.subset_ground (hI : M.IsBasis I X) : X ⊆ M.E :=
  hI.2
/-
**Matroid.IsBasis.isBasis_inter_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasi
s`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → M.IsBasis 
I (X ∩ M.E)
参数：X ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem IsBasis.isBasis_inter_ground (hI : M.IsBasis I X) : M.IsBasis I (X ∩ M.E) := by
  convert! hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets := [Matroid])]
/-
**Matroid.IsBasis.left_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → I ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
theorem IsBasis.left_subset_ground (hI : M.IsBasis I X) : I ⊆ M.E :=
  hI.indep.subset_ground
/-
**Matroid.IsBasis.eq_of_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis I X → M.Indep 
J → I ⊆ J → J ⊆ X → I = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis.eq_of_subset_indep (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I ⊆ J)
    (hJX : J ⊆ X) : I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)
/-
**Matroid.IsBasis.Finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → ∀ [M.RankF
inite], I.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
theorem IsBasis.Finite (hI : M.IsBasis I X) [RankFinite M] : I.Finite := hI.indep.finite
/-
**Matroid.isBasis_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBasis_iff' : M.IsBasis I X ↔ (M.Indep I ∧ I subseteq X ∧ forall ⦃J⦄, M.I
ndep J -> I subseteq J -> J subseteq X -> I = J) ∧ X subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M.
IsBasis I X = (Maximal (fun A => M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E)
· 使用定理 `maximal_subset_iff`：maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> s subseteq t -> s = t
-/
theorem isBasis_iff' :
    M.IsBasis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E := by
  rw [IsBasis, maximal_subset_iff]
  tauto
/-
**Matroid.isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBasis_iff (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff'`：isBasis_iff' : M.IsBasis I X ↔ (M.Indep I ∧ I subs
eteq X ∧ forall ⦃J⦄, M.Indep J -> I subseteq J -> J subseteq X -> I = J) ∧ X sub
seteq M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBasis_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) := by
  rw [isBasis_iff', and_iff_left hX]
/-
**Matroid.isBasis'_iff_isBasis_inter_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis
 I (X ∩ M.E)
参数：X ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M
.IsBasis' I X = Maximal (fun A => M.Indep A ∧ A ⊆ X) I
· 使用定理 `Matroid.IsBasis.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M.
IsBasis I X = (Maximal (fun A => M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `maximal_iff_maximal_of_imp_of_forall`：∀ {α : Type u_2} {P Q : α → Prop} 
{x : α} [inst : PartialOrder α],   (∀ ⦃x : α⦄, Q x → P x) → (∀ ⦃x : α⦄, P x → ∃ 
y, x ≤ y ∧ Q y) → (Maximal…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBasis'_iff_isBasis_inter_ground : M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E) := by
  rw [IsBasis', IsBasis, and_iff_left inter_subset_right, maximal_iff_maximal_of_imp_of_forall]
  · exact fun I hI ↦ ⟨hI.1, hI.2.trans inter_subset_left⟩
  exact fun I hI ↦ ⟨I, rfl.le, hI.1, subset_inter hI.2 hI.1.subset_ground⟩
/-
**Matroid.isBasis'_iff_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   autoParam (X ⊆ M.E) Matr
oid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I X ↔ M.IsBasis I X)
参数：X ⊆ M.E；M.IsBasis' I X ↔ M.IsBasis I X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBasis'_iff_isBasis (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis' I X ↔ M.IsBasis I X := by
  rw [isBasis'_iff_isBasis_inter_ground, inter_eq_self_of_subset_left hX]
/-
**Matroid.isBasis_iff_isBasis'_subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X ↔ M.IsBasis'
 I X ∧ X ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isBasis_iff_isBasis'_subset_ground : M.IsBasis I X ↔ M.IsBasis' I X ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.isBasis', h.subset_ground⟩, fun h ↦ (isBasis'_iff_isBasis h.2).mp h.1⟩
/-
**Matroid.IsBasis'.isBasis_inter_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → M.IsBasis
 I (X ∩ M.E)
参数：X ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
-/
theorem IsBasis'.isBasis_inter_ground (hIX : M.IsBasis' I X) : M.IsBasis I (X ∩ M.E) :=
  isBasis'_iff_isBasis_inter_ground.mp hIX
/-
**Matroid.IsBasis'.eq_of_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis
'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → M.Indep
 J → I ⊆ J → J ⊆ X → I = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsBasis'.eq_of_subset_indep (hI : M.IsBasis' I X) (hJ : M.Indep J) (hIJ : I ⊆ J)
    (hJX : J ⊆ X) : I = J :=
  hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)
/-
**Matroid.IsBasis'.insert_not_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {e : α}, M.IsBasis' I X → e
 ∈ X \ I → ¬M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.insert_eq_self`：insert_eq_self : insert a s = s ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 J X : Set α}, M.IsBasis' I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
-/
theorem IsBasis'.insert_not_indep (hI : M.IsBasis' I X) (he : e ∈ X \ I) : ¬ M.Indep (insert e I) :=
  fun hi ↦ he.2 <| insert_eq_self.1 <| Eq.symm <|
    hI.eq_of_subset_indep hi (subset_insert _ _) (insert_subset he.1 hI.subset)
/-
**Matroid.isBasis_iff_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBasis_iff_maximal (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M.
IsBasis I X = (Maximal (fun A => M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBasis_iff_maximal (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ Maximal (fun I ↦ M.Indep I ∧ I ⊆ X) I := by
  rw [IsBasis, and_iff_left hX]
/-
**Matroid.Indep.isBasis_of_maximal_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Ind
ep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.Indep I →     I ⊆ X → 
      (∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I) →         autoParam (X 
⊆ M.E) Matroid.Indep.isBasis_of_maximal_subset._auto_1 → M.IsBasis I X
参数：∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I；X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff`：isBasis_iff (hX : X subseteq M.E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
theorem Indep.isBasis_of_maximal_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X := by
  rw [isBasis_iff (by aesop_mat : X ⊆ M.E), and_iff_right hI, and_iff_right hIX]
  exact fun J hJ hIJ hJX ↦ hIJ.antisymm (hmax hJ hIJ hJX)
/-
**Matroid.IsBasis.isBasis_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y : Set α}, M.IsBasis I X → I ⊆ Y → 
Y ⊆ X → M.IsBasis I Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff`：isBasis_iff (hX : X subseteq M.E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
-/
theorem IsBasis.isBasis_subset (hI : M.IsBasis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) :
    M.IsBasis I Y := by
  rw [isBasis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY]
  exact fun J hJ hIJ hJY ↦ hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)
/-
**Matroid.isBasis_self_iff_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.IsBasis I I ↔ M.Indep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff'`：isBasis_iff' : M.IsBasis I X ↔ (M.Indep I ∧ I subs
eteq X ∧ forall ⦃J⦄, M.Indep J -> I subseteq J -> J subseteq X -> I = J) ∧ X sub
seteq M.E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
@[simp] theorem isBasis_self_iff_indep : M.IsBasis I I ↔ M.Indep I := by
  rw [isBasis_iff', and_iff_right rfl.subset, and_assoc, and_iff_left_iff_imp]
  exact fun hi ↦ ⟨fun _ _ ↦ subset_antisymm, hi.subset_ground⟩
/-
**Matroid.Indep.isBasis_self** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → M.IsBasis I I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBasis_self_iff_indep`：∀ {α : Type u_1} {M : Matroid α} {I : Se
t α}, M.IsBasis I I ↔ M.Indep I
-/
theorem Indep.isBasis_self (h : M.Indep I) : M.IsBasis I I :=
  isBasis_self_iff_indep.mpr h
/-
**Matroid.isBasis_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {I : Set α} (M : Matroid α), M.IsBasis I ∅ ↔ I = ∅
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
-/
@[simp] theorem isBasis_empty_iff (M : Matroid α) : M.IsBasis I ∅ ↔ I = ∅ :=
  ⟨fun h ↦ subset_empty_iff.mp h.subset, fun h ↦ by (rw [h]; exact M.empty_indep.isBasis_self)⟩
/-
**Matroid.IsBasis.dep_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y : Set α}, M.IsBasis I X → I ⊂ Y → 
Y ⊆ X → M.Dep Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `_private.Mathlib.Combinatorics.Matroid.Basic.0.Matroid.subset_ground_of_
subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, X ⊆ Y → Y ⊆ M.E → X ⊆ M.
E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
-/
theorem IsBasis.dep_of_ssubset (hI : M.IsBasis I X) (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.Dep Y := by
  have : X ⊆ M.E := hI.subset_ground
  rw [← not_indep_iff]
  exact fun hY ↦ hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)
/-
**Matroid.IsBasis.insert_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {e : α}, M.IsBasis I X → e 
∈ X \ I → M.Dep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.dep_of_ssubset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊂ Y → Y ⊆ X → M.Dep Y
· 使用定理 `Set.ssubset_insert`：ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂
 insert a s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
theorem IsBasis.insert_dep (hI : M.IsBasis I X) (he : e ∈ X \ I) : M.Dep (insert e I) :=
  hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)
/-
**Matroid.IsBasis.mem_of_insert_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {e : α}, M.IsBasis I X → e 
∈ X → M.Indep (insert e I) → e ∈ I
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsBasis.insert_dep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set 
α} {e : α}, M.IsBasis I X → e ∈ X \ I → M.Dep (insert e I)
-/
theorem IsBasis.mem_of_insert_indep (hI : M.IsBasis I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) :
    e ∈ I :=
  by_contra (fun heI ↦ (hI.insert_dep ⟨he, heI⟩).not_indep hIe)
/-
**Matroid.IsBasis'.mem_of_insert_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasi
s'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {e : α}, M.IsBasis' I X → e
 ∈ X → M.Indep (insert e I) → e ∈ I
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem IsBasis'.mem_of_insert_indep (hI : M.IsBasis' I X) (he : e ∈ X)
    (hIe : M.Indep (insert e I)) : e ∈ I :=
  hI.isBasis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe
/-
**Matroid.IsBasis.not_isBasis_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBa
sis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis I X → J ⊂ I → 
¬M.IsBasis J X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
theorem IsBasis.not_isBasis_of_ssubset (hI : M.IsBasis I X) (hJI : J ⊂ I) : ¬ M.IsBasis J X :=
  fun h ↦ hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)
/-
**Matroid.Indep.subset_isBasis_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Inde
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.Indep I → I ⊆ X → auto
Param (X ⊆ M.E) Matroid.Indep.subset_isBasis_of_subset._auto_1 → ∃ J, M.IsBasis 
J X ∧ I ⊆ J
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.maximality`：∀ {α : Type u_1} (self : Matroid α), ∀ X ⊆ self.E, M
atroid.ExistsMaximalSubsetProperty self.Indep X
-/
theorem Indep.subset_isBasis_of_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : X ⊆ M.E := by aesop_mat) : ∃ J, M.IsBasis J X ∧ I ⊆ J := by
  obtain ⟨J, hJ, hJmax⟩ := M.maximality X hX I hI hIX
  exact ⟨J, ⟨hJmax, hX⟩, hJ⟩
/-
**Matroid.Indep.subset_isBasis'_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Ind
ep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M
.IsBasis' J X ∧ I ⊆ J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Indep.subset_isBasis'_of_subset (hI : M.Indep I) (hIX : I ⊆ X) :
    ∃ J, M.IsBasis' J X ∧ I ⊆ J := by
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  exact hI.subset_isBasis_of_subset (subset_inter hIX hI.subset_ground)
/-
**Matroid.exists_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：exists_isBasis (M : Matroid α) (X : Set α) (hX : X subseteq M.E
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem exists_isBasis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.IsBasis I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis_of_subset (empty_subset X)
  ⟨_, hI⟩
/-
**Matroid.exists_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：exists_isBasis' (M : Matroid α) (X : Set α) : exists I, M.IsBasis' I X
参数：M : Matroid α；X : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem exists_isBasis' (M : Matroid α) (X : Set α) : ∃ I, M.IsBasis' I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis'_of_subset (empty_subset X)
  ⟨_, hI⟩
/-
**Matroid.exists_isBasis_subset_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：exists_isBasis_subset_isBasis (M : Matroid α) (hXY : X subseteq Y) (hY : Y
 subseteq M.E
参数：M : Matroid α；hXY : X subseteq Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
theorem exists_isBasis_subset_isBasis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I J, M.IsBasis I X ∧ M.IsBasis J Y ∧ I ⊆ J := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩
/-
**Matroid.IsBasis.exists_isBasis_inter_eq_of_superset** 是 Mathlib 中的一个定理，位于命名空间 
`Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y : Set α},   M.IsBasis I X →     X 
⊆ Y →       autoParam (Y ⊆ M.E) Matroid.IsBasis.exists_isBasis_inter_eq_of_super
set._auto_1 → ∃ J, M.IsBasis J Y ∧ J ∩ X = I
参数：Y ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
-/
theorem IsBasis.exists_isBasis_inter_eq_of_superset (hI : M.IsBasis I X) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ J, M.IsBasis J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he ↦ hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))
/-
**Matroid.exists_isBasis_union_inter_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`
。
形式化陈述：exists_isBasis_union_inter_isBasis (M : Matroid α) (X Y : Set α) (hX : X s
ubseteq M.E
参数：M : Matroid α；X Y : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBasis.exists_isBasis_inter_eq_of_superset`：∀ {α : Type u_1} {M
 : Matroid α} {I X Y : Set α},   M.IsBasis I X →     X ⊆ Y →       autoParam (Y 
⊆ M.E) Matroid.IsBasis.exists_isBasis_int…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_isBasis_union_inter_isBasis (M : Matroid α) (X Y : Set α)
    (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I, M.IsBasis I (X ∪ Y) ∧ M.IsBasis (I ∩ Y) Y :=
  let ⟨J, hJ⟩ := M.exists_isBasis Y
  (hJ.exists_isBasis_inter_eq_of_superset subset_union_right).imp
  (fun I hI ↦ ⟨hI.1, by rwa [hI.2]⟩)
/-
**Matroid.Indep.eq_of_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.Indep I → M.IsBasis J I 
→ J = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem Indep.eq_of_isBasis (hI : M.Indep I) (hJ : M.IsBasis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.subset rfl.subset
/-
**Matroid.IsBasis.exists_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → ∃ B, M.IsB
ase B ∧ I = B ∩ X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Matroid.Indep.inter_right`：∀ {α : Type u_1} {M : Matroid α} {I : Set α},
 M.Indep I → ∀ (X : Set α), M.Indep (I ∩ X)
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem IsBasis.exists_isBase (hI : M.IsBasis I X) : ∃ B, M.IsBase B ∧ I = B ∩ X :=
  let ⟨B,hB, hIB⟩ := hI.indep.exists_isBase_superset
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset)
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    inter_subset_right])⟩
/-
**Matroid.isBasis_ground_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBasis B M.E ↔ M.IsBase B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M.
IsBasis I X = (Maximal (fun A => M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Matroid.isBase_iff_maximal_indep`：isBase_iff_maximal_indep : M.IsBase B 
↔ Maximal M.Indep B
· 使用定理 `maximal_and_iff_right_of_imp`：∀ {α : Type u_2} {P Q : α → Prop} {x : α} 
[inst : LE α],   (∀ ⦃x : α⦄, P x → Q x) → (Maximal (fun x => P x ∧ Q x) x ↔ Maxi
mal P x ∧ Q x)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem isBasis_ground_iff : M.IsBasis B M.E ↔ M.IsBase B := by
  rw [IsBasis, and_iff_left rfl.subset, isBase_iff_maximal_indep,
    maximal_and_iff_right_of_imp (fun _ h ↦ h.subset_ground),
    and_iff_left_of_imp (fun h ↦ h.1.subset_ground)]
/-
**Matroid.IsBase.isBasis_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → M.IsBasis B M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
-/
theorem IsBase.isBasis_ground (hB : M.IsBase B) : M.IsBasis B M.E :=
  isBasis_ground_iff.mpr hB
/-
**Matroid.Indep.isBasis_iff_forall_insert_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.Indep I → I ⊆ X → (M.IsB
asis I X ↔ ∀ e ∈ X \ I, M.Dep (insert e I))
参数：M.IsBasis I X ↔ ∀ e ∈ X \ I, M.Dep (insert e I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M.
IsBasis I X = (Maximal (fun A => M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E)
· 使用定理 `Set.maximal_iff_forall_insert`：Set.maximal_iff_forall_insert (hP : foral
l ⦃s t⦄, P t -> s subseteq t -> P s) : Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (in
sert x s)
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem Indep.isBasis_iff_forall_insert_dep (hI : M.Indep I) (hIX : I ⊆ X) :
    M.IsBasis I X ↔ ∀ e ∈ X \ I, M.Dep (insert e I) := by
  rw [IsBasis, maximal_iff_forall_insert (fun I J hI hIJ ↦ ⟨hI.1.subset hIJ, hIJ.trans hI.2⟩)]
  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, mem_sdiff, and_imp,
    Dep, hI.subset_ground]
  exact ⟨fun h e heX heI ↦ ⟨fun hi ↦ h.1 e heI hi heX, h.2 heX⟩,
    fun h ↦ ⟨fun e heI hi heX ↦ (h e heX heI).1 hi,
      fun e heX ↦ (em (e ∈ I)).elim (fun h ↦ hI.subset_ground h) fun heI ↦ (h _ heX heI).2 ⟩⟩
/-
**Matroid.Indep.isBasis_of_forall_insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Inde
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.Indep I → I ⊆ X → (∀ e ∈
 X \ I, M.Dep (insert e I)) → M.IsBasis I X
参数：∀ e ∈ X \ I, M.Dep (insert e I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.Indep.isBasis_iff_forall_insert_dep`：∀ {α : Type u_1} {M : Matro
id α} {I X : Set α}, M.Indep I → I ⊆ X → (M.IsBasis I X ↔ ∀ e ∈ X \ I, M.Dep (in
sert e I))
-/
theorem Indep.isBasis_of_forall_insert (hI : M.Indep I) (hIX : I ⊆ X)
    (he : ∀ e ∈ X \ I, M.Dep (insert e I)) : M.IsBasis I X :=
  (hI.isBasis_iff_forall_insert_dep hIX).mpr he
/-
**Matroid.Indep.isBasis_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {e : α},   M.Indep I → (M.IsB
asis I (insert e I) ↔ M.Dep (insert e I) ∨ e ∈ I)
参数：M.IsBasis I (insert e I) ↔ M.Dep (insert e I) ∨ e ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.isBasis_iff_forall_insert_dep`：∀ {α : Type u_1} {M : Matro
id α} {I X : Set α}, M.Indep I → I ⊆ X → (M.IsBasis I X ↔ ∀ e ∈ X \ I, M.Dep (in
sert e I))
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem Indep.isBasis_insert_iff (hI : M.Indep I) :
    M.IsBasis I (insert e I) ↔ M.Dep (insert e I) ∨ e ∈ I := by
  simp_rw [hI.isBasis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff,
    and_iff_left hI.subset_ground, mem_sdiff, mem_insert_iff, or_and_right, and_not_self,
    or_false, and_imp, forall_eq]
  tauto
/-
**Matroid.IsBasis.iUnion_isBasis_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {ι : Type u_2} (X I : ι → Set α),   (∀ (i
 : ι), M.IsBasis (I i) (X i)) → M.Indep (⋃ i, I i) → M.IsBasis (⋃ i, I i) (⋃ i, 
X i)
参数：X I : ι → Set α；∀ (i : ι), M.IsBasis (I i) (X i)；⋃ i, I i；⋃ i, I i；⋃ i, X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_forall_insert`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α}, M.Indep I → I ⊆ X → (∀ e ∈ X \ I, M.Dep (insert e I)) → M.IsBasi
s I X
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Matroid.Dep.superset`：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   
M.Dep D → D ⊆ X → autoParam (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
· 使用定理 `Matroid.IsBasis.insert_dep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set 
α} {e : α}, M.IsBasis I X → e ∈ X \ I → M.Dep (insert e I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBasis.iUnion_isBasis_iUnion {ι : Type _} (X I : ι → Set α)
    (hI : ∀ i, M.IsBasis (I i) (X i)) (h_ind : M.Indep (⋃ i, I i)) :
    M.IsBasis (⋃ i, I i) (⋃ i, X i) := by
  refine h_ind.isBasis_of_forall_insert
    (iUnion_subset (fun i ↦ (hI i).subset.trans (subset_iUnion _ _))) ?_
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e ∈ X i)⟩⟩, he'⟩
  rw [mem_iUnion, not_exists] at he'
  refine ((hI i).insert_dep ⟨hes, he' _⟩).superset (insert_subset_insert (subset_iUnion _ _)) ?_
  rw [insert_subset_iff, iUnion_subset_iff, and_iff_left (fun i ↦ (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes
/-
**Matroid.IsBasis.isBasis_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {ι : Type u_2} [Nonempty ι] (
X : ι → Set α),   (∀ (i : ι), M.IsBasis I (X i)) → M.IsBasis I (⋃ i, X i)
参数：X : ι → Set α；∀ (i : ι), M.IsBasis I (X i)；⋃ i, X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `Matroid.IsBasis.iUnion_isBasis_iUnion`：∀ {α : Type u_1} {M : Matroid α} 
{ι : Type u_2} (X I : ι → Set α),   (∀ (i : ι), M.IsBasis (I i) (X i)) → M.Indep
 (⋃ i, I i) → M.IsBasis (⋃ …
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
theorem IsBasis.isBasis_iUnion {ι : Type _} [Nonempty ι] (X : ι → Set α)
    (hI : ∀ i, M.IsBasis I (X i)) : M.IsBasis I (⋃ i, X i) := by
  convert! IsBasis.iUnion_isBasis_iUnion X (fun _ ↦ I) (fun i ↦ hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep
/-
**Matroid.IsBasis.isBasis_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {Xs : Set (Set α)},   Xs.None
mpty → (∀ X ∈ Xs, M.IsBasis I X) → M.IsBasis I (⋃₀ Xs)
参数：Set α；∀ X ∈ Xs, M.IsBasis I X；⋃₀ Xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Matroid.IsBasis.isBasis_iUnion`：∀ {α : Type u_1} {M : Matroid α} {I : Se
t α} {ι : Type u_2} [Nonempty ι] (X : ι → Set α),   (∀ (i : ι), M.IsBasis I (X i
)) → M.IsBasis I (⋃ …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem IsBasis.isBasis_sUnion {Xs : Set (Set α)} (hne : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.IsBasis I X) : M.IsBasis I (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact IsBasis.isBasis_iUnion _ fun X ↦ h X X.prop
/-
**Matroid.Indep.isBasis_setOfPred_insert_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → M.IsBasis I {x |
 M.IsBasis I (insert x I)}
参数：insert x I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_forall_insert`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α}, M.Indep I → I ⊆ X → (∀ e ∈ X \ I, M.Dep (insert e I)) → M.IsBasi
s I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.eq_of_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I J : Set
 α}, M.Indep I → M.IsBasis J I → J = I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem Indep.isBasis_setOfPred_insert_isBasis (hI : M.Indep I) :
    M.IsBasis I {x | M.IsBasis I (insert x I)} := by
  refine hI.isBasis_of_forall_insert (fun e he ↦ (?_ : M.IsBasis _ _))
    (fun e he ↦ ⟨fun hu ↦ he.2 ?_, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.isBasis_self
  simpa using (hu.eq_of_isBasis he.1).symm

@[deprecated (since := "2026-07-09")]
alias Indep.isBasis_setOf_insert_isBasis := Indep.isBasis_setOfPred_insert_isBasis
/-
**Matroid.IsBasis.union_isBasis_union** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X Y : Set α},   M.IsBasis I X → M.Is
Basis J Y → M.Indep (I ∪ J) → M.IsBasis (I ∪ J) (X ∪ Y)
参数：I ∪ J；I ∪ J；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `Matroid.IsBasis.iUnion_isBasis_iUnion`：∀ {α : Type u_1} {M : Matroid α} 
{ι : Type u_2} (X I : ι → Set α),   (∀ (i : ι), M.IsBasis (I i) (X i)) → M.Indep
 (⋃ i, I i) → M.IsBasis (⋃ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBasis.union_isBasis_union (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
    (h : M.Indep (I ∪ J)) : M.IsBasis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  refine IsBasis.iUnion_isBasis_iUnion _ _ ?_ ?_
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_iUnion]
/-
**Matroid.IsBasis.isBasis_union** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y : Set α}, M.IsBasis I X → M.IsBasi
s I Y → M.IsBasis I (X ∪ Y)
参数：X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `Matroid.IsBasis.union_isBasis_union`：∀ {α : Type u_1} {M : Matroid α} {I
 J X Y : Set α},   M.IsBasis I X → M.IsBasis J Y → M.Indep (I ∪ J) → M.IsBasis (
I ∪ J) (X ∪ Y)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
theorem IsBasis.isBasis_union (hIX : M.IsBasis I X) (hIY : M.IsBasis I Y) :
    M.IsBasis I (X ∪ Y) := by
  convert! hIX.union_isBasis_union hIY _ <;> rw [union_self]; exact hIX.indep
/-
**Matroid.IsBasis.isBasis_union_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
asis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis I X → M.Indep 
J → I ⊆ J → M.IsBasis J (J ∪ X)
参数：J ∪ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Matroid.IsBasis.union_isBasis_union`：∀ {α : Type u_1} {M : Matroid α} {I
 J X Y : Set α},   M.IsBasis I X → M.IsBasis J Y → M.Indep (I ∪ J) → M.IsBasis (
I ∪ J) (X ∪ Y)
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
-/
theorem IsBasis.isBasis_union_of_subset (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) :
    M.IsBasis J (J ∪ X) := by
  convert! hJ.isBasis_self.union_isBasis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption
/-
**Matroid.IsBasis.insert_isBasis_insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {e : α},   M.IsBasis I X → 
M.Indep (insert e I) → M.IsBasis (insert e I) (insert e X)
参数：insert e I；insert e I；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.union_isBasis_union`：∀ {α : Type u_1} {M : Matroid α} {I
 J X Y : Set α},   M.IsBasis I X → M.IsBasis J Y → M.Indep (I ∪ J) → M.IsBasis (
I ∪ J) (X ∪ Y)
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem IsBasis.insert_isBasis_insert (hI : M.IsBasis I X) (h : M.Indep (insert e I)) :
    M.IsBasis (insert e I) (insert e X) := by
  simp_rw [← union_singleton] at *
  exact hI.union_isBasis_union (h.subset subset_union_right).isBasis_self h
/-
**Matroid.IsBase.isBase_of_isBasis_superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B I X : Set α}, M.IsBase B → B ⊆ X → M.I
sBasis I X → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.Indep.exists_insert_of_not_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B I : Set α}, M.Indep I → ¬M.IsBase I → M.IsBase B → ∃ e ∈ B \ I, M.Indep (
insert e I)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBase.isBase_of_isBasis_superset (hB : M.IsBase B) (hBX : B ⊆ X) (hIX : M.IsBasis I X) :
    M.IsBase I := by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_isBase h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)
/-
**Matroid.Indep.exists_isBase_subset_union_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Mat
roid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B I : Set α}, M.Indep I → M.IsBase B → ∃
 B', M.IsBase B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Matroid.IsBase.isBase_of_isBasis_superset`：∀ {α : Type u_1} {M : Matroid
 α} {B I X : Set α}, M.IsBase B → B ⊆ X → M.IsBasis I X → M.IsBase I
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
theorem Indep.exists_isBase_subset_union_isBase (hI : M.Indep I) (hB : M.IsBase B) :
    ∃ B', M.IsBase B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B := by
  obtain ⟨B', hB', hIB'⟩ := hI.subset_isBasis_of_subset <| subset_union_left (t := B)
  exact ⟨B', hB.isBase_of_isBasis_superset subset_union_right hB', hIB', hB'.subset⟩
/-
**Matroid.IsBasis.inter_eq_of_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Basis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis I X → I ⊆ J → 
M.Indep J → J ∩ X = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBasis.inter_eq_of_subset_indep (hIX : M.IsBasis I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I :=
(subset_inter hIJ hIX.subset).antisymm'
  (fun _ he ↦ hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ)))
/-
**Matroid.IsBasis'.inter_eq_of_subset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → I ⊆ J →
 M.Indep J → J ∩ X = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.inter_eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid 
α} {I J X : Set α}, M.IsBasis I X → I ⊆ J → M.Indep J → J ∩ X = I
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
theorem IsBasis'.inter_eq_of_subset_indep (hI : M.IsBasis' I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I := by
  rw [← hI.isBasis_inter_ground.inter_eq_of_subset_indep hIJ hJ, inter_comm X, ← inter_assoc,
    inter_eq_self_of_subset_left hJ.subset_ground]
/-
**Matroid.IsBase.isBasis_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B X : Set α},   autoParam (X ⊆ M.E) Matr
oid.IsBase.isBasis_of_subset._auto_1 → M.IsBase B → B ⊆ X → M.IsBasis B X
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff`：isBasis_iff (hX : X subseteq M.E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
-/
theorem IsBase.isBasis_of_subset (hX : X ⊆ M.E := by aesop_mat) (hB : M.IsBase B) (hBX : B ⊆ X) :
    M.IsBasis B X := by
  rw [isBasis_iff, and_iff_right hB.indep, and_iff_right hBX]
  exact fun J hJ hBJ _ ↦ hB.eq_of_subset_indep hJ hBJ
/-
**Matroid.exists_isBasis_disjoint_isBasis_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid`。
形式化陈述：exists_isBasis_disjoint_isBasis_of_subset (M : Matroid α) {X Y : Set α} (h
XY : X subseteq Y) (hY : Y subseteq M.E
参数：M : Matroid α；hXY : X subseteq Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis_subset_isBasis`：exists_isBasis_subset_isBasis (M 
: Matroid α) (hXY : X subseteq Y) (hY : Y subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
-/
theorem exists_isBasis_disjoint_isBasis_of_subset (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ I J, M.IsBasis I X ∧ M.IsBasis (I ∪ J) Y ∧ Disjoint X J := by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_isBasis_subset_isBasis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_sdiff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
  exact heI <| hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

end IsBasis

section Finite

/-- For finite `E`, finitely many matroids have ground set contained in `E`. -/
/-
**Matroid.finite_setOfPred_matroid** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：finite_setOfPred_matroid {E : Set α} (hE : E.Finite) : {M : Matroid α | M.
E subseteq E}.Finite
参数：hE : E.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `Set.Finite.finite_subsets`：∀ {α : Type u} {a : Set α}, a.Finite → {b | b
 ⊆ a}.Finite
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E

--- 原说明 ---
For finite `E`, finitely many matroids have ground set contained in `E`.
-/
theorem finite_setOfPred_matroid {E : Set α} (hE : E.Finite) :
    {M : Matroid α | M.E ⊆ E}.Finite := by
  set f : Matroid α → Set α × (Set (Set α)) := fun M ↦ ⟨M.E, {B | M.IsBase B}⟩
  have hf : f.Injective := by
    refine fun M M' hMM' ↦ ?_
    rw [Prod.mk.injEq, and_comm, Set.ext_iff, and_comm] at hMM'
    exact ext_isBase hMM'.1 (fun B _ ↦ hMM'.2 B)
  rw [← Set.finite_image_iff hf.injOn]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E ⊆ E, rfl⟩
  simp only [Set.mem_prod, Set.mem_ofPred_eq]
  exact ⟨hE, fun B hB ↦ hB.subset_ground.trans hE⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid := finite_setOfPred_matroid

/-- For finite `E`, finitely many matroids have ground set `E`. -/
/-
**Matroid.finite_setOfPred_matroid'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：finite_setOfPred_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M
.E = E}.Finite
参数：hE : E.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.finite_setOfPred_matroid`：finite_setOfPred_matroid {E : Set α} (
hE : E.Finite) : {M : Matroid α | M.E subseteq E}.Finite
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a

--- 原说明 ---
For finite `E`, finitely many matroids have ground set `E`.
-/
theorem finite_setOfPred_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E = E}.Finite :=
  (finite_setOfPred_matroid hE).subset (fun M ↦ by rintro rfl; exact subset_refl M.E)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_matroid' := finite_setOfPred_matroid'

end Finite

end Matroid

