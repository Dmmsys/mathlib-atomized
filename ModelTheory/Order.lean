/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Finset.Sort
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Fraisse
public import Mathlib.Order.CountableDenseLinearOrder

/-!
# Ordered First-Ordered Structures

This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions

- `FirstOrder.Language.order` is the language consisting of a single relation representing `≤`.
- `FirstOrder.Language.IsOrdered` points out a specific symbol in a language as representing `≤`.
- `FirstOrder.Language.OrderedStructure` indicates that the `≤` symbol in an ordered language
  is interpreted as the actual relation `≤` in a particular structure.
- `FirstOrder.Language.linearOrderTheory` and similar define the theories of preorders,
  partial orders, and linear orders.
- `FirstOrder.Language.dlo` defines the theory of dense linear orders without endpoints, a
  particularly useful example in model theory.
- `FirstOrder.Language.orderStructure` is the structure on an ordered type, assigning the symbol
  representing `≤` to the actual relation `≤`.
- Conversely, `FirstOrder.Language.LEOfStructure`, `FirstOrder.Language.preorderOfModels`,
  `FirstOrder.Language.partialOrderOfModels`, and `FirstOrder.Language.linearOrderOfModels`
  are the orders induced by first-order structures modelling the relevant theory.

## Main Results

- `PartialOrder`s model the theory of partial orders, `LinearOrder`s model the theory of
  linear orders, and dense linear orders without endpoints model `Language.dlo`.
- Under `L.orderedStructure` assumptions, elements of any `L.HomClass M N` are monotone, and
  strictly monotone if injective.
- Under `Language.order.orderedStructure` assumptions, any `OrderHomClass` has an instance of
  `L.HomClass M N`, while `M ↪o N` and any `OrderIsoClass` have an instance of
  `L.StrongHomClass M N`.
- `FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo` shows that any countable nonempty
  model of the theory of linear orders is a Fraïssé limit of the class of finite models of the
  theory of linear orders.
- `FirstOrder.Language.isFraisse_finite_linear_order` shows that the class of finite models of the
  theory of linear orders is Fraïssé.
- `FirstOrder.Language.aleph0_categorical_dlo` shows that the theory of dense linear orders is
  `ℵ₀`-categorical, and thus complete.

-/

@[expose] public section


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : Nat}

/--
Inductive type `orderRel` / 归纳类型 `orderRel`

English:
inductive orderRel
  parameters: : Nat -> Type
  constructors (1):
    - le: orderRel 2

中文:
归纳类型 orderRel
  参数: : 自然数 -> Type
  构造子 (1 个):
    - le: orderRel 2

Depends on / 依赖: orderRel
-/
inductive orderRel : Nat -> Type
  | le : orderRel 2
  deriving DecidableEq

/--
Definition of `order` / `order` 的定义

English:
definition order
  signature: : Language
  body: ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational

中文:
定义 order
  签名: : Language
  定义体: ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational
-/
protected def order : Language := ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational

namespace order

@[simp]
/--
lemma `forall_relations` / 引理 `forall_relations`

English:
lemma forall_relations
  given: {P : forall (n) (_ : Language.order.Relations n), Prop}
  proof: ⟨fun h => h _, fun h n R =>
      match n, R with
      | 2, .le => h⟩

中文:
引理 forall_relations
  条件: {P : 对任意 (n) (_ : Language.order.Relations n), 命题}
  证明: ⟨fun h => h _, fun h n R =>
      match n, R with
      | 2, .le => h⟩
-/
lemma forall_relations {P : forall (n) (_ : Language.order.Relations n), Prop} :
    (forall {n} (R), P n R) ↔ P 2 .le := ⟨fun h => h _, fun h n R =>
      match n, R with
      | 2, .le => h⟩

/--
Instance `instSubsingleton` / 实例 `instSubsingleton`

English:
instance instSubsingleton
  signature: : Subsingleton (Language.order.Relations n)
  body: ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

中文:
实例 instSubsingleton
  签名: : Subsingleton (Language.order.Relations n)
  定义体: ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
-/
instance instSubsingleton : Subsingleton (Language.order.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty (Language.order.Relations 0)
  body: ⟨fun x => by cases x⟩

中文:
实例 :
  签名: IsEmpty (Language.order.Relations 0)
  定义体: ⟨fun x => by cases x⟩
-/
instance : IsEmpty (Language.order.Relations 0) := ⟨fun x => by cases x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (Σ n, Language.order.Relations n)
  body: ⟨⟨⟨2, .le⟩⟩, fun ⟨n, R⟩ =>
      match n, R with
      | 2, .le => rfl⟩

中文:
实例 :
  签名: Unique (Σ n, Language.order.Relations n)
  定义体: ⟨⟨⟨2, .le⟩⟩, fun ⟨n, R⟩ =>
      match n, R with
      | 2, .le => rfl⟩
-/
instance : Unique (Σ n, Language.order.Relations n) :=
  ⟨⟨⟨2, .le⟩⟩, fun ⟨n, R⟩ =>
      match n, R with
      | 2, .le => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique Language.order.Symbols
  body: ⟨⟨Sum.inr default⟩, by
  have : IsEmpty (Σ n, Language.order.Functions n) := isEmpty_sigma.2 inferInstance
  simp only [Symbols, Sum.forall, reduceCtorEq, Sum.inr.injEq, IsEmpty.forall_iff, true_and]
  exact Unique.eq_default⟩

@[simp]

中文:
实例 :
  签名: Unique Language.order.Symbols
  定义体: ⟨⟨Sum.inr default⟩, by
  have : IsEmpty (Σ n, Language.order.Functions n) := isEmpty_sigma.2 inferInstance
  simp only [Symbols, Sum.forall, reduceCtorEq, Sum.inr.injEq, IsEmpty.forall_iff, true_and]
  exact Unique.eq_default⟩

@[simp]

Depends on / 依赖: Functions, IsEmpty, IsEmpty.forall_iff, Language, Language.order.Functions, Sum.forall, Sum.inr, Sum.inr.injEq, Symbols, Unique, Unique.eq_default, eq_default, forall_iff, isEmpty_sigma, reduceCtorEq, true_and
-/
instance : Unique Language.order.Symbols := ⟨⟨Sum.inr default⟩, by
  have : IsEmpty (Σ n, Language.order.Functions n) := isEmpty_sigma.2 inferInstance
  simp only [Symbols, Sum.forall, reduceCtorEq, Sum.inr.injEq, IsEmpty.forall_iff, true_and]
  exact Unique.eq_default⟩

@[simp]
/--
lemma `card_eq_one` / 引理 `card_eq_one`

English:
lemma card_eq_one
  statement: Language.order.card = 1
  proof: by simp [card]

中文:
引理 card_eq_one
  结论: Language.order.card = 1
  证明: by simp [card]
-/
lemma card_eq_one : Language.order.card = 1 := by simp [card]

end order

/--
Definition of `IsOrdered` / `IsOrdered` 的定义

English:
class IsOrdered
  parameters: (L : Language.{u, v})
  axioms and operations (1):
    - leSymb : L.Relations 2

中文:
类 IsOrdered
  参数: (L : Language.{u, v})
  公理与运算 (1 个):
    - leSymb : L.Relations 2
-/
class IsOrdered (L : Language.{u, v}) where
  /-- The relation symbol representing `≤`. -/
  leSymb : L.Relations 2

export IsOrdered (leSymb)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrdered Language.order
  body: ⟨.le⟩

中文:
实例 :
  签名: IsOrdered Language.order
  定义体: ⟨.le⟩
-/
instance : IsOrdered Language.order :=
  ⟨.le⟩

/--
lemma `order.relation_eq_leSymb` / 引理 `order.relation_eq_leSymb`

English:
lemma order.relation_eq_leSymb
  statement: (R : Language.order.Relations 2) -> R = leSymb

中文:
引理 order.relation_eq_leSymb
  结论: (R : Language.order.Relations 2) -> R = leSymb
-/
lemma order.relation_eq_leSymb : (R : Language.order.Relations 2) -> R = leSymb
  | .le => rfl

section IsOrdered

variable [IsOrdered L]

/--
Definition of `Term.le` / `Term.le` 的定义

English:
definition Term.le
  signature: (t₁ t₂ : L.Term (α oplus (Fin n)))
  body: leSymb.boundedFormula₂ t₁ t₂

中文:
定义 Term.le
  签名: (t₁ t₂ : L.Term (α oplus (Fin n)))
  定义体: leSymb.boundedFormula₂ t₁ t₂

Depends on / 依赖: leSymb, leSymb.boundedFormula
-/
def Term.le (t₁ t₂ : L.Term (α oplus (Fin n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂

/--
Definition of `Term.lt` / `Term.lt` 的定义

English:
definition Term.lt
  signature: (t₁ t₂ : L.Term (α oplus (Fin n)))
  body: t₁.le t₂ ⊓ ∼(t₂.le t₁)

中文:
定义 Term.lt
  签名: (t₁ t₂ : L.Term (α oplus (Fin n)))
  定义体: t₁.le t₂ ⊓ ∼(t₂.le t₁)
-/
def Term.lt (t₁ t₂ : L.Term (α oplus (Fin n))) : L.BoundedFormula α n :=
  t₁.le t₂ ⊓ ∼(t₂.le t₁)

variable (L)

/--
Definition of `orderLHom` / `orderLHom` 的定义

English:
definition orderLHom
  signature: : Language.order ->ᴸ L where

中文:
定义 orderLHom
  签名: : Language.order ->ᴸ L where
-/
@[simps] def orderLHom : Language.order ->ᴸ L where
  onRelation | _, .le => leSymb

@[simp]
/--
theorem `orderLHom_leSymb` / 定理 `orderLHom_leSymb`

English:
theorem orderLHom_leSymb
  proof: rfl

@[simp]

中文:
定理 orderLHom_leSymb
  证明: rfl

@[simp]
-/
theorem orderLHom_leSymb :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl

@[simp]
/--
theorem `orderLHom_order` / 定理 `orderLHom_order`

English:
theorem orderLHom_order
  statement: orderLHom Language.order = LHom.id Language.order
  proof: LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

中文:
定理 orderLHom_order
  结论: orderLHom Language.order = LHom.id Language.order
  证明: LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

Depends on / 依赖: LHom.funext, Subsingleton, Subsingleton.elim
-/
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/--
Definition of `preorderTheory` / `preorderTheory` 的定义

English:
definition preorderTheory
  signature: : L.Theory
  body: {leSymb.reflexive, leSymb.transitive}

中文:
定义 preorderTheory
  签名: : L.Theory
  定义体: {leSymb.reflexive, leSymb.transitive}

Depends on / 依赖: leSymb, leSymb.reflexive, leSymb.transitive, reflexive, transitive
-/
def preorderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.transitive}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Theory.IsUniversal L.preorderTheory
  body: ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

中文:
实例 :
  签名: Theory.IsUniversal L.preorderTheory
  定义体: ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq, forall_eq_or_imp, isUniversal_reflexive, isUniversal_transitive, leSymb, leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive, mem_insert_iff, mem_singleton_iff, preorderTheory
-/
instance : Theory.IsUniversal L.preorderTheory := ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

/--
Definition of `partialOrderTheory` / `partialOrderTheory` 的定义

English:
definition partialOrderTheory
  signature: : L.Theory
  body: insert leSymb.antisymmetric L.preorderTheory

中文:
定义 partialOrderTheory
  签名: : L.Theory
  定义体: insert leSymb.antisymmetric L.preorderTheory

Depends on / 依赖: L.preorderTheory, antisymmetric, insert, leSymb, leSymb.antisymmetric, preorderTheory
-/
def partialOrderTheory : L.Theory :=
  insert leSymb.antisymmetric L.preorderTheory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Theory.IsUniversal L.partialOrderTheory
  body: Theory.IsUniversal.insert leSymb.isUniversal_antisymmetric

中文:
实例 :
  签名: Theory.IsUniversal L.partialOrderTheory
  定义体: Theory.IsUniversal.insert leSymb.isUniversal_antisymmetric

Depends on / 依赖: IsUniversal, Theory, Theory.IsUniversal.insert, insert, isUniversal_antisymmetric, leSymb, leSymb.isUniversal_antisymmetric
-/
instance : Theory.IsUniversal L.partialOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_antisymmetric

/--
Definition of `linearOrderTheory` / `linearOrderTheory` 的定义

English:
definition linearOrderTheory
  signature: : L.Theory
  body: insert leSymb.total L.partialOrderTheory

中文:
定义 linearOrderTheory
  签名: : L.Theory
  定义体: insert leSymb.total L.partialOrderTheory

Depends on / 依赖: L.partialOrderTheory, insert, leSymb, leSymb.total, partialOrderTheory
-/
def linearOrderTheory : L.Theory :=
  insert leSymb.total L.partialOrderTheory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Theory.IsUniversal L.linearOrderTheory
  body: Theory.IsUniversal.insert leSymb.isUniversal_total

example [L.Structure M] [M ⊨ L.linearOrderTheory] (S : L.Substructure M) :
    S ⊨ L.linearOrderTheory := inferInstance

中文:
实例 :
  签名: Theory.IsUniversal L.linearOrderTheory
  定义体: Theory.IsUniversal.insert leSymb.isUniversal_total

example [L.Structure M] [M ⊨ L.linearOrderTheory] (S : L.Substructure M) :
    S ⊨ L.linearOrderTheory := inferInstance

Depends on / 依赖: IsUniversal, Theory, Theory.IsUniversal.insert, insert, isUniversal_total, leSymb, leSymb.isUniversal_total
-/
instance : Theory.IsUniversal L.linearOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_total

example [L.Structure M] [M ⊨ L.linearOrderTheory] (S : L.Substructure M) :
    S ⊨ L.linearOrderTheory := inferInstance

/--
Definition of `noTopOrderSentence` / `noTopOrderSentence` 的定义

English:
definition noTopOrderSentence
  signature: : L.Sentence
  body: forall' exists' ∼((&1).le &0)

中文:
定义 noTopOrderSentence
  签名: : L.Sentence
  定义体: forall' exists' ∼((&1).le &0)
-/
def noTopOrderSentence : L.Sentence :=
  forall' exists' ∼((&1).le &0)

/--
Definition of `noBotOrderSentence` / `noBotOrderSentence` 的定义

English:
definition noBotOrderSentence
  signature: : L.Sentence
  body: forall' exists' ∼((&0).le &1)

中文:
定义 noBotOrderSentence
  签名: : L.Sentence
  定义体: forall' exists' ∼((&0).le &1)
-/
def noBotOrderSentence : L.Sentence :=
  forall' exists' ∼((&0).le &1)

/--
Definition of `denselyOrderedSentence` / `denselyOrderedSentence` 的定义

English:
definition denselyOrderedSentence
  signature: : L.Sentence
  body: forall' forall' ((&0).lt &1 ⟹ exists' ((&0).lt &2 ⊓ (&2).lt &1))

中文:
定义 denselyOrderedSentence
  签名: : L.Sentence
  定义体: forall' forall' ((&0).lt &1 ⟹ exists' ((&0).lt &2 ⊓ (&2).lt &1))
-/
def denselyOrderedSentence : L.Sentence :=
  forall' forall' ((&0).lt &1 ⟹ exists' ((&0).lt &2 ⊓ (&2).lt &1))

/--
Definition of `dlo` / `dlo` 的定义

English:
definition dlo
  signature: : L.Theory
  body: L.linearOrderTheory union {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}

中文:
定义 dlo
  签名: : L.Theory
  定义体: L.linearOrderTheory union {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}

Depends on / 依赖: L.denselyOrderedSentence, L.linearOrderTheory, L.noBotOrderSentence, L.noTopOrderSentence, denselyOrderedSentence, linearOrderTheory, noBotOrderSentence, noTopOrderSentence
-/
def dlo : L.Theory :=
  L.linearOrderTheory union {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}

variable [L.Structure M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory
  body: h.mono Set.subset_union_left

中文:
实例 [h
  签名: : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory
  定义体: h.mono Set.subset_union_left

Depends on / 依赖: Set.subset_union_left, h.mono, subset_union_left
-/
instance [h : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory := h.mono Set.subset_union_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory
  body: h.mono (Set.subset_insert _ _)

中文:
实例 [h
  签名: : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory
  定义体: h.mono (Set.subset_insert _ _)

Depends on / 依赖: Set.subset_insert, h.mono, subset_insert
-/
instance [h : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory := h.mono (Set.subset_insert _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory
  body: h.mono (Set.subset_insert _ _)

中文:
实例 [h
  签名: : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory
  定义体: h.mono (Set.subset_insert _ _)

Depends on / 依赖: Set.subset_insert, h.mono, subset_insert
-/
instance [h : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory := h.mono (Set.subset_insert _ _)

end IsOrdered

/--
Instance `sum.instIsOrdered` / 实例 `sum.instIsOrdered`

English:
instance sum.instIsOrdered
  signature: : IsOrdered (L.sum Language.order)
  body: ⟨Sum.inr IsOrdered.leSymb⟩

中文:
实例 sum.instIsOrdered
  签名: : IsOrdered (L.sum Language.order)
  定义体: ⟨Sum.inr IsOrdered.leSymb⟩

Depends on / 依赖: IsOrdered, IsOrdered.leSymb, Sum.inr, leSymb
-/
instance sum.instIsOrdered : IsOrdered (L.sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

variable (L M)

/-- Any linearly-ordered type is naturally a structure in the language `Language.order`.
This is not an instance, because sometimes the `Language.order.Structure` is defined first. -/
@[instance_reducible]
/--
Definition of `orderStructure` / `orderStructure` 的定义

English:
definition orderStructure
  signature: [LE M]

中文:
定义 orderStructure
  签名: [LE M]
-/
def orderStructure [LE M] : Language.order.Structure M where
  RelMap | .le => (fun x => x 0 <= x 1)

/--
Definition of `OrderedStructure` / `OrderedStructure` 的定义

English:
class OrderedStructure
  parameters: [L.IsOrdered] [LE M] [L.Structure M]
  axioms and operations (1):
    - relMap_leSymb : forall (x : Fin 2 -> M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 <= x 1)

中文:
类 OrderedStructure
  参数: [L.IsOrdered] [LE M] [L.Structure M]
  公理与运算 (1 个):
    - relMap_leSymb : 对任意 (x : Fin 2 -> M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 <= x 1)
-/
class OrderedStructure [L.IsOrdered] [LE M] [L.Structure M] : Prop where
  relMap_leSymb : forall (x : Fin 2 -> M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 <= x 1)

export OrderedStructure (relMap_leSymb)

attribute [simp] relMap_leSymb

variable {L M}

section order_to_structure

variable [IsOrdered L] [L.Structure M]

section LE

variable [LE M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Language.order.Structure
  signature: M] [Language.order.OrderedStructure M]
  body: by
    rw [← orderLHom_leSymb L]; rw [LHom.IsExpansionOn.map_onRelation]; rw [relMap_leSymb]

中文:
实例 [Language.order.Structure
  签名: M] [Language.order.OrderedStructure M]
  定义体: by
    rw [← orderLHom_leSymb L]; rw [LHom.IsExpansionOn.map_onRelation]; rw [relMap_leSymb]

Depends on / 依赖: IsExpansionOn, LHom.IsExpansionOn.map_onRelation, map_onRelation, orderLHom_leSymb, relMap_leSymb
-/
instance [Language.order.Structure M] [Language.order.OrderedStructure M]
    [(orderLHom L).IsExpansionOn M] : L.OrderedStructure M where
  relMap_leSymb x := by
    rw [← orderLHom_leSymb L]; rw [LHom.IsExpansionOn.map_onRelation]; rw [relMap_leSymb]

variable [L.OrderedStructure M]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Language.order.Structure
  signature: M] [Language.order.OrderedStructure M] :
  body: by simp [order.relation_eq_leSymb]

中文:
实例 [Language.order.Structure
  签名: M] [Language.order.OrderedStructure M] :
  定义体: by simp [order.relation_eq_leSymb]

Depends on / 依赖: order.relation_eq_leSymb, relation_eq_leSymb
-/
instance [Language.order.Structure M] [Language.order.OrderedStructure M] :
    LHom.IsExpansionOn (orderLHom L) M where
  map_onRelation := by simp [order.relation_eq_leSymb]

instance (S : L.Substructure M) : L.OrderedStructure S := ⟨fun x => relMap_leSymb (S.subtype ∘ x)⟩

@[simp]
/--
theorem `Term.realize_le` / 定理 `Term.realize_le`

English:
theorem Term.realize_le
  statement: {t₁ t₂ : L.Term (α oplus (Fin n))} {v : α -> M}
  proof: by
  simp [Term.le]

中文:
定理 Term.realize_le
  结论: {t₁ t₂ : L.Term (α oplus (Fin n))} {v : α -> M}
  证明: by
  simp [Term.le]

Depends on / 依赖: Term.le
-/
theorem Term.realize_le {t₁ t₂ : L.Term (α oplus (Fin n))} {v : α -> M}
    {xs : Fin n -> M} :
    (t₁.le t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) <= t₂.realize (Sum.elim v xs) := by
  simp [Term.le]

/--
theorem `realize_noTopOrder_iff` / 定理 `realize_noTopOrder_iff`

English:
theorem realize_noTopOrder_iff
  statement: M ⊨ L.noTopOrderSentence ↔ NoTopOrder M
  proof: by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a

中文:
定理 realize_noTopOrder_iff
  结论: M ⊨ L.noTopOrderSentence ↔ NoTopOrder M
  证明: by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_not, Formula, Formula.Realize, Realize, Sentence, Sentence.Realize, Term.realize_le, exists_not_le, noTopOrderSentence, realize_all, realize_ex, realize_le, realize_not
-/
theorem realize_noTopOrder_iff : M ⊨ L.noTopOrderSentence ↔ NoTopOrder M := by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a

/--
theorem `realize_noBotOrder_iff` / 定理 `realize_noBotOrder_iff`

English:
theorem realize_noBotOrder_iff
  statement: M ⊨ L.noBotOrderSentence ↔ NoBotOrder M
  proof: by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a

中文:
定理 realize_noBotOrder_iff
  结论: M ⊨ L.noBotOrderSentence ↔ NoBotOrder M
  证明: by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_not, Formula, Formula.Realize, Realize, Sentence, Sentence.Realize, Term.realize_le, exists_not_ge, noBotOrderSentence, realize_all, realize_ex, realize_le, realize_not
-/
theorem realize_noBotOrder_iff : M ⊨ L.noBotOrderSentence ↔ NoBotOrder M := by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a

variable (L M)

@[simp]
/--
theorem `realize_noTopOrder` / 定理 `realize_noTopOrder`

English:
theorem realize_noTopOrder
  given: [h : NoTopOrder M]
  statement: M ⊨ L.noTopOrderSentence
  proof: realize_noTopOrder_iff.2 h

@[simp]

中文:
定理 realize_noTopOrder
  条件: [h : NoTopOrder M]
  结论: M ⊨ L.noTopOrderSentence
  证明: realize_noTopOrder_iff.2 h

@[simp]

Depends on / 依赖: realize_noTopOrder_iff
-/
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ L.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h

@[simp]
/--
theorem `realize_noBotOrder` / 定理 `realize_noBotOrder`

English:
theorem realize_noBotOrder
  given: [h : NoBotOrder M]
  statement: M ⊨ L.noBotOrderSentence
  proof: realize_noBotOrder_iff.2 h

中文:
定理 realize_noBotOrder
  条件: [h : NoBotOrder M]
  结论: M ⊨ L.noBotOrderSentence
  证明: realize_noBotOrder_iff.2 h

Depends on / 依赖: realize_noBotOrder_iff
-/
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ L.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h

/--
theorem `noTopOrder_of_dlo` / 定理 `noTopOrder_of_dlo`

English:
theorem noTopOrder_of_dlo
  given: [M ⊨ L.dlo]
  statement: NoTopOrder M
  proof: realize_noTopOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or]))

中文:
定理 noTopOrder_of_dlo
  条件: [M ⊨ L.dlo]
  结论: NoTopOrder M
  证明: realize_noTopOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or]))

Depends on / 依赖: L.dlo.realize_sentence_of_mem, Set.mem_insert_iff, Set.union_insert, Set.union_singleton, mem_insert_iff, realize_noTopOrder_iff, realize_sentence_of_mem, true_or, union_insert, union_singleton
-/
theorem noTopOrder_of_dlo [M ⊨ L.dlo] : NoTopOrder M :=
  realize_noTopOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or]))

/--
theorem `noBotOrder_of_dlo` / 定理 `noBotOrder_of_dlo`

English:
theorem noBotOrder_of_dlo
  given: [M ⊨ L.dlo]
  statement: NoBotOrder M
  proof: realize_noBotOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

中文:
定理 noBotOrder_of_dlo
  条件: [M ⊨ L.dlo]
  结论: NoBotOrder M
  证明: realize_noBotOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

Depends on / 依赖: L.dlo.realize_sentence_of_mem, Set.mem_insert_iff, Set.union_insert, Set.union_singleton, mem_insert_iff, or_true, realize_noBotOrder_iff, realize_sentence_of_mem, true_or, union_insert, union_singleton
-/
theorem noBotOrder_of_dlo [M ⊨ L.dlo] : NoBotOrder M :=
  realize_noBotOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

end LE

@[simp]
/--
theorem `orderedStructure_iff` / 定理 `orderedStructure_iff`

English:
theorem orderedStructure_iff
  proof: ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
定理 orderedStructure_iff
  证明: ⟨fun _ => inferInstance, fun _ => inferInstance⟩
-/
theorem orderedStructure_iff
    [LE M] [Language.order.Structure M] [Language.order.OrderedStructure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

section Preorder

variable [Preorder M] [L.OrderedStructure M]

/--
Instance `model_preorder` / 实例 `model_preorder`

English:
instance model_preorder
  signature: : M ⊨ L.preorderTheory
  body: by
  simp only [preorderTheory, Theory.model_insert_iff, Relations.realize_reflexive, relMap_leSymb,
    Theory.model_singleton_iff, Relations.realize_transitive, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ⟨inferInstance, inferInstance⟩

@[simp]

中文:
实例 model_preorder
  签名: : M ⊨ L.preorderTheory
  定义体: by
  simp only [preorderTheory, Theory.model_insert_iff, Relations.realize_reflexive, relMap_leSymb,
    Theory.model_singleton_iff, Relations.realize_transitive, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ⟨inferInstance, inferInstance⟩

@[simp]

Depends on / 依赖: Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, Relations, Relations.realize_reflexive, Relations.realize_transitive, Theory, Theory.model_insert_iff, Theory.model_singleton_iff, cons_val_one, cons_val_zero, model_insert_iff, model_singleton_iff, preorderTheory, realize_reflexive, realize_transitive, relMap_leSymb
-/
instance model_preorder : M ⊨ L.preorderTheory := by
  simp only [preorderTheory, Theory.model_insert_iff, Relations.realize_reflexive, relMap_leSymb,
    Theory.model_singleton_iff, Relations.realize_transitive, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ⟨inferInstance, inferInstance⟩

@[simp]
/--
theorem `Term.realize_lt` / 定理 `Term.realize_lt`

English:
theorem Term.realize_lt
  statement: {t₁ t₂ : L.Term (α oplus (Fin n))}
  proof: by
  simp [Term.lt, lt_iff_le_not_ge]

中文:
定理 Term.realize_lt
  结论: {t₁ t₂ : L.Term (α oplus (Fin n))}
  证明: by
  simp [Term.lt, lt_iff_le_not_ge]

Depends on / 依赖: Term.lt, lt_iff_le_not_ge
-/
theorem Term.realize_lt {t₁ t₂ : L.Term (α oplus (Fin n))}
    {v : α -> M} {xs : Fin n -> M} :
    (t₁.lt t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [Term.lt, lt_iff_le_not_ge]

/--
theorem `realize_denselyOrdered_iff` / 定理 `realize_denselyOrdered_iff`

English:
theorem realize_denselyOrdered_iff
  proof: by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize_lt,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between 

中文:
定理 realize_denselyOrdered_iff
  证明: by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize_lt,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between 

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf, Formula, Formula.Realize, Realize, Sentence, Sentence.Realize, Term.realize_lt, denselyOrderedSentence, exists_between, realize_all, realize_ex, realize_imp, realize_inf, realize_lt
-/
theorem realize_denselyOrdered_iff :
    M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered M := by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize_lt,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between ab

@[simp]
/--
theorem `realize_denselyOrdered` / 定理 `realize_denselyOrdered`

English:
theorem realize_denselyOrdered
  given: [h : DenselyOrdered M]
  proof: realize_denselyOrdered_iff.2 h

中文:
定理 realize_denselyOrdered
  条件: [h : DenselyOrdered M]
  证明: realize_denselyOrdered_iff.2 h

Depends on / 依赖: realize_denselyOrdered_iff
-/
theorem realize_denselyOrdered [h : DenselyOrdered M] :
    M ⊨ L.denselyOrderedSentence :=
  realize_denselyOrdered_iff.2 h

variable (L) (M)

/--
theorem `denselyOrdered_of_dlo` / 定理 `denselyOrdered_of_dlo`

English:
theorem denselyOrdered_of_dlo
  given: [M ⊨ L.dlo]
  statement: DenselyOrdered M
  proof: realize_denselyOrdered_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

中文:
定理 denselyOrdered_of_dlo
  条件: [M ⊨ L.dlo]
  结论: DenselyOrdered M
  证明: realize_denselyOrdered_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

Depends on / 依赖: L.dlo.realize_sentence_of_mem, Set.mem_insert_iff, Set.union_insert, Set.union_singleton, mem_insert_iff, or_true, realize_denselyOrdered_iff, realize_sentence_of_mem, true_or, union_insert, union_singleton
-/
theorem denselyOrdered_of_dlo [M ⊨ L.dlo] : DenselyOrdered M :=
  realize_denselyOrdered_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

end Preorder

/--
Instance `model_partialOrder` / 实例 `model_partialOrder`

English:
instance model_partialOrder
  signature: [PartialOrder M] [L.OrderedStructure M]
  body: by
  simp only [partialOrderTheory, Theory.model_insert_iff, Relations.realize_antisymmetric,
    relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    model_preorder, and_true]
  infer_instance

中文:
实例 model_partialOrder
  签名: [PartialOrder M] [L.OrderedStructure M]
  定义体: by
  simp only [partialOrderTheory, Theory.model_insert_iff, Relations.realize_antisymmetric,
    relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    model_preorder, and_true]
  infer_instance

Depends on / 依赖: Fin.isValue, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, Relations, Relations.realize_antisymmetric, Theory, Theory.model_insert_iff, and_true, cons_val_one, cons_val_zero, infer_instance, isValue, model_insert_iff, model_preorder, partialOrderTheory, realize_antisymmetric, relMap_leSymb
-/
instance model_partialOrder [PartialOrder M] [L.OrderedStructure M] :
    M ⊨ L.partialOrderTheory := by
  simp only [partialOrderTheory, Theory.model_insert_iff, Relations.realize_antisymmetric,
    relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    model_preorder, and_true]
  infer_instance

section LinearOrder

variable [LinearOrder M] [L.OrderedStructure M]

/--
Instance `model_linearOrder` / 实例 `model_linearOrder`

English:
instance model_linearOrder
  signature: : M ⊨ L.linearOrderTheory
  body: by
  simp only [linearOrderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, model_partialOrder,
    and_true]
  infer_instance

中文:
实例 model_linearOrder
  签名: : M ⊨ L.linearOrderTheory
  定义体: by
  simp only [linearOrderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, model_partialOrder,
    and_true]
  infer_instance

Depends on / 依赖: Fin.isValue, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, Relations, Relations.realize_total, Theory, Theory.model_insert_iff, and_true, cons_val_one, cons_val_zero, infer_instance, isValue, linearOrderTheory, model_insert_iff, model_partialOrder, realize_total, relMap_leSymb
-/
instance model_linearOrder : M ⊨ L.linearOrderTheory := by
  simp only [linearOrderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, model_partialOrder,
    and_true]
  infer_instance

/--
Instance `model_dlo` / 实例 `model_dlo`

English:
instance model_dlo
  signature: [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M]
  body: by
  simp [dlo, model_linearOrder, Theory.model_insert_iff]

中文:
实例 model_dlo
  签名: [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M]
  定义体: by
  simp [dlo, model_linearOrder, Theory.model_insert_iff]

Depends on / 依赖: Theory, Theory.model_insert_iff, model_insert_iff, model_linearOrder
-/
instance model_dlo [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] :
    M ⊨ L.dlo := by
  simp [dlo, model_linearOrder, Theory.model_insert_iff]

end LinearOrder

end order_to_structure

section structure_to_order

variable (L) [IsOrdered L] (M) [L.Structure M]

/-- Any structure in an ordered language can be ordered correspondingly. -/
@[instance_reducible]
/--
Definition of `leOfStructure` / `leOfStructure` 的定义

English:
definition leOfStructure
  signature: : LE M where
  body: Structure.RelMap (leSymb : L.Relations 2) ![a, b]

中文:
定义 leOfStructure
  签名: : LE M where
  定义体: Structure.RelMap (leSymb : L.Relations 2) ![a, b]

Depends on / 依赖: L.Relations, RelMap, Relations, Structure, Structure.RelMap, leSymb
-/
def leOfStructure : LE M where
  le a b := Structure.RelMap (leSymb : L.Relations 2) ![a, b]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @OrderedStructure L M _ (L.leOfStructure M) _
  body: by
  let := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl

中文:
实例 :
  签名: @OrderedStructure L M _ (L.leOfStructure M) _
  定义体: by
  let := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl

Depends on / 依赖: Fin.cons_zero, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, L.leOfStructure, cons_zero, forall_fin_succ_pi, forall_fin_zero_pi, intros, leOfStructure
-/
instance : @OrderedStructure L M _ (L.leOfStructure M) _ := by
  let := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl

/-- The order structure on an ordered language is decidable. -/
-- This should not be a global instance,
-- because it will match with any `LE` typeclass search
@[instance_reducible, local instance]
/--
Definition of `decidableLEOfStructure` / `decidableLEOfStructure` 的定义

English:
definition decidableLEOfStructure
  body: L.leOfStructure M
    DecidableLE M := h

中文:
定义 decidableLEOfStructure
  定义体: L.leOfStructure M
    DecidableLE M := h

Depends on / 依赖: L.leOfStructure, leOfStructure
-/
def decidableLEOfStructure
    [h : DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b])] :
    letI := L.leOfStructure M
    DecidableLE M := h

/-- Any model of a theory of preorders is a preorder. -/
@[instance_reducible]
/--
Definition of `preorderOfModels` / `preorderOfModels` 的定义

English:
definition preorderOfModels
  signature: [h : M ⊨ L.preorderTheory]
  body: L.leOfStructure M
  le_refl := (Relations.realize_reflexive.mp <|
.mp h _ by simp [preorderTheory]).refl Theory.model_iff _
  le_trans := (Relations.realize_transitive.mp <|
.mp h _ by simp [preorderTheory]).trans Theory.model_iff _

中文:
定义 preorderOfModels
  签名: [h : M ⊨ L.preorderTheory]
  定义体: L.leOfStructure M
  le_refl := (Relations.realize_reflexive.mp <|
.mp h _ by simp [preorderTheory]).refl Theory.model_iff _
  le_trans := (Relations.realize_transitive.mp <|
.mp h _ by simp [preorderTheory]).trans Theory.model_iff _

Depends on / 依赖: L.leOfStructure, leOfStructure
-/
def preorderOfModels [h : M ⊨ L.preorderTheory] : Preorder M where
  __ := L.leOfStructure M
  le_refl := (Relations.realize_reflexive.mp <|
.mp h _ by simp [preorderTheory]).refl Theory.model_iff _
  le_trans := (Relations.realize_transitive.mp <|
.mp h _ by simp [preorderTheory]).trans Theory.model_iff _

/-- Any model of a theory of partial orders is a partial order. -/
@[instance_reducible]
/--
Definition of `partialOrderOfModels` / `partialOrderOfModels` 的定义

English:
definition partialOrderOfModels
  signature: [h : M ⊨ L.partialOrderTheory]
  body: L.preorderOfModels M
  le_antisymm := (Relations.realize_antisymmetric.mp <|
.mp h _ by simp [partialOrderTheory]).antisymm Theory.model_iff _

中文:
定义 partialOrderOfModels
  签名: [h : M ⊨ L.partialOrderTheory]
  定义体: L.preorderOfModels M
  le_antisymm := (Relations.realize_antisymmetric.mp <|
.mp h _ by simp [partialOrderTheory]).antisymm Theory.model_iff _

Depends on / 依赖: L.preorderOfModels, preorderOfModels
-/
def partialOrderOfModels [h : M ⊨ L.partialOrderTheory] : PartialOrder M where
  __ := L.preorderOfModels M
  le_antisymm := (Relations.realize_antisymmetric.mp <|
.mp h _ by simp [partialOrderTheory]).antisymm Theory.model_iff _

/-- Any model of a theory of linear orders is a linear order. -/
@[instance_reducible]
/--
Definition of `linearOrderOfModels` / `linearOrderOfModels` 的定义

English:
definition linearOrderOfModels
  signature: [h : M ⊨ L.linearOrderTheory]
  body: L.partialOrderOfModels M
  le_total := (Relations.realize_total.mp <|
.mp h _ by simp [linearOrderTheory]).total Theory.model_iff _
  toDecidableLE := inferInstance

中文:
定义 linearOrderOfModels
  签名: [h : M ⊨ L.linearOrderTheory]
  定义体: L.partialOrderOfModels M
  le_total := (Relations.realize_total.mp <|
.mp h _ by simp [linearOrderTheory]).total Theory.model_iff _
  toDecidableLE := inferInstance

Depends on / 依赖: L.partialOrderOfModels, partialOrderOfModels
-/
def linearOrderOfModels [h : M ⊨ L.linearOrderTheory]
    [DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b])] :
    LinearOrder M where
  __ := L.partialOrderOfModels M
  le_total := (Relations.realize_total.mp <|
.mp h _ by simp [linearOrderTheory]).total Theory.model_iff _
  toDecidableLE := inferInstance

end structure_to_order

namespace order

variable [Language.order.Structure M] [LE M] [Language.order.OrderedStructure M]
  {N : Type*} [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N]
  {F : Type*}

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FunLike
  signature: F M N] [OrderHomClass F M N] : Language.order.HomClass F M N
  body: ⟨fun _ => isEmptyElim, by
    simp only [forall_relations, relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply]
    exact fun φ x => map_rel φ⟩

中文:
实例 [FunLike
  签名: F M N] [OrderHomClass F M N] : Language.order.HomClass F M N
  定义体: ⟨fun _ => isEmptyElim, by
    simp only [forall_relations, relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply]
    exact fun φ x => map_rel φ⟩

Depends on / 依赖: Fin.isValue, Function, Function.comp_apply, comp_apply, forall_relations, isEmptyElim, isValue, map_rel, relMap_leSymb, relation_eq_leSymb
-/
instance [FunLike F M N] [OrderHomClass F M N] : Language.order.HomClass F M N :=
  ⟨fun _ => isEmptyElim, by
    simp only [forall_relations, relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply]
    exact fun φ x => map_rel φ⟩

-- If `OrderEmbeddingClass` or `RelEmbeddingClass` is defined, this should be generalized.
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Language.order.StrongHomClass (M ↪o N) M N
  body: ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
    Function.comp_apply, RelEmbedding.map_rel_iff, implies_true]⟩

中文:
实例 :
  签名: Language.order.StrongHomClass (M ↪o N) M N
  定义体: ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
    Function.comp_apply, RelEmbedding.map_rel_iff, implies_true]⟩

Depends on / 依赖: Fin.isValue, Function, Function.comp_apply, RelEmbedding, RelEmbedding.map_rel_iff, comp_apply, forall_relations, implies_true, isEmptyElim, isValue, map_rel_iff, order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, relation_eq_leSymb
-/
instance : Language.order.StrongHomClass (M ↪o N) M N :=
  ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
    Function.comp_apply, RelEmbedding.map_rel_iff, implies_true]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EquivLike
  signature: F M N] [OrderIsoClass F M N] : Language.order.StrongHomClass F M N
  body: ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply, map_le_map_iff, implies_true]⟩

中文:
实例 [EquivLike
  签名: F M N] [OrderIsoClass F M N] : Language.order.StrongHomClass F M N
  定义体: ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply, map_le_map_iff, implies_true]⟩

Depends on / 依赖: Fin.isValue, Function, Function.comp_apply, comp_apply, forall_relations, implies_true, isEmptyElim, isValue, map_le_map_iff, order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, relation_eq_leSymb
-/
instance [EquivLike F M N] [OrderIsoClass F M N] : Language.order.StrongHomClass F M N :=
  ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply, map_le_map_iff, implies_true]⟩

end order

namespace HomClass

variable [L.IsOrdered] [L.Structure M] {N : Type*} [L.Structure N]
  {F : Type*} [FunLike F M N] [L.HomClass F M N]

/--
lemma `monotone` / 引理 `monotone`

English:
lemma monotone
  given: [Preorder M] [L.OrderedStructure M] [Preorder N] [L.OrderedStructure N] (f : F)
  proof: fun a b => by
  have h := HomClass.map_rel f leSymb ![a, b]
  simp only [relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at h
  exact h

中文:
引理 monotone
  条件: [Preorder M] [L.OrderedStructure M] [Preorder N] [L.OrderedStructure N] (f : F)
  证明: fun a b => by
  have h := HomClass.map_rel f leSymb ![a, b]
  simp only [relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at h
  exact h

Depends on / 依赖: Fin.isValue, Function, Function.comp_apply, HomClass, HomClass.map_rel, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, comp_apply, cons_val_one, cons_val_zero, isValue, leSymb, map_rel, relMap_leSymb
-/
lemma monotone [Preorder M] [L.OrderedStructure M] [Preorder N] [L.OrderedStructure N] (f : F) :
    Monotone f := fun a b => by
  have h := HomClass.map_rel f leSymb ![a, b]
  simp only [relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at h
  exact h

/--
lemma `strictMono` / 引理 `strictMono`

English:
lemma strictMono
  statement: [EmbeddingLike F M N] [PartialOrder M] [L.OrderedStructure M]
  proof: (HomClass.monotone f).strictMono_of_injective (EmbeddingLike.injective f)

中文:
引理 strictMono
  结论: [EmbeddingLike F M N] [PartialOrder M] [L.OrderedStructure M]
  证明: (HomClass.monotone f).strictMono_of_injective (EmbeddingLike.injective f)

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, HomClass, HomClass.monotone, injective, monotone, strictMono_of_injective
-/
lemma strictMono [EmbeddingLike F M N] [PartialOrder M] [L.OrderedStructure M]
    [PartialOrder N] [L.OrderedStructure N] (f : F) :
    StrictMono f :=
  (HomClass.monotone f).strictMono_of_injective (EmbeddingLike.injective f)

end HomClass

/--
lemma `StrongHomClass.toOrderIsoClass` / 引理 `StrongHomClass.toOrderIsoClass`

English:
lemma StrongHomClass.toOrderIsoClass
  proof: by
    have h := StrongHomClass.map_rel f leSymb ![a, b]
    simp only [relMap_leSymb, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    exact h

中文:
引理 StrongHomClass.toOrderIsoClass
  证明: by
    have h := StrongHomClass.map_rel f leSymb ![a, b]
    simp only [relMap_leSymb, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    exact h

Depends on / 依赖: Fin.isValue, Function, Function.comp_apply, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, StrongHomClass, StrongHomClass.map_rel, comp_apply, cons_val_one, cons_val_zero, isValue, leSymb, map_rel, relMap_leSymb
-/
lemma StrongHomClass.toOrderIsoClass
    (L : Language) [L.IsOrdered] (M : Type*) [L.Structure M] [LE M] [L.OrderedStructure M]
    (N : Type*) [L.Structure N] [LE N] [L.OrderedStructure N]
    (F : Type*) [EquivLike F M N] [L.StrongHomClass F M N] :
    OrderIsoClass F M N where
  map_le_map_iff f a b := by
    have h := StrongHomClass.map_rel f leSymb ![a, b]
    simp only [relMap_leSymb, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    exact h

section Fraisse

variable (M)

/--
lemma `dlo_isExtensionPair` / 引理 `dlo_isExtensionPair`

English:
lemma dlo_isExtensionPair
  proof: by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  have := Language.order.denselyOrdered_of_dlo N
  have := Language.order.noBotOrder_of_dlo N
  have := Lang

中文:
引理 dlo_isExtensionPair
  证明: by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  have := Language.order.denselyOrdered_of_dlo N
  have := Language.order.noBotOrder_of_dlo N
  have := Lang

Depends on / 依赖: Finite, Language, Language.order.denselyOrdered_of_dlo, Language.order.linearOrderOfModels, Language.order.noBotOrder_of_dlo, Language.order.noTopOrder_of_dlo, NoBotOrder, NoBotOrder.to_noMinOrder, NoTopOrder, NoTopOrder.to_noMaxOrder, Order.exists_orderEmbed, S.fg_iff_structure_fg, S_fg, Set.Finite, classical, denselyOrdered_of_dlo, exists_orderEmbed, fg_iff_structure_fg, finite, isExtensionPair_iff_exists_embedding_closure_singleton_sup
-/
lemma dlo_isExtensionPair
    (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.linearOrderTheory]
    (N : Type w') [Language.order.Structure N] [N ⊨ Language.order.dlo] [Nonempty N] :
    Language.order.IsExtensionPair M N := by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  have := Language.order.denselyOrdered_of_dlo N
  have := Language.order.noBotOrder_of_dlo N
  have := Language.order.noTopOrder_of_dlo N
  have := NoBotOrder.to_noMinOrder N
  have := NoTopOrder.to_noMaxOrder N
  have hS : Set.Finite (S : Set M) := (S.fg_iff_structure_fg.1 S_fg).finite
  obtain ⟨g, hg⟩ := Order.exists_orderEmbedding_insert hS.toFinset
    ((OrderIso.setCongr hS.toFinset (S : Set M) hS.coe_toFinset).toOrderEmbedding.trans
      (OrderEmbedding.ofStrictMono f (HomClass.strictMono f))) m
  let g' :
    ((Substructure.closure Language.order).toFun {m} ⊔ S : Language.order.Substructure M) ↪o N :=
    ((OrderIso.setCongr _ _ (by
      convert!
        LowerAdjoint.closure_eq_self_of_mem_closed _
          (Substructure.mem_closed_of_isRelational Language.order
            ((insert m hS.toFinset : Finset M) : Set M))
      simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Substructure.closure_insert,
        Substructure.closure_eq])).toOrderEmbedding.trans g)
  use StrongHomClass.toEmbedding g'
  ext ⟨x, xS⟩
  refine congr_fun hg.symm ⟨x, (?_ : x in hS.toFinset)⟩
  simp only [Set.Finite.mem_toFinset, SetLike.mem_coe, xS]

set_option backward.isDefEq.respectTransparency false in
instance (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo] [Nonempty M] :
    Infinite M := by
  let := orderStructure Rat
  obtain ⟨f, _⟩ := embedding_from_cg cg_of_countable default (dlo_isExtensionPair Rat M)
  exact Infinite.of_injective f f.injective

/--
lemma `dlo_age` / 引理 `dlo_age`

English:
lemma dlo_age
  given: [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [Nonempty M]
  proof: by
  classical
  rw [age]
  ext N
  refine ⟨fun ⟨hF, h⟩ => ⟨hF.finite, Theory.IsUniversal.models_of_embedding h.some⟩,
    fun ⟨hF, h⟩ => ⟨FG.of_finite, ?_⟩⟩
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  exact ⟨StrongHomClass.toEmbedding (nonempty_orde

中文:
引理 dlo_age
  条件: [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [Nonempty M]
  证明: by
  classical
  rw [age]
  ext N
  refine ⟨fun ⟨hF, h⟩ => ⟨hF.finite, Theory.IsUniversal.models_of_embedding h.some⟩,
    fun ⟨hF, h⟩ => ⟨FG.of_finite, ?_⟩⟩
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  exact ⟨StrongHomClass.toEmbedding (nonempty_orde

Depends on / 依赖: FG.of_finite, IsUniversal, Language, Language.order.linearOrderOfModels, StrongHomClass, StrongHomClass.toEmbedding, Theory, Theory.IsUniversal.models_of_embedding, classical, finite, h.some, hF.finite, linearOrderOfModels, models_of_embedding, nonempty_orderEmbedding_of_finite_infinite, of_finite, toEmbedding
-/
lemma dlo_age [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [Nonempty M] :
    Language.order.age M = {M : CategoryTheory.Bundled.{w'} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  classical
  rw [age]
  ext N
  refine ⟨fun ⟨hF, h⟩ => ⟨hF.finite, Theory.IsUniversal.models_of_embedding h.some⟩,
    fun ⟨hF, h⟩ => ⟨FG.of_finite, ?_⟩⟩
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  exact ⟨StrongHomClass.toEmbedding (nonempty_orderEmbedding_of_finite_infinite N M).some⟩

/--
theorem `isFraisseLimit_of_countable_nonempty_dlo` / 定理 `isFraisseLimit_of_countable_nonempty_dlo`

English:
theorem isFraisseLimit_of_countable_nonempty_dlo
  statement: (M : Type w)
  proof: ⟨(isUltrahomogeneous_iff_IsExtensionPair cg_of_countable).2 (dlo_isExtensionPair M M), dlo_age M⟩

中文:
定理 isFraisseLimit_of_countable_nonempty_dlo
  结论: (M : Type w)
  证明: ⟨(isUltrahomogeneous_iff_IsExtensionPair cg_of_countable).2 (dlo_isExtensionPair M M), dlo_age M⟩

Depends on / 依赖: cg_of_countable, dlo_age, dlo_isExtensionPair, isUltrahomogeneous_iff_IsExtensionPair
-/
theorem isFraisseLimit_of_countable_nonempty_dlo (M : Type w)
    [Language.order.Structure M] [Countable M] [Nonempty M] [M ⊨ Language.order.dlo] :
    IsFraisseLimit {M : CategoryTheory.Bundled.{w} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} M :=
  ⟨(isUltrahomogeneous_iff_IsExtensionPair cg_of_countable).2 (dlo_isExtensionPair M M), dlo_age M⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isFraisse_finite_linear_order` / 定理 `isFraisse_finite_linear_order`

English:
theorem isFraisse_finite_linear_order
  proof: by
  let : Language.order.Structure Rat := orderStructure _
  exact (isFraisseLimit_of_countable_nonempty_dlo Rat).isFraisse

中文:
定理 isFraisse_finite_linear_order
  证明: by
  let : Language.order.Structure Rat := orderStructure _
  exact (isFraisseLimit_of_countable_nonempty_dlo Rat).isFraisse

Depends on / 依赖: Language, Language.order.Structure, Structure, isFraisse, isFraisseLimit_of_countable_nonempty_dlo, orderStructure
-/
theorem isFraisse_finite_linear_order :
    IsFraisse {M : CategoryTheory.Bundled.{0} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  let : Language.order.Structure Rat := orderStructure _
  exact (isFraisseLimit_of_countable_nonempty_dlo Rat).isFraisse

open Cardinal

/--
theorem `aleph0_categorical_dlo` / 定理 `aleph0_categorical_dlo`

English:
theorem aleph0_categorical_dlo
  statement: (ℵ₀).Categorical Language.order.dlo
  proof: fun M₁ M₂ h₁ h₂ => by
  obtain ⟨_⟩ := denumerable_iff.2 h₁
  obtain ⟨_⟩ := denumerable_iff.2 h₂
  exact (isFraisseLimit_of_countable_nonempty_dlo M₁).nonempty_equiv
    (isFraisseLimit_of_countable_nonempty_dlo M₂)

中文:
定理 aleph0_categorical_dlo
  结论: (ℵ₀).Categorical Language.order.dlo
  证明: fun M₁ M₂ h₁ h₂ => by
  obtain ⟨_⟩ := denumerable_iff.2 h₁
  obtain ⟨_⟩ := denumerable_iff.2 h₂
  exact (isFraisseLimit_of_countable_nonempty_dlo M₁).nonempty_equiv
    (isFraisseLimit_of_countable_nonempty_dlo M₂)

Depends on / 依赖: denumerable_iff, isFraisseLimit_of_countable_nonempty_dlo, nonempty_equiv
-/
theorem aleph0_categorical_dlo : (ℵ₀).Categorical Language.order.dlo := fun M₁ M₂ h₁ h₂ => by
  obtain ⟨_⟩ := denumerable_iff.2 h₁
  obtain ⟨_⟩ := denumerable_iff.2 h₂
  exact (isFraisseLimit_of_countable_nonempty_dlo M₁).nonempty_equiv
    (isFraisseLimit_of_countable_nonempty_dlo M₂)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dlo_isComplete` / 定理 `dlo_isComplete`

English:
theorem dlo_isComplete
  statement: Language.order.dlo.IsComplete
  proof: aleph0_categorical_dlo.{0}.isComplete ℵ₀ _ le_rfl (by simp [one_le_aleph0])
    ⟨by
      letI : Language.order.Structure Rat := orderStructure Rat
      exact Theory.ModelType.of _ Rat⟩
    fun _ => inferInstance

中文:
定理 dlo_isComplete
  结论: Language.order.dlo.IsComplete
  证明: aleph0_categorical_dlo.{0}.isComplete ℵ₀ _ le_rfl (by simp [one_le_aleph0])
    ⟨by
      letI : Language.order.Structure Rat := orderStructure Rat
      exact Theory.ModelType.of _ Rat⟩
    fun _ => inferInstance

Depends on / 依赖: Language, Language.order.Structure, ModelType, Structure, Theory, Theory.ModelType.of, aleph0_categorical_dlo, isComplete, le_rfl, one_le_aleph0, orderStructure
-/
theorem dlo_isComplete : Language.order.dlo.IsComplete :=
  aleph0_categorical_dlo.{0}.isComplete ℵ₀ _ le_rfl (by simp [one_le_aleph0])
    ⟨by
      letI : Language.order.Structure Rat := orderStructure Rat
      exact Theory.ModelType.of _ Rat⟩
    fun _ => inferInstance

end Fraisse

end Language

end FirstOrder

namespace Order

open FirstOrder FirstOrder.Language

set_option backward.isDefEq.respectTransparency false in
/-- A model-theoretic adaptation of the proof of `Order.iso_of_countable_dense`: two countable,
  dense, nonempty linear orders without endpoints are order isomorphic. -/
example (α β : Type w') [LinearOrder α] [LinearOrder β]
    [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := by
  let := orderStructure α
  let := orderStructure β
  let := StrongHomClass.toOrderIsoClass Language.order α β (α ≃[Language.order] β)
  exact ⟨(IsFraisseLimit.nonempty_equiv (isFraisseLimit_of_countable_nonempty_dlo α)
    (isFraisseLimit_of_countable_nonempty_dlo β)).some⟩

end Order
