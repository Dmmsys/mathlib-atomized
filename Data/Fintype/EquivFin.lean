/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.NodupEquivFin

/-!
# Equivalences between `Fintype`, `Fin` and `Finite`

This file defines the bijection between a `Fintype α` and `Fin (Fintype.card α)`, and uses this to
relate `Fintype` with `Finite`. From that we can derive properties of `Finite` and `Infinite`,
and show some instances of `Infinite`.

## Main declarations

* `Fintype.truncEquivFin`: A fintype `α` is computably equivalent to `Fin (card α)`. The
  `Trunc`-free, noncomputable version is `Fintype.equivFin`.
* `Fintype.truncEquivOfCardEq` `Fintype.equivOfCardEq`: Two fintypes of same cardinality are
  equivalent. See above.
* `Fin.equiv_iff_eq`: `Fin m ≃ Fin n` iff `m = n`.
* `Infinite.natEmbedding`: An embedding of `ℕ` into an infinite type.

Types which have an injection from/a surjection to an `Infinite` type are themselves `Infinite`.
See `Infinite.of_injective` and `Infinite.of_surjective`.

## Instances

We provide `Infinite` instances for
* specific types: `ℕ`, `ℤ`, `String`
* type constructors: `Multiset α`, `List α`

-/

@[expose] public section

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

/--
Definition of `truncEquivFin` / `truncEquivFin` 的定义

English:
definition truncEquivFin
  signature: (α) [DecidableEq α] [Fintype α]
  body: by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (forall x : α, x in s) -> s.Nodup -> Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : forall x : α, x in l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).sy

中文:
定义 truncEquivFin
  签名: (α) [DecidableEq α] [Fintype α]
  定义体: by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (forall x : α, x in s) -> s.Nodup -> Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : forall x : α, x in l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).sy

Depends on / 依赖: Finset, Finset.card, Multiset, Multiset.card, Quot.recOnSubsingleton, Trunc.mk, getEquivOfForallMemList, l.Nodup, mem_univ_val, motive, nd.getEquivOfForallMemList, recOnSubsingleton, s.Nodup, univ.val
-/
def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α)) := by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (forall x : α, x in s) -> s.Nodup -> Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : forall x : α, x in l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2

/--
Definition of `equivFin` / `equivFin` 的定义

English:
definition equivFin
  signature: (α) [Fintype α]
  body: letI := Classical.decEq α
  (truncEquivFin α).out

中文:
定义 equivFin
  签名: (α) [Fintype α]
  定义体: letI := Classical.decEq α
  (truncEquivFin α).out

Depends on / 依赖: Classical, Classical.decEq, truncEquivFin
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (truncEquivFin α).out

/--
Definition of `truncFinBijection` / `truncFinBijection` 的定义

English:
definition truncFinBijection
  signature: (α) [Fintype α]
  body: by
  unfold card Finset.card
  refine
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (forall x : α, x in s) -> s.Nodup -> Trunc {f : Fin (Multiset.card s) -> α // Bijective f})
      univ.val
      (fun l (h : forall x : α, x in l) (nd : l.Nodup) => Trunc.mk (nd.getBijecti

中文:
定义 truncFinBijection
  签名: (α) [Fintype α]
  定义体: by
  unfold card Finset.card
  refine
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (forall x : α, x in s) -> s.Nodup -> Trunc {f : Fin (Multiset.card s) -> α // Bijective f})
      univ.val
      (fun l (h : forall x : α, x in l) (nd : l.Nodup) => Trunc.mk (nd.getBijecti

Depends on / 依赖: Bijective, Finset, Finset.card, Multiset, Multiset.card, Quot.recOnSubsingleton, Trunc.mk, getBijectionOfForallMemList, l.Nodup, mem_univ_val, motive, nd.getBijectionOfForallMemList, recOnSubsingleton, s.Nodup, univ.val
-/
def truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) -> α // Bijective f } := by
  unfold card Finset.card
  refine
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (forall x : α, x in s) -> s.Nodup -> Trunc {f : Fin (Multiset.card s) -> α // Bijective f})
      univ.val
      (fun l (h : forall x : α, x in l) (nd : l.Nodup) => Trunc.mk (nd.getBijectionOfForallMemList _ h))
      mem_univ_val univ.2

end Fintype

namespace Fintype

section

variable [Fintype α] [Fintype β]

/--
Definition of `truncEquivFinOfCardEq` / `truncEquivFinOfCardEq` 的定义

English:
definition truncEquivFinOfCardEq
  signature: [DecidableEq α] {n : Nat} (h : Fintype.card α = n)
  body: (truncEquivFin α).map fun e => e.trans (finCongr h)

中文:
定义 truncEquivFinOfCardEq
  签名: [DecidableEq α] {n : 自然数} (h : Fintype.card α = n)
  定义体: (truncEquivFin α).map fun e => e.trans (finCongr h)

Depends on / 依赖: e.trans, finCongr, truncEquivFin
-/
def truncEquivFinOfCardEq [DecidableEq α] {n : Nat} (h : Fintype.card α = n) : Trunc (α ≃ Fin n) :=
  (truncEquivFin α).map fun e => e.trans (finCongr h)

/--
Definition of `equivFinOfCardEq` / `equivFinOfCardEq` 的定义

English:
definition equivFinOfCardEq
  signature: {n : Nat} (h : Fintype.card α = n)
  body: letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out

中文:
定义 equivFinOfCardEq
  签名: {n : 自然数} (h : Fintype.card α = n)
  定义体: letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out

Depends on / 依赖: Classical, Classical.decEq, truncEquivFinOfCardEq
-/
noncomputable def equivFinOfCardEq {n : Nat} (h : Fintype.card α = n) : α ≃ Fin n :=
  letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out

/--
Definition of `truncEquivOfCardEq` / `truncEquivOfCardEq` 的定义

English:
definition truncEquivOfCardEq
  signature: [DecidableEq α] [DecidableEq β] (h : card α = card β)
  body: (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

中文:
定义 truncEquivOfCardEq
  签名: [DecidableEq α] [DecidableEq β] (h : card α = card β)
  定义体: (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

Depends on / 依赖: e.trans, truncEquivFin, truncEquivFinOfCardEq
-/
def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

/--
Definition of `equivOfCardEq` / `equivOfCardEq` 的定义

English:
definition equivOfCardEq
  signature: (h : card α = card β)
  body: by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (truncEquivOfCardEq h).out

中文:
定义 equivOfCardEq
  签名: (h : card α = card β)
  定义体: by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (truncEquivOfCardEq h).out

Depends on / 依赖: Classical, Classical.decEq, truncEquivOfCardEq
-/
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (truncEquivOfCardEq h).out

end

/--
theorem `card_eq` / 定理 `card_eq`

English:
theorem card_eq
  given: {α β} [_F : Fintype α] [_G : Fintype β]
  statement: card α = card β ↔ Nonempty (α ≃ β)
  proof: ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩

中文:
定理 card_eq
  条件: {α β} [_F : Fintype α] [_G : Fintype β]
  结论: card α = card β ↔ Nonempty (α ≃ β)
  证明: ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩

Depends on / 依赖: Classical, Classical.propDecidable, card_congr, nonempty, propDecidable, truncEquivOfCardEq
-/
theorem card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩

end Fintype


/--
theorem `Fintype.finite` / 定理 `Fintype.finite`

English:
theorem Fintype.finite
  given: {α : Type*} (_inst : Fintype α)
  statement: Finite α
  proof: ⟨Fintype.equivFin α⟩

中文:
定理 Fintype.finite
  条件: {α : 类型} (_inst : Fintype α)
  结论: Finite α
  证明: ⟨Fintype.equivFin α⟩
-/
protected theorem Fintype.finite {α : Type*} (_inst : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩

set_option linter.unusedFintypeInType false in
/-- For efficiency reasons, we want `Finite` instances to have higher
priority than ones coming from `Fintype` instances. -/
instance (priority := 900) Finite.of_fintype (α : Type*) [Fintype α] : Finite α :=
  Fintype.finite ‹_›

/--
theorem `finite_iff_nonempty_fintype` / 定理 `finite_iff_nonempty_fintype`

English:
theorem finite_iff_nonempty_fintype
  given: (α : Type*)
  statement: Finite α ↔ Nonempty (Fintype α)
  proof: ⟨fun _ => nonempty_fintype α, fun ⟨_⟩ => inferInstance⟩

中文:
定理 finite_iff_nonempty_fintype
  条件: (α : 类型)
  结论: Finite α ↔ Nonempty (Fintype α)
  证明: ⟨fun _ => nonempty_fintype α, fun ⟨_⟩ => inferInstance⟩

Depends on / 依赖: nonempty_fintype
-/
theorem finite_iff_nonempty_fintype (α : Type*) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun _ => nonempty_fintype α, fun ⟨_⟩ => inferInstance⟩

/-- Noncomputably get a `Fintype` instance from a `Finite` instance. This is not an
instance because we want `Fintype` instances to be useful for computations. -/
@[instance_reducible]
/--
Definition of `Fintype.ofFinite` / `Fintype.ofFinite` 的定义

English:
definition Fintype.ofFinite
  signature: (α : Type*) [Finite α]
  body: (nonempty_fintype α).some

中文:
定义 Fintype.ofFinite
  签名: (α : 类型) [Finite α]
  定义体: (nonempty_fintype α).some

Depends on / 依赖: nonempty_fintype
-/
noncomputable def Fintype.ofFinite (α : Type*) [Finite α] : Fintype α :=
  (nonempty_fintype α).some

/--
theorem `Finite.of_injective` / 定理 `Finite.of_injective`

English:
theorem Finite.of_injective
  given: {α β : Sort*} [Finite β] (f : α -> β) (H : Injective f)
  statement: Finite α
  proof: by
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e⟩⟩
  classical exact .of_equiv (Set.range (e ∘ f)) (Equiv.ofInjective _ (e.injective.comp H)).symm

中文:
定理 Finite.of_injective
  条件: {α β : Sort*} [Finite β] (f : α -> β) (H : Injective f)
  结论: Finite α
  证明: by
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e⟩⟩
  classical exact .of_equiv (Set.range (e ∘ f)) (Equiv.ofInjective _ (e.injective.comp H)).symm

Depends on / 依赖: Equiv.ofInjective, Finite, Finite.exists_equiv_fin, Set.range, classical, e.injective.comp, exists_equiv_fin, injective, ofInjective, of_equiv
-/
theorem Finite.of_injective {α β : Sort*} [Finite β] (f : α -> β) (H : Injective f) : Finite α := by
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e⟩⟩
  classical exact .of_equiv (Set.range (e ∘ f)) (Equiv.ofInjective _ (e.injective.comp H)).symm

-- see Note [lower instance priority]
instance (priority := 100) Finite.of_subsingleton {α : Sort*} [Subsingleton α] : Finite α :=
Finite.of_injective (Function.const α ()) Function.injective_of_subsingleton _

-- Higher priority for `Prop`s
/--
Instance `instFiniteProp` / 实例 `instFiniteProp`

English:
instance instFiniteProp
  signature: (p : Prop)
  body: Finite.of_subsingleton

中文:
实例 instFiniteProp
  签名: (p : 命题)
  定义体: Finite.of_subsingleton

Depends on / 依赖: Finite, Finite.of_subsingleton, of_subsingleton
-/
instance instFiniteProp (p : Prop) : Finite p :=
  Finite.of_subsingleton

/--
Instance `Subtype.finite` / 实例 `Subtype.finite`

English:
instance Subtype.finite
  signature: {α : Sort*} [Finite α] {p : α -> Prop}
  body: Finite.of_injective Subtype.val Subtype.coe_injective

中文:
实例 Subtype.finite
  签名: {α : Sort*} [Finite α] {p : α -> 命题}
  定义体: Finite.of_injective Subtype.val Subtype.coe_injective

Depends on / 依赖: Finite, Finite.of_injective, Subtype, Subtype.coe_injective, Subtype.val, coe_injective, of_injective
-/
instance Subtype.finite {α : Sort*} [Finite α] {p : α -> Prop} : Finite { x // p x } :=
  Finite.of_injective Subtype.val Subtype.coe_injective

/--
theorem `Finite.of_surjective` / 定理 `Finite.of_surjective`

English:
theorem Finite.of_surjective
  given: {α β : Sort*} [Finite α] (f : α -> β) (H : Surjective f)
  statement: Finite β
  proof: Finite.of_injective _ injective_surjInv H

中文:
定理 Finite.of_surjective
  条件: {α β : Sort*} [Finite α] (f : α -> β) (H : Surjective f)
  结论: Finite β
  证明: Finite.of_injective _ injective_surjInv H

Depends on / 依赖: Finite, Finite.of_injective, injective_surjInv, of_injective
-/
theorem Finite.of_surjective {α β : Sort*} [Finite α] (f : α -> β) (H : Surjective f) : Finite β :=
Finite.of_injective _ injective_surjInv H

/--
Instance `Quot.finite` / 实例 `Quot.finite`

English:
instance Quot.finite
  signature: {α : Sort*} [Finite α] (r : α -> α -> Prop)
  body: Finite.of_surjective _ Quot.mk_surjective

中文:
实例 Quot.finite
  签名: {α : Sort*} [Finite α] (r : α -> α -> 命题)
  定义体: Finite.of_surjective _ Quot.mk_surjective

Depends on / 依赖: Finite, Finite.of_surjective, Quot.mk_surjective, mk_surjective, of_surjective
-/
instance Quot.finite {α : Sort*} [Finite α] (r : α -> α -> Prop) : Finite (Quot r) :=
  Finite.of_surjective _ Quot.mk_surjective

/--
Instance `Quotient.finite` / 实例 `Quotient.finite`

English:
instance Quotient.finite
  signature: {α : Sort*} [Finite α] (s : Setoid α)
  body: Quot.finite _

中文:
实例 Quotient.finite
  签名: {α : Sort*} [Finite α] (s : Setoid α)
  定义体: Quot.finite _

Depends on / 依赖: Quot.finite, finite
-/
instance Quotient.finite {α : Sort*} [Finite α] (s : Setoid α) : Finite (Quotient s) :=
  Quot.finite _

namespace Fintype

variable [Fintype α] [Fintype β]

/--
theorem `card_eq_one_iff` / 定理 `card_eq_one_iff`

English:
theorem card_eq_one_iff
  statement: card α = 1 ↔ exists x : α, forall y, y = x
  proof: by
  rw [← card_unit]; rw [card_eq]
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩

中文:
定理 card_eq_one_iff
  结论: card α = 1 ↔ 存在 x : α, 对任意 y, y = x
  证明: by
  rw [← card_unit]; rw [card_eq]
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, a.injective, a.symm, card_eq, card_unit, injective
-/
theorem card_eq_one_iff : card α = 1 ↔ exists x : α, forall y, y = x := by
  rw [← card_unit]; rw [card_eq]
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩

/--
theorem `card_eq_one_iff_nonempty_unique` / 定理 `card_eq_one_iff_nonempty_unique`

English:
theorem card_eq_one_iff_nonempty_unique
  statement: card α = 1 ↔ Nonempty (Unique α)
  proof: ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{ default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩

中文:
定理 card_eq_one_iff_nonempty_unique
  结论: card α = 1 ↔ Nonempty (Unique α)
  证明: ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{ default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩

Depends on / 依赖: Fintype, Fintype.card_eq_one_iff.mp, Fintype.card_unique, card_eq_one_iff, card_unique
-/
theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{ default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩

/--
theorem `card_le_one_iff` / 定理 `card_le_one_iff`

English:
theorem card_le_one_iff
  statement: card α <= 1 ↔ forall a b : α, a = b
  proof: let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0, ha =>
    ⟨fun _h a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succ _⟩
  | 1, ha =>
    ⟨fun _h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a]; rw [hx b], fun _ => ha ▸ le_rfl⟩


中文:
定理 card_le_one_iff
  结论: card α <= 1 ↔ 对任意 a b : α, a = b
  证明: let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0, ha =>
    ⟨fun _h a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succ _⟩
  | 1, ha =>
    ⟨fun _h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a]; rw [hx b], fun _ => ha ▸ le_rfl⟩


Depends on / 依赖: False.elim, Nat.le_succ, card_eq_one_iff, card_eq_zero_iff, card_le_of_injective, card_unit, ha.symm, le_rfl, le_succ
-/
theorem card_le_one_iff : card α <= 1 ↔ forall a b : α, a = b :=
  let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0, ha =>
    ⟨fun _h a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succ _⟩
  | 1, ha =>
    ⟨fun _h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a]; rw [hx b], fun _ => ha ▸ le_rfl⟩
  | n + 2, ha =>
⟨fun h => False.elim by rw [← ha] at h; cases h with | step h => cases h; , fun h =>
      card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩

/--
theorem `card_le_one_iff_subsingleton` / 定理 `card_le_one_iff_subsingleton`

English:
theorem card_le_one_iff_subsingleton
  statement: card α <= 1 ↔ Subsingleton α
  proof: card_le_one_iff.trans subsingleton_iff.symm

中文:
定理 card_le_one_iff_subsingleton
  结论: card α <= 1 ↔ Subsingleton α
  证明: card_le_one_iff.trans subsingleton_iff.symm

Depends on / 依赖: card_le_one_iff, card_le_one_iff.trans, holderConjugate_iff_eq_conjExponent, subsingleton_iff, subsingleton_iff.symm
-/
theorem card_le_one_iff_subsingleton : card α <= 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm

/--
theorem `one_lt_card_iff_nontrivial` / 定理 `one_lt_card_iff_nontrivial`

English:
theorem one_lt_card_iff_nontrivial
  statement: 1 < card α ↔ Nontrivial α
  proof: by
  contrapose!; exact card_le_one_iff_subsingleton

中文:
定理 one_lt_card_iff_nontrivial
  结论: 1 < card α ↔ Nontrivial α
  证明: by
  contrapose!; exact card_le_one_iff_subsingleton

Depends on / 依赖: card_le_one_iff_subsingleton, contrapose
-/
theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α := by
  contrapose!; exact card_le_one_iff_subsingleton

/--
theorem `exists_ne_of_one_lt_card` / 定理 `exists_ne_of_one_lt_card`

English:
theorem exists_ne_of_one_lt_card
  given: (h : 1 < card α) (a : α)
  statement: exists b : α, b != a
  proof: haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a

中文:
定理 exists_ne_of_one_lt_card
  条件: (h : 1 < card α) (a : α)
  结论: 存在 b : α, b != a
  证明: haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a

Depends on / 依赖: Nontrivial, exists_ne, one_lt_card_iff_nontrivial
-/
theorem exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : exists b : α, b != a :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a

/--
theorem `exists_pair_of_one_lt_card` / 定理 `exists_pair_of_one_lt_card`

English:
theorem exists_pair_of_one_lt_card
  given: (h : 1 < card α)
  statement: exists a b : α, a != b
  proof: haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α

中文:
定理 exists_pair_of_one_lt_card
  条件: (h : 1 < card α)
  结论: 存在 a b : α, a != b
  证明: haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α

Depends on / 依赖: Nontrivial, exists_pair_ne, one_lt_card_iff_nontrivial
-/
theorem exists_pair_of_one_lt_card (h : 1 < card α) : exists a b : α, a != b :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α

/--
theorem `card_eq_one_of_forall_eq` / 定理 `card_eq_one_of_forall_eq`

English:
theorem card_eq_one_of_forall_eq
  given: {i : α} (h : forall j, j = i)
  statement: card α = 1
  proof: Fintype.card_eq_one_iff.2 ⟨i, h⟩

中文:
定理 card_eq_one_of_forall_eq
  条件: {i : α} (h : 对任意 j, j = i)
  结论: card α = 1
  证明: Fintype.card_eq_one_iff.2 ⟨i, h⟩

Depends on / 依赖: Fintype, Fintype.card_eq_one_iff, card_eq_one_iff
-/
theorem card_eq_one_of_forall_eq {i : α} (h : forall j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩

/--
theorem `one_lt_card` / 定理 `one_lt_card`

English:
theorem one_lt_card
  given: [h : Nontrivial α]
  statement: 1 < Fintype.card α
  proof: Fintype.one_lt_card_iff_nontrivial.mpr h

中文:
定理 one_lt_card
  条件: [h : Nontrivial α]
  结论: 1 < Fintype.card α
  证明: Fintype.one_lt_card_iff_nontrivial.mpr h

Depends on / 依赖: Fintype, Fintype.one_lt_card_iff_nontrivial.mpr, one_lt_card_iff_nontrivial
-/
theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h

/--
theorem `one_lt_card_iff` / 定理 `one_lt_card_iff`

English:
theorem one_lt_card_iff
  statement: 1 < card α ↔ exists a b : α, a != b
  proof: one_lt_card_iff_nontrivial.trans nontrivial_iff

中文:
定理 one_lt_card_iff
  结论: 1 < card α ↔ 存在 a b : α, a != b
  证明: one_lt_card_iff_nontrivial.trans nontrivial_iff

Depends on / 依赖: nontrivial_iff, one_lt_card_iff_nontrivial, one_lt_card_iff_nontrivial.trans
-/
theorem one_lt_card_iff : 1 < card α ↔ exists a b : α, a != b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff

end Fintype

namespace Fintype

variable [Fintype α] [Fintype β]

/--
theorem `bijective_iff_injective_and_card` / 定理 `bijective_iff_injective_and_card`

English:
theorem bijective_iff_injective_and_card
  given: (f : α -> β)
  proof: ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
⟨h.1, h.1.surjective_of_finite equivOfCardEq h.2⟩⟩

中文:
定理 bijective_iff_injective_and_card
  条件: (f : α -> β)
  证明: ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
⟨h.1, h.1.surjective_of_finite equivOfCardEq h.2⟩⟩

Depends on / 依赖: card_of_bijective, equivOfCardEq, surjective_of_finite
-/
theorem bijective_iff_injective_and_card (f : α -> β) :
    Bijective f ↔ Injective f ∧ card α = card β :=
  ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
⟨h.1, h.1.surjective_of_finite equivOfCardEq h.2⟩⟩

/--
theorem `bijective_iff_surjective_and_card` / 定理 `bijective_iff_surjective_and_card`

English:
theorem bijective_iff_surjective_and_card
  given: (f : α -> β)
  proof: ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
⟨h.1.injective_of_finite equivOfCardEq h.2, h.1⟩⟩

中文:
定理 bijective_iff_surjective_and_card
  条件: (f : α -> β)
  证明: ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
⟨h.1.injective_of_finite equivOfCardEq h.2, h.1⟩⟩

Depends on / 依赖: card_of_bijective, equivOfCardEq, injective_of_finite
-/
theorem bijective_iff_surjective_and_card (f : α -> β) :
    Bijective f ↔ Surjective f ∧ card α = card β :=
  ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
⟨h.1.injective_of_finite equivOfCardEq h.2, h.1⟩⟩

/--
theorem `_root_.Function.LeftInverse.rightInverse_of_card_le` / 定理 `_root_.Function.LeftInverse.rightInverse_of_card_le`

English:
theorem _root_.Function.LeftInverse.rightInverse_of_card_le
  statement: {f : α -> β} {g : β -> α}
  proof: have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg

中文:
定理 _root_.Function.LeftInverse.rightInverse_of_card_le
  结论: {f : α -> β} {g : β -> α}
  证明: have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg

Depends on / 依赖: Surjective, bijective_iff_surjective_and_card, card_le_of_surjective, le_antisymm, rightInverse_of_injective_of_leftInverse, surjective_iff_hasRightInverse
-/
theorem _root_.Function.LeftInverse.rightInverse_of_card_le {f : α -> β} {g : β -> α}
    (hfg : LeftInverse f g) (hcard : card α <= card β) : RightInverse f g :=
  have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg

/--
theorem `_root_.Function.RightInverse.leftInverse_of_card_le` / 定理 `_root_.Function.RightInverse.leftInverse_of_card_le`

English:
theorem _root_.Function.RightInverse.leftInverse_of_card_le
  statement: {f : α -> β} {g : β -> α}
  proof: Function.LeftInverse.rightInverse_of_card_le hfg hcard

中文:
定理 _root_.Function.RightInverse.leftInverse_of_card_le
  结论: {f : α -> β} {g : β -> α}
  证明: Function.LeftInverse.rightInverse_of_card_le hfg hcard

Depends on / 依赖: Function, Function.LeftInverse.rightInverse_of_card_le, LeftInverse, rightInverse_of_card_le
-/
theorem _root_.Function.RightInverse.leftInverse_of_card_le {f : α -> β} {g : β -> α}
    (hfg : RightInverse f g) (hcard : card β <= card α) : LeftInverse f g :=
  Function.LeftInverse.rightInverse_of_card_le hfg hcard

end Fintype

namespace Equiv

variable [Fintype α] [Fintype β]

open Fintype

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
/--
Definition of `ofLeftInverseOfCardLE` / `ofLeftInverseOfCardLE` 的定义

English:
definition ofLeftInverseOfCardLE
  signature: (hβα : card β <= card α) (f : α -> β) (g : β -> α) (h : LeftInverse g f)
  body: f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_card_le hβα

中文:
定义 ofLeftInverseOfCardLE
  签名: (hβα : card β <= card α) (f : α -> β) (g : β -> α) (h : LeftInverse g f)
  定义体: f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_card_le hβα
-/
def ofLeftInverseOfCardLE (hβα : card β <= card α) (f : α -> β) (g : β -> α) (h : LeftInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_card_le hβα

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
/--
Definition of `ofRightInverseOfCardLE` / `ofRightInverseOfCardLE` 的定义

English:
definition ofRightInverseOfCardLE
  signature: (hαβ : card α <= card β) (f : α -> β) (g : β -> α) (h : RightInverse g f)
  body: f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h

中文:
定义 ofRightInverseOfCardLE
  签名: (hαβ : card α <= card β) (f : α -> β) (g : β -> α) (h : RightInverse g f)
  定义体: f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h
-/
def ofRightInverseOfCardLE (hαβ : card α <= card β) (f : α -> β) (g : β -> α) (h : RightInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h

end Equiv

/--
Definition of `Finset.equivFin` / `Finset.equivFin` 的定义

English:
definition Finset.equivFin
  signature: (s : Finset α)
  body: Fintype.equivFinOfCardEq (Fintype.card_coe _)

中文:
定义 Finset.equivFin
  签名: (s : Finset α)
  定义体: Fintype.equivFinOfCardEq (Fintype.card_coe _)

Depends on / 依赖: Fintype, Fintype.card_coe, Fintype.equivFinOfCardEq, card_coe, equivFinOfCardEq
-/
noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin #s :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

/--
Definition of `Finset.equivFinOfCardEq` / `Finset.equivFinOfCardEq` 的定义

English:
definition Finset.equivFinOfCardEq
  signature: {s : Finset α} {n : Nat} (h : #s = n)
  body: Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)

中文:
定义 Finset.equivFinOfCardEq
  签名: {s : Finset α} {n : 自然数} (h : #s = n)
  定义体: Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)

Depends on / 依赖: Fintype, Fintype.card_coe, Fintype.equivFinOfCardEq, card_coe, equivFinOfCardEq
-/
noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : Nat} (h : #s = n) : s ≃ Fin n :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)

/--
theorem `Finset.card_eq_of_equiv_fin` / 定理 `Finset.card_eq_of_equiv_fin`

English:
theorem Finset.card_eq_of_equiv_fin
  given: {s : Finset α} {n : Nat} (i : s ≃ Fin n)
  statement: #s = n
  proof: Fin.equiv_iff_eq.1 ⟨s.equivFin.symm.trans i⟩

中文:
定理 Finset.card_eq_of_equiv_fin
  条件: {s : Finset α} {n : 自然数} (i : s ≃ Fin n)
  结论: #s = n
  证明: Fin.equiv_iff_eq.1 ⟨s.equivFin.symm.trans i⟩

Depends on / 依赖: Fin.equiv_iff_eq, equivFin, equiv_iff_eq, s.equivFin.symm.trans
-/
theorem Finset.card_eq_of_equiv_fin {s : Finset α} {n : Nat} (i : s ≃ Fin n) : #s = n :=
  Fin.equiv_iff_eq.1 ⟨s.equivFin.symm.trans i⟩

/--
theorem `Finset.card_eq_of_equiv_fintype` / 定理 `Finset.card_eq_of_equiv_fintype`

English:
theorem Finset.card_eq_of_equiv_fintype
  given: {s : Finset α} [Fintype β] (i : s ≃ β)
  proof: card_eq_of_equiv_fin i.trans Fintype.equivFin β

中文:
定理 Finset.card_eq_of_equiv_fintype
  条件: {s : Finset α} [Fintype β] (i : s ≃ β)
  证明: card_eq_of_equiv_fin i.trans Fintype.equivFin β

Depends on / 依赖: Fintype, Fintype.equivFin, card_eq_of_equiv_fin, equivFin, i.trans
-/
theorem Finset.card_eq_of_equiv_fintype {s : Finset α} [Fintype β] (i : s ≃ β) :
#s = Fintype.card β := card_eq_of_equiv_fin i.trans Fintype.equivFin β

/--
Definition of `Finset.equivOfCardEq` / `Finset.equivOfCardEq` 的定义

English:
definition Finset.equivOfCardEq
  signature: {s : Finset α} {t : Finset β} (h : #s = #t)
  body: Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))

中文:
定义 Finset.equivOfCardEq
  签名: {s : Finset α} {t : Finset β} (h : #s = #t)
  定义体: Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))

Depends on / 依赖: Fintype, Fintype.card_coe, Fintype.equivOfCardEq, card_coe, equivOfCardEq, h.trans
-/
noncomputable def Finset.equivOfCardEq {s : Finset α} {t : Finset β} (h : #s = #t) :
    s ≃ t := Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))

/--
theorem `Finset.card_eq_of_equiv` / 定理 `Finset.card_eq_of_equiv`

English:
theorem Finset.card_eq_of_equiv
  given: {s : Finset α} {t : Finset β} (i : s ≃ t)
  statement: #s = #t
  proof: (card_eq_of_equiv_fintype i).trans (Fintype.card_coe _)

中文:
定理 Finset.card_eq_of_equiv
  条件: {s : Finset α} {t : Finset β} (i : s ≃ t)
  结论: #s = #t
  证明: (card_eq_of_equiv_fintype i).trans (Fintype.card_coe _)

Depends on / 依赖: Fintype, Fintype.card_coe, card_coe, card_eq_of_equiv_fintype
-/
theorem Finset.card_eq_of_equiv {s : Finset α} {t : Finset β} (i : s ≃ t) : #s = #t :=
  (card_eq_of_equiv_fintype i).trans (Fintype.card_coe _)

namespace Function.Embedding

/--
Definition of `equivOfFiniteSelfEmbedding` / `equivOfFiniteSelfEmbedding` 的定义

English:
definition equivOfFiniteSelfEmbedding
  signature: [Finite α] (e : α ↪ α)
  body: Equiv.ofBijective e e.2.bijective_of_finite

@[simp]

中文:
定义 equivOfFiniteSelfEmbedding
  签名: [Finite α] (e : α ↪ α)
  定义体: Equiv.ofBijective e e.2.bijective_of_finite

@[simp]

Depends on / 依赖: Equiv.ofBijective, bijective_of_finite, ofBijective
-/
noncomputable def equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e e.2.bijective_of_finite

@[simp]
/--
theorem `toEmbedding_equivOfFiniteSelfEmbedding` / 定理 `toEmbedding_equivOfFiniteSelfEmbedding`

English:
theorem toEmbedding_equivOfFiniteSelfEmbedding
  given: [Finite α] (e : α ↪ α)
  proof: by
  ext
  rfl

中文:
定理 toEmbedding_equivOfFiniteSelfEmbedding
  条件: [Finite α] (e : α ↪ α)
  证明: by
  ext
  rfl
-/
theorem toEmbedding_equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) :
    e.equivOfFiniteSelfEmbedding.toEmbedding = e := by
  ext
  rfl

/--
Definition of `_root_.Equiv.embeddingEquivOfFinite` / `_root_.Equiv.embeddingEquivOfFinite` 的定义

English:
definition _root_.Equiv.embeddingEquivOfFinite
  signature: (α : Type*) [Finite α]
  body: e.equivOfFiniteSelfEmbedding
  invFun e := e.toEmbedding

中文:
定义 _root_.Equiv.embeddingEquivOfFinite
  签名: (α : 类型) [Finite α]
  定义体: e.equivOfFiniteSelfEmbedding
  invFun e := e.toEmbedding

Depends on / 依赖: Fact.out, conjExponent
-/
@[simps] noncomputable def _root_.Equiv.embeddingEquivOfFinite (α : Type*) [Finite α] :
    (α ↪ α) ≃ (α ≃ α) where
  toFun e := e.equivOfFiniteSelfEmbedding
  invFun e := e.toEmbedding

/--
Definition of `truncOfCardLE` / `truncOfCardLE` 的定义

English:
definition truncOfCardLE
  signature: [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  body: (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLEEmb h).trans eb.symm.toEmbedding)

中文:
定义 truncOfCardLE
  签名: [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  定义体: (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLEEmb h).trans eb.symm.toEmbedding)

Depends on / 依赖: Fin.castLEEmb, Fintype, Fintype.truncEquivFin, castLEEmb, ea.toEmbedding.trans, eb.symm.toEmbedding, toEmbedding, truncEquivFin
-/
def truncOfCardLE [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α <= Fintype.card β) : Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLEEmb h).trans eb.symm.toEmbedding)

/--
theorem `nonempty_of_card_le` / 定理 `nonempty_of_card_le`

English:
theorem nonempty_of_card_le
  given: [Fintype α] [Fintype β] (h : Fintype.card α <= Fintype.card β)
  proof: by classical exact (truncOfCardLE h).nonempty

中文:
定理 nonempty_of_card_le
  条件: [Fintype α] [Fintype β] (h : Fintype.card α <= Fintype.card β)
  证明: by classical exact (truncOfCardLE h).nonempty

Depends on / 依赖: classical, nonempty, truncOfCardLE
-/
theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α <= Fintype.card β) :
    Nonempty (α ↪ β) := by classical exact (truncOfCardLE h).nonempty

/--
theorem `nonempty_iff_card_le` / 定理 `nonempty_iff_card_le`

English:
theorem nonempty_iff_card_le
  given: [Fintype α] [Fintype β]
  proof: ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩

中文:
定理 nonempty_iff_card_le
  条件: [Fintype α] [Fintype β]
  证明: ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩

Depends on / 依赖: Fintype, Fintype.card_le_of_embedding, card_le_of_embedding, nonempty_of_card_le
-/
theorem nonempty_iff_card_le [Fintype α] [Fintype β] :
    Nonempty (α ↪ β) ↔ Fintype.card α <= Fintype.card β :=
  ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩

/--
theorem `exists_of_card_le_finset` / 定理 `exists_of_card_le_finset`

English:
theorem exists_of_card_le_finset
  given: [Fintype α] {s : Finset β} (h : Fintype.card α <= #s)
  proof: by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact ⟨f.trans (Embedding.subtype _), by simp [Set.range_subset_iff]⟩

中文:
定理 exists_of_card_le_finset
  条件: [Fintype α] {s : Finset β} (h : Fintype.card α <= #s)
  证明: by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact ⟨f.trans (Embedding.subtype _), by simp [Set.range_subset_iff]⟩

Depends on / 依赖: Embedding, Embedding.subtype, Fintype, Fintype.card_coe, Set.range_subset_iff, card_coe, f.trans, nonempty_of_card_le, range_subset_iff, subtype
-/
theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α <= #s) :
    exists f : α ↪ β, Set.range f subseteq s := by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact ⟨f.trans (Embedding.subtype _), by simp [Set.range_subset_iff]⟩

/--
lemma `exists_of_card_eq_finset` / 引理 `exists_of_card_eq_finset`

English:
lemma exists_of_card_eq_finset
  given: [Fintype α] {s : Finset β} (hsn : Fintype.card α = s.card)
  proof: by
  obtain ⟨f : α ↪ β, hf⟩ := exists_of_card_le_finset (Nat.le_of_eq hsn)
  use f
  apply Finset.eq_of_subset_of_card_le
  · simp [← coe_subset, hf]
  · simp [← hsn]

中文:
引理 exists_of_card_eq_finset
  条件: [Fintype α] {s : Finset β} (hsn : Fintype.card α = s.card)
  证明: by
  obtain ⟨f : α ↪ β, hf⟩ := exists_of_card_le_finset (Nat.le_of_eq hsn)
  use f
  apply Finset.eq_of_subset_of_card_le
  · simp [← coe_subset, hf]
  · simp [← hsn]

Depends on / 依赖: Finset, Finset.eq_of_subset_of_card_le, Nat.le_of_eq, coe_subset, eq_of_subset_of_card_le, exists_of_card_le_finset, le_of_eq
-/
lemma exists_of_card_eq_finset [Fintype α] {s : Finset β} (hsn : Fintype.card α = s.card) :
    exists f : α ↪ β, Finset.univ.map f = s := by
  obtain ⟨f : α ↪ β, hf⟩ := exists_of_card_le_finset (Nat.le_of_eq hsn)
  use f
  apply Finset.eq_of_subset_of_card_le
  · simp [← coe_subset, hf]
  · simp [← hsn]

end Function.Embedding

@[simp]
/--
theorem `Finset.univ_map_embedding` / 定理 `Finset.univ_map_embedding`

English:
theorem Finset.univ_map_embedding
  given: {α : Type*} [Fintype α] (e : α ↪ α)
  statement: univ.map e = univ
  proof: by
  rw [← e.toEmbedding_equivOfFiniteSelfEmbedding]; rw [univ_map_equiv_to_embedding]

中文:
定理 Finset.univ_map_embedding
  条件: {α : 类型} [Fintype α] (e : α ↪ α)
  结论: univ.map e = univ
  证明: by
  rw [← e.toEmbedding_equivOfFiniteSelfEmbedding]; rw [univ_map_equiv_to_embedding]

Depends on / 依赖: e.toEmbedding_equivOfFiniteSelfEmbedding, toEmbedding_equivOfFiniteSelfEmbedding, univ_map_equiv_to_embedding
-/
theorem Finset.univ_map_embedding {α : Type*} [Fintype α] (e : α ↪ α) : univ.map e = univ := by
  rw [← e.toEmbedding_equivOfFiniteSelfEmbedding]; rw [univ_map_equiv_to_embedding]

namespace Fintype

/--
theorem `card_lt_of_surjective_not_injective` / 定理 `card_lt_of_surjective_not_injective`

English:
theorem card_lt_of_surjective_not_injective
  statement: [Fintype α] [Fintype β] (f : α -> β)
  proof: card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
h' h.injective_of_finite (Equiv.ofBijective _ w).symm

中文:
定理 card_lt_of_surjective_not_injective
  结论: [Fintype α] [Fintype β] (f : α -> β)
  证明: card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
h' h.injective_of_finite (Equiv.ofBijective _ w).symm

Depends on / 依赖: Bijective, Equiv.ofBijective, Function, Function.Bijective, Function.injective_surjInv, Function.surjInv, card_lt_of_injective_not_surjective, h.injective_of_finite, injective_of_finite, injective_surjInv, ofBijective, surjInv
-/
theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α -> β)
    (h : Function.Surjective f) (h' : ¬Function.Injective f) : card β < card α :=
  card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
h' h.injective_of_finite (Equiv.ofBijective _ w).symm

end Fintype

/--
theorem `Fintype.false` / 定理 `Fintype.false`

English:
theorem Fintype.false
  given: [Infinite α] (_h : Fintype α)
  statement: False
  proof: not_finite α

@[simp]

中文:
定理 Fintype.false
  条件: [Infinite α] (_h : Fintype α)
  结论: False
  证明: not_finite α

@[simp]
-/
protected theorem Fintype.false [Infinite α] (_h : Fintype α) : False :=
  not_finite α

@[simp]
/--
theorem `isEmpty_fintype` / 定理 `isEmpty_fintype`

English:
theorem isEmpty_fintype
  given: {α : Type*}
  statement: IsEmpty (Fintype α) ↔ Infinite α
  proof: ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.finite⟩⟩

中文:
定理 isEmpty_fintype
  条件: {α : 类型}
  结论: IsEmpty (Fintype α) ↔ Infinite α
  证明: ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.finite⟩⟩

Depends on / 依赖: finite, nonempty_fintype
-/
theorem isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.finite⟩⟩

/-- A non-infinite type is a fintype. -/
@[instance_reducible]
/--
Definition of `fintypeOfNotInfinite` / `fintypeOfNotInfinite` 的定义

English:
definition fintypeOfNotInfinite
  signature: {α : Type*} (h : ¬Infinite α)
  body: @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)

中文:
定义 fintypeOfNotInfinite
  签名: {α : 类型} (h : ¬Infinite α)
  定义体: @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)

Depends on / 依赖: Fintype, Fintype.ofFinite, not_infinite_iff_finite, not_infinite_iff_finite.mp, ofFinite
-/
noncomputable def fintypeOfNotInfinite {α : Type*} (h : ¬Infinite α) : Fintype α :=
  @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)

section

open scoped Classical in
/--
Definition of `fintypeOrInfinite` / `fintypeOrInfinite` 的定义

English:
definition fintypeOrInfinite
  signature: (α : Type*)
  body: if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)

中文:
定义 fintypeOrInfinite
  签名: (α : 类型)
  定义体: if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)

Depends on / 依赖: Infinite, PSum.inl, PSum.inr, fintypeOfNotInfinite
-/
noncomputable def fintypeOrInfinite (α : Type*) : Fintype α oplus' Infinite α :=
  if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)

end

namespace Infinite

/--
theorem `of_not_fintype` / 定理 `of_not_fintype`

English:
theorem of_not_fintype
  given: (h : Fintype α -> False)
  statement: Infinite α
  proof: isEmpty_fintype.mp ⟨h⟩

中文:
定理 of_not_fintype
  条件: (h : Fintype α -> False)
  结论: Infinite α
  证明: isEmpty_fintype.mp ⟨h⟩

Depends on / 依赖: isEmpty_fintype, isEmpty_fintype.mp
-/
theorem of_not_fintype (h : Fintype α -> False) : Infinite α :=
  isEmpty_fintype.mp ⟨h⟩

/--
theorem `of_injective_to_set` / 定理 `of_injective_to_set`

English:
theorem of_injective_to_set
  given: {s : Set α} (hs : s != Set.univ) {f : α -> s} (hf : Injective f)
  proof: of_not_fintype fun h => by
    classical
      refine lt_irrefl (Fintype.card α) ?_
      calc
        Fintype.card α <= Fintype.card s := Fintype.card_le_of_injective f hf
        _ = #s.toFinset := s.toFinset_card.symm
        _ < Fintype.card α :=
Finset.card_lt_card by rwa [Set.toFinset_ssubset_

中文:
定理 of_injective_to_set
  条件: {s : Set α} (hs : s != Set.univ) {f : α -> s} (hf : Injective f)
  证明: of_not_fintype fun h => by
    classical
      refine lt_irrefl (Fintype.card α) ?_
      calc
        Fintype.card α <= Fintype.card s := Fintype.card_le_of_injective f hf
        _ = #s.toFinset := s.toFinset_card.symm
        _ < Fintype.card α :=
Finset.card_lt_card by rwa [Set.toFinset_ssubset_

Depends on / 依赖: Finset, Finset.card_lt_card, Fintype, Fintype.card, Fintype.card_le_of_injective, Set.ssubset_univ_iff, Set.toFinset_ssubset_univ, card_le_of_injective, card_lt_card, classical, lt_irrefl, of_not_fintype, s.toFinset, s.toFinset_card.symm, ssubset_univ_iff, toFinset, toFinset_card, toFinset_ssubset_univ
-/
theorem of_injective_to_set {s : Set α} (hs : s != Set.univ) {f : α -> s} (hf : Injective f) :
    Infinite α :=
  of_not_fintype fun h => by
    classical
      refine lt_irrefl (Fintype.card α) ?_
      calc
        Fintype.card α <= Fintype.card s := Fintype.card_le_of_injective f hf
        _ = #s.toFinset := s.toFinset_card.symm
        _ < Fintype.card α :=
Finset.card_lt_card by rwa [Set.toFinset_ssubset_univ, Set.ssubset_univ_iff]

/--
theorem `of_surjective_from_set` / 定理 `of_surjective_from_set`

English:
theorem of_surjective_from_set
  given: {s : Set α} (hs : s != Set.univ) {f : s -> α} (hf : Surjective f)
  proof: of_injective_to_set hs (injective_surjInv hf)

中文:
定理 of_surjective_from_set
  条件: {s : Set α} (hs : s != Set.univ) {f : s -> α} (hf : Surjective f)
  证明: of_injective_to_set hs (injective_surjInv hf)

Depends on / 依赖: injective_surjInv, of_injective_to_set
-/
theorem of_surjective_from_set {s : Set α} (hs : s != Set.univ) {f : s -> α} (hf : Surjective f) :
    Infinite α :=
  of_injective_to_set hs (injective_surjInv hf)

/--
theorem `exists_notMem_finset` / 定理 `exists_notMem_finset`

English:
theorem exists_notMem_finset
  given: [Infinite α] (s : Finset α)
  statement: exists x, x ∉ s
  proof: not_forall.1 fun h => Fintype.false ⟨s, h⟩

中文:
定理 exists_notMem_finset
  条件: [Infinite α] (s : Finset α)
  结论: 存在 x, x ∉ s
  证明: not_forall.1 fun h => Fintype.false ⟨s, h⟩

Depends on / 依赖: Fintype, Fintype.false, not_forall
-/
theorem exists_notMem_finset [Infinite α] (s : Finset α) : exists x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩

-- see Note [lower instance priority]
instance (priority := 100) (α : Type*) [Infinite α] : Nontrivial α :=
  ⟨let ⟨x, _hx⟩ := exists_notMem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_notMem_finset ({x} : Finset α)
    ⟨y, x, by simpa only [mem_singleton] using hy⟩⟩

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (α : Type*) [Infinite α]
  statement: Nonempty α
  proof: by infer_instance

中文:
定理 nonempty
  条件: (α : 类型) [Infinite α]
  结论: Nonempty α
  证明: by infer_instance
-/
protected theorem nonempty (α : Type*) [Infinite α] : Nonempty α := by infer_instance

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: {α β} [Infinite β] (f : β -> α) (hf : Injective f)
  statement: Infinite α
  proof: ⟨fun _I => (Finite.of_injective f hf).false⟩

中文:
定理 of_injective
  条件: {α β} [Infinite β] (f : β -> α) (hf : Injective f)
  结论: Infinite α
  证明: ⟨fun _I => (Finite.of_injective f hf).false⟩

Depends on / 依赖: Finite, Finite.of_injective, of_injective
-/
theorem of_injective {α β} [Infinite β] (f : β -> α) (hf : Injective f) : Infinite α :=
  ⟨fun _I => (Finite.of_injective f hf).false⟩

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: {α β} [Infinite β] (f : α -> β) (hf : Surjective f)
  statement: Infinite α
  proof: ⟨fun _I => (Finite.of_surjective f hf).false⟩

中文:
定理 of_surjective
  条件: {α β} [Infinite β] (f : α -> β) (hf : Surjective f)
  结论: Infinite α
  证明: ⟨fun _I => (Finite.of_surjective f hf).false⟩

Depends on / 依赖: Finite, Finite.of_surjective, of_surjective
-/
theorem of_surjective {α β} [Infinite β] (f : α -> β) (hf : Surjective f) : Infinite α :=
  ⟨fun _I => (Finite.of_surjective f hf).false⟩

instance {β : α -> Type*} [Infinite α] [forall a, Nonempty (β a)] : Infinite ((a : α) × β a) :=
  Infinite.of_surjective Sigma.fst Sigma.fst_surjective

/--
theorem `sigma_of_right` / 定理 `sigma_of_right`

English:
theorem sigma_of_right
  given: {β : α -> Type*} {a : α} [Infinite (β a)]
  proof: Infinite.of_injective (f := fun x => ⟨a,x⟩) fun _ _ => by simp

中文:
定理 sigma_of_right
  条件: {β : α -> 类型} {a : α} [Infinite (β a)]
  证明: Infinite.of_injective (f := fun x => ⟨a,x⟩) fun _ _ => by simp

Depends on / 依赖: Infinite, Infinite.of_injective, of_injective
-/
theorem sigma_of_right {β : α -> Type*} {a : α} [Infinite (β a)] :
    Infinite ((a : α) × β a) :=
  Infinite.of_injective (f := fun x => ⟨a,x⟩) fun _ _ => by simp

instance {β : α -> Type*} [Nonempty α] [forall a, Infinite (β a)] : Infinite ((a : α) × β a) :=
  Infinite.sigma_of_right (a := Classical.arbitrary α)

end Infinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Infinite Nat
  body: Infinite.of_not_fintype by
    intro h
    exact (Finset.range _).card_le_univ.not_gt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)

中文:
实例 :
  签名: Infinite 自然数
  定义体: Infinite.of_not_fintype by
    intro h
    exact (Finset.range _).card_le_univ.not_gt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)

Depends on / 依赖: Finset, Finset.range, Infinite, Infinite.of_not_fintype, Nat.lt_succ_self, card_le_univ, card_le_univ.not_gt, card_range, lt_succ_self, not_gt, of_not_fintype, trans_eq
-/
instance : Infinite Nat :=
Infinite.of_not_fintype by
    intro h
    exact (Finset.range _).card_le_univ.not_gt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)

/--
Instance `Int.infinite` / 实例 `Int.infinite`

English:
instance Int.infinite
  signature: : Infinite Int
  body: Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj

中文:
实例 Int.infinite
  签名: : Infinite 整数
  定义体: Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj

Depends on / 依赖: Infinite, Infinite.of_injective, Int.ofNat, Int.ofNat.inj, of_injective
-/
instance Int.infinite : Infinite Int :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Infinite (Multiset α)
  body: let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)

中文:
实例 [Nonempty
  签名: α] : Infinite (Multiset α)
  定义体: let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)

Depends on / 依赖: Infinite, Infinite.of_injective, Multiset, Multiset.replicate, Multiset.replicate_left_injective, Nonempty, of_injective, replicate, replicate_left_injective
-/
instance [Nonempty α] : Infinite (Multiset α) :=
  let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Infinite (List α)
  body: Infinite.of_surjective ((↑) : List α -> Multiset α) Quot.mk_surjective

中文:
实例 [Nonempty
  签名: α] : Infinite (List α)
  定义体: Infinite.of_surjective ((↑) : List α -> Multiset α) Quot.mk_surjective

Depends on / 依赖: Infinite, Infinite.of_surjective, Multiset, Quot.mk_surjective, mk_surjective, of_surjective
-/
instance [Nonempty α] : Infinite (List α) :=
  Infinite.of_surjective ((↑) : List α -> Multiset α) Quot.mk_surjective

/--
Instance `String.infinite` / 实例 `String.infinite`

English:
instance String.infinite
  signature: : Infinite String
  body: Infinite.of_injective String.ofList (fun _ _ => String.ofList_injective)

中文:
实例 String.infinite
  签名: : Infinite String
  定义体: Infinite.of_injective String.ofList (fun _ _ => String.ofList_injective)

Depends on / 依赖: Infinite, Infinite.of_injective, String.ofList, String.ofList_injective, ofList, ofList_injective, of_injective
-/
instance String.infinite : Infinite String :=
  Infinite.of_injective String.ofList (fun _ _ => String.ofList_injective)

/--
Instance `Infinite.set` / 实例 `Infinite.set`

English:
instance Infinite.set
  signature: [Infinite α]
  body: Infinite.of_injective singleton Set.singleton_injective

中文:
实例 Infinite.set
  签名: [Infinite α]
  定义体: Infinite.of_injective singleton Set.singleton_injective

Depends on / 依赖: Infinite, Infinite.of_injective, Set.singleton_injective, of_injective, singleton, singleton_injective
-/
instance Infinite.set [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective singleton Set.singleton_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite (Finset α)
  body: Infinite.of_injective singleton Finset.singleton_injective

中文:
实例 [Infinite
  签名: α] : Infinite (Finset α)
  定义体: Infinite.of_injective singleton Finset.singleton_injective

Depends on / 依赖: Finset, Finset.singleton_injective, Infinite, Infinite.of_injective, of_injective, singleton, singleton_injective
-/
instance [Infinite α] : Infinite (Finset α) :=
  Infinite.of_injective singleton Finset.singleton_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite (Option α)
  body: Infinite.of_injective some (Option.some_injective α)

中文:
实例 [Infinite
  签名: α] : Infinite (Option α)
  定义体: Infinite.of_injective some (Option.some_injective α)

Depends on / 依赖: Infinite, Infinite.of_injective, Option.some_injective, of_injective, some_injective
-/
instance [Infinite α] : Infinite (Option α) :=
  Infinite.of_injective some (Option.some_injective α)

/--
Instance `Sum.infinite_of_left` / 实例 `Sum.infinite_of_left`

English:
instance Sum.infinite_of_left
  signature: [Infinite α]
  body: Infinite.of_injective Sum.inl Sum.inl_injective

中文:
实例 Sum.infinite_of_left
  签名: [Infinite α]
  定义体: Infinite.of_injective Sum.inl Sum.inl_injective

Depends on / 依赖: Infinite, Infinite.of_injective, Sum.inl, Sum.inl_injective, inl_injective, of_injective
-/
instance Sum.infinite_of_left [Infinite α] : Infinite (α oplus β) :=
  Infinite.of_injective Sum.inl Sum.inl_injective

/--
Instance `Sum.infinite_of_right` / 实例 `Sum.infinite_of_right`

English:
instance Sum.infinite_of_right
  signature: [Infinite β]
  body: Infinite.of_injective Sum.inr Sum.inr_injective

中文:
实例 Sum.infinite_of_right
  签名: [Infinite β]
  定义体: Infinite.of_injective Sum.inr Sum.inr_injective

Depends on / 依赖: Infinite, Infinite.of_injective, Sum.inr, Sum.inr_injective, inr_injective, of_injective
-/
instance Sum.infinite_of_right [Infinite β] : Infinite (α oplus β) :=
  Infinite.of_injective Sum.inr Sum.inr_injective

/--
Instance `Prod.infinite_of_right` / 实例 `Prod.infinite_of_right`

English:
instance Prod.infinite_of_right
  signature: [Nonempty α] [Infinite β]
  body: Infinite.of_surjective Prod.snd Prod.snd_surjective

中文:
实例 Prod.infinite_of_right
  签名: [Nonempty α] [Infinite β]
  定义体: Infinite.of_surjective Prod.snd Prod.snd_surjective

Depends on / 依赖: Infinite, Infinite.of_surjective, Prod.snd, Prod.snd_surjective, of_surjective, snd_surjective
-/
instance Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.snd Prod.snd_surjective

/--
Instance `Prod.infinite_of_left` / 实例 `Prod.infinite_of_left`

English:
instance Prod.infinite_of_left
  signature: [Infinite α] [Nonempty β]
  body: Infinite.of_surjective Prod.fst Prod.fst_surjective

中文:
实例 Prod.infinite_of_left
  签名: [Infinite α] [Nonempty β]
  定义体: Infinite.of_surjective Prod.fst Prod.fst_surjective

Depends on / 依赖: Infinite, Infinite.of_surjective, Prod.fst, Prod.fst_surjective, fst_surjective, of_surjective
-/
instance Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.fst Prod.fst_surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite (Equiv.Perm α)
  body: by
  classical
  obtain ⟨a : α⟩ := Nontrivial.to_nonempty (α := α)
  exact Infinite.of_injective _ (Equiv.swap_injective_of_left a)

中文:
实例 [Infinite
  签名: α] : Infinite (Equiv.Perm α)
  定义体: by
  classical
  obtain ⟨a : α⟩ := Nontrivial.to_nonempty (α := α)
  exact Infinite.of_injective _ (Equiv.swap_injective_of_left a)

Depends on / 依赖: Equiv.swap_injective_of_left, Infinite, Infinite.of_injective, Nontrivial, Nontrivial.to_nonempty, classical, of_injective, swap_injective_of_left, to_nonempty
-/
instance [Infinite α] : Infinite (Equiv.Perm α) := by
  classical
  obtain ⟨a : α⟩ := Nontrivial.to_nonempty (α := α)
  exact Infinite.of_injective _ (Equiv.swap_injective_of_left a)

namespace Infinite

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def natEmbeddingAux (α : Type*) [Infinite α]
  body: Classical.decEq α
    Classical.choose
      (exists_notMem_finset
        ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)

中文:
定义 noncomputable
  签名: def natEmbeddingAux (α : 类型) [Infinite α]
  定义体: Classical.decEq α
    Classical.choose
      (exists_notMem_finset
        ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)
-/
private noncomputable def natEmbeddingAux (α : Type*) [Infinite α] : Nat -> α
  | n =>
    letI := Classical.decEq α
    Classical.choose
      (exists_notMem_finset
        ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)

set_option backward.privateInPublic true in
/--
theorem `natEmbeddingAux_injective` / 定理 `natEmbeddingAux_injective`

English:
theorem natEmbeddingAux_injective
  given: (α : Type*) [Infinite α]
  proof: by
  rintro m n h
  let := Classical.decEq α
  wlog hmlen : m <= n generalizing m n
  · exact (this h.symm <| le_of_not_ge hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine (Classical.choose_spec (exists_notMem_finset
    ((Multiset.range n).pmap (fun m (_ : m < n) 

中文:
定理 natEmbeddingAux_injective
  条件: (α : 类型) [Infinite α]
  证明: by
  rintro m n h
  let := Classical.decEq α
  wlog hmlen : m <= n generalizing m n
  · exact (this h.symm <| le_of_not_ge hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine (Classical.choose_spec (exists_notMem_finset
    ((Multiset.range n).pmap (fun m (_ : m < n) 
-/
private theorem natEmbeddingAux_injective (α : Type*) [Infinite α] :
    Function.Injective (natEmbeddingAux α) := by
  rintro m n h
  let := Classical.decEq α
  wlog hmlen : m <= n generalizing m n
  · exact (this h.symm <| le_of_not_ge hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine (Classical.choose_spec (exists_notMem_finset
    ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux α m)
      (fun _ => Multiset.mem_range.1)).toFinset)) ?_
  refine Multiset.mem_toFinset.2 (Multiset.mem_pmap.2 ⟨m, Multiset.mem_range.2 hmn, ?_⟩)
  rw [h]; rw [natEmbeddingAux]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `natEmbedding` / `natEmbedding` 的定义

English:
definition natEmbedding
  signature: (α : Type*) [Infinite α]
  body: ⟨_, natEmbeddingAux_injective α⟩

中文:
定义 natEmbedding
  签名: (α : 类型) [Infinite α]
  定义体: ⟨_, natEmbeddingAux_injective α⟩

Depends on / 依赖: natEmbeddingAux_injective
-/
noncomputable def natEmbedding (α : Type*) [Infinite α] : Nat ↪ α :=
  ⟨_, natEmbeddingAux_injective α⟩

/--
theorem `exists_subset_card_eq` / 定理 `exists_subset_card_eq`

English:
theorem exists_subset_card_eq
  given: (α : Type*) [Infinite α] (n : Nat)
  statement: exists s : Finset α, #s = n
  proof: ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩

中文:
定理 exists_subset_card_eq
  条件: (α : 类型) [Infinite α] (n : 自然数)
  结论: 存在 s : Finset α, #s = n
  证明: ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩

Depends on / 依赖: card_map, card_range, natEmbedding
-/
theorem exists_subset_card_eq (α : Type*) [Infinite α] (n : Nat) : exists s : Finset α, #s = n :=
  ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩

/--
theorem `exists_superset_card_eq` / 定理 `exists_superset_card_eq`

English:
theorem exists_superset_card_eq
  given: [Infinite α] (s : Finset α) (n : Nat) (hn : #s <= n)
  proof: by
  induction n generalizing s with
  | zero => exact ⟨s, subset_rfl, Nat.eq_zero_of_le_zero hn⟩
  | succ n IH =>
    rcases hn.eq_or_lt with hn' | hn'
    · exact ⟨s, subset_rfl, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_notMem_finset t
    refine ⟨Fi

中文:
定理 exists_superset_card_eq
  条件: [Infinite α] (s : Finset α) (n : 自然数) (hn : #s <= n)
  证明: by
  induction n generalizing s with
  | zero => exact ⟨s, subset_rfl, Nat.eq_zero_of_le_zero hn⟩
  | succ n IH =>
    rcases hn.eq_or_lt with hn' | hn'
    · exact ⟨s, subset_rfl, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_notMem_finset t
    refine ⟨Fi

Depends on / 依赖: Finset, Finset.cons, Finset.subset_cons, Nat.eq_zero_of_le_zero, Nat.le_of_lt_succ, eq_or_lt, eq_zero_of_le_zero, exists_notMem_finset, generalizing, hn.eq_or_lt, hs.trans, le_of_lt_succ, subset_cons, subset_rfl
-/
theorem exists_superset_card_eq [Infinite α] (s : Finset α) (n : Nat) (hn : #s <= n) :
    exists t : Finset α, s subseteq t ∧ #t = n := by
  induction n generalizing s with
  | zero => exact ⟨s, subset_rfl, Nat.eq_zero_of_le_zero hn⟩
  | succ n IH =>
    rcases hn.eq_or_lt with hn' | hn'
    · exact ⟨s, subset_rfl, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_notMem_finset t
    refine ⟨Finset.cons x t hx, hs.trans (Finset.subset_cons _), ?_⟩
    simp [ht]

end Infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
@[instance_reducible]
/--
Definition of `fintypeOfFinsetCardLe` / `fintypeOfFinsetCardLe` 的定义

English:
definition fintypeOfFinsetCardLe
  signature: {ι : Type*} (n : Nat) (w : forall s : Finset ι, #s <= n)
  body: by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w

中文:
定义 fintypeOfFinsetCardLe
  签名: {ι : 类型} (n : 自然数) (w : 对任意 s : Finset ι, #s <= n)
  定义体: by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w

Depends on / 依赖: Infinite, Infinite.exists_subset_card_eq, Nat.not_succ_le_self, exists_subset_card_eq, fintypeOfNotInfinite, not_succ_le_self, specialize
-/
noncomputable def fintypeOfFinsetCardLe {ι : Type*} (n : Nat) (w : forall s : Finset ι, #s <= n) :
    Fintype ι := by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w

/--
theorem `not_injective_infinite_finite` / 定理 `not_injective_infinite_finite`

English:
theorem not_injective_infinite_finite
  given: {α β} [Infinite α] [Finite β] (f : α -> β)
  statement: ¬Injective f
  proof: fun hf => (Finite.of_injective f hf).false

中文:
定理 not_injective_infinite_finite
  条件: {α β} [Infinite α] [Finite β] (f : α -> β)
  结论: ¬Injective f
  证明: fun hf => (Finite.of_injective f hf).false

Depends on / 依赖: Finite, Finite.of_injective, of_injective
-/
theorem not_injective_infinite_finite {α β} [Infinite α] [Finite β] (f : α -> β) : ¬Injective f :=
  fun hf => (Finite.of_injective f hf).false

/--
Instance `Function.Embedding.is_empty` / 实例 `Function.Embedding.is_empty`

English:
instance Function.Embedding.is_empty
  signature: {α β} [Infinite α] [Finite β]
  body: ⟨fun f => not_injective_infinite_finite f f.2⟩

中文:
实例 Function.Embedding.is_empty
  签名: {α β} [Infinite α] [Finite β]
  定义体: ⟨fun f => not_injective_infinite_finite f f.2⟩

Depends on / 依赖: not_injective_infinite_finite
-/
instance Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β) :=
  ⟨fun f => not_injective_infinite_finite f f.2⟩

/--
theorem `not_surjective_finite_infinite` / 定理 `not_surjective_finite_infinite`

English:
theorem not_surjective_finite_infinite
  given: {α β} [Finite α] [Infinite β] (f : α -> β)
  statement: ¬Surjective f
  proof: fun hf => (Infinite.of_surjective f hf).not_finite ‹_›

中文:
定理 not_surjective_finite_infinite
  条件: {α β} [Finite α] [Infinite β] (f : α -> β)
  结论: ¬Surjective f
  证明: fun hf => (Infinite.of_surjective f hf).not_finite ‹_›

Depends on / 依赖: Infinite, Infinite.of_surjective, not_finite, of_surjective
-/
theorem not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α -> β) : ¬Surjective f :=
  fun hf => (Infinite.of_surjective f hf).not_finite ‹_›
