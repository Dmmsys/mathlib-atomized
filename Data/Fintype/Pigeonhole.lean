/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.EquivFin

/-!
# Pigeonhole principles in finite types

## Main declarations

We provide the following versions of the pigeonholes principle.
* `Fintype.exists_ne_map_eq_of_card_lt` and `isEmpty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `Finite.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `Finite.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `Data.Fintype.CardEmbedding`.
-/

public section

assert_not_exists MonoidWithZero MulAction

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

variable [Fintype α] [Fintype β]

/--
theorem `exists_ne_map_eq_of_card_lt` / 定理 `exists_ne_map_eq_of_card_lt`

English:
theorem exists_ne_map_eq_of_card_lt
  given: (f : α -> β) (h : Fintype.card β < Fintype.card α)
  proof: let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

中文:
定理 存在_ne_map_eq_of_card_lt
  条件: (f : α -> β) (h : 有限类型.card β < 有限类型.card α)
  证明: let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

Depends on / 依赖: Finset, Finset.exists_ne_map_eq_of_card_lt_of_maps_to, exists_ne_map_eq_of_card_lt_of_maps_to, mem_univ
-/
theorem exists_ne_map_eq_of_card_lt (f : α -> β) (h : Fintype.card β < Fintype.card α) :
    exists x y, x != y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

end Fintype

namespace Function.Embedding

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp]
/--
theorem `isEmpty_of_card_lt` / 定理 `isEmpty_of_card_lt`

English:
theorem isEmpty_of_card_lt
  given: [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α)
  proof: ⟨fun f =>
    let ⟨_x, _y, ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
ne f.injective feq⟩

中文:
定理 isEmpty_of_card_lt
  条件: [有限类型 α] [有限类型 β] (h : 有限类型.card β < 有限类型.card α)
  证明: ⟨fun f =>
    let ⟨_x, _y, ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
ne f.injective feq⟩

Depends on / 依赖: Fintype, Fintype.exists_ne_map_eq_of_card_lt, exists_ne_map_eq_of_card_lt, f.injective, injective
-/
theorem isEmpty_of_card_lt [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α) :
    IsEmpty (α ↪ β) :=
  ⟨fun f =>
    let ⟨_x, _y, ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
ne f.injective feq⟩

end Function.Embedding

/--
theorem `Finite.exists_ne_map_eq_of_infinite` / 定理 `Finite.exists_ne_map_eq_of_infinite`

English:
theorem Finite.exists_ne_map_eq_of_infinite
  given: {α β} [Infinite α] [Finite β] (f : α -> β)
  proof: by
  simpa [Injective, and_comm] using not_injective_infinite_finite f

中文:
定理 有限.存在_ne_map_eq_of_infinite
  条件: {α β} [无限 α] [有限 β] (f : α -> β)
  证明: by
  simpa [Injective, and_comm] using not_injective_infinite_finite f

Depends on / 依赖: Injective, Pairwise, Pairwise.cons, Trans.simple, and_comm, cons_elim, forall_eq_or_imp, h_hd, h_tl, mem_cons_iff, not_injective_infinite_finite, simple
-/
theorem Finite.exists_ne_map_eq_of_infinite {α β} [Infinite α] [Finite β] (f : α -> β) :
    exists x y : α, x != y ∧ f x = f y := by
  simpa [Injective, and_comm] using not_injective_infinite_finite f

attribute [local instance] Fintype.ofFinite in
/--
theorem `Finite.exists_infinite_fiber` / 定理 `Finite.exists_infinite_fiber`

English:
theorem Finite.exists_infinite_fiber
  given: [Infinite α] [Finite β] (f : α -> β)
  proof: by
  classical
    by_contra! hf
    cases nonempty_fintype β
    let key : Fintype α :=
      { elems := univ.biUnion fun y : β => (f ⁻¹' {y}).toFinset
        complete := by simp }
    exact key.false

中文:
定理 有限.存在_infinite_fiber
  条件: [无限 α] [有限 β] (f : α -> β)
  证明: by
  classical
    by_contra! hf
    cases nonempty_fintype β
    let key : Fintype α :=
      { elems := univ.biUnion fun y : β => (f ⁻¹' {y}).toFinset
        complete := by simp }
    exact key.false

Depends on / 依赖: Fintype, biUnion, classical, complete, key.false, nonempty_fintype, toFinset, univ.biUnion
-/
theorem Finite.exists_infinite_fiber [Infinite α] [Finite β] (f : α -> β) :
    exists y : β, Infinite (f ⁻¹' {y}) := by
  classical
    by_contra! hf
    cases nonempty_fintype β
    let key : Fintype α :=
      { elems := univ.biUnion fun y : β => (f ⁻¹' {y}).toFinset
        complete := by simp }
    exact key.false
