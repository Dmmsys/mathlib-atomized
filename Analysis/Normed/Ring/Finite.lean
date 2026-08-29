/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Analysis.Normed.Ring.Basic


/-!
# Finite order elements in normed rings.

A finite order element in a normed ring has norm 1.

The values of additive characters on finite cancellative monoids have norm 1.

-/

public section

variable {α β : Type*}

section NormedRing
variable [NormedRing α] [NormMulClass α] [NormOneClass α] {a : α}

/--
lemma `IsOfFinOrder.norm_eq_one` / 引理 `IsOfFinOrder.norm_eq_one`

English:
lemma IsOfFinOrder.norm_eq_one
  given: (ha : IsOfFinOrder a)
  statement: ‖a‖ = 1
  proof: ((normHom : α ->*₀ Real).toMonoidHom.isOfFinOrder ha).eq_one norm_nonneg _

example [Monoid β] (φ : β ->* α) {x : β} {k : Nat+} (h : x ^ (k : Nat) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one

中文:
引理 IsOfFinOrder.norm_eq_one
  条件: (ha : IsOfFinOrder a)
  结论: ‖a‖ = 1
  证明: ((normHom : α ->*₀ Real).toMonoidHom.isOfFinOrder ha).eq_one norm_nonneg _

example [Monoid β] (φ : β ->* α) {x : β} {k : Nat+} (h : x ^ (k : Nat) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one
-/
protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
((normHom : α ->*₀ Real).toMonoidHom.isOfFinOrder ha).eq_one norm_nonneg _

example [Monoid β] (φ : β ->* α) {x : β} {k : Nat+} (h : x ^ (k : Nat) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one

/--
lemma `AddChar.norm_apply` / 引理 `AddChar.norm_apply`

English:
lemma AddChar.norm_apply
  statement: {G : Type*} [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
  proof: (ψ.toMonoidHom.isOfFinOrder <| isOfFinOrder_of_finite _).norm_eq_one

中文:
引理 加法特征.norm_apply
  结论: {G : 类型} [加法左消去幺半群 G] [有限 G] (ψ : 加法特征 G α)
  证明: (ψ.toMonoidHom.isOfFinOrder <| isOfFinOrder_of_finite _).norm_eq_one
-/
@[simp] lemma AddChar.norm_apply {G : Type*} [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
    (x : G) : ‖ψ x‖ = 1 := (ψ.toMonoidHom.isOfFinOrder <| isOfFinOrder_of_finite _).norm_eq_one

end NormedRing
