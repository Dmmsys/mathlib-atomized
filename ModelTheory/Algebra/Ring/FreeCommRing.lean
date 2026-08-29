/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.RingTheory.FreeCommRing

/-!
# Making a term in the language of rings from an element of the FreeCommRing

This file defines the function `FirstOrder.Ring.termOfFreeCommRing` which constructs a
`Language.ring.Term α` from an element of `FreeCommRing α`.

The theorem `FirstOrder.Ring.realize_termOfFreeCommRing` shows that the term constructed when
realized in a ring `R` is equal to the lift of the element of `FreeCommRing α` to `R`.
-/

@[expose] public section

namespace FirstOrder

namespace Ring

open Language

variable {α : Type*}

section

attribute [local instance] compatibleRingOfRing

set_option backward.privateInPublic true in
/--
theorem `exists_term_realize_eq_freeCommRing` / 定理 `exists_term_realize_eq_freeCommRing`

English:
theorem exists_term_realize_eq_freeCommRing
  given: (p : FreeCommRing α)
  proof: FreeCommRing.induction_on p
    ⟨-1, by simp⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all⟩)

中文:
定理 存在_term_realize_eq_freeCommRing
  条件: (p : FreeCommRing α)
  证明: FreeCommRing.induction_on p
    ⟨-1, by simp⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all⟩)
-/
private theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing α) :
    exists t : Language.ring.Term α,
      (t.realize FreeCommRing.of : FreeCommRing α) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all⟩)

end

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `termOfFreeCommRing` / `termOfFreeCommRing` 的定义

English:
definition termOfFreeCommRing
  signature: (p : FreeCommRing α)
  body: Classical.choose (exists_term_realize_eq_freeCommRing p)

中文:
定义 termOfFreeCommRing
  签名: (p : FreeCommRing α)
  定义体: Classical.choose (exists_term_realize_eq_freeCommRing p)

Depends on / 依赖: Classical, Classical.choose, exists_term_realize_eq_freeCommRing
-/
noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.ring.Term α :=
  Classical.choose (exists_term_realize_eq_freeCommRing p)

variable {R : Type*} [CommRing R] [CompatibleRing R]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `realize_termOfFreeCommRing` / 定理 `realize_termOfFreeCommRing`

English:
theorem realize_termOfFreeCommRing
  given: (p : FreeCommRing α) (v : α -> R)
  proof: by
  rw [termOfFreeCommRing]
  conv_rhs => rw [← Classical.choose_spec (exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (exists_term_realize_eq_freeCommRing p) with
  | var _ => simp
  | func f a ih =>
    cases f <;>
    simp [ih]

中文:
定理 realize_termOfFreeCommRing
  条件: (p : FreeCommRing α) (v : α -> R)
  证明: by
  rw [termOfFreeCommRing]
  conv_rhs => rw [← Classical.choose_spec (exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (exists_term_realize_eq_freeCommRing p) with
  | var _ => simp
  | func f a ih =>
    cases f <;>
    simp [ih]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, conv_rhs, exists_term_realize_eq_freeCommRing, termOfFreeCommRing
-/
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α -> R) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  rw [termOfFreeCommRing]
  conv_rhs => rw [← Classical.choose_spec (exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (exists_term_realize_eq_freeCommRing p) with
  | var _ => simp
  | func f a ih =>
    cases f <;>
    simp [ih]

end Ring

end FirstOrder
