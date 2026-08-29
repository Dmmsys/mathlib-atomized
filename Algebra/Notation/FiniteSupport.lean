/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of support
-/

public section

assert_not_exists Monoid

namespace Function
variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
/--
lemma `mulSupport_along_fiber_finite_of_finite` / 引理 `mulSupport_along_fiber_finite_of_finite`

English:
lemma mulSupport_along_fiber_finite_of_finite
  given: (f : α × β -> γ) (a : α) (h : HasFiniteMulSupport f)
  proof: (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

中文:
引理 mulSupport_along_fiber_finite_of_finite
  条件: (f : α × β -> γ) (a : α) (h : HasFiniteMulSupport f)
  证明: (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

Depends on / 依赖: Prod.snd, h.image, mulSupport_along_fiber_subset, subset
-/
lemma mulSupport_along_fiber_finite_of_finite (f : α × β -> γ) (a : α) (h : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun b => f (a, b) :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end Function
