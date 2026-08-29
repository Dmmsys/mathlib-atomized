/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.FiniteSupport
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite products and sums over types and sets

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `Finset.sum`,
when issues arise with `Finset` and `Fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
  Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
  it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : Set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `Finset` and
`Fintype`. By sticking solely to `Set.Finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
functions. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

We did not add `IsFinite (X : Type) : Prop`, because it is simply `Nonempty (Fintype X)`.

## Tags

finsum, finprod, finite sum, finite product
-/

@[expose] public section


open Function Set

/-!
### Definition and relation to `Finset.sum` and `Finset.prod`
-/

section sort

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

section

/- Note: we use classical logic only for these definitions, to ensure that we do not write lemmas
with `Classical.dec` in their statement. -/

open scoped Classical in
/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α -> M) : M :=
  if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i in h.toFinset, f i.down else 0

open scoped Classical in
/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[to_additive existing]
noncomputable irreducible_def finprod (lemma := finprod_def') (f : α -> M) : M :=
  if h : HasFiniteMulSupport (f ∘ PLift.down) then ∏ i in h.toFinset, f i.down else 1

attribute [to_additive existing] finprod_def'

end

open Batteries.ExtendedBinder

/-- `∑ᶠ x, f x` is notation for `finsum f`. It is the sum of `f x`, where `x` ranges over the
support of `f`, if it's finite, zero otherwise. Taking the sum over multiple arguments or
conditions is possible, e.g. `∏ᶠ (x) (y), f x y` and `∏ᶠ (x) (h: x ∈ s), f x` -/
notation3"∑ᶠ " (...) ", " r:67:(scoped f => finsum f) => r

/-- `∏ᶠ x, f x` is notation for `finprod f`. It is the product of `f x`, where `x` ranges over the
multiplicative support of `f`, if it's finite, one otherwise. Taking the product over multiple
arguments or conditions is possible, e.g. `∏ᶠ (x) (y), f x y` and `∏ᶠ (x) (h: x ∈ s), f x` -/
notation3"∏ᶠ " (...) ", " r:67:(scoped f => finprod f) => r

-- Porting note: The following ports the lean3 notation for this file, but is currently very fickle.

-- syntax (name := bigfinsum) "∑ᶠ" extBinders ", " term:67 : term
-- macro_rules (kind := bigfinsum)
-- | `(∑ᶠ $x:ident, $p) => `(finsum (fun $x:ident ↦ $p))
-- | `(∑ᶠ $x:ident : $t, $p) => `(finsum (fun $x:ident : $t ↦ $p))
-- | `(∑ᶠ $x:ident $b:binderPred, $p) =>
-- `(finsum fun $x => (finsum (α := satisfies_binder_pred% $x $b) (fun _ => $p)))

-- | `(∑ᶠ ($x:ident) ($h:ident : $t), $p) =>
-- `(finsum fun ($x) => finsum (α := $t) (fun $h => $p))
-- | `(∑ᶠ ($x:ident : $_) ($h:ident : $t), $p) =>
-- `(finsum fun ($x) => finsum (α := $t) (fun $h => $p))

-- | `(∑ᶠ ($x:ident) ($y:ident), $p) =>
-- `(finsum fun $x => (finsum fun $y => $p))
-- | `(∑ᶠ ($x:ident) ($y:ident) ($h:ident : $t), $p) =>
-- `(finsum fun $x => (finsum fun $y => (finsum (α := $t) fun $h => $p)))

-- | `(∑ᶠ ($x:ident) ($y:ident) ($z:ident), $p) =>
-- `(finsum fun $x => (finsum fun $y => (finsum fun $z => $p)))
-- | `(∑ᶠ ($x:ident) ($y:ident) ($z:ident) ($h:ident : $t), $p) =>
-- `(finsum fun $x => (finsum fun $y => (finsum fun $z => (finsum (α := $t) fun $h => $p))))
--
--
-- syntax (name := bigfinprod) "∏ᶠ " extBinders ", " term:67 : term
-- macro_rules (kind := bigfinprod)
-- | `(∏ᶠ $x:ident, $p) => `(finprod (fun $x:ident ↦ $p))
-- | `(∏ᶠ $x:ident : $t, $p) => `(finprod (fun $x:ident : $t ↦ $p))
-- | `(∏ᶠ $x:ident $b:binderPred, $p) =>
-- `(finprod fun $x => (finprod (α := satisfies_binder_pred% $x $b) (fun _ => $p)))

-- | `(∏ᶠ ($x:ident) ($h:ident : $t), $p) =>
-- `(finprod fun ($x) => finprod (α := $t) (fun $h => $p))
-- | `(∏ᶠ ($x:ident : $_) ($h:ident : $t), $p) =>
-- `(finprod fun ($x) => finprod (α := $t) (fun $h => $p))

-- | `(∏ᶠ ($x:ident) ($y:ident), $p) =>
-- `(finprod fun $x => (finprod fun $y => $p))
-- | `(∏ᶠ ($x:ident) ($y:ident) ($h:ident : $t), $p) =>
-- `(finprod fun $x => (finprod fun $y => (finprod (α := $t) fun $h => $p)))

-- | `(∏ᶠ ($x:ident) ($y:ident) ($z:ident), $p) =>
-- `(finprod fun $x => (finprod fun $y => (finprod fun $z => $p)))
-- | `(∏ᶠ ($x:ident) ($y:ident) ($z:ident) ($h:ident : $t), $p) =>
-- `(finprod fun $x => (finprod fun $y => (finprod fun $z =>
-- (finprod (α := $t) fun $h => $p))))

@[to_additive]
/--
theorem `finprod_eq_prod_plift_of_mulSupport_toFinset_subset` / 定理 `finprod_eq_prod_plift_of_mulSupport_toFinset_subset`

English:
theorem finprod_eq_prod_plift_of_mulSupport_toFinset_subset
  statement: {f : α -> M}
  proof: by
  rw [finprod]; rw [dif_pos hf]
  refine Finset.prod_subset hs fun x _ hxf => ?_
  rwa [hf.mem_toFinset, notMem_mulSupport] at hxf

@[to_additive]

中文:
定理 finprod_eq_prod_plift_of_mulSupport_toFinset_subset
  结论: {f : α -> M}
  证明: by
  rw [finprod]; rw [dif_pos hf]
  refine Finset.prod_subset hs fun x _ hxf => ?_
  rwa [hf.mem_toFinset, notMem_mulSupport] at hxf

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_subset, dif_pos, finprod, hf.mem_toFinset, mem_toFinset, notMem_mulSupport, prod_subset
-/
theorem finprod_eq_prod_plift_of_mulSupport_toFinset_subset {f : α -> M}
    (hf : HasFiniteMulSupport (f ∘ PLift.down)) {s : Finset (PLift α)} (hs : hf.toFinset subseteq s) :
    ∏ᶠ i, f i = ∏ i in s, f i.down := by
  rw [finprod]; rw [dif_pos hf]
  refine Finset.prod_subset hs fun x _ hxf => ?_
  rwa [hf.mem_toFinset, notMem_mulSupport] at hxf

@[to_additive]
/--
theorem `finprod_eq_prod_plift_of_mulSupport_subset` / 定理 `finprod_eq_prod_plift_of_mulSupport_subset`

English:
theorem finprod_eq_prod_plift_of_mulSupport_subset
  statement: {f : α -> M} {s : Finset (PLift α)}
  proof: finprod_eq_prod_plift_of_mulSupport_toFinset_subset (s.finite_toSet.subset hs) fun x hx => by
    rw [Finite.mem_toFinset] at hx
    exact hs hx

@[to_additive (attr := simp)]

中文:
定理 finprod_eq_prod_plift_of_mulSupport_subset
  结论: {f : α -> M} {s : Finset (PLift α)}
  证明: finprod_eq_prod_plift_of_mulSupport_toFinset_subset (s.finite_toSet.subset hs) fun x hx => by
    rw [Finite.mem_toFinset] at hx
    exact hs hx

@[to_additive (attr := simp)]

Depends on / 依赖: Finite, Finite.mem_toFinset, finite_toSet, finprod_eq_prod_plift_of_mulSupport_toFinset_subset, mem_toFinset, s.finite_toSet.subset, subset
-/
theorem finprod_eq_prod_plift_of_mulSupport_subset {f : α -> M} {s : Finset (PLift α)}
    (hs : mulSupport (f ∘ PLift.down) subseteq s) : ∏ᶠ i, f i = ∏ i in s, f i.down :=
  finprod_eq_prod_plift_of_mulSupport_toFinset_subset (s.finite_toSet.subset hs) fun x hx => by
    rw [Finite.mem_toFinset] at hx
    exact hs hx

@[to_additive (attr := simp)]
/--
theorem `finprod_one` / 定理 `finprod_one`

English:
theorem finprod_one
  statement: (∏ᶠ _ : α, (1 : M)) = 1
  proof: by
  have : (mulSupport fun x : PLift α => (fun _ => 1 : α -> M) x.down) subseteq (∅ : Finset (PLift α)) :=
    fun x h => by simp at h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]; rw [Finset.prod_empty]

@[to_additive]

中文:
定理 finprod_one
  结论: (∏ᶠ _ : α, (1 : M)) = 1
  证明: by
  have : (mulSupport fun x : PLift α => (fun _ => 1 : α -> M) x.down) subseteq (∅ : Finset (PLift α)) :=
    fun x h => by simp at h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]; rw [Finset.prod_empty]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_empty, finprod_eq_prod_plift_of_mulSupport_subset, mulSupport, prod_empty, subseteq, x.down
-/
theorem finprod_one : (∏ᶠ _ : α, (1 : M)) = 1 := by
  have : (mulSupport fun x : PLift α => (fun _ => 1 : α -> M) x.down) subseteq (∅ : Finset (PLift α)) :=
    fun x h => by simp at h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]; rw [Finset.prod_empty]

@[to_additive]
/--
theorem `finprod_of_isEmpty` / 定理 `finprod_of_isEmpty`

English:
theorem finprod_of_isEmpty
  given: [IsEmpty α] (f : α -> M)
  statement: ∏ᶠ i, f i = 1
  proof: by
  rw [← finprod_one]
  congr
  simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp)]

中文:
定理 finprod_of_isEmpty
  条件: [IsEmpty α] (f : α -> M)
  结论: ∏ᶠ i, f i = 1
  证明: by
  rw [← finprod_one]
  congr
  simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp)]

Depends on / 依赖: Algebra, Algebra.algebra_ext, RingHom, RingHom.congr_fun, Subsingleton, Subsingleton.elim, algebra_ext, congr_fun, eq_iff_true_of_subsingleton, finprod_one
-/
theorem finprod_of_isEmpty [IsEmpty α] (f : α -> M) : ∏ᶠ i, f i = 1 := by
  rw [← finprod_one]
  congr
  simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp)]
/--
theorem `finprod_false` / 定理 `finprod_false`

English:
theorem finprod_false
  given: (f : False -> M)
  statement: ∏ᶠ i, f i = 1
  proof: finprod_of_isEmpty _

@[to_additive]

中文:
定理 finprod_false
  条件: (f : False -> M)
  结论: ∏ᶠ i, f i = 1
  证明: finprod_of_isEmpty _

@[to_additive]

Depends on / 依赖: finprod_of_isEmpty
-/
theorem finprod_false (f : False -> M) : ∏ᶠ i, f i = 1 :=
  finprod_of_isEmpty _

@[to_additive]
/--
theorem `finprod_eq_single` / 定理 `finprod_eq_single`

English:
theorem finprod_eq_single
  given: (f : α -> M) (a : α) (ha : forall x, x != a -> f x = 1)
  proof: by
  have : mulSupport (f ∘ PLift.down) subseteq ({PLift.up a} : Finset (PLift α)) := by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]; rw [Finset.prod_singleton]

@[to_additive]

中文:
定理 finprod_eq_single
  条件: (f : α -> M) (a : α) (ha : 对任意 x, x != a -> f x = 1)
  证明: by
  have : mulSupport (f ∘ PLift.down) subseteq ({PLift.up a} : Finset (PLift α)) := by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]; rw [Finset.prod_singleton]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_singleton, PLift.down, PLift.eq_up_iff_down_eq, PLift.up, contrapose, eq_up_iff_down_eq, finprod_eq_prod_plift_of_mulSupport_subset, mulSupport, prod_singleton, subseteq, x.down
-/
theorem finprod_eq_single (f : α -> M) (a : α) (ha : forall x, x != a -> f x = 1) :
    ∏ᶠ x, f x = f a := by
  have : mulSupport (f ∘ PLift.down) subseteq ({PLift.up a} : Finset (PLift α)) := by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]; rw [Finset.prod_singleton]

@[to_additive]
/--
theorem `finprod_unique` / 定理 `finprod_unique`

English:
theorem finprod_unique
  given: [Unique α] (f : α -> M)
  statement: ∏ᶠ i, f i = f default
  proof: finprod_eq_single f default fun _x hx => (hx <| Unique.eq_default _).elim

@[to_additive (attr := simp)]

中文:
定理 finprod_unique
  条件: [Unique α] (f : α -> M)
  结论: ∏ᶠ i, f i = f default
  证明: finprod_eq_single f default fun _x hx => (hx <| Unique.eq_default _).elim

@[to_additive (attr := simp)]

Depends on / 依赖: Unique, Unique.eq_default, eq_default, finprod_eq_single
-/
theorem finprod_unique [Unique α] (f : α -> M) : ∏ᶠ i, f i = f default :=
  finprod_eq_single f default fun _x hx => (hx <| Unique.eq_default _).elim

@[to_additive (attr := simp)]
/--
theorem `finprod_true` / 定理 `finprod_true`

English:
theorem finprod_true
  given: (f : True -> M)
  statement: ∏ᶠ i, f i = f trivial
  proof: @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f

@[to_additive]

中文:
定理 finprod_true
  条件: (f : True -> M)
  结论: ∏ᶠ i, f i = f trivial
  证明: @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f

@[to_additive]

Depends on / 依赖: finprod_unique
-/
theorem finprod_true (f : True -> M) : ∏ᶠ i, f i = f trivial :=
  @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f

@[to_additive]
/--
theorem `finprod_eq_dif` / 定理 `finprod_eq_dif`

English:
theorem finprod_eq_dif
  given: {p : Prop} [Decidable p] (f : p -> M)
  proof: by
  split_ifs with h
  · have : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · have : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f

@[to_additive]

中文:
定理 finprod_eq_dif
  条件: {p : 命题} [Decidable p] (f : p -> M)
  证明: by
  split_ifs with h
  · have : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · have : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f

@[to_additive]

Depends on / 依赖: IsEmpty, Unique, finprod_of_isEmpty, finprod_unique, split_ifs
-/
theorem finprod_eq_dif {p : Prop} [Decidable p] (f : p -> M) :
    ∏ᶠ i, f i = if h : p then f h else 1 := by
  split_ifs with h
  · have : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · have : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f

@[to_additive]
/--
theorem `finprod_eq_if` / 定理 `finprod_eq_if`

English:
theorem finprod_eq_if
  given: {p : Prop} [Decidable p] {x : M}
  statement: ∏ᶠ _ : p, x = if p then x else 1
  proof: finprod_eq_dif fun _ => x

@[to_additive]

中文:
定理 finprod_eq_if
  条件: {p : 命题} [Decidable p] {x : M}
  结论: ∏ᶠ _ : p, x = if p then x else 1
  证明: finprod_eq_dif fun _ => x

@[to_additive]

Depends on / 依赖: finprod_eq_dif
-/
theorem finprod_eq_if {p : Prop} [Decidable p] {x : M} : ∏ᶠ _ : p, x = if p then x else 1 :=
  finprod_eq_dif fun _ => x

@[to_additive]
/--
theorem `finprod_congr` / 定理 `finprod_congr`

English:
theorem finprod_congr
  given: {f g : α -> M} (h : forall x, f x = g x)
  statement: finprod f = finprod g
  proof: congr_arg _ funext h

@[to_additive (attr := congr)]

中文:
定理 finprod_congr
  条件: {f g : α -> M} (h : 对任意 x, f x = g x)
  结论: finprod f = finprod g
  证明: congr_arg _ funext h

@[to_additive (attr := congr)]

Depends on / 依赖: congr_arg
-/
theorem finprod_congr {f g : α -> M} (h : forall x, f x = g x) : finprod f = finprod g :=
congr_arg _ funext h

@[to_additive (attr := congr)]
/--
theorem `finprod_congr_Prop` / 定理 `finprod_congr_Prop`

English:
theorem finprod_congr_Prop
  statement: {p q : Prop} {f : p -> M} {g : q -> M} (hpq : p = q)
  proof: by
  subst q
  exact finprod_congr hfg

中文:
定理 finprod_congr_Prop
  结论: {p q : 命题} {f : p -> M} {g : q -> M} (hpq : p = q)
  证明: by
  subst q
  exact finprod_congr hfg

Depends on / 依赖: finprod_congr
-/
theorem finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q -> M} (hpq : p = q)
    (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finprod g := by
  subst q
  exact finprod_congr hfg

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on the factors. -/
@[to_additive
      /-- To prove a property of a finite sum, it suffices to prove that the property is
      additive and holds on the summands. -/]
/--
theorem `finprod_induction` / 定理 `finprod_induction`

English:
theorem finprod_induction
  statement: {f : α -> M} (p : M -> Prop) (hp₀ : p 1)
  proof: by
  rw [finprod]
  split_ifs
  exacts [Finset.prod_induction _ _ hp₁ hp₀ fun i _ => hp₂ _, hp₀]

中文:
定理 finprod_induction
  结论: {f : α -> M} (p : M -> 命题) (hp₀ : p 1)
  证明: by
  rw [finprod]
  split_ifs
  exacts [Finset.prod_induction _ _ hp₁ hp₀ fun i _ => hp₂ _, hp₀]

Depends on / 依赖: Finset, Finset.prod_induction, exacts, finprod, prod_induction, split_ifs
-/
theorem finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ : p 1)
    (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p (∏ᶠ i, f i) := by
  rw [finprod]
  split_ifs
  exacts [Finset.prod_induction _ _ hp₁ hp₀ fun i _ => hp₂ _, hp₀]

/--
theorem `finprod_nonneg` / 定理 `finprod_nonneg`

English:
theorem finprod_nonneg
  statement: {R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
  proof: finprod_induction (fun x => 0 <= x) zero_le_one (fun _ _ => mul_nonneg) hf

@[to_additive finsum_nonneg]

中文:
定理 finprod_nonneg
  结论: {R : 类型} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
  证明: finprod_induction (fun x => 0 <= x) zero_le_one (fun _ _ => mul_nonneg) hf

@[to_additive finsum_nonneg]

Depends on / 依赖: finprod_induction, mul_nonneg, zero_le_one
-/
theorem finprod_nonneg {R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : α -> R} (hf : forall x, 0 <= f x) :
    0 <= ∏ᶠ x, f x :=
  finprod_induction (fun x => 0 <= x) zero_le_one (fun _ _ => mul_nonneg) hf

@[to_additive finsum_nonneg]
/--
theorem `one_le_finprod'` / 定理 `one_le_finprod'`

English:
theorem one_le_finprod'
  statement: {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
  proof: finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

中文:
定理 one_le_finprod'
  结论: {M : 类型} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
  证明: finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

Depends on / 依赖: finprod_induction, le_rfl, one_le_mul
-/
theorem one_le_finprod' {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    {f : α -> M} (hf : forall i, 1 <= f i) :
    1 <= ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

/--
lemma `one_le_finprod` / 引理 `one_le_finprod`

English:
lemma one_le_finprod
  statement: {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
  proof: finprod_induction _ le_rfl (fun _ _ => one_le_mul_of_one_le_of_one_le) hf

@[to_additive]

中文:
引理 one_le_finprod
  结论: {M : 类型} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
  证明: finprod_induction _ le_rfl (fun _ _ => one_le_mul_of_one_le_of_one_le) hf

@[to_additive]

Depends on / 依赖: finprod_induction, le_rfl, one_le_mul_of_one_le_of_one_le
-/
lemma one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
    [PosMulMono M] {f : α -> M} (hf : forall i, 1 <= f i) :
    1 <= ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul_of_one_le_of_one_le) hf

@[to_additive]
/--
theorem `MonoidHom.map_finprod_plift` / 定理 `MonoidHom.map_finprod_plift`

English:
theorem MonoidHom.map_finprod_plift
  statement: (f : M ->* N) (g : α -> M)
  proof: by
  rw [finprod_eq_prod_plift_of_mulSupport_subset h.coe_toFinset.ge]; rw [finprod_eq_prod_plift_of_mulSupport_subset]; rw [_root_.map_prod]
  rw [h.coe_toFinset]
  exact mulSupport_comp_subset f.map_one (g ∘ PLift.down)

@[to_additive]

中文:
定理 MonoidHom.map_finprod_plift
  结论: (f : M ->* N) (g : α -> M)
  证明: by
  rw [finprod_eq_prod_plift_of_mulSupport_subset h.coe_toFinset.ge]; rw [finprod_eq_prod_plift_of_mulSupport_subset]; rw [_root_.map_prod]
  rw [h.coe_toFinset]
  exact mulSupport_comp_subset f.map_one (g ∘ PLift.down)

@[to_additive]

Depends on / 依赖: PLift.down, _root_, _root_.map_prod, coe_toFinset, f.map_one, finprod_eq_prod_plift_of_mulSupport_subset, h.coe_toFinset, h.coe_toFinset.ge, map_one, map_prod, mulSupport_comp_subset
-/
theorem MonoidHom.map_finprod_plift (f : M ->* N) (g : α -> M)
    (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) := by
  rw [finprod_eq_prod_plift_of_mulSupport_subset h.coe_toFinset.ge]; rw [finprod_eq_prod_plift_of_mulSupport_subset]; rw [_root_.map_prod]
  rw [h.coe_toFinset]
  exact mulSupport_comp_subset f.map_one (g ∘ PLift.down)

@[to_additive]
/--
theorem `MonoidHom.map_finprod_Prop` / 定理 `MonoidHom.map_finprod_Prop`

English:
theorem MonoidHom.map_finprod_Prop
  given: {p : Prop} (f : M ->* N) (g : p -> M)
  proof: f.map_finprod_plift g (Set.toFinite _)

@[to_additive]

中文:
定理 MonoidHom.map_finprod_Prop
  条件: {p : 命题} (f : M ->* N) (g : p -> M)
  证明: f.map_finprod_plift g (Set.toFinite _)

@[to_additive]

Depends on / 依赖: Set.toFinite, f.map_finprod_plift, map_finprod_plift, toFinite
-/
theorem MonoidHom.map_finprod_Prop {p : Prop} (f : M ->* N) (g : p -> M) :
    f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
  f.map_finprod_plift g (Set.toFinite _)

@[to_additive]
/--
theorem `MonoidHom.map_finprod_of_preimage_one` / 定理 `MonoidHom.map_finprod_of_preimage_one`

English:
theorem MonoidHom.map_finprod_of_preimage_one
  given: (f : M ->* N) (hf : forall x, f x = 1 -> x = 1) (g : α -> M)
  proof: by
by_cases hg : HasFiniteMulSupport g ∘ PLift.down; · exact f.map_finprod_plift g hg
  rw [finprod]; rw [dif_neg]; rw [f.map_one]; rw [finprod]; rw [dif_neg]
  exacts [Infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

@[to_additive]

中文:
定理 MonoidHom.map_finprod_of_preimage_one
  条件: (f : M ->* N) (hf : 对任意 x, f x = 1 -> x = 1) (g : α -> M)
  证明: by
by_cases hg : HasFiniteMulSupport g ∘ PLift.down; · exact f.map_finprod_plift g hg
  rw [finprod]; rw [dif_neg]; rw [f.map_one]; rw [finprod]; rw [dif_neg]
  exacts [Infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

@[to_additive]

Depends on / 依赖: HasFiniteMulSupport, Infinite, Infinite.mono, PLift.down, dif_neg, exacts, f.map_finprod_plift, f.map_one, finprod, map_finprod_plift, map_one, x.down
-/
theorem MonoidHom.map_finprod_of_preimage_one (f : M ->* N) (hf : forall x, f x = 1 -> x = 1) (g : α -> M) :
    f (∏ᶠ i, g i) = ∏ᶠ i, f (g i) := by
by_cases hg : HasFiniteMulSupport g ∘ PLift.down; · exact f.map_finprod_plift g hg
  rw [finprod]; rw [dif_neg]; rw [f.map_one]; rw [finprod]; rw [dif_neg]
  exacts [Infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

@[to_additive]
/--
theorem `MonoidHom.map_finprod_of_injective` / 定理 `MonoidHom.map_finprod_of_injective`

English:
theorem MonoidHom.map_finprod_of_injective
  given: (g : M ->* N) (hg : Injective g) (f : α -> M)
  proof: g.map_finprod_of_preimage_one (fun _ => (hg.eq_iff' g.map_one).mp) f

@[to_additive]

中文:
定理 MonoidHom.map_finprod_of_injective
  条件: (g : M ->* N) (hg : Injective g) (f : α -> M)
  证明: g.map_finprod_of_preimage_one (fun _ => (hg.eq_iff' g.map_one).mp) f

@[to_additive]

Depends on / 依赖: eq_iff, g.map_finprod_of_preimage_one, g.map_one, hg.eq_iff, map_finprod_of_preimage_one, map_one
-/
theorem MonoidHom.map_finprod_of_injective (g : M ->* N) (hg : Injective g) (f : α -> M) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_of_preimage_one (fun _ => (hg.eq_iff' g.map_one).mp) f

@[to_additive]
/--
theorem `MulEquiv.map_finprod` / 定理 `MulEquiv.map_finprod`

English:
theorem MulEquiv.map_finprod
  given: (g : M ≃* N) (f : α -> M)
  statement: g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
  proof: g.toMonoidHom.map_finprod_of_injective (EquivLike.injective g) f

@[to_additive]

中文:
定理 MulEquiv.map_finprod
  条件: (g : M ≃* N) (f : α -> M)
  结论: g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
  证明: g.toMonoidHom.map_finprod_of_injective (EquivLike.injective g) f

@[to_additive]

Depends on / 依赖: EquivLike, EquivLike.injective, g.toMonoidHom.map_finprod_of_injective, injective, map_finprod_of_injective, toMonoidHom
-/
theorem MulEquiv.map_finprod (g : M ≃* N) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.toMonoidHom.map_finprod_of_injective (EquivLike.injective g) f

@[to_additive]
/--
theorem `MulEquivClass.map_finprod` / 定理 `MulEquivClass.map_finprod`

English:
theorem MulEquivClass.map_finprod
  statement: {F : Type*} [EquivLike F M N] [MulEquivClass F M N] (g : F)
  proof: MulEquiv.map_finprod (MulEquivClass.toMulEquiv g) f

中文:
定理 MulEquivClass.map_finprod
  结论: {F : 类型} [EquivLike F M N] [MulEquivClass F M N] (g : F)
  证明: MulEquiv.map_finprod (MulEquivClass.toMulEquiv g) f

Depends on / 依赖: MulEquiv, MulEquiv.map_finprod, MulEquivClass, MulEquivClass.toMulEquiv, map_finprod, toMulEquiv
-/
theorem MulEquivClass.map_finprod {F : Type*} [EquivLike F M N] [MulEquivClass F M N] (g : F)
    (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  MulEquiv.map_finprod (MulEquivClass.toMulEquiv g) f

/--
theorem `finsum_smul` / 定理 `finsum_smul`

English:
theorem finsum_smul
  statement: {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

中文:
定理 finsum_smul
  结论: {R M : 类型} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

Depends on / 依赖: eq_or_ne, map_finsum_of_injective, smulAddHom, smul_left_injective
-/
theorem finsum_smul {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (f : ι -> R) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

/--
theorem `smul_finsum` / 定理 `smul_finsum`

English:
theorem smul_finsum
  statement: {R M : Type*} [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M]
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
  · exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

@[to_additive]

中文:
定理 smul_finsum
  结论: {R M : 类型} [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M]
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
  · exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

@[to_additive]

Depends on / 依赖: eq_or_ne, map_finsum_of_injective, smulAddHom, smul_right_injective
-/
theorem smul_finsum {R M : Type*} [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (f : ι -> M) : c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
  · exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

@[to_additive]
/--
theorem `finprod_inv_distrib` / 定理 `finprod_inv_distrib`

English:
theorem finprod_inv_distrib
  given: [DivisionCommMonoid G] (f : α -> G)
  statement: (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹
  proof: ((MulEquiv.inv G).map_finprod f).symm

中文:
定理 finprod_inv_distrib
  条件: [DivisionCommMonoid G] (f : α -> G)
  结论: (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹
  证明: ((MulEquiv.inv G).map_finprod f).symm

Depends on / 依赖: MulEquiv, MulEquiv.inv, map_finprod
-/
theorem finprod_inv_distrib [DivisionCommMonoid G] (f : α -> G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod f).symm

end sort

section type

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

@[to_additive]
/--
theorem `finprod_eq_mulIndicator_apply` / 定理 `finprod_eq_mulIndicator_apply`

English:
theorem finprod_eq_mulIndicator_apply
  given: (s : Set α) (f : α -> M) (a : α)
  proof: by
  convert! finprod_eq_if (M := M) (p := a in s) (x := f a)

@[to_additive (attr := simp)]

中文:
定理 finprod_eq_mulIndicator_apply
  条件: (s : Set α) (f : α -> M) (a : α)
  证明: by
  convert! finprod_eq_if (M := M) (p := a in s) (x := f a)

@[to_additive (attr := simp)]

Depends on / 依赖: convert, finprod_eq_if
-/
theorem finprod_eq_mulIndicator_apply (s : Set α) (f : α -> M) (a : α) :
    ∏ᶠ _ : a in s, f a = mulIndicator s f a := by
  convert! finprod_eq_if (M := M) (p := a in s) (x := f a)

@[to_additive (attr := simp)]
/--
theorem `finprod_apply_ne_one` / 定理 `finprod_apply_ne_one`

English:
theorem finprod_apply_ne_one
  given: (f : α -> M) (a : α)
  statement: ∏ᶠ _ : f a != 1, f a = f a
  proof: by
  rw [← mem_mulSupport]; rw [finprod_eq_mulIndicator_apply]; rw [mulIndicator_mulSupport]

@[to_additive]

中文:
定理 finprod_apply_ne_one
  条件: (f : α -> M) (a : α)
  结论: ∏ᶠ _ : f a != 1, f a = f a
  证明: by
  rw [← mem_mulSupport]; rw [finprod_eq_mulIndicator_apply]; rw [mulIndicator_mulSupport]

@[to_additive]

Depends on / 依赖: finprod_eq_mulIndicator_apply, mem_mulSupport, mulIndicator_mulSupport
-/
theorem finprod_apply_ne_one (f : α -> M) (a : α) : ∏ᶠ _ : f a != 1, f a = f a := by
  rw [← mem_mulSupport]; rw [finprod_eq_mulIndicator_apply]; rw [mulIndicator_mulSupport]

@[to_additive]
/--
theorem `finprod_mem_def` / 定理 `finprod_mem_def`

English:
theorem finprod_mem_def
  given: (s : Set α) (f : α -> M)
  statement: ∏ᶠ a in s, f a = ∏ᶠ a, mulIndicator s f a
  proof: finprod_congr finprod_eq_mulIndicator_apply s f

@[to_additive]

中文:
定理 finprod_mem_def
  条件: (s : Set α) (f : α -> M)
  结论: ∏ᶠ a in s, f a = ∏ᶠ a, mulIndicator s f a
  证明: finprod_congr finprod_eq_mulIndicator_apply s f

@[to_additive]

Depends on / 依赖: finprod_congr, finprod_eq_mulIndicator_apply
-/
theorem finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f a = ∏ᶠ a, mulIndicator s f a :=
finprod_congr finprod_eq_mulIndicator_apply s f

@[to_additive]
/--
lemma `finprod_mem_mulSupport` / 引理 `finprod_mem_mulSupport`

English:
lemma finprod_mem_mulSupport
  given: (f : α -> M)
  statement: ∏ᶠ a in mulSupport f, f a = ∏ᶠ a, f a
  proof: by
  rw [finprod_mem_def]; rw [mulIndicator_mulSupport]

@[to_additive]

中文:
引理 finprod_mem_mulSupport
  条件: (f : α -> M)
  结论: ∏ᶠ a in mulSupport f, f a = ∏ᶠ a, f a
  证明: by
  rw [finprod_mem_def]; rw [mulIndicator_mulSupport]

@[to_additive]

Depends on / 依赖: finprod_mem_def, mulIndicator_mulSupport
-/
lemma finprod_mem_mulSupport (f : α -> M) : ∏ᶠ a in mulSupport f, f a = ∏ᶠ a, f a := by
  rw [finprod_mem_def]; rw [mulIndicator_mulSupport]

@[to_additive]
/--
theorem `finprod_eq_prod_of_mulSupport_subset` / 定理 `finprod_eq_prod_of_mulSupport_subset`

English:
theorem finprod_eq_prod_of_mulSupport_subset
  given: (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s)
  proof: by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage_symm _).symm
  have : mulSupport (f ∘ PLift.down) subseteq s.map Equiv.plift.symm.toEmbedding := by
    rw [A]; rw [Finset.coe_map]
  

中文:
定理 finprod_eq_prod_of_mulSupport_subset
  条件: (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s)
  证明: by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage_symm _).symm
  have : mulSupport (f ∘ PLift.down) subseteq s.map Equiv.plift.symm.toEmbedding := by
    rw [A]; rw [Finset.coe_map]
  

Depends on / 依赖: Equiv.coe_toEmbedding, Equiv.plift.symm, Equiv.plift.symm.image_eq_preimage_symm, Equiv.plift.symm.toEmbedding, Finset, Finset.coe_map, Finset.prod_map, PLift.down, coe_map, coe_toEmbedding, finprod_eq_prod_plift_of_mulSupport_subset, image_eq_preimage_symm, image_mono, mulSupport, mulSupport_comp_eq_preimage, prod_map, s.map, subseteq, toEmbedding
-/
theorem finprod_eq_prod_of_mulSupport_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) :
    ∏ᶠ i, f i = ∏ i in s, f i := by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage_symm _).symm
  have : mulSupport (f ∘ PLift.down) subseteq s.map Equiv.plift.symm.toEmbedding := by
    rw [A]; rw [Finset.coe_map]
    exact image_mono h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]
  simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  congr

@[to_additive]
/--
theorem `finprod_eq_prod_of_mulSupport_toFinset_subset` / 定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`

English:
theorem finprod_eq_prod_of_mulSupport_toFinset_subset
  statement: (f : α -> M) (hf : HasFiniteMulSupport f)
  proof: finprod_eq_prod_of_mulSupport_subset _ fun _ hx => h hf.mem_toFinset.2 hx

@[to_additive]

中文:
定理 finprod_eq_prod_of_mulSupport_toFinset_subset
  结论: (f : α -> M) (hf : HasFiniteMulSupport f)
  证明: finprod_eq_prod_of_mulSupport_subset _ fun _ hx => h hf.mem_toFinset.2 hx

@[to_additive]

Depends on / 依赖: finprod_eq_prod_of_mulSupport_subset, hf.mem_toFinset, mem_toFinset
-/
theorem finprod_eq_prod_of_mulSupport_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f)
    {s : Finset α} (h : hf.toFinset subseteq s) : ∏ᶠ i, f i = ∏ i in s, f i :=
finprod_eq_prod_of_mulSupport_subset _ fun _ hx => h hf.mem_toFinset.2 hx

@[to_additive]
/--
theorem `finprod_eq_prod_of_mulSupport_subset_of_finite` / 定理 `finprod_eq_prod_of_mulSupport_subset_of_finite`

English:
theorem finprod_eq_prod_of_mulSupport_subset_of_finite
  statement: (f : α -> M) {s : Set α}
  proof: finprod_eq_prod_of_mulSupport_subset f by rwa [Set.Finite.coe_toFinset]

@[to_additive]

中文:
定理 finprod_eq_prod_of_mulSupport_subset_of_finite
  结论: (f : α -> M) {s : Set α}
  证明: finprod_eq_prod_of_mulSupport_subset f by rwa [Set.Finite.coe_toFinset]

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.coe_toFinset, coe_toFinset, finprod_eq_prod_of_mulSupport_subset
-/
theorem finprod_eq_prod_of_mulSupport_subset_of_finite (f : α -> M) {s : Set α}
    (h : mulSupport f subseteq s) (hs : s.Finite) : ∏ᶠ i, f i = ∏ i in hs.toFinset, f i :=
finprod_eq_prod_of_mulSupport_subset f by rwa [Set.Finite.coe_toFinset]

@[to_additive]
/--
theorem `finprod_eq_finsetProd_of_mulSupport_subset` / 定理 `finprod_eq_finsetProd_of_mulSupport_subset`

English:
theorem finprod_eq_finsetProd_of_mulSupport_subset
  statement: (f : α -> M) {s : Finset α}
  proof: haveI h' : (s.finite_toSet.subset h).toFinset subseteq s := by
    simpa [← Finset.coe_subset, Set.coe_toFinset]
  finprod_eq_prod_of_mulSupport_toFinset_subset _ _ h'

@[deprecated (since := "2026-04-08")]
alias finsum_eq_finset_sum_of_support_subset := finsum_eq_finsetSum_of_support_subset

@[to_a

中文:
定理 finprod_eq_finsetProd_of_mulSupport_subset
  结论: (f : α -> M) {s : Finset α}
  证明: haveI h' : (s.finite_toSet.subset h).toFinset subseteq s := by
    simpa [← Finset.coe_subset, Set.coe_toFinset]
  finprod_eq_prod_of_mulSupport_toFinset_subset _ _ h'

@[deprecated (since := "2026-04-08")]
alias finsum_eq_finset_sum_of_support_subset := finsum_eq_finsetSum_of_support_subset

@[to_a

Depends on / 依赖: Finset, Finset.coe_subset, Set.coe_toFinset, coe_subset, coe_toFinset, finite_toSet, finprod_eq_prod_of_mulSupport_toFinset_subset, s.finite_toSet.subset, subset, subseteq, toFinset
-/
theorem finprod_eq_finsetProd_of_mulSupport_subset (f : α -> M) {s : Finset α}
    (h : mulSupport f subseteq (s : Set α)) : ∏ᶠ i, f i = ∏ i in s, f i :=
  haveI h' : (s.finite_toSet.subset h).toFinset subseteq s := by
    simpa [← Finset.coe_subset, Set.coe_toFinset]
  finprod_eq_prod_of_mulSupport_toFinset_subset _ _ h'

@[deprecated (since := "2026-04-08")]
alias finsum_eq_finset_sum_of_support_subset := finsum_eq_finsetSum_of_support_subset

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finprod_eq_finset_prod_of_mulSupport_subset := finprod_eq_finsetProd_of_mulSupport_subset

@[to_additive]
/--
theorem `finprod_def` / 定理 `finprod_def`

English:
theorem finprod_def
  given: (f : α -> M) [Decidable (HasFiniteMulSupport f)]
  proof: by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [HasFiniteMulSupport]; rw [mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h

中文:
定理 finprod_def
  条件: (f : α -> M) [Decidable (HasFiniteMulSupport f)]
  证明: by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [HasFiniteMulSupport]; rw [mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h

Depends on / 依赖: Equiv.plift.surjective, Finset, Finset.Subset.refl, HasFiniteMulSupport, Subset, dif_neg, finprod, finprod_eq_prod_of_mulSupport_toFinset_subset, hf.of_preimage, mulSupport_comp_eq_preimage, of_preimage, split_ifs, surjective
-/
theorem finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)] :
    ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i else 1 := by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [HasFiniteMulSupport]; rw [mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `finprod_of_infinite_mulSupport` / 定理 `finprod_of_infinite_mulSupport`

English:
theorem finprod_of_infinite_mulSupport
  given: {f : α -> M} (hf : (mulSupport f).Infinite)
  proof: by
  classical
  rw [finprod_def]
  simp only [HasFiniteMulSupport]
  rw [dif_neg hf]

@[to_additive]

中文:
定理 finprod_of_infinite_mulSupport
  条件: {f : α -> M} (hf : (mulSupport f).Infinite)
  证明: by
  classical
  rw [finprod_def]
  simp only [HasFiniteMulSupport]
  rw [dif_neg hf]

@[to_additive]

Depends on / 依赖: HasFiniteMulSupport, classical, dif_neg, finprod_def
-/
theorem finprod_of_infinite_mulSupport {f : α -> M} (hf : (mulSupport f).Infinite) :
    ∏ᶠ i, f i = 1 := by
  classical
  rw [finprod_def]
  simp only [HasFiniteMulSupport]
  rw [dif_neg hf]

@[to_additive]
/--
theorem `finprod_of_not_hasFiniteMulSupport` / 定理 `finprod_of_not_hasFiniteMulSupport`

English:
theorem finprod_of_not_hasFiniteMulSupport
  given: {f : α -> M} (hf : ¬ f.HasFiniteMulSupport)
  proof: finprod_of_infinite_mulSupport Set.not_finite.mp hf

@[to_additive]

中文:
定理 finprod_of_not_hasFiniteMulSupport
  条件: {f : α -> M} (hf : ¬ f.HasFiniteMulSupport)
  证明: finprod_of_infinite_mulSupport Set.not_finite.mp hf

@[to_additive]

Depends on / 依赖: Set.not_finite.mp, finprod_of_infinite_mulSupport, not_finite
-/
theorem finprod_of_not_hasFiniteMulSupport {f : α -> M} (hf : ¬ f.HasFiniteMulSupport) :
    ∏ᶠ i, f i = 1 :=
finprod_of_infinite_mulSupport Set.not_finite.mp hf

@[to_additive]
/--
theorem `hasFiniteMulSupport_of_finprod_ne_one` / 定理 `hasFiniteMulSupport_of_finprod_ne_one`

English:
theorem hasFiniteMulSupport_of_finprod_ne_one
  given: {f : α -> M} (h : ∏ᶠ i, f i != 1)
  proof: not_infinite.mp (finprod_of_infinite_mulSupport ·).mt h

@[deprecated (since := "2026-03-03")] alias
  finite_mulSupport_of_finprod_ne_one := hasFiniteMulSupport_of_finprod_ne_one

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_ne_zero := hasFiniteSupport_of_finsum_ne_zero

中文:
定理 hasFiniteMulSupport_of_finprod_ne_one
  条件: {f : α -> M} (h : ∏ᶠ i, f i != 1)
  证明: not_infinite.mp (finprod_of_infinite_mulSupport ·).mt h

@[deprecated (since := "2026-03-03")] alias
  finite_mulSupport_of_finprod_ne_one := hasFiniteMulSupport_of_finprod_ne_one

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_ne_zero := hasFiniteSupport_of_finsum_ne_zero

Depends on / 依赖: finprod_of_infinite_mulSupport, not_infinite, not_infinite.mp
-/
theorem hasFiniteMulSupport_of_finprod_ne_one {f : α -> M} (h : ∏ᶠ i, f i != 1) :
    HasFiniteMulSupport f :=
not_infinite.mp (finprod_of_infinite_mulSupport ·).mt h

@[deprecated (since := "2026-03-03")] alias
  finite_mulSupport_of_finprod_ne_one := hasFiniteMulSupport_of_finprod_ne_one

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_ne_zero := hasFiniteSupport_of_finsum_ne_zero

/--
theorem `hasFiniteSupport_of_finsum_eq_one` / 定理 `hasFiniteSupport_of_finsum_eq_one`

English:
theorem hasFiniteSupport_of_finsum_eq_one
  statement: {R : Type*} [NonAssocSemiring R] {f : α -> R}
  proof: by
  cases subsingleton_or_nontrivial R
  · simp_rw [HasFiniteSupport, Subsingleton.support_eq, finite_empty]
  · apply hasFiniteSupport_of_finsum_ne_zero
    rw [h]
    exact one_ne_zero

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_eq_one := hasFiniteSupport_of_finsum_eq_

中文:
定理 hasFiniteSupport_of_finsum_eq_one
  结论: {R : 类型} [NonAssocSemiring R] {f : α -> R}
  证明: by
  cases subsingleton_or_nontrivial R
  · simp_rw [HasFiniteSupport, Subsingleton.support_eq, finite_empty]
  · apply hasFiniteSupport_of_finsum_ne_zero
    rw [h]
    exact one_ne_zero

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_eq_one := hasFiniteSupport_of_finsum_eq_

Depends on / 依赖: HasFiniteSupport, Subsingleton, Subsingleton.support_eq, finite_empty, hasFiniteSupport_of_finsum_ne_zero, one_ne_zero, simp_rw, subsingleton_or_nontrivial, support_eq
-/
theorem hasFiniteSupport_of_finsum_eq_one {R : Type*} [NonAssocSemiring R] {f : α -> R}
    (h : ∑ᶠ i, f i = 1) : HasFiniteSupport f := by
  cases subsingleton_or_nontrivial R
  · simp_rw [HasFiniteSupport, Subsingleton.support_eq, finite_empty]
  · apply hasFiniteSupport_of_finsum_ne_zero
    rw [h]
    exact one_ne_zero

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_eq_one := hasFiniteSupport_of_finsum_eq_one

@[to_additive]
/--
theorem `finprod_eq_prod` / 定理 `finprod_eq_prod`

English:
theorem finprod_eq_prod
  given: (f : α -> M) (hf : HasFiniteMulSupport f)
  proof: by classical rw [finprod_def, dif_pos hf]

@[to_additive]

中文:
定理 finprod_eq_prod
  条件: (f : α -> M) (hf : HasFiniteMulSupport f)
  证明: by classical rw [finprod_def, dif_pos hf]

@[to_additive]

Depends on / 依赖: classical, dif_pos, finprod_def
-/
theorem finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i := by classical rw [finprod_def, dif_pos hf]

@[to_additive]
/--
theorem `finprod_eq_prod_of_fintype` / 定理 `finprod_eq_prod_of_fintype`

English:
theorem finprod_eq_prod_of_fintype
  given: [Fintype α] (f : α -> M)
  statement: ∏ᶠ i : α, f i = ∏ i, f i
  proof: finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) Finset.subset_univ _

中文:
定理 finprod_eq_prod_of_fintype
  条件: [Fintype α] (f : α -> M)
  结论: ∏ᶠ i : α, f i = ∏ i, f i
  证明: finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) Finset.subset_univ _

Depends on / 依赖: Finset, Finset.subset_univ, Set.toFinite, finprod_eq_prod_of_mulSupport_toFinset_subset, subset_univ, toFinite
-/
theorem finprod_eq_prod_of_fintype [Fintype α] (f : α -> M) : ∏ᶠ i : α, f i = ∏ i, f i :=
finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) Finset.subset_univ _

/--
theorem `finprod_ne_zero` / 定理 `finprod_ne_zero`

English:
theorem finprod_ne_zero
  statement: {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  proof: by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

中文:
定理 finprod_ne_zero
  结论: {M₀ : 类型} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  证明: by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

Depends on / 依赖: Finite, Finset, Finset.prod_ne_zero_iff, Set.Finite, f.mulSupport, finprod_eq_prod, finprod_of_infinite_mulSupport, mulSupport, prod_ne_zero_iff
-/
theorem finprod_ne_zero {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    {f : α -> M₀} (h : forall i, f i != 0) :
    ∏ᶠ i, f i != 0 := by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

/--
theorem `finprod_apply_ne_zero` / 定理 `finprod_apply_ne_zero`

English:
theorem finprod_apply_ne_zero
  statement: {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀]
  proof: by
  by_cases h₂ : f.mulSupport.Finite
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

@[to_additive]

中文:
定理 finprod_apply_ne_zero
  结论: {ι : 类型} {N₀ M₀ : 类型} [CommMonoidWithZero M₀] [Nontrivial M₀]
  证明: by
  by_cases h₂ : f.mulSupport.Finite
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

@[to_additive]

Depends on / 依赖: Finite, Finset, Finset.prod_apply, Finset.prod_ne_zero_iff, f.mulSupport.Finite, finprod_eq_prod, finprod_of_infinite_mulSupport, mulSupport, prod_apply, prod_ne_zero_iff
-/
theorem finprod_apply_ne_zero {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀]
    [NoZeroDivisors M₀] {n : N₀} {f : ι -> N₀ -> M₀} (h : forall i, f i n != 0) :
    (∏ᶠ i, f i) n != 0 := by
  by_cases h₂ : f.mulSupport.Finite
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

@[to_additive]
/--
theorem `map_finsetProd` / 定理 `map_finsetProd`

English:
theorem map_finsetProd
  statement: {α F : Type*} [Fintype α] [EquivLike F M N] [MulEquivClass F M N] (f : F)
  proof: by
  simp [← finprod_eq_prod_of_fintype, MulEquivClass.map_finprod]

@[deprecated (since := "2026-04-08")] alias map_finset_sum := map_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias map_finset_prod := map_finsetProd

@[to_additive]

中文:
定理 map_finsetProd
  结论: {α F : 类型} [Fintype α] [EquivLike F M N] [MulEquivClass F M N] (f : F)
  证明: by
  simp [← finprod_eq_prod_of_fintype, MulEquivClass.map_finprod]

@[deprecated (since := "2026-04-08")] alias map_finset_sum := map_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias map_finset_prod := map_finsetProd

@[to_additive]

Depends on / 依赖: MulEquivClass, MulEquivClass.map_finprod, finprod_eq_prod_of_fintype, map_finprod
-/
theorem map_finsetProd {α F : Type*} [Fintype α] [EquivLike F M N] [MulEquivClass F M N] (f : F)
    (g : α -> M) : f (∏ i : α, g i) = ∏ i : α, f (g i) := by
  simp [← finprod_eq_prod_of_fintype, MulEquivClass.map_finprod]

@[deprecated (since := "2026-04-08")] alias map_finset_sum := map_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias map_finset_prod := map_finsetProd

@[to_additive]
/--
theorem `finprod_cond_eq_prod_of_cond_iff` / 定理 `finprod_cond_eq_prod_of_cond_iff`

English:
theorem finprod_cond_eq_prod_of_cond_iff
  statement: (f : α -> M) {p : α -> Prop} {t : Finset α}
  proof: by
  set s := { x | p x }
  change ∏ᶠ (i : α) (_ : i in s), f i = ∏ i in t, f i
  have : mulSupport (s.mulIndicator f) subseteq t := by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  rw [finprod_mem_def]; rw [finprod_eq_prod_of_mulSupport_subset _ this]
  refine Fins

中文:
定理 finprod_cond_eq_prod_of_cond_iff
  结论: (f : α -> M) {p : α -> 命题} {t : Finset α}
  证明: by
  set s := { x | p x }
  change ∏ᶠ (i : α) (_ : i in s), f i = ∏ i in t, f i
  have : mulSupport (s.mulIndicator f) subseteq t := by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  rw [finprod_mem_def]; rw [finprod_eq_prod_of_mulSupport_subset _ this]
  refine Fins

Depends on / 依赖: Finset, Finset.prod_congr, Set.mulSupport_mulIndicator, contrapose, finprod_eq_prod_of_mulSupport_subset, finprod_mem_def, mulIndicator, mulIndicator_apply_eq_self, mulSupport, mulSupport_mulIndicator, prod_congr, s.mulIndicator, subseteq
-/
theorem finprod_cond_eq_prod_of_cond_iff (f : α -> M) {p : α -> Prop} {t : Finset α}
    (h : forall {x}, f x != 1 -> (p x ↔ x in t)) : (∏ᶠ (i) (_ : p i), f i) = ∏ i in t, f i := by
  set s := { x | p x }
  change ∏ᶠ (i : α) (_ : i in s), f i = ∏ i in t, f i
  have : mulSupport (s.mulIndicator f) subseteq t := by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  rw [finprod_mem_def]; rw [finprod_eq_prod_of_mulSupport_subset _ this]
  refine Finset.prod_congr rfl fun x hx => mulIndicator_apply_eq_self.2 fun hxs => ?_
  contrapose! hxs
  exact (h hxs).2 hx

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `finprod_cond_ne` / 定理 `finprod_cond_ne`

English:
theorem finprod_cond_ne
  given: (f : α -> M) (a : α) [DecidableEq α] (hf : HasFiniteMulSupport f)
  proof: by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase]; rw [Finite.mem_toFinset]; rw [mem_mulSupport]
  grind

@[to_additive]

中文:
定理 finprod_cond_ne
  条件: (f : α -> M) (a : α) [DecidableEq α] (hf : HasFiniteMulSupport f)
  证明: by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase]; rw [Finite.mem_toFinset]; rw [mem_mulSupport]
  grind

@[to_additive]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.mem_erase, finprod_cond_eq_prod_of_cond_iff, mem_erase, mem_mulSupport, mem_toFinset
-/
theorem finprod_cond_ne (f : α -> M) (a : α) [DecidableEq α] (hf : HasFiniteMulSupport f) :
    (∏ᶠ (i) (_ : i != a), f i) = ∏ i in hf.toFinset.erase a, f i := by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase]; rw [Finite.mem_toFinset]; rw [mem_mulSupport]
  grind

@[to_additive]
/--
theorem `finprod_mem_eq_prod_of_inter_mulSupport_eq` / 定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`

English:
theorem finprod_mem_eq_prod_of_inter_mulSupport_eq
  statement: (f : α -> M) {s : Set α} {t : Finset α}
  proof: finprod_cond_eq_prod_of_cond_iff _ by
    intro x hxf
    rw [← mem_mulSupport] at hxf
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ((mem_inter_iff x t (mulSupport f)).mp ?_).1
      rw [← Set.ext_iff.mp h x]; rw [mem_inter_iff]
      exact ⟨hx, hxf⟩
    · refine ((mem_inter_iff x s (mulSupp

中文:
定理 finprod_mem_eq_prod_of_inter_mulSupport_eq
  结论: (f : α -> M) {s : Set α} {t : Finset α}
  证明: finprod_cond_eq_prod_of_cond_iff _ by
    intro x hxf
    rw [← mem_mulSupport] at hxf
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ((mem_inter_iff x t (mulSupport f)).mp ?_).1
      rw [← Set.ext_iff.mp h x]; rw [mem_inter_iff]
      exact ⟨hx, hxf⟩
    · refine ((mem_inter_iff x s (mulSupp

Depends on / 依赖: Set.ext_iff.mp, ext_iff, finprod_cond_eq_prod_of_cond_iff, mem_inter_iff, mem_mulSupport, mulSupport
-/
theorem finprod_mem_eq_prod_of_inter_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α}
    (h : s inter mulSupport f = ↑t inter mulSupport f) : ∏ᶠ i in s, f i = ∏ i in t, f i :=
finprod_cond_eq_prod_of_cond_iff _ by
    intro x hxf
    rw [← mem_mulSupport] at hxf
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ((mem_inter_iff x t (mulSupport f)).mp ?_).1
      rw [← Set.ext_iff.mp h x]; rw [mem_inter_iff]
      exact ⟨hx, hxf⟩
    · refine ((mem_inter_iff x s (mulSupport f)).mp ?_).1
      rw [Set.ext_iff.mp h x]; rw [mem_inter_iff]
      exact ⟨hx, hxf⟩

@[to_additive]
/--
theorem `finprod_mem_eq_prod_of_subset` / 定理 `finprod_mem_eq_prod_of_subset`

English:
theorem finprod_mem_eq_prod_of_subset
  statement: (f : α -> M) {s : Set α} {t : Finset α}
  proof: finprod_cond_eq_prod_of_cond_iff _ fun hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩

@[to_additive]

中文:
定理 finprod_mem_eq_prod_of_subset
  结论: (f : α -> M) {s : Set α} {t : Finset α}
  证明: finprod_cond_eq_prod_of_cond_iff _ fun hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩

@[to_additive]

Depends on / 依赖: finprod_cond_eq_prod_of_cond_iff
-/
theorem finprod_mem_eq_prod_of_subset (f : α -> M) {s : Set α} {t : Finset α}
    (h₁ : s inter mulSupport f subseteq t) (h₂ : ↑t subseteq s) : ∏ᶠ i in s, f i = ∏ i in t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ fun hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩

@[to_additive]
/--
theorem `finprod_mem_eq_prod` / 定理 `finprod_mem_eq_prod`

English:
theorem finprod_mem_eq_prod
  given: (f : α -> M) {s : Set α} (hf : (s inter mulSupport f).Finite)
  proof: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by simp [inter_assoc]

中文:
定理 finprod_mem_eq_prod
  条件: (f : α -> M) {s : Set α} (hf : (s inter mulSupport f).Finite)
  证明: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by simp [inter_assoc]

Depends on / 依赖: finprod_mem_eq_prod_of_inter_mulSupport_eq, inter_assoc
-/
theorem finprod_mem_eq_prod (f : α -> M) {s : Set α} (hf : (s inter mulSupport f).Finite) :
    ∏ᶠ i in s, f i = ∏ i in hf.toFinset, f i :=
finprod_mem_eq_prod_of_inter_mulSupport_eq _ by simp [inter_assoc]

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `finprod_mem_eq_prod_filter` / 定理 `finprod_mem_eq_prod_filter`

English:
theorem finprod_mem_eq_prod_filter
  statement: (f : α -> M) (s : Set α) [DecidablePred (· in s)]
  proof: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by
    ext x
    simp [and_comm]

@[to_additive]

中文:
定理 finprod_mem_eq_prod_filter
  结论: (f : α -> M) (s : Set α) [DecidablePred (· in s)]
  证明: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by
    ext x
    simp [and_comm]

@[to_additive]

Depends on / 依赖: and_comm, finprod_mem_eq_prod_of_inter_mulSupport_eq
-/
theorem finprod_mem_eq_prod_filter (f : α -> M) (s : Set α) [DecidablePred (· in s)]
    (hf : HasFiniteMulSupport f) :
    ∏ᶠ i in s, f i = ∏ i in hf.toFinset with i in s, f i :=
finprod_mem_eq_prod_of_inter_mulSupport_eq _ by
    ext x
    simp [and_comm]

@[to_additive]
/--
theorem `finprod_mem_eq_toFinset_prod` / 定理 `finprod_mem_eq_toFinset_prod`

English:
theorem finprod_mem_eq_toFinset_prod
  given: (f : α -> M) (s : Set α) [Fintype s]
  proof: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by simp_rw [coe_toFinset s]

@[to_additive]

中文:
定理 finprod_mem_eq_toFinset_prod
  条件: (f : α -> M) (s : Set α) [Fintype s]
  证明: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by simp_rw [coe_toFinset s]

@[to_additive]

Depends on / 依赖: coe_toFinset, finprod_mem_eq_prod_of_inter_mulSupport_eq, simp_rw
-/
theorem finprod_mem_eq_toFinset_prod (f : α -> M) (s : Set α) [Fintype s] :
    ∏ᶠ i in s, f i = ∏ i in s.toFinset, f i :=
finprod_mem_eq_prod_of_inter_mulSupport_eq _ by simp_rw [coe_toFinset s]

@[to_additive]
/--
theorem `finprod_mem_eq_finite_toFinset_prod` / 定理 `finprod_mem_eq_finite_toFinset_prod`

English:
theorem finprod_mem_eq_finite_toFinset_prod
  given: (f : α -> M) {s : Set α} (hs : s.Finite)
  proof: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by rw [hs.coe_toFinset]

@[to_additive]

中文:
定理 finprod_mem_eq_finite_toFinset_prod
  条件: (f : α -> M) {s : Set α} (hs : s.Finite)
  证明: finprod_mem_eq_prod_of_inter_mulSupport_eq _ by rw [hs.coe_toFinset]

@[to_additive]

Depends on / 依赖: coe_toFinset, finprod_mem_eq_prod_of_inter_mulSupport_eq, hs.coe_toFinset
-/
theorem finprod_mem_eq_finite_toFinset_prod (f : α -> M) {s : Set α} (hs : s.Finite) :
    ∏ᶠ i in s, f i = ∏ i in hs.toFinset, f i :=
finprod_mem_eq_prod_of_inter_mulSupport_eq _ by rw [hs.coe_toFinset]

@[to_additive]
/--
theorem `finprod_mem_finset_eq_prod` / 定理 `finprod_mem_finset_eq_prod`

English:
theorem finprod_mem_finset_eq_prod
  given: (f : α -> M) (s : Finset α)
  statement: ∏ᶠ i in s, f i = ∏ i in s, f i
  proof: finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]

中文:
定理 finprod_mem_finset_eq_prod
  条件: (f : α -> M) (s : Finset α)
  结论: ∏ᶠ i in s, f i = ∏ i in s, f i
  证明: finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]

Depends on / 依赖: finprod_mem_eq_prod_of_inter_mulSupport_eq
-/
theorem finprod_mem_finset_eq_prod (f : α -> M) (s : Finset α) : ∏ᶠ i in s, f i = ∏ i in s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]
/--
theorem `finprod_mem_coe_finset` / 定理 `finprod_mem_coe_finset`

English:
theorem finprod_mem_coe_finset
  given: (f : α -> M) (s : Finset α)
  proof: finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]

中文:
定理 finprod_mem_coe_finset
  条件: (f : α -> M) (s : Finset α)
  证明: finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]

Depends on / 依赖: finprod_mem_eq_prod_of_inter_mulSupport_eq
-/
theorem finprod_mem_coe_finset (f : α -> M) (s : Finset α) :
    (∏ᶠ i in (s : Set α), f i) = ∏ i in s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]
/--
theorem `finprod_mem_eq_one_of_infinite` / 定理 `finprod_mem_eq_one_of_infinite`

English:
theorem finprod_mem_eq_one_of_infinite
  given: {f : α -> M} {s : Set α} (hs : (s inter mulSupport f).Infinite)
  proof: by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mulSupport_mulIndicator] at hs

@[to_additive]

中文:
定理 finprod_mem_eq_one_of_infinite
  条件: {f : α -> M} {s : Set α} (hs : (s inter mulSupport f).Infinite)
  证明: by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mulSupport_mulIndicator] at hs

@[to_additive]

Depends on / 依赖: finprod_mem_def, finprod_of_infinite_mulSupport, mulSupport_mulIndicator
-/
theorem finprod_mem_eq_one_of_infinite {f : α -> M} {s : Set α} (hs : (s inter mulSupport f).Infinite) :
    ∏ᶠ i in s, f i = 1 := by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mulSupport_mulIndicator] at hs

@[to_additive]
/--
theorem `finprod_mem_eq_one_of_forall_eq_one` / 定理 `finprod_mem_eq_one_of_forall_eq_one`

English:
theorem finprod_mem_eq_one_of_forall_eq_one
  given: {f : α -> M} {s : Set α} (h : forall x in s, f x = 1)
  proof: by simp +contextual [h]

@[to_additive]

中文:
定理 finprod_mem_eq_one_of_forall_eq_one
  条件: {f : α -> M} {s : Set α} (h : 对任意 x in s, f x = 1)
  证明: by simp +contextual [h]

@[to_additive]

Depends on / 依赖: contextual
-/
theorem finprod_mem_eq_one_of_forall_eq_one {f : α -> M} {s : Set α} (h : forall x in s, f x = 1) :
    ∏ᶠ i in s, f i = 1 := by simp +contextual [h]

@[to_additive]
/--
theorem `finprod_mem_inter_mulSupport` / 定理 `finprod_mem_inter_mulSupport`

English:
theorem finprod_mem_inter_mulSupport
  given: (f : α -> M) (s : Set α)
  proof: by
  rw [finprod_mem_def]; rw [finprod_mem_def]; rw [mulIndicator_inter_mulSupport]

@[to_additive]

中文:
定理 finprod_mem_inter_mulSupport
  条件: (f : α -> M) (s : Set α)
  证明: by
  rw [finprod_mem_def]; rw [finprod_mem_def]; rw [mulIndicator_inter_mulSupport]

@[to_additive]

Depends on / 依赖: finprod_mem_def, mulIndicator_inter_mulSupport
-/
theorem finprod_mem_inter_mulSupport (f : α -> M) (s : Set α) :
    ∏ᶠ i in s inter mulSupport f, f i = ∏ᶠ i in s, f i := by
  rw [finprod_mem_def]; rw [finprod_mem_def]; rw [mulIndicator_inter_mulSupport]

@[to_additive]
/--
theorem `finprod_mem_inter_mulSupport_eq` / 定理 `finprod_mem_inter_mulSupport_eq`

English:
theorem finprod_mem_inter_mulSupport_eq
  statement: (f : α -> M) (s t : Set α)
  proof: by
  rw [← finprod_mem_inter_mulSupport]; rw [h]; rw [finprod_mem_inter_mulSupport]

@[to_additive]

中文:
定理 finprod_mem_inter_mulSupport_eq
  结论: (f : α -> M) (s t : Set α)
  证明: by
  rw [← finprod_mem_inter_mulSupport]; rw [h]; rw [finprod_mem_inter_mulSupport]

@[to_additive]

Depends on / 依赖: finprod_mem_inter_mulSupport
-/
theorem finprod_mem_inter_mulSupport_eq (f : α -> M) (s t : Set α)
    (h : s inter mulSupport f = t inter mulSupport f) : ∏ᶠ i in s, f i = ∏ᶠ i in t, f i := by
  rw [← finprod_mem_inter_mulSupport]; rw [h]; rw [finprod_mem_inter_mulSupport]

@[to_additive]
/--
theorem `finprod_mem_inter_mulSupport_eq'` / 定理 `finprod_mem_inter_mulSupport_eq'`

English:
theorem finprod_mem_inter_mulSupport_eq'
  statement: (f : α -> M) (s t : Set α)
  proof: by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)

@[to_additive]

中文:
定理 finprod_mem_inter_mulSupport_eq'
  结论: (f : α -> M) (s t : Set α)
  证明: by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)

@[to_additive]

Depends on / 依赖: and_congr_left, finprod_mem_inter_mulSupport_eq
-/
theorem finprod_mem_inter_mulSupport_eq' (f : α -> M) (s t : Set α)
    (h : forall x in mulSupport f, x in s ↔ x in t) : ∏ᶠ i in s, f i = ∏ᶠ i in t, f i := by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)

@[to_additive]
/--
theorem `finprod_mem_univ` / 定理 `finprod_mem_univ`

English:
theorem finprod_mem_univ
  given: (f : α -> M)
  statement: ∏ᶠ i in @Set.univ α, f i = ∏ᶠ i : α, f i
  proof: finprod_congr fun _ => finprod_true _

中文:
定理 finprod_mem_univ
  条件: (f : α -> M)
  结论: ∏ᶠ i in @Set.univ α, f i = ∏ᶠ i : α, f i
  证明: finprod_congr fun _ => finprod_true _

Depends on / 依赖: finprod_congr, finprod_true
-/
theorem finprod_mem_univ (f : α -> M) : ∏ᶠ i in @Set.univ α, f i = ∏ᶠ i : α, f i :=
  finprod_congr fun _ => finprod_true _

variable {f g : α -> M} {a b : α} {s t : Set α}

@[to_additive]
/--
theorem `finprod_mem_congr` / 定理 `finprod_mem_congr`

English:
theorem finprod_mem_congr
  given: (h₀ : s = t) (h₁ : forall x in t, f x = g x)
  proof: h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)

@[to_additive]

中文:
定理 finprod_mem_congr
  条件: (h₀ : s = t) (h₁ : 对任意 x in t, f x = g x)
  证明: h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)

@[to_additive]

Depends on / 依赖: finprod_congr, finprod_congr_Prop
-/
theorem finprod_mem_congr (h₀ : s = t) (h₁ : forall x in t, f x = g x) :
    ∏ᶠ i in s, f i = ∏ᶠ i in t, g i :=
  h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)

@[to_additive]
/--
theorem `finprod_eq_one_of_forall_eq_one` / 定理 `finprod_eq_one_of_forall_eq_one`

English:
theorem finprod_eq_one_of_forall_eq_one
  given: {f : α -> M} (h : forall x, f x = 1)
  statement: ∏ᶠ i, f i = 1
  proof: by
  simp +contextual [h]

@[to_additive finsum_cond_pos]

中文:
定理 finprod_eq_one_of_forall_eq_one
  条件: {f : α -> M} (h : 对任意 x, f x = 1)
  结论: ∏ᶠ i, f i = 1
  证明: by
  simp +contextual [h]

@[to_additive finsum_cond_pos]

Depends on / 依赖: contextual
-/
theorem finprod_eq_one_of_forall_eq_one {f : α -> M} (h : forall x, f x = 1) : ∏ᶠ i, f i = 1 := by
  simp +contextual [h]

@[to_additive finsum_cond_pos]
/--
theorem `one_lt_finprod_cond` / 定理 `one_lt_finprod_cond`

English:
theorem one_lt_finprod_cond
  statement: {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
  proof: by
  rw [finprod_cond_eq_prod_of_cond_iff (t := hf.toFinset)]
  · apply Finset.one_lt_prod'
    · simp +contextual [h]
    · aesop
  · simp +contextual

@[deprecated (since := "2026-01-06")] alias finprod_cond_pos := finsum_cond_pos

@[to_additive finsum_pos]

中文:
定理 one_lt_finprod_cond
  结论: {M : 类型} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
  证明: by
  rw [finprod_cond_eq_prod_of_cond_iff (t := hf.toFinset)]
  · apply Finset.one_lt_prod'
    · simp +contextual [h]
    · aesop
  · simp +contextual

@[deprecated (since := "2026-01-06")] alias finprod_cond_pos := finsum_cond_pos

@[to_additive finsum_pos]

Depends on / 依赖: Finset, Finset.one_lt_prod, contextual, finprod_cond_eq_prod_of_cond_iff, hf.toFinset, one_lt_prod, toFinset
-/
theorem one_lt_finprod_cond {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι -> M} {p : ι -> Prop} (h : forall i, p i -> 1 <= f i) (h' : exists i, p i ∧ 1 < f i)
    (hf : (mulSupport f inter {i | p i}).Finite) : 1 < ∏ᶠ (i) (_ : p i), f i := by
  rw [finprod_cond_eq_prod_of_cond_iff (t := hf.toFinset)]
  · apply Finset.one_lt_prod'
    · simp +contextual [h]
    · aesop
  · simp +contextual

@[deprecated (since := "2026-01-06")] alias finprod_cond_pos := finsum_cond_pos

@[to_additive finsum_pos]
/--
theorem `one_lt_finprod` / 定理 `one_lt_finprod`

English:
theorem one_lt_finprod
  statement: {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
  proof: by
  rw [← finprod_mem_univ]
  apply one_lt_finprod_cond <;> simpa

@[deprecated (since := "2026-01-03")]
alias finsum_pos' := finsum_pos

@[to_additive existing finsum_pos', deprecated (since := "2026-01-03")]
alias one_lt_finprod' := one_lt_finprod

中文:
定理 one_lt_finprod
  结论: {M : 类型} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
  证明: by
  rw [← finprod_mem_univ]
  apply one_lt_finprod_cond <;> simpa

@[deprecated (since := "2026-01-03")]
alias finsum_pos' := finsum_pos

@[to_additive existing finsum_pos', deprecated (since := "2026-01-03")]
alias one_lt_finprod' := one_lt_finprod

Depends on / 依赖: finprod_mem_univ, one_lt_finprod_cond
-/
theorem one_lt_finprod {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι -> M}
    (h : forall i, 1 <= f i) (h' : exists i, 1 < f i) (hf : HasFiniteMulSupport f) : 1 < ∏ᶠ i, f i := by
  rw [← finprod_mem_univ]
  apply one_lt_finprod_cond <;> simpa

@[deprecated (since := "2026-01-03")]
alias finsum_pos' := finsum_pos

@[to_additive existing finsum_pos', deprecated (since := "2026-01-03")]
alias one_lt_finprod' := one_lt_finprod

/-- Monotonicity of `finprod`. See `finprod_le_finprod` for a variant where
`M` is a `CommMonoidWithZero`. -/
@[to_additive /-- Monotonicity of `finsum.` -/]
/--
lemma `finprod_le_finprod'` / 引理 `finprod_le_finprod'`

English:
lemma finprod_le_finprod'
  statement: [PartialOrder M] [MulLeftMono M] (hf : HasFiniteMulSupport f)
  proof: by
  have : Fintype ↑(f.mulSupport union g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport union g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport subseteq s by grind)]; rw [finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport subse

中文:
引理 finprod_le_finprod'
  结论: [PartialOrder M] [MulLeftMono M] (hf : HasFiniteMulSupport f)
  证明: by
  have : Fintype ↑(f.mulSupport union g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport union g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport subseteq s by grind)]; rw [finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport subse

Depends on / 依赖: Finset, Finset.prod_le_prod, Fintype, f.mulSupport, finprod_eq_finsetProd_of_mulSupport_subset, fintype, g.mulSupport, hf.union, mulSupport, prod_le_prod, subseteq, toFinset
-/
lemma finprod_le_finprod' [PartialOrder M] [MulLeftMono M] (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) (h : f <= g) :
    ∏ᶠ a, f a <= ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport union g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport union g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport subseteq s by grind)]; rw [finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport subseteq s by grind)]
  exact Finset.prod_le_prod' fun i _ => h i

/--
lemma `finprod_le_finprod` / 引理 `finprod_le_finprod`

English:
lemma finprod_le_finprod
  statement: {M : Type*} [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M]
  proof: by
  have : Fintype ↑(f.mulSupport union g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport union g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport subseteq s by grind)]; rw [finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport subse

中文:
引理 finprod_le_finprod
  结论: {M : 类型} [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M]
  证明: by
  have : Fintype ↑(f.mulSupport union g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport union g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport subseteq s by grind)]; rw [finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport subse

Depends on / 依赖: Finset, Finset.prod_le_prod, Fintype, f.mulSupport, finprod_eq_finsetProd_of_mulSupport_subset, fintype, g.mulSupport, hf.union, mulSupport, prod_le_prod, subseteq, toFinset
-/
lemma finprod_le_finprod {M : Type*} [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {f g : α -> M} (hf : HasFiniteMulSupport f) (hf₀ : forall a, 0 <= f a)
    (hg : HasFiniteMulSupport g) (h : f <= g) :
    ∏ᶠ a, f a <= ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport union g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport union g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport subseteq s by grind)]; rw [finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport subseteq s by grind)]
  exact Finset.prod_le_prod (fun i _ => hf₀ i) fun i _ => h i

/--
lemma `finprod_zero_le_one` / 引理 `finprod_zero_le_one`

English:
lemma finprod_zero_le_one
  statement: {M α : Type*} [CommMonoidWithZero M] [PartialOrder M]
  proof: by
  rw [← finprod_one (α := α)]
  by_cases H : (fun _ : α => (0 : M)).HasFiniteMulSupport
  · exact finprod_le_finprod H (fun _ => le_rfl) (by fun_prop) fun _ => zero_le_one
  · rw [finprod_of_not_hasFiniteMulSupport H]
    exact finprod_one.symm.le

中文:
引理 finprod_zero_le_one
  结论: {M α : 类型} [CommMonoidWithZero M] [PartialOrder M]
  证明: by
  rw [← finprod_one (α := α)]
  by_cases H : (fun _ : α => (0 : M)).HasFiniteMulSupport
  · exact finprod_le_finprod H (fun _ => le_rfl) (by fun_prop) fun _ => zero_le_one
  · rw [finprod_of_not_hasFiniteMulSupport H]
    exact finprod_one.symm.le

Depends on / 依赖: HasFiniteMulSupport, finprod_le_finprod, finprod_of_not_hasFiniteMulSupport, finprod_one, finprod_one.symm.le, fun_prop, le_rfl, zero_le_one
-/
lemma finprod_zero_le_one {M α : Type*} [CommMonoidWithZero M] [PartialOrder M]
    [ZeroLEOneClass M] [PosMulMono M] :
    ∏ᶠ _ : α, (0 : M) <= 1 := by
  rw [← finprod_one (α := α)]
  by_cases H : (fun _ : α => (0 : M)).HasFiniteMulSupport
  · exact finprod_le_finprod H (fun _ => le_rfl) (by fun_prop) fun _ => zero_le_one
  · rw [finprod_of_not_hasFiniteMulSupport H]
    exact finprod_one.symm.le

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/


set_option backward.isDefEq.respectTransparency false in
/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product of `g i`. -/
@[to_additive
      /-- If the additive supports of `f` and `g` are finite, then the sum of `f i + g i`
      equals the sum of `f i` plus the sum of `g i`. -/]
/--
theorem `finprod_mul_distrib` / 定理 `finprod_mul_distrib`

English:
theorem finprod_mul_distrib
  given: (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g)
  proof: by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf Finset.subset_union_left]; rw [finprod_eq_prod_of_mulSupport_toFinset_subset g hg Finset.subset_union_right]; rw [←
      Finset.prod_mul_distrib]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    simp only [Finset.coe_

中文:
定理 finprod_mul_distrib
  条件: (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g)
  证明: by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf Finset.subset_union_left]; rw [finprod_eq_prod_of_mulSupport_toFinset_subset g hg Finset.subset_union_right]; rw [←
      Finset.prod_mul_distrib]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    simp only [Finset.coe_

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, Finset.coe_union, Finset.prod_mul_distrib, Finset.subset_union_left, Finset.subset_union_right, classical, coe_toFinset, coe_union, contrapose, finprod_eq_prod_of_mulSupport_subset, finprod_eq_prod_of_mulSupport_toFinset_subset, mem_mulSupport, mem_union, mulSupport_subset_iff, prod_mul_distrib, subset_union_left, subset_union_right
-/
theorem finprod_mul_distrib (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i := by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf Finset.subset_union_left]; rw [finprod_eq_prod_of_mulSupport_toFinset_subset g hg Finset.subset_union_right]; rw [←
      Finset.prod_mul_distrib]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    simp only [Finset.coe_union, Finite.coe_toFinset, mulSupport_subset_iff,
      mem_union, mem_mulSupport]
    intro x
    contrapose!
    rintro ⟨hf, hg⟩
    simp [hf, hg]

/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i / g i`
equals the product of `f i` divided by the product of `g i`. -/
@[to_additive
      /-- If the additive supports of `f` and `g` are finite, then the sum of `f i - g i`
      equals the sum of `f i` minus the sum of `g i`. -/]
/--
theorem `finprod_div_distrib` / 定理 `finprod_div_distrib`

English:
theorem finprod_div_distrib
  statement: [DivisionCommMonoid G] {f g : α -> G} (hf : HasFiniteMulSupport f)
  proof: by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf <| hg.fun_inv, finprod_inv_distrib]

中文:
定理 finprod_div_distrib
  结论: [DivisionCommMonoid G] {f g : α -> G} (hf : HasFiniteMulSupport f)
  证明: by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf <| hg.fun_inv, finprod_inv_distrib]

Depends on / 依赖: div_eq_mul_inv, finprod_inv_distrib, finprod_mul_distrib, fun_inv, hg.fun_inv
-/
theorem finprod_div_distrib [DivisionCommMonoid G] {f g : α -> G} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) : ∏ᶠ i, f i / g i = (∏ᶠ i, f i) / ∏ᶠ i, g i := by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf <| hg.fun_inv, finprod_inv_distrib]

/-- A more general version of `finprod_mem_mul_distrib` that only requires `s ∩ mulSupport f` and
`s ∩ mulSupport g` rather than `s` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_add_distrib` that only requires `s ∩ support f`
      and `s ∩ support g` rather than `s` to be finite. -/]
/--
theorem `finprod_mem_mul_distrib'` / 定理 `finprod_mem_mul_distrib'`

English:
theorem finprod_mem_mul_distrib'
  given: (hf : (s inter mulSupport f).Finite) (hg : (s inter mulSupport g).Finite)
  proof: by
  rw [← mulSupport_mulIndicator] at hf hg
  simp only [finprod_mem_def, mulIndicator_mul, finprod_mul_distrib hf hg]

中文:
定理 finprod_mem_mul_distrib'
  条件: (hf : (s inter mulSupport f).Finite) (hg : (s inter mulSupport g).Finite)
  证明: by
  rw [← mulSupport_mulIndicator] at hf hg
  simp only [finprod_mem_def, mulIndicator_mul, finprod_mul_distrib hf hg]

Depends on / 依赖: finprod_mem_def, finprod_mul_distrib, mulIndicator_mul, mulSupport_mulIndicator
-/
theorem finprod_mem_mul_distrib' (hf : (s inter mulSupport f).Finite) (hg : (s inter mulSupport g).Finite) :
    ∏ᶠ i in s, f i * g i = (∏ᶠ i in s, f i) * ∏ᶠ i in s, g i := by
  rw [← mulSupport_mulIndicator] at hf hg
  simp only [finprod_mem_def, mulIndicator_mul, finprod_mul_distrib hf hg]

/-- The product of the constant function `1` over any set equals `1`. -/
@[to_additive /-- The sum of the constant function `0` over any set equals `0`. -/]
/--
theorem `finprod_mem_one` / 定理 `finprod_mem_one`

English:
theorem finprod_mem_one
  given: (s : Set α)
  statement: (∏ᶠ i in s, (1 : M)) = 1
  proof: by simp

中文:
定理 finprod_mem_one
  条件: (s : Set α)
  结论: (∏ᶠ i in s, (1 : M)) = 1
  证明: by simp
-/
theorem finprod_mem_one (s : Set α) : (∏ᶠ i in s, (1 : M)) = 1 := by simp

/-- If a function `f` equals `1` on a set `s`, then the product of `f i` over `i ∈ s` equals `1`. -/
@[to_additive
      /-- If a function `f` equals `0` on a set `s`, then the sum of `f i` over `i ∈ s`
      equals `0`. -/]
/--
theorem `finprod_mem_of_eqOn_one` / 定理 `finprod_mem_of_eqOn_one`

English:
theorem finprod_mem_of_eqOn_one
  given: (hf : s.EqOn f 1)
  statement: ∏ᶠ i in s, f i = 1
  proof: by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

中文:
定理 finprod_mem_of_eqOn_one
  条件: (hf : s.EqOn f 1)
  结论: ∏ᶠ i in s, f i = 1
  证明: by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

Depends on / 依赖: finprod_mem_congr, finprod_mem_one
-/
theorem finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : ∏ᶠ i in s, f i = 1 := by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

/-- If the product of `f i` over `i ∈ s` is not equal to `1`, then there is some `x ∈ s` such that
`f x ≠ 1`. -/
@[to_additive
      /-- If the sum of `f i` over `i ∈ s` is not equal to `0`, then there is some `x ∈ s`
      such that `f x ≠ 0`. -/]
/--
theorem `exists_ne_one_of_finprod_mem_ne_one` / 定理 `exists_ne_one_of_finprod_mem_ne_one`

English:
theorem exists_ne_one_of_finprod_mem_ne_one
  given: (h : ∏ᶠ i in s, f i != 1)
  statement: exists x in s, f x != 1
  proof: by
  by_contra! h'
  exact h (finprod_mem_of_eqOn_one h')

中文:
定理 exists_ne_one_of_finprod_mem_ne_one
  条件: (h : ∏ᶠ i in s, f i != 1)
  结论: 存在 x in s, f x != 1
  证明: by
  by_contra! h'
  exact h (finprod_mem_of_eqOn_one h')

Depends on / 依赖: finprod_mem_of_eqOn_one
-/
theorem exists_ne_one_of_finprod_mem_ne_one (h : ∏ᶠ i in s, f i != 1) : exists x in s, f x != 1 := by
  by_contra! h'
  exact h (finprod_mem_of_eqOn_one h')

/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s`, the sum of `f i + g i` over `i ∈ s` equals the sum of `f i`
      over `i ∈ s` plus the sum of `g i` over `i ∈ s`. -/]
/--
theorem `finprod_mem_mul_distrib` / 定理 `finprod_mem_mul_distrib`

English:
theorem finprod_mem_mul_distrib
  given: (hs : s.Finite)
  proof: finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive]

中文:
定理 finprod_mem_mul_distrib
  条件: (hs : s.Finite)
  证明: finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive]

Depends on / 依赖: finprod_mem_mul_distrib, hs.inter_of_left, inter_of_left
-/
theorem finprod_mem_mul_distrib (hs : s.Finite) :
    ∏ᶠ i in s, f i * g i = (∏ᶠ i in s, f i) * ∏ᶠ i in s, g i :=
  finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive]
/--
theorem `MonoidHom.map_finprod` / 定理 `MonoidHom.map_finprod`

English:
theorem MonoidHom.map_finprod
  given: {f : α -> M} (g : M ->* N) (hf : HasFiniteMulSupport f)
  proof: g.map_finprod_plift f hf.preimage Equiv.plift.injective.injOn

@[to_additive]

中文:
定理 MonoidHom.map_finprod
  条件: {f : α -> M} (g : M ->* N) (hf : HasFiniteMulSupport f)
  证明: g.map_finprod_plift f hf.preimage Equiv.plift.injective.injOn

@[to_additive]

Depends on / 依赖: Equiv.plift.injective.injOn, g.map_finprod_plift, hf.preimage, injective, map_finprod_plift, preimage
-/
theorem MonoidHom.map_finprod {f : α -> M} (g : M ->* N) (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
g.map_finprod_plift f hf.preimage Equiv.plift.injective.injOn

@[to_additive]
/--
theorem `map_finprod` / 定理 `map_finprod`

English:
theorem map_finprod
  statement: {G : Type*} [FunLike G M N] [MonoidHomClass G M N] (g : G)
  proof: (g : M ->* N).map_finprod hf

@[to_additive]

中文:
定理 map_finprod
  结论: {G : 类型} [FunLike G M N] [MonoidHomClass G M N] (g : G)
  证明: (g : M ->* N).map_finprod hf

@[to_additive]

Depends on / 依赖: map_finprod
-/
theorem map_finprod {G : Type*} [FunLike G M N] [MonoidHomClass G M N] (g : G)
    (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  (g : M ->* N).map_finprod hf

@[to_additive]
/--
theorem `finprod_pow` / 定理 `finprod_pow`

English:
theorem finprod_pow
  given: (hf : HasFiniteMulSupport f) (n : Nat)
  statement: (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n
  proof: (powMonoidHom n).map_finprod hf

中文:
定理 finprod_pow
  条件: (hf : HasFiniteMulSupport f) (n : 自然数)
  结论: (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n
  证明: (powMonoidHom n).map_finprod hf

Depends on / 依赖: map_finprod, powMonoidHom
-/
theorem finprod_pow (hf : HasFiniteMulSupport f) (n : Nat) : (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n :=
  (powMonoidHom n).map_finprod hf

/--
theorem `finsum_smul'` / 定理 `finsum_smul'`

English:
theorem finsum_smul'
  statement: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : ι -> R}
  proof: ((smulAddHom R M).flip x).map_finsum hf

中文:
定理 finsum_smul'
  结论: {R M : 类型} [Semiring R] [AddCommMonoid M] [Module R M] {f : ι -> R}
  证明: ((smulAddHom R M).flip x).map_finsum hf

Depends on / 依赖: map_finsum, smulAddHom
-/
theorem finsum_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : ι -> R}
    (hf : HasFiniteSupport f) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x :=
  ((smulAddHom R M).flip x).map_finsum hf

/--
theorem `smul_finsum'` / 定理 `smul_finsum'`

English:
theorem smul_finsum'
  statement: {R M : Type*} [AddCommMonoid M] [DistribSMul R M] (c : R)
  proof: (DistribSMul.toAddMonoidHom M c).map_finsum hf

中文:
定理 smul_finsum'
  结论: {R M : 类型} [AddCommMonoid M] [DistribSMul R M] (c : R)
  证明: (DistribSMul.toAddMonoidHom M c).map_finsum hf

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_finsum, toAddMonoidHom
-/
theorem smul_finsum' {R M : Type*} [AddCommMonoid M] [DistribSMul R M] (c : R)
    {f : ι -> M} (hf : HasFiniteSupport f) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i :=
  (DistribSMul.toAddMonoidHom M c).map_finsum hf

/-- A more general version of `MonoidHom.map_finprod_mem` that requires `s ∩ mulSupport f` rather
than `s` to be finite. -/
@[to_additive
      /-- A more general version of `AddMonoidHom.map_finsum_mem` that requires
      `s ∩ support f` rather than `s` to be finite. -/]
/--
theorem `MonoidHom.map_finprod_mem'` / 定理 `MonoidHom.map_finprod_mem'`

English:
theorem MonoidHom.map_finprod_mem'
  given: {f : α -> M} (g : M ->* N) (h₀ : (s inter mulSupport f).Finite)
  proof: by
  rw [g.map_finprod]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, HasFiniteMulSupport, mulSupport_mulIndicator]

中文:
定理 MonoidHom.map_finprod_mem'
  条件: {f : α -> M} (g : M ->* N) (h₀ : (s inter mulSupport f).Finite)
  证明: by
  rw [g.map_finprod]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, HasFiniteMulSupport, mulSupport_mulIndicator]

Depends on / 依赖: HasFiniteMulSupport, finprod_eq_mulIndicator_apply, g.map_finprod, g.map_finprod_Prop, map_finprod, map_finprod_Prop, mulSupport_mulIndicator
-/
theorem MonoidHom.map_finprod_mem' {f : α -> M} (g : M ->* N) (h₀ : (s inter mulSupport f).Finite) :
    g (∏ᶠ j in s, f j) = ∏ᶠ i in s, g (f i) := by
  rw [g.map_finprod]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, HasFiniteMulSupport, mulSupport_mulIndicator]

/-- Given a monoid homomorphism `g : M →* N` and a function `f : α → M`, the value of `g` at the
product of `f i` over `i ∈ s` equals the product of `g (f i)` over `s`. -/
@[to_additive
      /-- Given an additive monoid homomorphism `g : M →* N` and a function `f : α → M`, the
      value of `g` at the sum of `f i` over `i ∈ s` equals the sum of `g (f i)` over `s`. -/]
/--
theorem `MonoidHom.map_finprod_mem` / 定理 `MonoidHom.map_finprod_mem`

English:
theorem MonoidHom.map_finprod_mem
  given: (f : α -> M) (g : M ->* N) (hs : s.Finite)
  proof: g.map_finprod_mem' (hs.inter_of_left _)

@[to_additive]

中文:
定理 MonoidHom.map_finprod_mem
  条件: (f : α -> M) (g : M ->* N) (hs : s.Finite)
  证明: g.map_finprod_mem' (hs.inter_of_left _)

@[to_additive]

Depends on / 依赖: g.map_finprod_mem, hs.inter_of_left, inter_of_left, map_finprod_mem
-/
theorem MonoidHom.map_finprod_mem (f : α -> M) (g : M ->* N) (hs : s.Finite) :
    g (∏ᶠ j in s, f j) = ∏ᶠ i in s, g (f i) :=
  g.map_finprod_mem' (hs.inter_of_left _)

@[to_additive]
/--
theorem `MulEquiv.map_finprod_mem` / 定理 `MulEquiv.map_finprod_mem`

English:
theorem MulEquiv.map_finprod_mem
  given: (g : M ≃* N) (f : α -> M) {s : Set α} (hs : s.Finite)
  proof: g.toMonoidHom.map_finprod_mem f hs

@[to_additive]

中文:
定理 MulEquiv.map_finprod_mem
  条件: (g : M ≃* N) (f : α -> M) {s : Set α} (hs : s.Finite)
  证明: g.toMonoidHom.map_finprod_mem f hs

@[to_additive]

Depends on / 依赖: g.toMonoidHom.map_finprod_mem, map_finprod_mem, toMonoidHom
-/
theorem MulEquiv.map_finprod_mem (g : M ≃* N) (f : α -> M) {s : Set α} (hs : s.Finite) :
    g (∏ᶠ i in s, f i) = ∏ᶠ i in s, g (f i) :=
  g.toMonoidHom.map_finprod_mem f hs

@[to_additive]
/--
theorem `finprod_mem_inv_distrib` / 定理 `finprod_mem_inv_distrib`

English:
theorem finprod_mem_inv_distrib
  given: [DivisionCommMonoid G] (f : α -> G) (hs : s.Finite)
  proof: ((MulEquiv.inv G).map_finprod_mem f hs).symm

中文:
定理 finprod_mem_inv_distrib
  条件: [DivisionCommMonoid G] (f : α -> G) (hs : s.Finite)
  证明: ((MulEquiv.inv G).map_finprod_mem f hs).symm

Depends on / 依赖: MulEquiv, MulEquiv.inv, map_finprod_mem
-/
theorem finprod_mem_inv_distrib [DivisionCommMonoid G] (f : α -> G) (hs : s.Finite) :
    (∏ᶠ x in s, (f x)⁻¹) = (∏ᶠ x in s, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod_mem f hs).symm

/-- Given a finite set `s`, the product of `f i / g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` divided by the product of `g i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s`, the sum of `f i / g i` over `i ∈ s` equals the sum of `f i`
      over `i ∈ s` minus the sum of `g i` over `i ∈ s`. -/]
/--
theorem `finprod_mem_div_distrib` / 定理 `finprod_mem_div_distrib`

English:
theorem finprod_mem_div_distrib
  given: [DivisionCommMonoid G] (f g : α -> G) (hs : s.Finite)
  proof: by
  simp only [div_eq_mul_inv, finprod_mem_mul_distrib hs, finprod_mem_inv_distrib g hs]

中文:
定理 finprod_mem_div_distrib
  条件: [DivisionCommMonoid G] (f g : α -> G) (hs : s.Finite)
  证明: by
  simp only [div_eq_mul_inv, finprod_mem_mul_distrib hs, finprod_mem_inv_distrib g hs]

Depends on / 依赖: div_eq_mul_inv, finprod_mem_inv_distrib, finprod_mem_mul_distrib
-/
theorem finprod_mem_div_distrib [DivisionCommMonoid G] (f g : α -> G) (hs : s.Finite) :
    ∏ᶠ i in s, f i / g i = (∏ᶠ i in s, f i) / ∏ᶠ i in s, g i := by
  simp only [div_eq_mul_inv, finprod_mem_mul_distrib hs, finprod_mem_inv_distrib g hs]

/-!
### `∏ᶠ x ∈ s, f x` and set operations
-/


/-- The product of any function over an empty set is `1`. -/
@[to_additive /-- The sum of any function over an empty set is `0`. -/]
/--
theorem `finprod_mem_empty` / 定理 `finprod_mem_empty`

English:
theorem finprod_mem_empty
  statement: (∏ᶠ i in (∅ : Set α), f i) = 1
  proof: by simp

中文:
定理 finprod_mem_empty
  结论: (∏ᶠ i in (∅ : Set α), f i) = 1
  证明: by simp
-/
theorem finprod_mem_empty : (∏ᶠ i in (∅ : Set α), f i) = 1 := by simp

/-- A set `s` is nonempty if the product of some function over `s` is not equal to `1`. -/
@[to_additive
/-- A set `s` is nonempty if the sum of some function over `s` is not equal to `0`. -/]
/--
theorem `nonempty_of_finprod_mem_ne_one` / 定理 `nonempty_of_finprod_mem_ne_one`

English:
theorem nonempty_of_finprod_mem_ne_one
  given: (h : ∏ᶠ i in s, f i != 1)
  statement: s.Nonempty
  proof: nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ finprod_mem_empty

中文:
定理 nonempty_of_finprod_mem_ne_one
  条件: (h : ∏ᶠ i in s, f i != 1)
  结论: s.Nonempty
  证明: nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ finprod_mem_empty

Depends on / 依赖: finprod_mem_empty, nonempty_iff_ne_empty
-/
theorem nonempty_of_finprod_mem_ne_one (h : ∏ᶠ i in s, f i != 1) : s.Nonempty :=
nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ finprod_mem_empty

/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive
      /-- Given finite sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` plus the sum of
      `f i` over `i ∈ s ∩ t` equals the sum of `f i` over `i ∈ s` plus the sum of `f i`
      over `i ∈ t`. -/]
/--
theorem `finprod_mem_union_inter` / 定理 `finprod_mem_union_inter`

English:
theorem finprod_mem_union_inter
  given: (hs : s.Finite) (ht : t.Finite)
  proof: by
  lift s to Finset α using hs; lift t to Finset α using ht
  classical
    rw [← Finset.coe_union]; rw [← Finset.coe_inter]
    simp only [finprod_mem_coe_finset, Finset.prod_union_inter]

中文:
定理 finprod_mem_union_inter
  条件: (hs : s.Finite) (ht : t.Finite)
  证明: by
  lift s to Finset α using hs; lift t to Finset α using ht
  classical
    rw [← Finset.coe_union]; rw [← Finset.coe_inter]
    simp only [finprod_mem_coe_finset, Finset.prod_union_inter]

Depends on / 依赖: Finset, Finset.coe_inter, Finset.coe_union, Finset.prod_union_inter, classical, coe_inter, coe_union, finprod_mem_coe_finset, prod_union_inter
-/
theorem finprod_mem_union_inter (hs : s.Finite) (ht : t.Finite) :
    ((∏ᶠ i in s union t, f i) * ∏ᶠ i in s inter t, f i) = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i := by
  lift s to Finset α using hs; lift t to Finset α using ht
  classical
    rw [← Finset.coe_union]; rw [← Finset.coe_inter]
    simp only [finprod_mem_coe_finset, Finset.prod_union_inter]

/-- A more general version of `finprod_mem_union_inter` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_union_inter` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be finite. -/]
/--
theorem `finprod_mem_union_inter'` / 定理 `finprod_mem_union_inter'`

English:
theorem finprod_mem_union_inter'
  given: (hs : (s inter mulSupport f).Finite) (ht : (t inter mulSupport f).Finite)
  proof: by
  rw [← finprod_mem_inter_mulSupport f s]; rw [← finprod_mem_inter_mulSupport f t]; rw [←
    finprod_mem_union_inter hs ht]; rw [← union_inter_distrib_right]; rw [finprod_mem_inter_mulSupport]; rw [←
    finprod_mem_inter_mulSupport f (s inter t)]
  rw [inter_left_comm]; rw [inter_assoc]; rw [in

中文:
定理 finprod_mem_union_inter'
  条件: (hs : (s inter mulSupport f).Finite) (ht : (t inter mulSupport f).Finite)
  证明: by
  rw [← finprod_mem_inter_mulSupport f s]; rw [← finprod_mem_inter_mulSupport f t]; rw [←
    finprod_mem_union_inter hs ht]; rw [← union_inter_distrib_right]; rw [finprod_mem_inter_mulSupport]; rw [←
    finprod_mem_inter_mulSupport f (s inter t)]
  rw [inter_left_comm]; rw [inter_assoc]; rw [in

Depends on / 依赖: finprod_mem_inter_mulSupport, finprod_mem_union_inter, inter_assoc, inter_left_comm, inter_self, union_inter_distrib_right
-/
theorem finprod_mem_union_inter' (hs : (s inter mulSupport f).Finite) (ht : (t inter mulSupport f).Finite) :
    ((∏ᶠ i in s union t, f i) * ∏ᶠ i in s inter t, f i) = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i := by
  rw [← finprod_mem_inter_mulSupport f s]; rw [← finprod_mem_inter_mulSupport f t]; rw [←
    finprod_mem_union_inter hs ht]; rw [← union_inter_distrib_right]; rw [finprod_mem_inter_mulSupport]; rw [←
    finprod_mem_inter_mulSupport f (s inter t)]
  rw [inter_left_comm]; rw [inter_assoc]; rw [inter_assoc]; rw [inter_self]; rw [inter_left_comm]

/-- A more general version of `finprod_mem_union` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_union` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be finite. -/]
/--
theorem `finprod_mem_union'` / 定理 `finprod_mem_union'`

English:
theorem finprod_mem_union'
  statement: (hst : Disjoint s t) (hs : (s inter mulSupport f).Finite)
  proof: by
  rw [← finprod_mem_union_inter' hs ht]; rw [disjoint_iff_inter_eq_empty.1 hst]; rw [finprod_mem_empty]; rw [mul_one]

中文:
定理 finprod_mem_union'
  结论: (hst : Disjoint s t) (hs : (s inter mulSupport f).Finite)
  证明: by
  rw [← finprod_mem_union_inter' hs ht]; rw [disjoint_iff_inter_eq_empty.1 hst]; rw [finprod_mem_empty]; rw [mul_one]

Depends on / 依赖: disjoint_iff_inter_eq_empty, finprod_mem_empty, finprod_mem_union_inter, mul_one
-/
theorem finprod_mem_union' (hst : Disjoint s t) (hs : (s inter mulSupport f).Finite)
    (ht : (t inter mulSupport f).Finite) : ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i := by
  rw [← finprod_mem_union_inter' hs ht]; rw [disjoint_iff_inter_eq_empty.1 hst]; rw [finprod_mem_empty]; rw [mul_one]

/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive
      /-- Given two finite disjoint sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` equals
      the sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`. -/]
/--
theorem `finprod_mem_union` / 定理 `finprod_mem_union`

English:
theorem finprod_mem_union
  given: (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite)
  proof: finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

中文:
定理 finprod_mem_union
  条件: (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite)
  证明: finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

Depends on / 依赖: finprod_mem_union, hs.inter_of_left, ht.inter_of_left, inter_of_left
-/
theorem finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i :=
  finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

/-- A more general version of `finprod_mem_union'` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be disjoint -/
@[to_additive
      /-- A more general version of `finsum_mem_union'` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be disjoint -/]
/--
theorem `finprod_mem_union''` / 定理 `finprod_mem_union''`

English:
theorem finprod_mem_union''
  statement: (hst : Disjoint (s inter mulSupport f) (t inter mulSupport f))
  proof: by
  rw [← finprod_mem_inter_mulSupport f s]; rw [← finprod_mem_inter_mulSupport f t]; rw [←
    finprod_mem_union hst hs ht]; rw [← union_inter_distrib_right]; rw [finprod_mem_inter_mulSupport]

中文:
定理 finprod_mem_union''
  结论: (hst : Disjoint (s inter mulSupport f) (t inter mulSupport f))
  证明: by
  rw [← finprod_mem_inter_mulSupport f s]; rw [← finprod_mem_inter_mulSupport f t]; rw [←
    finprod_mem_union hst hs ht]; rw [← union_inter_distrib_right]; rw [finprod_mem_inter_mulSupport]

Depends on / 依赖: finprod_mem_inter_mulSupport, finprod_mem_union, union_inter_distrib_right
-/
theorem finprod_mem_union'' (hst : Disjoint (s inter mulSupport f) (t inter mulSupport f))
    (hs : (s inter mulSupport f).Finite) (ht : (t inter mulSupport f).Finite) :
    ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i := by
  rw [← finprod_mem_inter_mulSupport f s]; rw [← finprod_mem_inter_mulSupport f t]; rw [←
    finprod_mem_union hst hs ht]; rw [← union_inter_distrib_right]; rw [finprod_mem_inter_mulSupport]

/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive /-- The sum of `f i` over `i ∈ {a}` equals `f a`. -/]
/--
theorem `finprod_mem_singleton` / 定理 `finprod_mem_singleton`

English:
theorem finprod_mem_singleton
  statement: (∏ᶠ i in ({a} : Set α), f i) = f a
  proof: by
  rw [← Finset.coe_singleton]; rw [finprod_mem_coe_finset]; rw [Finset.prod_singleton]

@[to_additive (attr := simp)]

中文:
定理 finprod_mem_singleton
  结论: (∏ᶠ i in ({a} : Set α), f i) = f a
  证明: by
  rw [← Finset.coe_singleton]; rw [finprod_mem_coe_finset]; rw [Finset.prod_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.coe_singleton, Finset.prod_singleton, coe_singleton, finprod_mem_coe_finset, prod_singleton
-/
theorem finprod_mem_singleton : (∏ᶠ i in ({a} : Set α), f i) = f a := by
  rw [← Finset.coe_singleton]; rw [finprod_mem_coe_finset]; rw [Finset.prod_singleton]

@[to_additive (attr := simp)]
/--
theorem `finprod_cond_eq_left` / 定理 `finprod_cond_eq_left`

English:
theorem finprod_cond_eq_left
  statement: (∏ᶠ (i) (_ : i = a), f i) = f a
  proof: finprod_mem_singleton

@[to_additive (attr := simp)]

中文:
定理 finprod_cond_eq_left
  结论: (∏ᶠ (i) (_ : i = a), f i) = f a
  证明: finprod_mem_singleton

@[to_additive (attr := simp)]

Depends on / 依赖: finprod_mem_singleton
-/
theorem finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a :=
  finprod_mem_singleton

@[to_additive (attr := simp)]
/--
theorem `finprod_cond_eq_right` / 定理 `finprod_cond_eq_right`

English:
theorem finprod_cond_eq_right
  statement: (∏ᶠ (i) (_ : a = i), f i) = f a
  proof: by simp [@eq_comm _ a]

中文:
定理 finprod_cond_eq_right
  结论: (∏ᶠ (i) (_ : a = i), f i) = f a
  证明: by simp [@eq_comm _ a]

Depends on / 依赖: eq_comm
-/
theorem finprod_cond_eq_right : (∏ᶠ (i) (_ : a = i), f i) = f a := by simp [@eq_comm _ a]

/-- A more general version of `finprod_mem_insert` that requires `s ∩ mulSupport f` rather than `s`
to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_insert` that requires `s ∩ support f` rather
      than `s` to be finite. -/]
/--
theorem `finprod_mem_insert'` / 定理 `finprod_mem_insert'`

English:
theorem finprod_mem_insert'
  given: (f : α -> M) (h : a ∉ s) (hs : (s inter mulSupport f).Finite)
  proof: by
  rw [insert_eq]; rw [finprod_mem_union' _ _ hs]; rw [finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _

中文:
定理 finprod_mem_insert'
  条件: (f : α -> M) (h : a ∉ s) (hs : (s inter mulSupport f).Finite)
  证明: by
  rw [insert_eq]; rw [finprod_mem_union' _ _ hs]; rw [finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _

Depends on / 依赖: disjoint_singleton_left, finite_singleton, finprod_mem_singleton, finprod_mem_union, insert_eq, inter_of_left
-/
theorem finprod_mem_insert' (f : α -> M) (h : a ∉ s) (hs : (s inter mulSupport f).Finite) :
    ∏ᶠ i in insert a s, f i = f a * ∏ᶠ i in s, f i := by
  rw [insert_eq]; rw [finprod_mem_union' _ _ hs]; rw [finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _

/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s` and an element `a ∉ s`, the sum of `f i` over `i ∈ insert a s`
      equals `f a` plus the sum of `f i` over `i ∈ s`. -/]
/--
theorem `finprod_mem_insert` / 定理 `finprod_mem_insert`

English:
theorem finprod_mem_insert
  given: (f : α -> M) (h : a ∉ s) (hs : s.Finite)
  proof: finprod_mem_insert' f h hs.inter_of_left _

中文:
定理 finprod_mem_insert
  条件: (f : α -> M) (h : a ∉ s) (hs : s.Finite)
  证明: finprod_mem_insert' f h hs.inter_of_left _

Depends on / 依赖: finprod_mem_insert, hs.inter_of_left, inter_of_left
-/
theorem finprod_mem_insert (f : α -> M) (h : a ∉ s) (hs : s.Finite) :
    ∏ᶠ i in insert a s, f i = f a * ∏ᶠ i in s, f i :=
finprod_mem_insert' f h hs.inter_of_left _

/-- If `f a = 1` when `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the product of
`f i` over `i ∈ s`. -/
@[to_additive
      /-- If `f a = 0` when `a ∉ s`, then the sum of `f i` over `i ∈ insert a s` equals the sum
      of `f i` over `i ∈ s`. -/]
/--
theorem `finprod_mem_insert_of_eq_one_if_notMem` / 定理 `finprod_mem_insert_of_eq_one_if_notMem`

English:
theorem finprod_mem_insert_of_eq_one_if_notMem
  given: (h : a ∉ s -> f a = 1)
  proof: by
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨?_, Or.inr⟩
  rintro (rfl | hxs)
  exacts [not_imp_comm.1 h hx, hxs]

中文:
定理 finprod_mem_insert_of_eq_one_if_notMem
  条件: (h : a ∉ s -> f a = 1)
  证明: by
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨?_, Or.inr⟩
  rintro (rfl | hxs)
  exacts [not_imp_comm.1 h hx, hxs]

Depends on / 依赖: Or.inr, exacts, finprod_mem_inter_mulSupport_eq, not_imp_comm
-/
theorem finprod_mem_insert_of_eq_one_if_notMem (h : a ∉ s -> f a = 1) :
    ∏ᶠ i in insert a s, f i = ∏ᶠ i in s, f i := by
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨?_, Or.inr⟩
  rintro (rfl | hxs)
  exacts [not_imp_comm.1 h hx, hxs]

/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive
      /-- If `f a = 0`, then the sum of `f i` over `i ∈ insert a s` equals the sum of `f i`
      over `i ∈ s`. -/]
/--
theorem `finprod_mem_insert_one` / 定理 `finprod_mem_insert_one`

English:
theorem finprod_mem_insert_one
  given: (h : f a = 1)
  statement: ∏ᶠ i in insert a s, f i = ∏ᶠ i in s, f i
  proof: finprod_mem_insert_of_eq_one_if_notMem fun _ => h

中文:
定理 finprod_mem_insert_one
  条件: (h : f a = 1)
  结论: ∏ᶠ i in insert a s, f i = ∏ᶠ i in s, f i
  证明: finprod_mem_insert_of_eq_one_if_notMem fun _ => h

Depends on / 依赖: finprod_mem_insert_of_eq_one_if_notMem
-/
theorem finprod_mem_insert_one (h : f a = 1) : ∏ᶠ i in insert a s, f i = ∏ᶠ i in s, f i :=
  finprod_mem_insert_of_eq_one_if_notMem fun _ => h

/--
theorem `finprod_mem_dvd` / 定理 `finprod_mem_dvd`

English:
theorem finprod_mem_dvd
  given: {f : α -> N} (a : α) (hf : HasFiniteMulSupport f)
  statement: f a ∣ finprod f
  proof: by
  by_cases ha : a in mulSupport f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((Finite.mem_toFinset hf).mpr ha)
  · rw [notMem_mulSupport.mp ha]
    exact one_dvd (finprod f)

中文:
定理 finprod_mem_dvd
  条件: {f : α -> N} (a : α) (hf : HasFiniteMulSupport f)
  结论: f a ∣ finprod f
  证明: by
  by_cases ha : a in mulSupport f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((Finite.mem_toFinset hf).mpr ha)
  · rw [notMem_mulSupport.mp ha]
    exact one_dvd (finprod f)

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.dvd_prod_of_mem, Set.Subset.refl, Subset, dvd_prod_of_mem, finprod, finprod_eq_prod_of_mulSupport_toFinset_subset, mem_toFinset, mulSupport, notMem_mulSupport, notMem_mulSupport.mp, one_dvd
-/
theorem finprod_mem_dvd {f : α -> N} (a : α) (hf : HasFiniteMulSupport f) : f a ∣ finprod f := by
  by_cases ha : a in mulSupport f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((Finite.mem_toFinset hf).mpr ha)
  · rw [notMem_mulSupport.mp ha]
    exact one_dvd (finprod f)

/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive /-- The sum of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a + f b`. -/]
/--
theorem `finprod_mem_pair` / 定理 `finprod_mem_pair`

English:
theorem finprod_mem_pair
  given: (h : a != b)
  statement: (∏ᶠ i in ({a, b} : Set α), f i) = f a * f b
  proof: by
  rw [finprod_mem_insert]; rw [finprod_mem_singleton]
  exacts [h, finite_singleton b]

中文:
定理 finprod_mem_pair
  条件: (h : a != b)
  结论: (∏ᶠ i in ({a, b} : Set α), f i) = f a * f b
  证明: by
  rw [finprod_mem_insert]; rw [finprod_mem_singleton]
  exacts [h, finite_singleton b]

Depends on / 依赖: exacts, finite_singleton, finprod_mem_insert, finprod_mem_singleton
-/
theorem finprod_mem_pair (h : a != b) : (∏ᶠ i in ({a, b} : Set α), f i) = f a * f b := by
  rw [finprod_mem_insert]; rw [finprod_mem_singleton]
  exacts [h, finite_singleton b]

set_option backward.isDefEq.respectTransparency false in
/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mulSupport (f ∘ g)`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      `g` is injective on `s ∩ support (f ∘ g)`. -/]
/--
theorem `finprod_mem_image'` / 定理 `finprod_mem_image'`

English:
theorem finprod_mem_image'
  given: {s : Set β} {g : β -> α} (hg : (s inter mulSupport (f ∘ g)).InjOn g)
  proof: by
  classical
    by_cases hs : (s inter mulSupport (f ∘ g)).Finite
    · have hg : forall x in hs.toFinset, forall y in hs.toFinset, g x = g y -> x = y := by
        simpa only [hs.mem_toFinset]
      have := finprod_mem_eq_prod (comp f g) hs
      unfold Function.comp at this
      rw [this]; rw 

中文:
定理 finprod_mem_image'
  条件: {s : Set β} {g : β -> α} (hg : (s inter mulSupport (f ∘ g)).InjOn g)
  证明: by
  classical
    by_cases hs : (s inter mulSupport (f ∘ g)).Finite
    · have hg : forall x in hs.toFinset, forall y in hs.toFinset, g x = g y -> x = y := by
        simpa only [hs.mem_toFinset]
      have := finprod_mem_eq_prod (comp f g) hs
      unfold Function.comp at this
      rw [this]; rw 

Depends on / 依赖: Finite, Finset, Finset.coe_image, Finset.prod_image, Function, Function.comp, classical, coe_image, coe_toFinset, finprod_me, finprod_mem_eq_prod, finprod_mem_eq_prod_of_inter_mulSupport_eq, hs.coe_toFinset, hs.mem_toFinset, hs.toFinset, image_inter_mulSupport_eq, inter_assoc, inter_self, mem_toFinset, mulSupport
-/
theorem finprod_mem_image' {s : Set β} {g : β -> α} (hg : (s inter mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j) := by
  classical
    by_cases hs : (s inter mulSupport (f ∘ g)).Finite
    · have hg : forall x in hs.toFinset, forall y in hs.toFinset, g x = g y -> x = y := by
        simpa only [hs.mem_toFinset]
      have := finprod_mem_eq_prod (comp f g) hs
      unfold Function.comp at this
      rw [this]; rw [← Finset.prod_image hg]
      refine finprod_mem_eq_prod_of_inter_mulSupport_eq f ?_
      rw [Finset.coe_image]; rw [hs.coe_toFinset]; rw [← image_inter_mulSupport_eq]; rw [inter_assoc]; rw [inter_self]
    · unfold Function.comp at hs
      rw [finprod_mem_eq_one_of_infinite hs]; rw [finprod_mem_eq_one_of_infinite]
      rwa [image_inter_mulSupport_eq, infinite_image_iff hg]

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s` provided that
`g` is injective on `s`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      `g` is injective on `s`. -/]
/--
theorem `finprod_mem_image` / 定理 `finprod_mem_image`

English:
theorem finprod_mem_image
  given: {s : Set β} {g : β -> α} (hg : s.InjOn g)
  proof: finprod_mem_image' hg.mono inter_subset_left

中文:
定理 finprod_mem_image
  条件: {s : Set β} {g : β -> α} (hg : s.InjOn g)
  证明: finprod_mem_image' hg.mono inter_subset_left

Depends on / 依赖: finprod_mem_image, hg.mono, inter_subset_left
-/
theorem finprod_mem_image {s : Set β} {g : β -> α} (hg : s.InjOn g) :
    ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j) :=
finprod_mem_image' hg.mono inter_subset_left

/-- The product of `f y` over `y ∈ Set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mulSupport (f ∘ g)`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ Set.range g` equals the sum of `f (g i)` over all `i`
      provided that `g` is injective on `support (f ∘ g)`. -/]
/--
theorem `finprod_mem_range'` / 定理 `finprod_mem_range'`

English:
theorem finprod_mem_range'
  given: {g : β -> α} (hg : (mulSupport (f ∘ g)).InjOn g)
  proof: by
  rw [← image_univ]; rw [finprod_mem_image']; rw [finprod_mem_univ]
  rwa [univ_inter]

中文:
定理 finprod_mem_range'
  条件: {g : β -> α} (hg : (mulSupport (f ∘ g)).InjOn g)
  证明: by
  rw [← image_univ]; rw [finprod_mem_image']; rw [finprod_mem_univ]
  rwa [univ_inter]

Depends on / 依赖: finprod_mem_image, finprod_mem_univ, image_univ, univ_inter
-/
theorem finprod_mem_range' {g : β -> α} (hg : (mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i in range g, f i = ∏ᶠ j, f (g j) := by
  rw [← image_univ]; rw [finprod_mem_image']; rw [finprod_mem_univ]
  rwa [univ_inter]

/-- The product of `f y` over `y ∈ Set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ Set.range g` equals the sum of `f (g i)` over all `i`
      provided that `g` is injective. -/]
/--
theorem `finprod_mem_range` / 定理 `finprod_mem_range`

English:
theorem finprod_mem_range
  given: {g : β -> α} (hg : Injective g)
  statement: ∏ᶠ i in range g, f i = ∏ᶠ j, f (g j)
  proof: finprod_mem_range' hg.injOn

中文:
定理 finprod_mem_range
  条件: {g : β -> α} (hg : Injective g)
  结论: ∏ᶠ i in range g, f i = ∏ᶠ j, f (g j)
  证明: finprod_mem_range' hg.injOn

Depends on / 依赖: finprod_mem_range, hg.injOn
-/
theorem finprod_mem_range {g : β -> α} (hg : Injective g) : ∏ᶠ i in range g, f i = ∏ᶠ j, f (g j) :=
  finprod_mem_range' hg.injOn

/-- See also `Finset.prod_bij`. -/
@[to_additive /-- See also `Finset.sum_bij`. -/]
/--
theorem `finprod_mem_eq_of_bijOn` / 定理 `finprod_mem_eq_of_bijOn`

English:
theorem finprod_mem_eq_of_bijOn
  statement: {s : Set α} {t : Set β} {f : α -> M} {g : β -> M} (e : α -> β)
  proof: by
  rw [← Set.BijOn.image_eq he₀]; rw [finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁

中文:
定理 finprod_mem_eq_of_bijOn
  结论: {s : Set α} {t : Set β} {f : α -> M} {g : β -> M} (e : α -> β)
  证明: by
  rw [← Set.BijOn.image_eq he₀]; rw [finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁

Depends on / 依赖: Set.BijOn.image_eq, finprod_mem_congr, finprod_mem_image, image_eq
-/
theorem finprod_mem_eq_of_bijOn {s : Set α} {t : Set β} {f : α -> M} {g : β -> M} (e : α -> β)
    (he₀ : s.BijOn e t) (he₁ : forall x in s, f x = g (e x)) : ∏ᶠ i in s, f i = ∏ᶠ j in t, g j := by
  rw [← Set.BijOn.image_eq he₀]; rw [finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁

/-- See `finprod_comp`, `Fintype.prod_bijective` and `Finset.prod_bij`. -/
@[to_additive /-- See `finsum_comp`, `Fintype.sum_bijective` and `Finset.sum_bij`. -/]
/--
theorem `finprod_eq_of_bijective` / 定理 `finprod_eq_of_bijective`

English:
theorem finprod_eq_of_bijective
  statement: {f : α -> M} {g : β -> M} (e : α -> β) (he₀ : Bijective e)
  proof: by
  rw [← finprod_mem_univ f]; rw [← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ he₀.bijOn_univ fun x _ => he₁ x

中文:
定理 finprod_eq_of_bijective
  结论: {f : α -> M} {g : β -> M} (e : α -> β) (he₀ : Bijective e)
  证明: by
  rw [← finprod_mem_univ f]; rw [← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ he₀.bijOn_univ fun x _ => he₁ x

Depends on / 依赖: bijOn_univ, finprod_mem_eq_of_bijOn, finprod_mem_univ
-/
theorem finprod_eq_of_bijective {f : α -> M} {g : β -> M} (e : α -> β) (he₀ : Bijective e)
    (he₁ : forall x, f x = g (e x)) : ∏ᶠ i, f i = ∏ᶠ j, g j := by
  rw [← finprod_mem_univ f]; rw [← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ he₀.bijOn_univ fun x _ => he₁ x

/-- See also `finprod_eq_of_bijective`, `Fintype.prod_bijective` and `Finset.prod_bij`. -/
@[to_additive
/-- See also `finsum_eq_of_bijective`, `Fintype.sum_bijective` and `Finset.sum_bij`. -/]
/--
theorem `finprod_comp` / 定理 `finprod_comp`

English:
theorem finprod_comp
  given: {g : β -> M} (e : α -> β) (he₀ : Function.Bijective e)
  proof: finprod_eq_of_bijective e he₀ fun _ => rfl

@[to_additive]

中文:
定理 finprod_comp
  条件: {g : β -> M} (e : α -> β) (he₀ : Function.Bijective e)
  证明: finprod_eq_of_bijective e he₀ fun _ => rfl

@[to_additive]

Depends on / 依赖: finprod_eq_of_bijective
-/
theorem finprod_comp {g : β -> M} (e : α -> β) (he₀ : Function.Bijective e) :
    (∏ᶠ i, g (e i)) = ∏ᶠ j, g j :=
  finprod_eq_of_bijective e he₀ fun _ => rfl

@[to_additive]
/--
theorem `finprod_comp_equiv` / 定理 `finprod_comp_equiv`

English:
theorem finprod_comp_equiv
  given: (e : α ≃ β) {f : β -> M}
  statement: (∏ᶠ i, f (e i)) = ∏ᶠ i', f i'
  proof: finprod_comp e e.bijective

@[to_additive]

中文:
定理 finprod_comp_equiv
  条件: (e : α ≃ β) {f : β -> M}
  结论: (∏ᶠ i, f (e i)) = ∏ᶠ i', f i'
  证明: finprod_comp e e.bijective

@[to_additive]

Depends on / 依赖: bijective, e.bijective, finprod_comp
-/
theorem finprod_comp_equiv (e : α ≃ β) {f : β -> M} : (∏ᶠ i, f (e i)) = ∏ᶠ i', f i' :=
  finprod_comp e e.bijective

@[to_additive]
/--
theorem `finprod_set_coe_eq_finprod_mem` / 定理 `finprod_set_coe_eq_finprod_mem`

English:
theorem finprod_set_coe_eq_finprod_mem
  given: (s : Set α)
  statement: ∏ᶠ j : s, f j = ∏ᶠ i in s, f i
  proof: by
  rw [← finprod_mem_range]; rw [Subtype.range_coe]
  exact Subtype.coe_injective

@[to_additive]

中文:
定理 finprod_set_coe_eq_finprod_mem
  条件: (s : Set α)
  结论: ∏ᶠ j : s, f j = ∏ᶠ i in s, f i
  证明: by
  rw [← finprod_mem_range]; rw [Subtype.range_coe]
  exact Subtype.coe_injective

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_injective, Subtype.range_coe, coe_injective, finprod_mem_range, range_coe
-/
theorem finprod_set_coe_eq_finprod_mem (s : Set α) : ∏ᶠ j : s, f j = ∏ᶠ i in s, f i := by
  rw [← finprod_mem_range]; rw [Subtype.range_coe]
  exact Subtype.coe_injective

@[to_additive]
/--
theorem `finprod_subtype_eq_finprod_cond` / 定理 `finprod_subtype_eq_finprod_cond`

English:
theorem finprod_subtype_eq_finprod_cond
  given: (p : α -> Prop)
  proof: finprod_set_coe_eq_finprod_mem { i | p i }

@[to_additive]

中文:
定理 finprod_subtype_eq_finprod_cond
  条件: (p : α -> 命题)
  证明: finprod_set_coe_eq_finprod_mem { i | p i }

@[to_additive]

Depends on / 依赖: finprod_set_coe_eq_finprod_mem
-/
theorem finprod_subtype_eq_finprod_cond (p : α -> Prop) :
    ∏ᶠ j : Subtype p, f j = ∏ᶠ (i) (_ : p i), f i :=
  finprod_set_coe_eq_finprod_mem { i | p i }

@[to_additive]
/--
theorem `finprod_mem_inter_mul_sdiff'` / 定理 `finprod_mem_inter_mul_sdiff'`

English:
theorem finprod_mem_inter_mul_sdiff'
  given: (t : Set α) (h : (s inter mulSupport f).Finite)
  proof: by
  rw [← finprod_mem_union']; rw [inter_union_sdiff]
  · rw [disjoint_iff_inf_le]
    exact fun x hx => hx.2.2 hx.1.2
  exacts [h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff' := finprod_mem_inter_mu

中文:
定理 finprod_mem_inter_mul_sdiff'
  条件: (t : Set α) (h : (s inter mulSupport f).Finite)
  证明: by
  rw [← finprod_mem_union']; rw [inter_union_sdiff]
  · rw [disjoint_iff_inf_le]
    exact fun x hx => hx.2.2 hx.1.2
  exacts [h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff' := finprod_mem_inter_mu

Depends on / 依赖: disjoint_iff_inf_le, exacts, finprod_mem_union, h.subset, inter_union_sdiff, subset
-/
theorem finprod_mem_inter_mul_sdiff' (t : Set α) (h : (s inter mulSupport f).Finite) :
    ((∏ᶠ i in s inter t, f i) * ∏ᶠ i in s \ t, f i) = ∏ᶠ i in s, f i := by
  rw [← finprod_mem_union']; rw [inter_union_sdiff]
  · rw [disjoint_iff_inf_le]
    exact fun x hx => hx.2.2 hx.1.2
  exacts [h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff' := finprod_mem_inter_mul_sdiff'

@[to_additive]
/--
theorem `finprod_mem_inter_mul_sdiff` / 定理 `finprod_mem_inter_mul_sdiff`

English:
theorem finprod_mem_inter_mul_sdiff
  given: (t : Set α) (h : s.Finite)
  proof: finprod_mem_inter_mul_sdiff' _ h.inter_of_left _

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff := finprod_mem_inter_mul_sdiff

中文:
定理 finprod_mem_inter_mul_sdiff
  条件: (t : Set α) (h : s.Finite)
  证明: finprod_mem_inter_mul_sdiff' _ h.inter_of_left _

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff := finprod_mem_inter_mul_sdiff

Depends on / 依赖: finprod_mem_inter_mul_sdiff, h.inter_of_left, inter_of_left
-/
theorem finprod_mem_inter_mul_sdiff (t : Set α) (h : s.Finite) :
    ((∏ᶠ i in s inter t, f i) * ∏ᶠ i in s \ t, f i) = ∏ᶠ i in s, f i :=
finprod_mem_inter_mul_sdiff' _ h.inter_of_left _

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff := finprod_mem_inter_mul_sdiff

/-- A more general version of `finprod_mem_mul_diff` that requires `t ∩ mulSupport f` rather than
`t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_add_diff` that requires `t ∩ support f` rather
      than `t` to be finite. -/]
/--
theorem `finprod_mem_mul_sdiff'` / 定理 `finprod_mem_mul_sdiff'`

English:
theorem finprod_mem_mul_sdiff'
  given: (hst : s subseteq t) (ht : (t inter mulSupport f).Finite)
  proof: by
  rw [← finprod_mem_inter_mul_sdiff' _ ht]; rw [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff' := finprod_mem_mul_sdiff'

中文:
定理 finprod_mem_mul_sdiff'
  条件: (hst : s subseteq t) (ht : (t inter mulSupport f).Finite)
  证明: by
  rw [← finprod_mem_inter_mul_sdiff' _ ht]; rw [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff' := finprod_mem_mul_sdiff'

Depends on / 依赖: finprod_mem_inter_mul_sdiff, inter_eq_self_of_subset_right
-/
theorem finprod_mem_mul_sdiff' (hst : s subseteq t) (ht : (t inter mulSupport f).Finite) :
    ((∏ᶠ i in s, f i) * ∏ᶠ i in t \ s, f i) = ∏ᶠ i in t, f i := by
  rw [← finprod_mem_inter_mul_sdiff' _ ht]; rw [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff' := finprod_mem_mul_sdiff'

/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive
      /-- Given a finite set `t` and a subset `s` of `t`, the sum of `f i` over `i ∈ s` plus
      the sum of `f i` over `t \ s` equals the sum of `f i` over `i ∈ t`. -/]
/--
theorem `finprod_mem_mul_sdiff` / 定理 `finprod_mem_mul_sdiff`

English:
theorem finprod_mem_mul_sdiff
  given: (hst : s subseteq t) (ht : t.Finite)
  proof: finprod_mem_mul_sdiff' hst (ht.inter_of_left _)

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff := finprod_mem_mul_sdiff

中文:
定理 finprod_mem_mul_sdiff
  条件: (hst : s subseteq t) (ht : t.Finite)
  证明: finprod_mem_mul_sdiff' hst (ht.inter_of_left _)

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff := finprod_mem_mul_sdiff

Depends on / 依赖: finprod_mem_mul_sdiff, ht.inter_of_left, inter_of_left
-/
theorem finprod_mem_mul_sdiff (hst : s subseteq t) (ht : t.Finite) :
    ((∏ᶠ i in s, f i) * ∏ᶠ i in t \ s, f i) = ∏ᶠ i in t, f i :=
  finprod_mem_mul_sdiff' hst (ht.inter_of_left _)

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff := finprod_mem_mul_sdiff

/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the product of
`f a` over the union `⋃ i, t i` is equal to the product over all indexes `i` of the products of
`f a` over `a ∈ t i`. -/
@[to_additive
      /-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the
      sum of `f a` over the union `⋃ i, t i` is equal to the sum over all indexes `i` of the
      sums of `f a` over `a ∈ t i`. -/]
/--
theorem `finprod_mem_iUnion` / 定理 `finprod_mem_iUnion`

English:
theorem finprod_mem_iUnion
  statement: [Finite ι] {t : ι -> Set α} (h : Pairwise (Disjoint on t))
  proof: by
  cases nonempty_fintype ι
  lift t to ι -> Finset α using ht
  classical
    rw [← biUnion_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_biUnion]; rw [finprod_mem_coe_finset]; rw [Finset.prod_biUnion]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ 

中文:
定理 finprod_mem_iUnion
  结论: [Finite ι] {t : ι -> Set α} (h : Pairwise (Disjoint on t))
  证明: by
  cases nonempty_fintype ι
  lift t to ι -> Finset α using ht
  classical
    rw [← biUnion_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_biUnion]; rw [finprod_mem_coe_finset]; rw [Finset.prod_biUnion]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ 

Depends on / 依赖: Finset, Finset.coe_biUnion, Finset.coe_univ, Finset.disjoint_coe, Finset.prod_biUnion, biUnion_univ, classical, coe_biUnion, coe_univ, disjoint_coe, finprod_eq_prod_of_fintype, finprod_mem_coe_finset, nonempty_fintype, prod_biUnion
-/
theorem finprod_mem_iUnion [Finite ι] {t : ι -> Set α} (h : Pairwise (Disjoint on t))
    (ht : forall i, (t i).Finite) : ∏ᶠ a in ⋃ i : ι, t i, f a = ∏ᶠ i, ∏ᶠ a in t i, f a := by
  cases nonempty_fintype ι
  lift t to ι -> Finset α using ht
  classical
    rw [← biUnion_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_biUnion]; rw [finprod_mem_coe_finset]; rw [Finset.prod_biUnion]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ hxy => Finset.disjoint_coe.1 (h hxy)

/-- Given a family of sets `t : ι → Set α`, a finite set `I` in the index type such that all sets
`t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the product of `f a`
over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I` of the products of `f a` over
`a ∈ t i`. -/
@[to_additive
      /-- Given a family of sets `t : ι → Set α`, a finite set `I` in the index type such that
      all sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the
      sum of `f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the sum over `i ∈ I` of the sums of `f a`
      over `a ∈ t i`. -/]
/--
theorem `finprod_mem_biUnion` / 定理 `finprod_mem_biUnion`

English:
theorem finprod_mem_biUnion
  statement: {I : Set ι} {t : ι -> Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
  proof: by
  have := hI.fintype
  rw [biUnion_eq_iUnion]; rw [finprod_mem_iUnion]; rw [← finprod_set_coe_eq_finprod_mem]
  exacts [fun x y hxy => h x.2 y.2 (Subtype.coe_injective.ne hxy), fun b => ht b b.2]

中文:
定理 finprod_mem_biUnion
  结论: {I : Set ι} {t : ι -> Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
  证明: by
  have := hI.fintype
  rw [biUnion_eq_iUnion]; rw [finprod_mem_iUnion]; rw [← finprod_set_coe_eq_finprod_mem]
  exacts [fun x y hxy => h x.2 y.2 (Subtype.coe_injective.ne hxy), fun b => ht b b.2]

Depends on / 依赖: Subtype, Subtype.coe_injective.ne, biUnion_eq_iUnion, coe_injective, exacts, finprod_mem_iUnion, finprod_set_coe_eq_finprod_mem, fintype, hI.fintype
-/
theorem finprod_mem_biUnion {I : Set ι} {t : ι -> Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
    (ht : forall i in I, (t i).Finite) : ∏ᶠ a in ⋃ x in I, t x, f a = ∏ᶠ i in I, ∏ᶠ j in t i, f j := by
  have := hI.fintype
  rw [biUnion_eq_iUnion]; rw [finprod_mem_iUnion]; rw [← finprod_set_coe_eq_finprod_mem]
  exacts [fun x y hxy => h x.2 y.2 (Subtype.coe_injective.ne hxy), fun b => ht b b.2]

/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive
      /-- If `t` is a finite set of pairwise disjoint finite sets, then the sum of `f a` over
      `a ∈ ⋃₀ t` is the sum over `s ∈ t` of the sums of `f a` over `a ∈ s`. -/]
/--
theorem `finprod_mem_sUnion` / 定理 `finprod_mem_sUnion`

English:
theorem finprod_mem_sUnion
  statement: {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
  proof: by
  rw [Set.sUnion_eq_biUnion]
  exact finprod_mem_biUnion h ht₀ ht₁

@[to_additive]

中文:
定理 finprod_mem_sUnion
  结论: {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
  证明: by
  rw [Set.sUnion_eq_biUnion]
  exact finprod_mem_biUnion h ht₀ ht₁

@[to_additive]

Depends on / 依赖: Set.sUnion_eq_biUnion, finprod_mem_biUnion, sUnion_eq_biUnion
-/
theorem finprod_mem_sUnion {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
    (ht₁ : forall x in t, Set.Finite x) : ∏ᶠ a in ⋃₀ t, f a = ∏ᶠ s in t, ∏ᶠ a in s, f a := by
  rw [Set.sUnion_eq_biUnion]
  exact finprod_mem_biUnion h ht₀ ht₁

@[to_additive]
/--
lemma `finprod_option` / 引理 `finprod_option`

English:
lemma finprod_option
  given: {f : Option α -> M} (hf : HasFiniteMulSupport (f ∘ some))
  proof: by
  replace hf : (mulSupport f).Finite := by simpa [finite_option]
  convert!
    finprod_mem_insert' f (show none ∉ Set.range Option.some by simp) (hf.subset inter_subset_right)
  · simp
  · rw [finprod_mem_range]
    exact Option.some_injective _

@[to_additive]

中文:
引理 finprod_option
  条件: {f : Option α -> M} (hf : HasFiniteMulSupport (f ∘ some))
  证明: by
  replace hf : (mulSupport f).Finite := by simpa [finite_option]
  convert!
    finprod_mem_insert' f (show none ∉ Set.range Option.some by simp) (hf.subset inter_subset_right)
  · simp
  · rw [finprod_mem_range]
    exact Option.some_injective _

@[to_additive]

Depends on / 依赖: Finite, Option.some, Option.some_injective, Set.range, convert, finite_option, finprod_mem_insert, finprod_mem_range, hf.subset, inter_subset_right, mulSupport, replace, some_injective, subset
-/
lemma finprod_option {f : Option α -> M} (hf : HasFiniteMulSupport (f ∘ some)) :
    ∏ᶠ o, f o = f none * ∏ᶠ a, f (some a) := by
  replace hf : (mulSupport f).Finite := by simpa [finite_option]
  convert!
    finprod_mem_insert' f (show none ∉ Set.range Option.some by simp) (hf.subset inter_subset_right)
  · simp
  · rw [finprod_mem_range]
    exact Option.some_injective _

@[to_additive]
/--
lemma `finprod_mem_powerset_insert` / 引理 `finprod_mem_powerset_insert`

English:
lemma finprod_mem_powerset_insert
  statement: {f : Set α -> M} {s : Set α} {a : α} (hs : s.Finite)
  proof: by
  rw [Set.powerset_insert]; rw [finprod_mem_union (disjoint_powerset_insert has) hs.powerset (hs.powerset.image (insert a))]; rw [finprod_mem_image (powerset_insert_injOn has)]

@[to_additive]

中文:
引理 finprod_mem_powerset_insert
  结论: {f : Set α -> M} {s : Set α} {a : α} (hs : s.Finite)
  证明: by
  rw [Set.powerset_insert]; rw [finprod_mem_union (disjoint_powerset_insert has) hs.powerset (hs.powerset.image (insert a))]; rw [finprod_mem_image (powerset_insert_injOn has)]

@[to_additive]

Depends on / 依赖: Set.powerset_insert, disjoint_powerset_insert, finprod_mem_image, finprod_mem_union, hs.powerset, hs.powerset.image, insert, powerset, powerset_insert, powerset_insert_injOn
-/
lemma finprod_mem_powerset_insert {f : Set α -> M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∉ s) : ∏ᶠ t in 𝒫 insert a s, f t = (∏ᶠ t in 𝒫 s, f t) * ∏ᶠ t in 𝒫 s, f (insert a t) := by
  rw [Set.powerset_insert]; rw [finprod_mem_union (disjoint_powerset_insert has) hs.powerset (hs.powerset.image (insert a))]; rw [finprod_mem_image (powerset_insert_injOn has)]

@[to_additive]
/--
lemma `finprod_mem_powerset_sdiff_elem` / 引理 `finprod_mem_powerset_sdiff_elem`

English:
lemma finprod_mem_powerset_sdiff_elem
  statement: {f : Set α -> M} {s : Set α} {a : α} (hs : s.Finite)
  proof: by
  nth_rw 1 2 [← Set.insert_sdiff_self_of_mem has] -- second appearance hidden by notation
  exact finprod_mem_powerset_insert (hs.subset Set.sdiff_subset)
    (notMem_sdiff_of_mem (Set.mem_singleton a))

@[deprecated (since := "2026-06-03")]
alias finprod_mem_powerset_diff_elem := finprod_mem_pow

中文:
引理 finprod_mem_powerset_sdiff_elem
  结论: {f : Set α -> M} {s : Set α} {a : α} (hs : s.Finite)
  证明: by
  nth_rw 1 2 [← Set.insert_sdiff_self_of_mem has] -- second appearance hidden by notation
  exact finprod_mem_powerset_insert (hs.subset Set.sdiff_subset)
    (notMem_sdiff_of_mem (Set.mem_singleton a))

@[deprecated (since := "2026-06-03")]
alias finprod_mem_powerset_diff_elem := finprod_mem_pow

Depends on / 依赖: Set.insert_sdiff_self_of_mem, Set.mem_singleton, Set.sdiff_subset, appearance, finprod_mem_powerset_insert, hidden, hs.subset, insert_sdiff_self_of_mem, mem_singleton, notMem_sdiff_of_mem, notation, nth_rw, sdiff_subset, second, subset
-/
lemma finprod_mem_powerset_sdiff_elem {f : Set α -> M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a in s) : ∏ᶠ t in 𝒫 s, f t = (∏ᶠ t in 𝒫 (s \ {a}), f t)
    * ∏ᶠ t in 𝒫 (s \ {a}), f (insert a t) := by
  nth_rw 1 2 [← Set.insert_sdiff_self_of_mem has] -- second appearance hidden by notation
  exact finprod_mem_powerset_insert (hs.subset Set.sdiff_subset)
    (notMem_sdiff_of_mem (Set.mem_singleton a))

@[deprecated (since := "2026-06-03")]
alias finprod_mem_powerset_diff_elem := finprod_mem_powerset_sdiff_elem

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `mul_finprod_cond_ne` / 定理 `mul_finprod_cond_ne`

English:
theorem mul_finprod_cond_ne
  given: (a : α) (hf : HasFiniteMulSupport f)
  proof: by
  classical
    rw [finprod_eq_prod _ hf]
    have h : forall x : α, f x != 1 -> (x != a ↔ x in hf.toFinset \ {a}) := by
      intro x hx
      rw [Finset.mem_sdiff]; rw [Finset.mem_singleton]; rw [Finite.mem_toFinset]; rw [mem_mulSupport]
      grind
    rw [finprod_cond_eq_prod_of_cond_iff f (f

中文:
定理 mul_finprod_cond_ne
  条件: (a : α) (hf : HasFiniteMulSupport f)
  证明: by
  classical
    rw [finprod_eq_prod _ hf]
    have h : forall x : α, f x != 1 -> (x != a ↔ x in hf.toFinset \ {a}) := by
      intro x hx
      rw [Finset.mem_sdiff]; rw [Finset.mem_singleton]; rw [Finite.mem_toFinset]; rw [mem_mulSupport]
      grind
    rw [finprod_cond_eq_prod_of_cond_iff f (f

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.mem_sdiff, Finset.mem_singleton, Finset.mul_prod_erase, Finset.prod_, Finset.sdiff_singleton_eq_erase, classical, finprod_cond_eq_prod_of_cond_iff, finprod_eq_prod, hf.toFinset, mem_mulSupport, mem_sdiff, mem_singleton, mem_toFinset, mulSupport, mul_prod_erase, not_not, one_mul
-/
theorem mul_finprod_cond_ne (a : α) (hf : HasFiniteMulSupport f) :
    (f a * ∏ᶠ (i) (_ : i != a), f i) = ∏ᶠ i, f i := by
  classical
    rw [finprod_eq_prod _ hf]
    have h : forall x : α, f x != 1 -> (x != a ↔ x in hf.toFinset \ {a}) := by
      intro x hx
      rw [Finset.mem_sdiff]; rw [Finset.mem_singleton]; rw [Finite.mem_toFinset]; rw [mem_mulSupport]
      grind
    rw [finprod_cond_eq_prod_of_cond_iff f (fun hx => h _ hx)]; rw [Finset.sdiff_singleton_eq_erase]
    by_cases ha : a in mulSupport f
    · apply Finset.mul_prod_erase _ _ ((Finite.mem_toFinset _).mpr ha)
    · rw [mem_mulSupport, not_not] at ha
      rw [ha]; rw [one_mul]
      apply Finset.prod_erase _ ha

/-- If `s : Set α` and `t : Set β` are finite sets, then taking the product over `s` commutes with
taking the product over `t`. -/
@[to_additive
      /-- If `s : Set α` and `t : Set β` are finite sets, then summing over `s` commutes with
      summing over `t`. -/]
/--
theorem `finprod_mem_comm` / 定理 `finprod_mem_comm`

English:
theorem finprod_mem_comm
  given: {s : Set α} {t : Set β} (f : α -> β -> M) (hs : s.Finite) (ht : t.Finite)
  proof: by
  lift s to Finset α using hs; lift t to Finset β using ht
  simp only [finprod_mem_coe_finset]
  exact Finset.prod_comm

中文:
定理 finprod_mem_comm
  条件: {s : Set α} {t : Set β} (f : α -> β -> M) (hs : s.Finite) (ht : t.Finite)
  证明: by
  lift s to Finset α using hs; lift t to Finset β using ht
  simp only [finprod_mem_coe_finset]
  exact Finset.prod_comm

Depends on / 依赖: Finset, Finset.prod_comm, finprod_mem_coe_finset, prod_comm
-/
theorem finprod_mem_comm {s : Set α} {t : Set β} (f : α -> β -> M) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i in s, ∏ᶠ j in t, f i j) = ∏ᶠ j in t, ∏ᶠ i in s, f i j := by
  lift s to Finset α using hs; lift t to Finset β using ht
  simp only [finprod_mem_coe_finset]
  exact Finset.prod_comm

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on factors. -/
@[to_additive
      /-- To prove a property of a finite sum, it suffices to prove that the property is
      additive and holds on summands. -/]
/--
theorem `finprod_mem_induction` / 定理 `finprod_mem_induction`

English:
theorem finprod_mem_induction
  statement: (p : M -> Prop) (hp₀ : p 1) (hp₁ : forall x y, p x -> p y -> p (x * y))
  proof: finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ hp₂ x

中文:
定理 finprod_mem_induction
  结论: (p : M -> 命题) (hp₀ : p 1) (hp₁ : 对任意 x y, p x -> p y -> p (x * y))
  证明: finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ hp₂ x

Depends on / 依赖: finprod_induction
-/
theorem finprod_mem_induction (p : M -> Prop) (hp₀ : p 1) (hp₁ : forall x y, p x -> p y -> p (x * y))
    (hp₂ : forall x in s, p <| f x) : p (∏ᶠ i in s, f i) :=
finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ hp₂ x

/--
theorem `finprod_cond_nonneg` / 定理 `finprod_cond_nonneg`

English:
theorem finprod_cond_nonneg
  statement: {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  proof: finprod_nonneg fun x => finprod_nonneg hf x

@[to_additive]

中文:
定理 finprod_cond_nonneg
  结论: {R : 类型} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  证明: finprod_nonneg fun x => finprod_nonneg hf x

@[to_additive]

Depends on / 依赖: finprod_nonneg
-/
theorem finprod_cond_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {p : α -> Prop} {f : α -> R}
    (hf : forall x, p x -> 0 <= f x) : 0 <= ∏ᶠ (x) (_ : p x), f x :=
finprod_nonneg fun x => finprod_nonneg hf x

@[to_additive]
/--
theorem `single_le_finprod` / 定理 `single_le_finprod`

English:
theorem single_le_finprod
  statement: {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
  proof: by
  classical calc
      f i <= ∏ j in insert i hf.toFinset, f j :=
        Finset.single_le_prod' (fun j _ => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm

中文:
定理 single_le_finprod
  结论: {M : 类型} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
  证明: by
  classical calc
      f i <= ∏ j in insert i hf.toFinset, f j :=
        Finset.single_le_prod' (fun j _ => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm

Depends on / 依赖: Finset, Finset.mem_insert_self, Finset.single_le_prod, Finset.subset_insert, classical, finprod_eq_prod_of_mulSupport_toFinset_subset, hf.toFinset, insert, mem_insert_self, single_le_prod, subset_insert, toFinset
-/
theorem single_le_finprod {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    (i : α) {f : α -> M}
    (hf : HasFiniteMulSupport f) (h : forall j, 1 <= f j) : f i <= ∏ᶠ j, f j := by
  classical calc
      f i <= ∏ j in insert i hf.toFinset, f j :=
        Finset.single_le_prod' (fun j _ => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm

/--
theorem `finprod_eq_zero` / 定理 `finprod_eq_zero`

English:
theorem finprod_eq_zero
  statement: {M₀ : Type*} [CommMonoidWithZero M₀] (f : α -> M₀) (x : α) (hx : f x = 0)
  proof: by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (hf.mem_toFinset.2 ?_) hx
  simp [hx]

@[to_additive]

中文:
定理 finprod_eq_zero
  结论: {M₀ : 类型} [CommMonoidWithZero M₀] (f : α -> M₀) (x : α) (hx : f x = 0)
  证明: by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (hf.mem_toFinset.2 ?_) hx
  simp [hx]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_zero, finprod_eq_prod, hf.mem_toFinset, mem_toFinset, nontriviality, prod_eq_zero
-/
theorem finprod_eq_zero {M₀ : Type*} [CommMonoidWithZero M₀] (f : α -> M₀) (x : α) (hx : f x = 0)
    (hf : HasFiniteMulSupport f) : ∏ᶠ x, f x = 0 := by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (hf.mem_toFinset.2 ?_) hx
  simp [hx]

@[to_additive]
/--
theorem `finprod_prod_comm` / 定理 `finprod_prod_comm`

English:
theorem finprod_prod_comm
  statement: (s : Finset β) (f : α -> β -> M)
  proof: by
  have hU :
    (mulSupport fun a => ∏ b in s, f a b) subseteq
      (s.finite_toSet.biUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset := by
    rw [Finite.coe_toFinset]
    intro x hx
    simp only [exists_prop, mem_iUnion, Ne, mem_mulSupport, Finset.mem_coe]
    contrapose! hx
    rw [mem

中文:
定理 finprod_prod_comm
  结论: (s : Finset β) (f : α -> β -> M)
  证明: by
  have hU :
    (mulSupport fun a => ∏ b in s, f a b) subseteq
      (s.finite_toSet.biUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset := by
    rw [Finite.coe_toFinset]
    intro x hx
    simp only [exists_prop, mem_iUnion, Ne, mem_mulSupport, Finset.mem_coe]
    contrapose! hx
    rw [mem

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, Finset.mem_coe, Finset.prod_comm, Finset.prod_congr, Finset.prod_const_one, biUnion, coe_toFinset, contrapose, exists_prop, finite_toSet, finprod_eq_prod_of_mulSupport_subs, finprod_eq_prod_of_mulSupport_subset, mem_coe, mem_iUnion, mem_mulSupport, mulSupport, not_not, prod_comm
-/
theorem finprod_prod_comm (s : Finset β) (f : α -> β -> M)
    (h : forall b in s, HasFiniteMulSupport fun a => f a b) :
    (∏ᶠ a : α, ∏ b in s, f a b) = ∏ b in s, ∏ᶠ a : α, f a b := by
  have hU :
    (mulSupport fun a => ∏ b in s, f a b) subseteq
      (s.finite_toSet.biUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset := by
    rw [Finite.coe_toFinset]
    intro x hx
    simp only [exists_prop, mem_iUnion, Ne, mem_mulSupport, Finset.mem_coe]
    contrapose! hx
    rw [mem_mulSupport]; rw [not_not]; rw [Finset.prod_congr rfl hx]; rw [Finset.prod_const_one]
  rw [finprod_eq_prod_of_mulSupport_subset _ hU]; rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b hb => (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro a ha
  simp only [Finite.coe_toFinset, mem_iUnion]
  exact ⟨b, hb, ha⟩

@[to_additive]
/--
theorem `prod_finprod_comm` / 定理 `prod_finprod_comm`

English:
theorem prod_finprod_comm
  given: (s : Finset α) (f : α -> β -> M) (h : forall a in s, HasFiniteMulSupport (f a))
  proof: (finprod_prod_comm s (fun b a => f a b) h).symm

@[to_additive]

中文:
定理 prod_finprod_comm
  条件: (s : Finset α) (f : α -> β -> M) (h : 对任意 a in s, HasFiniteMulSupport (f a))
  证明: (finprod_prod_comm s (fun b a => f a b) h).symm

@[to_additive]

Depends on / 依赖: finprod_prod_comm
-/
theorem prod_finprod_comm (s : Finset α) (f : α -> β -> M) (h : forall a in s, HasFiniteMulSupport (f a)) :
    (∏ a in s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a in s, f a b :=
  (finprod_prod_comm s (fun b a => f a b) h).symm

@[to_additive]
/--
theorem `finprod_prod_filter` / 定理 `finprod_prod_filter`

English:
theorem finprod_prod_filter
  given: [DecidableEq α] (f : β -> α) (s : Finset β) (g : β -> M)
  proof: by
  rw [finprod_eq_finsetProd_of_mulSupport_subset]
  · rw [Finset.prod_image']
    exact fun _ _ => rfl
  · intro x hx
    rw [mem_mulSupport] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_one_of_prod_ne_one hx
    simp only [Finset.mem_filter, Finset.coe_image, mem_image, SetLike.mem_coe] at h ⊢

中文:
定理 finprod_prod_filter
  条件: [DecidableEq α] (f : β -> α) (s : Finset β) (g : β -> M)
  证明: by
  rw [finprod_eq_finsetProd_of_mulSupport_subset]
  · rw [Finset.prod_image']
    exact fun _ _ => rfl
  · intro x hx
    rw [mem_mulSupport] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_one_of_prod_ne_one hx
    simp only [Finset.mem_filter, Finset.coe_image, mem_image, SetLike.mem_coe] at h ⊢

Depends on / 依赖: Finset, Finset.coe_image, Finset.exists_ne_one_of_prod_ne_one, Finset.mem_filter, Finset.prod_image, SetLike, SetLike.mem_coe, coe_image, exists_ne_one_of_prod_ne_one, finprod_eq_finsetProd_of_mulSupport_subset, mem_coe, mem_filter, mem_image, mem_mulSupport, prod_image
-/
theorem finprod_prod_filter [DecidableEq α] (f : β -> α) (s : Finset β) (g : β -> M) :
    ∏ᶠ x, ∏ y in s with f y = x, g y = ∏ k in s, g k := by
  rw [finprod_eq_finsetProd_of_mulSupport_subset]
  · rw [Finset.prod_image']
    exact fun _ _ => rfl
  · intro x hx
    rw [mem_mulSupport] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_one_of_prod_ne_one hx
    simp only [Finset.mem_filter, Finset.coe_image, mem_image, SetLike.mem_coe] at h ⊢
    exact ⟨a, h⟩

/--
theorem `mul_finsum'` / 定理 `mul_finsum'`

English:
theorem mul_finsum'
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
  proof: (AddMonoidHom.mulLeft r).map_finsum h

中文:
定理 mul_finsum'
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
  证明: (AddMonoidHom.mulLeft r).map_finsum h

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, map_finsum, mulLeft
-/
theorem mul_finsum' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
    (h : HasFiniteSupport f) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum h

/--
theorem `mul_finsum_mem'` / 定理 `mul_finsum_mem'`

English:
theorem mul_finsum_mem'
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α -> R) (r : R)
  proof: (AddMonoidHom.mulLeft r).map_finsum_mem f hs

中文:
定理 mul_finsum_mem'
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α -> R) (r : R)
  证明: (AddMonoidHom.mulLeft r).map_finsum_mem f hs

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, map_finsum_mem, mulLeft
-/
theorem mul_finsum_mem' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α -> R) (r : R)
    (hs : s.Finite) : (r * ∑ᶠ a in s, f a) = ∑ᶠ a in s, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum_mem f hs

/--
theorem `finsum_mul'` / 定理 `finsum_mul'`

English:
theorem finsum_mul'
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
  proof: (AddMonoidHom.mulRight r).map_finsum h

中文:
定理 finsum_mul'
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
  证明: (AddMonoidHom.mulRight r).map_finsum h

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, map_finsum, mulRight
-/
theorem finsum_mul' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
    (h : HasFiniteSupport f) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum h

/--
theorem `finsum_mem_mul'` / 定理 `finsum_mem_mul'`

English:
theorem finsum_mem_mul'
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α -> R) (r : R)
  proof: (AddMonoidHom.mulRight r).map_finsum_mem f hs

中文:
定理 finsum_mem_mul'
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α -> R) (r : R)
  证明: (AddMonoidHom.mulRight r).map_finsum_mem f hs

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, map_finsum_mem, mulRight
-/
theorem finsum_mem_mul' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α -> R) (r : R)
    (hs : s.Finite) : (∑ᶠ a in s, f a) * r = ∑ᶠ a in s, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum_mem f hs

/--
theorem `mul_finsum` / 定理 `mul_finsum`

English:
theorem mul_finsum
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α -> R)
  proof: by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (r * f ·).support = f.support)]

中文:
定理 mul_finsum
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α -> R)
  证明: by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (r * f ·).support = f.support)]

Depends on / 依赖: Finite, HasFiniteSupport, classical, f.support, f.support.Finite, finsum_def, mul_finsum, support
-/
theorem mul_finsum {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α -> R)
    (r : R) :
    (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a := by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (r * f ·).support = f.support)]

/--
theorem `mul_finsum_mem` / 定理 `mul_finsum_mem`

English:
theorem mul_finsum_mem
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
  proof: by
  rw [mul_finsum]
  congr
  ext a
  by_cases h : a in s <;> simp_all

中文:
定理 mul_finsum_mem
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
  证明: by
  rw [mul_finsum]
  congr
  ext a
  by_cases h : a in s <;> simp_all

Depends on / 依赖: mul_finsum
-/
theorem mul_finsum_mem {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α -> R) (r : R) :
    (r * ∑ᶠ a in s, f a) = ∑ᶠ a in s, r * f a := by
  rw [mul_finsum]
  congr
  ext a
  by_cases h : a in s <;> simp_all

/--
theorem `finsum_mul` / 定理 `finsum_mul`

English:
theorem finsum_mul
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α -> R)
  proof: by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact finsum_mul' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (f · * r).support = f.support)]

中文:
定理 finsum_mul
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α -> R)
  证明: by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact finsum_mul' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (f · * r).support = f.support)]

Depends on / 依赖: Finite, HasFiniteSupport, classical, f.support, f.support.Finite, finsum_def, finsum_mul, support
-/
theorem finsum_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α -> R)
    (r : R) :
    (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r := by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact finsum_mul' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (f · * r).support = f.support)]

/--
theorem `finsum_mem_mul` / 定理 `finsum_mem_mul`

English:
theorem finsum_mem_mul
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
  proof: by
  rw [finsum_mul]
  congr
  ext a
  by_cases h : a in s <;> simp_all

中文:
定理 finsum_mem_mul
  结论: {R : 类型} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
  证明: by
  rw [finsum_mul]
  congr
  ext a
  by_cases h : a in s <;> simp_all

Depends on / 依赖: finsum_mul
-/
theorem finsum_mem_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α -> R) (r : R) :
    (∑ᶠ a in s, f a) * r = ∑ᶠ a in s, f a * r := by
  rw [finsum_mul]
  congr
  ext a
  by_cases h : a in s <;> simp_all

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `finprod_apply` / 引理 `finprod_apply`

English:
lemma finprod_apply
  given: {α ι : Type*} {f : ι -> α -> N} (hf : HasFiniteMulSupport f) (a : α)
  proof: by
  classical
  have hf' : HasFiniteMulSupport fun i => f i a := by fun_prop (disch := simp)
  simp only [finprod_def, dif_pos, hf, hf', Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop

@[to_additive]

中文:
引理 finprod_apply
  条件: {α ι : 类型} {f : ι -> α -> N} (hf : HasFiniteMulSupport f) (a : α)
  证明: by
  classical
  have hf' : HasFiniteMulSupport fun i => f i a := by fun_prop (disch := simp)
  simp only [finprod_def, dif_pos, hf, hf', Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_apply, Finset.prod_subset, HasFiniteMulSupport, classical, dif_pos, finprod_def, fun_prop, prod_apply, prod_subset
-/
lemma finprod_apply {α ι : Type*} {f : ι -> α -> N} (hf : HasFiniteMulSupport f) (a : α) :
    (∏ᶠ i, f i) a = ∏ᶠ i, f i a := by
  classical
  have hf' : HasFiniteMulSupport fun i => f i a := by fun_prop (disch := simp)
  simp only [finprod_def, dif_pos, hf, hf', Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop

@[to_additive]
/--
theorem `Finset.mulSupport_of_fiberwise_prod_subset_image` / 定理 `Finset.mulSupport_of_fiberwise_prod_subset_image`

English:
theorem Finset.mulSupport_of_fiberwise_prod_subset_image
  statement: [DecidableEq β] (s : Finset α) (f : α -> M)
  proof: by
  simp only [Finset.coe_image]
  intro b h
  suffices {a in s | g a = b}.Nonempty by
    simpa only [fiber_nonempty_iff_mem_image, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

中文:
定理 Finset.mulSupport_of_fiberwise_prod_subset_image
  结论: [DecidableEq β] (s : Finset α) (f : α -> M)
  证明: by
  simp only [Finset.coe_image]
  intro b h
  suffices {a in s | g a = b}.Nonempty by
    simpa only [fiber_nonempty_iff_mem_image, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

Depends on / 依赖: Finset, Finset.coe_image, Finset.mem_image, Finset.nonempty_of_prod_ne_one, Nonempty, coe_image, exists_prop, fiber_nonempty_iff_mem_image, mem_image, nonempty_of_prod_ne_one
-/
theorem Finset.mulSupport_of_fiberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α -> M)
    (g : α -> β) : (mulSupport fun b => ∏ a in s with g a = b, f a) subseteq s.image g := by
  simp only [Finset.coe_image]
  intro b h
  suffices {a in s | g a = b}.Nonempty by
    simpa only [fiber_nonempty_iff_mem_image, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

/-- Note that `b ∈ (s.filter (fun ab => Prod.fst ab = a)).image Prod.snd` iff `(a, b) ∈ s` so
we can simplify the right-hand side of this lemma. However the form stated here is more useful for
iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/
@[to_additive
      /-- Note that `b ∈ (s.filter (fun ab => Prod.fst ab = a)).image Prod.snd` iff `(a, b) ∈ s` so
      we can simplify the right-hand side of this lemma. However the form stated here is more
      useful for iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/]
/--
theorem `finprod_mem_finset_product'` / 定理 `finprod_mem_finset_product'`

English:
theorem finprod_mem_finset_product'
  statement: [DecidableEq α] [DecidableEq β] (s : Finset (α × β))
  proof: by
  have (a : _) :
      ∏ i in (s.filter fun ab => Prod.fst ab = a).image Prod.snd, f (a, i) =
        (s.filter (Prod.fst · = a)).prod f := by
    refine Finset.prod_nbij' (fun b => (a, b)) Prod.snd ?_ ?_ ?_ ?_ ?_ <;> aesop
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, 

中文:
定理 finprod_mem_finset_product'
  结论: [DecidableEq α] [DecidableEq β] (s : Finset (α × β))
  证明: by
  have (a : _) :
      ∏ i in (s.filter fun ab => Prod.fst ab = a).image Prod.snd, f (a, i) =
        (s.filter (Prod.fst · = a)).prod f := by
    refine Finset.prod_nbij' (fun b => (a, b)) Prod.snd ?_ ?_ ?_ ?_ ?_ <;> aesop
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, 

Depends on / 依赖: Finset, Finset.image, Finset.prod_fiberwise_of_maps_to, Finset.prod_nbij, Prod.fst, Prod.snd, filter, finprod_eq_prod_of_mulSupport_subset, finprod_mem_finset_eq_prod, mulSupport_of_fiberwise_prod_subset_image, prod_fiberwise_of_maps_to, prod_nbij, s.filter, s.mulSupport_of_fiberwise_prod_subset_image, simp_rw
-/
theorem finprod_mem_finset_product' [DecidableEq α] [DecidableEq β] (s : Finset (α × β))
    (f : α × β -> M) :
    (∏ᶠ (ab) (_ : ab in s), f ab) =
      ∏ᶠ (a) (b) (_ : b in (s.filter fun ab => Prod.fst ab = a).image Prod.snd), f (a, b) := by
  have (a : _) :
      ∏ i in (s.filter fun ab => Prod.fst ab = a).image Prod.snd, f (a, i) =
        (s.filter (Prod.fst · = a)).prod f := by
    refine Finset.prod_nbij' (fun b => (a, b)) Prod.snd ?_ ?_ ?_ ?_ ?_ <;> aesop
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, this]
  rw [finprod_eq_prod_of_mulSupport_subset _
      (s.mulSupport_of_fiberwise_prod_subset_image f Prod.fst)]; rw [← Finset.prod_fiberwise_of_maps_to (t := Finset.image Prod.fst s) _ f]
  -- `finish` could close the goal here
  simp only [Finset.mem_image]
  exact fun x hx => ⟨x, hx, rfl⟩

/-- See also `finprod_mem_finset_product'`. -/
@[to_additive /-- See also `finsum_mem_finset_product'`. -/]
/--
theorem `finprod_mem_finset_product` / 定理 `finprod_mem_finset_product`

English:
theorem finprod_mem_finset_product
  given: (s : Finset (α × β)) (f : α × β -> M)
  proof: by
  classical
    rw [finprod_mem_finset_product']
    simp

@[to_additive]

中文:
定理 finprod_mem_finset_product
  条件: (s : Finset (α × β)) (f : α × β -> M)
  证明: by
  classical
    rw [finprod_mem_finset_product']
    simp

@[to_additive]

Depends on / 依赖: classical, finprod_mem_finset_product
-/
theorem finprod_mem_finset_product (s : Finset (α × β)) (f : α × β -> M) :
    (∏ᶠ (ab) (_ : ab in s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) in s), f (a, b) := by
  classical
    rw [finprod_mem_finset_product']
    simp

@[to_additive]
/--
theorem `finprod_mem_finset_product₃` / 定理 `finprod_mem_finset_product₃`

English:
theorem finprod_mem_finset_product₃
  given: {γ : Type*} (s : Finset (α × β × γ)) (f : α × β × γ -> M)
  proof: by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp

中文:
定理 finprod_mem_finset_product₃
  条件: {γ : 类型} (s : Finset (α × β × γ)) (f : α × β × γ -> M)
  证明: by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp

Depends on / 依赖: classical, finprod_mem_finset_product, simp_rw
-/
theorem finprod_mem_finset_product₃ {γ : Type*} (s : Finset (α × β × γ)) (f : α × β × γ -> M) :
    (∏ᶠ (abc) (_ : abc in s), f abc) = ∏ᶠ (a) (b) (c) (_ : (a, b, c) in s), f (a, b, c) := by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `finprod_curry` / 定理 `finprod_curry`

English:
theorem finprod_curry
  given: (f : α × β -> M) (hf : HasFiniteMulSupport f)
  proof: by
  have h₁ : forall a, ∏ᶠ _ : a in hf.toFinset, f a = f a := by simp
  have h₂ : ∏ᶠ a, f a = ∏ᶠ (a) (_ : a in hf.toFinset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

@[to_additive]

中文:
定理 finprod_curry
  条件: (f : α × β -> M) (hf : HasFiniteMulSupport f)
  证明: by
  have h₁ : forall a, ∏ᶠ _ : a in hf.toFinset, f a = f a := by simp
  have h₂ : ∏ᶠ a, f a = ∏ᶠ (a) (_ : a in hf.toFinset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

@[to_additive]

Depends on / 依赖: finprod_mem_finset_product, hf.toFinset, simp_rw, toFinset
-/
theorem finprod_curry (f : α × β -> M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ ab, f ab = ∏ᶠ (a) (b), f (a, b) := by
  have h₁ : forall a, ∏ᶠ _ : a in hf.toFinset, f a = f a := by simp
  have h₂ : ∏ᶠ a, f a = ∏ᶠ (a) (_ : a in hf.toFinset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

@[to_additive]
/--
theorem `finprod_curry₃` / 定理 `finprod_curry₃`

English:
theorem finprod_curry₃
  given: {γ : Type*} (f : α × β × γ -> M) (h : HasFiniteMulSupport f)
  proof: by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]

@[to_additive]

中文:
定理 finprod_curry₃
  条件: {γ : 类型} (f : α × β × γ -> M) (h : HasFiniteMulSupport f)
  证明: by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]

@[to_additive]

Depends on / 依赖: finprod_curry
-/
theorem finprod_curry₃ {γ : Type*} (f : α × β × γ -> M) (h : HasFiniteMulSupport f) :
    ∏ᶠ abc, f abc = ∏ᶠ (a) (b) (c), f (a, b, c) := by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]

@[to_additive]
/--
theorem `finprod_dmem` / 定理 `finprod_dmem`

English:
theorem finprod_dmem
  given: {s : Set α} [DecidablePred (· in s)] (f : forall a : α, a in s -> M)
  proof: finprod_congr fun _ => finprod_congr fun ha => (dif_pos ha).symm

@[to_additive]

中文:
定理 finprod_dmem
  条件: {s : Set α} [DecidablePred (· in s)] (f : 对任意 a : α, a in s -> M)
  证明: finprod_congr fun _ => finprod_congr fun ha => (dif_pos ha).symm

@[to_additive]

Depends on / 依赖: dif_pos, finprod_congr
-/
theorem finprod_dmem {s : Set α} [DecidablePred (· in s)] (f : forall a : α, a in s -> M) :
    (∏ᶠ (a : α) (h : a in s), f a h) = ∏ᶠ (a : α) (_ : a in s), if h' : a in s then f a h' else 1 :=
  finprod_congr fun _ => finprod_congr fun ha => (dif_pos ha).symm

@[to_additive]
/--
theorem `finprod_emb_domain'` / 定理 `finprod_emb_domain'`

English:
theorem finprod_emb_domain'
  statement: {f : α -> β} (hf : Injective f) [DecidablePred (· in Set.range f)]
  proof: by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem]; rw [finprod_mem_range hf]; rw [finprod_congr fun a => _]
  intro a
  rw [dif_pos (Set.mem_range_self a)]; rw [hf (Classical.choose_spec (Set.mem_range_self a))]

@[to_additive]

中文:
定理 finprod_emb_domain'
  结论: {f : α -> β} (hf : Injective f) [DecidablePred (· in Set.range f)]
  证明: by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem]; rw [finprod_mem_range hf]; rw [finprod_congr fun a => _]
  intro a
  rw [dif_pos (Set.mem_range_self a)]; rw [hf (Classical.choose_spec (Set.mem_range_self a))]

@[to_additive]

Depends on / 依赖: Classical, Classical.choose_spec, Set.mem_range_self, choose_spec, dif_pos, finprod_congr, finprod_dmem, finprod_eq_dif, finprod_mem_range, mem_range_self, simp_rw
-/
theorem finprod_emb_domain' {f : α -> β} (hf : Injective f) [DecidablePred (· in Set.range f)]
    (g : α -> M) :
    (∏ᶠ b : β, if h : b in Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a := by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem]; rw [finprod_mem_range hf]; rw [finprod_congr fun a => _]
  intro a
  rw [dif_pos (Set.mem_range_self a)]; rw [hf (Classical.choose_spec (Set.mem_range_self a))]

@[to_additive]
/--
theorem `finprod_emb_domain` / 定理 `finprod_emb_domain`

English:
theorem finprod_emb_domain
  given: (f : α ↪ β) [DecidablePred (· in Set.range f)] (g : α -> M)
  proof: finprod_emb_domain' f.injective g

@[simp, norm_cast]

中文:
定理 finprod_emb_domain
  条件: (f : α ↪ β) [DecidablePred (· in Set.range f)] (g : α -> M)
  证明: finprod_emb_domain' f.injective g

@[simp, norm_cast]

Depends on / 依赖: f.injective, finprod_emb_domain, injective
-/
theorem finprod_emb_domain (f : α ↪ β) [DecidablePred (· in Set.range f)] (g : α -> M) :
    (∏ᶠ b : β, if h : b in Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a :=
  finprod_emb_domain' f.injective g

@[simp, norm_cast]
/--
lemma `Nat.cast_finprod` / 引理 `Nat.cast_finprod`

English:
lemma Nat.cast_finprod
  given: [Finite ι] {R : Type*} [CommSemiring R] (f : ι -> Nat)
  proof: (Nat.castRingHom R).map_finprod f.mulSupport.toFinite

中文:
引理 Nat.cast_finprod
  条件: [Finite ι] {R : 类型} [CommSemiring R] (f : ι -> 自然数)
  证明: (Nat.castRingHom R).map_finprod f.mulSupport.toFinite

Depends on / 依赖: Nat.castRingHom, castRingHom, f.mulSupport.toFinite, map_finprod, mulSupport, toFinite
-/
lemma Nat.cast_finprod [Finite ι] {R : Type*} [CommSemiring R] (f : ι -> Nat) :
    ↑(∏ᶠ x, f x : Nat) = ∏ᶠ x, (f x : R) :=
  (Nat.castRingHom R).map_finprod f.mulSupport.toFinite

/-- This version does not assume that `ι` is finite (compare `Nat.cast_finprod`), but instead needs
to assume characteristic zero to deal with the infinite case. -/
@[simp, norm_cast]
/--
lemma `Nat.cast_finprod'` / 引理 `Nat.cast_finprod'`

English:
lemma Nat.cast_finprod'
  given: {R : Type*} [CommSemiring R] [CharZero R] (f : ι -> Nat)
  proof: by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i => (f i : R)).HasFiniteMulSupport :=
fun h => hf h.of_comp cast_one cast_injective
    rw [finprod_of_not_hasFiniteMulSupport hf]; rw [finprod_of_not_hasFiniteMulSupport H]; rw [cast_one]

@[s

中文:
引理 Nat.cast_finprod'
  条件: {R : 类型} [CommSemiring R] [CharZero R] (f : ι -> 自然数)
  证明: by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i => (f i : R)).HasFiniteMulSupport :=
fun h => hf h.of_comp cast_one cast_injective
    rw [finprod_of_not_hasFiniteMulSupport hf]; rw [finprod_of_not_hasFiniteMulSupport H]; rw [cast_one]

@[s

Depends on / 依赖: HasFiniteMulSupport, Nat.castRingHom, castRingHom, cast_injective, cast_one, f.HasFiniteMulSupport, finprod_of_not_hasFiniteMulSupport, h.of_comp, map_finprod, of_comp
-/
lemma Nat.cast_finprod' {R : Type*} [CommSemiring R] [CharZero R] (f : ι -> Nat) :
    (∏ᶠ (x : ι), f x : Nat) = ∏ᶠ (x : ι), (f x : R) := by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i => (f i : R)).HasFiniteMulSupport :=
fun h => hf h.of_comp cast_one cast_injective
    rw [finprod_of_not_hasFiniteMulSupport hf]; rw [finprod_of_not_hasFiniteMulSupport H]; rw [cast_one]

@[simp, norm_cast]
/--
lemma `Nat.cast_finprod_mem` / 引理 `Nat.cast_finprod_mem`

English:
lemma Nat.cast_finprod_mem
  given: {s : Set ι} (hs : s.Finite) {R : Type*} [CommSemiring R] (f : ι -> Nat)
  proof: (Nat.castRingHom R).map_finprod_mem _ hs

@[simp, norm_cast]

中文:
引理 Nat.cast_finprod_mem
  条件: {s : Set ι} (hs : s.Finite) {R : 类型} [CommSemiring R] (f : ι -> 自然数)
  证明: (Nat.castRingHom R).map_finprod_mem _ hs

@[simp, norm_cast]

Depends on / 依赖: Nat.castRingHom, castRingHom, map_finprod_mem
-/
lemma Nat.cast_finprod_mem {s : Set ι} (hs : s.Finite) {R : Type*} [CommSemiring R] (f : ι -> Nat) :
    ↑(∏ᶠ x in s, f x : Nat) = ∏ᶠ x in s, (f x : R) :=
  (Nat.castRingHom R).map_finprod_mem _ hs

@[simp, norm_cast]
/--
lemma `Nat.cast_finsum` / 引理 `Nat.cast_finsum`

English:
lemma Nat.cast_finsum
  statement: [Finite ι] {M : Type*} [AddCommMonoidWithOne M]
  proof: (Nat.castAddMonoidHom M).map_finsum f.support.toFinite

@[simp, norm_cast]

中文:
引理 Nat.cast_finsum
  结论: [Finite ι] {M : 类型} [AddCommMonoidWithOne M]
  证明: (Nat.castAddMonoidHom M).map_finsum f.support.toFinite

@[simp, norm_cast]

Depends on / 依赖: Nat.castAddMonoidHom, castAddMonoidHom, f.support.toFinite, map_finsum, support, toFinite
-/
lemma Nat.cast_finsum [Finite ι] {M : Type*} [AddCommMonoidWithOne M]
    (f : ι -> Nat) : ↑(∑ᶠ x, f x : Nat) = ∑ᶠ x, (f x : M) :=
  (Nat.castAddMonoidHom M).map_finsum f.support.toFinite

@[simp, norm_cast]
/--
lemma `Nat.cast_finsum_mem` / 引理 `Nat.cast_finsum_mem`

English:
lemma Nat.cast_finsum_mem
  statement: {s : Set ι} (hs : s.Finite) {M : Type*}
  proof: (Nat.castAddMonoidHom M).map_finsum_mem _ hs

中文:
引理 Nat.cast_finsum_mem
  结论: {s : Set ι} (hs : s.Finite) {M : 类型}
  证明: (Nat.castAddMonoidHom M).map_finsum_mem _ hs

Depends on / 依赖: Nat.castAddMonoidHom, castAddMonoidHom, map_finsum_mem
-/
lemma Nat.cast_finsum_mem {s : Set ι} (hs : s.Finite) {M : Type*}
    [AddCommMonoidWithOne M] (f : ι -> Nat) : ↑(∑ᶠ x in s, f x : Nat) = ∑ᶠ x in s, (f x : M) :=
  (Nat.castAddMonoidHom M).map_finsum_mem _ hs

end type

/-!
### Some API for `fun a ↦ f a ^ count a s` on multisets
-/

namespace Multiset

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

@[to_additive]
/--
lemma `mulSupport_fun_pow_count_subset` / 引理 `mulSupport_fun_pow_count_subset`

English:
lemma mulSupport_fun_pow_count_subset
  given: (s : Multiset α) (f : α -> M)
  proof: by
  simp +contextual [not_imp_comm]

@[to_additive (attr := fun_prop)]

中文:
引理 mulSupport_fun_pow_count_subset
  条件: (s : Multiset α) (f : α -> M)
  证明: by
  simp +contextual [not_imp_comm]

@[to_additive (attr := fun_prop)]

Depends on / 依赖: contextual, not_imp_comm
-/
lemma mulSupport_fun_pow_count_subset (s : Multiset α) (f : α -> M) :
    (fun a => f a ^ count a s).mulSupport subseteq s.toFinset := by
  simp +contextual [not_imp_comm]

@[to_additive (attr := fun_prop)]
/--
lemma `hasFiniteMulSupport_fun_pow_count` / 引理 `hasFiniteMulSupport_fun_pow_count`

English:
lemma hasFiniteMulSupport_fun_pow_count
  given: (s : Multiset α) (f : α -> M)
  proof: s.toFinset.finite_toSet.subset mulSupport_fun_pow_count_subset ..

@[to_additive]

中文:
引理 hasFiniteMulSupport_fun_pow_count
  条件: (s : Multiset α) (f : α -> M)
  证明: s.toFinset.finite_toSet.subset mulSupport_fun_pow_count_subset ..

@[to_additive]

Depends on / 依赖: finite_toSet, mulSupport_fun_pow_count_subset, s.toFinset.finite_toSet.subset, subset, toFinset
-/
lemma hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α -> M) :
    (fun a => (f a) ^ s.count a).HasFiniteMulSupport :=
s.toFinset.finite_toSet.subset mulSupport_fun_pow_count_subset ..

@[to_additive]
/--
lemma `prod_map_eq_finprod` / 引理 `prod_map_eq_finprod`

English:
lemma prod_map_eq_finprod
  given: (s : Multiset α) (f : α -> M)
  proof: by
  rw [Finset.prod_multiset_map_count]; rw [eq_comm]
exact finprod_eq_prod_of_mulSupport_subset _ mulSupport_fun_pow_count_subset ..

中文:
引理 prod_map_eq_finprod
  条件: (s : Multiset α) (f : α -> M)
  证明: by
  rw [Finset.prod_multiset_map_count]; rw [eq_comm]
exact finprod_eq_prod_of_mulSupport_subset _ mulSupport_fun_pow_count_subset ..

Depends on / 依赖: Finset, Finset.prod_multiset_map_count, eq_comm, finprod_eq_prod_of_mulSupport_subset, mulSupport_fun_pow_count_subset, prod_multiset_map_count
-/
lemma prod_map_eq_finprod (s : Multiset α) (f : α -> M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  rw [Finset.prod_multiset_map_count]; rw [eq_comm]
exact finprod_eq_prod_of_mulSupport_subset _ mulSupport_fun_pow_count_subset ..

end Multiset
