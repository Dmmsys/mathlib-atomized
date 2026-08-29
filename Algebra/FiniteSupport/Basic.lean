/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Algebra.Module.Basic

/-!
# Make `fun_prop` work for finite (multiplicative) support

We provide API lemmas for the predicate `HasFiniteMulSupport` (and its additivized version
`HasFiniteSupport`) on functions so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support.
-/

public section

namespace Function

variable {α M : Type*} [One M]

@[to_additive (attr := fun_prop)]
/--
lemma `hasFiniteMulSupport_fun_one` / 引理 `hasFiniteMulSupport_fun_one`

English:
lemma hasFiniteMulSupport_fun_one
  statement: HasFiniteMulSupport (1 : α -> M)
  proof: by
  simp [HasFiniteMulSupport]

@[to_additive (attr := fun_prop)]

中文:
引理 hasFiniteMulSupport_fun_one
  结论: HasFiniteMulSupport (1 : α -> M)
  证明: by
  simp [HasFiniteMulSupport]

@[to_additive (attr := fun_prop)]

Depends on / 依赖: HasFiniteMulSupport
-/
lemma hasFiniteMulSupport_fun_one : HasFiniteMulSupport (1 : α -> M) := by
  simp [HasFiniteMulSupport]

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.fun_comp` / 引理 `HasFiniteMulSupport.fun_comp`

English:
lemma HasFiniteMulSupport.fun_comp
  statement: {N : Type*} [One N] {g : M -> N} {f : α -> M}
  proof: hf.subset mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.fun_comp
  结论: {N : 类型} [One N] {g : M -> N} {f : α -> M}
  证明: hf.subset mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.subset, mulSupport_comp_subset, subset
-/
lemma HasFiniteMulSupport.fun_comp {N : Type*} [One N] {g : M -> N} {f : α -> M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport fun a => g (f a) :=
hf.subset mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.comp` / 引理 `HasFiniteMulSupport.comp`

English:
lemma HasFiniteMulSupport.comp
  statement: {N : Type*} [One N] {g : M -> N} {f : α -> M}
  proof: hf.subset mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.comp
  结论: {N : 类型} [One N] {g : M -> N} {f : α -> M}
  证明: hf.subset mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.subset, mulSupport_comp_subset, subset
-/
lemma HasFiniteMulSupport.comp {N : Type*} [One N] {g : M -> N} {f : α -> M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport (g ∘ f) :=
hf.subset mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.fst` / 引理 `HasFiniteMulSupport.fst`

English:
lemma HasFiniteMulSupport.fst
  given: {M' : Type*} [One M'] {f : α -> M × M'} (hf : HasFiniteMulSupport f)
  proof: hf.comp rfl

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.fst
  条件: {M' : 类型} [One M'] {f : α -> M × M'} (hf : HasFiniteMulSupport f)
  证明: hf.comp rfl

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.comp
-/
lemma HasFiniteMulSupport.fst {M' : Type*} [One M'] {f : α -> M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a => (f a).fst :=
  hf.comp rfl

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.snd` / 引理 `HasFiniteMulSupport.snd`

English:
lemma HasFiniteMulSupport.snd
  given: {M' : Type*} [One M'] {f : α -> M × M'} (hf : HasFiniteMulSupport f)
  proof: hf.comp rfl

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.snd
  条件: {M' : 类型} [One M'] {f : α -> M × M'} (hf : HasFiniteMulSupport f)
  证明: hf.comp rfl

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.comp
-/
lemma HasFiniteMulSupport.snd {M' : Type*} [One M'] {f : α -> M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a => (f a).snd :=
  hf.comp rfl

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.prodMk` / 引理 `HasFiniteMulSupport.prodMk`

English:
lemma HasFiniteMulSupport.prodMk
  statement: {M' : Type*} [One M'] {f : α -> M} {g : α -> M'}
  proof: by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
引理 HasFiniteMulSupport.prodMk
  结论: {M' : 类型} [One M'] {f : α -> M} {g : α -> M'}
  证明: by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := to_fun (attr := fun_prop))]

Depends on / 依赖: HasFiniteMulSupport, hf.union, mulSupport_prodMk
-/
lemma HasFiniteMulSupport.prodMk {M' : Type*} [One M'] {f : α -> M} {g : α -> M'}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a => (f a, g a) := by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `HasFiniteMulSupport.mul` / 引理 `HasFiniteMulSupport.mul`

English:
lemma HasFiniteMulSupport.mul
  statement: {M : Type*} [MulOneClass M] {f g : α -> M}
  proof: (hf.union hg).subset mulSupport_mul ..

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
引理 HasFiniteMulSupport.mul
  结论: {M : 类型} [MulOneClass M] {f g : α -> M}
  证明: (hf.union hg).subset mulSupport_mul ..

@[to_additive (attr := to_fun (attr := fun_prop))]

Depends on / 依赖: hf.union, mulSupport_mul, subset
-/
lemma HasFiniteMulSupport.mul {M : Type*} [MulOneClass M] {f g : α -> M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f * g) :=
(hf.union hg).subset mulSupport_mul ..

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `HasFiniteMulSupport.inv` / 引理 `HasFiniteMulSupport.inv`

English:
lemma HasFiniteMulSupport.inv
  statement: {M : Type*} [DivisionMonoid M] {f : α -> M}
  proof: hf.comp inv_one

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.inv
  结论: {M : 类型} [DivisionMonoid M] {f : α -> M}
  证明: hf.comp inv_one

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.comp, inv_one
-/
lemma HasFiniteMulSupport.inv {M : Type*} [DivisionMonoid M] {f : α -> M}
    (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport f⁻¹ :=
  hf.comp inv_one

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.prod` / 引理 `HasFiniteMulSupport.prod`

English:
lemma HasFiniteMulSupport.prod
  statement: {M : Type*} [CommMonoid M] {ι : Type*} {f : ι -> α -> M}
  proof: (s.finite_toSet.biUnion fun i _ => hf i).subset s.mulSupport_prod f

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
引理 HasFiniteMulSupport.prod
  结论: {M : 类型} [CommMonoid M] {ι : 类型} {f : ι -> α -> M}
  证明: (s.finite_toSet.biUnion fun i _ => hf i).subset s.mulSupport_prod f

@[to_additive (attr := to_fun (attr := fun_prop))]

Depends on / 依赖: biUnion, finite_toSet, mulSupport_prod, s.finite_toSet.biUnion, s.mulSupport_prod, subset
-/
lemma HasFiniteMulSupport.prod {M : Type*} [CommMonoid M] {ι : Type*} {f : ι -> α -> M}
    (hf : forall i, HasFiniteMulSupport (f i)) (s : Finset ι) :
    HasFiniteMulSupport fun a => ∏ i in s, f i a :=
(s.finite_toSet.biUnion fun i _ => hf i).subset s.mulSupport_prod f

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `HasFiniteMulSupport.div` / 引理 `HasFiniteMulSupport.div`

English:
lemma HasFiniteMulSupport.div
  statement: {M : Type*} [DivisionMonoid M] {f g : α -> M}
  proof: (hf.union hg).subset mulSupport_div ..

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
引理 HasFiniteMulSupport.div
  结论: {M : 类型} [DivisionMonoid M] {f g : α -> M}
  证明: (hf.union hg).subset mulSupport_div ..

@[to_additive (attr := to_fun (attr := fun_prop))]

Depends on / 依赖: hf.union, mulSupport_div, subset
-/
lemma HasFiniteMulSupport.div {M : Type*} [DivisionMonoid M] {f g : α -> M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f / g) :=
(hf.union hg).subset mulSupport_div ..

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `HasFiniteMulSupport.pow` / 引理 `HasFiniteMulSupport.pow`

English:
lemma HasFiniteMulSupport.pow
  statement: {M : Type*} [Monoid M] {f : α -> M} (hf : HasFiniteMulSupport f)
  proof: hf.comp (one_pow n)

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
引理 HasFiniteMulSupport.pow
  结论: {M : 类型} [Monoid M] {f : α -> M} (hf : HasFiniteMulSupport f)
  证明: hf.comp (one_pow n)

@[to_additive (attr := to_fun (attr := fun_prop))]

Depends on / 依赖: hf.comp, one_pow
-/
lemma HasFiniteMulSupport.pow {M : Type*} [Monoid M] {f : α -> M} (hf : HasFiniteMulSupport f)
    (n : Nat) :
    HasFiniteMulSupport (f ^ n) :=
  hf.comp (one_pow n)

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `HasFiniteMulSupport.zpow` / 引理 `HasFiniteMulSupport.zpow`

English:
lemma HasFiniteMulSupport.zpow
  statement: {M : Type*} [DivisionMonoid M] {f : α -> M}
  proof: hf.comp (one_zpow n)

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.zpow
  结论: {M : 类型} [DivisionMonoid M] {f : α -> M}
  证明: hf.comp (one_zpow n)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.comp, one_zpow
-/
lemma HasFiniteMulSupport.zpow {M : Type*} [DivisionMonoid M] {f : α -> M}
    (hf : HasFiniteMulSupport f) (n : Int) :
    HasFiniteMulSupport (f ^ n) :=
  hf.comp (one_zpow n)

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.max` / 引理 `HasFiniteMulSupport.max`

English:
lemma HasFiniteMulSupport.max
  statement: [LinearOrder M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  proof: (hf.union hg).subset mulSupport_max ..

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.max
  结论: [LinearOrder M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  证明: (hf.union hg).subset mulSupport_max ..

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.union, mulSupport_max, subset
-/
lemma HasFiniteMulSupport.max [LinearOrder M] {f g : α -> M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a => max (f a) (g a) :=
(hf.union hg).subset mulSupport_max ..

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.min` / 引理 `HasFiniteMulSupport.min`

English:
lemma HasFiniteMulSupport.min
  statement: [LinearOrder M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  proof: (hf.union hg).subset mulSupport_min ..

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.min
  结论: [LinearOrder M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  证明: (hf.union hg).subset mulSupport_min ..

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.union, mulSupport_min, subset
-/
lemma HasFiniteMulSupport.min [LinearOrder M] {f g : α -> M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a => min (f a) (g a) :=
(hf.union hg).subset mulSupport_min ..

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.sup` / 引理 `HasFiniteMulSupport.sup`

English:
lemma HasFiniteMulSupport.sup
  statement: [SemilatticeSup M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  proof: (hf.union hg).subset mulSupport_sup ..

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.sup
  结论: [SemilatticeSup M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  证明: (hf.union hg).subset mulSupport_sup ..

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.union, mulSupport_sup, subset
-/
lemma HasFiniteMulSupport.sup [SemilatticeSup M] {f g : α -> M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a => f a ⊔ g a :=
(hf.union hg).subset mulSupport_sup ..

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.inf` / 引理 `HasFiniteMulSupport.inf`

English:
lemma HasFiniteMulSupport.inf
  statement: [SemilatticeInf M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  proof: (hf.union hg).subset mulSupport_inf ..

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.inf
  结论: [SemilatticeInf M] {f g : α -> M} (hf : HasFiniteMulSupport f)
  证明: (hf.union hg).subset mulSupport_inf ..

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.union, mulSupport_inf, subset
-/
lemma HasFiniteMulSupport.inf [SemilatticeInf M] {f g : α -> M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a => f a ⊓ g a :=
(hf.union hg).subset mulSupport_inf ..

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.iSup` / 引理 `HasFiniteMulSupport.iSup`

English:
lemma HasFiniteMulSupport.iSup
  statement: [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
  proof: (Set.finite_iUnion hf).subset mulSupport_iSup f

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.iSup
  结论: [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
  证明: (Set.finite_iUnion hf).subset mulSupport_iSup f

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Set.finite_iUnion, finite_iUnion, mulSupport_iSup, subset
-/
lemma HasFiniteMulSupport.iSup [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι -> α -> M} (hf : forall i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a => ⨆ i, f i a :=
(Set.finite_iUnion hf).subset mulSupport_iSup f

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.iInf` / 引理 `HasFiniteMulSupport.iInf`

English:
lemma HasFiniteMulSupport.iInf
  statement: [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
  proof: (Set.finite_iUnion hf).subset mulSupport_iInf f

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.iInf
  结论: [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
  证明: (Set.finite_iUnion hf).subset mulSupport_iInf f

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Set.finite_iUnion, finite_iUnion, mulSupport_iInf, subset
-/
lemma HasFiniteMulSupport.iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι -> α -> M} (hf : forall i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a => ⨅ i, f i a :=
(Set.finite_iUnion hf).subset mulSupport_iInf f

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.pi` / 引理 `HasFiniteMulSupport.pi`

English:
lemma HasFiniteMulSupport.pi
  statement: {ι : Type*} [Finite α] {f : ι -> α -> M}
  proof: by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi => ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.pi
  结论: {ι : 类型} [Finite α] {f : ι -> α -> M}
  证明: by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi => ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive (attr := fun_prop)]

Depends on / 依赖: HasFiniteMulSupport, Set.finite_iUnion, Set.mem_iUnion, finite_iUnion, mem_iUnion, mem_mulSupport, ne_iff, ne_iff.mp, subset
-/
lemma HasFiniteMulSupport.pi {ι : Type*} [Finite α] {f : ι -> α -> M}
    (hf : forall a, HasFiniteMulSupport (f · a)) :
    HasFiniteMulSupport f := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi => ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.sup'` / 引理 `HasFiniteMulSupport.sup'`

English:
lemma HasFiniteMulSupport.sup'
  statement: [SemilatticeSup M] {ι : Type*} {f : ι -> α -> M}
  proof: by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha => ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (fun x => f x a) ha

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.sup'
  结论: [SemilatticeSup M] {ι : 类型} {f : ι -> α -> M}
  证明: by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha => ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (fun x => f x a) ha

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Finset, Finset.sup, HasFiniteMulSupport, Set.mem_iUnion, SetLike, SetLike.mem_coe, _eq_of_forall, biUnion, contrapose, exists_prop, finite_toSet, mem_coe, mem_iUnion, mem_mulSupport, s.finite_toSet.biUnion, subset
-/
lemma HasFiniteMulSupport.sup' [SemilatticeSup M] {ι : Type*} {f : ι -> α -> M}
    (s : Finset ι) (hf : forall i in s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a => s.sup' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha => ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (fun x => f x a) ha

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.inf'` / 引理 `HasFiniteMulSupport.inf'`

English:
lemma HasFiniteMulSupport.inf'
  statement: [SemilatticeInf M] {ι : Type*} {f : ι -> α -> M}
  proof: by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha => ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x => f x a) ha

中文:
引理 HasFiniteMulSupport.inf'
  结论: [SemilatticeInf M] {ι : 类型} {f : ι -> α -> M}
  证明: by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha => ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x => f x a) ha

Depends on / 依赖: Finset, Finset.inf, HasFiniteMulSupport, Set.mem_iUnion, SetLike, SetLike.mem_coe, _eq_of_forall, biUnion, contrapose, exists_prop, finite_toSet, mem_coe, mem_iUnion, mem_mulSupport, s.finite_toSet.biUnion, subset
-/
lemma HasFiniteMulSupport.inf' [SemilatticeInf M] {ι : Type*} {f : ι -> α -> M}
    (s : Finset ι) (hf : forall i in s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a => s.inf' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha => ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x => f x a) ha

variable {β : Type*} {f : β -> M} {g : α -> β}

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.comp_of_injective` / 引理 `HasFiniteMulSupport.comp_of_injective`

English:
lemma HasFiniteMulSupport.comp_of_injective
  given: (hg : Injective g) (hf : f.HasFiniteMulSupport)
  proof: by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage, Function.mulSupport]

@[to_additive (attr := fun_prop)]

中文:
引理 HasFiniteMulSupport.comp_of_injective
  条件: (hg : Injective g) (hf : f.HasFiniteMulSupport)
  证明: by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage, Function.mulSupport]

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Finite, Function, Function.mulSupport, Set.Finite.of_injOn, Set.injOn_of_injective, Set.mapsTo_iff_subset_preimage, injOn_of_injective, mapsTo_iff_subset_preimage, mulSupport, of_injOn
-/
lemma HasFiniteMulSupport.comp_of_injective (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage, Function.mulSupport]

@[to_additive (attr := fun_prop)]
/--
lemma `HasFiniteMulSupport.fun_comp_of_injective` / 引理 `HasFiniteMulSupport.fun_comp_of_injective`

English:
lemma HasFiniteMulSupport.fun_comp_of_injective
  given: (hg : Injective g) (hf : f.HasFiniteMulSupport)
  proof: hf.comp_of_injective hg

@[to_additive]

中文:
引理 HasFiniteMulSupport.fun_comp_of_injective
  条件: (hg : Injective g) (hf : f.HasFiniteMulSupport)
  证明: hf.comp_of_injective hg

@[to_additive]

Depends on / 依赖: comp_of_injective, hf.comp_of_injective
-/
lemma HasFiniteMulSupport.fun_comp_of_injective (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (fun a => f (g a)).HasFiniteMulSupport :=
  hf.comp_of_injective hg

@[to_additive]
/--
lemma `HasFiniteMulSupport.of_comp` / 引理 `HasFiniteMulSupport.of_comp`

English:
lemma HasFiniteMulSupport.of_comp
  statement: [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
  proof: by
  refine Set.Finite.subset hfg fun _ ha => Set.mem_ofPred.mpr fun H => Set.mem_ofPred.mp ha ?_
  grind

中文:
引理 HasFiniteMulSupport.of_comp
  结论: [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
  证明: by
  refine Set.Finite.subset hfg fun _ ha => Set.mem_ofPred.mpr fun H => Set.mem_ofPred.mp ha ?_
  grind

Depends on / 依赖: Finite, Set.Finite.subset, Set.mem_ofPred.mp, Set.mem_ofPred.mpr, mem_ofPred, subset
-/
lemma HasFiniteMulSupport.of_comp [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
    (hf : Injective f) :
    g.HasFiniteMulSupport := by
  refine Set.Finite.subset hfg fun _ ha => Set.mem_ofPred.mpr fun H => Set.mem_ofPred.mp ha ?_
  grind

-- The additive version is a special case of `Function.HasFiniteSupport.smul_left`.
@[fun_prop]
/--
lemma `HasFiniteSupport.hasFiniteMulSupport_fun_pow` / 引理 `HasFiniteSupport.hasFiniteMulSupport_fun_pow`

English:
lemma HasFiniteSupport.hasFiniteMulSupport_fun_pow
  statement: {M : Type*} [Monoid M] (f : α -> M) {g : α -> Nat}
  proof: Set.Finite.subset hg fun a ha => by contrapose! ha; simp_all

中文:
引理 HasFiniteSupport.hasFiniteMulSupport_fun_pow
  结论: {M : 类型} [Monoid M] (f : α -> M) {g : α -> 自然数}
  证明: Set.Finite.subset hg fun a ha => by contrapose! ha; simp_all

Depends on / 依赖: Finite, Set.Finite.subset, contrapose, subset
-/
lemma HasFiniteSupport.hasFiniteMulSupport_fun_pow {M : Type*} [Monoid M] (f : α -> M) {g : α -> Nat}
    (hg : g.HasFiniteSupport) :
    (fun a : α => f a ^ g a).HasFiniteMulSupport :=
  Set.Finite.subset hg fun a ha => by contrapose! ha; simp_all

section MulZeroClass

variable {M : Type*} [MulZeroClass M]

@[to_fun (attr := fun_prop)]
/--
lemma `HasFiniteSupport.mul_left` / 引理 `HasFiniteSupport.mul_left`

English:
lemma HasFiniteSupport.mul_left
  given: {f : α -> M} (hf : f.HasFiniteSupport) (g : α -> M)
  proof: Set.Finite.subset hf fun _ ha => support_mul_subset_left f g ha

@[to_fun (attr := fun_prop)]

中文:
引理 HasFiniteSupport.mul_left
  条件: {f : α -> M} (hf : f.HasFiniteSupport) (g : α -> M)
  证明: Set.Finite.subset hf fun _ ha => support_mul_subset_left f g ha

@[to_fun (attr := fun_prop)]

Depends on / 依赖: Finite, Set.Finite.subset, subset, support_mul_subset_left
-/
lemma HasFiniteSupport.mul_left {f : α -> M} (hf : f.HasFiniteSupport) (g : α -> M) :
    (f * g).HasFiniteSupport :=
  Set.Finite.subset hf fun _ ha => support_mul_subset_left f g ha

@[to_fun (attr := fun_prop)]
/--
lemma `HasFiniteSupport.mul_right` / 引理 `HasFiniteSupport.mul_right`

English:
lemma HasFiniteSupport.mul_right
  given: (f : α -> M) {g : α -> M} (hg : g.HasFiniteSupport)
  proof: Set.Finite.subset hg fun _ ha => support_mul_subset_right f g ha

中文:
引理 HasFiniteSupport.mul_right
  条件: (f : α -> M) {g : α -> M} (hg : g.HasFiniteSupport)
  证明: Set.Finite.subset hg fun _ ha => support_mul_subset_right f g ha

Depends on / 依赖: Finite, Set.Finite.subset, subset, support_mul_subset_right
-/
lemma HasFiniteSupport.mul_right (f : α -> M) {g : α -> M} (hg : g.HasFiniteSupport) :
    (f * g).HasFiniteSupport :=
  Set.Finite.subset hg fun _ ha => support_mul_subset_right f g ha

end MulZeroClass

end Function

@[fun_prop]
/--
lemma `Multiset.hasFiniteSupport_count` / 引理 `Multiset.hasFiniteSupport_count`

English:
lemma Multiset.hasFiniteSupport_count
  given: {α : Type*} [DecidableEq α] (s : Multiset α)
  proof: s.toFinset.finite_toSet.subset by simp

中文:
引理 Multiset.hasFiniteSupport_count
  条件: {α : 类型} [DecidableEq α] (s : Multiset α)
  证明: s.toFinset.finite_toSet.subset by simp

Depends on / 依赖: finite_toSet, s.toFinset.finite_toSet.subset, subset, toFinset
-/
lemma Multiset.hasFiniteSupport_count {α : Type*} [DecidableEq α] (s : Multiset α) :
    (count · s).HasFiniteSupport :=
s.toFinset.finite_toSet.subset by simp

end

namespace Function.HasFiniteSupport

public section SMul

variable {α R M : Type*} [Zero M]

@[to_fun (attr := fun_prop)]
/--
lemma `smul_left` / 引理 `smul_left`

English:
lemma smul_left
  given: [Zero R] [SMulWithZero R M] {f : α -> R} (hf : f.HasFiniteSupport) (g : α -> M)
  proof: Set.Finite.subset hf fun _ ha => support_smul_subset_left f g ha

@[to_fun (attr := fun_prop)]

中文:
引理 smul_left
  条件: [Zero R] [SMulWithZero R M] {f : α -> R} (hf : f.HasFiniteSupport) (g : α -> M)
  证明: Set.Finite.subset hf fun _ ha => support_smul_subset_left f g ha

@[to_fun (attr := fun_prop)]

Depends on / 依赖: Finite, Set.Finite.subset, subset, support_smul_subset_left
-/
lemma smul_left [Zero R] [SMulWithZero R M] {f : α -> R} (hf : f.HasFiniteSupport) (g : α -> M) :
    (f • g).HasFiniteSupport :=
  Set.Finite.subset hf fun _ ha => support_smul_subset_left f g ha

@[to_fun (attr := fun_prop)]
/--
lemma `smul_right` / 引理 `smul_right`

English:
lemma smul_right
  given: [SMulZeroClass R M] (f : α -> R) {g : α -> M} (hg : g.HasFiniteSupport)
  proof: Set.Finite.subset hg fun _ ha => support_smul_subset_right f g ha

中文:
引理 smul_right
  条件: [SMulZeroClass R M] (f : α -> R) {g : α -> M} (hg : g.HasFiniteSupport)
  证明: Set.Finite.subset hg fun _ ha => support_smul_subset_right f g ha

Depends on / 依赖: Finite, Set.Finite.subset, subset, support_smul_subset_right
-/
lemma smul_right [SMulZeroClass R M] (f : α -> R) {g : α -> M} (hg : g.HasFiniteSupport) :
    (f • g).HasFiniteSupport :=
  Set.Finite.subset hg fun _ ha => support_smul_subset_right f g ha

end SMul

end Function.HasFiniteSupport
