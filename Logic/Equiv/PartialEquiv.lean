/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Core
public import Mathlib.Tactic.Attr.Core

/-!
# Partial equivalences

This file defines equivalences between subsets of given types.
An element `e` of `PartialEquiv α β` is made of two maps `e.toFun` and `e.invFun` respectively
from α to β and from β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two partial equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.toFun x` and `e.invFun y`.

## Main definitions

* `Equiv.toPartialEquiv`: associating a partial equiv to an equiv, with source = target = univ
* `PartialEquiv.symm`: the inverse of a partial equivalence
* `PartialEquiv.trans`: the composition of two partial equivalences
* `PartialEquiv.refl`: the identity partial equivalence
* `PartialEquiv.ofSet`: the identity on a set `s`
* `EqOnSource`: equivalence relation describing the "right" notion of equality for partial
  equivalences (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of partial equivalences:
* equivs on subtypes
* pairs of functions taking values in `Option α` and `Option β`, equal to none where the partial
  equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
  restriction of domains. Checking that one always belongs to the right subtype makes things very
  tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
  instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
  the domain is restricted automatically). These are implemented in `PEquiv.lean`. For manifolds,
  where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
  overhead as one would need to extend all classes of smoothness to option-valued maps.
* The `PartialEquiv` version as explained above is easier to use for manifolds. The drawback is that
  there is extra useless data (the values of `toFun` and `invFun` outside of `source` and `target`).
  In particular, the equality notion between partial equivs is not "the right one", i.e., coinciding
  source and target and equality there. Moreover, there are no partial equivs in this sense between
  an empty type and a nonempty type. Since empty types are not that useful, and since one almost
  never needs to talk about equal partial equivs, this is not an issue in practice.
  Still, we introduce an equivalence relation `EqOnSource` that captures this right notion of
  equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/

@[expose] public section
open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`PartialEquiv`, `OpenPartialHomeomorph`, etc).

This is in a separate file from `Mathlib/Tactic/Attr/Register.lean` because attributes need a
new file to become functional.
-/

namespace Mathlib.Tactic.MfldSetTac

/-- A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another. -/
elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      apply Set.ext; intro my_y
      constructor <;>
        · intro h_my_y
          try simp only [*, mfld_simps] at h_my_y
          try simp only [*, mfld_simps])))
  | (``LE.le, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      intro my_y h_my_y
      try simp only [*, mfld_simps] at h_my_y
      try simp only [*, mfld_simps])))
  | _ => throwError "goal should be an equality or an inclusion"

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply

end Mathlib.Tactic.MfldSetTac

open Function Set

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/--
Definition of `PartialEquiv` / `PartialEquiv` 的定义

English:
structure PartialEquiv
  parameters: (α : Type*) (β : Type*)
  axioms and operations (8):
    - toFun : α -> β
    - invFun : β -> α
    - source : Set α
    - target : Set β
    - map_source' : forall ⦃x⦄, x in source -> toFun x in target
    - map_target' : forall ⦃x⦄, x in target -> invFun x in source
    - left_inv' : forall ⦃x⦄, x in source -> invFun (toFun x) = x
    - right_inv' : forall ⦃x⦄, x in target -> toFun (invFun x) = x

中文:
结构 PartialEquiv
  参数: (α : 类型) (β : 类型)
  公理与运算 (8 个):
    - toFun : α -> β
    - invFun : β -> α
    - source : Set α
    - target : Set β
    - map_source' : 对任意 ⦃x⦄, x in source -> toFun x in target
    - map_target' : 对任意 ⦃x⦄, x in target -> invFun x in source
    - left_inv' : 对任意 ⦃x⦄, x in source -> invFun (toFun x) = x
    - right_inv' : 对任意 ⦃x⦄, x in target -> toFun (invFun x) = x
-/
structure PartialEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a partial inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α -> β
  /-- The partial inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β -> α
  /-- The domain of the partial equivalence. -/
  source : Set α
  /-- The codomain of the partial equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : forall ⦃x⦄, x in source -> toFun x in target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : forall ⦃x⦄, x in target -> invFun x in source
  /-- The proposition that `invFun` is a left-inverse of `toFun` on `source`. -/
  left_inv' : forall ⦃x⦄, x in source -> invFun (toFun x) = x
  /-- The proposition that `invFun` is a right-inverse of `toFun` on `target`. -/
  right_inv' : forall ⦃x⦄, x in target -> toFun (invFun x) = x

attribute [coe] PartialEquiv.toFun

namespace PartialEquiv

variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] [Inhabited β] : Inhabited (PartialEquiv α β)
  body: ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

中文:
实例 [Inhabited
  签名: α] [Inhabited β] : Inhabited (PartialEquiv α β)
  定义体: ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

Depends on / 依赖: eqOn_empty, mapsTo_empty
-/
instance [Inhabited α] [Inhabited β] : Inhabited (PartialEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

/-- The inverse of a partial equivalence -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : PartialEquiv β α where
  body: e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'

中文:
定义 symm
  签名: : PartialEquiv β α where
  定义体: e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'
-/
protected def symm : PartialEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (PartialEquiv α β) fun _ => α -> β
  body: ⟨PartialEquiv.toFun⟩

中文:
实例 :
  签名: CoeFun (PartialEquiv α β) fun _ => α -> β
  定义体: ⟨PartialEquiv.toFun⟩

Depends on / 依赖: PartialEquiv, PartialEquiv.toFun
-/
instance : CoeFun (PartialEquiv α β) fun _ => α -> β :=
  ⟨PartialEquiv.toFun⟩

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : PartialEquiv α β)
  body: e.symm

initialize_simps_projections PartialEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : PartialEquiv α β)
  定义体: e.symm

initialize_simps_projections PartialEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (e : PartialEquiv α β) : β -> α :=
  e.symm

initialize_simps_projections PartialEquiv (toFun -> apply, invFun -> symm_apply)

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α -> β) (g s t ml mr il ir)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_mk
  条件: (f : α -> β) (g s t ml mr il ir)
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_mk (f : α -> β) (g s t ml mr il ir) :
    (PartialEquiv.mk f g s t ml mr il ir : α -> β) = f := rfl

@[simp, mfld_simps]
/--
theorem `coe_symm_mk` / 定理 `coe_symm_mk`

English:
theorem coe_symm_mk
  given: (f : α -> β) (g s t ml mr il ir)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_symm_mk
  条件: (f : α -> β) (g s t ml mr il ir)
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_symm_mk (f : α -> β) (g s t ml mr il ir) :
    ((PartialEquiv.mk f g s t ml mr il ir).symm : β -> α) = g :=
  rfl

@[simp, mfld_simps]
/--
theorem `invFun_as_coe` / 定理 `invFun_as_coe`

English:
theorem invFun_as_coe
  statement: e.invFun = e.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 invFun_as_coe
  结论: e.invFun = e.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem invFun_as_coe : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `map_source` / 定理 `map_source`

English:
theorem map_source
  given: {x : α} (h : x in e.source)
  statement: e x in e.target
  proof: e.map_source' h

中文:
定理 map_source
  条件: {x : α} (h : x in e.source)
  结论: e x in e.target
  证明: e.map_source' h

Depends on / 依赖: e.map_source, map_source
-/
theorem map_source {x : α} (h : x in e.source) : e x in e.target :=
  e.map_source' h

/--
lemma `image_source_subset` / 引理 `image_source_subset`

English:
lemma image_source_subset
  statement: e '' e.source subseteq e.target
  proof: fun _ ⟨_, hx, hex⟩ => mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[deprecated (since := "2026-06-17")] alias map_source'' := image_source_subset

@[simp, mfld_simps]

中文:
引理 image_source_subset
  结论: e '' e.source subseteq e.target
  证明: fun _ ⟨_, hx, hex⟩ => mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[deprecated (since := "2026-06-17")] alias map_source'' := image_source_subset

@[simp, mfld_simps]

Depends on / 依赖: e.map_source, hex.symm, map_source, mem_of_eq_of_mem
-/
lemma image_source_subset : e '' e.source subseteq e.target :=
  fun _ ⟨_, hx, hex⟩ => mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[deprecated (since := "2026-06-17")] alias map_source'' := image_source_subset

@[simp, mfld_simps]
/--
theorem `map_target` / 定理 `map_target`

English:
theorem map_target
  given: {x : β} (h : x in e.target)
  statement: e.symm x in e.source
  proof: e.map_target' h

@[simp, mfld_simps]

中文:
定理 map_target
  条件: {x : β} (h : x in e.target)
  结论: e.symm x in e.source
  证明: e.map_target' h

@[simp, mfld_simps]

Depends on / 依赖: e.map_target, map_target
-/
theorem map_target {x : β} (h : x in e.target) : e.symm x in e.source :=
  e.map_target' h

@[simp, mfld_simps]
/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: {x : α} (h : x in e.source)
  statement: e.symm (e x) = x
  proof: e.left_inv' h

@[simp, mfld_simps]

中文:
定理 left_inv
  条件: {x : α} (h : x in e.source)
  结论: e.symm (e x) = x
  证明: e.left_inv' h

@[simp, mfld_simps]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem left_inv {x : α} (h : x in e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: {x : β} (h : x in e.target)
  statement: e (e.symm x) = x
  proof: e.right_inv' h

中文:
定理 right_inv
  条件: {x : β} (h : x in e.target)
  结论: e (e.symm x) = x
  证明: e.right_inv' h

Depends on / 依赖: e.right_inv, right_inv
-/
theorem right_inv {x : β} (h : x in e.target) : e (e.symm x) = x :=
  e.right_inv' h

/--
theorem `target_subset_range` / 定理 `target_subset_range`

English:
theorem target_subset_range
  statement: e.target subseteq range e
  proof: fun x hx => ⟨e.symm x, right_inv e hx⟩

中文:
定理 target_subset_range
  结论: e.target subseteq range e
  证明: fun x hx => ⟨e.symm x, right_inv e hx⟩

Depends on / 依赖: e.symm, right_inv
-/
theorem target_subset_range : e.target subseteq range e :=
  fun x hx => ⟨e.symm x, right_inv e hx⟩

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: {x : α} {y : β} (hx : x in e.source) (hy : y in e.target)
  proof: ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩

中文:
定理 symm_apply_eq
  条件: {x : α} {y : β} (hx : x in e.source) (hy : y in e.target)
  证明: ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩

Depends on / 依赖: e.left_inv, e.right_inv, left_inv, right_inv
-/
theorem symm_apply_eq {x : α} {y : β} (hx : x in e.source) (hy : y in e.target) :
    e.symm y = x ↔ y = e x :=
  ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {x : α} {y : β} (hx : x in e.source) (hy : y in e.target)
  proof: by
  simp [eq_comm, ← symm_apply_eq e hx hy]

中文:
定理 eq_symm_apply
  条件: {x : α} {y : β} (hx : x in e.source) (hy : y in e.target)
  证明: by
  simp [eq_comm, ← symm_apply_eq e hx hy]

Depends on / 依赖: eq_comm, symm_apply_eq
-/
theorem eq_symm_apply {x : α} {y : β} (hx : x in e.source) (hy : y in e.target) :
    x = e.symm y ↔ e x = y := by
  simp [eq_comm, ← symm_apply_eq e hx hy]

/--
theorem `mapsTo` / 定理 `mapsTo`

English:
theorem mapsTo
  statement: MapsTo e e.source e.target
  proof: fun _ => e.map_source

中文:
定理 mapsTo
  结论: MapsTo e e.source e.target
  证明: fun _ => e.map_source
-/
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

/--
theorem `mapsTo_symm` / 定理 `mapsTo_symm`

English:
theorem mapsTo_symm
  statement: MapsTo e.symm e.target e.source
  proof: e.symm.mapsTo

@[deprecated (since := "2026-05-18")] alias symm_mapsTo := mapsTo_symm

中文:
定理 mapsTo_symm
  结论: MapsTo e.symm e.target e.source
  证明: e.symm.mapsTo

@[deprecated (since := "2026-05-18")] alias symm_mapsTo := mapsTo_symm

Depends on / 依赖: e.symm.mapsTo, mapsTo
-/
theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

@[deprecated (since := "2026-05-18")] alias symm_mapsTo := mapsTo_symm

/--
theorem `leftInvOn` / 定理 `leftInvOn`

English:
theorem leftInvOn
  statement: LeftInvOn e.symm e e.source
  proof: fun _ => e.left_inv

中文:
定理 leftInvOn
  结论: LeftInvOn e.symm e e.source
  证明: fun _ => e.left_inv
-/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv

/--
theorem `rightInvOn` / 定理 `rightInvOn`

English:
theorem rightInvOn
  statement: RightInvOn e.symm e e.target
  proof: fun _ => e.right_inv

中文:
定理 rightInvOn
  结论: RightInvOn e.symm e e.target
  证明: fun _ => e.right_inv
-/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv

/--
theorem `invOn` / 定理 `invOn`

English:
theorem invOn
  statement: InvOn e.symm e e.source e.target
  proof: ⟨e.leftInvOn, e.rightInvOn⟩

中文:
定理 invOn
  结论: InvOn e.symm e e.source e.target
  证明: ⟨e.leftInvOn, e.rightInvOn⟩
-/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩

/--
theorem `injOn` / 定理 `injOn`

English:
theorem injOn
  statement: InjOn e e.source
  proof: e.leftInvOn.injOn

中文:
定理 injOn
  结论: InjOn e e.source
  证明: e.leftInvOn.injOn
-/
protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn

/--
theorem `bijOn` / 定理 `bijOn`

English:
theorem bijOn
  statement: BijOn e e.source e.target
  proof: e.invOn.bijOn e.mapsTo e.mapsTo_symm

中文:
定理 bijOn
  结论: BijOn e e.source e.target
  证明: e.invOn.bijOn e.mapsTo e.mapsTo_symm
-/
protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.mapsTo_symm

/--
theorem `surjOn` / 定理 `surjOn`

English:
theorem surjOn
  statement: SurjOn e e.source e.target
  proof: e.bijOn.surjOn

中文:
定理 surjOn
  结论: SurjOn e e.source e.target
  证明: e.bijOn.surjOn
-/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

/-- Interpret an `Equiv` as a `PartialEquiv` by restricting it to `s` in the domain
and to `t` in the codomain. -/
@[simps -fullyApplied]
/--
Definition of `_root_.Equiv.toPartialEquivOfImageEq` / `_root_.Equiv.toPartialEquivOfImageEq` 的定义

English:
definition _root_.Equiv.toPartialEquivOfImageEq
  signature: (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t)
  body: e
  invFun := e.symm
  source := s
  target := t
  map_source' _ hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

中文:
定义 _root_.Equiv.toPartialEquivOfImageEq
  签名: (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t)
  定义体: e
  invFun := e.symm
  source := s
  target := t
  map_source' _ hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x
-/
def _root_.Equiv.toPartialEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
    PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := s
  target := t
  map_source' _ hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

/-- Associate a `PartialEquiv` to an `Equiv`. -/
@[simps! (attr := mfld_simps) -fullyApplied]
/--
Definition of `_root_.Equiv.toPartialEquiv` / `_root_.Equiv.toPartialEquiv` 的定义

English:
definition _root_.Equiv.toPartialEquiv
  signature: (e : α ≃ β)
  body: e.toPartialEquivOfImageEq univ univ by rw [image_univ, e.surjective.range_eq]

中文:
定义 _root_.Equiv.toPartialEquiv
  签名: (e : α ≃ β)
  定义体: e.toPartialEquivOfImageEq univ univ by rw [image_univ, e.surjective.range_eq]

Depends on / 依赖: e.surjective.range_eq, e.toPartialEquivOfImageEq, image_univ, range_eq, surjective, toPartialEquivOfImageEq
-/
def _root_.Equiv.toPartialEquiv (e : α ≃ β) : PartialEquiv α β :=
e.toPartialEquivOfImageEq univ univ by rw [image_univ, e.surjective.range_eq]

/--
Instance `inhabitedOfEmpty` / 实例 `inhabitedOfEmpty`

English:
instance inhabitedOfEmpty
  signature: [IsEmpty α] [IsEmpty β]
  body: ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩

中文:
实例 inhabitedOfEmpty
  签名: [IsEmpty α] [IsEmpty β]
  定义体: ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩

Depends on / 依赖: Equiv.equivEmpty, equivEmpty, toPartialEquiv
-/
instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (PartialEquiv α β) :=
  ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩

/-- Create a copy of a `PartialEquiv` providing better definitional equalities. -/
@[simps -fullyApplied]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : ⇑e.symm = g) (s : Set α)
  body: f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv

中文:
定义 copy
  签名: (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : ⇑e.symm = g) (s : Set α)
  定义体: f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv
-/
def copy (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    PartialEquiv α β where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  statement: (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : ⇑e.symm = g)
  proof: by
  subst f g s t
  cases e
  rfl

中文:
定理 copy_eq
  结论: (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : ⇑e.symm = g)
  证明: by
  subst f g s t
  cases e
  rfl
-/
theorem copy_eq (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : ⇑e.symm = g)
    (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    e.copy f hf g hg s hs t ht = e := by
  subst f g s t
  cases e
  rfl

/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: : e.source ≃ e.target where
  body: ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
left_inv := fun ⟨_, hx⟩ => Subtype.ext e.left_inv hx
right_inv := fun ⟨_, hy⟩ => Subtype.ext e.right_inv hy

中文:
定义 toEquiv
  签名: : e.source ≃ e.target where
  定义体: ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
left_inv := fun ⟨_, hx⟩ => Subtype.ext e.left_inv hx
right_inv := fun ⟨_, hy⟩ => Subtype.ext e.right_inv hy
-/
protected def toEquiv : e.source ≃ e.target where
  toFun x := ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
left_inv := fun ⟨_, hx⟩ => Subtype.ext e.left_inv hx
right_inv := fun ⟨_, hy⟩ => Subtype.ext e.right_inv hy

/--
lemma `toEquiv_eq_codRestrict_restrict` / 引理 `toEquiv_eq_codRestrict_restrict`

English:
lemma toEquiv_eq_codRestrict_restrict
  proof: rfl

中文:
引理 toEquiv_eq_codRestrict_restrict
  证明: rfl
-/
lemma toEquiv_eq_codRestrict_restrict :
    e.toEquiv = codRestrict (e.source.domRestrict e) e.target (by simp) :=
  rfl

/--
lemma `toEquiv_symm_eq_codRestrict_restrict` / 引理 `toEquiv_symm_eq_codRestrict_restrict`

English:
lemma toEquiv_symm_eq_codRestrict_restrict
  proof: by
  rfl

@[simp, mfld_simps]

中文:
引理 toEquiv_symm_eq_codRestrict_restrict
  证明: by
  rfl

@[simp, mfld_simps]
-/
lemma toEquiv_symm_eq_codRestrict_restrict :
    e.toEquiv.symm = codRestrict (e.target.domRestrict e.invFun) e.source (by simp) := by
  rfl

@[simp, mfld_simps]
/--
theorem `symm_source` / 定理 `symm_source`

English:
theorem symm_source
  statement: e.symm.source = e.target
  proof: rfl

@[simp, mfld_simps]

中文:
定理 symm_source
  结论: e.symm.source = e.target
  证明: rfl

@[simp, mfld_simps]
-/
theorem symm_source : e.symm.source = e.target :=
  rfl

@[simp, mfld_simps]
/--
theorem `symm_target` / 定理 `symm_target`

English:
theorem symm_target
  statement: e.symm.target = e.source
  proof: rfl

@[simp, mfld_simps]

中文:
定理 symm_target
  结论: e.symm.target = e.source
  证明: rfl

@[simp, mfld_simps]
-/
theorem symm_target : e.symm.target = e.source :=
  rfl

@[simp, mfld_simps]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective :
    Function.Bijective (PartialEquiv.symm : PartialEquiv α β -> PartialEquiv β α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `image_source_eq_target` / 定理 `image_source_eq_target`

English:
theorem image_source_eq_target
  statement: e '' e.source = e.target
  proof: e.bijOn.image_eq

中文:
定理 image_source_eq_target
  结论: e '' e.source = e.target
  证明: e.bijOn.image_eq

Depends on / 依赖: e.bijOn.image_eq, image_eq
-/
theorem image_source_eq_target : e '' e.source = e.target :=
  e.bijOn.image_eq

/--
theorem `forall_mem_target` / 定理 `forall_mem_target`

English:
theorem forall_mem_target
  given: {p : β -> Prop}
  statement: (forall y in e.target, p y) ↔ forall x in e.source, p (e x)
  proof: by
  rw [← image_source_eq_target]; rw [forall_mem_image]

中文:
定理 forall_mem_target
  条件: {p : β -> 命题}
  结论: (对任意 y in e.target, p y) ↔ 对任意 x in e.source, p (e x)
  证明: by
  rw [← image_source_eq_target]; rw [forall_mem_image]

Depends on / 依赖: forall_mem_image, image_source_eq_target
-/
theorem forall_mem_target {p : β -> Prop} : (forall y in e.target, p y) ↔ forall x in e.source, p (e x) := by
  rw [← image_source_eq_target]; rw [forall_mem_image]

/--
theorem `exists_mem_target` / 定理 `exists_mem_target`

English:
theorem exists_mem_target
  given: {p : β -> Prop}
  statement: (exists y in e.target, p y) ↔ exists x in e.source, p (e x)
  proof: by
  rw [← image_source_eq_target]; rw [exists_mem_image]

中文:
定理 exists_mem_target
  条件: {p : β -> 命题}
  结论: (存在 y in e.target, p y) ↔ 存在 x in e.source, p (e x)
  证明: by
  rw [← image_source_eq_target]; rw [exists_mem_image]

Depends on / 依赖: exists_mem_image, image_source_eq_target
-/
theorem exists_mem_target {p : β -> Prop} : (exists y in e.target, p y) ↔ exists x in e.source, p (e x) := by
  rw [← image_source_eq_target]; rw [exists_mem_image]

/--
Definition of `IsImage` / `IsImage` 的定义

English:
definition IsImage
  signature: (s : Set α) (t : Set β)
  body: forall ⦃x⦄, x in e.source -> (e x in t ↔ x in s)

中文:
定义 IsImage
  签名: (s : Set α) (t : Set β)
  定义体: forall ⦃x⦄, x in e.source -> (e x in t ↔ x in s)

Depends on / 依赖: e.source, source
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  forall ⦃x⦄, x in e.source -> (e x in t ↔ x in s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α}

/--
theorem `apply_mem_iff` / 定理 `apply_mem_iff`

English:
theorem apply_mem_iff
  given: (h : e.IsImage s t) (hx : x in e.source)
  statement: e x in t ↔ x in s
  proof: h hx

中文:
定理 apply_mem_iff
  条件: (h : e.IsImage s t) (hx : x in e.source)
  结论: e x in t ↔ x in s
  证明: h hx
-/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x in e.source) : e x in t ↔ x in s :=
  h hx

/--
theorem `symm_apply_mem_iff` / 定理 `symm_apply_mem_iff`

English:
theorem symm_apply_mem_iff
  given: (h : e.IsImage s t)
  statement: forall ⦃y⦄, y in e.target -> (e.symm y in s ↔ y in t)
  proof: e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]

中文:
定理 symm_apply_mem_iff
  条件: (h : e.IsImage s t)
  结论: 对任意 ⦃y⦄, y in e.target -> (e.symm y in s ↔ y in t)
  证明: e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]

Depends on / 依赖: e.forall_mem_target.mpr, e.left_inv, forall_mem_target, left_inv
-/
theorem symm_apply_mem_iff (h : e.IsImage s t) : forall ⦃y⦄, y in e.target -> (e.symm y in s ↔ y in t) :=
  e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : e.IsImage s t)
  statement: e.symm.IsImage t s
  proof: h.symm_apply_mem_iff

@[simp]

中文:
定理 symm
  条件: (h : e.IsImage s t)
  结论: e.symm.IsImage t s
  证明: h.symm_apply_mem_iff

@[simp]
-/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff

@[simp]
/--
theorem `symm_iff` / 定理 `symm_iff`

English:
theorem symm_iff
  statement: e.symm.IsImage t s ↔ e.IsImage s t
  proof: ⟨fun h => h.symm, fun h => h.symm⟩

中文:
定理 symm_iff
  结论: e.symm.IsImage t s ↔ e.IsImage s t
  证明: ⟨fun h => h.symm, fun h => h.symm⟩

Depends on / 依赖: h.symm
-/
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/--
theorem `mapsTo` / 定理 `mapsTo`

English:
theorem mapsTo
  given: (h : e.IsImage s t)
  statement: MapsTo e (e.source inter s) (e.target inter t)
  proof: fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩

中文:
定理 mapsTo
  条件: (h : e.IsImage s t)
  结论: MapsTo e (e.source inter s) (e.target inter t)
  证明: fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩
-/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source inter s) (e.target inter t) :=
  fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩

/--
theorem `symm_mapsTo` / 定理 `symm_mapsTo`

English:
theorem symm_mapsTo
  given: (h : e.IsImage s t)
  statement: MapsTo e.symm (e.target inter t) (e.source inter s)
  proof: h.symm.mapsTo

中文:
定理 symm_mapsTo
  条件: (h : e.IsImage s t)
  结论: MapsTo e.symm (e.target inter t) (e.source inter s)
  证明: h.symm.mapsTo

Depends on / 依赖: h.symm.mapsTo, mapsTo
-/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target inter t) (e.source inter s) :=
  h.symm.mapsTo

/-- Restrict a `PartialEquiv` to a pair of corresponding sets. -/
@[simps -fullyApplied]
/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: (h : e.IsImage s t)
  body: e
  invFun := e.symm
  source := e.source inter s
  target := e.target inter t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono inter_subset_left
  right_inv' := e.rightInvOn.mono inter_subset_left

中文:
定义 restr
  签名: (h : e.IsImage s t)
  定义体: e
  invFun := e.symm
  source := e.source inter s
  target := e.target inter t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono inter_subset_left
  right_inv' := e.rightInvOn.mono inter_subset_left
-/
def restr (h : e.IsImage s t) : PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := e.source inter s
  target := e.target inter t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono inter_subset_left
  right_inv' := e.rightInvOn.mono inter_subset_left

/--
theorem `image_eq` / 定理 `image_eq`

English:
theorem image_eq
  given: (h : e.IsImage s t)
  statement: e '' (e.source inter s) = e.target inter t
  proof: h.restr.image_source_eq_target

中文:
定理 image_eq
  条件: (h : e.IsImage s t)
  结论: e '' (e.source inter s) = e.target inter t
  证明: h.restr.image_source_eq_target

Depends on / 依赖: h.restr.image_source_eq_target, image_source_eq_target
-/
theorem image_eq (h : e.IsImage s t) : e '' (e.source inter s) = e.target inter t :=
  h.restr.image_source_eq_target

/--
theorem `symm_image_eq` / 定理 `symm_image_eq`

English:
theorem symm_image_eq
  given: (h : e.IsImage s t)
  statement: e.symm '' (e.target inter t) = e.source inter s
  proof: h.symm.image_eq

中文:
定理 symm_image_eq
  条件: (h : e.IsImage s t)
  结论: e.symm '' (e.target inter t) = e.source inter s
  证明: h.symm.image_eq

Depends on / 依赖: h.symm.image_eq, image_eq
-/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target inter t) = e.source inter s :=
  h.symm.image_eq

/--
theorem `iff_preimage_eq` / 定理 `iff_preimage_eq`

English:
theorem iff_preimage_eq
  statement: e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter s
  proof: by
  simp only [IsImage, Set.ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

中文:
定理 iff_preimage_eq
  结论: e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter s
  证明: by
  simp only [IsImage, Set.ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

Depends on / 依赖: IsImage, Set.ext_iff, and_congr_right_iff, ext_iff, mem_inter_iff, mem_preimage
-/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter s := by
  simp only [IsImage, Set.ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

/--
theorem `iff_symm_preimage_eq` / 定理 `iff_symm_preimage_eq`

English:
theorem iff_symm_preimage_eq
  statement: e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t
  proof: symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

中文:
定理 iff_symm_preimage_eq
  结论: e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t
  证明: symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

Depends on / 依赖: iff_preimage_eq, symm_iff, symm_iff.symm.trans
-/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

/--
theorem `of_image_eq` / 定理 `of_image_eq`

English:
theorem of_image_eq
  given: (h : e '' (e.source inter s) = e.target inter t)
  statement: e.IsImage s t
  proof: of_symm_preimage_eq Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

中文:
定理 of_image_eq
  条件: (h : e '' (e.source inter s) = e.target inter t)
  结论: e.IsImage s t
  证明: of_symm_preimage_eq Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

Depends on / 依赖: Eq.trans, image_eq, image_eq.symm, of_symm_preimage_eq
-/
theorem of_image_eq (h : e '' (e.source inter s) = e.target inter t) : e.IsImage s t :=
of_symm_preimage_eq Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

/--
theorem `of_symm_image_eq` / 定理 `of_symm_image_eq`

English:
theorem of_symm_image_eq
  given: (h : e.symm '' (e.target inter t) = e.source inter s)
  statement: e.IsImage s t
  proof: of_preimage_eq Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h

中文:
定理 of_symm_image_eq
  条件: (h : e.symm '' (e.target inter t) = e.source inter s)
  结论: e.IsImage s t
  证明: of_preimage_eq Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h

Depends on / 依赖: Eq.trans, iff_preimage_eq, of_preimage_eq, symm_image_eq, symm_image_eq.symm
-/
theorem of_symm_image_eq (h : e.symm '' (e.target inter t) = e.source inter s) : e.IsImage s t :=
of_preimage_eq Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h

/--
theorem `compl` / 定理 `compl`

English:
theorem compl
  given: (h : e.IsImage s t)
  statement: e.IsImage sᶜ tᶜ
  proof: fun _ hx => not_congr (h hx)

中文:
定理 compl
  条件: (h : e.IsImage s t)
  结论: e.IsImage sᶜ tᶜ
  证明: fun _ hx => not_congr (h hx)
-/
protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => not_congr (h hx)

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  proof: fun _ hx => and_congr (h hx) (h' hx)

中文:
定理 inter
  条件: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  证明: fun _ hx => and_congr (h hx) (h' hx)
-/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s inter s') (t inter t') := fun _ hx => and_congr (h hx) (h' hx)

/--
theorem `union` / 定理 `union`

English:
theorem union
  given: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  proof: fun _ hx => or_congr (h hx) (h' hx)

中文:
定理 union
  条件: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  证明: fun _ hx => or_congr (h hx) (h' hx)
-/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s union s') (t union t') := fun _ hx => or_congr (h hx) (h' hx)

/--
theorem `diff` / 定理 `diff`

English:
theorem diff
  given: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  proof: h.inter h'.compl

中文:
定理 diff
  条件: {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t')
  证明: h.inter h'.compl
-/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

/--
theorem `leftInvOn_piecewise` / 定理 `leftInvOn_piecewise`

English:
theorem leftInvOn_piecewise
  statement: {e' : PartialEquiv α β} [forall i, Decidable (i in s)]
  proof: by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  · rw [piecewise_eq_of_notMem _ _ _ hs, piecewise_eq_of_notMem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]

中文:
定理 leftInvOn_piecewise
  结论: {e' : PartialEquiv α β} [对任意 i, Decidable (i in s)]
  证明: by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  · rw [piecewise_eq_of_notMem _ _ _ hs, piecewise_eq_of_notMem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]

Depends on / 依赖: e.left_inv, left_inv, piecewise_eq_of_mem, piecewise_eq_of_notMem
-/
theorem leftInvOn_piecewise {e' : PartialEquiv α β} [forall i, Decidable (i in s)]
    [forall i, Decidable (i in t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  · rw [piecewise_eq_of_notMem _ _ _ hs, piecewise_eq_of_notMem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]

/--
theorem `inter_eq_of_inter_eq_of_eqOn` / 定理 `inter_eq_of_inter_eq_of_eqOn`

English:
theorem inter_eq_of_inter_eq_of_eqOn
  statement: {e' : PartialEquiv α β} (h : e.IsImage s t)
  proof: by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]

中文:
定理 inter_eq_of_inter_eq_of_eqOn
  结论: {e' : PartialEquiv α β} (h : e.IsImage s t)
  证明: by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]

Depends on / 依赖: h.image_eq, heq.image_eq, image_eq
-/
theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source inter s = e'.source inter s) (heq : EqOn e e' (e.source inter s)) :
    e.target inter t = e'.target inter t := by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]

/--
theorem `symm_eq_on_of_inter_eq_of_eqOn` / 定理 `symm_eq_on_of_inter_eq_of_eqOn`

English:
theorem symm_eq_on_of_inter_eq_of_eqOn
  statement: {e' : PartialEquiv α β} (h : e.IsImage s t)
  proof: by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1]; rw [heq hx]; rw [e'.left_inv hx'.1]

中文:
定理 symm_eq_on_of_inter_eq_of_eqOn
  结论: {e' : PartialEquiv α β} (h : e.IsImage s t)
  证明: by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1]; rw [heq hx]; rw [e'.left_inv hx'.1]

Depends on / 依赖: e.left_inv, h.image_eq, image_eq, left_inv
-/
theorem symm_eq_on_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (hs : e.source inter s = e'.source inter s) (heq : EqOn e e' (e.source inter s)) :
    EqOn e.symm e'.symm (e.target inter t) := by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1]; rw [heq hx]; rw [e'.left_inv hx'.1]

end IsImage

/--
theorem `isImage_source_target` / 定理 `isImage_source_target`

English:
theorem isImage_source_target
  statement: e.IsImage e.source e.target
  proof: fun x hx => by simp [hx]

中文:
定理 isImage_source_target
  结论: e.IsImage e.source e.target
  证明: fun x hx => by simp [hx]
-/
theorem isImage_source_target : e.IsImage e.source e.target := fun x hx => by simp [hx]

/--
theorem `isImage_source_target_of_disjoint` / 定理 `isImage_source_target_of_disjoint`

English:
theorem isImage_source_target_of_disjoint
  statement: (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
  proof: IsImage.of_image_eq by rw [hs.inter_eq, ht.inter_eq, image_empty]

中文:
定理 isImage_source_target_of_disjoint
  结论: (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
  证明: IsImage.of_image_eq by rw [hs.inter_eq, ht.inter_eq, image_empty]

Depends on / 依赖: IsImage, IsImage.of_image_eq, hs.inter_eq, ht.inter_eq, image_empty, inter_eq, of_image_eq
-/
theorem isImage_source_target_of_disjoint (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.target :=
IsImage.of_image_eq by rw [hs.inter_eq, ht.inter_eq, image_empty]

/--
theorem `image_source_inter_eq'` / 定理 `image_source_inter_eq'`

English:
theorem image_source_inter_eq'
  given: (s : Set α)
  statement: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
  proof: by
  rw [inter_comm]; rw [e.leftInvOn.image_inter']; rw [image_source_eq_target]; rw [inter_comm]

中文:
定理 image_source_inter_eq'
  条件: (s : Set α)
  结论: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
  证明: by
  rw [inter_comm]; rw [e.leftInvOn.image_inter']; rw [image_source_eq_target]; rw [inter_comm]

Depends on / 依赖: e.leftInvOn.image_inter, image_inter, image_source_eq_target, inter_comm, leftInvOn
-/
theorem image_source_inter_eq' (s : Set α) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s := by
  rw [inter_comm]; rw [e.leftInvOn.image_inter']; rw [image_source_eq_target]; rw [inter_comm]

/--
theorem `image_source_inter_eq` / 定理 `image_source_inter_eq`

English:
theorem image_source_inter_eq
  given: (s : Set α)
  proof: by
  rw [inter_comm]; rw [e.leftInvOn.image_inter]; rw [image_source_eq_target]; rw [inter_comm]

中文:
定理 image_source_inter_eq
  条件: (s : Set α)
  证明: by
  rw [inter_comm]; rw [e.leftInvOn.image_inter]; rw [image_source_eq_target]; rw [inter_comm]

Depends on / 依赖: e.leftInvOn.image_inter, image_inter, image_source_eq_target, inter_comm, leftInvOn
-/
theorem image_source_inter_eq (s : Set α) :
    e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s) := by
  rw [inter_comm]; rw [e.leftInvOn.image_inter]; rw [image_source_eq_target]; rw [inter_comm]

/--
theorem `image_eq_target_inter_inv_preimage` / 定理 `image_eq_target_inter_inv_preimage`

English:
theorem image_eq_target_inter_inv_preimage
  given: {s : Set α} (h : s subseteq e.source)
  proof: by
  rw [← e.image_source_inter_eq']; rw [inter_eq_self_of_subset_right h]

中文:
定理 image_eq_target_inter_inv_preimage
  条件: {s : Set α} (h : s subseteq e.source)
  证明: by
  rw [← e.image_source_inter_eq']; rw [inter_eq_self_of_subset_right h]

Depends on / 依赖: e.image_source_inter_eq, image_source_inter_eq, inter_eq_self_of_subset_right
-/
theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s subseteq e.source) :
    e '' s = e.target inter e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq']; rw [inter_eq_self_of_subset_right h]

/--
theorem `symm_image_eq_source_inter_preimage` / 定理 `symm_image_eq_source_inter_preimage`

English:
theorem symm_image_eq_source_inter_preimage
  given: {s : Set β} (h : s subseteq e.target)
  proof: e.symm.image_eq_target_inter_inv_preimage h

中文:
定理 symm_image_eq_source_inter_preimage
  条件: {s : Set β} (h : s subseteq e.target)
  证明: e.symm.image_eq_target_inter_inv_preimage h

Depends on / 依赖: e.symm.image_eq_target_inter_inv_preimage, image_eq_target_inter_inv_preimage
-/
theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s subseteq e.target) :
    e.symm '' s = e.source inter e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

/--
theorem `symm_image_target_inter_eq` / 定理 `symm_image_target_inter_eq`

English:
theorem symm_image_target_inter_eq
  given: (s : Set β)
  proof: e.symm.image_source_inter_eq _

中文:
定理 symm_image_target_inter_eq
  条件: (s : Set β)
  证明: e.symm.image_source_inter_eq _

Depends on / 依赖: e.symm.image_source_inter_eq, image_source_inter_eq
-/
theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target inter s) = e.source inter e ⁻¹' (e.target inter s) :=
  e.symm.image_source_inter_eq _

/--
theorem `symm_image_target_inter_eq'` / 定理 `symm_image_target_inter_eq'`

English:
theorem symm_image_target_inter_eq'
  given: (s : Set β)
  statement: e.symm '' (e.target inter s) = e.source inter e ⁻¹' s
  proof: e.symm.image_source_inter_eq' _

中文:
定理 symm_image_target_inter_eq'
  条件: (s : Set β)
  结论: e.symm '' (e.target inter s) = e.source inter e ⁻¹' s
  证明: e.symm.image_source_inter_eq' _

Depends on / 依赖: e.symm.image_source_inter_eq, image_source_inter_eq
-/
theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target inter s) = e.source inter e ⁻¹' s :=
  e.symm.image_source_inter_eq' _

/--
theorem `source_inter_preimage_inv_preimage` / 定理 `source_inter_preimage_inv_preimage`

English:
theorem source_inter_preimage_inv_preimage
  given: (s : Set α)
  proof: Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]

中文:
定理 source_inter_preimage_inv_preimage
  条件: (s : Set α)
  证明: Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]

Depends on / 依赖: Set.ext, and_congr_right_iff, e.left_inv, left_inv, mem_preimage
-/
theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source inter e ⁻¹' e.symm ⁻¹' s = e.source inter s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]

/--
theorem `source_inter_preimage_target_inter` / 定理 `source_inter_preimage_target_inter`

English:
theorem source_inter_preimage_target_inter
  given: (s : Set β)
  proof: ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩

中文:
定理 source_inter_preimage_target_inter
  条件: (s : Set β)
  证明: ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩

Depends on / 依赖: e.map_source, map_source
-/
theorem source_inter_preimage_target_inter (s : Set β) :
    e.source inter e ⁻¹' (e.target inter s) = e.source inter e ⁻¹' s :=
  ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩

/--
theorem `target_inter_inv_preimage_preimage` / 定理 `target_inter_inv_preimage_preimage`

English:
theorem target_inter_inv_preimage_preimage
  given: (s : Set β)
  proof: e.symm.source_inter_preimage_inv_preimage _

中文:
定理 target_inter_inv_preimage_preimage
  条件: (s : Set β)
  证明: e.symm.source_inter_preimage_inv_preimage _

Depends on / 依赖: e.symm.source_inter_preimage_inv_preimage, source_inter_preimage_inv_preimage
-/
theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target inter e.symm ⁻¹' e ⁻¹' s = e.target inter s :=
  e.symm.source_inter_preimage_inv_preimage _

/--
theorem `symm_image_image_of_subset_source` / 定理 `symm_image_image_of_subset_source`

English:
theorem symm_image_image_of_subset_source
  given: {s : Set α} (h : s subseteq e.source)
  statement: e.symm '' e '' s = s
  proof: (e.leftInvOn.mono h).image_image

中文:
定理 symm_image_image_of_subset_source
  条件: {s : Set α} (h : s subseteq e.source)
  结论: e.symm '' e '' s = s
  证明: (e.leftInvOn.mono h).image_image

Depends on / 依赖: e.leftInvOn.mono, image_image, leftInvOn
-/
theorem symm_image_image_of_subset_source {s : Set α} (h : s subseteq e.source) : e.symm '' e '' s = s :=
  (e.leftInvOn.mono h).image_image

/--
theorem `image_symm_image_of_subset_target` / 定理 `image_symm_image_of_subset_target`

English:
theorem image_symm_image_of_subset_target
  given: {s : Set β} (h : s subseteq e.target)
  statement: e '' e.symm '' s = s
  proof: e.symm.symm_image_image_of_subset_source h

中文:
定理 image_symm_image_of_subset_target
  条件: {s : Set β} (h : s subseteq e.target)
  结论: e '' e.symm '' s = s
  证明: e.symm.symm_image_image_of_subset_source h

Depends on / 依赖: e.symm.symm_image_image_of_subset_source, symm_image_image_of_subset_source
-/
theorem image_symm_image_of_subset_target {s : Set β} (h : s subseteq e.target) : e '' e.symm '' s = s :=
  e.symm.symm_image_image_of_subset_source h

/--
theorem `source_subset_preimage_target` / 定理 `source_subset_preimage_target`

English:
theorem source_subset_preimage_target
  statement: e.source subseteq e ⁻¹' e.target
  proof: e.mapsTo

中文:
定理 source_subset_preimage_target
  结论: e.source subseteq e ⁻¹' e.target
  证明: e.mapsTo

Depends on / 依赖: e.mapsTo, mapsTo
-/
theorem source_subset_preimage_target : e.source subseteq e ⁻¹' e.target :=
  e.mapsTo

/--
theorem `symm_image_target_eq_source` / 定理 `symm_image_target_eq_source`

English:
theorem symm_image_target_eq_source
  statement: e.symm '' e.target = e.source
  proof: e.symm.image_source_eq_target

中文:
定理 symm_image_target_eq_source
  结论: e.symm '' e.target = e.source
  证明: e.symm.image_source_eq_target

Depends on / 依赖: e.symm.image_source_eq_target, image_source_eq_target
-/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

/--
theorem `target_subset_preimage_source` / 定理 `target_subset_preimage_source`

English:
theorem target_subset_preimage_source
  statement: e.target subseteq e.symm ⁻¹' e.source
  proof: e.mapsTo_symm

中文:
定理 target_subset_preimage_source
  结论: e.target subseteq e.symm ⁻¹' e.source
  证明: e.mapsTo_symm

Depends on / 依赖: e.mapsTo_symm, mapsTo_symm
-/
theorem target_subset_preimage_source : e.target subseteq e.symm ⁻¹' e.source :=
  e.mapsTo_symm

/-- Two partial equivs that have the same `source`, same `toFun` and same `invFun`, coincide. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {e e' : PartialEquiv α β} (h : forall x, e x = e' x)
  proof: by
  have A : (e : α -> β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β -> α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A]; rw [hs]; rw [I'] at I


中文:
定理 ext
  结论: {e e' : PartialEquiv α β} (h : 对任意 x, e x = e' x)
  证明: by
  have A : (e : α -> β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β -> α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A]; rw [hs]; rw [I'] at I

-/
protected theorem ext {e e' : PartialEquiv α β} (h : forall x, e x = e' x)
    (hsymm : forall x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' := by
  have A : (e : α -> β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β -> α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A]; rw [hs]; rw [I'] at I
  cases e; cases e'
  simp_all

/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: (s : Set α)
  body: (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

@[simp, mfld_simps]

中文:
定义 restr
  签名: (s : Set α)
  定义体: (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

@[simp, mfld_simps]
-/
protected def restr (s : Set α) : PartialEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

@[simp, mfld_simps]
/--
theorem `restr_coe` / 定理 `restr_coe`

English:
theorem restr_coe
  given: (s : Set α)
  statement: (e.restr s : α -> β) = e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 restr_coe
  条件: (s : Set α)
  结论: (e.restr s : α -> β) = e
  证明: rfl

@[simp, mfld_simps]
-/
theorem restr_coe (s : Set α) : (e.restr s : α -> β) = e :=
  rfl

@[simp, mfld_simps]
/--
theorem `restr_coe_symm` / 定理 `restr_coe_symm`

English:
theorem restr_coe_symm
  given: (s : Set α)
  statement: ((e.restr s).symm : β -> α) = e.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 restr_coe_symm
  条件: (s : Set α)
  结论: ((e.restr s).symm : β -> α) = e.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β -> α) = e.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `restr_source` / 定理 `restr_source`

English:
theorem restr_source
  given: (s : Set α)
  statement: (e.restr s).source = e.source inter s
  proof: rfl

中文:
定理 restr_source
  条件: (s : Set α)
  结论: (e.restr s).source = e.source inter s
  证明: rfl
-/
theorem restr_source (s : Set α) : (e.restr s).source = e.source inter s :=
  rfl

/--
theorem `source_restr_subset_source` / 定理 `source_restr_subset_source`

English:
theorem source_restr_subset_source
  given: (s : Set α)
  statement: (e.restr s).source subseteq e.source
  proof: inter_subset_left

@[simp, mfld_simps]

中文:
定理 source_restr_subset_source
  条件: (s : Set α)
  结论: (e.restr s).source subseteq e.source
  证明: inter_subset_left

@[simp, mfld_simps]

Depends on / 依赖: inter_subset_left
-/
theorem source_restr_subset_source (s : Set α) : (e.restr s).source subseteq e.source := inter_subset_left

@[simp, mfld_simps]
/--
theorem `restr_target` / 定理 `restr_target`

English:
theorem restr_target
  given: (s : Set α)
  statement: (e.restr s).target = e.target inter e.symm ⁻¹' s
  proof: rfl

中文:
定理 restr_target
  条件: (s : Set α)
  结论: (e.restr s).target = e.target inter e.symm ⁻¹' s
  证明: rfl
-/
theorem restr_target (s : Set α) : (e.restr s).target = e.target inter e.symm ⁻¹' s :=
  rfl

/--
theorem `restr_eq_of_source_subset` / 定理 `restr_eq_of_source_subset`

English:
theorem restr_eq_of_source_subset
  given: {e : PartialEquiv α β} {s : Set α} (h : e.source subseteq s)
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp, mfld_simps]

中文:
定理 restr_eq_of_source_subset
  条件: {e : PartialEquiv α β} {s : Set α} (h : e.source subseteq s)
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, inter_eq_self_of_subset_left
-/
theorem restr_eq_of_source_subset {e : PartialEquiv α β} {s : Set α} (h : e.source subseteq s) :
    e.restr s = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp, mfld_simps]
/--
theorem `restr_univ` / 定理 `restr_univ`

English:
theorem restr_univ
  given: {e : PartialEquiv α β}
  statement: e.restr univ = e
  proof: restr_eq_of_source_subset (subset_univ _)

中文:
定理 restr_univ
  条件: {e : PartialEquiv α β}
  结论: e.restr univ = e
  证明: restr_eq_of_source_subset (subset_univ _)

Depends on / 依赖: restr_eq_of_source_subset, subset_univ
-/
theorem restr_univ {e : PartialEquiv α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Type*)
  body: (Equiv.refl α).toPartialEquiv

@[simp, mfld_simps]

中文:
定义 refl
  签名: (α : 类型)
  定义体: (Equiv.refl α).toPartialEquiv

@[simp, mfld_simps]
-/
protected def refl (α : Type*) : PartialEquiv α α :=
  (Equiv.refl α).toPartialEquiv

@[simp, mfld_simps]
/--
theorem `refl_source` / 定理 `refl_source`

English:
theorem refl_source
  statement: (PartialEquiv.refl α).source = univ
  proof: rfl

@[simp, mfld_simps]

中文:
定理 refl_source
  结论: (PartialEquiv.refl α).source = univ
  证明: rfl

@[simp, mfld_simps]
-/
theorem refl_source : (PartialEquiv.refl α).source = univ :=
  rfl

@[simp, mfld_simps]
/--
theorem `refl_target` / 定理 `refl_target`

English:
theorem refl_target
  statement: (PartialEquiv.refl α).target = univ
  proof: rfl

@[simp, mfld_simps]

中文:
定理 refl_target
  结论: (PartialEquiv.refl α).target = univ
  证明: rfl

@[simp, mfld_simps]
-/
theorem refl_target : (PartialEquiv.refl α).target = univ :=
  rfl

@[simp, mfld_simps]
/--
theorem `refl_coe` / 定理 `refl_coe`

English:
theorem refl_coe
  statement: (PartialEquiv.refl α : α -> α) = id
  proof: rfl

@[simp, mfld_simps]

中文:
定理 refl_coe
  结论: (PartialEquiv.refl α : α -> α) = id
  证明: rfl

@[simp, mfld_simps]
-/
theorem refl_coe : (PartialEquiv.refl α : α -> α) = id :=
  rfl

@[simp, mfld_simps]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (PartialEquiv.refl α).symm = PartialEquiv.refl α
  proof: rfl

@[mfld_simps]

中文:
定理 refl_symm
  结论: (PartialEquiv.refl α).symm = PartialEquiv.refl α
  证明: rfl

@[mfld_simps]
-/
theorem refl_symm : (PartialEquiv.refl α).symm = PartialEquiv.refl α :=
  rfl

@[mfld_simps]
/--
theorem `refl_restr_source` / 定理 `refl_restr_source`

English:
theorem refl_restr_source
  given: (s : Set α)
  statement: ((PartialEquiv.refl α).restr s).source = s
  proof: by simp

@[mfld_simps]

中文:
定理 refl_restr_source
  条件: (s : Set α)
  结论: ((PartialEquiv.refl α).restr s).source = s
  证明: by simp

@[mfld_simps]
-/
theorem refl_restr_source (s : Set α) : ((PartialEquiv.refl α).restr s).source = s := by simp

@[mfld_simps]
/--
theorem `refl_restr_target` / 定理 `refl_restr_target`

English:
theorem refl_restr_target
  given: (s : Set α)
  statement: ((PartialEquiv.refl α).restr s).target = s
  proof: by simp

中文:
定理 refl_restr_target
  条件: (s : Set α)
  结论: ((PartialEquiv.refl α).restr s).target = s
  证明: by simp
-/
theorem refl_restr_target (s : Set α) : ((PartialEquiv.refl α).restr s).target = s := by simp

/--
Definition of `ofSet` / `ofSet` 的定义

English:
definition ofSet
  signature: (s : Set α)
  body: id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

@[simp, mfld_simps]

中文:
定义 ofSet
  签名: (s : Set α)
  定义体: id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

@[simp, mfld_simps]
-/
def ofSet (s : Set α) : PartialEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

@[simp, mfld_simps]
/--
theorem `ofSet_source` / 定理 `ofSet_source`

English:
theorem ofSet_source
  given: (s : Set α)
  statement: (PartialEquiv.ofSet s).source = s
  proof: rfl

@[simp, mfld_simps]

中文:
定理 ofSet_source
  条件: (s : Set α)
  结论: (PartialEquiv.ofSet s).source = s
  证明: rfl

@[simp, mfld_simps]
-/
theorem ofSet_source (s : Set α) : (PartialEquiv.ofSet s).source = s :=
  rfl

@[simp, mfld_simps]
/--
theorem `ofSet_target` / 定理 `ofSet_target`

English:
theorem ofSet_target
  given: (s : Set α)
  statement: (PartialEquiv.ofSet s).target = s
  proof: rfl

@[simp, mfld_simps]

中文:
定理 ofSet_target
  条件: (s : Set α)
  结论: (PartialEquiv.ofSet s).target = s
  证明: rfl

@[simp, mfld_simps]
-/
theorem ofSet_target (s : Set α) : (PartialEquiv.ofSet s).target = s :=
  rfl

@[simp, mfld_simps]
/--
theorem `ofSet_coe` / 定理 `ofSet_coe`

English:
theorem ofSet_coe
  given: (s : Set α)
  statement: (PartialEquiv.ofSet s : α -> α) = id
  proof: rfl

@[simp, mfld_simps]

中文:
定理 ofSet_coe
  条件: (s : Set α)
  结论: (PartialEquiv.ofSet s : α -> α) = id
  证明: rfl

@[simp, mfld_simps]
-/
theorem ofSet_coe (s : Set α) : (PartialEquiv.ofSet s : α -> α) = id :=
  rfl

@[simp, mfld_simps]
/--
theorem `ofSet_symm` / 定理 `ofSet_symm`

English:
theorem ofSet_symm
  given: (s : Set α)
  statement: (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet s
  proof: rfl

中文:
定理 ofSet_symm
  条件: (s : Set α)
  结论: (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet s
  证明: rfl
-/
theorem ofSet_symm (s : Set α) : (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet s :=
  rfl

/-- `Function.const` as a `PartialEquiv`.
It consists of two constant maps in opposite directions. -/
@[simps]
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (a : α) (b : β)
  body: Function.const α b
  invFun := Function.const β a
  source := {a}
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := rfl
  left_inv' a' ha' := by rw [eq_of_mem_singleton ha', const_apply]
  right_inv' b' hb' := by rw [eq_of_mem_singleton hb', const_apply]

中文:
定义 single
  签名: (a : α) (b : β)
  定义体: Function.const α b
  invFun := Function.const β a
  source := {a}
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := rfl
  left_inv' a' ha' := by rw [eq_of_mem_singleton ha', const_apply]
  right_inv' b' hb' := by rw [eq_of_mem_singleton hb', const_apply]

Depends on / 依赖: Function, Function.const
-/
def single (a : α) (b : β) : PartialEquiv α β where
  toFun := Function.const α b
  invFun := Function.const β a
  source := {a}
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := rfl
  left_inv' a' ha' := by rw [eq_of_mem_singleton ha', const_apply]
  right_inv' b' hb' := by rw [eq_of_mem_singleton hb', const_apply]

/-- Composing two partial equivs if the target of the first coincides with the source of the
second. -/
@[simps]
/--
Definition of `trans'` / `trans'` 的定义

English:
definition trans'
  signature: (e' : PartialEquiv β γ) (h : e.target = e'.source)
  body: e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]

中文:
定义 trans'
  签名: (e' : PartialEquiv β γ) (h : e.target = e'.source)
  定义体: e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]
-/
protected def trans' (e' : PartialEquiv β γ) (h : e.target = e'.source) : PartialEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]

/-- Composing two partial equivs, by restricting to the maximal domain where their composition
is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ f` for this.
-/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: : PartialEquiv α γ
  body: PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)

@[simp, mfld_simps]

中文:
定义 trans
  签名: : PartialEquiv α γ
  定义体: PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)

@[simp, mfld_simps]
-/
protected def trans : PartialEquiv α γ :=
  PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)

@[simp, mfld_simps]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  statement: (e.trans e' : α -> γ) = e' ∘ e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_trans
  结论: (e.trans e' : α -> γ) = e' ∘ e
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_trans : (e.trans e' : α -> γ) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_trans_symm` / 定理 `coe_trans_symm`

English:
theorem coe_trans_symm
  statement: ((e.trans e').symm : γ -> α) = e.symm ∘ e'.symm
  proof: rfl

中文:
定理 coe_trans_symm
  结论: ((e.trans e').symm : γ -> α) = e.symm ∘ e'.symm
  证明: rfl
-/
theorem coe_trans_symm : ((e.trans e').symm : γ -> α) = e.symm ∘ e'.symm :=
  rfl

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: {x : α}
  statement: (e.trans e') x = e' (e x)
  proof: rfl

中文:
定理 trans_apply
  条件: {x : α}
  结论: (e.trans e') x = e' (e x)
  证明: rfl
-/
theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl

/--
theorem `trans_symm_eq_symm_trans_symm` / 定理 `trans_symm_eq_symm_trans_symm`

English:
theorem trans_symm_eq_symm_trans_symm
  statement: (e.trans e').symm = e'.symm.trans e.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trans_symm_eq_symm_trans_symm
  结论: (e.trans e').symm = e'.symm.trans e.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

@[simp, mfld_simps]
/--
theorem `trans_source` / 定理 `trans_source`

English:
theorem trans_source
  statement: (e.trans e').source = e.source inter e ⁻¹' e'.source
  proof: rfl

中文:
定理 trans_source
  结论: (e.trans e').source = e.source inter e ⁻¹' e'.source
  证明: rfl
-/
theorem trans_source : (e.trans e').source = e.source inter e ⁻¹' e'.source :=
  rfl

/--
theorem `trans_source'` / 定理 `trans_source'`

English:
theorem trans_source'
  statement: (e.trans e').source = e.source inter e ⁻¹' (e.target inter e'.source)
  proof: by
  mfld_set_tac

中文:
定理 trans_source'
  结论: (e.trans e').source = e.source inter e ⁻¹' (e.target inter e'.source)
  证明: by
  mfld_set_tac

Depends on / 依赖: mfld_set_tac
-/
theorem trans_source' : (e.trans e').source = e.source inter e ⁻¹' (e.target inter e'.source) := by
  mfld_set_tac

/--
theorem `trans_source''` / 定理 `trans_source''`

English:
theorem trans_source''
  statement: (e.trans e').source = e.symm '' (e.target inter e'.source)
  proof: by
  rw [e.trans_source']; rw [e.symm_image_target_inter_eq]

中文:
定理 trans_source''
  结论: (e.trans e').source = e.symm '' (e.target inter e'.source)
  证明: by
  rw [e.trans_source']; rw [e.symm_image_target_inter_eq]

Depends on / 依赖: e.symm_image_target_inter_eq, e.trans_source, symm_image_target_inter_eq, trans_source
-/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target inter e'.source) := by
  rw [e.trans_source']; rw [e.symm_image_target_inter_eq]

/--
theorem `image_trans_source` / 定理 `image_trans_source`

English:
theorem image_trans_source
  statement: e '' (e.trans e').source = e.target inter e'.source
  proof: (e.symm.restr e'.source).symm.image_source_eq_target

@[simp, mfld_simps]

中文:
定理 image_trans_source
  结论: e '' (e.trans e').source = e.target inter e'.source
  证明: (e.symm.restr e'.source).symm.image_source_eq_target

@[simp, mfld_simps]

Depends on / 依赖: e.symm.restr, image_source_eq_target, source, symm.image_source_eq_target
-/
theorem image_trans_source : e '' (e.trans e').source = e.target inter e'.source :=
  (e.symm.restr e'.source).symm.image_source_eq_target

@[simp, mfld_simps]
/--
theorem `trans_target` / 定理 `trans_target`

English:
theorem trans_target
  statement: (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target
  proof: rfl

中文:
定理 trans_target
  结论: (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target
  证明: rfl
-/
theorem trans_target : (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target :=
  rfl

/--
theorem `trans_target'` / 定理 `trans_target'`

English:
theorem trans_target'
  statement: (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.source inter e.target)
  proof: trans_source' e'.symm e.symm

中文:
定理 trans_target'
  结论: (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.source inter e.target)
  证明: trans_source' e'.symm e.symm

Depends on / 依赖: e.symm, trans_source
-/
theorem trans_target' : (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.source inter e.target) :=
  trans_source' e'.symm e.symm

/--
theorem `trans_target''` / 定理 `trans_target''`

English:
theorem trans_target''
  statement: (e.trans e').target = e' '' (e'.source inter e.target)
  proof: trans_source'' e'.symm e.symm

中文:
定理 trans_target''
  结论: (e.trans e').target = e' '' (e'.source inter e.target)
  证明: trans_source'' e'.symm e.symm

Depends on / 依赖: e.symm, trans_source
-/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source inter e.target) :=
  trans_source'' e'.symm e.symm

/--
theorem `inv_image_trans_target` / 定理 `inv_image_trans_target`

English:
theorem inv_image_trans_target
  statement: e'.symm '' (e.trans e').target = e'.source inter e.target
  proof: image_trans_source e'.symm e.symm

中文:
定理 inv_image_trans_target
  结论: e'.symm '' (e.trans e').target = e'.source inter e.target
  证明: image_trans_source e'.symm e.symm

Depends on / 依赖: e.symm, image_trans_source
-/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source inter e.target :=
  image_trans_source e'.symm e.symm

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (e'' : PartialEquiv γ δ)
  statement: (e.trans e').trans e'' = e.trans (e'.trans e'')
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp, mfld_simps]

中文:
定理 trans_assoc
  条件: (e'' : PartialEquiv γ δ)
  结论: (e.trans e').trans e'' = e.trans (e'.trans e'')
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, inter_assoc, preimage_comp, trans_source
-/
theorem trans_assoc (e'' : PartialEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp, mfld_simps]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  statement: e.trans (PartialEquiv.refl β) = e
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

@[simp, mfld_simps]

中文:
定理 trans_refl
  结论: e.trans (PartialEquiv.refl β) = e
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, trans_source
-/
theorem trans_refl : e.trans (PartialEquiv.refl β) = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

@[simp, mfld_simps]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  statement: (PartialEquiv.refl α).trans e = e
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source, preimage_id])

中文:
定理 refl_trans
  结论: (PartialEquiv.refl α).trans e = e
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source, preimage_id])

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, preimage_id, trans_source
-/
theorem refl_trans : (PartialEquiv.refl α).trans e = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source, preimage_id])

/--
theorem `trans_ofSet` / 定理 `trans_ofSet`

English:
theorem trans_ofSet
  given: (s : Set β)
  statement: e.trans (ofSet s) = e.restr (e ⁻¹' s)
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl

中文:
定理 trans_ofSet
  条件: (s : Set β)
  结论: e.trans (ofSet s) = e.restr (e ⁻¹' s)
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl

Depends on / 依赖: PartialEquiv, PartialEquiv.ext
-/
theorem trans_ofSet (s : Set β) : e.trans (ofSet s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl

/--
theorem `trans_refl_restr` / 定理 `trans_refl_restr`

English:
theorem trans_refl_restr
  given: (s : Set β)
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

中文:
定理 trans_refl_restr
  条件: (s : Set β)
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, trans_source
-/
theorem trans_refl_restr (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

/--
theorem `trans_refl_restr'` / 定理 `trans_refl_restr'`

English:
theorem trans_refl_restr'
  given: (s : Set β)
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) by
    simp only [trans_source, restr_source, refl_source, univ_inter]
    rw [← inter_assoc]; rw [inter_self]

中文:
定理 trans_refl_restr'
  条件: (s : Set β)
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) by
    simp only [trans_source, restr_source, refl_source, univ_inter]
    rw [← inter_assoc]; rw [inter_self]

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, inter_assoc, inter_self, refl_source, restr_source, trans_source, univ_inter
-/
theorem trans_refl_restr' (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e.source inter e ⁻¹' s) :=
PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) by
    simp only [trans_source, restr_source, refl_source, univ_inter]
    rw [← inter_assoc]; rw [inter_self]

/--
theorem `restr_trans` / 定理 `restr_trans`

English:
theorem restr_trans
  given: (s : Set α)
  statement: (e.restr s).trans e' = (e.trans e').restr s
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) by
    simp [trans_source, inter_comm, inter_assoc]

中文:
定理 restr_trans
  条件: (s : Set α)
  结论: (e.restr s).trans e' = (e.trans e').restr s
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) by
    simp [trans_source, inter_comm, inter_assoc]

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, inter_assoc, inter_comm, trans_source
-/
theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) by
    simp [trans_source, inter_comm, inter_assoc]

/--
theorem `mem_symm_trans_source` / 定理 `mem_symm_trans_source`

English:
theorem mem_symm_trans_source
  statement: {e' : PartialEquiv α γ} {x : α} (he : x in e.source)
  proof: ⟨e.mapsTo he, by rwa [mem_preimage, PartialEquiv.symm_symm, e.left_inv he]⟩

中文:
定理 mem_symm_trans_source
  结论: {e' : PartialEquiv α γ} {x : α} (he : x in e.source)
  证明: ⟨e.mapsTo he, by rwa [mem_preimage, PartialEquiv.symm_symm, e.left_inv he]⟩

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_symm, e.left_inv, e.mapsTo, left_inv, mapsTo, mem_preimage, symm_symm
-/
theorem mem_symm_trans_source {e' : PartialEquiv α γ} {x : α} (he : x in e.source)
    (he' : x in e'.source) : e x in (e.symm.trans e').source :=
  ⟨e.mapsTo he, by rwa [mem_preimage, PartialEquiv.symm_symm, e.left_inv he]⟩

/--
Definition of `EqOnSource` / `EqOnSource` 的定义

English:
definition EqOnSource
  signature: (e e' : PartialEquiv α β)
  body: e.source = e'.source ∧ e.source.EqOn e e'

中文:
定义 EqOnSource
  签名: (e e' : PartialEquiv α β)
  定义体: e.source = e'.source ∧ e.source.EqOn e e'

Depends on / 依赖: e.source, e.source.EqOn, source
-/
def EqOnSource (e e' : PartialEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'

/--
Instance `eqOnSourceSetoid` / 实例 `eqOnSourceSetoid`

English:
instance eqOnSourceSetoid
  signature: : Setoid (PartialEquiv α β) where
  body: EqOnSource
  iseqv := by constructor <;> grind [EqOnSource, EqOn]

中文:
实例 eqOnSourceSetoid
  签名: : Setoid (PartialEquiv α β) where
  定义体: EqOnSource
  iseqv := by constructor <;> grind [EqOnSource, EqOn]

Depends on / 依赖: EqOnSource
-/
instance eqOnSourceSetoid : Setoid (PartialEquiv α β) where
  r := EqOnSource
  iseqv := by constructor <;> grind [EqOnSource, EqOn]

/--
theorem `eqOnSource_refl` / 定理 `eqOnSource_refl`

English:
theorem eqOnSource_refl
  statement: e ≈ e
  proof: Setoid.refl _

中文:
定理 eqOnSource_refl
  结论: e ≈ e
  证明: Setoid.refl _

Depends on / 依赖: Setoid, Setoid.refl
-/
theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _

/--
theorem `EqOnSource.source_eq` / 定理 `EqOnSource.source_eq`

English:
theorem EqOnSource.source_eq
  given: {e e' : PartialEquiv α β} (h : e ≈ e')
  statement: e.source = e'.source
  proof: h.1

中文:
定理 EqOnSource.source_eq
  条件: {e e' : PartialEquiv α β} (h : e ≈ e')
  结论: e.source = e'.source
  证明: h.1
-/
theorem EqOnSource.source_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1

/--
theorem `EqOnSource.eqOn` / 定理 `EqOnSource.eqOn`

English:
theorem EqOnSource.eqOn
  given: {e e' : PartialEquiv α β} (h : e ≈ e')
  statement: e.source.EqOn e e'
  proof: h.2

中文:
定理 EqOnSource.eqOn
  条件: {e e' : PartialEquiv α β} (h : e ≈ e')
  结论: e.source.EqOn e e'
  证明: h.2
-/
theorem EqOnSource.eqOn {e e' : PartialEquiv α β} (h : e ≈ e') : e.source.EqOn e e' :=
  h.2

/--
theorem `EqOnSource.target_eq` / 定理 `EqOnSource.target_eq`

English:
theorem EqOnSource.target_eq
  given: {e e' : PartialEquiv α β} (h : e ≈ e')
  statement: e.target = e'.target
  proof: by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]

中文:
定理 EqOnSource.target_eq
  条件: {e e' : PartialEquiv α β} (h : e ≈ e')
  结论: e.target = e'.target
  证明: by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]

Depends on / 依赖: image_eq, image_source_eq_target, source_eq
-/
theorem EqOnSource.target_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.target = e'.target := by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]

/--
theorem `EqOnSource.symm'` / 定理 `EqOnSource.symm'`

English:
theorem EqOnSource.symm'
  given: {e e' : PartialEquiv α β} (h : e ≈ e')
  statement: e.symm ≈ e'.symm
  proof: by
  refine ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_source, target_eq h, source_eq h, e'.mapsTo_symm]
  exact e'.rightInvOn.congr_right e'.mapsTo_symm (source_eq h ▸ h.eqOn.symm)

中文:
定理 EqOnSource.symm'
  条件: {e e' : PartialEquiv α β} (h : e ≈ e')
  结论: e.symm ≈ e'.symm
  证明: by
  refine ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_source, target_eq h, source_eq h, e'.mapsTo_symm]
  exact e'.rightInvOn.congr_right e'.mapsTo_symm (source_eq h ▸ h.eqOn.symm)

Depends on / 依赖: congr_right, e.leftInvOn, eqOn_of_leftInvOn_of_rightInvOn, h.eqOn.symm, leftInvOn, mapsTo_symm, rightInvOn, rightInvOn.congr_right, source_eq, symm_source, target_eq
-/
theorem EqOnSource.symm' {e e' : PartialEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
  refine ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_source, target_eq h, source_eq h, e'.mapsTo_symm]
  exact e'.rightInvOn.congr_right e'.mapsTo_symm (source_eq h ▸ h.eqOn.symm)

/--
theorem `EqOnSource.symm_eqOn` / 定理 `EqOnSource.symm_eqOn`

English:
theorem EqOnSource.symm_eqOn
  given: {e e' : PartialEquiv α β} (h : e ≈ e')
  proof: eqOn h.symm'

中文:
定理 EqOnSource.symm_eqOn
  条件: {e e' : PartialEquiv α β} (h : e ≈ e')
  证明: eqOn h.symm'

Depends on / 依赖: h.symm
-/
theorem EqOnSource.symm_eqOn {e e' : PartialEquiv α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  eqOn h.symm'

/--
theorem `EqOnSource.trans'` / 定理 `EqOnSource.trans'`

English:
theorem EqOnSource.trans'
  statement: {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
  proof: by
  constructor
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    exact (he.symm'.eqOn.mono inter_subset_left).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [Function.comp_apply, PartialEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]

中文:
定理 EqOnSource.trans'
  结论: {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
  证明: by
  constructor
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    exact (he.symm'.eqOn.mono inter_subset_left).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [Function.comp_apply, PartialEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]

Depends on / 依赖: Function, Function.comp_apply, PartialEquiv, PartialEquiv.coe_trans, coe_trans, comp_apply, eqOn.mono, he.symm, image_eq, inter_subset_left, target_eq, trans_source
-/
theorem EqOnSource.trans' {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' := by
  constructor
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    exact (he.symm'.eqOn.mono inter_subset_left).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [Function.comp_apply, PartialEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]

/--
theorem `EqOnSource.restr` / 定理 `EqOnSource.restr`

English:
theorem EqOnSource.restr
  given: {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set α)
  proof: by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1

中文:
定理 EqOnSource.restr
  条件: {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set α)
  证明: by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1

Depends on / 依赖: mem_inter_iff, restr_source
-/
theorem EqOnSource.restr {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s := by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1

/--
theorem `EqOnSource.source_inter_preimage_eq` / 定理 `EqOnSource.source_inter_preimage_eq`

English:
theorem EqOnSource.source_inter_preimage_eq
  given: {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set β)
  proof: by rw [he.eqOn.inter_preimage_eq, source_eq he]

中文:
定理 EqOnSource.source_inter_preimage_eq
  条件: {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set β)
  证明: by rw [he.eqOn.inter_preimage_eq, source_eq he]

Depends on / 依赖: he.eqOn.inter_preimage_eq, inter_preimage_eq, source_eq
-/
theorem EqOnSource.source_inter_preimage_eq {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set β) :
    e.source inter e ⁻¹' s = e'.source inter e' ⁻¹' s := by rw [he.eqOn.inter_preimage_eq, source_eq he]

/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  statement: e.trans e.symm ≈ ofSet e.source
  proof: by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine ⟨by rw [A, ofSet_source], fun x hx => ?_⟩
  rw [A] at hx
  simp only [hx, mfld_simps]

中文:
定理 self_trans_symm
  结论: e.trans e.symm ≈ ofSet e.source
  证明: by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine ⟨by rw [A, ofSet_source], fun x hx => ?_⟩
  rw [A] at hx
  simp only [hx, mfld_simps]

Depends on / 依赖: e.source, e.symm, e.trans, mfld_set_tac, mfld_simps, ofSet_source, source
-/
theorem self_trans_symm : e.trans e.symm ≈ ofSet e.source := by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine ⟨by rw [A, ofSet_source], fun x hx => ?_⟩
  rw [A] at hx
  simp only [hx, mfld_simps]

/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  statement: e.symm.trans e ≈ ofSet e.target
  proof: self_trans_symm e.symm

中文:
定理 symm_trans_self
  结论: e.symm.trans e ≈ ofSet e.target
  证明: self_trans_symm e.symm

Depends on / 依赖: e.symm, self_trans_symm
-/
theorem symm_trans_self : e.symm.trans e ≈ ofSet e.target :=
  self_trans_symm e.symm

/--
theorem `eq_of_eqOnSource_univ` / 定理 `eq_of_eqOnSource_univ`

English:
theorem eq_of_eqOnSource_univ
  statement: (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source = univ)
  proof: by
  refine PartialEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source]; rw [t]
    exact mem_univ _

中文:
定理 eq_of_eqOnSource_univ
  结论: (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source = univ)
  证明: by
  refine PartialEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source]; rw [t]
    exact mem_univ _

Depends on / 依赖: PartialEquiv, PartialEquiv.ext, h.symm, mem_univ, symm_source
-/
theorem eq_of_eqOnSource_univ (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' := by
  refine PartialEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source]; rw [t]
    exact mem_univ _

section Prod

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  body: e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp := by simp_all
  right_inv' p hp := by simp_all

@[simp, mfld_simps]

中文:
定义 prod
  签名: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  定义体: e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp := by simp_all
  right_inv' p hp := by simp_all

@[simp, mfld_simps]

Depends on / 依赖: e.source, source
-/
def prod (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : PartialEquiv (α × γ) (β × δ) where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp := by simp_all
  right_inv' p hp := by simp_all

@[simp, mfld_simps]
/--
theorem `prod_source` / 定理 `prod_source`

English:
theorem prod_source
  given: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 prod_source
  条件: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  证明: rfl

@[simp, mfld_simps]
-/
theorem prod_source (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').source = e.source ×ˢ e'.source :=
  rfl

@[simp, mfld_simps]
/--
theorem `prod_target` / 定理 `prod_target`

English:
theorem prod_target
  given: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 prod_target
  条件: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  证明: rfl

@[simp, mfld_simps]
-/
theorem prod_target (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').target = e.target ×ˢ e'.target :=
  rfl

@[simp, mfld_simps]
/--
theorem `prod_coe` / 定理 `prod_coe`

English:
theorem prod_coe
  given: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  proof: rfl

中文:
定理 prod_coe
  条件: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  证明: rfl
-/
theorem prod_coe (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e' : α × γ -> β × δ) = fun p => (e p.1, e' p.2) :=
  rfl

/--
theorem `prod_coe_symm` / 定理 `prod_coe_symm`

English:
theorem prod_coe_symm
  given: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 prod_coe_symm
  条件: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  证明: rfl

@[simp, mfld_simps]
-/
theorem prod_coe_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    ((e.prod e').symm : β × δ -> α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl

@[simp, mfld_simps]
/--
theorem `prod_symm` / 定理 `prod_symm`

English:
theorem prod_symm
  given: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  proof: by
  ext x <;> simp [prod_coe_symm]

@[simp, mfld_simps]

中文:
定理 prod_symm
  条件: (e : PartialEquiv α β) (e' : PartialEquiv γ δ)
  证明: by
  ext x <;> simp [prod_coe_symm]

@[simp, mfld_simps]

Depends on / 依赖: prod_coe_symm
-/
theorem prod_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm := by
  ext x <;> simp [prod_coe_symm]

@[simp, mfld_simps]
/--
theorem `refl_prod_refl` / 定理 `refl_prod_refl`

English:
theorem refl_prod_refl
  proof: by
  ext ⟨x, y⟩ <;> simp

@[simp, mfld_simps]

中文:
定理 refl_prod_refl
  证明: by
  ext ⟨x, y⟩ <;> simp

@[simp, mfld_simps]
-/
theorem refl_prod_refl :
    (PartialEquiv.refl α).prod (PartialEquiv.refl β) = PartialEquiv.refl (α × β) := by
  ext ⟨x, y⟩ <;> simp

@[simp, mfld_simps]
/--
theorem `prod_trans` / 定理 `prod_trans`

English:
theorem prod_trans
  statement: {η : Type*} {ε : Type*} (e : PartialEquiv α β) (f : PartialEquiv β γ)
  proof: by
  ext ⟨x, y⟩ <;> simp; tauto

中文:
定理 prod_trans
  结论: {η : 类型} {ε : 类型} (e : PartialEquiv α β) (f : PartialEquiv β γ)
  证明: by
  ext ⟨x, y⟩ <;> simp; tauto
-/
theorem prod_trans {η : Type*} {ε : Type*} (e : PartialEquiv α β) (f : PartialEquiv β γ)
    (e' : PartialEquiv δ η) (f' : PartialEquiv η ε) :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') := by
  ext ⟨x, y⟩ <;> simp; tauto

end Prod

/-- Combine two `PartialEquiv`s using `Set.piecewise`. The source of the new `PartialEquiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target. The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.isImage s t` and
`e'.isImage s t`. -/
@[simps -fullyApplied]
/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [forall x, Decidable (x in s)]
  body: s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_

中文:
定义 piecewise
  签名: (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [对任意 x, Decidable (x in s)]
  定义体: s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_

Depends on / 依赖: piecewise, s.piecewise
-/
def piecewise (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [forall x, Decidable (x in s)]
    [forall y, Decidable (y in t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    PartialEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm

/--
theorem `symm_piecewise` / 定理 `symm_piecewise`

English:
theorem symm_piecewise
  statement: (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [forall x, Decidable (x in s)]
  proof: rfl

中文:
定理 symm_piecewise
  结论: (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [对任意 x, Decidable (x in s)]
  证明: rfl
-/
theorem symm_piecewise (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [forall x, Decidable (x in s)]
    [forall y, Decidable (y in t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl

/-- Combine two `PartialEquiv`s with disjoint sources and disjoint targets. We reuse
`PartialEquiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps! -fullyApplied]
/--
Definition of `disjointUnion` / `disjointUnion` 的定义

English:
definition disjointUnion
  signature: (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
  body: (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source union e'.source) (ite_left _ _) (e.target union e'.target) (ite_left _ _)

中文:
定义 disjointUnion
  签名: (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
  定义体: (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source union e'.source) (ite_left _ _) (e.target union e'.target) (ite_left _ _)

Depends on / 依赖: e.isImage_source_target, e.piecewise, e.source, e.target, hs.symm, ht.symm, isImage_source_target, isImage_source_target_of_disjoint, ite_left, piecewise, source, target
-/
def disjointUnion (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [forall x, Decidable (x in e.source)]
    [forall y, Decidable (y in e.target)] : PartialEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source union e'.source) (ite_left _ _) (e.target union e'.target) (ite_left _ _)

/--
theorem `disjointUnion_eq_piecewise` / 定理 `disjointUnion_eq_piecewise`

English:
theorem disjointUnion_eq_piecewise
  statement: (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
  proof: copy_eq ..

中文:
定理 disjointUnion_eq_piecewise
  结论: (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
  证明: copy_eq ..

Depends on / 依赖: copy_eq
-/
theorem disjointUnion_eq_piecewise (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [forall x, Decidable (x in e.source)]
    [forall y, Decidable (y in e.target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq ..

section Pi

variable {ι : Type*} {αi βi γi : ι -> Type*}

/-- The product of a family of partial equivalences, as a partial equivalence on the pi type. -/
@[simps (attr := mfld_simps) -fullyApplied apply source target]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (ei : forall i, PartialEquiv (αi i) (βi i))
  body: Pi.map fun i => ei i
  invFun := Pi.map fun i => (ei i).symm
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).

中文:
定义 pi
  签名: (ei : 对任意 i, PartialEquiv (αi i) (βi i))
  定义体: Pi.map fun i => ei i
  invFun := Pi.map fun i => (ei i).symm
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).
-/
protected def pi (ei : forall i, PartialEquiv (αi i) (βi i)) : PartialEquiv (forall i, αi i) (forall i, βi i) where
  toFun := Pi.map fun i => ei i
  invFun := Pi.map fun i => (ei i).symm
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' _ hf := funext fun i => (ei i).right_inv (hf i trivial)

@[simp, mfld_simps]
/--
theorem `pi_symm` / 定理 `pi_symm`

English:
theorem pi_symm
  given: (ei : forall i, PartialEquiv (αi i) (βi i))
  proof: rfl

中文:
定理 pi_symm
  条件: (ei : 对任意 i, PartialEquiv (αi i) (βi i))
  证明: rfl
-/
theorem pi_symm (ei : forall i, PartialEquiv (αi i) (βi i)) :
    (PartialEquiv.pi ei).symm = .pi fun i => (ei i).symm :=
  rfl

/--
theorem `pi_symm_apply` / 定理 `pi_symm_apply`

English:
theorem pi_symm_apply
  given: (ei : forall i, PartialEquiv (αi i) (βi i))
  proof: rfl

@[simp, mfld_simps]

中文:
定理 pi_symm_apply
  条件: (ei : 对任意 i, PartialEquiv (αi i) (βi i))
  证明: rfl

@[simp, mfld_simps]
-/
theorem pi_symm_apply (ei : forall i, PartialEquiv (αi i) (βi i)) :
    ⇑(PartialEquiv.pi ei).symm = fun f i => (ei i).symm (f i) :=
  rfl

@[simp, mfld_simps]
/--
theorem `pi_refl` / 定理 `pi_refl`

English:
theorem pi_refl
  statement: (PartialEquiv.pi fun i => PartialEquiv.refl (αi i)) = .refl (forall i, αi i)
  proof: by
  ext <;> simp

@[simp, mfld_simps]

中文:
定理 pi_refl
  结论: (PartialEquiv.pi fun i => PartialEquiv.refl (αi i)) = .refl (对任意 i, αi i)
  证明: by
  ext <;> simp

@[simp, mfld_simps]
-/
theorem pi_refl : (PartialEquiv.pi fun i => PartialEquiv.refl (αi i)) = .refl (forall i, αi i) := by
  ext <;> simp

@[simp, mfld_simps]
/--
theorem `pi_trans` / 定理 `pi_trans`

English:
theorem pi_trans
  given: (ei : forall i, PartialEquiv (αi i) (βi i)) (ei' : forall i, PartialEquiv (βi i) (γi i))
  proof: by
  ext <;> simp [forall_and]

中文:
定理 pi_trans
  条件: (ei : 对任意 i, PartialEquiv (αi i) (βi i)) (ei' : 对任意 i, PartialEquiv (βi i) (γi i))
  证明: by
  ext <;> simp [forall_and]

Depends on / 依赖: forall_and
-/
theorem pi_trans (ei : forall i, PartialEquiv (αi i) (βi i)) (ei' : forall i, PartialEquiv (βi i) (γi i)) :
    (PartialEquiv.pi ei).trans (PartialEquiv.pi ei') = .pi fun i => (ei i).trans (ei' i) := by
  ext <;> simp [forall_and]

end Pi

/--
lemma `surjective_of_target_eq_univ` / 引理 `surjective_of_target_eq_univ`

English:
lemma surjective_of_target_eq_univ
  given: (h : e.target = univ)
  proof: surjOn_univ.mp e.surjOn.mono (by simp) (by simp [h])

中文:
引理 surjective_of_target_eq_univ
  条件: (h : e.target = univ)
  证明: surjOn_univ.mp e.surjOn.mono (by simp) (by simp [h])

Depends on / 依赖: e.surjOn.mono, surjOn, surjOn_univ, surjOn_univ.mp
-/
lemma surjective_of_target_eq_univ (h : e.target = univ) :
    Surjective e :=
surjOn_univ.mp e.surjOn.mono (by simp) (by simp [h])

/--
lemma `injective_of_source_eq_univ` / 引理 `injective_of_source_eq_univ`

English:
lemma injective_of_source_eq_univ
  given: (h : e.source = univ)
  statement: Injective e
  proof: by simpa [h] using e.injOn

中文:
引理 injective_of_source_eq_univ
  条件: (h : e.source = univ)
  结论: Injective e
  证明: by simpa [h] using e.injOn

Depends on / 依赖: e.injOn
-/
lemma injective_of_source_eq_univ (h : e.source = univ) : Injective e := by simpa [h] using e.injOn

/--
lemma `injective_symm_of_target_eq_univ` / 引理 `injective_symm_of_target_eq_univ`

English:
lemma injective_symm_of_target_eq_univ
  given: (h : e.target = univ)
  proof: e.symm.injective_of_source_eq_univ h

中文:
引理 injective_symm_of_target_eq_univ
  条件: (h : e.target = univ)
  证明: e.symm.injective_of_source_eq_univ h

Depends on / 依赖: e.symm.injective_of_source_eq_univ, injective_of_source_eq_univ
-/
lemma injective_symm_of_target_eq_univ (h : e.target = univ) :
    Injective e.symm :=
  e.symm.injective_of_source_eq_univ h

/--
lemma `surjective_symm_of_source_eq_univ` / 引理 `surjective_symm_of_source_eq_univ`

English:
lemma surjective_symm_of_source_eq_univ
  given: (h : e.source = univ)
  proof: e.symm.surjective_of_target_eq_univ h

中文:
引理 surjective_symm_of_source_eq_univ
  条件: (h : e.source = univ)
  证明: e.symm.surjective_of_target_eq_univ h

Depends on / 依赖: e.symm.surjective_of_target_eq_univ, surjective_of_target_eq_univ
-/
lemma surjective_symm_of_source_eq_univ (h : e.source = univ) :
    Surjective e.symm :=
  e.symm.surjective_of_target_eq_univ h

end PartialEquiv

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : Set α` and `t : Set β` provides a partial equivalence
between `α` and `β`. -/
@[simps -fullyApplied]
/--
Definition of `BijOn.toPartialEquiv` / `BijOn.toPartialEquiv` 的定义

English:
definition BijOn.toPartialEquiv
  signature: [Nonempty α] (f : α -> β) (s : Set α) (t : Set β)
  body: f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

中文:
定义 BijOn.toPartialEquiv
  签名: [Nonempty α] (f : α -> β) (s : Set α) (t : Set β)
  定义体: f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2
-/
noncomputable def BijOn.toPartialEquiv [Nonempty α] (f : α -> β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : PartialEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

/-- A map injective on a subset of its domain provides a partial equivalence. -/
@[simp, mfld_simps]
/--
Definition of `InjOn.toPartialEquiv` / `InjOn.toPartialEquiv` 的定义

English:
definition InjOn.toPartialEquiv
  signature: [Nonempty α] (f : α -> β) (s : Set α) (hf : InjOn f s)
  body: hf.bijOn_image.toPartialEquiv f s (f '' s)

中文:
定义 InjOn.toPartialEquiv
  签名: [Nonempty α] (f : α -> β) (s : Set α) (hf : InjOn f s)
  定义体: hf.bijOn_image.toPartialEquiv f s (f '' s)

Depends on / 依赖: bijOn_image, hf.bijOn_image.toPartialEquiv, toPartialEquiv
-/
noncomputable def InjOn.toPartialEquiv [Nonempty α] (f : α -> β) (s : Set α) (hf : InjOn f s) :
    PartialEquiv α β :=
  hf.bijOn_image.toPartialEquiv f s (f '' s)

end Set

namespace Equiv

/- `Equiv`s give rise to `PartialEquiv`s. We set up simp lemmas to reduce most properties of the
`PartialEquiv` to that of the `Equiv`. -/
variable (e : α ≃ β) (e' : β ≃ γ)

@[simp, mfld_simps]
/--
theorem `refl_toPartialEquiv` / 定理 `refl_toPartialEquiv`

English:
theorem refl_toPartialEquiv
  statement: (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α
  proof: rfl

@[simp, mfld_simps]

中文:
定理 refl_toPartialEquiv
  结论: (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α
  证明: rfl

@[simp, mfld_simps]
-/
theorem refl_toPartialEquiv : (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α :=
  rfl

@[simp, mfld_simps]
/--
theorem `symm_toPartialEquiv` / 定理 `symm_toPartialEquiv`

English:
theorem symm_toPartialEquiv
  statement: e.symm.toPartialEquiv = e.toPartialEquiv.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 symm_toPartialEquiv
  结论: e.symm.toPartialEquiv = e.toPartialEquiv.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `trans_toPartialEquiv` / 定理 `trans_toPartialEquiv`

English:
theorem trans_toPartialEquiv
  proof: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [PartialEquiv.trans_source, Equiv.toPartialEquiv])

中文:
定理 trans_toPartialEquiv
  证明: PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [PartialEquiv.trans_source, Equiv.toPartialEquiv])

Depends on / 依赖: Equiv.toPartialEquiv, PartialEquiv, PartialEquiv.ext, PartialEquiv.trans_source, toPartialEquiv, trans_source
-/
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [PartialEquiv.trans_source, Equiv.toPartialEquiv])

/-- Precompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
/--
Definition of `transPartialEquiv` / `transPartialEquiv` 的定义

English:
definition transPartialEquiv
  signature: (e : α ≃ β) (f' : PartialEquiv β γ)
  body: (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)

中文:
定义 transPartialEquiv
  签名: (e : α ≃ β) (f' : PartialEquiv β γ)
  定义体: (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)

Depends on / 依赖: e.toPartialEquiv.trans, inter_univ, source, target, toPartialEquiv, univ_inter
-/
def transPartialEquiv (e : α ≃ β) (f' : PartialEquiv β γ) : PartialEquiv α γ :=
  (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)

/--
theorem `transPartialEquiv_eq_trans` / 定理 `transPartialEquiv_eq_trans`

English:
theorem transPartialEquiv_eq_trans
  given: (e : α ≃ β) (f' : PartialEquiv β γ)
  proof: PartialEquiv.copy_eq ..

@[simp, mfld_simps]

中文:
定理 transPartialEquiv_eq_trans
  条件: (e : α ≃ β) (f' : PartialEquiv β γ)
  证明: PartialEquiv.copy_eq ..

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.copy_eq, copy_eq
-/
theorem transPartialEquiv_eq_trans (e : α ≃ β) (f' : PartialEquiv β γ) :
    e.transPartialEquiv f' = e.toPartialEquiv.trans f' :=
  PartialEquiv.copy_eq ..

@[simp, mfld_simps]
/--
theorem `transPartialEquiv_trans` / 定理 `transPartialEquiv_trans`

English:
theorem transPartialEquiv_trans
  given: (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : PartialEquiv γ δ)
  proof: by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc]

@[simp, mfld_simps]

中文:
定理 transPartialEquiv_trans
  条件: (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : PartialEquiv γ δ)
  证明: by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc]

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.trans_assoc, transPartialEquiv_eq_trans, trans_assoc
-/
theorem transPartialEquiv_trans (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : PartialEquiv γ δ) :
    (e.transPartialEquiv f').trans f'' = e.transPartialEquiv (f'.trans f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc]

@[simp, mfld_simps]
/--
theorem `trans_transPartialEquiv` / 定理 `trans_transPartialEquiv`

English:
theorem trans_transPartialEquiv
  given: (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ)
  proof: by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc, trans_toPartialEquiv]

@[simp]

中文:
定理 trans_transPartialEquiv
  条件: (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ)
  证明: by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc, trans_toPartialEquiv]

@[simp]

Depends on / 依赖: PartialEquiv, PartialEquiv.trans_assoc, transPartialEquiv_eq_trans, trans_assoc, trans_toPartialEquiv
-/
theorem trans_transPartialEquiv (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ) :
    (e.trans e').transPartialEquiv f'' = e.transPartialEquiv (e'.transPartialEquiv f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc, trans_toPartialEquiv]

@[simp]
/--
lemma `coe_transPartialEquiv` / 引理 `coe_transPartialEquiv`

English:
lemma coe_transPartialEquiv
  given: {f : α ≃ β} {g : PartialEquiv β γ}
  statement: f.transPartialEquiv g = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_transPartialEquiv
  条件: {f : α ≃ β} {g : PartialEquiv β γ}
  结论: f.transPartialEquiv g = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_transPartialEquiv {f : α ≃ β} {g : PartialEquiv β γ} : f.transPartialEquiv g = g ∘ f :=
  rfl

@[simp]
/--
lemma `coe_transPartialEquiv_symm` / 引理 `coe_transPartialEquiv_symm`

English:
lemma coe_transPartialEquiv_symm
  given: {f : α ≃ β} {g : PartialEquiv β γ}
  proof: rfl

中文:
引理 coe_transPartialEquiv_symm
  条件: {f : α ≃ β} {g : PartialEquiv β γ}
  证明: rfl
-/
lemma coe_transPartialEquiv_symm {f : α ≃ β} {g : PartialEquiv β γ} :
    (f.transPartialEquiv g).symm = f.symm ∘ g.symm :=
  rfl

end Equiv

namespace PartialEquiv

/-- Postcompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
/--
Definition of `transEquiv` / `transEquiv` 的定义

English:
definition transEquiv
  signature: (e : PartialEquiv α β) (f' : β ≃ γ)
  body: (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)

中文:
定义 transEquiv
  签名: (e : PartialEquiv α β) (f' : β ≃ γ)
  定义体: (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)

Depends on / 依赖: e.source, e.target, e.trans, inter_univ, source, target, toPartialEquiv, univ_inter
-/
def transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) : PartialEquiv α γ :=
  (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)

/--
theorem `transEquiv_eq_trans` / 定理 `transEquiv_eq_trans`

English:
theorem transEquiv_eq_trans
  given: (e : PartialEquiv α β) (e' : β ≃ γ)
  proof: copy_eq ..

@[simp, mfld_simps]

中文:
定理 transEquiv_eq_trans
  条件: (e : PartialEquiv α β) (e' : β ≃ γ)
  证明: copy_eq ..

@[simp, mfld_simps]

Depends on / 依赖: copy_eq
-/
theorem transEquiv_eq_trans (e : PartialEquiv α β) (e' : β ≃ γ) :
    e.transEquiv e' = e.trans e'.toPartialEquiv :=
  copy_eq ..

@[simp, mfld_simps]
/--
theorem `transEquiv_transEquiv` / 定理 `transEquiv_transEquiv`

English:
theorem transEquiv_transEquiv
  given: (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ)
  proof: by
  simp only [transEquiv_eq_trans, trans_assoc, Equiv.trans_toPartialEquiv]

@[simp, mfld_simps]

中文:
定理 transEquiv_transEquiv
  条件: (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ)
  证明: by
  simp only [transEquiv_eq_trans, trans_assoc, Equiv.trans_toPartialEquiv]

@[simp, mfld_simps]

Depends on / 依赖: Equiv.trans_toPartialEquiv, transEquiv_eq_trans, trans_assoc, trans_toPartialEquiv
-/
theorem transEquiv_transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ) :
    (e.transEquiv f').transEquiv f'' = e.transEquiv (f'.trans f'') := by
  simp only [transEquiv_eq_trans, trans_assoc, Equiv.trans_toPartialEquiv]

@[simp, mfld_simps]
/--
theorem `trans_transEquiv` / 定理 `trans_transEquiv`

English:
theorem trans_transEquiv
  given: (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃ δ)
  proof: by
  simp only [transEquiv_eq_trans, trans_assoc]

中文:
定理 trans_transEquiv
  条件: (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃ δ)
  证明: by
  simp only [transEquiv_eq_trans, trans_assoc]

Depends on / 依赖: transEquiv_eq_trans, trans_assoc
-/
theorem trans_transEquiv (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃ δ) :
    (e.trans e').transEquiv f'' = e.trans (e'.transEquiv f'') := by
  simp only [transEquiv_eq_trans, trans_assoc]

/--
lemma `coe_transEquiv` / 引理 `coe_transEquiv`

English:
lemma coe_transEquiv
  given: {f : PartialEquiv α β} {g : β ≃ γ}
  statement: f.transEquiv g = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_transEquiv
  条件: {f : PartialEquiv α β} {g : β ≃ γ}
  结论: f.transEquiv g = g ∘ f
  证明: rfl

@[simp]
-/
@[simp] lemma coe_transEquiv {f : PartialEquiv α β} {g : β ≃ γ} : f.transEquiv g = g ∘ f := rfl

@[simp]
/--
lemma `coe_transEquiv_symm` / 引理 `coe_transEquiv_symm`

English:
lemma coe_transEquiv_symm
  given: {f : PartialEquiv α β} {g : β ≃ γ}
  proof: rfl

中文:
引理 coe_transEquiv_symm
  条件: {f : PartialEquiv α β} {g : β ≃ γ}
  证明: rfl
-/
lemma coe_transEquiv_symm {f : PartialEquiv α β} {g : β ≃ γ} :
    (f.transEquiv g).symm = f.symm ∘ g.symm :=
  rfl

end PartialEquiv
