/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Topology.ContinuousOn

/-!
# Partial homeomorphisms: definitions

This file defines homeomorphisms between subsets of topological spaces. An element `e` of
`PartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that the functions are continuous on them. Equivalently, they are
homeomorphisms there.

As for `Equiv`s, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

This file is intentionally kept small; many other constructions of, and lemmas about,
partial homeomorphisms can be found in other files under `Mathlib/Topology/PartialHomeomorph/`.

* `Homeomorph.toPartialHomeomorph`: associating a partial homeomorphism to a
  homeomorphism, with `source = target = Set.univ`;
* `PartialHomeomorph.symm`: the inverse of a partial homeomorphism

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

/--
Definition of `PartialHomeomorph` / `PartialHomeomorph` 的定义

English:
structure PartialHomeomorph
  parameters: (X : Type*) (Y : Type*) [TopologicalSpace X]
  extends: PartialEquiv X Y
  axioms and operations (2):
    - continuousOn_toFun : ContinuousOn toFun source
    - continuousOn_invFun : ContinuousOn invFun target

中文:
结构 PartialHomeomorph
  参数: (X : 类型) (Y : 类型) [拓扑空间 X]
  继承: 部分等价 X Y
  公理与运算 (2 个):
    - continuousOn_toFun : ContinuousOn toFun source
    - continuousOn_invFun : ContinuousOn invFun target
-/
structure PartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] extends PartialEquiv X Y where
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-! Basic properties; inverse (symm instance) -/
section Basic
/--
Definition of `toFun'` / `toFun'` 的定义

English:
definition toFun'
  signature: : X -> Y
  body: e.toFun

中文:
定义 toFun'
  签名: : X -> Y
  定义体: e.toFun
-/
@[coe] def toFun' : X -> Y := e.toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (PartialHomeomorph X Y) fun _ => X -> Y
  body: ⟨fun e => e.toFun'⟩

中文:
实例 :
  签名: CoeFun (PartialHomeomorph X Y) fun _ => X -> Y
  定义体: ⟨fun e => e.toFun'⟩

Depends on / 依赖: e.toFun
-/
instance : CoeFun (PartialHomeomorph X Y) fun _ => X -> Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of a partial homeomorphism -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : PartialHomeomorph Y X where
  body: e.toPartialEquiv.symm
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun

中文:
定义 symm
  签名: : PartialHomeomorph Y X where
  定义体: e.toPartialEquiv.symm
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun
-/
protected def symm : PartialHomeomorph Y X where
  toPartialEquiv := e.toPartialEquiv.symm
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : PartialHomeomorph X Y)
  body: e

中文:
定义 Simps.apply
  签名: (e : PartialHomeomorph X Y)
  定义体: e
-/
def Simps.apply (e : PartialHomeomorph X Y) : X -> Y := e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : PartialHomeomorph X Y)
  body: e.symm

initialize_simps_projections PartialHomeomorph (toFun -> apply, invFun -> symm_apply)

@[fun_prop]

中文:
定义 Simps.symm_apply
  签名: (e : PartialHomeomorph X Y)
  定义体: e.symm

initialize_simps_projections PartialHomeomorph (toFun -> apply, invFun -> symm_apply)

@[fun_prop]
-/
def Simps.symm_apply (e : PartialHomeomorph X Y) : Y -> X := e.symm

initialize_simps_projections PartialHomeomorph (toFun -> apply, invFun -> symm_apply)

@[fun_prop]
/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  statement: ContinuousOn e e.source
  proof: e.continuousOn_toFun

@[fun_prop]

中文:
定理 continuousOn
  结论: ContinuousOn e e.source
  证明: e.continuousOn_toFun

@[fun_prop]
-/
protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun

@[fun_prop]
/--
theorem `continuousOn_symm` / 定理 `continuousOn_symm`

English:
theorem continuousOn_symm
  statement: ContinuousOn e.symm e.target
  proof: e.continuousOn_invFun

@[simp]

中文:
定理 continuousOn_symm
  结论: ContinuousOn e.symm e.target
  证明: e.continuousOn_invFun

@[simp]

Depends on / 依赖: continuousOn_invFun, e.continuousOn_invFun
-/
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : PartialEquiv X Y) (h₁ h₂)
  statement: (PartialHomeomorph.mk e h₁ h₂ : X -> Y) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e : 部分等价 X Y) (h₁ h₂)
  结论: (PartialHomeomorph.mk e h₁ h₂ : X -> Y) = e
  证明: rfl

@[simp]
-/
theorem coe_mk (e : PartialEquiv X Y) (h₁ h₂) : (PartialHomeomorph.mk e h₁ h₂ : X -> Y) = e := rfl

@[simp]
/--
theorem `coe_mk_symm` / 定理 `coe_mk_symm`

English:
theorem coe_mk_symm
  given: (e : PartialEquiv X Y) (h₁ h₂)
  proof: rfl

中文:
定理 coe_mk_symm
  条件: (e : 部分等价 X Y) (h₁ h₂)
  证明: rfl
-/
theorem coe_mk_symm (e : PartialEquiv X Y) (h₁ h₂) :
    ((PartialHomeomorph.mk e h₁ h₂).symm : Y -> X) = e.symm :=
  rfl

/--
theorem `toPartialEquiv_injective` / 定理 `toPartialEquiv_injective`

English:
theorem toPartialEquiv_injective

中文:
定理 toPartialEquiv_injective
-/
theorem toPartialEquiv_injective :
    Injective (toPartialEquiv : PartialHomeomorph X Y -> PartialEquiv X Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (e : PartialHomeomorph X Y)
  statement: e.toFun = e
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: (e : PartialHomeomorph X Y)
  结论: e.toFun = e
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe (e : PartialHomeomorph X Y) : e.toFun = e :=
  rfl

@[simp]
/--
theorem `invFun_eq_coe` / 定理 `invFun_eq_coe`

English:
theorem invFun_eq_coe
  given: (e : PartialHomeomorph X Y)
  statement: e.invFun = e.symm
  proof: rfl

@[simp]

中文:
定理 invFun_eq_coe
  条件: (e : PartialHomeomorph X Y)
  结论: e.invFun = e.symm
  证明: rfl

@[simp]
-/
theorem invFun_eq_coe (e : PartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl

@[simp]
/--
theorem `coe_toPartialEquiv` / 定理 `coe_toPartialEquiv`

English:
theorem coe_toPartialEquiv
  statement: (e.toPartialEquiv : X -> Y) = e
  proof: rfl

@[simp]

中文:
定理 coe_toPartialEquiv
  结论: (e.toPartialEquiv : X -> Y) = e
  证明: rfl

@[simp]
-/
theorem coe_toPartialEquiv : (e.toPartialEquiv : X -> Y) = e :=
  rfl

@[simp]
/--
theorem `coe_toPartialEquiv_symm` / 定理 `coe_toPartialEquiv_symm`

English:
theorem coe_toPartialEquiv_symm
  statement: (e.toPartialEquiv.symm : Y -> X) = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_toPartialEquiv_symm
  结论: (e.toPartialEquiv.symm : Y -> X) = e.symm
  证明: rfl

@[simp]
-/
theorem coe_toPartialEquiv_symm : (e.toPartialEquiv.symm : Y -> X) = e.symm :=
  rfl

@[simp]
/--
theorem `map_source` / 定理 `map_source`

English:
theorem map_source
  given: {x : X} (h : x in e.source)
  statement: e x in e.target
  proof: e.map_source' h

中文:
定理 map_source
  条件: {x : X} (h : x in e.source)
  结论: e x in e.target
  证明: e.map_source' h

Depends on / 依赖: e.map_source, map_source
-/
theorem map_source {x : X} (h : x in e.source) : e x in e.target :=
  e.map_source' h

/--
lemma `image_source_subset` / 引理 `image_source_subset`

English:
lemma image_source_subset
  statement: e '' e.source subseteq e.target
  proof: fun _ ⟨_, hx, hex⟩ => mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp]

中文:
引理 image_source_subset
  结论: e '' e.source subseteq e.target
  证明: fun _ ⟨_, hx, hex⟩ => mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp]

Depends on / 依赖: e.map_source, hex.symm, map_source, mem_of_eq_of_mem
-/
lemma image_source_subset : e '' e.source subseteq e.target :=
  fun _ ⟨_, hx, hex⟩ => mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp]
/--
theorem `map_target` / 定理 `map_target`

English:
theorem map_target
  given: {x : Y} (h : x in e.target)
  statement: e.symm x in e.source
  proof: e.map_target' h

@[simp]

中文:
定理 map_target
  条件: {x : Y} (h : x in e.target)
  结论: e.symm x in e.source
  证明: e.map_target' h

@[simp]

Depends on / 依赖: e.map_target, map_target
-/
theorem map_target {x : Y} (h : x in e.target) : e.symm x in e.source :=
  e.map_target' h

@[simp]
/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: {x : X} (h : x in e.source)
  statement: e.symm (e x) = x
  proof: e.left_inv' h

@[simp]

中文:
定理 left_inv
  条件: {x : X} (h : x in e.source)
  结论: e.symm (e x) = x
  证明: e.left_inv' h

@[simp]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem left_inv {x : X} (h : x in e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp]
/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: {x : Y} (h : x in e.target)
  statement: e (e.symm x) = x
  proof: e.right_inv' h

中文:
定理 right_inv
  条件: {x : Y} (h : x in e.target)
  结论: e (e.symm x) = x
  证明: e.right_inv' h

Depends on / 依赖: e.right_inv, right_inv
-/
theorem right_inv {x : Y} (h : x in e.target) : e (e.symm x) = x :=
  e.right_inv' h

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {x : X} {y : Y} (hx : x in e.source) (hy : y in e.target)
  proof: e.toPartialEquiv.eq_symm_apply hx hy

中文:
定理 eq_symm_apply
  条件: {x : X} {y : Y} (hx : x in e.source) (hy : y in e.target)
  证明: e.toPartialEquiv.eq_symm_apply hx hy

Depends on / 依赖: e.toPartialEquiv.eq_symm_apply, eq_symm_apply, toPartialEquiv
-/
theorem eq_symm_apply {x : X} {y : Y} (hx : x in e.source) (hy : y in e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy

/--
theorem `mapsTo` / 定理 `mapsTo`

English:
theorem mapsTo
  statement: MapsTo e e.source e.target
  proof: fun _ => e.map_source

中文:
定理 mapsTo
  结论: 映射到 e e.source e.target
  证明: fun _ => e.map_source
-/
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

/--
theorem `mapsTo_symm` / 定理 `mapsTo_symm`

English:
theorem mapsTo_symm
  statement: MapsTo e.symm e.target e.source
  proof: e.symm.mapsTo

中文:
定理 mapsTo_symm
  结论: 映射到 e.symm e.target e.source
  证明: e.symm.mapsTo
-/
protected theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

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
  结论: 单射限制 e e.source
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
  结论: 双射限制 e e.source e.target
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
  结论: 满射限制 e e.source e.target
  证明: e.bijOn.surjOn
-/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

end Basic

/-- Interpret a `Homeomorph` as a `PartialHomeomorph` by restricting it
to a set `s` in the domain and to `t` in the codomain. -/
@[simps! -fullyApplied apply symm_apply toPartialEquiv,
  simps! -isSimp source target]
/--
Definition of `_root_.Homeomorph.toPartialHomeomorphOfImageEq` / `_root_.Homeomorph.toPartialHomeomorphOfImageEq` 的定义

English:
definition _root_.Homeomorph.toPartialHomeomorphOfImageEq
  signature: (e : X ≃ₜ Y) (s : Set X)
  body: e.toPartialEquivOfImageEq s t h
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

中文:
定义 _root_.同胚.toPartialHomeomorphOfImageEq
  签名: (e : X ≃ₜ Y) (s : 集合 X)
  定义体: e.toPartialEquivOfImageEq s t h
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

Depends on / 依赖: e.toPartialEquivOfImageEq, toPartialEquivOfImageEq
-/
def _root_.Homeomorph.toPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X)
    (t : Set Y) (h : e '' s = t) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

/-- A homeomorphism induces a partial homeomorphism on the whole space -/
@[simps! -fullyApplied]
/--
Definition of `_root_.Homeomorph.toPartialHomeomorph` / `_root_.Homeomorph.toPartialHomeomorph` 的定义

English:
definition _root_.Homeomorph.toPartialHomeomorph
  signature: (e : X ≃ₜ Y)
  body: e.toPartialHomeomorphOfImageEq univ univ by rw [image_univ, e.surjective.range_eq]

中文:
定义 _root_.同胚.toPartialHomeomorph
  签名: (e : X ≃ₜ Y)
  定义体: e.toPartialHomeomorphOfImageEq univ univ by rw [image_univ, e.surjective.range_eq]

Depends on / 依赖: e.surjective.range_eq, e.toPartialHomeomorphOfImageEq, image_univ, range_eq, surjective, toPartialHomeomorphOfImageEq
-/
def _root_.Homeomorph.toPartialHomeomorph (e : X ≃ₜ Y) : PartialHomeomorph X Y :=
e.toPartialHomeomorphOfImageEq univ univ by rw [image_univ, e.surjective.range_eq]

/--
Definition of `replacePartialEquiv` / `replacePartialEquiv` 的定义

English:
definition replacePartialEquiv
  signature: (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y)
  body: e'
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun

中文:
定义 replacePartialEquiv
  签名: (e : PartialHomeomorph X Y) (e' : 部分等价 X Y)
  定义体: e'
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun
-/
def replacePartialEquiv (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : PartialHomeomorph X Y where
  toPartialEquiv := e'
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun

/--
theorem `replacePartialEquiv_eq_self` / 定理 `replacePartialEquiv_eq_self`

English:
theorem replacePartialEquiv_eq_self
  statement: (e' : PartialEquiv X Y)
  proof: by
  cases e
  subst e'
  rfl

中文:
定理 replacePartialEquiv_eq_self
  结论: (e' : 部分等价 X Y)
  证明: by
  cases e
  subst e'
  rfl
-/
theorem replacePartialEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replacePartialEquiv e' h = e := by
  cases e
  subst e'
  rfl

/-- Two partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (e' : PartialHomeomorph X Y) (h : forall x, e x = e' x)
  proof: toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp]

中文:
定理 ext
  结论: (e' : PartialHomeomorph X Y) (h : 对任意 x, e x = e' x)
  证明: toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp]
-/
protected theorem ext (e' : PartialHomeomorph X Y) (h : forall x, e x = e' x)
    (hinv : forall x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp]
/--
theorem `symm_toPartialEquiv` / 定理 `symm_toPartialEquiv`

English:
theorem symm_toPartialEquiv
  statement: e.symm.toPartialEquiv = e.toPartialEquiv.symm
  proof: rfl

中文:
定理 symm_toPartialEquiv
  结论: e.symm.toPartialEquiv = e.toPartialEquiv.symm
  证明: rfl
-/
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

-- The following lemmas are already simp via `PartialEquiv`
/--
theorem `symm_source` / 定理 `symm_source`

English:
theorem symm_source
  statement: e.symm.source = e.target
  proof: rfl

中文:
定理 symm_source
  结论: e.symm.source = e.target
  证明: rfl
-/
theorem symm_source : e.symm.source = e.target :=
  rfl

/--
theorem `symm_target` / 定理 `symm_target`

English:
theorem symm_target
  statement: e.symm.target = e.source
  proof: rfl

中文:
定理 symm_target
  结论: e.symm.target = e.source
  证明: rfl
-/
theorem symm_target : e.symm.target = e.source :=
  rfl

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
@[simp] theorem symm_symm : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: 函数.双射
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective
    (PartialHomeomorph.symm : PartialHomeomorph X Y -> PartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

end PartialHomeomorph
