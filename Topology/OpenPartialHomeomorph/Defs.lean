/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.PartialHomeomorph.Defs

/-!
# Partial homeomorphisms: definitions

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`OpenPartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As for `Equiv`s, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

This file is intentionally kept small; many other constructions of, and lemmas about,
partial homeomorphisms can be found in other files under `Mathlib/Topology/PartialHomeomorph/`.

* `Homeomorph.toOpenPartialHomeomorph`: associating an open partial homeomorphism to a
  homeomorphism, with `source = target = Set.univ`;
* `OpenPartialHomeomorph.symm`: the inverse of an open partial homeomorphism

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

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
Definition of `OpenPartialHomeomorph` / `OpenPartialHomeomorph` 的定义

English:
structure OpenPartialHomeomorph
  parameters: (X : Type*) (Y : Type*) [TopologicalSpace X]
  extends: PartialHomeomorph X Y
  axioms and operations (2):
    - open_source : IsOpen source
    - open_target : IsOpen target

中文:
结构 OpenPartialHomeomorph
  参数: (X : 类型) (Y : 类型) [拓扑空间 X]
  继承: PartialHomeomorph X Y
  公理与运算 (2 个):
    - open_source : 是开集 source
    - open_target : 是开集 target
-/
structure OpenPartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] extends PartialHomeomorph X Y where
  open_source : IsOpen source
  open_target : IsOpen target

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

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
  signature: CoeFun (OpenPartialHomeomorph X Y) fun _ => X -> Y
  body: ⟨fun e => e.toFun'⟩

中文:
实例 :
  签名: CoeFun (OpenPartialHomeomorph X Y) fun _ => X -> Y
  定义体: ⟨fun e => e.toFun'⟩

Depends on / 依赖: e.toFun
-/
instance : CoeFun (OpenPartialHomeomorph X Y) fun _ => X -> Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of an open partial homeomorphism -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : OpenPartialHomeomorph Y X where
  body: e.toPartialHomeomorph.symm
  open_source := e.open_target
  open_target := e.open_source

中文:
定义 symm
  签名: : OpenPartialHomeomorph Y X where
  定义体: e.toPartialHomeomorph.symm
  open_source := e.open_target
  open_target := e.open_source
-/
protected def symm : OpenPartialHomeomorph Y X where
  toPartialHomeomorph := e.toPartialHomeomorph.symm
  open_source := e.open_target
  open_target := e.open_source

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : OpenPartialHomeomorph X Y)
  body: e

中文:
定义 Simps.apply
  签名: (e : OpenPartialHomeomorph X Y)
  定义体: e
-/
def Simps.apply (e : OpenPartialHomeomorph X Y) : X -> Y := e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : OpenPartialHomeomorph X Y)
  body: e.symm

initialize_simps_projections OpenPartialHomeomorph (toFun -> apply, invFun -> symm_apply)

@[fun_prop]

中文:
定义 Simps.symm_apply
  签名: (e : OpenPartialHomeomorph X Y)
  定义体: e.symm

initialize_simps_projections OpenPartialHomeomorph (toFun -> apply, invFun -> symm_apply)

@[fun_prop]
-/
def Simps.symm_apply (e : OpenPartialHomeomorph X Y) : Y -> X := e.symm

initialize_simps_projections OpenPartialHomeomorph (toFun -> apply, invFun -> symm_apply)

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

@[simp, mfld_simps]

中文:
定理 continuousOn_symm
  结论: ContinuousOn e.symm e.target
  证明: e.continuousOn_invFun

@[simp, mfld_simps]

Depends on / 依赖: continuousOn_invFun, e.continuousOn_invFun
-/
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun

@[simp, mfld_simps]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄)
  proof: rfl

@[deprecated (since := "2026-05-20")] alias mk_coe := coe_mk

@[simp, mfld_simps]

中文:
定理 coe_mk
  条件: (e : 部分等价 X Y) (h₁ h₂ h₃ h₄)
  证明: rfl

@[deprecated (since := "2026-05-20")] alias mk_coe := coe_mk

@[simp, mfld_simps]
-/
theorem coe_mk (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄) :
    (OpenPartialHomeomorph.mk (.mk e h₁ h₂) h₃ h₄ : X -> Y) = e :=
  rfl

@[deprecated (since := "2026-05-20")] alias mk_coe := coe_mk

@[simp, mfld_simps]
/--
theorem `coe_mk_symm` / 定理 `coe_mk_symm`

English:
theorem coe_mk_symm
  given: (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄)
  proof: rfl

@[deprecated (since := "2026-05-20")] alias mk_coe_symm := coe_mk_symm

中文:
定理 coe_mk_symm
  条件: (e : 部分等价 X Y) (h₁ h₂ h₃ h₄)
  证明: rfl

@[deprecated (since := "2026-05-20")] alias mk_coe_symm := coe_mk_symm
-/
theorem coe_mk_symm (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄) :
    ((OpenPartialHomeomorph.mk (.mk e h₁ h₂) h₃ h₄).symm : Y -> X) = e.symm :=
  rfl

@[deprecated (since := "2026-05-20")] alias mk_coe_symm := coe_mk_symm

/--
theorem `toPartialHomeomorph_injective` / 定理 `toPartialHomeomorph_injective`

English:
theorem toPartialHomeomorph_injective

中文:
定理 toPartialHomeomorph_injective
-/
theorem toPartialHomeomorph_injective :
    Injective (toPartialHomeomorph : OpenPartialHomeomorph X Y -> PartialHomeomorph X Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/--
theorem `toPartialEquiv_injective` / 定理 `toPartialEquiv_injective`

English:
theorem toPartialEquiv_injective
  proof: PartialHomeomorph.toPartialEquiv_injective.comp toPartialHomeomorph_injective

中文:
定理 toPartialEquiv_injective
  证明: PartialHomeomorph.toPartialEquiv_injective.comp toPartialHomeomorph_injective

Depends on / 依赖: PartialHomeomorph, PartialHomeomorph.toPartialEquiv_injective.comp, toPartialEquiv_injective, toPartialHomeomorph_injective
-/
theorem toPartialEquiv_injective :
    Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEquiv X Y) :=
  PartialHomeomorph.toPartialEquiv_injective.comp toPartialHomeomorph_injective

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (e : OpenPartialHomeomorph X Y)
  statement: e.toFun = e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 toFun_eq_coe
  条件: (e : OpenPartialHomeomorph X Y)
  结论: e.toFun = e
  证明: rfl

@[simp, mfld_simps]
-/
theorem toFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.toFun = e :=
  rfl

@[simp, mfld_simps]
/--
theorem `invFun_eq_coe` / 定理 `invFun_eq_coe`

English:
theorem invFun_eq_coe
  given: (e : OpenPartialHomeomorph X Y)
  statement: e.invFun = e.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 invFun_eq_coe
  条件: (e : OpenPartialHomeomorph X Y)
  结论: e.invFun = e.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem invFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_toPartialEquiv` / 定理 `coe_toPartialEquiv`

English:
theorem coe_toPartialEquiv
  statement: (e.toPartialEquiv : X -> Y) = e
  proof: rfl

@[deprecated (since := "2026-05-18")] alias coe_coe := coe_toPartialEquiv

@[simp, mfld_simps]

中文:
定理 coe_toPartialEquiv
  结论: (e.toPartialEquiv : X -> Y) = e
  证明: rfl

@[deprecated (since := "2026-05-18")] alias coe_coe := coe_toPartialEquiv

@[simp, mfld_simps]
-/
theorem coe_toPartialEquiv : (e.toPartialEquiv : X -> Y) = e :=
  rfl

@[deprecated (since := "2026-05-18")] alias coe_coe := coe_toPartialEquiv

@[simp, mfld_simps]
/--
theorem `coe_toPartialEquiv_symm` / 定理 `coe_toPartialEquiv_symm`

English:
theorem coe_toPartialEquiv_symm
  statement: (e.toPartialEquiv.symm : Y -> X) = e.symm
  proof: rfl

@[deprecated (since := "2026-05-18")] alias coe_coe_symm := coe_toPartialEquiv_symm

@[simp, mfld_simps]

中文:
定理 coe_toPartialEquiv_symm
  结论: (e.toPartialEquiv.symm : Y -> X) = e.symm
  证明: rfl

@[deprecated (since := "2026-05-18")] alias coe_coe_symm := coe_toPartialEquiv_symm

@[simp, mfld_simps]
-/
theorem coe_toPartialEquiv_symm : (e.toPartialEquiv.symm : Y -> X) = e.symm :=
  rfl

@[deprecated (since := "2026-05-18")] alias coe_coe_symm := coe_toPartialEquiv_symm

@[simp, mfld_simps]
/--
theorem `map_source` / 定理 `map_source`

English:
theorem map_source
  given: {x : X} (h : x in e.source)
  statement: e x in e.target
  proof: e.map_source' h

@[simp, mfld_simps]

中文:
定理 map_source
  条件: {x : X} (h : x in e.source)
  结论: e x in e.target
  证明: e.map_source' h

@[simp, mfld_simps]

Depends on / 依赖: e.map_source, map_source
-/
theorem map_source {x : X} (h : x in e.source) : e x in e.target :=
  e.map_source' h

@[simp, mfld_simps]
/--
theorem `coe_toPartialHomeomorph` / 定理 `coe_toPartialHomeomorph`

English:
theorem coe_toPartialHomeomorph
  statement: (e.toPartialHomeomorph : X -> Y) = e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_toPartialHomeomorph
  结论: (e.toPartialHomeomorph : X -> Y) = e
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_toPartialHomeomorph : (e.toPartialHomeomorph : X -> Y) = e :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_toPartialHomeomorph_symm` / 定理 `coe_toPartialHomeomorph_symm`

English:
theorem coe_toPartialHomeomorph_symm
  statement: (e.toPartialHomeomorph.symm : Y -> X) = e.symm
  proof: rfl

中文:
定理 coe_toPartialHomeomorph_symm
  结论: (e.toPartialHomeomorph.symm : Y -> X) = e.symm
  证明: rfl
-/
theorem coe_toPartialHomeomorph_symm : (e.toPartialHomeomorph.symm : Y -> X) = e.symm :=
  rfl

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
  given: {x : Y} (h : x in e.target)
  statement: e.symm x in e.source
  proof: e.map_target' h

@[simp, mfld_simps]

中文:
定理 map_target
  条件: {x : Y} (h : x in e.target)
  结论: e.symm x in e.source
  证明: e.map_target' h

@[simp, mfld_simps]

Depends on / 依赖: e.map_target, map_target
-/
theorem map_target {x : Y} (h : x in e.target) : e.symm x in e.source :=
  e.map_target' h

@[simp, mfld_simps]
/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: {x : X} (h : x in e.source)
  statement: e.symm (e x) = x
  proof: e.left_inv' h

@[simp, mfld_simps]

中文:
定理 left_inv
  条件: {x : X} (h : x in e.source)
  结论: e.symm (e x) = x
  证明: e.left_inv' h

@[simp, mfld_simps]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem left_inv {x : X} (h : x in e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
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

@[deprecated (since := "2026-05-28")] alias symm_mapsTo := OpenPartialHomeomorph.mapsTo_symm

中文:
定理 mapsTo_symm
  结论: 映射到 e.symm e.target e.source
  证明: e.symm.mapsTo

@[deprecated (since := "2026-05-28")] alias symm_mapsTo := OpenPartialHomeomorph.mapsTo_symm
-/
protected theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

@[deprecated (since := "2026-05-28")] alias symm_mapsTo := OpenPartialHomeomorph.mapsTo_symm

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

/-- Interpret a `Homeomorph` as an `OpenPartialHomeomorph` by restricting it
to an open set `s` in the domain and to `t` in the codomain. -/
@[simps! -fullyApplied apply symm_apply toPartialHomeomorph,
  simps! -isSimp source target]
/--
Definition of `_root_.Homeomorph.toOpenPartialHomeomorphOfImageEq` / `_root_.Homeomorph.toOpenPartialHomeomorphOfImageEq` 的定义

English:
definition _root_.Homeomorph.toOpenPartialHomeomorphOfImageEq
  signature: (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
  body: e.toPartialHomeomorphOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]

中文:
定义 _root_.同胚.toOpenPartialHomeomorphOfImageEq
  签名: (e : X ≃ₜ Y) (s : 集合 X) (hs : 是开集 s)
  定义体: e.toPartialHomeomorphOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]

Depends on / 依赖: e.toPartialHomeomorphOfImageEq, toPartialHomeomorphOfImageEq
-/
def _root_.Homeomorph.toOpenPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
    (t : Set Y) (h : e '' s = t) : OpenPartialHomeomorph X Y where
  toPartialHomeomorph := e.toPartialHomeomorphOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]

/-- A homeomorphism induces an open partial homeomorphism on the whole space -/
@[simps! (attr := mfld_simps) -fullyApplied]
/--
Definition of `_root_.Homeomorph.toOpenPartialHomeomorph` / `_root_.Homeomorph.toOpenPartialHomeomorph` 的定义

English:
definition _root_.Homeomorph.toOpenPartialHomeomorph
  signature: (e : X ≃ₜ Y)
  body: e.toOpenPartialHomeomorphOfImageEq univ isOpen_univ univ
    by rw [image_univ, e.surjective.range_eq]

中文:
定义 _root_.同胚.toOpenPartialHomeomorph
  签名: (e : X ≃ₜ Y)
  定义体: e.toOpenPartialHomeomorphOfImageEq univ isOpen_univ univ
    by rw [image_univ, e.surjective.range_eq]

Depends on / 依赖: e.surjective.range_eq, e.toOpenPartialHomeomorphOfImageEq, image_univ, isOpen_univ, range_eq, surjective, toOpenPartialHomeomorphOfImageEq
-/
def _root_.Homeomorph.toOpenPartialHomeomorph (e : X ≃ₜ Y) : OpenPartialHomeomorph X Y :=
e.toOpenPartialHomeomorphOfImageEq univ isOpen_univ univ
    by rw [image_univ, e.surjective.range_eq]

/--
Definition of `replacePartialEquiv` / `replacePartialEquiv` 的定义

English:
definition replacePartialEquiv
  signature: (e : OpenPartialHomeomorph X Y) (e' : PartialEquiv X Y)
  body: e.toPartialHomeomorph.replacePartialEquiv e' h
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target

@[deprecated (since := "2026-05-19")] alias replaceEquiv := replacePartialEquiv

中文:
定义 replacePartialEquiv
  签名: (e : OpenPartialHomeomorph X Y) (e' : 部分等价 X Y)
  定义体: e.toPartialHomeomorph.replacePartialEquiv e' h
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target

@[deprecated (since := "2026-05-19")] alias replaceEquiv := replacePartialEquiv

Depends on / 依赖: e.toPartialHomeomorph.replacePartialEquiv, replacePartialEquiv, toPartialHomeomorph
-/
def replacePartialEquiv (e : OpenPartialHomeomorph X Y) (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : OpenPartialHomeomorph X Y where
  toPartialHomeomorph := e.toPartialHomeomorph.replacePartialEquiv e' h
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target

@[deprecated (since := "2026-05-19")] alias replaceEquiv := replacePartialEquiv

/--
theorem `replacePartialEquiv_eq_self` / 定理 `replacePartialEquiv_eq_self`

English:
theorem replacePartialEquiv_eq_self
  statement: (e' : PartialEquiv X Y)
  proof: by
  cases e
  subst e'
  rfl

@[deprecated (since := "2026-05-20")] alias replaceEquiv_eq_self := replacePartialEquiv_eq_self

中文:
定理 replacePartialEquiv_eq_self
  结论: (e' : 部分等价 X Y)
  证明: by
  cases e
  subst e'
  rfl

@[deprecated (since := "2026-05-20")] alias replaceEquiv_eq_self := replacePartialEquiv_eq_self
-/
theorem replacePartialEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replacePartialEquiv e' h = e := by
  cases e
  subst e'
  rfl

@[deprecated (since := "2026-05-20")] alias replaceEquiv_eq_self := replacePartialEquiv_eq_self

/-- Two open partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (e' : OpenPartialHomeomorph X Y) (h : forall x, e x = e' x)
  proof: toPartialHomeomorph_injective
    (PartialHomeomorph.ext e.toPartialHomeomorph e'.toPartialHomeomorph h hinv hs)

@[simp, mfld_simps]

中文:
定理 ext
  结论: (e' : OpenPartialHomeomorph X Y) (h : 对任意 x, e x = e' x)
  证明: toPartialHomeomorph_injective
    (PartialHomeomorph.ext e.toPartialHomeomorph e'.toPartialHomeomorph h hinv hs)

@[simp, mfld_simps]
-/
protected theorem ext (e' : OpenPartialHomeomorph X Y) (h : forall x, e x = e' x)
    (hinv : forall x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialHomeomorph_injective
    (PartialHomeomorph.ext e.toPartialHomeomorph e'.toPartialHomeomorph h hinv hs)

@[simp, mfld_simps]
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
@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl

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
    (OpenPartialHomeomorph.symm : OpenPartialHomeomorph X Y -> OpenPartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

end OpenPartialHomeomorph
