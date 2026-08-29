/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local diffeomorphisms between manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively, such that `f` restricts to a diffeomorphism
between `s` and `t`. `f` is called a **local diffeomorphism on `s`** iff it is a local
diffeomorphism at every `x ∈ s`, and a **local diffeomorphism** iff it is a local diffeomorphism on
`univ`.

## Main definitions
* `IsLocalDiffeomorphAt I J n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `IsLocalDiffeomorphOn I J n f s`: `f` is a `C^n` local diffeomorphism on `s`
* `IsLocalDiffeomorph I J n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `IsLocalDiffeomorph`, `IsLocalDiffeomorphOn` and `IsLocalDiffeomorphAt`
  implies the next condition.
* `IsLocalDiffeomorph.isLocalHomeomorph`: a local diffeomorphism is a local homeomorphism,
  and similarly for a local diffeomorphism on `s`.
* `IsLocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open
* `IsLocalDiffeomorph.diffeomorphOfBijective`:
  a bijective local diffeomorphism is a diffeomorphism

* `Diffeomorph.mfderivToContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
  (`n ≠ 0`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism
  at `x`, the differential `mfderiv I J n f x` is a continuous linear equivalence.
* `LocalDiffeomorph.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism,
  each differential `mfderiv I J n f x` is a continuous linear equivalence.

## TODO
* an injective local diffeomorphism is a diffeomorphism to its image
* if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
  `f` is a local diffeomorphism at `x` (using the inverse function theorem).

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

public noncomputable section

open Manifold Set TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H₁ : Type*} [TopologicalSpace H₁]
  {H₂ : Type*} [TopologicalSpace H₂]
  {H₃ : Type*} [TopologicalSpace H₃]
  (I : ModelWithCorners 𝕜 E H₁) (J : ModelWithCorners 𝕜 F H₂) (K : ModelWithCorners 𝕜 F' H₃)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H₁ M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace H₂ N]
  (P : Type*) [TopologicalSpace P] [ChartedSpace H₃ P] (n : WithTop Nat∞)

section PartialDiffeomorph
/--
Definition of `PartialDiffeomorph` / `PartialDiffeomorph` 的定义

English:
structure PartialDiffeomorph
  parameters: extends PartialEquiv M N
  extends: PartialEquiv M N
  axioms and operations (4):
    - open_source : IsOpen source
    - open_target : IsOpen target
    - contMDiffOn_toFun : CMDiff[source] n toFun
    - contMDiffOn_invFun : CMDiff[target] n invFun

中文:
结构 PartialDiffeomorph
  参数: extends PartialEquiv M N
  继承: PartialEquiv M N
  公理与运算 (4 个):
    - open_source : IsOpen source
    - open_target : IsOpen target
    - contMDiffOn_toFun : CMDiff[source] n toFun
    - contMDiffOn_invFun : CMDiff[target] n invFun
-/
structure PartialDiffeomorph extends PartialEquiv M N where
  open_source : IsOpen source
  open_target : IsOpen target
  contMDiffOn_toFun : CMDiff[source] n toFun
  contMDiffOn_invFun : CMDiff[target] n invFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (PartialDiffeomorph I J M N n) fun _ => M -> N
  body: ⟨fun Φ => Φ.toFun⟩

中文:
实例 :
  签名: CoeFun (PartialDiffeomorph I J M N n) fun _ => M -> N
  定义体: ⟨fun Φ => Φ.toFun⟩
-/
instance : CoeFun (PartialDiffeomorph I J M N n) fun _ => M -> N :=
  ⟨fun Φ => Φ.toFun⟩

variable {I J K M N P n}

/--
Definition of `Diffeomorph.toPartialDiffeomorph` / `Diffeomorph.toPartialDiffeomorph` 的定义

English:
definition Diffeomorph.toPartialDiffeomorph
  signature: (h : Diffeomorph I J M N n)
  body: h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

中文:
定义 Diffeomorph.toPartialDiffeomorph
  签名: (h : Diffeomorph I J M N n)
  定义体: h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

Depends on / 依赖: h.toHomeomorph.toPartialEquiv, toHomeomorph, toPartialEquiv
-/
def Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

-- Add the very basic API we need.
namespace PartialDiffeomorph
variable (Φ : PartialDiffeomorph I J M N n)

/-- A partial diffeomorphism is also a local homeomorphism. -/
@[expose, simps toPartialHomeomorph_toPartialEquiv]
/--
Definition of `toOpenPartialHomeomorph` / `toOpenPartialHomeomorph` 的定义

English:
definition toOpenPartialHomeomorph
  signature: : OpenPartialHomeomorph M N where
  body: Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

中文:
定义 toOpenPartialHomeomorph
  签名: : OpenPartialHomeomorph M N where
  定义体: Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

Depends on / 依赖: toPartialEquiv
-/
def toOpenPartialHomeomorph : OpenPartialHomeomorph M N where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

/-- The inverse of a local diffeomorphism. -/
@[expose, simps toPartialEquiv]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : PartialDiffeomorph J I N M n where
  body: Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun

中文:
定义 symm
  签名: : PartialDiffeomorph J I N M n where
  定义体: Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun
-/
protected def symm : PartialDiffeomorph J I N M n where
  toPartialEquiv := Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun

/--
theorem `contMDiffOn` / 定理 `contMDiffOn`

English:
theorem contMDiffOn
  statement: CMDiff[Φ.source] n Φ
  proof: Φ.contMDiffOn_toFun

中文:
定理 contMDiffOn
  结论: CMDiff[Φ.source] n Φ
  证明: Φ.contMDiffOn_toFun
-/
protected theorem contMDiffOn : CMDiff[Φ.source] n Φ := Φ.contMDiffOn_toFun

/--
theorem `mdifferentiableOn` / 定理 `mdifferentiableOn`

English:
theorem mdifferentiableOn
  given: (hn : n != 0)
  statement: MDiff[Φ.source] Φ
  proof: (Φ.contMDiffOn).mdifferentiableOn hn

中文:
定理 mdifferentiableOn
  条件: (hn : n != 0)
  结论: MDiff[Φ.source] Φ
  证明: (Φ.contMDiffOn).mdifferentiableOn hn
-/
protected theorem mdifferentiableOn (hn : n != 0) : MDiff[Φ.source] Φ :=
  (Φ.contMDiffOn).mdifferentiableOn hn

/--
theorem `mdifferentiableAt` / 定理 `mdifferentiableAt`

English:
theorem mdifferentiableAt
  given: (hn : n != 0) {x : M} (hx : x in Φ.source)
  proof: (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

中文:
定理 mdifferentiableAt
  条件: (hn : n != 0) {x : M} (hx : x in Φ.source)
  证明: (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)
-/
protected theorem mdifferentiableAt (hn : n != 0) {x : M} (hx : x in Φ.source) :
    MDiffAt Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

/-- Composition of partial diffeomorphisms. -/
@[expose, simps toPartialEquiv]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (Ψ : PartialDiffeomorph J K N P n)
  body: Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun :=
    Ψ.contMDiffOn_toFun.comp (Φ.contMDiffOn_toFun.mono inter_subset_left) inter_subset_right
  contMDiffOn_invFun :=
    Φ.contMDiffOn_invFun.comp (Ψ.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right

中文:
定义 trans
  签名: (Ψ : PartialDiffeomorph J K N P n)
  定义体: Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun :=
    Ψ.contMDiffOn_toFun.comp (Φ.contMDiffOn_toFun.mono inter_subset_left) inter_subset_right
  contMDiffOn_invFun :=
    Φ.contMDiffOn_invFun.comp (Ψ.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right
-/
protected def trans (Ψ : PartialDiffeomorph J K N P n) : PartialDiffeomorph I K M P n where
  __ := Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun :=
    Ψ.contMDiffOn_toFun.comp (Φ.contMDiffOn_toFun.mono inter_subset_left) inter_subset_right
  contMDiffOn_invFun :=
    Φ.contMDiffOn_invFun.comp (Ψ.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right

/- We could add lots of additional API (following `Diffeomorph` and `OpenPartialHomeomorph`),
such as
* further continuity and differentiability lemmas
* refl and trans instances; lemmas between them.

As this declaration is meant for internal use only, we keep it simple. -/
end PartialDiffeomorph
end PartialDiffeomorph

variable {M N}

/--
Definition of `IsLocalDiffeomorphAt` / `IsLocalDiffeomorphAt` 的定义

English:
definition IsLocalDiffeomorphAt
  signature: (f : M -> N) (x : M)
  body: exists Φ : PartialDiffeomorph I J M N n, x in Φ.source ∧ EqOn f Φ Φ.source

中文:
定义 IsLocalDiffeomorphAt
  签名: (f : M -> N) (x : M)
  定义体: exists Φ : PartialDiffeomorph I J M N n, x in Φ.source ∧ EqOn f Φ Φ.source

Depends on / 依赖: PartialDiffeomorph, source
-/
def IsLocalDiffeomorphAt (f : M -> N) (x : M) : Prop :=
  exists Φ : PartialDiffeomorph I J M N n, x in Φ.source ∧ EqOn f Φ Φ.source

/--
lemma `PartialDiffeomorph.isLocalDiffeomorphAt` / 引理 `PartialDiffeomorph.isLocalDiffeomorphAt`

English:
lemma PartialDiffeomorph.isLocalDiffeomorphAt
  statement: (φ : PartialDiffeomorph I J M N n)
  proof: ⟨φ, hx, Set.eqOn_refl _ _⟩

中文:
引理 PartialDiffeomorph.isLocalDiffeomorphAt
  结论: (φ : PartialDiffeomorph I J M N n)
  证明: ⟨φ, hx, Set.eqOn_refl _ _⟩

Depends on / 依赖: Set.eqOn_refl, eqOn_refl
-/
lemma PartialDiffeomorph.isLocalDiffeomorphAt (φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x in φ.source) : IsLocalDiffeomorphAt I J n φ x :=
  ⟨φ, hx, Set.eqOn_refl _ _⟩

namespace IsLocalDiffeomorphAt

variable {f : M -> N} {x : M}

variable {I I' J n}

/--
Definition of `localInverse` / `localInverse` 的定义

English:
definition localInverse
  signature: (hf : IsLocalDiffeomorphAt I J n f x)
  body: (Classical.choose hf).symm

中文:
定义 localInverse
  签名: (hf : IsLocalDiffeomorphAt I J n f x)
  定义体: (Classical.choose hf).symm

Depends on / 依赖: Classical, Classical.choose
-/
def localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    PartialDiffeomorph J I N M n := (Classical.choose hf).symm

/--
lemma `localInverse_open_source` / 引理 `localInverse_open_source`

English:
lemma localInverse_open_source
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: PartialDiffeomorph.open_source _

中文:
引理 localInverse_open_source
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: PartialDiffeomorph.open_source _

Depends on / 依赖: PartialDiffeomorph, PartialDiffeomorph.open_source, open_source
-/
lemma localInverse_open_source (hf : IsLocalDiffeomorphAt I J n f x) :
    IsOpen hf.localInverse.source :=
  PartialDiffeomorph.open_source _

/--
lemma `localInverse_mem_source` / 引理 `localInverse_mem_source`

English:
lemma localInverse_mem_source
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: by
  rw [(hf.choose_spec.2 hf.choose_spec.1)]
  exact (Classical.choose hf).map_source hf.choose_spec.1

中文:
引理 localInverse_mem_source
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: by
  rw [(hf.choose_spec.2 hf.choose_spec.1)]
  exact (Classical.choose hf).map_source hf.choose_spec.1

Depends on / 依赖: Classical, Classical.choose, choose_spec, hf.choose_spec, map_source
-/
lemma localInverse_mem_source (hf : IsLocalDiffeomorphAt I J n f x) :
    f x in hf.localInverse.source := by
  rw [(hf.choose_spec.2 hf.choose_spec.1)]
  exact (Classical.choose hf).map_source hf.choose_spec.1

/--
lemma `localInverse_mem_target` / 引理 `localInverse_mem_target`

English:
lemma localInverse_mem_target
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: hf.choose_spec.1

中文:
引理 localInverse_mem_target
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: hf.choose_spec.1

Depends on / 依赖: choose_spec, hf.choose_spec
-/
lemma localInverse_mem_target (hf : IsLocalDiffeomorphAt I J n f x) :
    x in hf.localInverse.target :=
  hf.choose_spec.1

/--
lemma `contmdiffOn_localInverse` / 引理 `contmdiffOn_localInverse`

English:
lemma contmdiffOn_localInverse
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: hf.localInverse.contMDiffOn_toFun

中文:
引理 contmdiffOn_localInverse
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: hf.localInverse.contMDiffOn_toFun

Depends on / 依赖: contMDiffOn_toFun, hf.localInverse.contMDiffOn_toFun, localInverse
-/
lemma contmdiffOn_localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiff[hf.localInverse.source] n hf.localInverse :=
  hf.localInverse.contMDiffOn_toFun

/--
lemma `localInverse_right_inv` / 引理 `localInverse_right_inv`

English:
lemma localInverse_right_inv
  statement: (hf : IsLocalDiffeomorphAt I J n f x) {y : N}
  proof: by
  have : hf.localInverse y in hf.choose.source := by
    rw [← hf.choose.symm_target]
    exact hf.choose.symm.map_source hy
  rw [hf.choose_spec.2 this]
  exact hf.choose.right_inv hy

中文:
引理 localInverse_right_inv
  结论: (hf : IsLocalDiffeomorphAt I J n f x) {y : N}
  证明: by
  have : hf.localInverse y in hf.choose.source := by
    rw [← hf.choose.symm_target]
    exact hf.choose.symm.map_source hy
  rw [hf.choose_spec.2 this]
  exact hf.choose.right_inv hy

Depends on / 依赖: choose_spec, hf.choose.right_inv, hf.choose.source, hf.choose.symm.map_source, hf.choose.symm_target, hf.choose_spec, hf.localInverse, localInverse, map_source, right_inv, source, symm_target
-/
lemma localInverse_right_inv (hf : IsLocalDiffeomorphAt I J n f x) {y : N}
    (hy : y in hf.localInverse.source) : f (hf.localInverse y) = y := by
  have : hf.localInverse y in hf.choose.source := by
    rw [← hf.choose.symm_target]
    exact hf.choose.symm.map_source hy
  rw [hf.choose_spec.2 this]
  exact hf.choose.right_inv hy

/--
lemma `localInverse_eqOn_right` / 引理 `localInverse_eqOn_right`

English:
lemma localInverse_eqOn_right
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: fun _y hy => hf.localInverse_right_inv hy

中文:
引理 localInverse_eqOn_right
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: fun _y hy => hf.localInverse_right_inv hy

Depends on / 依赖: hf.localInverse_right_inv, localInverse_right_inv
-/
lemma localInverse_eqOn_right (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (f ∘ hf.localInverse) id hf.localInverse.source :=
  fun _y hy => hf.localInverse_right_inv hy

/--
lemma `localInverse_eventuallyEq_right` / 引理 `localInverse_eventuallyEq_right`

English:
lemma localInverse_eventuallyEq_right
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: Filter.eventuallyEq_of_mem
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
    hf.localInverse_eqOn_right

中文:
引理 localInverse_eventuallyEq_right
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: Filter.eventuallyEq_of_mem
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
    hf.localInverse_eqOn_right

Depends on / 依赖: Filter, Filter.eventuallyEq_of_mem, eventuallyEq_of_mem, hf.localInverse.open_source.mem_nhds, hf.localInverse_eqOn_right, hf.localInverse_mem_source, localInverse, localInverse_eqOn_right, localInverse_mem_source, mem_nhds, open_source
-/
lemma localInverse_eventuallyEq_right (hf : IsLocalDiffeomorphAt I J n f x) :
    f ∘ hf.localInverse =ᶠ[nhds (f x)] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
    hf.localInverse_eqOn_right

/--
lemma `localInverse_left_inv` / 引理 `localInverse_left_inv`

English:
lemma localInverse_left_inv
  statement: (hf : IsLocalDiffeomorphAt I J n f x) {x' : M}
  proof: by
  rw [hf.choose_spec.2 (hf.choose.symm_target ▸ hx')]
  exact hf.choose.left_inv hx'

中文:
引理 localInverse_left_inv
  结论: (hf : IsLocalDiffeomorphAt I J n f x) {x' : M}
  证明: by
  rw [hf.choose_spec.2 (hf.choose.symm_target ▸ hx')]
  exact hf.choose.left_inv hx'

Depends on / 依赖: choose_spec, hf.choose.left_inv, hf.choose.symm_target, hf.choose_spec, left_inv, symm_target
-/
lemma localInverse_left_inv (hf : IsLocalDiffeomorphAt I J n f x) {x' : M}
    (hx' : x' in hf.localInverse.target) : hf.localInverse (f x') = x' := by
  rw [hf.choose_spec.2 (hf.choose.symm_target ▸ hx')]
  exact hf.choose.left_inv hx'

/--
lemma `localInverse_eqOn_left` / 引理 `localInverse_eqOn_left`

English:
lemma localInverse_eqOn_left
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: fun _ hx => hf.localInverse_left_inv hx

中文:
引理 localInverse_eqOn_left
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: fun _ hx => hf.localInverse_left_inv hx

Depends on / 依赖: hf.localInverse_left_inv, localInverse_left_inv
-/
lemma localInverse_eqOn_left (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (hf.localInverse ∘ f) id hf.localInverse.target :=
  fun _ hx => hf.localInverse_left_inv hx

/--
lemma `localInverse_eventuallyEq_left` / 引理 `localInverse_eventuallyEq_left`

English:
lemma localInverse_eventuallyEq_left
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: Filter.eventuallyEq_of_mem
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) hf.localInverse_eqOn_left

中文:
引理 localInverse_eventuallyEq_left
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: Filter.eventuallyEq_of_mem
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) hf.localInverse_eqOn_left

Depends on / 依赖: Filter, Filter.eventuallyEq_of_mem, eventuallyEq_of_mem, hf.localInverse.open_target.mem_nhds, hf.localInverse_eqOn_left, hf.localInverse_mem_target, localInverse, localInverse_eqOn_left, localInverse_mem_target, mem_nhds, open_target
-/
lemma localInverse_eventuallyEq_left (hf : IsLocalDiffeomorphAt I J n f x) :
    hf.localInverse ∘ f =ᶠ[nhds x] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) hf.localInverse_eqOn_left

/--
lemma `localInverse_isLocalDiffeomorphAt` / 引理 `localInverse_isLocalDiffeomorphAt`

English:
lemma localInverse_isLocalDiffeomorphAt
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: hf.localInverse.isLocalDiffeomorphAt _ _ _ hf.localInverse_mem_source

中文:
引理 localInverse_isLocalDiffeomorphAt
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: hf.localInverse.isLocalDiffeomorphAt _ _ _ hf.localInverse_mem_source

Depends on / 依赖: hf.localInverse.isLocalDiffeomorphAt, hf.localInverse_mem_source, isLocalDiffeomorphAt, localInverse, localInverse_mem_source
-/
lemma localInverse_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt J I n (hf.localInverse) (f x) :=
  hf.localInverse.isLocalDiffeomorphAt _ _ _ hf.localInverse_mem_source

/--
lemma `localInverse_contMDiffOn` / 引理 `localInverse_contMDiffOn`

English:
lemma localInverse_contMDiffOn
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: hf.localInverse.contMDiffOn_toFun

中文:
引理 localInverse_contMDiffOn
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: hf.localInverse.contMDiffOn_toFun

Depends on / 依赖: contMDiffOn_toFun, hf.localInverse.contMDiffOn_toFun, localInverse
-/
lemma localInverse_contMDiffOn (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiff[hf.localInverse.source] n hf.localInverse :=
  hf.localInverse.contMDiffOn_toFun

/--
lemma `localInverse_contMDiffAt` / 引理 `localInverse_contMDiffAt`

English:
lemma localInverse_contMDiffAt
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: hf.localInverse_contMDiffOn.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)

中文:
引理 localInverse_contMDiffAt
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: hf.localInverse_contMDiffOn.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)

Depends on / 依赖: contMDiffAt, hf.localInverse.open_source.mem_nhds, hf.localInverse_contMDiffOn.contMDiffAt, hf.localInverse_mem_source, localInverse, localInverse_contMDiffOn, localInverse_mem_source, mem_nhds, open_source
-/
lemma localInverse_contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiffAt n hf.localInverse (f x) :=
  hf.localInverse_contMDiffOn.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)

/--
lemma `localInverse_mdifferentiableAt` / 引理 `localInverse_mdifferentiableAt`

English:
lemma localInverse_mdifferentiableAt
  given: (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0)
  proof: hf.localInverse_contMDiffAt.mdifferentiableAt hn

中文:
引理 localInverse_mdifferentiableAt
  条件: (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0)
  证明: hf.localInverse_contMDiffAt.mdifferentiableAt hn

Depends on / 依赖: hf.localInverse_contMDiffAt.mdifferentiableAt, localInverse_contMDiffAt, mdifferentiableAt
-/
lemma localInverse_mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) :
    MDiffAt hf.localInverse (f x) :=
  hf.localInverse_contMDiffAt.mdifferentiableAt hn

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: (hf : IsLocalDiffeomorphAt I J n f x) {g : N -> P}
  proof: by
  obtain ⟨Φ, hx, heq⟩ := hf
  obtain ⟨Ψ, hy, heq'⟩ := hg
  refine ⟨Φ.trans Ψ, by simp [hx, ← heq.eq_of_mem hx, hy], ?_⟩
  intro y ⟨hyl, hyr⟩
  have hfy : f y in Ψ.source := by rwa [heq.eq_of_mem hyl]
  simp [← heq.eq_of_mem hyl, ← heq'.eq_of_mem hfy]

中文:
引理 comp
  结论: (hf : IsLocalDiffeomorphAt I J n f x) {g : N -> P}
  证明: by
  obtain ⟨Φ, hx, heq⟩ := hf
  obtain ⟨Ψ, hy, heq'⟩ := hg
  refine ⟨Φ.trans Ψ, by simp [hx, ← heq.eq_of_mem hx, hy], ?_⟩
  intro y ⟨hyl, hyr⟩
  have hfy : f y in Ψ.source := by rwa [heq.eq_of_mem hyl]
  simp [← heq.eq_of_mem hyl, ← heq'.eq_of_mem hfy]

Depends on / 依赖: eq_of_mem, heq.eq_of_mem, source
-/
lemma comp (hf : IsLocalDiffeomorphAt I J n f x) {g : N -> P}
    (hg : IsLocalDiffeomorphAt J K n g (f x)) :
    IsLocalDiffeomorphAt I K n (g ∘ f) x := by
  obtain ⟨Φ, hx, heq⟩ := hf
  obtain ⟨Ψ, hy, heq'⟩ := hg
  refine ⟨Φ.trans Ψ, by simp [hx, ← heq.eq_of_mem hx, hy], ?_⟩
  intro y ⟨hyl, hyr⟩
  have hfy : f y in Ψ.source := by rwa [heq.eq_of_mem hyl]
  simp [← heq.eq_of_mem hyl, ← heq'.eq_of_mem hfy]

end IsLocalDiffeomorphAt

/--
Definition of `IsLocalDiffeomorphOn` / `IsLocalDiffeomorphOn` 的定义

English:
definition IsLocalDiffeomorphOn
  signature: (f : M -> N) (s : Set M)
  body: forall x : s, IsLocalDiffeomorphAt I J n f x

中文:
定义 IsLocalDiffeomorphOn
  签名: (f : M -> N) (s : Set M)
  定义体: forall x : s, IsLocalDiffeomorphAt I J n f x
-/
@[expose] def IsLocalDiffeomorphOn (f : M -> N) (s : Set M) : Prop :=
  forall x : s, IsLocalDiffeomorphAt I J n f x

/--
Definition of `IsLocalDiffeomorph` / `IsLocalDiffeomorph` 的定义

English:
definition IsLocalDiffeomorph
  signature: (f : M -> N)
  body: forall x : M, IsLocalDiffeomorphAt I J n f x

中文:
定义 IsLocalDiffeomorph
  签名: (f : M -> N)
  定义体: forall x : M, IsLocalDiffeomorphAt I J n f x
-/
@[expose] def IsLocalDiffeomorph (f : M -> N) : Prop :=
  forall x : M, IsLocalDiffeomorphAt I J n f x

variable {I J n} in
/--
lemma `isLocalDiffeomorphOn_iff` / 引理 `isLocalDiffeomorphOn_iff`

English:
lemma isLocalDiffeomorphOn_iff
  given: {f : M -> N} (s : Set M)
  proof: by rfl

中文:
引理 isLocalDiffeomorphOn_iff
  条件: {f : M -> N} (s : Set M)
  证明: by rfl
-/
lemma isLocalDiffeomorphOn_iff {f : M -> N} (s : Set M) :
    IsLocalDiffeomorphOn I J n f s ↔ forall x : s, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
/--
lemma `isLocalDiffeomorph_iff` / 引理 `isLocalDiffeomorph_iff`

English:
lemma isLocalDiffeomorph_iff
  given: {f : M -> N}
  proof: by rfl

中文:
引理 isLocalDiffeomorph_iff
  条件: {f : M -> N}
  证明: by rfl
-/
lemma isLocalDiffeomorph_iff {f : M -> N} :
    IsLocalDiffeomorph I J n f ↔ forall x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
/--
theorem `isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ` / 定理 `isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ`

English:
theorem isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ
  given: {f : M -> N}
  proof: ⟨fun hf x => hf x, fun hf x => hf ⟨x, trivial⟩⟩

中文:
定理 isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ
  条件: {f : M -> N}
  证明: ⟨fun hf x => hf x, fun hf x => hf ⟨x, trivial⟩⟩
-/
theorem isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ {f : M -> N} :
    IsLocalDiffeomorph I J n f ↔ IsLocalDiffeomorphOn I J n f Set.univ :=
  ⟨fun hf x => hf x, fun hf x => hf ⟨x, trivial⟩⟩

variable {I J n} in
/--
lemma `IsLocalDiffeomorph.isLocalDiffeomorphOn` / 引理 `IsLocalDiffeomorph.isLocalDiffeomorphOn`

English:
lemma IsLocalDiffeomorph.isLocalDiffeomorphOn
  proof: fun x => hf x

中文:
引理 IsLocalDiffeomorph.isLocalDiffeomorphOn
  证明: fun x => hf x
-/
lemma IsLocalDiffeomorph.isLocalDiffeomorphOn
    {f : M -> N} (hf : IsLocalDiffeomorph I J n f) (s : Set M) : IsLocalDiffeomorphOn I J n f s :=
  fun x => hf x

/-! ### Basic properties of local diffeomorphisms -/
section Basic
variable {f : M -> N} {s : Set M} {x : M}
variable {I J n}

/--
lemma `IsLocalDiffeomorphAt.contMDiffAt` / 引理 `IsLocalDiffeomorphAt.contMDiffAt`

English:
lemma IsLocalDiffeomorphAt.contMDiffAt
  given: (hf : IsLocalDiffeomorphAt I J n f x)
  proof: by
  choose Φ hx heq using hf
  -- In fact, even `CMDiff[Φ.source] n f`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

中文:
引理 IsLocalDiffeomorphAt.contMDiffAt
  条件: (hf : IsLocalDiffeomorphAt I J n f x)
  证明: by
  choose Φ hx heq using hf
  -- In fact, even `CMDiff[Φ.source] n f`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)
-/
lemma IsLocalDiffeomorphAt.contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiffAt n f x := by
  choose Φ hx heq using hf
  -- In fact, even `CMDiff[Φ.source] n f`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

/--
lemma `IsLocalDiffeomorphAt.mdifferentiableAt` / 引理 `IsLocalDiffeomorphAt.mdifferentiableAt`

English:
lemma IsLocalDiffeomorphAt.mdifferentiableAt
  given: (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0)
  proof: hf.contMDiffAt.mdifferentiableAt hn

中文:
引理 IsLocalDiffeomorphAt.mdifferentiableAt
  条件: (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0)
  证明: hf.contMDiffAt.mdifferentiableAt hn

Depends on / 依赖: contMDiffAt, hf.contMDiffAt.mdifferentiableAt, mdifferentiableAt
-/
lemma IsLocalDiffeomorphAt.mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) :
    MDiffAt f x :=
  hf.contMDiffAt.mdifferentiableAt hn

/--
lemma `IsLocalDiffeomorphOn.contMDiffOn` / 引理 `IsLocalDiffeomorphOn.contMDiffOn`

English:
lemma IsLocalDiffeomorphOn.contMDiffOn
  given: (hf : IsLocalDiffeomorphOn I J n f s)
  proof: fun x hx => (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

中文:
引理 IsLocalDiffeomorphOn.contMDiffOn
  条件: (hf : IsLocalDiffeomorphOn I J n f s)
  证明: fun x hx => (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

Depends on / 依赖: contMDiffAt, contMDiffAt.contMDiffWithinAt, contMDiffWithinAt
-/
lemma IsLocalDiffeomorphOn.contMDiffOn (hf : IsLocalDiffeomorphOn I J n f s) :
    CMDiff[s] n f :=
  fun x hx => (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

/--
lemma `IsLocalDiffeomorphOn.mdifferentiableOn` / 引理 `IsLocalDiffeomorphOn.mdifferentiableOn`

English:
lemma IsLocalDiffeomorphOn.mdifferentiableOn
  given: (hf : IsLocalDiffeomorphOn I J n f s) (hn : n != 0)
  proof: hf.contMDiffOn.mdifferentiableOn hn

中文:
引理 IsLocalDiffeomorphOn.mdifferentiableOn
  条件: (hf : IsLocalDiffeomorphOn I J n f s) (hn : n != 0)
  证明: hf.contMDiffOn.mdifferentiableOn hn

Depends on / 依赖: contMDiffOn, hf.contMDiffOn.mdifferentiableOn, mdifferentiableOn
-/
lemma IsLocalDiffeomorphOn.mdifferentiableOn (hf : IsLocalDiffeomorphOn I J n f s) (hn : n != 0) :
    MDiff[s] f :=
  hf.contMDiffOn.mdifferentiableOn hn

/--
lemma `IsLocalDiffeomorph.contMDiff` / 引理 `IsLocalDiffeomorph.contMDiff`

English:
lemma IsLocalDiffeomorph.contMDiff
  given: (hf : IsLocalDiffeomorph I J n f)
  statement: CMDiff n f
  proof: fun x => (hf x).contMDiffAt

中文:
引理 IsLocalDiffeomorph.contMDiff
  条件: (hf : IsLocalDiffeomorph I J n f)
  结论: CMDiff n f
  证明: fun x => (hf x).contMDiffAt

Depends on / 依赖: contMDiffAt
-/
lemma IsLocalDiffeomorph.contMDiff (hf : IsLocalDiffeomorph I J n f) : CMDiff n f :=
  fun x => (hf x).contMDiffAt

/--
lemma `IsLocalDiffeomorph.mdifferentiable` / 引理 `IsLocalDiffeomorph.mdifferentiable`

English:
lemma IsLocalDiffeomorph.mdifferentiable
  given: (hf : IsLocalDiffeomorph I J n f) (hn : n != 0)
  proof: fun x => (hf x).mdifferentiableAt hn

中文:
引理 IsLocalDiffeomorph.mdifferentiable
  条件: (hf : IsLocalDiffeomorph I J n f) (hn : n != 0)
  证明: fun x => (hf x).mdifferentiableAt hn

Depends on / 依赖: mdifferentiableAt
-/
lemma IsLocalDiffeomorph.mdifferentiable (hf : IsLocalDiffeomorph I J n f) (hn : n != 0) :
    MDiff f :=
  fun x => (hf x).mdifferentiableAt hn

/--
lemma `Diffeomorph.isLocalDiffeomorph` / 引理 `Diffeomorph.isLocalDiffeomorph`

English:
lemma Diffeomorph.isLocalDiffeomorph
  given: (Φ : M ≃ₘ^n⟮I, J⟯ N)
  statement: IsLocalDiffeomorph I J n Φ
  proof: fun _x => ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

中文:
引理 Diffeomorph.isLocalDiffeomorph
  条件: (Φ : M ≃ₘ^n⟮I, J⟯ N)
  结论: IsLocalDiffeomorph I J n Φ
  证明: fun _x => ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

Depends on / 依赖: eqOn_refl, toPartialDiffeomorph
-/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _x => ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

-- FUTURE: if useful, also add "a `PartialDiffeomorph` is a local diffeomorphism on its source"

/--
theorem `IsLocalDiffeomorphOn.isLocalHomeomorphOn` / 定理 `IsLocalDiffeomorphOn.isLocalHomeomorphOn`

English:
theorem IsLocalDiffeomorphOn.isLocalHomeomorphOn
  given: {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s)
  proof: by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toOpenPartialHomeomorph, hyp⟩

中文:
定理 IsLocalDiffeomorphOn.isLocalHomeomorphOn
  条件: {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s)
  证明: by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toOpenPartialHomeomorph, hyp⟩

Depends on / 依赖: IsLocalHomeomorphOn, IsLocalHomeomorphOn.mk, U.toOpenPartialHomeomorph, toOpenPartialHomeomorph
-/
theorem IsLocalDiffeomorphOn.isLocalHomeomorphOn {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s) :
    IsLocalHomeomorphOn f s := by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toOpenPartialHomeomorph, hyp⟩

/--
theorem `IsLocalDiffeomorph.isLocalHomeomorph` / 定理 `IsLocalDiffeomorph.isLocalHomeomorph`

English:
theorem IsLocalDiffeomorph.isLocalHomeomorph
  given: (hf : IsLocalDiffeomorph I J n f)
  proof: by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ] at hf
  exact hf.isLocalHomeomorphOn

中文:
定理 IsLocalDiffeomorph.isLocalHomeomorph
  条件: (hf : IsLocalDiffeomorph I J n f)
  证明: by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ] at hf
  exact hf.isLocalHomeomorphOn

Depends on / 依赖: hf.isLocalHomeomorphOn, isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ, isLocalHomeomorphOn, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ
-/
theorem IsLocalDiffeomorph.isLocalHomeomorph (hf : IsLocalDiffeomorph I J n f) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ] at hf
  exact hf.isLocalHomeomorphOn

/--
lemma `IsLocalDiffeomorph.isOpenMap` / 引理 `IsLocalDiffeomorph.isOpenMap`

English:
lemma IsLocalDiffeomorph.isOpenMap
  given: (hf : IsLocalDiffeomorph I J n f)
  statement: IsOpenMap f
  proof: (hf.isLocalHomeomorph).isOpenMap

中文:
引理 IsLocalDiffeomorph.isOpenMap
  条件: (hf : IsLocalDiffeomorph I J n f)
  结论: IsOpenMap f
  证明: (hf.isLocalHomeomorph).isOpenMap

Depends on / 依赖: hf.isLocalHomeomorph, isLocalHomeomorph, isOpenMap
-/
lemma IsLocalDiffeomorph.isOpenMap (hf : IsLocalDiffeomorph I J n f) : IsOpenMap f :=
  (hf.isLocalHomeomorph).isOpenMap

/--
lemma `IsLocalDiffeomorph.isOpen_range` / 引理 `IsLocalDiffeomorph.isOpen_range`

English:
lemma IsLocalDiffeomorph.isOpen_range
  given: (hf : IsLocalDiffeomorph I J n f)
  statement: IsOpen (range f)
  proof: (hf.isOpenMap).isOpen_range

中文:
引理 IsLocalDiffeomorph.isOpen_range
  条件: (hf : IsLocalDiffeomorph I J n f)
  结论: IsOpen (range f)
  证明: (hf.isOpenMap).isOpen_range

Depends on / 依赖: hf.isOpenMap, isOpenMap, isOpen_range
-/
lemma IsLocalDiffeomorph.isOpen_range (hf : IsLocalDiffeomorph I J n f) : IsOpen (range f) :=
  (hf.isOpenMap).isOpen_range

/--
Definition of `IsLocalDiffeomorph.image` / `IsLocalDiffeomorph.image` 的定义

English:
definition IsLocalDiffeomorph.image
  signature: (hf : IsLocalDiffeomorph I J n f)
  body: ⟨range f, hf.isOpen_range⟩

中文:
定义 IsLocalDiffeomorph.image
  签名: (hf : IsLocalDiffeomorph I J n f)
  定义体: ⟨range f, hf.isOpen_range⟩
-/
@[expose] def IsLocalDiffeomorph.image (hf : IsLocalDiffeomorph I J n f) : Opens N :=
  ⟨range f, hf.isOpen_range⟩

/--
lemma `IsLocalDiffeomorph.image_coe` / 引理 `IsLocalDiffeomorph.image_coe`

English:
lemma IsLocalDiffeomorph.image_coe
  given: (hf : IsLocalDiffeomorph I J n f)
  statement: hf.image.1 = range f
  proof: rfl

中文:
引理 IsLocalDiffeomorph.image_coe
  条件: (hf : IsLocalDiffeomorph I J n f)
  结论: hf.image.1 = range f
  证明: rfl
-/
lemma IsLocalDiffeomorph.image_coe (hf : IsLocalDiffeomorph I J n f) : hf.image.1 = range f :=
  rfl

-- TODO: this result holds more generally for (local) structomorphisms
-- This argument implies a `LocalDiffeomorphOn f s` for `s` open is a `PartialDiffeomorph`

/--
Definition of `IsLocalDiffeomorph.diffeomorphOfBijective` / `IsLocalDiffeomorph.diffeomorphOfBijective` 的定义

English:
definition IsLocalDiffeomorph.diffeomorphOfBijective
  body: by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  -- Choose diffeomorphisms φ_x which coincide with `f` near `x`.
  choose Φ hyp using (fun x => hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  --

中文:
定义 IsLocalDiffeomorph.diffeomorphOfBijective
  定义体: by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  -- Choose diffeomorphisms φ_x which coincide with `f` near `x`.
  choose Φ hyp using (fun x => hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  --
-/
def IsLocalDiffeomorph.diffeomorphOfBijective
    (hf : IsLocalDiffeomorph I J n f) (hf' : Function.Bijective f) : Diffeomorph I J M N n := by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  -- Choose diffeomorphisms φ_x which coincide with `f` near `x`.
  choose Φ hyp using (fun x => hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  -- they're both inverses to g. In fact, the latter suffices for our proof.
  -- have (x y) : EqOn (Φ x).symm (Φ y).symm ((Φ x).target ∩ (Φ y).target) := sorry
  have aux (x) : EqOn g (Φ x).symm (Φ x).target :=
    eqOn_of_leftInvOn_of_rightInvOn (fun x' _ => hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toOpenPartialHomeomorph).rightInvOn
        ((Φ x).toOpenPartialHomeomorph).mapsTo_symm (hyp x).2.symm)
      (fun _y hy => (Φ x).map_target hy)
  exact {
    toFun := f
    invFun := g
    left_inv := hgInverse.1
    right_inv := hgInverse.2
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := by
      intro y
      let x := g y
      obtain ⟨hx, hfx⟩ := hyp x
      apply ((Φ x).symm.contMDiffOn.congr (aux x)).contMDiffAt (((Φ x).open_target).mem_nhds ?_)
      have : y = (Φ x) x := ((hgInverse.2 y).congr (hfx hx)).mp rfl
      exact this ▸ (Φ x).map_source hx }

end Basic

section Differential

variable {f : M -> N} {s : Set M} {x : M}

variable {I I' J n}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv` / `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv` 的定义

English:
definition IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
  body: mfderiv% f x
  invFun := mfderiv% hf.localInverse (f x)
  left_inv := by
    apply ContinuousLinearMap.leftInverse_of_comp
    rw [← mfderiv_id]; rw [← hf.localInverse_eventuallyEq_left.mfderiv_eq]
    exact (mfderiv_comp _ (hf.localInverse_mdifferentiableAt hn) (hf.mdifferentiableAt hn)).symm
  rig

中文:
定义 IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
  定义体: mfderiv% f x
  invFun := mfderiv% hf.localInverse (f x)
  left_inv := by
    apply ContinuousLinearMap.leftInverse_of_comp
    rw [← mfderiv_id]; rw [← hf.localInverse_eventuallyEq_left.mfderiv_eq]
    exact (mfderiv_comp _ (hf.localInverse_mdifferentiableAt hn) (hf.mdifferentiableAt hn)).symm
  rig
-/
@[expose] def IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) where
  toFun := mfderiv% f x
  invFun := mfderiv% hf.localInverse (f x)
  left_inv := by
    apply ContinuousLinearMap.leftInverse_of_comp
    rw [← mfderiv_id]; rw [← hf.localInverse_eventuallyEq_left.mfderiv_eq]
    exact (mfderiv_comp _ (hf.localInverse_mdifferentiableAt hn) (hf.mdifferentiableAt hn)).symm
  right_inv := by
    apply ContinuousLinearMap.rightInverse_of_comp
    rw [← mfderiv_id]; rw [← hf.localInverse_eventuallyEq_right.mfderiv_eq]
    -- We need to rewrite the base point hf.localInverse (f x) = x twice,
    -- in the differentiability hypothesis and for applying the chain rule.
    have hf' : MDifferentiableAt I J f (hf.localInverse (f x)) := by
      rw [hf.localInverse_left_inv hf.localInverse_mem_target]
      exact hf.mdifferentiableAt hn
    rw [mfderiv_comp _ hf' (hf.localInverse_mdifferentiableAt hn)]; rw [hf.localInverse_left_inv hf.localInverse_mem_target]
  continuous_toFun := (mfderiv% f x).cont
  continuous_invFun := (mfderiv% hf.localInverse (f x)).cont
  map_add' := fun x_1 y => map_add _ x_1 y
  map_smul' := by intros; simp

@[simp, mfld_simps]
/--
lemma `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe` / 引理 `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe`

English:
lemma IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
  proof: rfl

中文:
引理 IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
  证明: rfl
-/
lemma IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) :
    hf.mfderivToContinuousLinearEquiv hn = mfderiv% f x := rfl

/--
Definition of `Diffeomorph.mfderivToContinuousLinearEquiv` / `Diffeomorph.mfderivToContinuousLinearEquiv` 的定义

English:
definition Diffeomorph.mfderivToContinuousLinearEquiv
  body: (Φ.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn

中文:
定义 Diffeomorph.mfderivToContinuousLinearEquiv
  定义体: (Φ.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn

Depends on / 依赖: isLocalDiffeomorph, mfderivToContinuousLinearEquiv
-/
def Diffeomorph.mfderivToContinuousLinearEquiv
    (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (Φ x) :=
  (Φ.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn

/--
lemma `Diffeomorph.mfderivToContinuousLinearEquiv_coe` / 引理 `Diffeomorph.mfderivToContinuousLinearEquiv_coe`

English:
lemma Diffeomorph.mfderivToContinuousLinearEquiv_coe
  given: (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0)
  proof: by rfl

中文:
引理 Diffeomorph.mfderivToContinuousLinearEquiv_coe
  条件: (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0)
  证明: by rfl
-/
lemma Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) :
    Φ.mfderivToContinuousLinearEquiv hn x = mfderiv% Φ x := by rfl

/--
Definition of `IsLocalDiffeomorph.mfderivToContinuousLinearEquiv` / `IsLocalDiffeomorph.mfderivToContinuousLinearEquiv` 的定义

English:
definition IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
  body: (hf x).mfderivToContinuousLinearEquiv hn

中文:
定义 IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
  定义体: (hf x).mfderivToContinuousLinearEquiv hn

Depends on / 依赖: mfderivToContinuousLinearEquiv
-/
def IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorph I J n f) (hn : n != 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) :=
  (hf x).mfderivToContinuousLinearEquiv hn

/--
lemma `IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe` / 引理 `IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe`

English:
lemma IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
  proof: (hf x).mfderivToContinuousLinearEquiv_coe hn

中文:
引理 IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
  证明: (hf x).mfderivToContinuousLinearEquiv_coe hn

Depends on / 依赖: mfderivToContinuousLinearEquiv_coe
-/
lemma IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorph I J n f) (hn : n != 0) (x : M) :
    hf.mfderivToContinuousLinearEquiv hn x = mfderiv% f x :=
  (hf x).mfderivToContinuousLinearEquiv_coe hn

end Differential
