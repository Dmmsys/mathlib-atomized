/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Patrick Massot, Floris van Doorn
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Vector bundles

In this file we define (topological) vector bundles.

Let `B` be the base space, let `F` be a normed space over a normed field `R`, and let
`E : B → Type*` be a `FiberBundle` with fiber `F`, in which, for each `x`, the fiber `E x` is a
topological vector space over `R`.

To have a vector bundle structure on `Bundle.TotalSpace F E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
  fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
  from `B` into `F →L[R] F` is continuous on `e.baseSet ∩ e'.baseSet` with respect to the operator
  norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `VectorBundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Main Definitions

* `Bundle.Trivialization.IsLinear`: a class stating that a trivialization is fiberwise linear
  on its base set.
* `Bundle.Trivialization.linearEquivAt` and `Bundle.Trivialization.continuousLinearMapAt` are the
  (continuous) linear fiberwise equivalences a trivialization induces.
* They have forward maps `Bundle.Trivialization.linearMapAt` /
  `Bundle.Trivialization.continuousLinearMapAt` and inverses `Bundle.Trivialization.symmₗ` /
  `Bundle.Trivialization.symmL`. Note that these are all defined
  everywhere, since they are extended using the zero function.
* `Bundle.Trivialization.coordChangeL` is the coordinate change induced by two trivializations.
  It only makes sense on the intersection of their base sets,
  but is extended outside it using the identity.
* Given a continuous (semi)linear map between `E x` and `E' y` where `E` and `E'` are bundles over
  possibly different base sets, `ContinuousLinearMap.inCoordinates` turns this into a continuous
  (semi)linear map between the chosen fibers of those bundles.

## Implementation notes

The implementation choices in the vector bundle definition are discussed in the "Implementation
notes" section of `Mathlib/Topology/FiberBundle/Basic.lean`.

## Tags
Vector bundle
-/

@[expose] public section

noncomputable section

open Bundle Set Topology

variable (R : Type*) {B : Type*} (F : Type*) (E : B -> Type*)

section TopologicalVectorSpace

variable {F E}
variable [Semiring R] [TopologicalSpace F] [TopologicalSpace B]

/--
Definition of `Bundle.Pretrivialization.IsLinear` / `Bundle.Pretrivialization.IsLinear` 的定义

English:
class Bundle.Pretrivialization.IsLinear
  parameters: [AddCommMonoid F] [Module R F]
  axioms and operations (1):
    - linear : forall b in e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

中文:
类 Bundle.Pretrivialization.IsLinear
  参数: [AddCommMonoid F] [Module R F]
  公理与运算 (1 个):
    - linear : 对任意 b in e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2
-/
protected class Bundle.Pretrivialization.IsLinear [AddCommMonoid F] [Module R F]
  [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)] (e : Pretrivialization F (π F E)) : Prop where
  linear : forall b in e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Bundle.Pretrivialization

variable (e : Pretrivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

/--
theorem `linear` / 定理 `linear`

English:
theorem linear
  statement: [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)]
  proof: IsLinear.linear b hb

中文:
定理 linear
  结论: [AddCommMonoid F] [Module R F] [对任意 x, AddCommMonoid (E x)] [对任意 x, Module R (E x)]
  证明: IsLinear.linear b hb

Depends on / 依赖: IsLinear, IsLinear.linear, linear
-/
theorem linear [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)]
    [e.IsLinear R] {b : B} (hb : b in e.baseSet) :
    IsLinearMap R fun x : E b => (e ⟨b, x⟩).2 :=
  IsLinear.linear b hb

variable [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)]

open scoped Classical in
/--
Definition of `symmₗ` / `symmₗ` 的定义

English:
definition symmₗ
  signature: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B)
  body: by
  refine if hb : b in e.baseSet then IsLinearMap.mk' (e.symm b) ?_ else 0
  exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v =>
congr_arg Prod.snd e.apply_mk_symm hb v).isLinear

@[simp]

中文:
定义 symmₗ
  签名: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: by
  refine if hb : b in e.baseSet then IsLinearMap.mk' (e.symm b) ?_ else 0
  exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v =>
congr_arg Prod.snd e.apply_mk_symm hb v).isLinear

@[simp]
-/
protected def symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : F ->ₗ[R] E b := by
  refine if hb : b in e.baseSet then IsLinearMap.mk' (e.symm b) ?_ else 0
  exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v =>
congr_arg Prod.snd e.apply_mk_symm hb v).isLinear

@[simp]
/--
lemma `symmₗ_apply` / 引理 `symmₗ_apply`

English:
lemma symmₗ_apply
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: by
  simp [Pretrivialization.symmₗ, hb]

@[simp]

中文:
引理 symmₗ_apply
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: by
  simp [Pretrivialization.symmₗ, hb]

@[simp]

Depends on / 依赖: Pretrivialization, Pretrivialization.symm
-/
lemma symmₗ_apply (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : F) : e.symmₗ R b y = e.symm b y := by
  simp [Pretrivialization.symmₗ, hb]

@[simp]
/--
lemma `symmₗ_apply_of_notMem` / 引理 `symmₗ_apply_of_notMem`

English:
lemma symmₗ_apply_of_notMem
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by
  simp [Pretrivialization.symmₗ, hb]

中文:
引理 symmₗ_apply_of_notMem
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by
  simp [Pretrivialization.symmₗ, hb]

Depends on / 依赖: Pretrivialization, Pretrivialization.symm
-/
lemma symmₗ_apply_of_notMem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmₗ R b y = 0 := by
  simp [Pretrivialization.symmₗ, hb]

/-- A pretrivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps -fullyApplied]
/--
Definition of `linearEquivAt` / `linearEquivAt` 的定义

English:
definition linearEquivAt
  signature: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b in e.baseSet)
  body: (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v

中文:
定义 linearEquivAt
  签名: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b in e.baseSet)
  定义体: (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v
-/
def linearEquivAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b in e.baseSet) :
    E b ≃ₗ[R] F where
  toFun y := (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v

open scoped Classical in
/--
Definition of `linearMapAt` / `linearMapAt` 的定义

English:
definition linearMapAt
  signature: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B)
  body: if hb : b in e.baseSet then e.linearEquivAt R b hb else 0

中文:
定义 linearMapAt
  签名: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: if hb : b in e.baseSet then e.linearEquivAt R b hb else 0
-/
protected def linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : E b ->ₗ[R] F :=
  if hb : b in e.baseSet then e.linearEquivAt R b hb else 0

variable {R}

open scoped Classical in
/--
theorem `coe_linearMapAt` / 定理 `coe_linearMapAt`

English:
theorem coe_linearMapAt
  given: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B)
  proof: by
  rw [Pretrivialization.linearMapAt]
  split_ifs <;> rfl

@[simp]

中文:
定理 coe_linearMapAt
  条件: (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B)
  证明: by
  rw [Pretrivialization.linearMapAt]
  split_ifs <;> rfl

@[simp]

Depends on / 依赖: Pretrivialization, Pretrivialization.linearMapAt, linearMapAt, split_ifs
-/
theorem coe_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b in e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [Pretrivialization.linearMapAt]
  split_ifs <;> rfl

@[simp]
/--
theorem `coe_linearMapAt_of_mem` / 定理 `coe_linearMapAt_of_mem`

English:
theorem coe_linearMapAt_of_mem
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by
  simp_rw [coe_linearMapAt, if_pos hb]

中文:
定理 coe_linearMapAt_of_mem
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by
  simp_rw [coe_linearMapAt, if_pos hb]

Depends on / 依赖: coe_linearMapAt, if_pos, simp_rw
-/
theorem coe_linearMapAt_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, if_pos hb]

open scoped Classical in
/--
theorem `linearMapAt_apply` / 定理 `linearMapAt_apply`

English:
theorem linearMapAt_apply
  given: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b)
  proof: by
  rw [coe_linearMapAt]

中文:
定理 linearMapAt_apply
  条件: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b)
  证明: by
  rw [coe_linearMapAt]

Depends on / 依赖: coe_linearMapAt
-/
theorem linearMapAt_apply (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b in e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [coe_linearMapAt]

/--
theorem `linearMapAt_def_of_mem` / 定理 `linearMapAt_def_of_mem`

English:
theorem linearMapAt_def_of_mem
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: dif_pos hb

中文:
定理 linearMapAt_def_of_mem
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: dif_pos hb

Depends on / 依赖: dif_pos
-/
theorem linearMapAt_def_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb

/--
theorem `linearMapAt_def_of_notMem` / 定理 `linearMapAt_def_of_notMem`

English:
theorem linearMapAt_def_of_notMem
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: dif_neg hb

中文:
定理 linearMapAt_def_of_notMem
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: dif_neg hb

Depends on / 依赖: dif_neg
-/
theorem linearMapAt_def_of_notMem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb

/--
theorem `linearMapAt_eq_zero` / 定理 `linearMapAt_eq_zero`

English:
theorem linearMapAt_eq_zero
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: dif_neg hb

中文:
定理 linearMapAt_eq_zero
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: dif_neg hb

Depends on / 依赖: dif_neg
-/
theorem linearMapAt_eq_zero (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb

/--
theorem `symmₗ_linearMapAt` / 定理 `symmₗ_linearMapAt`

English:
theorem symmₗ_linearMapAt
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by simp [hb]

中文:
定理 symmₗ_linearMapAt
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by simp [hb]
-/
theorem symmₗ_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y := by simp [hb]

/--
theorem `linearMapAt_symmₗ` / 定理 `linearMapAt_symmₗ`

English:
theorem linearMapAt_symmₗ
  statement: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by simp [hb]

中文:
定理 linearMapAt_symmₗ
  结论: (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by simp [hb]
-/
theorem linearMapAt_symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y := by simp [hb]

end Pretrivialization

variable [TopologicalSpace (TotalSpace F E)]

/--
Definition of `Trivialization.IsLinear` / `Trivialization.IsLinear` 的定义

English:
class Trivialization.IsLinear
  parameters: [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)]
  axioms and operations (1):
    - linear : forall b in e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

中文:
类 Trivialization.IsLinear
  参数: [AddCommMonoid F] [Module R F] [对任意 x, AddCommMonoid (E x)]
  公理与运算 (1 个):
    - linear : 对任意 b in e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2
-/
protected class Trivialization.IsLinear [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)]
  [forall x, Module R (E x)] (e : Trivialization F (π F E)) : Prop where
  linear : forall b in e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Trivialization

variable (e : Trivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

/--
theorem `linear` / 定理 `linear`

English:
theorem linear
  statement: [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)]
  proof: Trivialization.IsLinear.linear b hb

中文:
定理 linear
  结论: [AddCommMonoid F] [Module R F] [对任意 x, AddCommMonoid (E x)]
  证明: Trivialization.IsLinear.linear b hb
-/
protected theorem linear [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)]
    [forall x, Module R (E x)] [e.IsLinear R] {b : B} (hb : b in e.baseSet) :
    IsLinearMap R fun y : E b => (e ⟨b, y⟩).2 :=
  Trivialization.IsLinear.linear b hb

/--
Instance `toPretrivialization.isLinear` / 实例 `toPretrivialization.isLinear`

English:
instance toPretrivialization.isLinear
  signature: [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)]
  body: { (‹_› : e.IsLinear R) with }

中文:
实例 toPretrivialization.isLinear
  签名: [AddCommMonoid F] [Module R F] [对任意 x, AddCommMonoid (E x)]
  定义体: { (‹_› : e.IsLinear R) with }

Depends on / 依赖: IsLinear, e.IsLinear
-/
instance toPretrivialization.isLinear [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)]
    [forall x, Module R (E x)] [e.IsLinear R] : e.toPretrivialization.IsLinear R :=
  { (‹_› : e.IsLinear R) with }

variable [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)]

/--
Definition of `linearEquivAt` / `linearEquivAt` 的定义

English:
definition linearEquivAt
  signature: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b in e.baseSet)
  body: e.toPretrivialization.linearEquivAt R b hb

中文:
定义 linearEquivAt
  签名: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b in e.baseSet)
  定义体: e.toPretrivialization.linearEquivAt R b hb

Depends on / 依赖: e.toPretrivialization.linearEquivAt, linearEquivAt, toPretrivialization
-/
def linearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b in e.baseSet) :
    E b ≃ₗ[R] F :=
  e.toPretrivialization.linearEquivAt R b hb

variable {R}

@[simp]
/--
theorem `linearEquivAt_apply` / 定理 `linearEquivAt_apply`

English:
theorem linearEquivAt_apply
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  proof: rfl

@[simp]

中文:
定理 linearEquivAt_apply
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  证明: rfl

@[simp]
-/
theorem linearEquivAt_apply (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b in e.baseSet) (v : E b) : e.linearEquivAt R b hb v = (e ⟨b, v⟩).2 :=
  rfl

@[simp]
/--
theorem `linearEquivAt_symm_apply` / 定理 `linearEquivAt_symm_apply`

English:
theorem linearEquivAt_symm_apply
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  proof: rfl

中文:
定理 linearEquivAt_symm_apply
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  证明: rfl
-/
theorem linearEquivAt_symm_apply (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b in e.baseSet) (v : F) : (e.linearEquivAt R b hb).symm v = e.symm b v :=
  rfl

variable (R) in
/--
Definition of `symmₗ` / `symmₗ` 的定义

English:
definition symmₗ
  signature: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  body: e.toPretrivialization.symmₗ R b

中文:
定义 symmₗ
  签名: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: e.toPretrivialization.symmₗ R b
-/
protected def symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F ->ₗ[R] E b :=
  e.toPretrivialization.symmₗ R b

/--
theorem `coe_symmₗ` / 定理 `coe_symmₗ`

English:
theorem coe_symmₗ
  given: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: by
  ext y; exact e.toPretrivialization.symmₗ_apply R hb y

@[simp]

中文:
定理 coe_symmₗ
  条件: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: by
  ext y; exact e.toPretrivialization.symmₗ_apply R hb y

@[simp]

Depends on / 依赖: e.toPretrivialization.symm, toPretrivialization
-/
theorem coe_symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet) :
    ⇑(e.symmₗ R b) = e.symm b := by
  ext y; exact e.toPretrivialization.symmₗ_apply R hb y

@[simp]
/--
theorem `symmₗ_apply` / 定理 `symmₗ_apply`

English:
theorem symmₗ_apply
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: e.toPretrivialization.symmₗ_apply R hb y

@[simp]

中文:
定理 symmₗ_apply
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: e.toPretrivialization.symmₗ_apply R hb y

@[simp]

Depends on / 依赖: e.toPretrivialization.symm, toPretrivialization
-/
theorem symmₗ_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : F) : e.symmₗ R b y = e.symm b y :=
  e.toPretrivialization.symmₗ_apply R hb y

@[simp]
/--
theorem `symmₗ_apply_of_notMem` / 定理 `symmₗ_apply_of_notMem`

English:
theorem symmₗ_apply_of_notMem
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: e.toPretrivialization.symmₗ_apply_of_notMem R hb y

中文:
定理 symmₗ_apply_of_notMem
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: e.toPretrivialization.symmₗ_apply_of_notMem R hb y

Depends on / 依赖: e.toPretrivialization.symm, toPretrivialization
-/
theorem symmₗ_apply_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmₗ R b y = 0 :=
  e.toPretrivialization.symmₗ_apply_of_notMem R hb y

variable (R) in
/--
Definition of `linearMapAt` / `linearMapAt` 的定义

English:
definition linearMapAt
  signature: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  body: e.toPretrivialization.linearMapAt R b

中文:
定义 linearMapAt
  签名: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: e.toPretrivialization.linearMapAt R b
-/
protected def linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b ->ₗ[R] F :=
  e.toPretrivialization.linearMapAt R b

open scoped Classical in
/--
theorem `coe_linearMapAt` / 定理 `coe_linearMapAt`

English:
theorem coe_linearMapAt
  given: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  proof: e.toPretrivialization.coe_linearMapAt b

@[simp]

中文:
定理 coe_linearMapAt
  条件: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  证明: e.toPretrivialization.coe_linearMapAt b

@[simp]

Depends on / 依赖: coe_linearMapAt, e.toPretrivialization.coe_linearMapAt, toPretrivialization
-/
theorem coe_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b in e.baseSet then (e ⟨b, y⟩).2 else 0 :=
  e.toPretrivialization.coe_linearMapAt b

@[simp]
/--
theorem `coe_linearMapAt_of_mem` / 定理 `coe_linearMapAt_of_mem`

English:
theorem coe_linearMapAt_of_mem
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by
  simp_rw [coe_linearMapAt, if_pos hb]

中文:
定理 coe_linearMapAt_of_mem
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by
  simp_rw [coe_linearMapAt, if_pos hb]

Depends on / 依赖: coe_linearMapAt, if_pos, simp_rw
-/
theorem coe_linearMapAt_of_mem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, if_pos hb]

open scoped Classical in
/--
theorem `linearMapAt_apply` / 定理 `linearMapAt_apply`

English:
theorem linearMapAt_apply
  given: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b)
  proof: by
  rw [coe_linearMapAt]

中文:
定理 linearMapAt_apply
  条件: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b)
  证明: by
  rw [coe_linearMapAt]

Depends on / 依赖: coe_linearMapAt
-/
theorem linearMapAt_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b in e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [coe_linearMapAt]

/--
theorem `linearMapAt_def_of_mem` / 定理 `linearMapAt_def_of_mem`

English:
theorem linearMapAt_def_of_mem
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: dif_pos hb

中文:
定理 linearMapAt_def_of_mem
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: dif_pos hb

Depends on / 依赖: dif_pos
-/
theorem linearMapAt_def_of_mem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb

/--
theorem `linearMapAt_def_of_notMem` / 定理 `linearMapAt_def_of_notMem`

English:
theorem linearMapAt_def_of_notMem
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: dif_neg hb

中文:
定理 linearMapAt_def_of_notMem
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: dif_neg hb

Depends on / 依赖: dif_neg
-/
theorem linearMapAt_def_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb

/--
theorem `symm_linearMapAt` / 定理 `symm_linearMapAt`

English:
theorem symm_linearMapAt
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: by
  simp [hb]

中文:
定理 symm_linearMapAt
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: by
  simp [hb]
-/
theorem symm_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : E b) : e.symm b (e.linearMapAt R b y) = y := by
  simp [hb]

/--
theorem `symmₗ_linearMapAt` / 定理 `symmₗ_linearMapAt`

English:
theorem symmₗ_linearMapAt
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: e.toPretrivialization.symmₗ_linearMapAt hb y

@[simp]

中文:
定理 symmₗ_linearMapAt
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: e.toPretrivialization.symmₗ_linearMapAt hb y

@[simp]

Depends on / 依赖: e.toPretrivialization.symm, toPretrivialization
-/
theorem symmₗ_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y :=
  e.toPretrivialization.symmₗ_linearMapAt hb y

@[simp]
/--
theorem `linearMapAt_symm` / 定理 `linearMapAt_symm`

English:
theorem linearMapAt_symm
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: by
  simp [hb]

中文:
定理 linearMapAt_symm
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: by
  simp [hb]
-/
theorem linearMapAt_symm (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : F) : e.linearMapAt R b (e.symm b y) = y := by
  simp [hb]

/--
theorem `linearMapAt_symmₗ` / 定理 `linearMapAt_symmₗ`

English:
theorem linearMapAt_symmₗ
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: e.toPretrivialization.linearMapAt_symmₗ hb y

中文:
定理 linearMapAt_symmₗ
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: e.toPretrivialization.linearMapAt_symmₗ hb y

Depends on / 依赖: e.toPretrivialization.linearMapAt_symm, toPretrivialization
-/
theorem linearMapAt_symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y :=
  e.toPretrivialization.linearMapAt_symmₗ hb y

variable (R) in
open scoped Classical in
/--
Definition of `coordChangeL` / `coordChangeL` 的定义

English:
definition coordChangeL
  signature: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B)
  body: { toLinearEquiv := if hb : b in e.baseSet inter e'.baseSet
      then (e.linearEquivAt R b (hb.1 :)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
    continuous_toFun := by
      by_cases hb : b in e.baseSet inter e'.baseSet
      · rw [dif_pos hb]
        refine (e'.contin

中文:
定义 coordChangeL
  签名: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B)
  定义体: { toLinearEquiv := if hb : b in e.baseSet inter e'.baseSet
      then (e.linearEquivAt R b (hb.1 :)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
    continuous_toFun := by
      by_cases hb : b in e.baseSet inter e'.baseSet
      · rw [dif_pos hb]
        refine (e'.contin

Depends on / 依赖: Continuous, Continuous.prodMk_right, LinearEquiv, LinearEquiv.refl, baseSet, comp_continuous, continuousOn, continuousOn.comp_continuous, continuousOn_symm, continuous_id, continuous_in, continuous_toFun, dif_neg, dif_pos, e.baseSet, e.continuousOn_symm.comp_continuous, e.linearEquivAt, linearEquivAt, mem_source, mem_source.mpr
-/
def coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B) :
    F ≃L[R] F :=
  { toLinearEquiv := if hb : b in e.baseSet inter e'.baseSet
      then (e.linearEquivAt R b (hb.1 :)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
    continuous_toFun := by
      by_cases hb : b in e.baseSet inter e'.baseSet
      · rw [dif_pos hb]
        refine (e'.continuousOn.comp_continuous ?_ ?_).snd
        · exact e.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.1 (mem_univ y)
        · exact fun y => e'.mem_source.mpr hb.2
      · rw [dif_neg hb]
        exact continuous_id
    continuous_invFun := by
      by_cases hb : b in e.baseSet inter e'.baseSet
      · rw [dif_pos hb]
        refine (e.continuousOn.comp_continuous ?_ ?_).snd
        · exact e'.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1
      · rw [dif_neg hb]
        exact continuous_id }

/--
theorem `coe_coordChangeL` / 定理 `coe_coordChangeL`

English:
theorem coe_coordChangeL
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  proof: congr_arg (fun f : F ≃ₗ[R] F => ⇑f) (dif_pos hb)

中文:
定理 coe_coordChangeL
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  证明: congr_arg (fun f : F ≃ₗ[R] F => ⇑f) (dif_pos hb)

Depends on / 依赖: congr_arg, dif_pos
-/
theorem coe_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b in e.baseSet inter e'.baseSet) :
    ⇑(coordChangeL R e e' b) = (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  congr_arg (fun f : F ≃ₗ[R] F => ⇑f) (dif_pos hb)

/--
theorem `coe_coordChangeL'` / 定理 `coe_coordChangeL'`

English:
theorem coe_coordChangeL'
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  proof: LinearEquiv.coe_injective (coe_coordChangeL _ _ hb)

中文:
定理 coe_coordChangeL'
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  证明: LinearEquiv.coe_injective (coe_coordChangeL _ _ hb)

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_injective, coe_coordChangeL, coe_injective
-/
theorem coe_coordChangeL' (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b in e.baseSet inter e'.baseSet) :
    (coordChangeL R e e' b).toLinearEquiv =
      (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  LinearEquiv.coe_injective (coe_coordChangeL _ _ hb)

/--
theorem `symm_coordChangeL` / 定理 `symm_coordChangeL`

English:
theorem symm_coordChangeL
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  proof: by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [coe_coordChangeL' e' e hb]; rw [(coordChangeL R e e' b).toLinearEquiv_symm]; rw [coe_coordChangeL' e e' hb.symm]; rw [LinearEquiv.trans_symm]; rw [LinearEquiv.symm_symm]

中文:
定理 symm_coordChangeL
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  证明: by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [coe_coordChangeL' e' e hb]; rw [(coordChangeL R e e' b).toLinearEquiv_symm]; rw [coe_coordChangeL' e e' hb.symm]; rw [LinearEquiv.trans_symm]; rw [LinearEquiv.symm_symm]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_injective, LinearEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_symm, coe_coordChangeL, coordChangeL, hb.symm, symm_symm, toLinearEquiv_injective, toLinearEquiv_symm, trans_symm
-/
theorem symm_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b in e'.baseSet inter e.baseSet) : (e.coordChangeL R e' b).symm = e'.coordChangeL R e b := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [coe_coordChangeL' e' e hb]; rw [(coordChangeL R e e' b).toLinearEquiv_symm]; rw [coe_coordChangeL' e e' hb.symm]; rw [LinearEquiv.trans_symm]; rw [LinearEquiv.symm_symm]

/--
theorem `coordChangeL_apply` / 定理 `coordChangeL_apply`

English:
theorem coordChangeL_apply
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  proof: congr_fun (coe_coordChangeL e e' hb) y

中文:
定理 coordChangeL_apply
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  证明: congr_fun (coe_coordChangeL e e' hb) y

Depends on / 依赖: coe_coordChangeL, congr_fun
-/
theorem coordChangeL_apply (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b in e.baseSet inter e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' ⟨b, e.symm b y⟩).2 :=
  congr_fun (coe_coordChangeL e e' hb) y

/--
theorem `mk_coordChangeL` / 定理 `mk_coordChangeL`

English:
theorem mk_coordChangeL
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  proof: by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact e.coordChangeL_apply e' hb y

中文:
定理 mk_coordChangeL
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  证明: by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact e.coordChangeL_apply e' hb y

Depends on / 依赖: coe_fst, coordChangeL_apply, e.coordChangeL_apply, e.mk_symm, e.proj_symm_apply, mk_symm, proj_symm_apply
-/
theorem mk_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b in e.baseSet inter e'.baseSet) (y : F) :
    (b, coordChangeL R e e' b y) = e' ⟨b, e.symm b y⟩ := by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact e.coordChangeL_apply e' hb y

/--
theorem `apply_symm_apply_eq_coordChangeL` / 定理 `apply_symm_apply_eq_coordChangeL`

English:
theorem apply_symm_apply_eq_coordChangeL
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R]
  proof: by
  rw [e.mk_coordChangeL e' hb]; rw [e.mk_symm hb.1]

中文:
定理 apply_symm_apply_eq_coordChangeL
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R]
  证明: by
  rw [e.mk_coordChangeL e' hb]; rw [e.mk_symm hb.1]

Depends on / 依赖: e.mk_coordChangeL, e.mk_symm, mk_coordChangeL, mk_symm
-/
theorem apply_symm_apply_eq_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R]
    [e'.IsLinear R] {b : B} (hb : b in e.baseSet inter e'.baseSet) (v : F) :
    e' (e.toOpenPartialHomeomorph.symm (b, v)) = (b, e.coordChangeL R e' b v) := by
  rw [e.mk_coordChangeL e' hb]; rw [e.mk_symm hb.1]

/--
theorem `coordChangeL_apply'` / 定理 `coordChangeL_apply'`

English:
theorem coordChangeL_apply'
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  proof: by
  rw [e.coordChangeL_apply e' hb]; rw [e.mk_symm hb.1]

中文:
定理 coordChangeL_apply'
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
  证明: by
  rw [e.coordChangeL_apply e' hb]; rw [e.mk_symm hb.1]

Depends on / 依赖: coordChangeL_apply, e.coordChangeL_apply, e.mk_symm, mk_symm
-/
theorem coordChangeL_apply' (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b in e.baseSet inter e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' (e.toOpenPartialHomeomorph.symm (b, y))).2 := by
  rw [e.coordChangeL_apply e' hb]; rw [e.mk_symm hb.1]

/--
theorem `coordChangeL_symm_apply` / 定理 `coordChangeL_symm_apply`

English:
theorem coordChangeL_symm_apply
  statement: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R]
  proof: congr_arg LinearEquiv.invFun (dif_pos hb)

中文:
定理 coordChangeL_symm_apply
  结论: (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R]
  证明: congr_arg LinearEquiv.invFun (dif_pos hb)

Depends on / 依赖: LinearEquiv, LinearEquiv.invFun, congr_arg, dif_pos, invFun
-/
theorem coordChangeL_symm_apply (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R]
    {b : B} (hb : b in e.baseSet inter e'.baseSet) :
    ⇑(coordChangeL R e e' b).symm =
      (e'.linearEquivAt R b hb.2).symm.trans (e.linearEquivAt R b hb.1) :=
  congr_arg LinearEquiv.invFun (dif_pos hb)

end Bundle.Trivialization

end TopologicalVectorSpace

section

namespace Bundle

/--
Definition of `zeroSection` / `zeroSection` 的定义

English:
definition zeroSection
  signature: [forall x, Zero (E x)]
  body: (⟨·, 0⟩)

@[simp, mfld_simps]

中文:
定义 zeroSection
  签名: [对任意 x, Zero (E x)]
  定义体: (⟨·, 0⟩)

@[simp, mfld_simps]
-/
def zeroSection [forall x, Zero (E x)] : B -> TotalSpace F E := (⟨·, 0⟩)

@[simp, mfld_simps]
/--
theorem `zeroSection_proj` / 定理 `zeroSection_proj`

English:
theorem zeroSection_proj
  given: [forall x, Zero (E x)] (x : B)
  statement: (zeroSection F E x).proj = x
  proof: rfl

@[simp, mfld_simps]

中文:
定理 zeroSection_proj
  条件: [对任意 x, Zero (E x)] (x : B)
  结论: (zeroSection F E x).proj = x
  证明: rfl

@[simp, mfld_simps]
-/
theorem zeroSection_proj [forall x, Zero (E x)] (x : B) : (zeroSection F E x).proj = x :=
  rfl

@[simp, mfld_simps]
/--
theorem `zeroSection_snd` / 定理 `zeroSection_snd`

English:
theorem zeroSection_snd
  given: [forall x, Zero (E x)] (x : B)
  statement: (zeroSection F E x).2 = 0
  proof: rfl

中文:
定理 zeroSection_snd
  条件: [对任意 x, Zero (E x)] (x : B)
  结论: (zeroSection F E x).2 = 0
  证明: rfl
-/
theorem zeroSection_snd [forall x, Zero (E x)] (x : B) : (zeroSection F E x).2 = 0 :=
  rfl

end Bundle

open Bundle

variable [NontriviallyNormedField R] [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [forall x, TopologicalSpace (E x)] [FiberBundle F E]

/--
Definition of `VectorBundle` / `VectorBundle` 的定义

English:
class VectorBundle
  parameters: : Prop where
  axioms and operations (2):
    - trivialization_linear' : forall (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.IsLinear R
    - continuousOn_coordChange' : forall (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'], ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B -> F ->L[R] F) (e.baseSet inter e'.baseSet)

中文:
类 VectorBundle
  参数: : 命题 where
  公理与运算 (2 个):
    - trivialization_linear' : 对任意 (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.IsLinear R
    - continuousOn_coordChange' : 对任意 (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'], ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B -> F ->L[R] F) (e.baseSet inter e'.baseSet)
-/
class VectorBundle : Prop where
  trivialization_linear' : forall (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.IsLinear R
  continuousOn_coordChange' :
    forall (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B -> F ->L[R] F)
        (e.baseSet inter e'.baseSet)

variable {F E}

instance (priority := 100) trivialization_linear [VectorBundle R F E] (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] : e.IsLinear R :=
  VectorBundle.trivialization_linear' e

/--
theorem `continuousOn_coordChange` / 定理 `continuousOn_coordChange`

English:
theorem continuousOn_coordChange
  statement: [VectorBundle R F E] (e e' : Trivialization F (π F E))
  proof: VectorBundle.continuousOn_coordChange' e e'

中文:
定理 continuousOn_coordChange
  结论: [VectorBundle R F E] (e e' : Trivialization F (π F E))
  证明: VectorBundle.continuousOn_coordChange' e e'

Depends on / 依赖: VectorBundle, VectorBundle.continuousOn_coordChange, continuousOn_coordChange
-/
theorem continuousOn_coordChange [VectorBundle R F E] (e e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B -> F ->L[R] F)
      (e.baseSet inter e'.baseSet) :=
  VectorBundle.continuousOn_coordChange' e e'

namespace Bundle.Trivialization

/-- Forward map of `Bundle.Trivialization.continuousLinearEquivAt` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps -fullyApplied apply]
/--
Definition of `continuousLinearMapAt` / `continuousLinearMapAt` 的定义

English:
definition continuousLinearMapAt
  signature: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  body: { e.linearMapAt R b with
    toFun := e.linearMapAt R b -- given explicitly to help `simps`
    cont := by
      rw [e.coe_linearMapAt b]
      classical
      refine continuous_if_const _ (fun hb => ?_) fun _ => continuous_zero
      exact (e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_i

中文:
定义 continuousLinearMapAt
  签名: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: { e.linearMapAt R b with
    toFun := e.linearMapAt R b -- given explicitly to help `simps`
    cont := by
      rw [e.coe_linearMapAt b]
      classical
      refine continuous_if_const _ (fun hb => ?_) fun _ => continuous_zero
      exact (e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_i

Depends on / 依赖: FiberBundle, FiberBundle.totalSpaceMk_isInducing, classical, coe_linearMapAt, comp_continuous, continuous, continuousOn, continuous_if_const, continuous_zero, e.coe_linearMapAt, e.continuousOn.comp_continuous, e.linearMapAt, e.mem_source.mpr, explicitly, linearMapAt, mem_source, totalSpaceMk_isInducing
-/
def continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b ->L[R] F :=
  { e.linearMapAt R b with
    toFun := e.linearMapAt R b -- given explicitly to help `simps`
    cont := by
      rw [e.coe_linearMapAt b]
      classical
      refine continuous_if_const _ (fun hb => ?_) fun _ => continuous_zero
      exact (e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_isInducing F E b).continuous
        fun x => e.mem_source.mpr hb).snd }

/--
lemma `continuousLinearMapAt_apply_of_mem` / 引理 `continuousLinearMapAt_apply_of_mem`

English:
lemma continuousLinearMapAt_apply_of_mem
  statement: (e : Trivialization F TotalSpace.proj)
  proof: by
  simp [coe_linearMapAt_of_mem e hb]

中文:
引理 continuousLinearMapAt_apply_of_mem
  结论: (e : Trivialization F TotalSpace.proj)
  证明: by
  simp [coe_linearMapAt_of_mem e hb]

Depends on / 依赖: coe_linearMapAt_of_mem
-/
lemma continuousLinearMapAt_apply_of_mem (e : Trivialization F TotalSpace.proj)
    [Trivialization.IsLinear R e] {b : B} (hb : b in e.baseSet) (y : E b) :
    (continuousLinearMapAt R e b) y = (e ⟨b, y⟩).2 := by
  simp [coe_linearMapAt_of_mem e hb]

/--
Definition of `symmL` / `symmL` 的定义

English:
definition symmL
  signature: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  body: { e.symmₗ R b with
    cont := by
      by_cases hb : b in e.baseSet
      · rw [(FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff]
        refine .congr (f := TotalSpace.mk b ∘ e.symm b) ?_ (by simp [hb])
        exact e.continuousOn_symm.comp_continuous (.prodMk_right _) fun x =>
        

中文:
定义 symmL
  签名: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: { e.symmₗ R b with
    cont := by
      by_cases hb : b in e.baseSet
      · rw [(FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff]
        refine .congr (f := TotalSpace.mk b ∘ e.symm b) ?_ (by simp [hb])
        exact e.continuousOn_symm.comp_continuous (.prodMk_right _) fun x =>
        

Depends on / 依赖: FiberBundle, FiberBundle.totalSpaceMk_isInducing, TotalSpace, TotalSpace.mk, baseSet, comp_continuous, continuousOn_symm, continuous_iff, continuous_zero, continuous_zero.congr, e.baseSet, e.continuousOn_symm.comp_continuous, e.symm, mem_univ, mk_mem_prod, prodMk_right, totalSpaceMk_isInducing
-/
def symmL (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F ->L[R] E b :=
  { e.symmₗ R b with
    cont := by
      by_cases hb : b in e.baseSet
      · rw [(FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff]
        refine .congr (f := TotalSpace.mk b ∘ e.symm b) ?_ (by simp [hb])
        exact e.continuousOn_symm.comp_continuous (.prodMk_right _) fun x =>
          mk_mem_prod hb (mem_univ x)
      · exact continuous_zero.congr fun x => (e.symmₗ_apply_of_notMem hb x).symm }

variable {R}

@[simp]
/--
theorem `symmL_apply` / 定理 `symmL_apply`

English:
theorem symmL_apply
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  proof: e.toPretrivialization.symmₗ_apply R hb y

@[simp]

中文:
定理 symmL_apply
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
  证明: e.toPretrivialization.symmₗ_apply R hb y

@[simp]

Depends on / 依赖: e.toPretrivialization.symm, toPretrivialization
-/
theorem symmL_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet)
    (y : F) : e.symmL R b y = e.symm b y :=
  e.toPretrivialization.symmₗ_apply R hb y

@[simp]
/--
lemma `symmL_apply_of_notMem` / 引理 `symmL_apply_of_notMem`

English:
lemma symmL_apply_of_notMem
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: e.toPretrivialization.symmₗ_apply_of_notMem _ hb _

中文:
引理 symmL_apply_of_notMem
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: e.toPretrivialization.symmₗ_apply_of_notMem _ hb _

Depends on / 依赖: e.toPretrivialization.symm, toPretrivialization
-/
lemma symmL_apply_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmL R b y = 0 :=
  e.toPretrivialization.symmₗ_apply_of_notMem _ hb _

/--
theorem `symmL_continuousLinearMapAt` / 定理 `symmL_continuousLinearMapAt`

English:
theorem symmL_continuousLinearMapAt
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: e.symmₗ_linearMapAt hb y

中文:
定理 symmL_continuousLinearMapAt
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: e.symmₗ_linearMapAt hb y

Depends on / 依赖: e.symm
-/
theorem symmL_continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) (y : E b) : e.symmL R b (e.continuousLinearMapAt R b y) = y :=
  e.symmₗ_linearMapAt hb y

/--
theorem `continuousLinearMapAt_symmL` / 定理 `continuousLinearMapAt_symmL`

English:
theorem continuousLinearMapAt_symmL
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: e.linearMapAt_symmₗ hb y

中文:
定理 continuousLinearMapAt_symmL
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: e.linearMapAt_symmₗ hb y

Depends on / 依赖: e.linearMapAt_symm
-/
theorem continuousLinearMapAt_symmL (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) (y : F) : e.continuousLinearMapAt R b (e.symmL R b y) = y :=
  e.linearMapAt_symmₗ hb y

variable (R) in
/-- In a vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps -fullyApplied apply symm_apply]
/--
Definition of `continuousLinearEquivAt` / `continuousLinearEquivAt` 的定义

English:
definition continuousLinearEquivAt
  signature: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  body: { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun

中文:
定义 continuousLinearEquivAt
  签名: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  定义体: { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun

Depends on / 依赖: FiberBundle, FiberBundle.totalSpaceMk_isInducing, comp_continuous, continuous, continuousOn, continuous_invFun, continuous_toFun, convert, e.continuousOn.comp_continuous, e.mem_source.mpr, e.symm, e.symmL, e.toPretrivialization.linearEquivAt, explicitly, invFun, linearEquivAt, mem_source, toPretrivialization, totalSpaceMk_isInducing
-/
def continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b in e.baseSet) : E b ≃L[R] F :=
  { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun _ => e.mem_source.mpr hb).snd
    continuous_invFun := by convert (e.symmL R b).continuous; ext; simp [hb] }

/--
theorem `coe_continuousLinearEquivAt_eq` / 定理 `coe_continuousLinearEquivAt_eq`

English:
theorem coe_continuousLinearEquivAt_eq
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: (e.coe_linearMapAt_of_mem hb).symm

中文:
定理 coe_continuousLinearEquivAt_eq
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: (e.coe_linearMapAt_of_mem hb).symm

Depends on / 依赖: coe_linearMapAt_of_mem, e.coe_linearMapAt_of_mem
-/
theorem coe_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b -> F) = e.continuousLinearMapAt R b :=
  (e.coe_linearMapAt_of_mem hb).symm

/--
theorem `coe_continuousLinearEquivAt_eq'` / 定理 `coe_continuousLinearEquivAt_eq'`

English:
theorem coe_continuousLinearEquivAt_eq'
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: DFunLike.coe_injective (e.coe_linearMapAt_of_mem hb).symm

中文:
定理 coe_continuousLinearEquivAt_eq'
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: DFunLike.coe_injective (e.coe_linearMapAt_of_mem hb).symm

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, coe_linearMapAt_of_mem, e.coe_linearMapAt_of_mem
-/
theorem coe_continuousLinearEquivAt_eq' (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b ->L[R] F) = e.continuousLinearMapAt R b :=
  DFunLike.coe_injective (e.coe_linearMapAt_of_mem hb).symm

/--
theorem `symm_continuousLinearEquivAt_eq` / 定理 `symm_continuousLinearEquivAt_eq`

English:
theorem symm_continuousLinearEquivAt_eq
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by
  ext; simp [hb]

中文:
定理 symm_continuousLinearEquivAt_eq
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by
  ext; simp [hb]
-/
theorem symm_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) : ((e.continuousLinearEquivAt R b hb).symm : F -> E b) = e.symmL R b := by
  ext; simp [hb]

/--
theorem `symm_continuousLinearEquivAt_eq'` / 定理 `symm_continuousLinearEquivAt_eq'`

English:
theorem symm_continuousLinearEquivAt_eq'
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  proof: by
  ext; simp [hb]

@[simp]

中文:
定理 symm_continuousLinearEquivAt_eq'
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
  证明: by
  ext; simp [hb]

@[simp]
-/
theorem symm_continuousLinearEquivAt_eq' (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b in e.baseSet) :
    ((e.continuousLinearEquivAt R b hb).symm : F ->L[R] E b) = e.symmL R b := by
  ext; simp [hb]

@[simp]
/--
theorem `continuousLinearEquivAt_apply'` / 定理 `continuousLinearEquivAt_apply'`

English:
theorem continuousLinearEquivAt_apply'
  statement: (e : Trivialization F (π F E)) [e.IsLinear R]
  proof: rfl

中文:
定理 continuousLinearEquivAt_apply'
  结论: (e : Trivialization F (π F E)) [e.IsLinear R]
  证明: rfl
-/
theorem continuousLinearEquivAt_apply' (e : Trivialization F (π F E)) [e.IsLinear R]
    (x : TotalSpace F E) (hx : x in e.source) :
    e.continuousLinearEquivAt R x.proj (e.mem_source.1 hx) x.2 = (e x).2 := rfl

variable (R)

/--
theorem `apply_eq_prod_continuousLinearEquivAt` / 定理 `apply_eq_prod_continuousLinearEquivAt`

English:
theorem apply_eq_prod_continuousLinearEquivAt
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  proof: by
  ext
  · refine e.coe_fst ?_
    rw [e.source_eq]
    exact hb
  · simp only [continuousLinearEquivAt_apply]

中文:
定理 apply_eq_prod_continuousLinearEquivAt
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
  证明: by
  ext
  · refine e.coe_fst ?_
    rw [e.source_eq]
    exact hb
  · simp only [continuousLinearEquivAt_apply]

Depends on / 依赖: coe_fst, continuousLinearEquivAt_apply, e.coe_fst, e.source_eq, source_eq
-/
theorem apply_eq_prod_continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b in e.baseSet) (z : E b) : e ⟨b, z⟩ = (b, e.continuousLinearEquivAt R b hb z) := by
  ext
  · refine e.coe_fst ?_
    rw [e.source_eq]
    exact hb
  · simp only [continuousLinearEquivAt_apply]

/--
theorem `zeroSection` / 定理 `zeroSection`

English:
theorem zeroSection
  statement: (e : Trivialization F (π F E)) [e.IsLinear R] {x : B}
  proof: by
  simp_rw [zeroSection, e.apply_eq_prod_continuousLinearEquivAt R x hx 0, map_zero]

中文:
定理 zeroSection
  结论: (e : Trivialization F (π F E)) [e.IsLinear R] {x : B}
  证明: by
  simp_rw [zeroSection, e.apply_eq_prod_continuousLinearEquivAt R x hx 0, map_zero]
-/
protected theorem zeroSection (e : Trivialization F (π F E)) [e.IsLinear R] {x : B}
    (hx : x in e.baseSet) : e (zeroSection F E x) = (x, 0) := by
  simp_rw [zeroSection, e.apply_eq_prod_continuousLinearEquivAt R x hx 0, map_zero]

/--
theorem `continuous_zeroSection` / 定理 `continuous_zeroSection`

English:
theorem continuous_zeroSection
  given: [VectorBundle R F E]
  proof: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  unfold zeroSection
  rw [FiberBundle.continuousAt_section]
  apply (continuousAt_const (y := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using co

中文:
定理 continuous_zeroSection
  条件: [VectorBundle R F E]
  证明: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  unfold zeroSection
  rw [FiberBundle.continuousAt_section]
  apply (continuousAt_const (y := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using co

Depends on / 依赖: FiberBundle, FiberBundle.continuousAt_section, Prod.snd, congr_arg, congr_of_eventuallyEq, continuousAt_const, continuousAt_section, continuous_iff_continuousAt, filter_upwards, mem_baseSet_trivializationAt, mem_nhds, open_baseSet, open_baseSet.mem_nhds, trivializationAt, zeroSection
-/
theorem continuous_zeroSection [VectorBundle R F E] :
    Continuous (zeroSection F E) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  unfold zeroSection
  rw [FiberBundle.continuousAt_section]
  apply (continuousAt_const (y := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).zeroSection R hy

/--
theorem `continuousOn_zeroSection` / 定理 `continuousOn_zeroSection`

English:
theorem continuousOn_zeroSection
  given: [VectorBundle R F E] (s : Set B)
  proof: (continuous_zeroSection R).continuousOn

中文:
定理 continuousOn_zeroSection
  条件: [VectorBundle R F E] (s : Set B)
  证明: (continuous_zeroSection R).continuousOn

Depends on / 依赖: continuousOn, continuous_zeroSection
-/
theorem continuousOn_zeroSection [VectorBundle R F E] (s : Set B) :
    ContinuousOn (zeroSection F E) s :=
  (continuous_zeroSection R).continuousOn

/--
theorem `continuousAt_zeroSection` / 定理 `continuousAt_zeroSection`

English:
theorem continuousAt_zeroSection
  given: [VectorBundle R F E] (x : B)
  proof: (continuous_zeroSection R).continuousAt

中文:
定理 continuousAt_zeroSection
  条件: [VectorBundle R F E] (x : B)
  证明: (continuous_zeroSection R).continuousAt

Depends on / 依赖: continuousAt, continuous_zeroSection
-/
theorem continuousAt_zeroSection [VectorBundle R F E] (x : B) :
    ContinuousAt (zeroSection F E) x :=
  (continuous_zeroSection R).continuousAt

variable {R}

/--
theorem `symm_apply_eq_mk_continuousLinearEquivAt_symm` / 定理 `symm_apply_eq_mk_continuousLinearEquivAt_symm`

English:
theorem symm_apply_eq_mk_continuousLinearEquivAt_symm
  statement: (e : Trivialization F (π F E)) [e.IsLinear R]
  proof: by
  simpa using (mk_symm _ hb _).symm

中文:
定理 symm_apply_eq_mk_continuousLinearEquivAt_symm
  结论: (e : Trivialization F (π F E)) [e.IsLinear R]
  证明: by
  simpa using (mk_symm _ hb _).symm

Depends on / 依赖: mk_symm
-/
theorem symm_apply_eq_mk_continuousLinearEquivAt_symm (e : Trivialization F (π F E)) [e.IsLinear R]
    (b : B) (hb : b in e.baseSet) (z : F) :
    e.toOpenPartialHomeomorph.symm ⟨b, z⟩ = ⟨b, (e.continuousLinearEquivAt R b hb).symm z⟩ := by
  simpa using (mk_symm _ hb _).symm

/--
theorem `comp_continuousLinearEquivAt_eq_coord_change` / 定理 `comp_continuousLinearEquivAt_eq_coord_change`

English:
theorem comp_continuousLinearEquivAt_eq_coord_change
  statement: (e e' : Trivialization F (π F E))
  proof: by
  ext v
  rw [coordChangeL_apply e e' hb]
  rfl

中文:
定理 comp_continuousLinearEquivAt_eq_coord_change
  结论: (e e' : Trivialization F (π F E))
  证明: by
  ext v
  rw [coordChangeL_apply e e' hb]
  rfl

Depends on / 依赖: coordChangeL_apply
-/
theorem comp_continuousLinearEquivAt_eq_coord_change (e e' : Trivialization F (π F E))
    [e.IsLinear R] [e'.IsLinear R] {b : B} (hb : b in e.baseSet inter e'.baseSet) :
    (e.continuousLinearEquivAt R b hb.1).symm.trans (e'.continuousLinearEquivAt R b hb.2) =
      coordChangeL R e e' b := by
  ext v
  rw [coordChangeL_apply e e' hb]
  rfl

end Bundle.Trivialization

variable (F E) [VectorBundle R F E] in
/-- A continuous linear equivalence between the fiber at `b` and the model fiber,
induced by the preferred trivialisation at each `b`. -/
@[simps!]
/--
Definition of `VectorBundle.continuousLinearEquivAt` / `VectorBundle.continuousLinearEquivAt` 的定义

English:
definition VectorBundle.continuousLinearEquivAt
  signature: (b : B)
  body: (trivializationAt F E b).continuousLinearEquivAt R b (FiberBundle.mem_baseSet_trivializationAt' b)

中文:
定义 VectorBundle.continuousLinearEquivAt
  签名: (b : B)
  定义体: (trivializationAt F E b).continuousLinearEquivAt R b (FiberBundle.mem_baseSet_trivializationAt' b)

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, continuousLinearEquivAt, mem_baseSet_trivializationAt, trivializationAt
-/
noncomputable def VectorBundle.continuousLinearEquivAt (b : B) : E b ≃L[R] F :=
  (trivializationAt F E b).continuousLinearEquivAt R b (FiberBundle.mem_baseSet_trivializationAt' b)

/-! ### Constructing vector bundles -/

variable (B F)

/--
Definition of `VectorBundleCore` / `VectorBundleCore` 的定义

English:
structure VectorBundleCore
  parameters: (ι : Type*)
  axioms and operations (8):
    - baseSet : ι -> Set B
    - isOpen_baseSet : forall i, IsOpen (baseSet i)
    - indexAt : B -> ι
    - mem_baseSet_at : forall x, x in baseSet (indexAt x)
    - coordChange : ι -> ι -> B -> F ->L[R] F
    - coordChange_self : forall i, forall x in baseSet i, forall v, coordChange i i x v = v
    - continuousOn_coordChange : forall i j, ContinuousOn (coordChange i j) (baseSet i inter baseSet j)
    - coordChange_comp : forall i j k, forall x in baseSet i inter baseSet j inter baseSet k, forall v, (coordChange j k x) (coordChange i j x v) = coordChange i k x v

中文:
结构 VectorBundleCore
  参数: (ι : 类型)
  公理与运算 (8 个):
    - baseSet : ι -> Set B
    - isOpen_baseSet : 对任意 i, IsOpen (baseSet i)
    - indexAt : B -> ι
    - mem_baseSet_at : 对任意 x, x in baseSet (indexAt x)
    - coordChange : ι -> ι -> B -> F ->L[R] F
    - coordChange_self : 对任意 i, 对任意 x in baseSet i, 对任意 v, coordChange i i x v = v
    - continuousOn_coordChange : 对任意 i j, ContinuousOn (coordChange i j) (baseSet i inter baseSet j)
    - coordChange_comp : 对任意 i j k, 对任意 x in baseSet i inter baseSet j inter baseSet k, 对任意 v, (coordChange j k x) (coordChange i j x v) = coordChange i k x v
-/
structure VectorBundleCore (ι : Type*) where
  baseSet : ι -> Set B
  isOpen_baseSet : forall i, IsOpen (baseSet i)
  indexAt : B -> ι
  mem_baseSet_at : forall x, x in baseSet (indexAt x)
  coordChange : ι -> ι -> B -> F ->L[R] F
  coordChange_self : forall i, forall x in baseSet i, forall v, coordChange i i x v = v
  continuousOn_coordChange : forall i j, ContinuousOn (coordChange i j) (baseSet i inter baseSet j)
  coordChange_comp : forall i j k, forall x in baseSet i inter baseSet j inter baseSet k, forall v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v

/--
Definition of `trivialVectorBundleCore` / `trivialVectorBundleCore` 的定义

English:
definition trivialVectorBundleCore
  signature: (ι : Type*) [Inhabited ι]
  body: univ
  isOpen_baseSet _ := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange _ _ _ := ContinuousLinearMap.id R F
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const

中文:
定义 trivialVectorBundleCore
  签名: (ι : 类型) [Inhabited ι]
  定义体: univ
  isOpen_baseSet _ := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange _ _ _ := ContinuousLinearMap.id R F
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const
-/
def trivialVectorBundleCore (ι : Type*) [Inhabited ι] : VectorBundleCore R B F ι where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange _ _ _ := ContinuousLinearMap.id R F
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const

instance (ι : Type*) [Inhabited ι] : Inhabited (VectorBundleCore R B F ι) :=
  ⟨trivialVectorBundleCore R B F ι⟩

namespace VectorBundleCore

variable {R B F} {ι : Type*}
variable (Z : VectorBundleCore R B F ι)

/-- Natural identification to a `FiberBundleCore`. -/
@[simps (attr := mfld_simps) -fullyApplied]
/--
Definition of `toFiberBundleCore` / `toFiberBundleCore` 的定义

English:
definition toFiberBundleCore
  signature: : FiberBundleCore ι B F
  body: { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).prodMap continuousOn_id) }

中文:
定义 toFiberBundleCore
  签名: : FiberBundleCore ι B F
  定义体: { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).prodMap continuousOn_id) }

Depends on / 依赖: Z.continuousOn_coordChange, Z.coordChange, comp_continuousOn, continuous, continuousOn_coordChange, continuousOn_id, coordChange, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.continuous.comp_continuousOn, prodMap
-/
def toFiberBundleCore : FiberBundleCore ι B F :=
  { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).prodMap continuousOn_id) }

-- TODO: restore coercion?
-- instance toFiberBundleCoreCoe : Coe (VectorBundleCore R B F ι) (FiberBundleCore ι B F) :=
-- ⟨toFiberBundleCore⟩

/--
theorem `coordChange_linear_comp` / 定理 `coordChange_linear_comp`

English:
theorem coordChange_linear_comp
  given: (i j k : ι)
  proof: fun x hx => by
  ext v
  exact Z.coordChange_comp i j k x hx v

中文:
定理 coordChange_linear_comp
  条件: (i j k : ι)
  证明: fun x hx => by
  ext v
  exact Z.coordChange_comp i j k x hx v

Depends on / 依赖: Z.coordChange_comp, coordChange_comp
-/
theorem coordChange_linear_comp (i j k : ι) :
    forall x in Z.baseSet i inter Z.baseSet j inter Z.baseSet k,
      (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
  fun x hx => by
  ext v
  exact Z.coordChange_comp i j k x hx v

/-- The index set of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments]
/--
Definition of `Index` / `Index` 的定义

English:
definition Index
  body: ι

中文:
定义 Index
  定义体: ι
-/
def Index := ι

/-- The base space of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
/--
Definition of `Base` / `Base` 的定义

English:
definition Base
  body: B

中文:
定义 Base
  定义体: B
-/
def Base := B

/-- The fiber of a vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unusedArguments]
/--
Definition of `Fiber` / `Fiber` 的定义

English:
definition Fiber
  signature: : B -> Type _
  body: Z.toFiberBundleCore.Fiber

中文:
定义 Fiber
  签名: : B -> Type _
  定义体: Z.toFiberBundleCore.Fiber

Depends on / 依赖: Z.toFiberBundleCore.Fiber, toFiberBundleCore
-/
def Fiber : B -> Type _ :=
  Z.toFiberBundleCore.Fiber

/--
Instance `topologicalSpaceFiber` / 实例 `topologicalSpaceFiber`

English:
instance topologicalSpaceFiber
  signature: (x : B)
  body: letI : TopologicalSpace (Z.toFiberBundleCore.Fiber x) :=
    Z.toFiberBundleCore.topologicalSpaceFiber x
inferInstanceAs TopologicalSpace (Z.toFiberBundleCore.Fiber x)

中文:
实例 topologicalSpaceFiber
  签名: (x : B)
  定义体: letI : TopologicalSpace (Z.toFiberBundleCore.Fiber x) :=
    Z.toFiberBundleCore.topologicalSpaceFiber x
inferInstanceAs TopologicalSpace (Z.toFiberBundleCore.Fiber x)

Depends on / 依赖: TopologicalSpace, Z.toFiberBundleCore.Fiber, Z.toFiberBundleCore.topologicalSpaceFiber, toFiberBundleCore, topologicalSpaceFiber
-/
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) :=
  letI : TopologicalSpace (Z.toFiberBundleCore.Fiber x) :=
    Z.toFiberBundleCore.topologicalSpaceFiber x
inferInstanceAs TopologicalSpace (Z.toFiberBundleCore.Fiber x)

/--
Instance `addCommGroupFiber` / 实例 `addCommGroupFiber`

English:
instance addCommGroupFiber
  signature: (x : B)
  body: inferInstanceAs AddCommGroup F

中文:
实例 addCommGroupFiber
  签名: (x : B)
  定义体: inferInstanceAs AddCommGroup F

Depends on / 依赖: AddCommGroup
-/
instance addCommGroupFiber (x : B) : AddCommGroup (Z.Fiber x) :=
inferInstanceAs AddCommGroup F

/--
Instance `moduleFiber` / 实例 `moduleFiber`

English:
instance moduleFiber
  signature: (x : B)
  body: inferInstanceAs Module R F

中文:
实例 moduleFiber
  签名: (x : B)
  定义体: inferInstanceAs Module R F

Depends on / 依赖: Module
-/
instance moduleFiber (x : B) : Module R (Z.Fiber x) :=
inferInstanceAs Module R F

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: : TotalSpace F Z.Fiber -> B
  body: TotalSpace.proj

中文:
定义 proj
  签名: : TotalSpace F Z.Fiber -> B
  定义体: TotalSpace.proj
-/
protected def proj : TotalSpace F Z.Fiber -> B :=
  TotalSpace.proj

/-- The total space of the vector bundle, as a convenience function for dot notation.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`. -/
@[nolint unusedArguments, reducible]
/--
Definition of `TotalSpace` / `TotalSpace` 的定义

English:
definition TotalSpace
  body: Bundle.TotalSpace F Z.Fiber

中文:
定义 TotalSpace
  定义体: Bundle.TotalSpace F Z.Fiber
-/
protected def TotalSpace :=
  Bundle.TotalSpace F Z.Fiber

/--
Definition of `trivChange` / `trivChange` 的定义

English:
definition trivChange
  signature: (i j : ι)
  body: Z.toFiberBundleCore.trivChange i j

@[simp, mfld_simps]

中文:
定义 trivChange
  签名: (i j : ι)
  定义体: Z.toFiberBundleCore.trivChange i j

@[simp, mfld_simps]

Depends on / 依赖: Z.toFiberBundleCore.trivChange, toFiberBundleCore, trivChange
-/
def trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) :=
  Z.toFiberBundleCore.trivChange i j

@[simp, mfld_simps]
/--
theorem `mem_trivChange_source` / 定理 `mem_trivChange_source`

English:
theorem mem_trivChange_source
  given: (i j : ι) (p : B × F)
  proof: Z.toFiberBundleCore.mem_trivChange_source i j p

中文:
定理 mem_trivChange_source
  条件: (i j : ι) (p : B × F)
  证明: Z.toFiberBundleCore.mem_trivChange_source i j p

Depends on / 依赖: Z.toFiberBundleCore.mem_trivChange_source, mem_trivChange_source, toFiberBundleCore
-/
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p in (Z.trivChange i j).source ↔ p.1 in Z.baseSet i inter Z.baseSet j :=
  Z.toFiberBundleCore.mem_trivChange_source i j p

/--
Instance `toTopologicalSpace` / 实例 `toTopologicalSpace`

English:
instance toTopologicalSpace
  signature: : TopologicalSpace Z.TotalSpace
  body: fast_instance% Z.toFiberBundleCore.toTopologicalSpace

中文:
实例 toTopologicalSpace
  签名: : TopologicalSpace Z.TotalSpace
  定义体: fast_instance% Z.toFiberBundleCore.toTopologicalSpace

Depends on / 依赖: Z.toFiberBundleCore.toTopologicalSpace, fast_instance, toFiberBundleCore, toTopologicalSpace
-/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  fast_instance% Z.toFiberBundleCore.toTopologicalSpace

variable (b : B) (a : F)

@[simp, mfld_simps]
/--
theorem `coe_coordChange` / 定理 `coe_coordChange`

English:
theorem coe_coordChange
  given: (i j : ι)
  statement: Z.toFiberBundleCore.coordChange i j b = Z.coordChange i j b
  proof: rfl

中文:
定理 coe_coordChange
  条件: (i j : ι)
  结论: Z.toFiberBundleCore.coordChange i j b = Z.coordChange i j b
  证明: rfl
-/
theorem coe_coordChange (i j : ι) : Z.toFiberBundleCore.coordChange i j b = Z.coordChange i j b :=
  rfl

/--
Definition of `localTriv` / `localTriv` 的定义

English:
definition localTriv
  signature: (i : ι)
  body: Z.toFiberBundleCore.localTriv i

@[simp, mfld_simps]

中文:
定义 localTriv
  签名: (i : ι)
  定义体: Z.toFiberBundleCore.localTriv i

@[simp, mfld_simps]

Depends on / 依赖: Z.toFiberBundleCore.localTriv, localTriv, toFiberBundleCore
-/
def localTriv (i : ι) : Trivialization F (π F Z.Fiber) :=
  Z.toFiberBundleCore.localTriv i

@[simp, mfld_simps]
/--
theorem `localTriv_apply` / 定理 `localTriv_apply`

English:
theorem localTriv_apply
  given: {i : ι} (p : Z.TotalSpace)
  proof: rfl

中文:
定理 localTriv_apply
  条件: {i : ι} (p : Z.TotalSpace)
  证明: rfl
-/
theorem localTriv_apply {i : ι} (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `localTriv.isLinear` / 实例 `localTriv.isLinear`

English:
instance localTriv.isLinear
  signature: (i : ι)
  body: { map_add := fun _ _ => by simp only [map_add, localTriv_apply, mfld_simps]
      map_smul := fun _ _ => by simp only [map_smul, localTriv_apply, mfld_simps] }

中文:
实例 localTriv.isLinear
  签名: (i : ι)
  定义体: { map_add := fun _ _ => by simp only [map_add, localTriv_apply, mfld_simps]
      map_smul := fun _ _ => by simp only [map_smul, localTriv_apply, mfld_simps] }

Depends on / 依赖: localTriv_apply, map_add, map_smul, mfld_simps
-/
instance localTriv.isLinear (i : ι) : (Z.localTriv i).IsLinear R where
  linear x _ :=
    { map_add := fun _ _ => by simp only [map_add, localTriv_apply, mfld_simps]
      map_smul := fun _ _ => by simp only [map_smul, localTriv_apply, mfld_simps] }

variable (i j : ι)

@[simp, mfld_simps]
/--
theorem `mem_localTriv_source` / 定理 `mem_localTriv_source`

English:
theorem mem_localTriv_source
  given: (p : Z.TotalSpace)
  statement: p in (Z.localTriv i).source ↔ p.1 in Z.baseSet i
  proof: Iff.rfl

@[simp, mfld_simps]

中文:
定理 mem_localTriv_source
  条件: (p : Z.TotalSpace)
  结论: p in (Z.localTriv i).source ↔ p.1 in Z.baseSet i
  证明: Iff.rfl

@[simp, mfld_simps]

Depends on / 依赖: Iff.rfl
-/
theorem mem_localTriv_source (p : Z.TotalSpace) : p in (Z.localTriv i).source ↔ p.1 in Z.baseSet i :=
  Iff.rfl

@[simp, mfld_simps]
/--
theorem `baseSet_at` / 定理 `baseSet_at`

English:
theorem baseSet_at
  statement: Z.baseSet i = (Z.localTriv i).baseSet
  proof: rfl

@[simp, mfld_simps]

中文:
定理 baseSet_at
  结论: Z.baseSet i = (Z.localTriv i).baseSet
  证明: rfl

@[simp, mfld_simps]
-/
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl

@[simp, mfld_simps]
/--
theorem `mem_localTriv_target` / 定理 `mem_localTriv_target`

English:
theorem mem_localTriv_target
  given: (p : B × F)
  proof: Z.toFiberBundleCore.mem_localTriv_target i p

@[simp, mfld_simps]

中文:
定理 mem_localTriv_target
  条件: (p : B × F)
  证明: Z.toFiberBundleCore.mem_localTriv_target i p

@[simp, mfld_simps]

Depends on / 依赖: Z.toFiberBundleCore.mem_localTriv_target, mem_localTriv_target, toFiberBundleCore
-/
theorem mem_localTriv_target (p : B × F) :
    p in (Z.localTriv i).target ↔ p.1 in (Z.localTriv i).baseSet :=
  Z.toFiberBundleCore.mem_localTriv_target i p

@[simp, mfld_simps]
/--
theorem `localTriv_symm_fst` / 定理 `localTriv_symm_fst`

English:
theorem localTriv_symm_fst
  given: (p : B × F)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTriv_symm_fst
  条件: (p : B × F)
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTriv_symm_fst (p : B × F) :
    (Z.localTriv i).toOpenPartialHomeomorph.symm p =
      ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
/--
theorem `localTriv_symm_apply` / 定理 `localTriv_symm_apply`

English:
theorem localTriv_symm_apply
  given: {b : B} (hb : b in (Z.localTriv i).baseSet) (v : F)
  proof: by
  apply (Z.localTriv i).symm_apply hb v

@[simp, mfld_simps]

中文:
定理 localTriv_symm_apply
  条件: {b : B} (hb : b in (Z.localTriv i).baseSet) (v : F)
  证明: by
  apply (Z.localTriv i).symm_apply hb v

@[simp, mfld_simps]

Depends on / 依赖: Z.localTriv, localTriv, symm_apply
-/
theorem localTriv_symm_apply {b : B} (hb : b in (Z.localTriv i).baseSet) (v : F) :
    (Z.localTriv i).symm b v = Z.coordChange i (Z.indexAt b) b v := by
  apply (Z.localTriv i).symm_apply hb v

@[simp, mfld_simps]
/--
theorem `localTriv_coordChange_eq` / 定理 `localTriv_coordChange_eq`

English:
theorem localTriv_coordChange_eq
  statement: {b : B}
  proof: by
  rw [Trivialization.coordChangeL_apply']; rw [localTriv_symm_fst]; rw [localTriv_apply]; rw [coordChange_comp]
  exacts [⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩, hb]

中文:
定理 localTriv_coordChange_eq
  结论: {b : B}
  证明: by
  rw [Trivialization.coordChangeL_apply']; rw [localTriv_symm_fst]; rw [localTriv_apply]; rw [coordChange_comp]
  exacts [⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩, hb]

Depends on / 依赖: Trivialization, Trivialization.coordChangeL_apply, Z.mem_baseSet_at, coordChangeL_apply, coordChange_comp, exacts, localTriv_apply, localTriv_symm_fst, mem_baseSet_at
-/
theorem localTriv_coordChange_eq {b : B}
    (hb : b in (Z.localTriv i).baseSet ∧ b in (Z.localTriv j).baseSet) (v : F) :
    (Z.localTriv i).coordChangeL R (Z.localTriv j) b v = Z.coordChange i j b v := by
  rw [Trivialization.coordChangeL_apply']; rw [localTriv_symm_fst]; rw [localTriv_apply]; rw [coordChange_comp]
  exacts [⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩, hb]

/--
Definition of `localTrivAt` / `localTrivAt` 的定义

English:
definition localTrivAt
  signature: (b : B)
  body: Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]

中文:
定义 localTrivAt
  签名: (b : B)
  定义体: Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]

Depends on / 依赖: Z.indexAt, Z.localTriv, indexAt, localTriv
-/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
/--
theorem `localTrivAt_def` / 定理 `localTrivAt_def`

English:
theorem localTrivAt_def
  statement: Z.localTriv (Z.indexAt b) = Z.localTrivAt b
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTrivAt_def
  结论: Z.localTriv (Z.indexAt b) = Z.localTrivAt b
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTrivAt_def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

@[simp, mfld_simps]
/--
theorem `mem_source_at` / 定理 `mem_source_at`

English:
theorem mem_source_at
  statement: (⟨b, a⟩ : Z.TotalSpace) in (Z.localTrivAt b).source
  proof: by
  rw [localTrivAt]; rw [mem_localTriv_source]
  exact Z.mem_baseSet_at b

@[simp, mfld_simps]

中文:
定理 mem_source_at
  结论: (⟨b, a⟩ : Z.TotalSpace) in (Z.localTrivAt b).source
  证明: by
  rw [localTrivAt]; rw [mem_localTriv_source]
  exact Z.mem_baseSet_at b

@[simp, mfld_simps]

Depends on / 依赖: Z.mem_baseSet_at, localTrivAt, mem_baseSet_at, mem_localTriv_source
-/
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) in (Z.localTrivAt b).source := by
  rw [localTrivAt]; rw [mem_localTriv_source]
  exact Z.mem_baseSet_at b

@[simp, mfld_simps]
/--
theorem `localTrivAt_apply` / 定理 `localTrivAt_apply`

English:
theorem localTrivAt_apply
  given: (p : Z.TotalSpace)
  statement: Z.localTrivAt p.1 p = ⟨p.1, p.2⟩
  proof: Z.toFiberBundleCore.localTrivAt_apply p

@[simp, mfld_simps]

中文:
定理 localTrivAt_apply
  条件: (p : Z.TotalSpace)
  结论: Z.localTrivAt p.1 p = ⟨p.1, p.2⟩
  证明: Z.toFiberBundleCore.localTrivAt_apply p

@[simp, mfld_simps]

Depends on / 依赖: Z.toFiberBundleCore.localTrivAt_apply, localTrivAt_apply, toFiberBundleCore
-/
theorem localTrivAt_apply (p : Z.TotalSpace) : Z.localTrivAt p.1 p = ⟨p.1, p.2⟩ :=
  Z.toFiberBundleCore.localTrivAt_apply p

@[simp, mfld_simps]
/--
theorem `localTrivAt_apply_mk` / 定理 `localTrivAt_apply_mk`

English:
theorem localTrivAt_apply_mk
  given: (b : B) (a : F)
  statement: Z.localTrivAt b ⟨b, a⟩ = ⟨b, a⟩
  proof: Z.localTrivAt_apply _

@[simp, mfld_simps]

中文:
定理 localTrivAt_apply_mk
  条件: (b : B) (a : F)
  结论: Z.localTrivAt b ⟨b, a⟩ = ⟨b, a⟩
  证明: Z.localTrivAt_apply _

@[simp, mfld_simps]

Depends on / 依赖: Z.localTrivAt_apply, localTrivAt_apply
-/
theorem localTrivAt_apply_mk (b : B) (a : F) : Z.localTrivAt b ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _

@[simp, mfld_simps]
/--
theorem `mem_localTrivAt_baseSet` / 定理 `mem_localTrivAt_baseSet`

English:
theorem mem_localTrivAt_baseSet
  statement: b in (Z.localTrivAt b).baseSet
  proof: Z.toFiberBundleCore.mem_localTrivAt_baseSet b

中文:
定理 mem_localTrivAt_baseSet
  结论: b in (Z.localTrivAt b).baseSet
  证明: Z.toFiberBundleCore.mem_localTrivAt_baseSet b

Depends on / 依赖: Z.toFiberBundleCore.mem_localTrivAt_baseSet, mem_localTrivAt_baseSet, toFiberBundleCore
-/
theorem mem_localTrivAt_baseSet : b in (Z.localTrivAt b).baseSet :=
  Z.toFiberBundleCore.mem_localTrivAt_baseSet b

/--
Instance `fiberBundle` / 实例 `fiberBundle`

English:
instance fiberBundle
  signature: : FiberBundle F Z.Fiber
  body: fast_instance% Z.toFiberBundleCore.fiberBundle

中文:
实例 fiberBundle
  签名: : FiberBundle F Z.Fiber
  定义体: fast_instance% Z.toFiberBundleCore.fiberBundle

Depends on / 依赖: Z.toFiberBundleCore.fiberBundle, fast_instance, fiberBundle, toFiberBundleCore
-/
instance fiberBundle : FiberBundle F Z.Fiber :=
  fast_instance% Z.toFiberBundleCore.fiberBundle

/--
lemma `trivializationAt` / 引理 `trivializationAt`

English:
lemma trivializationAt
  statement: trivializationAt F Z.Fiber b = Z.localTrivAt b
  proof: rfl

中文:
引理 trivializationAt
  结论: trivializationAt F Z.Fiber b = Z.localTrivAt b
  证明: rfl
-/
protected lemma trivializationAt : trivializationAt F Z.Fiber b = Z.localTrivAt b := rfl

/--
Instance `vectorBundle` / 实例 `vectorBundle`

English:
instance vectorBundle
  signature: : VectorBundle R F Z.Fiber where
  body: by
    rintro _ ⟨i, rfl⟩
    apply localTriv.isLinear
  continuousOn_coordChange' := by
    rintro _ _ ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.continuousOn_coordChange i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

中文:
实例 vectorBundle
  签名: : VectorBundle R F Z.Fiber where
  定义体: by
    rintro _ ⟨i, rfl⟩
    apply localTriv.isLinear
  continuousOn_coordChange' := by
    rintro _ _ ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.continuousOn_coordChange i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

Depends on / 依赖: Z.continuousOn_coordChange, Z.localTriv_coordChange_eq, continuousOn_coordChange, isLinear, localTriv, localTriv.isLinear, localTriv_coordChange_eq
-/
instance vectorBundle : VectorBundle R F Z.Fiber where
  trivialization_linear' := by
    rintro _ ⟨i, rfl⟩
    apply localTriv.isLinear
  continuousOn_coordChange' := by
    rintro _ _ ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.continuousOn_coordChange i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

/-- The projection on the base of a vector bundle created from core is continuous -/
@[continuity]
/--
theorem `continuous_proj` / 定理 `continuous_proj`

English:
theorem continuous_proj
  statement: Continuous Z.proj
  proof: Z.toFiberBundleCore.continuous_proj

中文:
定理 continuous_proj
  结论: Continuous Z.proj
  证明: Z.toFiberBundleCore.continuous_proj

Depends on / 依赖: Z.toFiberBundleCore.continuous_proj, continuous_proj, toFiberBundleCore
-/
theorem continuous_proj : Continuous Z.proj :=
  Z.toFiberBundleCore.continuous_proj

/--
theorem `isOpenMap_proj` / 定理 `isOpenMap_proj`

English:
theorem isOpenMap_proj
  statement: IsOpenMap Z.proj
  proof: Z.toFiberBundleCore.isOpenMap_proj

中文:
定理 isOpenMap_proj
  结论: IsOpenMap Z.proj
  证明: Z.toFiberBundleCore.isOpenMap_proj

Depends on / 依赖: Z.toFiberBundleCore.isOpenMap_proj, isOpenMap_proj, toFiberBundleCore
-/
theorem isOpenMap_proj : IsOpenMap Z.proj :=
  Z.toFiberBundleCore.isOpenMap_proj

variable {i j}

@[simp, mfld_simps]
/--
theorem `localTriv_continuousLinearMapAt` / 定理 `localTriv_continuousLinearMapAt`

English:
theorem localTriv_continuousLinearMapAt
  given: {b : B} (hb : b in (Z.localTriv i).baseSet)
  proof: by
  ext1 v
  simp_all
  rfl

@[simp, mfld_simps]

中文:
定理 localTriv_continuousLinearMapAt
  条件: {b : B} (hb : b in (Z.localTriv i).baseSet)
  证明: by
  ext1 v
  simp_all
  rfl

@[simp, mfld_simps]
-/
theorem localTriv_continuousLinearMapAt {b : B} (hb : b in (Z.localTriv i).baseSet) :
    (Z.localTriv i).continuousLinearMapAt R b = Z.coordChange (Z.indexAt b) i b := by
  ext1 v
  simp_all
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_continuousLinearMapAt` / 定理 `trivializationAt_continuousLinearMapAt`

English:
theorem trivializationAt_continuousLinearMapAt
  statement: {b₀ b : B}
  proof: Z.localTriv_continuousLinearMapAt hb

@[simp, mfld_simps]

中文:
定理 trivializationAt_continuousLinearMapAt
  结论: {b₀ b : B}
  证明: Z.localTriv_continuousLinearMapAt hb

@[simp, mfld_simps]

Depends on / 依赖: Z.localTriv_continuousLinearMapAt, localTriv_continuousLinearMapAt
-/
theorem trivializationAt_continuousLinearMapAt {b₀ b : B}
    (hb : b in (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).continuousLinearMapAt R b =
      Z.coordChange (Z.indexAt b) (Z.indexAt b₀) b :=
  Z.localTriv_continuousLinearMapAt hb

@[simp, mfld_simps]
/--
theorem `localTriv_symmL` / 定理 `localTriv_symmL`

English:
theorem localTriv_symmL
  given: {b : B} (hb : b in (Z.localTriv i).baseSet)
  proof: by
  ext1 v
  rw [(Z.localTriv i).symmL_apply hb]; rw [(Z.localTriv i).symm_apply]
  exacts [rfl, hb]

@[simp, mfld_simps]

中文:
定理 localTriv_symmL
  条件: {b : B} (hb : b in (Z.localTriv i).baseSet)
  证明: by
  ext1 v
  rw [(Z.localTriv i).symmL_apply hb]; rw [(Z.localTriv i).symm_apply]
  exacts [rfl, hb]

@[simp, mfld_simps]

Depends on / 依赖: Z.localTriv, exacts, localTriv, symmL_apply, symm_apply
-/
theorem localTriv_symmL {b : B} (hb : b in (Z.localTriv i).baseSet) :
    (Z.localTriv i).symmL R b = Z.coordChange i (Z.indexAt b) b := by
  ext1 v
  rw [(Z.localTriv i).symmL_apply hb]; rw [(Z.localTriv i).symm_apply]
  exacts [rfl, hb]

@[simp, mfld_simps]
/--
theorem `trivializationAt_symmL` / 定理 `trivializationAt_symmL`

English:
theorem trivializationAt_symmL
  given: {b₀ b : B} (hb : b in (trivializationAt F Z.Fiber b₀).baseSet)
  proof: Z.localTriv_symmL hb

@[simp, mfld_simps]

中文:
定理 trivializationAt_symmL
  条件: {b₀ b : B} (hb : b in (trivializationAt F Z.Fiber b₀).baseSet)
  证明: Z.localTriv_symmL hb

@[simp, mfld_simps]

Depends on / 依赖: Z.localTriv_symmL, localTriv_symmL
-/
theorem trivializationAt_symmL {b₀ b : B} (hb : b in (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).symmL R b = Z.coordChange (Z.indexAt b₀) (Z.indexAt b) b :=
  Z.localTriv_symmL hb

@[simp, mfld_simps]
/--
theorem `trivializationAt_coordChange_eq` / 定理 `trivializationAt_coordChange_eq`

English:
theorem trivializationAt_coordChange_eq
  statement: {b₀ b₁ b : B}
  proof: Z.localTriv_coordChange_eq _ _ hb v

中文:
定理 trivializationAt_coordChange_eq
  结论: {b₀ b₁ b : B}
  证明: Z.localTriv_coordChange_eq _ _ hb v

Depends on / 依赖: Z.localTriv_coordChange_eq, localTriv_coordChange_eq
-/
theorem trivializationAt_coordChange_eq {b₀ b₁ b : B}
    (hb : b in (trivializationAt F Z.Fiber b₀).baseSet inter (trivializationAt F Z.Fiber b₁).baseSet)
    (v : F) :
    (trivializationAt F Z.Fiber b₀).coordChangeL R (trivializationAt F Z.Fiber b₁) b v =
      Z.coordChange (Z.indexAt b₀) (Z.indexAt b₁) b v :=
  Z.localTriv_coordChange_eq _ _ hb v

end VectorBundleCore

end

/-! ### Vector prebundle -/

section

variable [NontriviallyNormedField R] [forall x, AddCommMonoid (E x)] [forall x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [forall x, TopologicalSpace (E x)]

open TopologicalSpace

open VectorBundle

/--
Definition of `VectorPrebundle` / `VectorPrebundle` 的定义

English:
structure VectorPrebundle
  parameters: where
  axioms and operations (7):
    - pretrivializationAtlas : Set (Pretrivialization F (π F E))
    - pretrivialization_linear' : forall e, e in pretrivializationAtlas -> e.IsLinear R
    - pretrivializationAt : B -> Pretrivialization F (π F E)
    - mem_base_pretrivializationAt : forall x : B, x in (pretrivializationAt x).baseSet
    - pretrivialization_mem_atlas : forall x : B, pretrivializationAt x in pretrivializationAtlas
    - exists_coordChange : forallᵉ (e in pretrivializationAtlas) (e' in pretrivializationAtlas), exists f : B -> F ->L[R] F, ContinuousOn f (e.baseSet inter e'.baseSet) ∧ forallᵉ (b in e.baseSet inter e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
    - totalSpaceMk_isInducing : forall b : B, IsInducing (pretrivializationAt b ∘ .mk b)

中文:
结构 VectorPrebundle
  参数: where
  公理与运算 (7 个):
    - pretrivializationAtlas : Set (Pretrivialization F (π F E))
    - pretrivialization_linear' : 对任意 e, e in pretrivializationAtlas -> e.IsLinear R
    - pretrivializationAt : B -> Pretrivialization F (π F E)
    - mem_base_pretrivializationAt : 对任意 x : B, x in (pretrivializationAt x).baseSet
    - pretrivialization_mem_atlas : 对任意 x : B, pretrivializationAt x in pretrivializationAtlas
    - exists_coordChange : 对任意ᵉ (e in pretrivializationAtlas) (e' in pretrivializationAtlas), 存在 f : B -> F ->L[R] F, ContinuousOn f (e.baseSet inter e'.baseSet) ∧ 对任意ᵉ (b in e.baseSet inter e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
    - totalSpaceMk_isInducing : 对任意 b : B, IsInducing (pretrivializationAt b ∘ .mk b)
-/
structure VectorPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivialization_linear' : forall e, e in pretrivializationAtlas -> e.IsLinear R
  pretrivializationAt : B -> Pretrivialization F (π F E)
  mem_base_pretrivializationAt : forall x : B, x in (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : forall x : B, pretrivializationAt x in pretrivializationAtlas
  exists_coordChange : forallᵉ (e in pretrivializationAtlas) (e' in pretrivializationAtlas),
    exists f : B -> F ->L[R] F, ContinuousOn f (e.baseSet inter e'.baseSet) ∧
      forallᵉ (b in e.baseSet inter e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
  totalSpaceMk_isInducing : forall b : B, IsInducing (pretrivializationAt b ∘ .mk b)

namespace VectorPrebundle

variable {R E F}

/--
Definition of `coordChange` / `coordChange` 的定义

English:
definition coordChange
  signature: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  body: Classical.choose (a.exists_coordChange e he e' he') b

中文:
定义 coordChange
  签名: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  定义体: Classical.choose (a.exists_coordChange e he e' he') b

Depends on / 依赖: Classical, Classical.choose, a.exists_coordChange, exists_coordChange
-/
def coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivializationAtlas) (b : B) : F ->L[R] F :=
  Classical.choose (a.exists_coordChange e he e' he') b

/--
theorem `continuousOn_coordChange` / 定理 `continuousOn_coordChange`

English:
theorem continuousOn_coordChange
  statement: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  proof: (Classical.choose_spec (a.exists_coordChange e he e' he')).1

中文:
定理 continuousOn_coordChange
  结论: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  证明: (Classical.choose_spec (a.exists_coordChange e he e' he')).1

Depends on / 依赖: Classical, Classical.choose_spec, a.exists_coordChange, choose_spec, exists_coordChange
-/
theorem continuousOn_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivializationAtlas) :
    ContinuousOn (a.coordChange he he') (e.baseSet inter e'.baseSet) :=
  (Classical.choose_spec (a.exists_coordChange e he e' he')).1

/--
theorem `coordChange_apply` / 定理 `coordChange_apply`

English:
theorem coordChange_apply
  statement: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  proof: (Classical.choose_spec (a.exists_coordChange e he e' he')).2 b hb v

中文:
定理 coordChange_apply
  结论: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  证明: (Classical.choose_spec (a.exists_coordChange e he e' he')).2 b hb v

Depends on / 依赖: Classical, Classical.choose_spec, a.exists_coordChange, choose_spec, exists_coordChange
-/
theorem coordChange_apply (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivializationAtlas) {b : B}
    (hb : b in e.baseSet inter e'.baseSet) (v : F) :
    a.coordChange he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (a.exists_coordChange e he e' he')).2 b hb v

/--
theorem `mk_coordChange` / 定理 `mk_coordChange`

English:
theorem mk_coordChange
  statement: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  proof: by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact a.coordChange_apply he he' hb v

中文:
定理 mk_coordChange
  结论: (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
  证明: by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact a.coordChange_apply he he' hb v

Depends on / 依赖: a.coordChange_apply, coe_fst, coordChange_apply, e.mk_symm, e.proj_symm_apply, mk_symm, proj_symm_apply
-/
theorem mk_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivializationAtlas) {b : B}
    (hb : b in e.baseSet inter e'.baseSet) (v : F) :
    (b, a.coordChange he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact a.coordChange_apply he he' hb v

/--
Definition of `toFiberPrebundle` / `toFiberPrebundle` 的定义

English:
definition toFiberPrebundle
  signature: (a : VectorPrebundle R F E)
  body: { a with
    continuous_trivChange := fun e he e' he' => by
      have : ContinuousOn (fun x : B × F => a.coordChange he' he x.1 x.2)
          ((e'.baseSet inter e.baseSet) ×ˢ univ) :=
        isBoundedBilinearMap_apply.continuous.comp_continuousOn
          ((a.continuousOn_coordChange he' he).pro

中文:
定义 toFiberPrebundle
  签名: (a : VectorPrebundle R F E)
  定义体: { a with
    continuous_trivChange := fun e he e' he' => by
      have : ContinuousOn (fun x : B × F => a.coordChange he' he x.1 x.2)
          ((e'.baseSet inter e.baseSet) ×ˢ univ) :=
        isBoundedBilinearMap_apply.continuous.comp_continuousOn
          ((a.continuousOn_coordChange he' he).pro

Depends on / 依赖: ContinuousOn, Function, Function.comp_def, Prod.map, a.continuousOn_coordChange, a.coordChange, a.mk_coordChange, baseSet, comp_continuousOn, comp_def, continuous, continuousOn_coordChange, continuousOn_fst, continuousOn_fst.prodMk, continuousOn_id, continuous_trivChange, coordChange, e.baseSet, e.target_inter_preimage_symm_source_eq, inter_comm
-/
def toFiberPrebundle (a : VectorPrebundle R F E) : FiberPrebundle F E :=
  { a with
    continuous_trivChange := fun e he e' he' => by
      have : ContinuousOn (fun x : B × F => a.coordChange he' he x.1 x.2)
          ((e'.baseSet inter e.baseSet) ×ˢ univ) :=
        isBoundedBilinearMap_apply.continuous.comp_continuousOn
          ((a.continuousOn_coordChange he' he).prodMap continuousOn_id)
      rw [e.target_inter_preimage_symm_source_eq e']; rw [inter_comm]
      refine (continuousOn_fst.prodMk this).congr ?_
      rintro ⟨b, f⟩ ⟨hb, -⟩
      dsimp only [Function.comp_def, Prod.map]
      rw [a.mk_coordChange _ _ hb]; rw [e'.mk_symm hb.1] }

/-- Topology on the total space that will make the prebundle into a bundle. -/
@[instance_reducible]
/--
Definition of `totalSpaceTopology` / `totalSpaceTopology` 的定义

English:
definition totalSpaceTopology
  signature: (a : VectorPrebundle R F E)
  body: a.toFiberPrebundle.totalSpaceTopology

中文:
定义 totalSpaceTopology
  签名: (a : VectorPrebundle R F E)
  定义体: a.toFiberPrebundle.totalSpaceTopology

Depends on / 依赖: a.toFiberPrebundle.totalSpaceTopology, toFiberPrebundle, totalSpaceTopology
-/
def totalSpaceTopology (a : VectorPrebundle R F E) : TopologicalSpace (TotalSpace F E) :=
  a.toFiberPrebundle.totalSpaceTopology

/--
Definition of `trivializationOfMemPretrivializationAtlas` / `trivializationOfMemPretrivializationAtlas` 的定义

English:
definition trivializationOfMemPretrivializationAtlas
  signature: (a : VectorPrebundle R F E)
  body: a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he

中文:
定义 trivializationOfMemPretrivializationAtlas
  签名: (a : VectorPrebundle R F E)
  定义体: a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he

Depends on / 依赖: a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas, toFiberPrebundle, trivializationOfMemPretrivializationAtlas
-/
def trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e in a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he

/--
theorem `linear_trivializationOfMemPretrivializationAtlas` / 定理 `linear_trivializationOfMemPretrivializationAtlas`

English:
theorem linear_trivializationOfMemPretrivializationAtlas
  statement: (a : VectorPrebundle R F E)
  proof: a.totalSpaceTopology
    Trivialization.IsLinear R (trivializationOfMemPretrivializationAtlas a he) :=
  letI := a.totalSpaceTopology
  { linear := (a.pretrivialization_linear' e he).linear }

中文:
定理 linear_trivializationOfMemPretrivializationAtlas
  结论: (a : VectorPrebundle R F E)
  证明: a.totalSpaceTopology
    Trivialization.IsLinear R (trivializationOfMemPretrivializationAtlas a he) :=
  letI := a.totalSpaceTopology
  { linear := (a.pretrivialization_linear' e he).linear }

Depends on / 依赖: a.totalSpaceTopology, totalSpaceTopology
-/
theorem linear_trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e in a.pretrivializationAtlas) :
    letI := a.totalSpaceTopology
    Trivialization.IsLinear R (trivializationOfMemPretrivializationAtlas a he) :=
  letI := a.totalSpaceTopology
  { linear := (a.pretrivialization_linear' e he).linear }

variable (a : VectorPrebundle R F E)

/--
theorem `mem_trivialization_at_source` / 定理 `mem_trivialization_at_source`

English:
theorem mem_trivialization_at_source
  given: (b : B) (x : E b)
  proof: a.toFiberPrebundle.mem_pretrivializationAt_source b x

@[simp]

中文:
定理 mem_trivialization_at_source
  条件: (b : B) (x : E b)
  证明: a.toFiberPrebundle.mem_pretrivializationAt_source b x

@[simp]

Depends on / 依赖: a.toFiberPrebundle.mem_pretrivializationAt_source, mem_pretrivializationAt_source, toFiberPrebundle
-/
theorem mem_trivialization_at_source (b : B) (x : E b) :
    ⟨b, x⟩ in (a.pretrivializationAt b).source :=
  a.toFiberPrebundle.mem_pretrivializationAt_source b x

@[simp]
/--
theorem `totalSpaceMk_preimage_source` / 定理 `totalSpaceMk_preimage_source`

English:
theorem totalSpaceMk_preimage_source
  given: (b : B)
  proof: a.toFiberPrebundle.totalSpaceMk_preimage_source b

@[continuity]

中文:
定理 totalSpaceMk_preimage_source
  条件: (b : B)
  证明: a.toFiberPrebundle.totalSpaceMk_preimage_source b

@[continuity]

Depends on / 依赖: a.toFiberPrebundle.totalSpaceMk_preimage_source, toFiberPrebundle, totalSpaceMk_preimage_source
-/
theorem totalSpaceMk_preimage_source (b : B) :
    .mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  a.toFiberPrebundle.totalSpaceMk_preimage_source b

@[continuity]
/--
theorem `continuous_totalSpaceMk` / 定理 `continuous_totalSpaceMk`

English:
theorem continuous_totalSpaceMk
  given: (b : B)
  proof: a.toFiberPrebundle.continuous_totalSpaceMk b

中文:
定理 continuous_totalSpaceMk
  条件: (b : B)
  证明: a.toFiberPrebundle.continuous_totalSpaceMk b

Depends on / 依赖: a.toFiberPrebundle.continuous_totalSpaceMk, continuous_totalSpaceMk, toFiberPrebundle
-/
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (.mk b) :=
  a.toFiberPrebundle.continuous_totalSpaceMk b

/-- Make a `FiberBundle` from a `VectorPrebundle`; auxiliary construction for
`VectorPrebundle.toVectorBundle`. -/
@[instance_reducible]
/--
Definition of `toFiberBundle` / `toFiberBundle` 的定义

English:
definition toFiberBundle
  signature: : @FiberBundle B F _ _ _ a.totalSpaceTopology _
  body: a.toFiberPrebundle.toFiberBundle

中文:
定义 toFiberBundle
  签名: : @FiberBundle B F _ _ _ a.totalSpaceTopology _
  定义体: a.toFiberPrebundle.toFiberBundle

Depends on / 依赖: a.toFiberPrebundle.toFiberBundle, toFiberBundle, toFiberPrebundle
-/
def toFiberBundle : @FiberBundle B F _ _ _ a.totalSpaceTopology _ :=
  a.toFiberPrebundle.toFiberBundle

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toVectorBundle` / 定理 `toVectorBundle`

English:
theorem toVectorBundle
  statement: @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle
  proof: letI := a.totalSpaceTopology; letI := a.toFiberBundle
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_trivializationOfMemPretrivializationAtlas
    continuousOn_coordChange' := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.continuousOn_coordChange he

中文:
定理 toVectorBundle
  结论: @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle
  证明: letI := a.totalSpaceTopology; letI := a.toFiberBundle
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_trivializationOfMemPretrivializationAtlas
    continuousOn_coordChange' := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.continuousOn_coordChange he

Depends on / 依赖: a.continuousOn_coordChange, a.coor, a.linear_trivializationOfMemPretrivializationAtlas, a.toFiberBundle, a.totalSpaceTopology, continuousOn_coordChange, linear_trivializationOfMemPretrivializationAtlas, toFiberBundle, totalSpaceTopology, trivializationOfMemPretrivializationAtlas, trivialization_linear
-/
theorem toVectorBundle : @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_trivializationOfMemPretrivializationAtlas
    continuousOn_coordChange' := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.continuousOn_coordChange he he').congr fun b hb => ?_
      ext v
      have h₁ := a.linear_trivializationOfMemPretrivializationAtlas he
      have h₂ := a.linear_trivializationOfMemPretrivializationAtlas he'
      rw [trivializationOfMemPretrivializationAtlas] at h₁ h₂
      rw [a.coordChange_apply he he' hb v]; rw [ContinuousLinearEquiv.coe_coe]; rw [Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }

end VectorPrebundle

namespace ContinuousLinearMap

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable {σ : 𝕜₁ ->+* 𝕜₂}
variable {B' : Type*} [TopologicalSpace B']
variable [NormedSpace 𝕜₁ F] [forall x, Module 𝕜₁ (E x)] [TopologicalSpace (TotalSpace F E)]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜₂ F'] {E' : B' -> Type*}
  [forall x, AddCommMonoid (E' x)] [forall x, Module 𝕜₂ (E' x)] [TopologicalSpace (TotalSpace F' E')]

variable [FiberBundle F E] [VectorBundle 𝕜₁ F E]
variable [forall x, TopologicalSpace (E' x)] [FiberBundle F' E'] [VectorBundle 𝕜₂ F' E']
variable (F' E')

/--
Definition of `inCoordinates` / `inCoordinates` 的定义

English:
definition inCoordinates
  signature: (x₀ x : B) (y₀ y : B') (ϕ : E x ->SL[σ] E' y)
  body: ((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp
ϕ.comp (trivializationAt F E x₀).symmL 𝕜₁ x

中文:
定义 inCoordinates
  签名: (x₀ x : B) (y₀ y : B') (ϕ : E x ->SL[σ] E' y)
  定义体: ((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp
ϕ.comp (trivializationAt F E x₀).symmL 𝕜₁ x

Depends on / 依赖: continuousLinearMapAt, trivializationAt
-/
def inCoordinates (x₀ x : B) (y₀ y : B') (ϕ : E x ->SL[σ] E' y) : F ->SL[σ] F' :=
((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp
ϕ.comp (trivializationAt F E x₀).symmL 𝕜₁ x

variable {E E' F F'}

/--
theorem `inCoordinates_eq` / 定理 `inCoordinates_eq`

English:
theorem inCoordinates_eq
  statement: {x₀ x : B} {y₀ y : B'} {ϕ : E x ->SL[σ] E' y}
  proof: by
  ext
  simp_rw [inCoordinates, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]

中文:
定理 inCoordinates_eq
  结论: {x₀ x : B} {y₀ y : B'} {ϕ : E x ->SL[σ] E' y}
  证明: by
  ext
  simp_rw [inCoordinates, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap, ContinuousLinearMap.coe_comp, Trivialization, Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq, coe_coe, coe_comp, coe_continuousLinearEquivAt_eq, inCoordinates, simp_rw, symm_continuousLinearEquivAt_eq
-/
theorem inCoordinates_eq {x₀ x : B} {y₀ y : B'} {ϕ : E x ->SL[σ] E' y}
    (hx : x in (trivializationAt F E x₀).baseSet) (hy : y in (trivializationAt F' E' y₀).baseSet) :
    inCoordinates F E F' E' x₀ x y₀ y ϕ =
      ((trivializationAt F' E' y₀).continuousLinearEquivAt 𝕜₂ y hy : E' y ->L[𝕜₂] F').comp
        (ϕ.comp <|
          (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜₁ x hx).symm : F ->L[𝕜₁] E x)) := by
  ext
  simp_rw [inCoordinates, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.VectorBundleCore.inCoordinates_eq` / 定理 `_root_.VectorBundleCore.inCoordinates_eq`

English:
theorem _root_.VectorBundleCore.inCoordinates_eq
  statement: {ι ι'} (Z : VectorBundleCore 𝕜₁ B F ι)
  proof: by
  simp_rw [inCoordinates, Z'.trivializationAt_continuousLinearMapAt hy,
    Z.trivializationAt_symmL hx]

中文:
定理 _root_.VectorBundleCore.inCoordinates_eq
  结论: {ι ι'} (Z : VectorBundleCore 𝕜₁ B F ι)
  证明: by
  simp_rw [inCoordinates, Z'.trivializationAt_continuousLinearMapAt hy,
    Z.trivializationAt_symmL hx]
-/
protected theorem _root_.VectorBundleCore.inCoordinates_eq {ι ι'} (Z : VectorBundleCore 𝕜₁ B F ι)
    (Z' : VectorBundleCore 𝕜₂ B' F' ι') {x₀ x : B} {y₀ y : B'} (ϕ : F ->SL[σ] F')
    (hx : x in Z.baseSet (Z.indexAt x₀)) (hy : y in Z'.baseSet (Z'.indexAt y₀)) :
    inCoordinates F Z.Fiber F' Z'.Fiber x₀ x y₀ y ϕ =
      (Z'.coordChange (Z'.indexAt y) (Z'.indexAt y₀) y).comp
        (ϕ.comp <| Z.coordChange (Z.indexAt x₀) (Z.indexAt x) x) := by
  simp_rw [inCoordinates, Z'.trivializationAt_continuousLinearMapAt hy,
    Z.trivializationAt_symmL hx]

end ContinuousLinearMap

end
