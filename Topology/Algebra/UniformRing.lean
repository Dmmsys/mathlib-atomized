/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-!
# Completion of topological rings:

This file endows the completion of a topological ring with a ring structure.
More precisely, the instance `UniformSpace.Completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`IsUniformAddGroup`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`UniformSpace.Completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `UniformSpace.Completion.extensionHom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `Completion R`.
* `UniformSpace.Completion.mapRingHom`: promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `Completion R` to `Completion S`.

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/

@[expose] public section

noncomputable section

universe u
namespace UniformSpace.Completion

open IsDenseInducing UniformSpace Function

section one_and_mul
variable (α : Type*) [Ring α] [UniformSpace α]

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (Completion α)
  body: ⟨(1 : α)⟩

中文:
实例 one
  签名: : One (Completion α)
  定义体: ⟨(1 : α)⟩
-/
instance one : One (Completion α) :=
  ⟨(1 : α)⟩

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul (Completion α)
  body: ⟨curry (isDenseInducing_coe.prodMap isDenseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

@[norm_cast]

中文:
实例 mul
  签名: : Mul (Completion α)
  定义体: ⟨curry (isDenseInducing_coe.prodMap isDenseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

@[norm_cast]

Depends on / 依赖: extend, isDenseInducing_coe, isDenseInducing_coe.prodMap, prodMap, uncurry
-/
instance mul : Mul (Completion α) :=
⟨curry (isDenseInducing_coe.prodMap isDenseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

@[norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : α) : Completion α) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : α) : Completion α) = 1
  证明: rfl
-/
theorem coe_one : ((1 : α) : Completion α) = 1 :=
  rfl

/--
lemma `coe_eq_one_iff` / 引理 `coe_eq_one_iff`

English:
lemma coe_eq_one_iff
  given: [T0Space α] {x : α}
  statement: (x : Completion α) = 1 ↔ x = 1
  proof: Completion.coe_inj

中文:
引理 coe_eq_one_iff
  条件: [T0Space α] {x : α}
  结论: (x : Completion α) = 1 ↔ x = 1
  证明: Completion.coe_inj
-/
@[simp] lemma coe_eq_one_iff [T0Space α] {x : α} : (x : Completion α) = 1 ↔ x = 1 :=
  Completion.coe_inj

end one_and_mul

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α]

@[norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (a b : α)
  statement: ((a * b : α) : Completion α) = a * b
  proof: ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

中文:
定理 coe_mul
  条件: (a b : α)
  结论: ((a * b : α) : Completion α) = a * b
  证明: ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

Depends on / 依赖: continuous_coe, continuous_mul, extend_eq, isDenseInducing_coe, isDenseInducing_coe.prodMap, prodMap
-/
theorem coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

variable [IsUniformAddGroup α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMul (Completion α)
  body: by
    let m := (AddMonoidHom.mul : α ->+ α ->+ α).compr₂ toCompl
    have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
    have di : IsDenseInducing (toCompl : α -> Completion α) := isDenseInducing_coe
    exact (di.extend_Z_bilin di this :)

中文:
实例 :
  签名: ContinuousMul (Completion α)
  定义体: by
    let m := (AddMonoidHom.mul : α ->+ α ->+ α).compr₂ toCompl
    have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
    have di : IsDenseInducing (toCompl : α -> Completion α) := isDenseInducing_coe
    exact (di.extend_Z_bilin di this :)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mul, Completion, Continuous, IsDenseInducing, continuous_coe, continuous_mul, di.extend_Z_bilin, extend_Z_bilin, isDenseInducing_coe, toCompl
-/
instance : ContinuousMul (Completion α) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : α ->+ α ->+ α).compr₂ toCompl
    have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
    have di : IsDenseInducing (toCompl : α -> Completion α) := isDenseInducing_coe
    exact (di.extend_Z_bilin di this :)

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: : Ring (Completion α)
  body: { AddMonoidWithOne.unary, ((inferInstance : AddCommGroup (Completion α))),
      ((inferInstance : Mul (Completion α))), ((inferInstance : One (Completion α))) with
    zero_mul a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← co

中文:
实例 ring
  签名: : Ring (Completion α)
  定义体: { AddMonoidWithOne.unary, ((inferInstance : AddCommGroup (Completion α))),
      ((inferInstance : Mul (Completion α))), ((inferInstance : One (Completion α))) with
    zero_mul a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← co

Depends on / 依赖: AddCommGroup, AddMonoidWithOne, AddMonoidWithOne.unary, Completion, Completion.induction_on, coe_mul, coe_zero, continu, continuous_const, fun_prop, induction_on, isClosed_eq, mul_zero, one_mul, zero_mul
-/
instance ring : Ring (Completion α) :=
  { AddMonoidWithOne.unary, ((inferInstance : AddCommGroup (Completion α))),
      ((inferInstance : Mul (Completion α))), ((inferInstance : One (Completion α))) with
    zero_mul a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, zero_mul]
    mul_zero a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, mul_zero]
    one_mul a :=
      Completion.induction_on a
        (isClosed_eq (by fun_prop) continuous_id)
        fun a => by rw [← coe_one, ← coe_mul, one_mul]
    mul_one a :=
      Completion.induction_on a
        (isClosed_eq (by fun_prop) continuous_id)
        fun a => by rw [← coe_one, ← coe_mul, mul_one]
    mul_assoc a b c :=
      Completion.induction_on₃ a b c
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]
    left_distrib a b c :=
      Completion.induction_on₃ a b c
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_add]
    right_distrib a b c :=
      Completion.induction_on₃ a b c
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mul] }

/--
Definition of `coeRingHom` / `coeRingHom` 的定义

English:
definition coeRingHom
  signature: : α ->+* Completion α where
  body: (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul

中文:
定义 coeRingHom
  签名: : α ->+* Completion α where
  定义体: (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul
-/
def coeRingHom : α ->+* Completion α where
  toFun := (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul

/--
theorem `continuous_coeRingHom` / 定理 `continuous_coeRingHom`

English:
theorem continuous_coeRingHom
  statement: Continuous (coeRingHom : α -> Completion α)
  proof: continuous_coe α

中文:
定理 continuous_coeRingHom
  结论: Continuous (coeRingHom : α -> Completion α)
  证明: continuous_coe α

Depends on / 依赖: continuous_coe
-/
theorem continuous_coeRingHom : Continuous (coeRingHom : α -> Completion α) :=
  continuous_coe α

variable {β : Type u} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α ->+* β) (hf : Continuous f)

/--
Definition of `extensionHom` / `extensionHom` 的定义

English:
definition extensionHom
  signature: [CompleteSpace β] [T0Space β]
  body: have hf' : Continuous (f : α ->+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.in

中文:
定义 extensionHom
  签名: [CompleteSpace β] [T0Space β]
  定义体: have hf' : Continuous (f : α ->+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.in

Depends on / 依赖: Continuous
-/
def extensionHom [CompleteSpace β] [T0Space β] : Completion α ->+* β :=
  have hf' : Continuous (f : α ->+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by simp_rw [← coe_add, extension_coe hf, f.map_add]
    map_one' := by rw [← coe_one, extension_coe hf, f.map_one]
    map_mul' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by simp_rw [← coe_mul, extension_coe hf, f.map_mul] }

/--
theorem `extensionHom_coe` / 定理 `extensionHom_coe`

English:
theorem extensionHom_coe
  given: [CompleteSpace β] [T0Space β] (a : α)
  proof: by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
UniformSpace.Completion.extension_coe uniformContinuous_addMonoidHom_of_continuous hf]

中文:
定理 extensionHom_coe
  条件: [CompleteSpace β] [T0Space β] (a : α)
  证明: by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
UniformSpace.Completion.extension_coe uniformContinuous_addMonoidHom_of_continuous hf]

Depends on / 依赖: Completion, Completion.extensionHom, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, RingHom, RingHom.coe_mk, UniformSpace, UniformSpace.Completion.extension_coe, coe_mk, extensionHom, extension_coe, uniformContinuous_addMonoidHom_of_continuous
-/
theorem extensionHom_coe [CompleteSpace β] [T0Space β] (a : α) :
    Completion.extensionHom f hf a = f a := by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
UniformSpace.Completion.extension_coe uniformContinuous_addMonoidHom_of_continuous hf]

/--
Instance `topologicalRing` / 实例 `topologicalRing`

English:
instance topologicalRing
  signature: : IsTopologicalRing (Completion α) where
  body: continuous_add
  continuous_mul := continuous_mul

中文:
实例 topologicalRing
  签名: : IsTopologicalRing (Completion α) where
  定义体: continuous_add
  continuous_mul := continuous_mul

Depends on / 依赖: continuous_add
-/
instance topologicalRing : IsTopologicalRing (Completion α) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul

/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: (hf : Continuous f)
  body: extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)

中文:
定义 mapRingHom
  签名: (hf : Continuous f)
  定义体: extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)

Depends on / 依赖: coeRingHom, coeRingHom.comp, continuous_coeRingHom, continuous_coeRingHom.comp, extensionHom
-/
def mapRingHom (hf : Continuous f) : Completion α ->+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)

/--
theorem `mapRingHom_apply` / 定理 `mapRingHom_apply`

English:
theorem mapRingHom_apply
  given: {x : Completion α}
  statement: mapRingHom f hf x = .map f x
  proof: rfl

中文:
定理 mapRingHom_apply
  条件: {x : Completion α}
  结论: mapRingHom f hf x = .map f x
  证明: rfl
-/
@[simp] theorem mapRingHom_apply {x : Completion α} : mapRingHom f hf x = .map f x := rfl
/--
theorem `coe_mapRingHom` / 定理 `coe_mapRingHom`

English:
theorem coe_mapRingHom
  statement: mapRingHom f hf = Completion.map f
  proof: rfl

中文:
定理 coe_mapRingHom
  结论: mapRingHom f hf = Completion.map f
  证明: rfl
-/
theorem coe_mapRingHom : mapRingHom f hf = Completion.map f := rfl

variable {f}

/--
theorem `mapRingHom_coe` / 定理 `mapRingHom_coe`

English:
theorem mapRingHom_coe
  given: (hf : Continuous f) (a : α)
  statement: mapRingHom f hf a = f a
  proof: by
  rw [mapRingHom_apply]; rw [map_coe (uniformContinuous_addMonoidHom_of_continuous hf)]

中文:
定理 mapRingHom_coe
  条件: (hf : Continuous f) (a : α)
  结论: mapRingHom f hf a = f a
  证明: by
  rw [mapRingHom_apply]; rw [map_coe (uniformContinuous_addMonoidHom_of_continuous hf)]

Depends on / 依赖: mapRingHom_apply, map_coe, uniformContinuous_addMonoidHom_of_continuous
-/
theorem mapRingHom_coe (hf : Continuous f) (a : α) : mapRingHom f hf a = f a := by
  rw [mapRingHom_apply]; rw [map_coe (uniformContinuous_addMonoidHom_of_continuous hf)]

/--
theorem `mapRingHom_comp` / 定理 `mapRingHom_comp`

English:
theorem mapRingHom_comp
  statement: {γ : Type*} [UniformSpace γ] [Ring γ] [IsUniformAddGroup γ]
  proof: DFunLike.ext' map_comp
    (uniformContinuous_addMonoidHom_of_continuous hg)
    (uniformContinuous_addMonoidHom_of_continuous hf)

中文:
定理 mapRingHom_comp
  结论: {γ : 类型} [UniformSpace γ] [Ring γ] [IsUniformAddGroup γ]
  证明: DFunLike.ext' map_comp
    (uniformContinuous_addMonoidHom_of_continuous hg)
    (uniformContinuous_addMonoidHom_of_continuous hf)

Depends on / 依赖: DFunLike, DFunLike.ext, map_comp, uniformContinuous_addMonoidHom_of_continuous
-/
theorem mapRingHom_comp {γ : Type*} [UniformSpace γ] [Ring γ] [IsUniformAddGroup γ]
    [IsTopologicalRing γ] {g : β ->+* γ} (hg : Continuous g) (hf : Continuous f) :
    (mapRingHom g hg).comp (mapRingHom f hf) = mapRingHom (g.comp f) (hg.comp hf) :=
DFunLike.ext' map_comp
    (uniformContinuous_addMonoidHom_of_continuous hg)
    (uniformContinuous_addMonoidHom_of_continuous hf)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mapRingHom_id` / 定理 `mapRingHom_id`

English:
theorem mapRingHom_id
  statement: mapRingHom (.id α) continuous_id = .id (Completion α)
  proof: by
  simp [RingHom.ext_iff, mapRingHom_apply]

#adaptation_note

中文:
定理 mapRingHom_id
  结论: mapRingHom (.id α) continuous_id = .id (Completion α)
  证明: by
  simp [RingHom.ext_iff, mapRingHom_apply]

#adaptation_note

Depends on / 依赖: RingHom, RingHom.ext_iff, ext_iff, mapRingHom_apply
-/
theorem mapRingHom_id : mapRingHom (.id α) continuous_id = .id (Completion α) := by
  simp [RingHom.ext_iff, mapRingHom_apply]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A ring isomorphism `α ≃+* β` between uniform rings, uniformly continuous in both directions,
lifts to a ring isomorphism between corresponding uniform space completions. -/
@[simps!]
/--
Definition of `mapRingEquiv` / `mapRingEquiv` 的定义

English:
definition mapRingEquiv
  signature: (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm)
  body: .ofRingHom (mapRingHom f.toRingHom hf) (mapRingHom f.symm.toRingHom hf')
    (by simp [mapRingHom_comp]) (by simp [mapRingHom_comp])

中文:
定义 mapRingEquiv
  签名: (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm)
  定义体: .ofRingHom (mapRingHom f.toRingHom hf) (mapRingHom f.symm.toRingHom hf')
    (by simp [mapRingHom_comp]) (by simp [mapRingHom_comp])

Depends on / 依赖: f.symm.toRingHom, f.toRingHom, mapRingHom, mapRingHom_comp, ofRingHom, toRingHom
-/
def mapRingEquiv (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm) :
    Completion α ≃+* Completion β :=
  .ofRingHom (mapRingHom f.toRingHom hf) (mapRingHom f.symm.toRingHom hf')
    (by simp [mapRingHom_comp]) (by simp [mapRingHom_comp])

section Algebra

variable (A : Type*) [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  (R : Type*) [CommSemiring R] [Algebra R A] [UniformContinuousConstSMul R A]

@[simp]
/--
theorem `map_smul_eq_mul_coe` / 定理 `map_smul_eq_mul_coe`

English:
theorem map_smul_eq_mul_coe
  given: (r : R)
  proof: by
  ext x
  refine Completion.induction_on x ?_ fun a => ?_
  · exact isClosed_eq Completion.continuous_map (continuous_const_mul _)
  · simp_rw [map_coe (uniformContinuous_const_smul r) a, Algebra.smul_def, coe_mul]

中文:
定理 map_smul_eq_mul_coe
  条件: (r : R)
  证明: by
  ext x
  refine Completion.induction_on x ?_ fun a => ?_
  · exact isClosed_eq Completion.continuous_map (continuous_const_mul _)
  · simp_rw [map_coe (uniformContinuous_const_smul r) a, Algebra.smul_def, coe_mul]

Depends on / 依赖: Algebra, Algebra.smul_def, Completion, Completion.continuous_map, Completion.induction_on, coe_mul, continuous_const_mul, continuous_map, induction_on, isClosed_eq, map_coe, simp_rw, smul_def, uniformContinuous_const_smul
-/
theorem map_smul_eq_mul_coe (r : R) :
    Completion.map (r • ·) = ((algebraMap R A r : Completion A) * ·) := by
  ext x
  refine Completion.induction_on x ?_ fun a => ?_
  · exact isClosed_eq Completion.continuous_map (continuous_const_mul _)
  · simp_rw [map_coe (uniformContinuous_const_smul r) a, Algebra.smul_def, coe_mul]

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra R (Completion A) where
  body: (UniformSpace.Completion.coeRingHom : A ->+* Completion A).comp (algebraMap R A)
  commutes' := fun r x =>
    Completion.induction_on x (isClosed_eq (continuous_const_mul _) (continuous_mul_const _))
      fun a => by
      simpa only [coe_mul] using! congr_arg ((↑) : A -> Completion A) (Algebra.co

中文:
实例 algebra
  签名: : Algebra R (Completion A) where
  定义体: (UniformSpace.Completion.coeRingHom : A ->+* Completion A).comp (algebraMap R A)
  commutes' := fun r x =>
    Completion.induction_on x (isClosed_eq (continuous_const_mul _) (continuous_mul_const _))
      fun a => by
      simpa only [coe_mul] using! congr_arg ((↑) : A -> Completion A) (Algebra.co

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.coeRingHom, algebraMap, coeRingHom
-/
instance algebra : Algebra R (Completion A) where
  algebraMap := (UniformSpace.Completion.coeRingHom : A ->+* Completion A).comp (algebraMap R A)
  commutes' := fun r x =>
    Completion.induction_on x (isClosed_eq (continuous_const_mul _) (continuous_mul_const _))
      fun a => by
      simpa only [coe_mul] using! congr_arg ((↑) : A -> Completion A) (Algebra.commutes r a)
  smul_def' := fun r x => congr_fun (map_smul_eq_mul_coe A R r) x

/--
theorem `algebraMap_def` / 定理 `algebraMap_def`

English:
theorem algebraMap_def
  given: (r : R)
  proof: rfl

中文:
定理 algebraMap_def
  条件: (r : R)
  证明: rfl
-/
theorem algebraMap_def (r : R) :
    algebraMap R (Completion A) r = (algebraMap R A r : Completion A) :=
  rfl

end Algebra

section CommRing

variable (R : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing (Completion R)
  body: { Completion.ring with
    mul_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }

中文:
实例 commRing
  签名: : CommRing (Completion R)
  定义体: { Completion.ring with
    mul_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }

Depends on / 依赖: Completion, Completion.induction_on, Completion.ring, coe_mul, fun_prop, isClosed_eq, mul_comm
-/
instance commRing : CommRing (Completion R) :=
  { Completion.ring with
    mul_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }

/--
Instance `algebra'` / 实例 `algebra'`

English:
instance algebra'
  signature: : Algebra R (Completion R)
  body: by infer_instance

中文:
实例 algebra'
  签名: : Algebra R (Completion R)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance algebra' : Algebra R (Completion R) := by infer_instance

end CommRing

end UniformSpace.Completion

namespace UniformSpace

variable {α : Type*}

-- TODO: move (some of) these results to the file about topological rings
/--
theorem `inseparableSetoid_ring` / 定理 `inseparableSetoid_ring`

English:
theorem inseparableSetoid_ring
  given: (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α]
  proof: Setoid.ext fun x y =>
addGroup_inseparable_iff.trans .trans (by rfl) (Submodule.quotientRel_def _).symm

中文:
定理 inseparableSetoid_ring
  条件: (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α]
  证明: Setoid.ext fun x y =>
addGroup_inseparable_iff.trans .trans (by rfl) (Submodule.quotientRel_def _).symm

Depends on / 依赖: Setoid, Setoid.ext, Submodule, Submodule.quotientRel_def, addGroup_inseparable_iff, addGroup_inseparable_iff.trans, quotientRel_def
-/
theorem inseparableSetoid_ring (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α] :
    inseparableSetoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoid.ext fun x y =>
addGroup_inseparable_iff.trans .trans (by rfl) (Submodule.quotientRel_def _).symm

/--
Definition of `sepQuotHomeomorphRingQuot` / `sepQuotHomeomorphRingQuot` 的定义

English:
definition sepQuotHomeomorphRingQuot
  signature: (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α]
  body: Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
continuous_toFun := continuous_id.quotient_map' by
    rw [inseparableSetoid_ring]; exact fun _ _ => id
continuous_invFun := continuous_id.quotient_map' by
    rw [inseparableSetoid_ring]; exact fun _ _ => id

中文:
定义 sepQuotHomeomorphRingQuot
  签名: (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α]
  定义体: Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
continuous_toFun := continuous_id.quotient_map' by
    rw [inseparableSetoid_ring]; exact fun _ _ => id
continuous_invFun := continuous_id.quotient_map' by
    rw [inseparableSetoid_ring]; exact fun _ _ => id

Depends on / 依赖: Quotient, Quotient.congrRight, congrRight, inseparableSetoid_ring
-/
def sepQuotHomeomorphRingQuot (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α] :
    SeparationQuotient α ≃ₜ α ⧸ (⊥ : Ideal α).closure where
  toEquiv := Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
continuous_toFun := continuous_id.quotient_map' by
    rw [inseparableSetoid_ring]; exact fun _ _ => id
continuous_invFun := continuous_id.quotient_map' by
    rw [inseparableSetoid_ring]; exact fun _ _ => id

/--
Definition of `sepQuotRingEquivRingQuot` / `sepQuotRingEquivRingQuot` 的定义

English:
definition sepQuotRingEquivRingQuot
  signature: (α) [CommRing α] [TopologicalSpace α] [IsTopologicalRing α]
  body: sepQuotHomeomorphRingQuot α
  map_mul' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ => rfl)
  map_add' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ => rfl)

中文:
定义 sepQuotRingEquivRingQuot
  签名: (α) [CommRing α] [TopologicalSpace α] [IsTopologicalRing α]
  定义体: sepQuotHomeomorphRingQuot α
  map_mul' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ => rfl)
  map_add' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ => rfl)

Depends on / 依赖: sepQuotHomeomorphRingQuot
-/
def sepQuotRingEquivRingQuot (α) [CommRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    SeparationQuotient α ≃+* α ⧸ (⊥ : Ideal α).closure where
  __ := sepQuotHomeomorphRingQuot α
  map_mul' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ => rfl)
  map_add' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ => rfl)

end UniformSpace

section UniformExtension

variable {α : Type*} [UniformSpace α] [Semiring α]
variable {β : Type*} [UniformSpace β] [Semiring β] [IsTopologicalSemiring β]
variable {γ : Type*} [UniformSpace γ] [Semiring γ] [IsTopologicalSemiring γ]
variable [T2Space γ] [CompleteSpace γ]

/--
Definition of `IsDenseInducing.extendRingHom` / `IsDenseInducing.extendRingHom` 的定义

English:
definition IsDenseInducing.extendRingHom
  signature: {i : α ->+* β} {f : α ->+* γ}
  body: (ue.isDenseInducing dr).extend f
  map_one' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 1
    exacts [i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 0 <;>
    simp only [map_zero]
 

中文:
定义 IsDenseInducing.extendRingHom
  签名: {i : α ->+* β} {f : α ->+* γ}
  定义体: (ue.isDenseInducing dr).extend f
  map_one' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 1
    exacts [i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 0 <;>
    simp only [map_zero]
 

Depends on / 依赖: extend, isDenseInducing, ue.isDenseInducing
-/
noncomputable def IsDenseInducing.extendRingHom {i : α ->+* β} {f : α ->+* γ}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) : β ->+* γ where
  toFun := (ue.isDenseInducing dr).extend f
  map_one' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 1
    exacts [i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 0 <;>
    simp only [map_zero]
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y => DenseRange.induction_on₂ dr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · simp_rw [← i.map_add, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous _,
        ← f.map_add]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y => DenseRange.induction_on₂ dr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · simp_rw [← i.map_mul, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous _,
        ← f.map_mul]

end UniformExtension
