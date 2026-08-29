/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Direct sum of modules

The first part of the file provides constructors for direct sums of modules. It provides a
construction of the direct sum using the universal property and proves its uniqueness
(`DirectSum.toModule.unique`).

The second part of the file covers the special case of direct sums of submodules of a fixed module
`M`. There is a canonical linear map from this direct sum to `M` (`DirectSum.coeLinearMap`), and
the construction is of particular importance when this linear map is an equivalence; that is, when
the submodules provide an internal decomposition of `M`. The property is defined more generally
elsewhere as `DirectSum.IsInternal`, but its basic consequences on `Submodule`s are established
in this file.

-/

@[expose] public section

universe u v w u₁

namespace DirectSum

open DirectSum Finsupp Module

section General

variable {R : Type u} [Semiring R]
variable {ι : Type v}
variable {M : ι -> Type w} [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (⨁ i, M i)
  body: inferInstanceAs Module R (Π₀ i, M i)

中文:
实例 :
  签名: Module R (⨁ i, M i)
  定义体: inferInstanceAs Module R (Π₀ i, M i)

Depends on / 依赖: Module
-/
instance : Module R (⨁ i, M i) :=
inferInstanceAs Module R (Π₀ i, M i)

instance {S : Type*} [Semiring S] [forall i, Module S (M i)] [forall i, SMulCommClass R S (M i)] :
    SMulCommClass R S (⨁ i, M i) :=
inferInstanceAs SMulCommClass R S (Π₀ i, M i)

instance {S : Type*} [Semiring S] [SMul R S] [forall i, Module S (M i)] [forall i, IsScalarTower R S (M i)] :
    IsScalarTower R S (⨁ i, M i) :=
inferInstanceAs IsScalarTower R S (Π₀ i, M i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Module Rᵐᵒᵖ (M i)] [forall i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i)
  body: inferInstanceAs IsCentralScalar R (Π₀ i, M i)

中文:
实例 [forall
  签名: i, Module Rᵐᵒᵖ (M i)] [对任意 i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i)
  定义体: inferInstanceAs IsCentralScalar R (Π₀ i, M i)

Depends on / 依赖: IsCentralScalar
-/
instance [forall i, Module Rᵐᵒᵖ (M i)] [forall i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i) :=
inferInstanceAs IsCentralScalar R (Π₀ i, M i)

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (b : R) (v : ⨁ i, M i) (i : ι)
  statement: (b • v) i = b • v i
  proof: DFinsupp.smul_apply _ _ _

中文:
定理 smul_apply
  条件: (b : R) (v : ⨁ i, M i) (i : ι)
  结论: (b • v) i = b • v i
  证明: DFinsupp.smul_apply _ _ _

Depends on / 依赖: DFinsupp, DFinsupp.smul_apply, smul_apply
-/
theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
  DFinsupp.smul_apply _ _ _

variable (R) in
/--
Definition of `coeFnLinearMap` / `coeFnLinearMap` 的定义

English:
definition coeFnLinearMap
  signature: : (⨁ i, M i) ->ₗ[R] forall i, M i
  body: DFinsupp.coeFnLinearMap R

@[simp]

中文:
定义 coeFnLinearMap
  签名: : (⨁ i, M i) ->ₗ[R] 对任意 i, M i
  定义体: DFinsupp.coeFnLinearMap R

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.coeFnLinearMap, coeFnLinearMap
-/
def coeFnLinearMap : (⨁ i, M i) ->ₗ[R] forall i, M i :=
  DFinsupp.coeFnLinearMap R

@[simp]
/--
lemma `coeFnLinearMap_apply` / 引理 `coeFnLinearMap_apply`

English:
lemma coeFnLinearMap_apply
  given: (v : ⨁ i, M i)
  statement: coeFnLinearMap R v = v
  proof: rfl

中文:
引理 coeFnLinearMap_apply
  条件: (v : ⨁ i, M i)
  结论: coeFnLinearMap R v = v
  证明: rfl
-/
lemma coeFnLinearMap_apply (v : ⨁ i, M i) : coeFnLinearMap R v = v :=
  rfl

variable (R ι M)

section DecidableEq

variable [DecidableEq ι]

/--
Definition of `lmk` / `lmk` 的定义

English:
definition lmk
  signature: : forall s : Finset ι, (forall i : (↑s : Set ι), M i.val) ->ₗ[R] ⨁ i, M i
  body: DFinsupp.lmk

中文:
定义 lmk
  签名: : 对任意 s : Finset ι, (对任意 i : (↑s : Set ι), M i.val) ->ₗ[R] ⨁ i, M i
  定义体: DFinsupp.lmk

Depends on / 依赖: DFinsupp, DFinsupp.lmk
-/
def lmk : forall s : Finset ι, (forall i : (↑s : Set ι), M i.val) ->ₗ[R] ⨁ i, M i :=
  DFinsupp.lmk

/--
Definition of `lof` / `lof` 的定义

English:
definition lof
  signature: : forall i : ι, M i ->ₗ[R] ⨁ i, M i
  body: DFinsupp.lsingle

中文:
定义 lof
  签名: : 对任意 i : ι, M i ->ₗ[R] ⨁ i, M i
  定义体: DFinsupp.lsingle

Depends on / 依赖: DFinsupp, DFinsupp.lsingle, lsingle
-/
def lof : forall i : ι, M i ->ₗ[R] ⨁ i, M i :=
  DFinsupp.lsingle

/--
theorem `lof_eq_of` / 定理 `lof_eq_of`

English:
theorem lof_eq_of
  given: (i : ι) (b : M i)
  statement: lof R ι M i b = of M i b
  proof: rfl

中文:
定理 lof_eq_of
  条件: (i : ι) (b : M i)
  结论: lof R ι M i b = of M i b
  证明: rfl
-/
theorem lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b := rfl

variable {ι M}

/--
theorem `single_eq_lof` / 定理 `single_eq_lof`

English:
theorem single_eq_lof
  given: (i : ι) (b : M i)
  statement: DFinsupp.single i b = lof R ι M i b
  proof: rfl

中文:
定理 single_eq_lof
  条件: (i : ι) (b : M i)
  结论: DFinsupp.single i b = lof R ι M i b
  证明: rfl
-/
theorem single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = lof R ι M i b := rfl

/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: (s : Finset ι) (c : R) (x)
  statement: mk M s (c • x) = c • mk M s x
  proof: (lmk R ι M s).map_smul c x

中文:
定理 mk_smul
  条件: (s : Finset ι) (c : R) (x)
  结论: mk M s (c • x) = c • mk M s x
  证明: (lmk R ι M s).map_smul c x

Depends on / 依赖: map_smul
-/
theorem mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
  (lmk R ι M s).map_smul c x

/--
theorem `of_smul` / 定理 `of_smul`

English:
theorem of_smul
  given: (i : ι) (c : R) (x)
  statement: of M i (c • x) = c • of M i x
  proof: (lof R ι M i).map_smul c x

中文:
定理 of_smul
  条件: (i : ι) (c : R) (x)
  结论: of M i (c • x) = c • of M i x
  证明: (lof R ι M i).map_smul c x

Depends on / 依赖: map_smul
-/
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
  (lof R ι M i).map_smul c x

variable {R}

/--
theorem `support_smul` / 定理 `support_smul`

English:
theorem support_smul
  given: [forall (i : ι) (x : M i), Decidable (x != 0)] (c : R) (v : ⨁ i, M i)
  proof: DFinsupp.support_smul _ _

中文:
定理 support_smul
  条件: [对任意 (i : ι) (x : M i), Decidable (x != 0)] (c : R) (v : ⨁ i, M i)
  证明: DFinsupp.support_smul _ _

Depends on / 依赖: DFinsupp, DFinsupp.support_smul, support_smul
-/
theorem support_smul [forall (i : ι) (x : M i), Decidable (x != 0)] (c : R) (v : ⨁ i, M i) :
    (c • v).support subseteq v.support :=
  DFinsupp.support_smul _ _

variable {N : Type u₁} [AddCommMonoid N] [Module R N]
variable (φ : forall i, M i ->ₗ[R] N)
variable (R ι N)

/--
Definition of `toModule` / `toModule` 的定义

English:
definition toModule
  signature: : (⨁ i, M i) ->ₗ[R] N
  body: DFunLike.coe (DFinsupp.lsum Nat) φ

中文:
定义 toModule
  签名: : (⨁ i, M i) ->ₗ[R] N
  定义体: DFunLike.coe (DFinsupp.lsum Nat) φ

Depends on / 依赖: DFinsupp, DFinsupp.lsum, DFunLike, DFunLike.coe
-/
def toModule : (⨁ i, M i) ->ₗ[R] N :=
  DFunLike.coe (DFinsupp.lsum Nat) φ

/--
theorem `coe_toModule_eq_coe_toAddMonoid` / 定理 `coe_toModule_eq_coe_toAddMonoid`

English:
theorem coe_toModule_eq_coe_toAddMonoid
  proof: rfl

中文:
定理 coe_toModule_eq_coe_toAddMonoid
  证明: rfl
-/
theorem coe_toModule_eq_coe_toAddMonoid :
    (toModule R ι N φ : (⨁ i, M i) -> N) = toAddMonoid fun i => (φ i).toAddMonoidHom := rfl

variable {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp]
/--
theorem `toModule_lof` / 定理 `toModule_lof`

English:
theorem toModule_lof
  given: (i) (x : M i)
  statement: toModule R ι N φ (lof R ι M i x) = φ i x
  proof: toAddMonoid_of (fun i => (φ i).toAddMonoidHom) i x

中文:
定理 toModule_lof
  条件: (i) (x : M i)
  结论: toModule R ι N φ (lof R ι M i x) = φ i x
  证明: toAddMonoid_of (fun i => (φ i).toAddMonoidHom) i x

Depends on / 依赖: toAddMonoidHom, toAddMonoid_of
-/
theorem toModule_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x :=
  toAddMonoid_of (fun i => (φ i).toAddMonoidHom) i x

variable (ψ : (⨁ i, M i) ->ₗ[R] N)

/--
theorem `toModule.unique` / 定理 `toModule.unique`

English:
theorem toModule.unique
  given: (f : ⨁ i, M i)
  statement: ψ f = toModule R ι N (fun i => ψ.comp <| lof R ι M i) f
  proof: toAddMonoid.unique ψ.toAddMonoidHom f

中文:
定理 toModule.unique
  条件: (f : ⨁ i, M i)
  结论: ψ f = toModule R ι N (fun i => ψ.comp <| lof R ι M i) f
  证明: toAddMonoid.unique ψ.toAddMonoidHom f

Depends on / 依赖: toAddMonoid, toAddMonoid.unique, toAddMonoidHom, unique
-/
theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i => ψ.comp <| lof R ι M i) f :=
  toAddMonoid.unique ψ.toAddMonoidHom f

variable {ψ} {ψ' : (⨁ i, M i) ->ₗ[R] N}

/-- Two `LinearMap`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `linearMap_ext` / 定理 `linearMap_ext`

English:
theorem linearMap_ext
  given: ⦃ψ ψ'
  statement: (⨁ i, M i) ->ₗ[R] N⦄
  proof: DFinsupp.lhom_ext' H

中文:
定理 linearMap_ext
  条件: ⦃ψ ψ'
  结论: (⨁ i, M i) ->ₗ[R] N⦄
  证明: DFinsupp.lhom_ext' H

Depends on / 依赖: DFinsupp, DFinsupp.lhom_ext, lhom_ext
-/
theorem linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄
    (H : forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' :=
  DFinsupp.lhom_ext' H

/--
Definition of `lsetToSet` / `lsetToSet` 的定义

English:
definition lsetToSet
  signature: (S T : Set ι) (H : S subseteq T)
  body: toModule R _ _ fun i => lof R T (fun i : T => M i) ⟨i, H i.prop⟩

中文:
定义 lsetToSet
  签名: (S T : Set ι) (H : S subseteq T)
  定义体: toModule R _ _ fun i => lof R T (fun i : T => M i) ⟨i, H i.prop⟩

Depends on / 依赖: i.prop, toModule
-/
def lsetToSet (S T : Set ι) (H : S subseteq T) : (⨁ i : S, M i) ->ₗ[R] ⨁ i : T, M i :=
  toModule R _ _ fun i => lof R T (fun i : T => M i) ⟨i, H i.prop⟩

variable (ι M)

/-- Given `Fintype α`, `linearEquivFunOnFintype R` is the natural `R`-linear equivalence
between `⨁ i, M i` and `∀ i, M i`. -/
@[simps! apply]
/--
Definition of `linearEquivFunOnFintype` / `linearEquivFunOnFintype` 的定义

English:
definition linearEquivFunOnFintype
  signature: [Fintype ι]
  body: DFinsupp.linearEquivFunOnFintype

中文:
定义 linearEquivFunOnFintype
  签名: [Fintype ι]
  定义体: DFinsupp.linearEquivFunOnFintype

Depends on / 依赖: DFinsupp, DFinsupp.linearEquivFunOnFintype, linearEquivFunOnFintype
-/
def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] forall i, M i :=
  DFinsupp.linearEquivFunOnFintype

variable {ι M}

@[simp]
/--
theorem `linearEquivFunOnFintype_lof` / 定理 `linearEquivFunOnFintype_lof`

English:
theorem linearEquivFunOnFintype_lof
  given: [Fintype ι] (i : ι) (m : M i)
  proof: by
  rfl

@[simp]

中文:
定理 linearEquivFunOnFintype_lof
  条件: [Fintype ι] (i : ι) (m : M i)
  证明: by
  rfl

@[simp]
-/
theorem linearEquivFunOnFintype_lof [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M) (lof R ι M i m) = Pi.single i m := by
  rfl

@[simp]
/--
theorem `linearEquivFunOnFintype_symm_single` / 定理 `linearEquivFunOnFintype_symm_single`

English:
theorem linearEquivFunOnFintype_symm_single
  given: [Fintype ι] (i : ι) (m : M i)
  proof: DFinsupp.equivFunOnFintype_symm_single i m

中文:
定理 linearEquivFunOnFintype_symm_single
  条件: [Fintype ι] (i : ι) (m : M i)
  证明: DFinsupp.equivFunOnFintype_symm_single i m

Depends on / 依赖: DFinsupp, DFinsupp.equivFunOnFintype_symm_single, equivFunOnFintype_symm_single
-/
theorem linearEquivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m :=
  DFinsupp.equivFunOnFintype_symm_single i m

end DecidableEq

@[simp]
/--
theorem `linearEquivFunOnFintype_symm_coe` / 定理 `linearEquivFunOnFintype_symm_coe`

English:
theorem linearEquivFunOnFintype_symm_coe
  given: [Fintype ι] (f : ⨁ i, M i)
  proof: (linearEquivFunOnFintype R ι M).symm_apply_apply _

中文:
定理 linearEquivFunOnFintype_symm_coe
  条件: [Fintype ι] (f : ⨁ i, M i)
  证明: (linearEquivFunOnFintype R ι M).symm_apply_apply _

Depends on / 依赖: linearEquivFunOnFintype, symm_apply_apply
-/
theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (linearEquivFunOnFintype R ι M).symm f = f :=
  (linearEquivFunOnFintype R ι M).symm_apply_apply _

/--
Definition of `lid` / `lid` 的定义

English:
definition lid
  signature: (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι]
  body: { DirectSum.id M ι, toModule R ι M fun _ => LinearMap.id with }

中文:
定义 lid
  签名: (M : 类型v) (ι : 类型 := PUnit) [AddCommMonoid M] [Module R M] [Unique ι]
  定义体: { DirectSum.id M ι, toModule R ι M fun _ => LinearMap.id with }
-/
protected def lid (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun _ => LinearMap.id with }

/--
lemma `lid_apply` / 引理 `lid_apply`

English:
lemma lid_apply
  statement: {M : Type v} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
  proof: DirectSum.id_apply x

中文:
引理 lid_apply
  结论: {M : 类型v} {ι : 类型} [AddCommMonoid M] [Module R M] [Unique ι]
  证明: DirectSum.id_apply x
-/
@[simp] lemma lid_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
    (x : ⨁ _ : ι, M) : DirectSum.lid R M ι x = x default :=
  DirectSum.id_apply x

/--
lemma `lid_symm_apply` / 引理 `lid_symm_apply`

English:
lemma lid_symm_apply
  statement: {M : Type v} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
  proof: DirectSum.id_symm_apply x

中文:
引理 lid_symm_apply
  结论: {M : 类型v} {ι : 类型} [AddCommMonoid M] [Module R M] [Unique ι]
  证明: DirectSum.id_symm_apply x
-/
@[simp] lemma lid_symm_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
    (x : M) : (DirectSum.lid R M ι).symm x = lof R _ _ default x :=
  DirectSum.id_symm_apply x

/--
Definition of `component` / `component` 的定义

English:
definition component
  signature: (i : ι)
  body: DFinsupp.lapply i

中文:
定义 component
  签名: (i : ι)
  定义体: DFinsupp.lapply i

Depends on / 依赖: DFinsupp, DFinsupp.lapply, lapply
-/
def component (i : ι) : (⨁ i, M i) ->ₗ[R] M i :=
  DFinsupp.lapply i

variable {ι M}

/--
theorem `apply_eq_component` / 定理 `apply_eq_component`

English:
theorem apply_eq_component
  given: (f : ⨁ i, M i) (i : ι)
  statement: f i = component R ι M i f
  proof: rfl

中文:
定理 apply_eq_component
  条件: (f : ⨁ i, M i) (i : ι)
  结论: f i = component R ι M i f
  证明: rfl
-/
theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f := rfl

-- Note(kmill): `@[ext]` cannot prove `ext_iff` because `R` is not determined by `f` or `g`.
-- This is not useful as an `@[ext]` lemma as the `ext` tactic cannot infer `R`.
/--
theorem `ext_component` / 定理 `ext_component`

English:
theorem ext_component
  given: {f g : ⨁ i, M i} (h : forall i, component R ι M i f = component R ι M i g)
  proof: DFinsupp.ext h

中文:
定理 ext_component
  条件: {f g : ⨁ i, M i} (h : 对任意 i, component R ι M i f = component R ι M i g)
  证明: DFinsupp.ext h

Depends on / 依赖: DFinsupp, DFinsupp.ext
-/
theorem ext_component {f g : ⨁ i, M i} (h : forall i, component R ι M i f = component R ι M i g) :
    f = g :=
  DFinsupp.ext h

/--
theorem `ext_component_iff` / 定理 `ext_component_iff`

English:
theorem ext_component_iff
  given: {f g : ⨁ i, M i}
  proof: ⟨fun h _ => by rw [h], ext_component R⟩

@[simp]

中文:
定理 ext_component_iff
  条件: {f g : ⨁ i, M i}
  证明: ⟨fun h _ => by rw [h], ext_component R⟩

@[simp]

Depends on / 依赖: ext_component
-/
theorem ext_component_iff {f g : ⨁ i, M i} :
    f = g ↔ forall i, component R ι M i f = component R ι M i g :=
  ⟨fun h _ => by rw [h], ext_component R⟩

@[simp]
/--
theorem `lof_apply` / 定理 `lof_apply`

English:
theorem lof_apply
  given: [DecidableEq ι] (i : ι) (b : M i)
  statement: ((lof R ι M i) b) i = b
  proof: DFinsupp.single_eq_same

@[simp]

中文:
定理 lof_apply
  条件: [DecidableEq ι] (i : ι) (b : M i)
  结论: ((lof R ι M i) b) i = b
  证明: DFinsupp.single_eq_same

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.single_eq_same, single_eq_same
-/
theorem lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
  DFinsupp.single_eq_same

@[simp]
/--
theorem `component.lof_self` / 定理 `component.lof_self`

English:
theorem component.lof_self
  given: [DecidableEq ι] (i : ι) (b : M i)
  proof: lof_apply R i b

中文:
定理 component.lof_self
  条件: [DecidableEq ι] (i : ι) (b : M i)
  证明: lof_apply R i b

Depends on / 依赖: lof_apply
-/
theorem component.lof_self [DecidableEq ι] (i : ι) (b : M i) :
    component R ι M i ((lof R ι M i) b) = b :=
  lof_apply R i b

/--
theorem `component.of` / 定理 `component.of`

English:
theorem component.of
  given: [DecidableEq ι] (i j : ι) (b : M j)
  proof: DFinsupp.single_apply

中文:
定理 component.of
  条件: [DecidableEq ι] (i j : ι) (b : M j)
  证明: DFinsupp.single_apply

Depends on / 依赖: DFinsupp, DFinsupp.single_apply, single_apply
-/
theorem component.of [DecidableEq ι] (i j : ι) (b : M j) :
    component R ι M i ((lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0 :=
  DFinsupp.single_apply

/--
lemma `component_comp_lof` / 引理 `component_comp_lof`

English:
lemma component_comp_lof
  given: [DecidableEq ι] (i j : ι)
  proof: by
  aesop (add simp component.of)

@[simp]

中文:
引理 component_comp_lof
  条件: [DecidableEq ι] (i j : ι)
  证明: by
  aesop (add simp component.of)

@[simp]

Depends on / 依赖: component, component.of
-/
lemma component_comp_lof [DecidableEq ι] (i j : ι) :
    component R ι M i ∘ₗ lof R ι M j = if h : j = i then h ▸ .id else 0 := by
  aesop (add simp component.of)

@[simp]
/--
lemma `component_comp_lof_same` / 引理 `component_comp_lof_same`

English:
lemma component_comp_lof_same
  given: [DecidableEq ι] (i : ι)
  statement: component R ι M i ∘ₗ lof R ι M i = .id
  proof: by
  simp [component_comp_lof]

中文:
引理 component_comp_lof_same
  条件: [DecidableEq ι] (i : ι)
  结论: component R ι M i ∘ₗ lof R ι M i = .id
  证明: by
  simp [component_comp_lof]

Depends on / 依赖: component_comp_lof
-/
lemma component_comp_lof_same [DecidableEq ι] (i : ι) : component R ι M i ∘ₗ lof R ι M i = .id := by
  simp [component_comp_lof]

section map

variable {R} {N : ι -> Type*}

section AddCommMonoid
variable [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]

section
variable (f : forall i, M i ->+ N i)

/--
lemma `mker_map` / 引理 `mker_map`

English:
lemma mker_map
  proof: DFinsupp.mker_mapRangeAddMonoidHom f

中文:
引理 mker_map
  证明: DFinsupp.mker_mapRangeAddMonoidHom f

Depends on / 依赖: DFinsupp, DFinsupp.mker_mapRangeAddMonoidHom, mker_mapRangeAddMonoidHom
-/
lemma mker_map :
    AddMonoidHom.mker (map f) =
      (AddSubmonoid.pi Set.univ (fun i => AddMonoidHom.mker (f i))).comap (coeFnAddMonoidHom M) :=
  DFinsupp.mker_mapRangeAddMonoidHom f

/--
lemma `mrange_map` / 引理 `mrange_map`

English:
lemma mrange_map
  proof: DFinsupp.mrange_mapRangeAddMonoidHom f

中文:
引理 mrange_map
  证明: DFinsupp.mrange_mapRangeAddMonoidHom f

Depends on / 依赖: DFinsupp, DFinsupp.mrange_mapRangeAddMonoidHom, mrange_mapRangeAddMonoidHom
-/
lemma mrange_map :
    AddMonoidHom.mrange (map f) =
      (AddSubmonoid.pi Set.univ (fun i => AddMonoidHom.mrange (f i))).comap (coeFnAddMonoidHom N) :=
  DFinsupp.mrange_mapRangeAddMonoidHom f

end

variable (f : Π i, M i ->ₗ[R] N i)

/--
Definition of `lmap` / `lmap` 的定义

English:
definition lmap
  signature: : (⨁ i, M i) ->ₗ[R] ⨁ i, N i
  body: DFinsupp.mapRange.linearMap f

中文:
定义 lmap
  签名: : (⨁ i, M i) ->ₗ[R] ⨁ i, N i
  定义体: DFinsupp.mapRange.linearMap f

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.linearMap, linearMap, mapRange
-/
def lmap : (⨁ i, M i) ->ₗ[R] ⨁ i, N i := DFinsupp.mapRange.linearMap f

/--
theorem `lmap_apply` / 定理 `lmap_apply`

English:
theorem lmap_apply
  given: (x i)
  statement: lmap f x i = f i (x i)
  proof: rfl

中文:
定理 lmap_apply
  条件: (x i)
  结论: lmap f x i = f i (x i)
  证明: rfl
-/
@[simp] theorem lmap_apply (x i) : lmap f x i = f i (x i) := rfl

/--
lemma `lmap_of` / 引理 `lmap_of`

English:
lemma lmap_of
  given: [DecidableEq ι] (i : ι) (x : M i)
  proof: DFinsupp.mapRange_single (hf := fun _ => map_zero _)

中文:
引理 lmap_of
  条件: [DecidableEq ι] (i : ι) (x : M i)
  证明: DFinsupp.mapRange_single (hf := fun _ => map_zero _)
-/
@[simp] lemma lmap_of [DecidableEq ι] (i : ι) (x : M i) :
    lmap f (of M i x) = of N i (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)

/--
theorem `lmap_lof` / 定理 `lmap_lof`

English:
theorem lmap_lof
  given: [DecidableEq ι] (i) (x : M i)
  proof: DFinsupp.mapRange_single (hf := fun _ => map_zero _)

中文:
定理 lmap_lof
  条件: [DecidableEq ι] (i) (x : M i)
  证明: DFinsupp.mapRange_single (hf := fun _ => map_zero _)
-/
@[simp] theorem lmap_lof [DecidableEq ι] (i) (x : M i) :
    lmap f (lof R _ _ _ x) = lof R _ _ _ (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)

/--
lemma `lmap_id` / 引理 `lmap_id`

English:
lemma lmap_id
  proof: DFinsupp.mapRange.linearMap_id

中文:
引理 lmap_id
  证明: DFinsupp.mapRange.linearMap_id
-/
@[simp] lemma lmap_id :
    (lmap (fun i => LinearMap.id (R := R) (M := M i))) = LinearMap.id :=
  DFinsupp.mapRange.linearMap_id

/--
lemma `lmap_comp` / 引理 `lmap_comp`

English:
lemma lmap_comp
  statement: {K : ι -> Type*} [forall i, AddCommMonoid (K i)] [forall i, Module R (K i)]
  proof: DFinsupp.mapRange.linearMap_comp _ _

中文:
引理 lmap_comp
  结论: {K : ι -> 类型} [对任意 i, AddCommMonoid (K i)] [对任意 i, Module R (K i)]
  证明: DFinsupp.mapRange.linearMap_comp _ _
-/
@[simp] lemma lmap_comp {K : ι -> Type*} [forall i, AddCommMonoid (K i)] [forall i, Module R (K i)]
    (g : forall (i : ι), N i ->ₗ[R] K i) :
    (lmap (fun i => (g i) ∘ₗ (f i))) = (lmap g) ∘ₗ (lmap f) :=
  DFinsupp.mapRange.linearMap_comp _ _

/--
theorem `lmap_injective` / 定理 `lmap_injective`

English:
theorem lmap_injective
  statement: Function.Injective (lmap f) ↔ forall i, Function.Injective (f i)
  proof: by
  exact DFinsupp.mapRange_injective (hf := fun _ => map_zero _)

中文:
定理 lmap_injective
  结论: Function.Injective (lmap f) ↔ 对任意 i, Function.Injective (f i)
  证明: by
  exact DFinsupp.mapRange_injective (hf := fun _ => map_zero _)

Depends on / 依赖: DFinsupp, DFinsupp.mapRange_injective, mapRange_injective, map_zero
-/
theorem lmap_injective : Function.Injective (lmap f) ↔ forall i, Function.Injective (f i) := by
  exact DFinsupp.mapRange_injective (hf := fun _ => map_zero _)

/--
theorem `lmap_surjective` / 定理 `lmap_surjective`

English:
theorem lmap_surjective
  statement: Function.Surjective (lmap f) ↔ (forall i, Function.Surjective (f i))
  proof: by
  exact DFinsupp.mapRange_surjective (hf := fun _ => map_zero _)

中文:
定理 lmap_surjective
  结论: Function.Surjective (lmap f) ↔ (对任意 i, Function.Surjective (f i))
  证明: by
  exact DFinsupp.mapRange_surjective (hf := fun _ => map_zero _)

Depends on / 依赖: DFinsupp, DFinsupp.mapRange_surjective, mapRange_surjective, map_zero
-/
theorem lmap_surjective : Function.Surjective (lmap f) ↔ (forall i, Function.Surjective (f i)) := by
  exact DFinsupp.mapRange_surjective (hf := fun _ => map_zero _)

/--
lemma `lmap_eq_iff` / 引理 `lmap_eq_iff`

English:
lemma lmap_eq_iff
  given: (x y : ⨁ i, M i)
  proof: map_eq_iff (fun i => (f i).toAddMonoidHom) _ _

中文:
引理 lmap_eq_iff
  条件: (x y : ⨁ i, M i)
  证明: map_eq_iff (fun i => (f i).toAddMonoidHom) _ _

Depends on / 依赖: map_eq_iff, toAddMonoidHom
-/
lemma lmap_eq_iff (x y : ⨁ i, M i) :
    lmap f x = lmap f y ↔ forall i, f i (x i) = f i (y i) :=
  map_eq_iff (fun i => (f i).toAddMonoidHom) _ _

/--
lemma `toAddMonoidHom_lmap` / 引理 `toAddMonoidHom_lmap`

English:
lemma toAddMonoidHom_lmap
  proof: rfl

中文:
引理 toAddMonoidHom_lmap
  证明: rfl
-/
lemma toAddMonoidHom_lmap :
    (lmap f).toAddMonoidHom = map (fun i => (f i).toAddMonoidHom) :=
  rfl

/--
lemma `lmap_eq_map` / 引理 `lmap_eq_map`

English:
lemma lmap_eq_map
  given: (x : ⨁ i, M i)
  statement: lmap f x = map (fun i => (f i).toAddMonoidHom) x
  proof: rfl

中文:
引理 lmap_eq_map
  条件: (x : ⨁ i, M i)
  结论: lmap f x = map (fun i => (f i).toAddMonoidHom) x
  证明: rfl
-/
lemma lmap_eq_map (x : ⨁ i, M i) : lmap f x = map (fun i => (f i).toAddMonoidHom) x :=
  rfl

/--
lemma `ker_lmap` / 引理 `ker_lmap`

English:
lemma ker_lmap
  proof: DFinsupp.ker_mapRangeLinearMap f

中文:
引理 ker_lmap
  证明: DFinsupp.ker_mapRangeLinearMap f

Depends on / 依赖: DFinsupp, DFinsupp.ker_mapRangeLinearMap, ker_mapRangeLinearMap
-/
lemma ker_lmap :
    LinearMap.ker (lmap f) =
      (Submodule.pi Set.univ (fun i => LinearMap.ker (f i))).comap (DirectSum.coeFnLinearMap R) :=
  DFinsupp.ker_mapRangeLinearMap f

/--
lemma `range_lmap` / 引理 `range_lmap`

English:
lemma range_lmap
  proof: DFinsupp.range_mapRangeLinearMap f

中文:
引理 range_lmap
  证明: DFinsupp.range_mapRangeLinearMap f

Depends on / 依赖: DFinsupp, DFinsupp.range_mapRangeLinearMap, range_mapRangeLinearMap
-/
lemma range_lmap :
    LinearMap.range (lmap f) =
      (Submodule.pi Set.univ (fun i => LinearMap.range (f i))).comap (DirectSum.coeFnLinearMap R) :=
  DFinsupp.range_mapRangeLinearMap f

end AddCommMonoid

section AddCommGroup
variable {R : Type u} {ι : Type v} {M : ι -> Type w} {N : ι -> Type*}

/--
lemma `ker_map` / 引理 `ker_map`

English:
lemma ker_map
  given: [forall i, AddCommGroup (M i)] [forall i, AddCommMonoid (N i)] (f : forall i, M i ->+ N i)
  proof: DFinsupp.ker_mapRangeAddMonoidHom f

中文:
引理 ker_map
  条件: [对任意 i, AddCommGroup (M i)] [对任意 i, AddCommMonoid (N i)] (f : 对任意 i, M i ->+ N i)
  证明: DFinsupp.ker_mapRangeAddMonoidHom f

Depends on / 依赖: DFinsupp, DFinsupp.ker_mapRangeAddMonoidHom, ker_mapRangeAddMonoidHom
-/
lemma ker_map [forall i, AddCommGroup (M i)] [forall i, AddCommMonoid (N i)] (f : forall i, M i ->+ N i) :
    (map f).ker =
      (AddSubgroup.pi Set.univ (f · |>.ker)).comap (DirectSum.coeFnAddMonoidHom M) :=
  DFinsupp.ker_mapRangeAddMonoidHom f

/--
lemma `range_map` / 引理 `range_map`

English:
lemma range_map
  given: [forall i, AddCommGroup (M i)] [forall i, AddCommGroup (N i)] (f : forall i, M i ->+ N i)
  proof: DFinsupp.range_mapRangeAddMonoidHom f

中文:
引理 range_map
  条件: [对任意 i, AddCommGroup (M i)] [对任意 i, AddCommGroup (N i)] (f : 对任意 i, M i ->+ N i)
  证明: DFinsupp.range_mapRangeAddMonoidHom f

Depends on / 依赖: DFinsupp, DFinsupp.range_mapRangeAddMonoidHom, range_mapRangeAddMonoidHom
-/
lemma range_map [forall i, AddCommGroup (M i)] [forall i, AddCommGroup (N i)] (f : forall i, M i ->+ N i) :
    (map f).range =
      (AddSubgroup.pi Set.univ (f · |>.range)).comap (DirectSum.coeFnAddMonoidHom N) :=
  DFinsupp.range_mapRangeAddMonoidHom f

end AddCommGroup

end map

section CongrLeft

variable {κ : Type*}

/--
Definition of `lequivCongrLeft` / `lequivCongrLeft` 的定义

English:
definition lequivCongrLeft
  signature: (h : ι ≃ κ)
  body: DFinsupp.domLCongr h

@[simp]

中文:
定义 lequivCongrLeft
  签名: (h : ι ≃ κ)
  定义体: DFinsupp.domLCongr h

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.domLCongr, domLCongr
-/
def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) :=
  DFinsupp.domLCongr h

@[simp]
/--
theorem `lequivCongrLeft_apply` / 定理 `lequivCongrLeft_apply`

English:
theorem lequivCongrLeft_apply
  given: (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ)
  proof: equivCongrLeft_apply _ _ _

中文:
定理 lequivCongrLeft_apply
  条件: (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ)
  证明: equivCongrLeft_apply _ _ _

Depends on / 依赖: equivCongrLeft_apply
-/
theorem lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) :
    lequivCongrLeft R h f k = f (h.symm k) :=
  equivCongrLeft_apply _ _ _

-- We need to try very hard to avoid dependent type "issues".
/--
lemma `lequivCongrLeft_lof` / 引理 `lequivCongrLeft_lof`

English:
lemma lequivCongrLeft_lof
  statement: [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ}
  proof: by
  subst hik hxy
  ext j
  simp [lof_eq_of, of_apply]
  lia

中文:
引理 lequivCongrLeft_lof
  结论: [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ}
  证明: by
  subst hik hxy
  ext j
  simp [lof_eq_of, of_apply]
  lia

Depends on / 依赖: lof_eq_of, of_apply
-/
lemma lequivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ}
    {i : ι} {k : κ} (hik : i = e.symm k)
    (x : M i) (y : M (e.symm k)) (hxy : cast congr(M $hik) x = y) :
    lequivCongrLeft R e (lof R ι M i x) = lof R _ _ k y := by
  subst hik hxy
  ext j
  simp [lof_eq_of, of_apply]
  lia

/--
lemma `lequivCongrLeft_symm_lof` / 引理 `lequivCongrLeft_symm_lof`

English:
lemma lequivCongrLeft_symm_lof
  statement: [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
  proof: by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact lequivCongrLeft_lof _ rfl _ _ rfl

中文:
引理 lequivCongrLeft_symm_lof
  结论: [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
  证明: by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact lequivCongrLeft_lof _ rfl _ _ rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, lequivCongrLeft_lof, symm_apply_eq
-/
lemma lequivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
    {k : κ} {x : M (h.symm k)} :
    (lequivCongrLeft R h).symm (lof R κ (fun k => M (h.symm k)) k x) = lof R ι M (h.symm k) x := by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact lequivCongrLeft_lof _ rfl _ _ rfl

end CongrLeft

section Sigma

variable {α : ι -> Type*} {δ : forall i, α i -> Type w}
variable [DecidableEq ι] [forall i j, AddCommMonoid (δ i j)] [forall i j, Module R (δ i j)]

/--
Definition of `sigmaLcurry` / `sigmaLcurry` 的定义

English:
definition sigmaLcurry
  signature: : (⨁ i : Σ _, _, δ i.1 i.2) ->ₗ[R] ⨁ (i) (j), δ i j
  body: { sigmaCurry with map_smul' := fun r => by convert! DFinsupp.sigmaCurry_smul (δ := δ) r }

@[simp]

中文:
定义 sigmaLcurry
  签名: : (⨁ i : Σ _, _, δ i.1 i.2) ->ₗ[R] ⨁ (i) (j), δ i j
  定义体: { sigmaCurry with map_smul' := fun r => by convert! DFinsupp.sigmaCurry_smul (δ := δ) r }

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurry_smul, convert, map_smul, sigmaCurry, sigmaCurry_smul
-/
def sigmaLcurry : (⨁ i : Σ _, _, δ i.1 i.2) ->ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with map_smul' := fun r => by convert! DFinsupp.sigmaCurry_smul (δ := δ) r }

@[simp]
/--
theorem `sigmaLcurry_apply` / 定理 `sigmaLcurry_apply`

English:
theorem sigmaLcurry_apply
  given: (f : ⨁ i : Σ _, _, δ i.1 i.2) (i : ι) (j : α i)
  proof: sigmaCurry_apply f i j

中文:
定理 sigmaLcurry_apply
  条件: (f : ⨁ i : Σ _, _, δ i.1 i.2) (i : ι) (j : α i)
  证明: sigmaCurry_apply f i j

Depends on / 依赖: sigmaCurry_apply
-/
theorem sigmaLcurry_apply (f : ⨁ i : Σ _, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaLcurry R f i j = f ⟨i, j⟩ :=
  sigmaCurry_apply f i j

/--
Definition of `sigmaLuncurry` / `sigmaLuncurry` 的定义

English:
definition sigmaLuncurry
  signature: : (⨁ (i) (j), δ i j) ->ₗ[R] ⨁ i : Σ _, _, δ i.1 i.2
  body: { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }

@[simp]

中文:
定义 sigmaLuncurry
  签名: : (⨁ (i) (j), δ i j) ->ₗ[R] ⨁ i : Σ _, _, δ i.1 i.2
  定义体: { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sigmaUncurry_smul, map_smul, sigmaUncurry, sigmaUncurry_smul
-/
def sigmaLuncurry : (⨁ (i) (j), δ i j) ->ₗ[R] ⨁ i : Σ _, _, δ i.1 i.2 :=
  { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }

@[simp]
/--
theorem `sigmaLuncurry_apply` / 定理 `sigmaLuncurry_apply`

English:
theorem sigmaLuncurry_apply
  given: (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i)
  proof: sigmaUncurry_apply f i j

中文:
定理 sigmaLuncurry_apply
  条件: (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i)
  证明: sigmaUncurry_apply f i j

Depends on / 依赖: sigmaUncurry_apply
-/
theorem sigmaLuncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaLuncurry R f ⟨i, j⟩ = f i j :=
  sigmaUncurry_apply f i j

/--
Definition of `sigmaLcurryEquiv` / `sigmaLcurryEquiv` 的定义

English:
definition sigmaLcurryEquiv
  signature: : (⨁ i : Σ _, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j
  body: DFinsupp.sigmaCurryLEquiv

中文:
定义 sigmaLcurryEquiv
  签名: : (⨁ i : Σ _, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j
  定义体: DFinsupp.sigmaCurryLEquiv

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurryLEquiv, sigmaCurryLEquiv
-/
def sigmaLcurryEquiv : (⨁ i : Σ _, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j :=
  DFinsupp.sigmaCurryLEquiv

end Sigma

section Option

variable {α : Option ι -> Type w} [forall i, AddCommMonoid (α i)] [forall i, Module R (α i)]

/-- Linear isomorphism obtained by separating the term of index `none` of a direct sum over
`Option ι`. -/
@[simps]
/--
Definition of `lequivProdDirectSum` / `lequivProdDirectSum` 的定义

English:
definition lequivProdDirectSum
  signature: : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i)
  body: { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }

中文:
定义 lequivProdDirectSum
  签名: : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i)
  定义体: { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }

Depends on / 依赖: DFinsupp, DFinsupp.equivProdDFinsupp_smul, addEquivProdDirectSum, equivProdDFinsupp_smul, map_smul
-/
noncomputable def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }

end Option

end General

section Submodule

section Semiring

variable {R : Type u} [Semiring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (A : ι -> Submodule R M)

/--
Definition of `coeLinearMap` / `coeLinearMap` 的定义

English:
definition coeLinearMap
  signature: : (⨁ i, A i) ->ₗ[R] M
  body: toModule R ι M fun i => (A i).subtype

中文:
定义 coeLinearMap
  签名: : (⨁ i, A i) ->ₗ[R] M
  定义体: toModule R ι M fun i => (A i).subtype

Depends on / 依赖: subtype, toModule
-/
def coeLinearMap : (⨁ i, A i) ->ₗ[R] M :=
  toModule R ι M fun i => (A i).subtype

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeLinearMap_eq_dfinsuppSum` / 定理 `coeLinearMap_eq_dfinsuppSum`

English:
theorem coeLinearMap_eq_dfinsuppSum
  given: [DecidableEq M] (x : DirectSum ι fun i => A i)
  proof: by
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]

@[simp]

中文:
定理 coeLinearMap_eq_dfinsuppSum
  条件: [DecidableEq M] (x : DirectSum ι fun i => A i)
  证明: by
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]

@[simp]

Depends on / 依赖: AddHom, AddHom.coe_mk, DFinsupp, DFinsupp.lsum, DFinsupp.sumAddHom_apply, LinearEquiv, LinearEquiv.coe_mk, LinearMap, LinearMap.coe_mk, LinearMap.toAddMonoidHom_coe, Submodule, Submodule.coe_subtype, coeLinearMap, coe_mk, coe_subtype, sumAddHom_apply, toAddMonoidHom_coe, toModule
-/
theorem coeLinearMap_eq_dfinsuppSum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]

@[simp]
/--
theorem `coeLinearMap_of` / 定理 `coeLinearMap_of`

English:
theorem coeLinearMap_of
  given: (i : ι) (x : A i)
  statement: DirectSum.coeLinearMap A (of (fun i => A i) i x) = x
  proof: -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i => ((A i).subtype : A i ->+ M)) i x

中文:
定理 coeLinearMap_of
  条件: (i : ι) (x : A i)
  结论: DirectSum.coeLinearMap A (of (fun i => A i) i x) = x
  证明: -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i => ((A i).subtype : A i ->+ M)) i x
-/
theorem coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i => A i) i x) = x :=
  -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i => ((A i).subtype : A i ->+ M)) i x

/--
lemma `coeLinearMap_lof` / 引理 `coeLinearMap_lof`

English:
lemma coeLinearMap_lof
  given: (i : ι) (x : A i)
  proof: coeLinearMap_of A i x

中文:
引理 coeLinearMap_lof
  条件: (i : ι) (x : A i)
  证明: coeLinearMap_of A i x
-/
@[simp] lemma coeLinearMap_lof (i : ι) (x : A i) :
    DirectSum.coeLinearMap A (lof R ι (fun i => A i) i x) = x :=
  coeLinearMap_of A i x

variable {A}

/--
theorem `range_coeLinearMap` / 定理 `range_coeLinearMap`

English:
theorem range_coeLinearMap
  statement: LinearMap.range (coeLinearMap A) = ⨆ i, A i
  proof: (Submodule.iSup_eq_range_dfinsupp_lsum _).symm

中文:
定理 range_coeLinearMap
  结论: LinearMap.range (coeLinearMap A) = ⨆ i, A i
  证明: (Submodule.iSup_eq_range_dfinsupp_lsum _).symm

Depends on / 依赖: Submodule, Submodule.iSup_eq_range_dfinsupp_lsum, iSup_eq_range_dfinsupp_lsum
-/
theorem range_coeLinearMap : LinearMap.range (coeLinearMap A) = ⨆ i, A i :=
  (Submodule.iSup_eq_range_dfinsupp_lsum _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `IsInternal.ofBijective_coeLinearMap_same` / 定理 `IsInternal.ofBijective_coeLinearMap_same`

English:
theorem IsInternal.ofBijective_coeLinearMap_same
  statement: (h : IsInternal A)
  proof: by
  rw [← coeLinearMap_of]; rw [LinearEquiv.ofBijective_symm_apply_apply]; rw [of_eq_same]

中文:
定理 IsInternal.ofBijective_coeLinearMap_same
  结论: (h : Is整数ernal A)
  证明: by
  rw [← coeLinearMap_of]; rw [LinearEquiv.ofBijective_symm_apply_apply]; rw [of_eq_same]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective_symm_apply_apply, coeLinearMap_of, ofBijective_symm_apply_apply, of_eq_same
-/
theorem IsInternal.ofBijective_coeLinearMap_same (h : IsInternal A)
    {i : ι} (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = x := by
  rw [← coeLinearMap_of]; rw [LinearEquiv.ofBijective_symm_apply_apply]; rw [of_eq_same]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `IsInternal.ofBijective_coeLinearMap_of_ne` / 定理 `IsInternal.ofBijective_coeLinearMap_of_ne`

English:
theorem IsInternal.ofBijective_coeLinearMap_of_ne
  statement: (h : IsInternal A)
  proof: by
  rw [← coeLinearMap_of]; rw [LinearEquiv.ofBijective_symm_apply_apply]; rw [of_eq_of_ne i j _ hij.symm]

中文:
定理 IsInternal.ofBijective_coeLinearMap_of_ne
  结论: (h : Is整数ernal A)
  证明: by
  rw [← coeLinearMap_of]; rw [LinearEquiv.ofBijective_symm_apply_apply]; rw [of_eq_of_ne i j _ hij.symm]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective_symm_apply_apply, coeLinearMap_of, hij.symm, ofBijective_symm_apply_apply, of_eq_of_ne
-/
theorem IsInternal.ofBijective_coeLinearMap_of_ne (h : IsInternal A)
    {i j : ι} (hij : i != j) (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 := by
  rw [← coeLinearMap_of]; rw [LinearEquiv.ofBijective_symm_apply_apply]; rw [of_eq_of_ne i j _ hij.symm]

/--
theorem `IsInternal.ofBijective_coeLinearMap_of_mem` / 定理 `IsInternal.ofBijective_coeLinearMap_of_mem`

English:
theorem IsInternal.ofBijective_coeLinearMap_of_mem
  statement: (h : IsInternal A)
  proof: h.ofBijective_coeLinearMap_same ⟨x, hx⟩

中文:
定理 IsInternal.ofBijective_coeLinearMap_of_mem
  结论: (h : Is整数ernal A)
  证明: h.ofBijective_coeLinearMap_same ⟨x, hx⟩

Depends on / 依赖: IntFractPair, IntFractPair.stream_succ_of_some, _intFractPair_stream, _of_eq_some_of_succ_get, h.ofBijective_coeLinearMap_same, nth_fr_ne_zero, ofBijective_coeLinearMap_same, stream_nth_eq, stream_succ_of_some
-/
theorem IsInternal.ofBijective_coeLinearMap_of_mem (h : IsInternal A)
    {i : ι} {x : M} (hx : x in A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = ⟨x, hx⟩ :=
  h.ofBijective_coeLinearMap_same ⟨x, hx⟩

/--
theorem `IsInternal.ofBijective_coeLinearMap_of_mem_ne` / 定理 `IsInternal.ofBijective_coeLinearMap_of_mem_ne`

English:
theorem IsInternal.ofBijective_coeLinearMap_of_mem_ne
  statement: (h : IsInternal A)
  proof: h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩

中文:
定理 IsInternal.ofBijective_coeLinearMap_of_mem_ne
  结论: (h : Is整数ernal A)
  证明: h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩

Depends on / 依赖: h.ofBijective_coeLinearMap_of_ne, ofBijective_coeLinearMap_of_ne
-/
theorem IsInternal.ofBijective_coeLinearMap_of_mem_ne (h : IsInternal A)
    {i j : ι} (hij : i != j) {x : M} (hx : x in A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 :=
  h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩

/--
theorem `IsInternal.submodule_iSup_eq_top` / 定理 `IsInternal.submodule_iSup_eq_top`

English:
theorem IsInternal.submodule_iSup_eq_top
  given: (h : IsInternal A)
  statement: iSup A = ⊤
  proof: by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum]; rw [LinearMap.range_eq_top]
  exact Function.Bijective.surjective h

中文:
定理 IsInternal.submodule_iSup_eq_top
  条件: (h : Is整数ernal A)
  结论: iSup A = ⊤
  证明: by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum]; rw [LinearMap.range_eq_top]
  exact Function.Bijective.surjective h

Depends on / 依赖: Bijective, Function, Function.Bijective.surjective, LinearMap, LinearMap.range_eq_top, Submodule, Submodule.iSup_eq_range_dfinsupp_lsum, iSup_eq_range_dfinsupp_lsum, range_eq_top, surjective
-/
theorem IsInternal.submodule_iSup_eq_top (h : IsInternal A) : iSup A = ⊤ := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum]; rw [LinearMap.range_eq_top]
  exact Function.Bijective.surjective h

/--
theorem `IsInternal.submodule_iSupIndep` / 定理 `IsInternal.submodule_iSupIndep`

English:
theorem IsInternal.submodule_iSupIndep
  given: (h : IsInternal A)
  statement: iSupIndep A
  proof: iSupIndep_of_dfinsupp_lsum_injective _ h.injective

中文:
定理 IsInternal.submodule_iSupIndep
  条件: (h : Is整数ernal A)
  结论: iSupIndep A
  证明: iSupIndep_of_dfinsupp_lsum_injective _ h.injective

Depends on / 依赖: h.injective, iSupIndep_of_dfinsupp_lsum_injective, injective
-/
theorem IsInternal.submodule_iSupIndep (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_lsum_injective _ h.injective

/--
Definition of `IsInternal.collectedBasis` / `IsInternal.collectedBasis` 的定义

English:
definition IsInternal.collectedBasis
  signature: (h : IsInternal A) {α : ι -> Type*}
  body: ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i => (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm

中文:
定义 IsInternal.collectedBasis
  签名: (h : Is整数ernal A) {α : ι -> 类型}
  定义体: ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i => (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.linearEquiv, DirectSum, DirectSum.coeLinearMap, LinearEquiv, LinearEquiv.ofBijective, coeLinearMap, linearEquiv, mapRange, ofBijective, sigmaFinsuppLequivDFinsupp
-/
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι -> Type*}
    (v : forall i, Basis (α i) R (A i)) : Basis (Σ i, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i => (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `IsInternal.collectedBasis_coe` / 定理 `IsInternal.collectedBasis_coe`

English:
theorem IsInternal.collectedBasis_coe
  statement: (h : IsInternal A) {α : ι -> Type*}
  proof: by
  simp [IsInternal.collectedBasis, coeLinearMap, DFinsupp.mapRange.linearEquiv,
    toModule, DFinsupp.lsum]

中文:
定理 IsInternal.collectedBasis_coe
  结论: (h : Is整数ernal A) {α : ι -> 类型}
  证明: by
  simp [IsInternal.collectedBasis, coeLinearMap, DFinsupp.mapRange.linearEquiv,
    toModule, DFinsupp.lsum]

Depends on / 依赖: DFinsupp, DFinsupp.lsum, DFinsupp.mapRange.linearEquiv, IsInternal, IsInternal.collectedBasis, coeLinearMap, collectedBasis, linearEquiv, mapRange, toModule
-/
theorem IsInternal.collectedBasis_coe (h : IsInternal A) {α : ι -> Type*}
    (v : forall i, Basis (α i) R (A i)) : ⇑(h.collectedBasis v) = fun a : Σ i, α i => ↑(v a.1 a.2) := by
  simp [IsInternal.collectedBasis, coeLinearMap, DFinsupp.mapRange.linearEquiv,
    toModule, DFinsupp.lsum]

/--
theorem `IsInternal.collectedBasis_mem` / 定理 `IsInternal.collectedBasis_mem`

English:
theorem IsInternal.collectedBasis_mem
  statement: (h : IsInternal A) {α : ι -> Type*}
  proof: by simp

中文:
定理 IsInternal.collectedBasis_mem
  结论: (h : Is整数ernal A) {α : ι -> 类型}
  证明: by simp

Depends on / 依赖: Aux_succ_none, Seq.get, Stream, _eq_h, _nil, add_eq_left, floor_intCast, of_h_eq_floor, of_s_of_int, zeroth_conv
-/
theorem IsInternal.collectedBasis_mem (h : IsInternal A) {α : ι -> Type*}
    (v : forall i, Basis (α i) R (A i)) (a : Σ i, α i) : h.collectedBasis v a in A a.1 := by simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsInternal.collectedBasis_repr_of_mem` / 定理 `IsInternal.collectedBasis_repr_of_mem`

English:
theorem IsInternal.collectedBasis_repr_of_mem
  statement: (h : IsInternal A) {α : ι -> Type*}
  proof: by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i => map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]

中文:
定理 IsInternal.collectedBasis_repr_of_mem
  结论: (h : Is整数ernal A) {α : ι -> 类型}
  证明: by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i => map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]

Depends on / 依赖: Aux_succ_some, DFinsupp, DFinsupp.mapRange, _of_int, add_right_inj, add_zero, cast_zero, congr_arg, div_zero, eq_of_sub_eq_zero, eq_or_ne, floor_intCast, fract_intCast, h.ofBijective_coeLinearMap_of_mem, inv_zero, mapRange, map_zero, ofBijective_coeLinearMap_of_mem, of_h_eq_floor, of_s_head
-/
theorem IsInternal.collectedBasis_repr_of_mem (h : IsInternal A) {α : ι -> Type*}
    (v : forall i, Basis (α i) R (A i)) {x : M} {i : ι} {a : α i} (hx : x in A i) :
    (h.collectedBasis v).repr x ⟨i, a⟩ = (v i).repr ⟨x, hx⟩ a := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i => map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsInternal.collectedBasis_repr_of_mem_ne` / 定理 `IsInternal.collectedBasis_repr_of_mem_ne`

English:
theorem IsInternal.collectedBasis_repr_of_mem_ne
  statement: (h : IsInternal A) {α : ι -> Type*}
  proof: by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i => map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

中文:
定理 IsInternal.collectedBasis_repr_of_mem_ne
  结论: (h : Is整数ernal A) {α : ι -> 类型}
  证明: by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i => map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

Depends on / 依赖: DFinsupp, DFinsupp.mapRange, h.ofBijective_coeLinearMap_of_mem_ne, mapRange, map_zero, ofBijective_coeLinearMap_of_mem_ne, sigmaFinsuppLequivDFinsupp
-/
theorem IsInternal.collectedBasis_repr_of_mem_ne (h : IsInternal A) {α : ι -> Type*}
    (v : forall i, Basis (α i) R (A i)) {x : M} {i j : ι} (hij : i != j) {a : α j} (hx : x in A i) :
    (h.collectedBasis v).repr x ⟨j, a⟩ = 0 := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i => map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

/--
theorem `IsInternal.isCompl` / 定理 `IsInternal.isCompl`

English:
theorem IsInternal.isCompl
  statement: {A : ι -> Submodule R M} {i j : ι} (hij : i != j)
  proof: ⟨hi.submodule_iSupIndep.pairwiseDisjoint hij,
codisjoint_iff.mpr Eq.symm hi.submodule_iSup_eq_top.symm.trans by
      rw [← sSup_pair]; rw [iSup]; rw [← Set.image_univ]; rw [h]; rw [Set.image_insert_eq]; rw [Set.image_singleton]⟩

中文:
定理 IsInternal.isCompl
  结论: {A : ι -> Submodule R M} {i j : ι} (hij : i != j)
  证明: ⟨hi.submodule_iSupIndep.pairwiseDisjoint hij,
codisjoint_iff.mpr Eq.symm hi.submodule_iSup_eq_top.symm.trans by
      rw [← sSup_pair]; rw [iSup]; rw [← Set.image_univ]; rw [h]; rw [Set.image_insert_eq]; rw [Set.image_singleton]⟩

Depends on / 依赖: Eq.symm, Set.image_insert_eq, Set.image_singleton, Set.image_univ, codisjoint_iff, codisjoint_iff.mpr, hi.submodule_iSupIndep.pairwiseDisjoint, hi.submodule_iSup_eq_top.symm.trans, image_insert_eq, image_singleton, image_univ, pairwiseDisjoint, sSup_pair, submodule_iSupIndep, submodule_iSup_eq_top
-/
theorem IsInternal.isCompl {A : ι -> Submodule R M} {i j : ι} (hij : i != j)
    (h : (Set.univ : Set ι) = {i, j}) (hi : IsInternal A) : IsCompl (A i) (A j) :=
  ⟨hi.submodule_iSupIndep.pairwiseDisjoint hij,
codisjoint_iff.mpr Eq.symm hi.submodule_iSup_eq_top.symm.trans by
      rw [← sSup_pair]; rw [iSup]; rw [← Set.image_univ]; rw [h]; rw [Set.image_insert_eq]; rw [Set.image_singleton]⟩

end Semiring

section Ring

variable {R : Type u} [Ring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

/--
theorem `isInternal_submodule_of_iSupIndep_of_iSup_eq_top` / 定理 `isInternal_submodule_of_iSupIndep_of_iSup_eq_top`

English:
theorem isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  statement: {A : ι -> Submodule R M}
  proof: ⟨hi.dfinsupp_lsum_injective,
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify value of `f`
(LinearMap.range_eq_top (f := DFinsupp.lsum _ _)).1
      (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans hs⟩

中文:
定理 isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  结论: {A : ι -> Submodule R M}
  证明: ⟨hi.dfinsupp_lsum_injective,
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify value of `f`
(LinearMap.range_eq_top (f := DFinsupp.lsum _ _)).1
      (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans hs⟩

Depends on / 依赖: dfinsupp_lsum_injective, hi.dfinsupp_lsum_injective
-/
theorem isInternal_submodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M}
    (hi : iSupIndep A) (hs : iSup A = ⊤) : IsInternal A :=
  ⟨hi.dfinsupp_lsum_injective,
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify value of `f`
(LinearMap.range_eq_top (f := DFinsupp.lsum _ _)).1
      (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans hs⟩

/--
theorem `isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` / 定理 `isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`

English:
theorem isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
  given: (A : ι -> Submodule R M)
  proof: ⟨fun i => ⟨i.submodule_iSupIndep, i.submodule_iSup_eq_top⟩,
    And.rec isInternal_submodule_of_iSupIndep_of_iSup_eq_top⟩

中文:
定理 isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
  条件: (A : ι -> Submodule R M)
  证明: ⟨fun i => ⟨i.submodule_iSupIndep, i.submodule_iSup_eq_top⟩,
    And.rec isInternal_submodule_of_iSupIndep_of_iSup_eq_top⟩

Depends on / 依赖: And.rec, i.submodule_iSupIndep, i.submodule_iSup_eq_top, isInternal_submodule_of_iSupIndep_of_iSup_eq_top, submodule_iSupIndep, submodule_iSup_eq_top
-/
theorem isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι -> Submodule R M) :
    IsInternal A ↔ iSupIndep A ∧ iSup A = ⊤ :=
  ⟨fun i => ⟨i.submodule_iSupIndep, i.submodule_iSup_eq_top⟩,
    And.rec isInternal_submodule_of_iSupIndep_of_iSup_eq_top⟩

/--
theorem `isInternal_submodule_iff_isCompl` / 定理 `isInternal_submodule_iff_isCompl`

English:
theorem isInternal_submodule_iff_isCompl
  statement: (A : ι -> Submodule R M) {i j : ι} (hij : i != j)
  proof: by
  have : forall k, k = i ∨ k = j := fun k => by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]; rw [iSup]; rw [← Set.image_univ]; rw [h]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [sSup_pair]; rw [iSupIndep_pair hij this]
  exact ⟨fun ⟨hd, ht

中文:
定理 isInternal_submodule_iff_isCompl
  结论: (A : ι -> Submodule R M) {i j : ι} (hij : i != j)
  证明: by
  have : forall k, k = i ∨ k = j := fun k => by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]; rw [iSup]; rw [← Set.image_univ]; rw [h]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [sSup_pair]; rw [iSupIndep_pair hij this]
  exact ⟨fun ⟨hd, ht

Depends on / 依赖: Set.ext_iff.mp, Set.image_insert_eq, Set.image_singleton, Set.image_univ, codisjoint_iff, codisjoint_iff.mpr, eq_top, ext_iff, ht.eq_top, iSupIndep_pair, image_insert_eq, image_singleton, image_univ, isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, sSup_pair
-/
theorem isInternal_submodule_iff_isCompl (A : ι -> Submodule R M) {i j : ι} (hij : i != j)
    (h : (Set.univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j) := by
  have : forall k, k = i ∨ k = j := fun k => by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]; rw [iSup]; rw [← Set.image_univ]; rw [h]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [sSup_pair]; rw [iSupIndep_pair hij this]
  exact ⟨fun ⟨hd, ht⟩ => ⟨hd, codisjoint_iff.mpr ht⟩, fun ⟨hd, ht⟩ => ⟨hd, ht.eq_top⟩⟩

@[simp]
/--
theorem `isInternal_ne_bot_iff` / 定理 `isInternal_ne_bot_iff`

English:
theorem isInternal_ne_bot_iff
  given: {A : ι -> Submodule R M}
  proof: by
  simp [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]

中文:
定理 isInternal_ne_bot_iff
  条件: {A : ι -> Submodule R M}
  证明: by
  simp [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]

Depends on / 依赖: isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
-/
theorem isInternal_ne_bot_iff {A : ι -> Submodule R M} :
    IsInternal (fun i : {i // A i != ⊥} => A i) ↔ IsInternal A := by
  simp [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]

/--
lemma `isInternal_biSup_submodule_of_iSupIndep` / 引理 `isInternal_biSup_submodule_of_iSupIndep`

English:
lemma isInternal_biSup_submodule_of_iSupIndep
  statement: {A : ι -> Submodule R M} (s : Set ι)
  proof: by
  refine (isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i in s, A i
  have hp : forall i in s, A i <= p := fun i hi => le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s => (A i).comap p.subtype) = fun i =

中文:
引理 isInternal_biSup_submodule_of_iSupIndep
  结论: {A : ι -> Submodule R M} (s : Set ι)
  证明: by
  refine (isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i in s, A i
  have hp : forall i in s, A i <= p := fun i hi => le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s => (A i).comap p.subtype) = fun i =

Depends on / 依赖: Set.Iic, Submodule, Submodule.map_comap_subtype, i.property, iSupIndep_map_orderIso_iff, iSup_subtype, inf_of_le_, isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, le_biSup, mapIic, map_comap_subtype, of_coe_Iic_comp, p.mapIic, p.subtype, property, subtype
-/
lemma isInternal_biSup_submodule_of_iSupIndep {A : ι -> Submodule R M} (s : Set ι)
    (h : iSupIndep <| fun i : s => A i) :
IsInternal fun (i : s) => (A i).comap (⨆ i in s, A i).subtype := by
  refine (isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i in s, A i
  have hp : forall i in s, A i <= p := fun i hi => le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s => (A i).comap p.subtype) = fun i => ⟨A i, hp i i.property⟩ by
    rw [← iSupIndep_map_orderIso_iff e]; rw [this]
    exact .of_coe_Iic_comp h
  ext i m
  change m in ((A i).comap p.subtype).map p.subtype ↔ _
  rw [Submodule.map_comap_subtype]; rw [inf_of_le_right (hp i i.property)]



/--
theorem `IsInternal.addSubmonoid_iSupIndep` / 定理 `IsInternal.addSubmonoid_iSupIndep`

English:
theorem IsInternal.addSubmonoid_iSupIndep
  statement: {M : Type*} [AddCommMonoid M] {A : ι -> AddSubmonoid M}
  proof: iSupIndep_of_dfinsuppSumAddHom_injective _ h.injective

中文:
定理 IsInternal.addSubmonoid_iSupIndep
  结论: {M : 类型} [AddCommMonoid M] {A : ι -> AddSubmonoid M}
  证明: iSupIndep_of_dfinsuppSumAddHom_injective _ h.injective

Depends on / 依赖: h.injective, iSupIndep_of_dfinsuppSumAddHom_injective, injective
-/
theorem IsInternal.addSubmonoid_iSupIndep {M : Type*} [AddCommMonoid M] {A : ι -> AddSubmonoid M}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsuppSumAddHom_injective _ h.injective

/--
theorem `IsInternal.addSubgroup_iSupIndep` / 定理 `IsInternal.addSubgroup_iSupIndep`

English:
theorem IsInternal.addSubgroup_iSupIndep
  statement: {G : Type*} [AddCommGroup G] {A : ι -> AddSubgroup G}
  proof: iSupIndep_of_dfinsuppSumAddHom_injective' _ h.injective

中文:
定理 IsInternal.addSubgroup_iSupIndep
  结论: {G : 类型} [AddCommGroup G] {A : ι -> AddSubgroup G}
  证明: iSupIndep_of_dfinsuppSumAddHom_injective' _ h.injective

Depends on / 依赖: h.injective, iSupIndep_of_dfinsuppSumAddHom_injective, injective
-/
theorem IsInternal.addSubgroup_iSupIndep {G : Type*} [AddCommGroup G] {A : ι -> AddSubgroup G}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsuppSumAddHom_injective' _ h.injective

end Ring

end Submodule

section Congr

variable {R : Type*} [Semiring R]
    {ι : Type*}
    {N : ι -> Type*} [(i : ι) -> AddCommMonoid (N i)] [(i : ι) -> Module R (N i)]
    {P : ι -> Type*} [forall i, AddCommMonoid (P i)] [forall i, Module R (P i)]

/--
Definition of `congrAddEquiv` / `congrAddEquiv` 的定义

English:
definition congrAddEquiv
  signature: (u : (i : ι) -> N i ≃+ P i)
  body: DirectSum.map fun i => (u i).toAddMonoidHom
  invFun := DirectSum.map fun i => (u i).symm.toAddMonoidHom
  left_inv x := by aesop
  right_inv y := by aesop

中文:
定义 congrAddEquiv
  签名: (u : (i : ι) -> N i ≃+ P i)
  定义体: DirectSum.map fun i => (u i).toAddMonoidHom
  invFun := DirectSum.map fun i => (u i).symm.toAddMonoidHom
  left_inv x := by aesop
  right_inv y := by aesop

Depends on / 依赖: DirectSum, DirectSum.map, toAddMonoidHom
-/
def congrAddEquiv (u : (i : ι) -> N i ≃+ P i) :
    (⨁ i, N i) ≃+ ⨁ i, P i where
  toAddHom := DirectSum.map fun i => (u i).toAddMonoidHom
  invFun := DirectSum.map fun i => (u i).symm.toAddMonoidHom
  left_inv x := by aesop
  right_inv y := by aesop

/--
theorem `coe_congrAddEquiv` / 定理 `coe_congrAddEquiv`

English:
theorem coe_congrAddEquiv
  given: (u : (i : ι) -> N i ≃+ P i)
  proof: rfl

中文:
定理 coe_congrAddEquiv
  条件: (u : (i : ι) -> N i ≃+ P i)
  证明: rfl
-/
theorem coe_congrAddEquiv (u : (i : ι) -> N i ≃+ P i) :
    ⇑(congrAddEquiv u).toAddMonoidHom = ⇑(DirectSum.map fun i => (u i).toAddMonoidHom) :=
  rfl

/--
Definition of `congrLinearEquiv` / `congrLinearEquiv` 的定义

English:
definition congrLinearEquiv
  signature: (u : (i : ι) -> N i ≃ₗ[R] P i)
  body: congrAddEquiv (fun i => (u i).toAddEquiv)
  map_smul' r x := by
    exact (DirectSum.lmap (fun i => (u i).toLinearMap)).map_smul r x

中文:
定义 congrLinearEquiv
  签名: (u : (i : ι) -> N i ≃ₗ[R] P i)
  定义体: congrAddEquiv (fun i => (u i).toAddEquiv)
  map_smul' r x := by
    exact (DirectSum.lmap (fun i => (u i).toLinearMap)).map_smul r x

Depends on / 依赖: congrAddEquiv, toAddEquiv
-/
def congrLinearEquiv (u : (i : ι) -> N i ≃ₗ[R] P i) :
    (⨁ i, N i) ≃ₗ[R] ⨁ i, P i where
  toAddEquiv := congrAddEquiv (fun i => (u i).toAddEquiv)
  map_smul' r x := by
    exact (DirectSum.lmap (fun i => (u i).toLinearMap)).map_smul r x

/--
theorem `coe_congrLinearEquiv` / 定理 `coe_congrLinearEquiv`

English:
theorem coe_congrLinearEquiv
  given: (u : (i : ι) -> N i ≃ₗ[R] P i)
  proof: rfl

中文:
定理 coe_congrLinearEquiv
  条件: (u : (i : ι) -> N i ≃ₗ[R] P i)
  证明: rfl
-/
theorem coe_congrLinearEquiv (u : (i : ι) -> N i ≃ₗ[R] P i) :
    ⇑(congrLinearEquiv u) = ⇑(DirectSum.lmap (fun i => (u i).toLinearMap)) :=
  rfl

/--
theorem `congrLinearEquiv_toAddEquiv` / 定理 `congrLinearEquiv_toAddEquiv`

English:
theorem congrLinearEquiv_toAddEquiv
  given: (u : (i : ι) -> N i ≃ₗ[R] P i)
  proof: rfl

中文:
定理 congrLinearEquiv_toAddEquiv
  条件: (u : (i : ι) -> N i ≃ₗ[R] P i)
  证明: rfl
-/
theorem congrLinearEquiv_toAddEquiv (u : (i : ι) -> N i ≃ₗ[R] P i) :
    (congrLinearEquiv u).toAddEquiv = congrAddEquiv (fun i => (u i).toAddEquiv) :=
  rfl

/--
theorem `congrLinearEquiv_toLinearMap` / 定理 `congrLinearEquiv_toLinearMap`

English:
theorem congrLinearEquiv_toLinearMap
  given: (u : (i : ι) -> N i ≃ₗ[R] P i)
  proof: rfl

中文:
定理 congrLinearEquiv_toLinearMap
  条件: (u : (i : ι) -> N i ≃ₗ[R] P i)
  证明: rfl
-/
theorem congrLinearEquiv_toLinearMap (u : (i : ι) -> N i ≃ₗ[R] P i) :
    (congrLinearEquiv u).toLinearMap = DirectSum.lmap (fun i => (u i).toLinearMap) :=
  rfl

end Congr

end DirectSum
