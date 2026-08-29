/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.UniformSpace.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-! # Type synonym for types with a `CStarModule` structure

It is often the case that we want to construct a `CStarModule` instance on a type that is already
endowed with a norm, but this norm is not the one associated to its `CStarModule` structure. For
this reason, we create a type synonym `WithCStarModule` which is endowed with the requisite
`CStarModule` instance. We also introduce the scoped notation `C⋆ᵐᵒᵈ` for this type synonym.

The common use cases are, when `A` is a C⋆-algebra:

+ `E × F` where `E` and `F` are `CStarModule`s over `A`
+ `Π i, E i` where `E i` is a `CStarModule` over `A` and `i : ι` with `ι` a `Fintype`

In this way, the set up is very similar to the `WithLp` type synonym, although there is no way to
reuse `WithLp` because the norms *do not* coincide in general.

The `WithCStarModule` synonym is of vital importance, especially because the `CStarModule` class
marks `A` as an `outParam`. Indeed, we want to infer `A` from the type of `E`, but, as with modules,
a type `E` can be a `CStarModule` over different C⋆-algebras. For example, note that if `A` is a
C⋆-algebra, then so is `A × A`, and therefore we may consider both `A` and `A × A` as `CStarModule`s
over themselves, respectively. However, we may *also* consider `A × A` as a `CStarModule` over `A`.
However, by utilizing the type synonym, these actually correspond to *different types*, namely:

+ `A` as a `CStarModule` over `A` corresponds to `A`
+ `A × A` as a `CStarModule` over `A × A` corresponds to `A × A`
+ `A × A` as a `CStarModule` over `A` corresponds to `C⋆ᵐᵒᵈ (A × A)`

## Main definitions

* `WithCStarModule A E`: a copy of `E` to be equipped with a `CStarModule A` structure.
* `WithCStarModule.equiv A E`: the canonical equivalence between `WithCStarModule A E` and `E`.
* `WithCStarModule.linearEquiv ℂ A E`: the canonical `ℂ`-module isomorphism between
  `WithCStarModule A E` and `E`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type, and allows all the structure-copying code to be shared.
-/

@[expose] public section

set_option linter.unusedVariables false in
/-- A type synonym for endowing a given type with a `CStarModule` structure. This has the scoped
notation `C⋆ᵐᵒᵈ`. -/
@[nolint unusedArguments]
/--
Definition of `WithCStarModule` / `WithCStarModule` 的定义

English:
definition WithCStarModule
  signature: (A E : Type*)
  body: E

中文:
定义 WithCStarModule
  签名: (A E : 类型)
  定义体: E
-/
def WithCStarModule (A E : Type*) := E

namespace WithCStarModule

@[inherit_doc]
scoped notation "C⋆ᵐᵒᵈ(" A ", " E ")" => WithCStarModule A E

section Basic

variable (R R' A E : Type*)

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : WithCStarModule A E ≃ E
  body: Equiv.refl _

中文:
定义 equiv
  签名: : WithCStarModule A E ≃ E
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def equiv : WithCStarModule A E ≃ E := Equiv.refl _

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial E]
  body: ‹Nontrivial E›

中文:
实例 instNontrivial
  签名: [Nontrivial E]
  定义体: ‹Nontrivial E›

Depends on / 依赖: Nontrivial
-/
instance instNontrivial [Nontrivial E] : Nontrivial C⋆ᵐᵒᵈ(A, E) := ‹Nontrivial E›
/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited E]
  body: ‹Inhabited E›

中文:
实例 instInhabited
  签名: [Inhabited E]
  定义体: ‹Inhabited E›

Depends on / 依赖: Inhabited
-/
instance instInhabited [Inhabited E] : Inhabited C⋆ᵐᵒᵈ(A, E) := ‹Inhabited E›
/--
Instance `instNonempty` / 实例 `instNonempty`

English:
instance instNonempty
  signature: [Nonempty E]
  body: ‹Nonempty E›

中文:
实例 instNonempty
  签名: [Nonempty E]
  定义体: ‹Nonempty E›

Depends on / 依赖: Nonempty
-/
instance instNonempty [Nonempty E] : Nonempty C⋆ᵐᵒᵈ(A, E) := ‹Nonempty E›
/--
Instance `instUnique` / 实例 `instUnique`

English:
instance instUnique
  signature: [Unique E]
  body: ‹Unique E›

中文:
实例 instUnique
  签名: [Unique E]
  定义体: ‹Unique E›

Depends on / 依赖: Unique
-/
instance instUnique [Unique E] : Unique C⋆ᵐᵒᵈ(A, E) := ‹Unique E›


/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero E]
  body: ‹Zero E›

中文:
实例 instZero
  签名: [Zero E]
  定义体: ‹Zero E›
-/
instance instZero [Zero E] : Zero C⋆ᵐᵒᵈ(A, E) := ‹Zero E›
/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [Add E]
  body: ‹Add E›

中文:
实例 instAdd
  签名: [Add E]
  定义体: ‹Add E›
-/
instance instAdd [Add E] : Add C⋆ᵐᵒᵈ(A, E) := ‹Add E›
/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: [Sub E]
  body: ‹Sub E›

中文:
实例 instSub
  签名: [Sub E]
  定义体: ‹Sub E›
-/
instance instSub [Sub E] : Sub C⋆ᵐᵒᵈ(A, E) := ‹Sub E›
/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [Neg E]
  body: ‹Neg E›

中文:
实例 instNeg
  签名: [Neg E]
  定义体: ‹Neg E›
-/
instance instNeg [Neg E] : Neg C⋆ᵐᵒᵈ(A, E) := ‹Neg E›
/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid E]
  body: ‹AddMonoid E›

中文:
实例 instAddMonoid
  签名: [AddMonoid E]
  定义体: ‹AddMonoid E›

Depends on / 依赖: AddMonoid
-/
instance instAddMonoid [AddMonoid E] : AddMonoid C⋆ᵐᵒᵈ(A, E) := ‹AddMonoid E›
/--
Instance `instSubNegMonoid` / 实例 `instSubNegMonoid`

English:
instance instSubNegMonoid
  signature: [SubNegMonoid E]
  body: ‹SubNegMonoid E›

中文:
实例 instSubNegMonoid
  签名: [SubNegMonoid E]
  定义体: ‹SubNegMonoid E›

Depends on / 依赖: SubNegMonoid
-/
instance instSubNegMonoid [SubNegMonoid E] : SubNegMonoid C⋆ᵐᵒᵈ(A, E) := ‹SubNegMonoid E›
/--
Instance `instSubNegZeroMonoid` / 实例 `instSubNegZeroMonoid`

English:
instance instSubNegZeroMonoid
  signature: [SubNegZeroMonoid E]
  body: ‹SubNegZeroMonoid E›

中文:
实例 instSubNegZeroMonoid
  签名: [SubNegZeroMonoid E]
  定义体: ‹SubNegZeroMonoid E›

Depends on / 依赖: SubNegZeroMonoid
-/
instance instSubNegZeroMonoid [SubNegZeroMonoid E] : SubNegZeroMonoid C⋆ᵐᵒᵈ(A, E) :=
  ‹SubNegZeroMonoid E›

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup E]
  body: ‹AddCommGroup E›

中文:
实例 instAddCommGroup
  签名: [AddCommGroup E]
  定义体: ‹AddCommGroup E›

Depends on / 依赖: AddCommGroup
-/
instance instAddCommGroup [AddCommGroup E] : AddCommGroup C⋆ᵐᵒᵈ(A, E) := ‹AddCommGroup E›

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {R : Type*} [SMul R E]
  body: ‹SMul R E›

中文:
实例 instSMul
  签名: {R : 类型} [SMul R E]
  定义体: ‹SMul R E›
-/
instance instSMul {R : Type*} [SMul R E] : SMul R C⋆ᵐᵒᵈ(A, E) := ‹SMul R E›

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {R : Type*} [Semiring R] [AddCommGroup E] [Module R E]
  body: ‹Module R E›

中文:
实例 instModule
  签名: {R : 类型} [Semiring R] [AddCommGroup E] [Module R E]
  定义体: ‹Module R E›

Depends on / 依赖: Module
-/
instance instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    Module R C⋆ᵐᵒᵈ(A, E) :=
  ‹Module R E›

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul R R'] [SMul R E] [SMul R' E]
  body: ‹IsScalarTower R R' E›

中文:
实例 instIsScalarTower
  签名: [SMul R R'] [SMul R E] [SMul R' E]
  定义体: ‹IsScalarTower R R' E›

Depends on / 依赖: IsScalarTower
-/
instance instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E]
    [IsScalarTower R R' E] : IsScalarTower R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹IsScalarTower R R' E›

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul R E] [SMul R' E] [SMulCommClass R R' E]
  body: ‹SMulCommClass R R' E›

中文:
实例 instSMulCommClass
  签名: [SMul R E] [SMul R' E] [SMulCommClass R R' E]
  定义体: ‹SMulCommClass R R' E›

Depends on / 依赖: SMulCommClass
-/
instance instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] :
    SMulCommClass R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹SMulCommClass R R' E›

section Equiv

variable {R A E}
variable [SMul R E] (c : R) (x y : C⋆ᵐᵒᵈ(A, E)) (x' y' : E)

/-! `WithCStarModule.equiv` preserves the module structure. -/

section AddCommGroup

variable [AddCommGroup E]

@[simp]
/--
theorem `equiv_zero` / 定理 `equiv_zero`

English:
theorem equiv_zero
  statement: equiv A E 0 = 0
  proof: rfl

@[simp]

中文:
定理 equiv_zero
  结论: equiv A E 0 = 0
  证明: rfl

@[simp]
-/
theorem equiv_zero : equiv A E 0 = 0 :=
  rfl

@[simp]
/--
theorem `equiv_symm_zero` / 定理 `equiv_symm_zero`

English:
theorem equiv_symm_zero
  statement: (equiv A E).symm 0 = 0
  proof: rfl

@[simp]

中文:
定理 equiv_symm_zero
  结论: (equiv A E).symm 0 = 0
  证明: rfl

@[simp]
-/
theorem equiv_symm_zero : (equiv A E).symm 0 = 0 :=
  rfl

@[simp]
/--
theorem `equiv_add` / 定理 `equiv_add`

English:
theorem equiv_add
  statement: equiv A E (x + y) = equiv A E x + equiv A E y
  proof: rfl

@[simp]

中文:
定理 equiv_add
  结论: equiv A E (x + y) = equiv A E x + equiv A E y
  证明: rfl

@[simp]
-/
theorem equiv_add : equiv A E (x + y) = equiv A E x + equiv A E y :=
  rfl

@[simp]
/--
theorem `equiv_symm_add` / 定理 `equiv_symm_add`

English:
theorem equiv_symm_add
  proof: rfl

@[simp]

中文:
定理 equiv_symm_add
  证明: rfl

@[simp]
-/
theorem equiv_symm_add :
    (equiv A E).symm (x' + y') = (equiv A E).symm x' + (equiv A E).symm y' :=
  rfl

@[simp]
/--
theorem `equiv_sub` / 定理 `equiv_sub`

English:
theorem equiv_sub
  statement: equiv A E (x - y) = equiv A E x - equiv A E y
  proof: rfl

@[simp]

中文:
定理 equiv_sub
  结论: equiv A E (x - y) = equiv A E x - equiv A E y
  证明: rfl

@[simp]
-/
theorem equiv_sub : equiv A E (x - y) = equiv A E x - equiv A E y :=
  rfl

@[simp]
/--
theorem `equiv_symm_sub` / 定理 `equiv_symm_sub`

English:
theorem equiv_symm_sub
  proof: rfl

@[simp]

中文:
定理 equiv_symm_sub
  证明: rfl

@[simp]
-/
theorem equiv_symm_sub :
    (equiv A E).symm (x' - y') = (equiv A E).symm x' - (equiv A E).symm y' :=
  rfl

@[simp]
/--
theorem `equiv_neg` / 定理 `equiv_neg`

English:
theorem equiv_neg
  statement: equiv A E (-x) = -equiv A E x
  proof: rfl

@[simp]

中文:
定理 equiv_neg
  结论: equiv A E (-x) = -equiv A E x
  证明: rfl

@[simp]
-/
theorem equiv_neg : equiv A E (-x) = -equiv A E x :=
  rfl

@[simp]
/--
theorem `equiv_symm_neg` / 定理 `equiv_symm_neg`

English:
theorem equiv_symm_neg
  statement: (equiv A E).symm (-x') = -(equiv A E).symm x'
  proof: rfl

中文:
定理 equiv_symm_neg
  结论: (equiv A E).symm (-x') = -(equiv A E).symm x'
  证明: rfl
-/
theorem equiv_symm_neg : (equiv A E).symm (-x') = -(equiv A E).symm x' :=
  rfl

end AddCommGroup

@[simp]
/--
theorem `equiv_smul` / 定理 `equiv_smul`

English:
theorem equiv_smul
  statement: equiv A E (c • x) = c • equiv A E x
  proof: rfl

@[simp]

中文:
定理 equiv_smul
  结论: equiv A E (c • x) = c • equiv A E x
  证明: rfl

@[simp]
-/
theorem equiv_smul : equiv A E (c • x) = c • equiv A E x :=
  rfl

@[simp]
/--
theorem `equiv_symm_smul` / 定理 `equiv_symm_smul`

English:
theorem equiv_symm_smul
  statement: (equiv A E).symm (c • x') = c • (equiv A E).symm x'
  proof: rfl

中文:
定理 equiv_symm_smul
  结论: (equiv A E).symm (c • x') = c • (equiv A E).symm x'
  证明: rfl
-/
theorem equiv_symm_smul : (equiv A E).symm (c • x') = c • (equiv A E).symm x' :=
  rfl

end Equiv

/--
Definition of `addEquiv` / `addEquiv` 的定义

English:
definition addEquiv
  signature: [AddCommGroup E]
  body: { AddEquiv.refl _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

中文:
定义 addEquiv
  签名: [AddCommGroup E]
  定义体: { AddEquiv.refl _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

Depends on / 依赖: AddEquiv, AddEquiv.refl, invFun
-/
def addEquiv [AddCommGroup E] : C⋆ᵐᵒᵈ(A, E) ≃+ E :=
  { AddEquiv.refl _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

/-- `WithCStarModule.equiv` as a linear equivalence. -/
@[simps -fullyApplied]
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: [Semiring R] [AddCommGroup E] [Module R E]
  body: { LinearEquiv.refl _ _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

中文:
定义 linearEquiv
  签名: [Semiring R] [AddCommGroup E] [Module R E]
  定义体: { LinearEquiv.refl _ _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, invFun
-/
def linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃ₗ[R] E :=
  { LinearEquiv.refl _ _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

/--
lemma `map_top_submodule` / 引理 `map_top_submodule`

English:
lemma map_top_submodule
  given: {R : Type*} [Semiring R] [AddCommGroup E] [Module R E]
  proof: Submodule.map_eq_top_iff.mpr rfl

中文:
引理 map_top_submodule
  条件: {R : 类型} [Semiring R] [AddCommGroup E] [Module R E]
  证明: Submodule.map_eq_top_iff.mpr rfl

Depends on / 依赖: Submodule, Submodule.map_eq_top_iff.mpr, map_eq_top_iff
-/
lemma map_top_submodule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    (⊤ : Submodule R E).map (linearEquiv R A E).symm.toLinearMap = ⊤ :=
  Submodule.map_eq_top_iff.mpr rfl

/--
Instance `instModuleFinite` / 实例 `instModuleFinite`

English:
instance instModuleFinite
  signature: [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E]
  body: ‹Module.Finite R E›

中文:
实例 instModuleFinite
  签名: [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E]
  定义体: ‹Module.Finite R E›

Depends on / 依赖: Finite, Module, Module.Finite
-/
instance instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E] :
    Module.Finite R C⋆ᵐᵒᵈ(A, E) := ‹Module.Finite R E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits the uniformity and bornology from `E`. -/

variable {A E}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [u
  signature: : UniformSpace E] : UniformSpace C⋆ᵐᵒᵈ(A, E)
  body: u.comap equiv A E

中文:
实例 [u
  签名: : UniformSpace E] : UniformSpace C⋆ᵐᵒᵈ(A, E)
  定义体: u.comap equiv A E

Depends on / 依赖: u.comap
-/
instance [u : UniformSpace E] : UniformSpace C⋆ᵐᵒᵈ(A, E) := u.comap equiv A E

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Bornology
  signature: E] : Bornology C⋆ᵐᵒᵈ(A, E)
  body: Bornology.induced equiv A E

中文:
实例 [Bornology
  签名: E] : Bornology C⋆ᵐᵒᵈ(A, E)
  定义体: Bornology.induced equiv A E

Depends on / 依赖: Bornology, Bornology.induced, induced
-/
instance [Bornology E] : Bornology C⋆ᵐᵒᵈ(A, E) := Bornology.induced equiv A E


/--
Definition of `uniformEquiv` / `uniformEquiv` 的定义

English:
definition uniformEquiv
  signature: [UniformSpace E]
  body: .toUniformEquivOfIsUniformInducing ⟨rfl⟩ equiv A E

中文:
定义 uniformEquiv
  签名: [UniformSpace E]
  定义体: .toUniformEquivOfIsUniformInducing ⟨rfl⟩ equiv A E

Depends on / 依赖: toUniformEquivOfIsUniformInducing
-/
def uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ(A, E) ≃ᵤ E :=
.toUniformEquivOfIsUniformInducing ⟨rfl⟩ equiv A E

/-- `WithCStarModule.equiv` as a continuous linear equivalence between `C⋆ᵐᵒᵈ E` and `E`. -/
@[simps! apply symm_apply]
/--
Definition of `equivL` / `equivL` 的定义

English:
definition equivL
  signature: [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E]
  body: { linearEquiv R A E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }

中文:
定义 equivL
  签名: [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E]
  定义体: { linearEquiv R A E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }

Depends on / 依赖: UniformEquiv, UniformEquiv.continuous, continuous, continuous_invFun, continuous_toFun, linearEquiv, uniformEquiv, uniformEquiv.symm
-/
def equivL [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃L[R] E :=
  { linearEquiv R A E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: E] [CompleteSpace E] : CompleteSpace C⋆ᵐᵒᵈ(A, E)
  body: uniformEquiv.completeSpace_iff.mpr inferInstance

中文:
实例 [UniformSpace
  签名: E] [CompleteSpace E] : CompleteSpace C⋆ᵐᵒᵈ(A, E)
  定义体: uniformEquiv.completeSpace_iff.mpr inferInstance

Depends on / 依赖: completeSpace_iff, uniformEquiv, uniformEquiv.completeSpace_iff.mpr
-/
instance [UniformSpace E] [CompleteSpace E] : CompleteSpace C⋆ᵐᵒᵈ(A, E) :=
  uniformEquiv.completeSpace_iff.mpr inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd C⋆ᵐᵒᵈ(A, E)
  body: ContinuousAdd.induced (addEquiv A E)

中文:
实例 [AddCommGroup
  签名: E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd C⋆ᵐᵒᵈ(A, E)
  定义体: ContinuousAdd.induced (addEquiv A E)

Depends on / 依赖: ContinuousAdd, ContinuousAdd.induced, addEquiv, induced
-/
instance [AddCommGroup E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd C⋆ᵐᵒᵈ(A, E) :=
  ContinuousAdd.induced (addEquiv A E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C⋆ᵐᵒᵈ(A, E)
  body: IsUniformAddGroup.comap (addEquiv A E)

中文:
实例 [AddCommGroup
  签名: E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C⋆ᵐᵒᵈ(A, E)
  定义体: IsUniformAddGroup.comap (addEquiv A E)

Depends on / 依赖: IsUniformAddGroup, IsUniformAddGroup.comap, addEquiv
-/
instance [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C⋆ᵐᵒᵈ(A, E) :=
  IsUniformAddGroup.comap (addEquiv A E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
  body: ContinuousSMul.induced (linearEquiv R A E)

中文:
实例 [Semiring
  签名: R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
  定义体: ContinuousSMul.induced (linearEquiv R A E)

Depends on / 依赖: ContinuousSMul, ContinuousSMul.induced, induced, linearEquiv
-/
instance [Semiring R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
    [ContinuousSMul R E] : ContinuousSMul R C⋆ᵐᵒᵈ(A, E) :=
  ContinuousSMul.induced (linearEquiv R A E)

end Basic

/-! ## Prod

Register simplification lemmas for the applications of `WithCStarModule (E × F)` elements, as
the usual lemmas for `Prod` will not trigger. -/

section Prod

variable {R A E F : Type*}
variable [SMul R E] [SMul R F]
variable (x y : C⋆ᵐᵒᵈ(A, E × F)) (c : R)

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F]

@[simp]
/--
theorem `zero_fst` / 定理 `zero_fst`

English:
theorem zero_fst
  statement: (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0
  proof: rfl

@[simp]

中文:
定理 zero_fst
  结论: (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0
  证明: rfl

@[simp]
-/
theorem zero_fst : (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0 :=
  rfl

@[simp]
/--
theorem `zero_snd` / 定理 `zero_snd`

English:
theorem zero_snd
  statement: (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0
  proof: rfl

@[simp]

中文:
定理 zero_snd
  结论: (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0
  证明: rfl

@[simp]
-/
theorem zero_snd : (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0 :=
  rfl

@[simp]
/--
theorem `add_fst` / 定理 `add_fst`

English:
theorem add_fst
  statement: (x + y).fst = x.fst + y.fst
  proof: rfl

@[simp]

中文:
定理 add_fst
  结论: (x + y).fst = x.fst + y.fst
  证明: rfl

@[simp]
-/
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

@[simp]
/--
theorem `add_snd` / 定理 `add_snd`

English:
theorem add_snd
  statement: (x + y).snd = x.snd + y.snd
  proof: rfl

@[simp]

中文:
定理 add_snd
  结论: (x + y).snd = x.snd + y.snd
  证明: rfl

@[simp]
-/
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

@[simp]
/--
theorem `sub_fst` / 定理 `sub_fst`

English:
theorem sub_fst
  statement: (x - y).fst = x.fst - y.fst
  proof: rfl

@[simp]

中文:
定理 sub_fst
  结论: (x - y).fst = x.fst - y.fst
  证明: rfl

@[simp]
-/
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

@[simp]
/--
theorem `sub_snd` / 定理 `sub_snd`

English:
theorem sub_snd
  statement: (x - y).snd = x.snd - y.snd
  proof: rfl

@[simp]

中文:
定理 sub_snd
  结论: (x - y).snd = x.snd - y.snd
  证明: rfl

@[simp]
-/
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

@[simp]
/--
theorem `neg_fst` / 定理 `neg_fst`

English:
theorem neg_fst
  statement: (-x).fst = -x.fst
  proof: rfl

@[simp]

中文:
定理 neg_fst
  结论: (-x).fst = -x.fst
  证明: rfl

@[simp]
-/
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
/--
theorem `neg_snd` / 定理 `neg_snd`

English:
theorem neg_snd
  statement: (-x).snd = -x.snd
  proof: rfl

中文:
定理 neg_snd
  结论: (-x).snd = -x.snd
  证明: rfl
-/
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

end AddCommGroup

@[simp]
/--
theorem `smul_fst` / 定理 `smul_fst`

English:
theorem smul_fst
  statement: (c • x).fst = c • x.fst
  proof: rfl

@[simp]

中文:
定理 smul_fst
  结论: (c • x).fst = c • x.fst
  证明: rfl

@[simp]
-/
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
/--
theorem `smul_snd` / 定理 `smul_snd`

English:
theorem smul_snd
  statement: (c • x).snd = c • x.snd
  proof: rfl

中文:
定理 smul_snd
  结论: (c • x).snd = c • x.snd
  证明: rfl
-/
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
/--
theorem `equiv_fst` / 定理 `equiv_fst`

English:
theorem equiv_fst
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: (equiv A (E × F) x).fst = x.fst
  proof: rfl

@[simp]

中文:
定理 equiv_fst
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: (equiv A (E × F) x).fst = x.fst
  证明: rfl

@[simp]
-/
theorem equiv_fst (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).fst = x.fst :=
  rfl

@[simp]
/--
theorem `equiv_snd` / 定理 `equiv_snd`

English:
theorem equiv_snd
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: (equiv A (E × F) x).snd = x.snd
  proof: rfl

@[simp]

中文:
定理 equiv_snd
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: (equiv A (E × F) x).snd = x.snd
  证明: rfl

@[simp]

Depends on / 依赖: NormedAddCommGroup, NormedAddTorsor, NormedAddTorsor.toAddTorsor, toAddTorsor
-/
theorem equiv_snd (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).snd = x.snd :=
  rfl

@[simp]
/--
theorem `equiv_symm_fst` / 定理 `equiv_symm_fst`

English:
theorem equiv_symm_fst
  given: (x : E × F)
  statement: ((equiv A (E × F)).symm x).fst = x.fst
  proof: rfl

@[simp]

中文:
定理 equiv_symm_fst
  条件: (x : E × F)
  结论: ((equiv A (E × F)).symm x).fst = x.fst
  证明: rfl

@[simp]

Depends on / 依赖: IsIsometricVAdd, NormedAddTorsor, NormedAddTorsor.to_isIsIsometricVAdd, to_isIsIsometricVAdd
-/
theorem equiv_symm_fst (x : E × F) : ((equiv A (E × F)).symm x).fst = x.fst :=
  rfl

@[simp]
/--
theorem `equiv_symm_snd` / 定理 `equiv_symm_snd`

English:
theorem equiv_symm_snd
  given: (x : E × F)
  statement: ((equiv A (E × F)).symm x).snd = x.snd
  proof: rfl

中文:
定理 equiv_symm_snd
  条件: (x : E × F)
  结论: ((equiv A (E × F)).symm x).snd = x.snd
  证明: rfl

Depends on / 依赖: NormedAddTorsor, SeminormedAddCommGroup, SeminormedAddCommGroup.toNormedAddTorsor, toNormedAddTorsor
-/
theorem equiv_symm_snd (x : E × F) : ((equiv A (E × F)).symm x).snd = x.snd :=
  rfl

end Prod

/-! ## Pi

Register simplification lemmas for the applications of `WithCStarModule (Π i, E i)` elements, as
the usual lemmas for `Pi` will not trigger.

We also provide a `CoeFun` instance for `WithCStarModule (Π i, E i)`. -/

section Pi

/-- The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithCStarModule.equiv`. -/
instance {A ι : Type*} (E : ι -> Type*) : CoeFun (C⋆ᵐᵒᵈ(A, Π i, E i)) (fun _ => Π i, E i) where
  coe := equiv _ _

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {A ι : Type*} {E : ι -> Type*} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
  proof: funext h

中文:
定理 ext
  结论: {A ι : 类型} {E : ι -> 类型} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
  证明: funext h
-/
protected theorem ext {A ι : Type*} {E : ι -> Type*} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
    (h : forall i, x i = y i) : x = y :=
  funext h

variable {R A ι : Type*} {E : ι -> Type*}
variable [forall i, SMul R (E i)]
variable (c : R) (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι)

section AddCommGroup

variable [forall i, AddCommGroup (E i)]

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  statement: (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  结论: (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0
  证明: rfl

@[simp]
-/
theorem zero_apply : (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0 :=
  rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  statement: (x + y) i = x i + y i
  proof: rfl

@[simp]

中文:
定理 add_apply
  结论: (x + y) i = x i + y i
  证明: rfl

@[simp]
-/
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  statement: (x - y) i = x i - y i
  proof: rfl

@[simp]

中文:
定理 sub_apply
  结论: (x - y) i = x i - y i
  证明: rfl

@[simp]
-/
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  statement: (-x) i = -x i
  proof: rfl

中文:
定理 neg_apply
  结论: (-x) i = -x i
  证明: rfl
-/
theorem neg_apply : (-x) i = -x i :=
  rfl

end AddCommGroup

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  statement: (c • x) i = c • x i
  proof: rfl

中文:
定理 smul_apply
  结论: (c • x) i = c • x i
  证明: rfl
-/
theorem smul_apply : (c • x) i = c • x i :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
/--
theorem `equiv_pi_apply` / 定理 `equiv_pi_apply`

English:
theorem equiv_pi_apply
  given: (i : ι)
  statement: equiv _ _ x i = x i
  proof: rfl

@[simp]

中文:
定理 equiv_pi_apply
  条件: (i : ι)
  结论: equiv _ _ x i = x i
  证明: rfl

@[simp]
-/
theorem equiv_pi_apply (i : ι) : equiv _ _ x i = x i :=
  rfl

@[simp]
/--
theorem `equiv_symm_pi_apply` / 定理 `equiv_symm_pi_apply`

English:
theorem equiv_symm_pi_apply
  given: (x : forall i, E i) (i : ι)
  proof: rfl

中文:
定理 equiv_symm_pi_apply
  条件: (x : 对任意 i, E i) (i : ι)
  证明: rfl
-/
theorem equiv_symm_pi_apply (x : forall i, E i) (i : ι) :
    (equiv A _).symm x i = x i :=
  rfl

end Pi

end WithCStarModule
