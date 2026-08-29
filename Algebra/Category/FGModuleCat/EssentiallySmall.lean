/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The category of finitely generated modules over a ring is essentially small

This file proves that `FGModuleCat R`, the category of finitely generated modules over a ring `R`,
is essentially small, by providing an explicit small model. However, for applications, it is
recommended to use the standard `CategoryTheory.SmallModel (FGModuleCat R)` instead.

-/

@[expose] public section

universe v w u

variable (R : Type u) [Ring R]

open CategoryTheory

/--
Definition of `FGModuleRepr` / `FGModuleRepr` 的定义

English:
structure FGModuleRepr
  parameters: : Type u where
  axioms and operations (2):
    - (n : Nat)
    - (S : Submodule R (Fin n -> R))

中文:
结构 FGModuleRepr
  参数: : 类型u where
  公理与运算 (2 个):
    - (n : 自然数)
    - (S : 子模 R (有限集 n -> R))
-/
structure FGModuleRepr : Type u where
  /-- The natural number `n` that defines the module as a quotient of `Fin n → R` (i.e. `R^n`). -/
  (n : Nat)
  /-- The kernel of the surjective map from `Fin n → R` (i.e. `R^n`) to the module represented. -/
  (S : Submodule R (Fin n -> R))

namespace FGModuleRepr

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

variable {R} in
/--
Definition of `repr` / `repr` 的定义

English:
definition repr
  signature: (x : FGModuleRepr R)
  body: _ ⧸ x.S
deriving AddCommGroup, Module R

中文:
定义 repr
  签名: (x : FGModuleRepr R)
  定义体: _ ⧸ x.S
deriving AddCommGroup, Module R
-/
def repr (x : FGModuleRepr R) : Type u :=
  _ ⧸ x.S
deriving AddCommGroup, Module R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (FGModuleRepr R) (Type u)
  body: ⟨repr⟩

中文:
实例 :
  签名: CoeSort (FGModuleRepr R) (类型u)
  定义体: ⟨repr⟩
-/
instance : CoeSort (FGModuleRepr R) (Type u) :=
  ⟨repr⟩

instance (x : FGModuleRepr R) : Module.Finite R x :=
inferInstanceAs Module.Finite R (_ ⧸ x.S)

/-- A non-canonical representation of a finite module (as a quotient of `Rⁿ`). -/
@[instance_reducible]
/--
Definition of `ofFinite` / `ofFinite` 的定义

English:
definition ofFinite
  signature: : FGModuleRepr R where
  body: (Module.Finite.exists_fin_quot_equiv R M).choose
  S := (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose

中文:
定义 ofFinite
  签名: : FGModuleRepr R where
  定义体: (Module.Finite.exists_fin_quot_equiv R M).choose
  S := (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose

Depends on / 依赖: Finite, Module, Module.Finite.exists_fin_quot_equiv, exists_fin_quot_equiv
-/
noncomputable def ofFinite : FGModuleRepr R where
  n := (Module.Finite.exists_fin_quot_equiv R M).choose
  S := (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose

/--
Definition of `ofFiniteEquiv` / `ofFiniteEquiv` 的定义

English:
definition ofFiniteEquiv
  signature: : ofFinite R M ≃ₗ[R] M
  body: Classical.choice (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose_spec

中文:
定义 ofFiniteEquiv
  签名: : ofFinite R M ≃ₗ[R] M
  定义体: Classical.choice (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose_spec

Depends on / 依赖: Classical, Classical.choice, Finite, Module, Module.Finite.exists_fin_quot_equiv, choice, choose_spec, choose_spec.choose_spec, exists_fin_quot_equiv
-/
noncomputable def ofFiniteEquiv : ofFinite R M ≃ₗ[R] M :=
  Classical.choice (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose_spec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (FGModuleRepr R)
  body: inferInstanceAs (Category (InducedCategory _
    (fun x : FGModuleRepr R => FGModuleCat.of R x)))

中文:
实例 :
  签名: 范畴 (FGModuleRepr R)
  定义体: inferInstanceAs (Category (InducedCategory _
    (fun x : FGModuleRepr R => FGModuleCat.of R x)))

Depends on / 依赖: Category, FGModuleCat, FGModuleCat.of, FGModuleRepr, InducedCategory
-/
instance : Category (FGModuleRepr R) :=
  inferInstanceAs (Category (InducedCategory _
    (fun x : FGModuleRepr R => FGModuleCat.of R x)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (FGModuleRepr R)

中文:
实例 :
  签名: 小范畴 (FGModuleRepr R)
-/
instance : SmallCategory (FGModuleRepr R) where

/--
Definition of `embed` / `embed` 的定义

English:
definition embed
  signature: : FGModuleRepr.{u} R ⥤ FGModuleCat.{max u v} R
  body: inducedFunctor _ ⋙ FGModuleCat.ulift R

中文:
定义 embed
  签名: : FGModuleRepr.{u} R ⥤ FGModuleCat.{最大值 u v} R
  定义体: inducedFunctor _ ⋙ FGModuleCat.ulift R

Depends on / 依赖: FGModuleCat, FGModuleCat.ulift, inducedFunctor
-/
def embed : FGModuleRepr.{u} R ⥤ FGModuleCat.{max u v} R :=
  inducedFunctor _ ⋙ FGModuleCat.ulift R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embed R).IsEquivalence
  body: (fullyFaithfulInducedFunctor _).faithful.comp _ _
  full := (fullyFaithfulInducedFunctor _).full.comp _ _
  essSurj := ⟨fun M => ⟨ofFinite R M,
    ⟨(ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

中文:
实例 :
  签名: (embed R).是等价
  定义体: (fullyFaithfulInducedFunctor _).faithful.comp _ _
  full := (fullyFaithfulInducedFunctor _).full.comp _ _
  essSurj := ⟨fun M => ⟨ofFinite R M,
    ⟨(ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

Depends on / 依赖: faithful, faithful.comp, fullyFaithfulInducedFunctor
-/
instance : (embed R).IsEquivalence where
  faithful := (fullyFaithfulInducedFunctor _).faithful.comp _ _
  full := (fullyFaithfulInducedFunctor _).full.comp _ _
  essSurj := ⟨fun M => ⟨ofFinite R M,
    ⟨(ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

end FGModuleRepr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{u} (FGModuleCat.{v} R)
  body: letI : EssentiallySmall.{u} (FGModuleCat.{max u v} R) :=
    ⟨_, _, ⟨(FGModuleRepr.embed R).asEquivalence.symm⟩⟩
  essentiallySmall_of_fully_faithful (FGModuleCat.ulift.{v, max u v} R)

中文:
实例 :
  签名: EssentiallySmall.{u} (FGModuleCat.{v} R)
  定义体: letI : EssentiallySmall.{u} (FGModuleCat.{max u v} R) :=
    ⟨_, _, ⟨(FGModuleRepr.embed R).asEquivalence.symm⟩⟩
  essentiallySmall_of_fully_faithful (FGModuleCat.ulift.{v, max u v} R)

Depends on / 依赖: EssentiallySmall, FGModuleCat, FGModuleCat.ulift, FGModuleRepr, FGModuleRepr.embed, asEquivalence, asEquivalence.symm, essentiallySmall_of_fully_faithful
-/
instance : EssentiallySmall.{u} (FGModuleCat.{v} R) :=
  letI : EssentiallySmall.{u} (FGModuleCat.{max u v} R) :=
    ⟨_, _, ⟨(FGModuleRepr.embed R).asEquivalence.symm⟩⟩
  essentiallySmall_of_fully_faithful (FGModuleCat.ulift.{v, max u v} R)

open FGModuleRepr in
-- There is probably a proof using `embedIsEquivalence` or `EssentiallySmall`.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (FGModuleCat.ulift.{max u v, w} R).IsEquivalence
  body: ⟨fun M => ⟨(embed R).obj (ofFinite R M),
    ⟨(ULift.moduleEquiv.trans <| ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

中文:
实例 :
  签名: (FGModuleCat.ulift.{最大值 u v, w} R).是等价
  定义体: ⟨fun M => ⟨(embed R).obj (ofFinite R M),
    ⟨(ULift.moduleEquiv.trans <| ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

Depends on / 依赖: ofFinite
-/
instance : (FGModuleCat.ulift.{max u v, w} R).IsEquivalence where
  essSurj := ⟨fun M => ⟨(embed R).obj (ofFinite R M),
    ⟨(ULift.moduleEquiv.trans <| ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩
