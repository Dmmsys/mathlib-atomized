/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Normal closure of an extension of domains

We define the normal closure of an extension of domains `R ⊆ S` as a domain `T` such that
`R ⊆ S ⊆ T` and the extension `Frac T / Frac R` is Galois, and prove several instances about it.

Under the hood, `T` is defined as the `integralClosure` of `S` inside the
`IntermediateField.normalClosure` of the extension `Frac S / Frac R` inside the `AlgebraicClosure`
of `Frac S`. In particular, if `S` is a Dedekind domain, then `T` is also a Dedekind domain.

## Technical notes

* Many instances are proved about the `IntermediateField.normalClosure` of the extension
  `Frac S / Frac R` inside the `AlgebraicClosure` of `Frac S`. However these are only needed for the
  construction of `T` and to prove some results about it. Therefore, these instances are local.
* `Ring.NormalClosure` is defined as a type rather than a `Subalgebra` for performance reasons
  (and thus we need to provide explicit instances for it). Although defining it as a `Subalgebra`
  does not cause timeouts in this file, it does slow down considerably its compilation and
  does trigger timeouts in applications.
-/

@[expose] public section

namespace Ring

noncomputable section NormalClosure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

/--
We register this specific instance as a local instance rather than making
`FractionRing.liftAlgebra` a local instance because the latter causes timeouts since
it is too general.
-/
local instance : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra _ _

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))


/--
This is a local instance since it is only used in this file to construct `Ring.NormalClosure`.
-/
local instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra

local instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

/--
Definition of `NormalClosure` / `NormalClosure` 的定义

English:
definition NormalClosure
  signature: : Type _
  body: integralClosure S E

local notation3 "T" => NormalClosure R S

中文:
定义 正规闭包
  签名: : 类型 _
  定义体: integralClosure S E

local notation3 "T" => NormalClosure R S

Depends on / 依赖: integralClosure
-/
def NormalClosure : Type _ := integralClosure S E

local notation3 "T" => NormalClosure R S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing T
  body: inferInstanceAs (CommRing (integralClosure S E))

中文:
实例 :
  签名: 交换环 T
  定义体: inferInstanceAs (CommRing (integralClosure S E))

Depends on / 依赖: CommRing, integralClosure
-/
instance : CommRing T := inferInstanceAs (CommRing (integralClosure S E))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain T
  body: inferInstanceAs (IsDomain (integralClosure S E))

中文:
实例 :
  签名: 是整环 T
  定义体: inferInstanceAs (IsDomain (integralClosure S E))

Depends on / 依赖: IsDomain, integralClosure
-/
instance : IsDomain T := inferInstanceAs (IsDomain (integralClosure S E))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial T
  body: inferInstanceAs (Nontrivial (integralClosure S E))

中文:
实例 :
  签名: 非平凡 T
  定义体: inferInstanceAs (Nontrivial (integralClosure S E))

Depends on / 依赖: Nontrivial, integralClosure
-/
instance : Nontrivial T := inferInstanceAs (Nontrivial (integralClosure S E))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra S T
  body: inferInstanceAs (Algebra S (integralClosure S E))

中文:
实例 :
  签名: 代数 S T
  定义体: inferInstanceAs (Algebra S (integralClosure S E))

Depends on / 依赖: Algebra, integralClosure
-/
instance : Algebra S T := inferInstanceAs (Algebra S (integralClosure S E))

/--
This is a local instance since it is only used in this file to construct `Ring.NormalClosure`.
-/
local instance : Algebra T E := inferInstanceAs (Algebra (integralClosure S E) E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R T
  body: ((algebraMap S T).comp (algebraMap R S)).toAlgebra

local instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E

中文:
实例 :
  签名: 代数 R T
  定义体: ((algebraMap S T).comp (algebraMap R S)).toAlgebra

local instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E

Depends on / 依赖: algebraMap, toAlgebra
-/
instance : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra

local instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R S T
  body: IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E

local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E

local instance : FaithfulSMul S E := (faithfulSMul_iff_a

中文:
实例 :
  签名: 标量塔 R S T
  定义体: IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E

local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E

local instance : FaithfulSMul S E := (faithfulSMul_iff_a

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E

local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E

local instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr
      (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.IsTorsionFree S T
  body: Subalgebra.instIsTorsionFree (integralClosure S E)

中文:
实例 :
  签名: 模.是无挠 S T
  定义体: Subalgebra.instIsTorsionFree (integralClosure S E)

Depends on / 依赖: Subalgebra, Subalgebra.instIsTorsionFree, instIsTorsionFree, integralClosure
-/
instance : Module.IsTorsionFree S T := Subalgebra.instIsTorsionFree (integralClosure S E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul R T
  body: (faithfulSMul_iff_algebraMap_injective R T).mpr
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

中文:
实例 :
  签名: 忠实标量乘法 R T
  定义体: (faithfulSMul_iff_algebraMap_injective R T).mpr
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, faithfulSMul_iff_algebraMap_injective
-/
instance : FaithfulSMul R T :=
(faithfulSMul_iff_algebraMap_injective R T).mpr
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

variable [Module.Finite R S]

local instance : FiniteDimensional L E := Module.Finite.right K L E

local instance : IsFractionRing T E :=
  integralClosure.isFractionRing_of_finite_extension L E

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegrallyClosed T
  body: integralClosure.isIntegrallyClosedOfFiniteExtension L

中文:
实例 :
  签名: 是整闭 T
  定义体: integralClosure.isIntegrallyClosedOfFiniteExtension L

Depends on / 依赖: integralClosure, integralClosure.isIntegrallyClosedOfFiniteExtension, isIntegrallyClosedOfFiniteExtension
-/
instance : IsIntegrallyClosed T :=
  integralClosure.isIntegrallyClosedOfFiniteExtension L

variable [PerfectField (FractionRing R)]

local instance : Algebra.IsSeparable L E :=
  Algebra.isSeparable_tower_top_of_isSeparable K L E

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGalois K (FractionRing T)
  body: by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

中文:
实例 :
  签名: 是Galois K (FractionRing T)
  定义体: by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

Depends on / 依赖: FractionRing, FractionRing.algEquiv, IsFractionRing, IsFractionRing.algEquiv_commutes, IsGalois, IsGalois.of_equiv_equiv, algEquiv, algEquiv_commutes, of_equiv_equiv, symm.toRingEquiv, toRingEquiv
-/
instance : IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

variable [IsDedekindDomain S]

set_option linter.overlappingInstances false

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite S T
  body: IsIntegralClosure.finite S L E T

中文:
实例 :
  签名: 模.有限 S T
  定义体: IsIntegralClosure.finite S L E T

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.finite, finite
-/
instance : Module.Finite S T :=
  IsIntegralClosure.finite S L E T

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R T
  body: Module.Finite.trans S T

中文:
实例 :
  签名: 模.有限 R T
  定义体: Module.Finite.trans S T

Depends on / 依赖: Finite, Module, Module.Finite.trans
-/
instance : Module.Finite R T :=
  Module.Finite.trans S T

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDedekindDomain T
  body: integralClosure.isDedekindDomain S L E

中文:
实例 :
  签名: 是Dedekind整环 T
  定义体: integralClosure.isDedekindDomain S L E

Depends on / 依赖: integralClosure, integralClosure.isDedekindDomain, isDedekindDomain
-/
instance : IsDedekindDomain T :=
  integralClosure.isDedekindDomain S L E

end Ring.NormalClosure
