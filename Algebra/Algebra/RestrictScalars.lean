/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Tower

/-!

# The `RestrictScalars` type alias

See the documentation attached to the `RestrictScalars` definition for advice on how and when to
use this type alias. As described there, it is often a better choice to use the `IsScalarTower`
typeclass instead.

## Main definitions

* `RestrictScalars R S M`: the `S`-module `M` viewed as an `R` module when `S` is an `R`-algebra.
  Note that by default we do *not* have a `Module S (RestrictScalars R S M)` instance
  for the original action.
  This is available as a def `RestrictScalars.moduleOrig` if really needed.
* `RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M`: the additive equivalence
  between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A`: the ring equivalence
  between the restricted and original space when the module is an algebra.
* `Module.restrictScalars R S M`, `Algebra.restrictScalars R S A`: non-instance definitions for
  `Module R M` and `Algebra R A`.

## See also

There are many similarly-named definitions elsewhere which do not refer to this type alias. These
refer to restricting the scalar type in a bundled type, such as from `A →ₗ[R] B` to `A →ₗ[S] B`:

* `LinearMap.restrictScalars`
* `LinearEquiv.restrictScalars`
* `AlgHom.restrictScalars`
* `AlgEquiv.restrictScalars`
* `Submodule.restrictScalars`
* `Subalgebra.restrictScalars`
-/

@[expose] public section


variable (R S M A : Type*)

/-- If we put an `R`-algebra structure on a semiring `S`, we get a natural equivalence from the
category of `S`-modules to the category of representations of the algebra `S` (over `R`). The type
synonym `RestrictScalars` is essentially this equivalence.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `S`, given:
```lean
variable (R S M : Type*)
variable [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module S M]
```
With the assumptions above we can't directly state our map as we have no `Module R M` structure, but
`RestrictScalars` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `RestrictScalars` which is compatible
example : RestrictScalars R S M →ₗ[R] S := sorry
```
However, it is usually better just to add this extra structure as an argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [Module R M] [IsScalarTower R S M] : M →ₗ[R] S := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[Module R M] [IsScalarTower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `RestrictScalars` entirely. If not, we can pass
`RestrictScalars R S M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`IsScalarTower` rather than `RestrictScalars`.

An example of when one might want to use `RestrictScalars` would be if one has a vector space
over a field of characteristic zero and wishes to make use of the `ℚ`-algebra structure. -/
@[nolint unusedArguments]
/--
Definition of `RestrictScalars` / `RestrictScalars` 的定义

English:
definition RestrictScalars
  signature: (_R _S M : Type*)
  body: M

中文:
定义 RestrictScalars
  签名: (_R _S M : 类型)
  定义体: M
-/
def RestrictScalars (_R _S M : Type*) : Type _ := M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : Inhabited M] : Inhabited (RestrictScalars R S M)
  body: I

中文:
实例 [I
  签名: : 可居 M] : 可居 (RestrictScalars R S M)
  定义体: I
-/
instance [I : Inhabited M] : Inhabited (RestrictScalars R S M) := I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : AddCommMonoid M] : AddCommMonoid (RestrictScalars R S M)
  body: I

中文:
实例 [I
  签名: : 加法交换幺半群 M] : 加法交换幺半群 (RestrictScalars R S M)
  定义体: I
-/
instance [I : AddCommMonoid M] : AddCommMonoid (RestrictScalars R S M) := I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : AddCommGroup M] : AddCommGroup (RestrictScalars R S M)
  body: I

中文:
实例 [I
  签名: : 加法交换群 M] : 加法交换群 (RestrictScalars R S M)
  定义体: I
-/
instance [I : AddCommGroup M] : AddCommGroup (RestrictScalars R S M) := I

section Module

section

variable [Semiring S] [AddCommMonoid M]

/-- We temporarily install an action of the original ring on `RestrictScalars R S M`. -/
@[instance_reducible]
/--
Definition of `RestrictScalars.moduleOrig` / `RestrictScalars.moduleOrig` 的定义

English:
definition RestrictScalars.moduleOrig
  signature: [I : Module S M]
  body: I

中文:
定义 RestrictScalars.moduleOrig
  签名: [I : 模 S M]
  定义体: I
-/
def RestrictScalars.moduleOrig [I : Module S M] : Module S (RestrictScalars R S M) := I

variable [CommSemiring R] [Algebra R S]

section

attribute [local instance] RestrictScalars.moduleOrig

/--
Definition of `Module.restrictScalars` / `Module.restrictScalars` 的定义

English:
abbreviation Module.restrictScalars
  signature: [Module S M]
  body: Module.compHom M (algebraMap R S)

中文:
缩写 模.restrictScalars
  签名: [模 S M]
  定义体: Module.compHom M (algebraMap R S)

Depends on / 依赖: Module, Module.compHom, algebraMap, compHom
-/
abbrev Module.restrictScalars [Module S M] : Module R M :=
  Module.compHom M (algebraMap R S)

/--
Instance `RestrictScalars.module` / 实例 `RestrictScalars.module`

English:
instance RestrictScalars.module
  signature: [Module S M]
  body: Module.restrictScalars R S M

中文:
实例 RestrictScalars.module
  签名: [模 S M]
  定义体: Module.restrictScalars R S M

Depends on / 依赖: Module, Module.restrictScalars, restrictScalars
-/
instance RestrictScalars.module [Module S M] : Module R (RestrictScalars R S M) :=
  Module.restrictScalars R S M

/--
theorem `IsScalarTower.restrictScalars` / 定理 `IsScalarTower.restrictScalars`

English:
theorem IsScalarTower.restrictScalars
  given: [Module S M]
  proof: Module.restrictScalars R S M
    IsScalarTower R S M :=
  IsScalarTower.of_compHom R S M

中文:
定理 标量塔.restrictScalars
  条件: [模 S M]
  证明: Module.restrictScalars R S M
    IsScalarTower R S M :=
  IsScalarTower.of_compHom R S M

Depends on / 依赖: Algebra, Module, Module.restrictScalars, ofSubsemiring, restrictScalars
-/
theorem IsScalarTower.restrictScalars [Module S M] :
    letI := Module.restrictScalars R S M
    IsScalarTower R S M :=
  IsScalarTower.of_compHom R S M

/--
Instance `RestrictScalars.isScalarTower` / 实例 `RestrictScalars.isScalarTower`

English:
instance RestrictScalars.isScalarTower
  signature: [Module S M]
  body: IsScalarTower.restrictScalars R S M

中文:
实例 RestrictScalars.isScalarTower
  签名: [模 S M]
  定义体: IsScalarTower.restrictScalars R S M

Depends on / 依赖: IsScalarTower, IsScalarTower.restrictScalars, restrictScalars
-/
instance RestrictScalars.isScalarTower [Module S M] : IsScalarTower R S (RestrictScalars R S M) :=
  IsScalarTower.restrictScalars R S M

end

/--
Instance `RestrictScalars.opModule` / 实例 `RestrictScalars.opModule`

English:
instance RestrictScalars.opModule
  signature: [Module Sᵐᵒᵖ M]
  body: letI : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M (RingHom.op <| algebraMap R S)

中文:
实例 RestrictScalars.opModule
  签名: [模 Sᵐᵒᵖ M]
  定义体: letI : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M (RingHom.op <| algebraMap R S)

Depends on / 依赖: Module, Module.compHom, RestrictScalars, RingHom, RingHom.op, algebraMap, compHom
-/
instance RestrictScalars.opModule [Module Sᵐᵒᵖ M] : Module Rᵐᵒᵖ (RestrictScalars R S M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M (RingHom.op <| algebraMap R S)

/--
Instance `RestrictScalars.isCentralScalar` / 实例 `RestrictScalars.isCentralScalar`

English:
instance RestrictScalars.isCentralScalar
  signature: [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M]
  body: (op_smul_eq_smul (algebraMap R S r) (_ : M) :)

中文:
实例 RestrictScalars.isCentralScalar
  签名: [模 S M] [模 Sᵐᵒᵖ M] [中心标量 S M]
  定义体: (op_smul_eq_smul (algebraMap R S r) (_ : M) :)

Depends on / 依赖: algebraMap, op_smul_eq_smul
-/
instance RestrictScalars.isCentralScalar [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R (RestrictScalars R S M) where
  op_smul_eq_smul r _x := (op_smul_eq_smul (algebraMap R S r) (_ : M) :)

/--
Definition of `RestrictScalars.lsmul` / `RestrictScalars.lsmul` 的定义

English:
definition RestrictScalars.lsmul
  signature: [Module S M]
  body: -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)

中文:
定义 RestrictScalars.lsmul
  签名: [模 S M]
  定义体: -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)
-/
def RestrictScalars.lsmul [Module S M] : S ->ₐ[R] Module.End R (RestrictScalars R S M) :=
  -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)

end

variable [AddCommMonoid M]

/--
Definition of `RestrictScalars.addEquiv` / `RestrictScalars.addEquiv` 的定义

English:
definition RestrictScalars.addEquiv
  signature: : RestrictScalars R S M ≃+ M
  body: AddEquiv.refl M

中文:
定义 RestrictScalars.addEquiv
  签名: : RestrictScalars R S M ≃+ M
  定义体: AddEquiv.refl M

Depends on / 依赖: AddEquiv, AddEquiv.refl
-/
def RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M :=
  AddEquiv.refl M

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

/--
theorem `RestrictScalars.smul_def` / 定理 `RestrictScalars.smul_def`

English:
theorem RestrictScalars.smul_def
  given: (c : R) (x : RestrictScalars R S M)
  proof: rfl

@[simp]

中文:
定理 RestrictScalars.smul_def
  条件: (c : R) (x : RestrictScalars R S M)
  证明: rfl

@[simp]
-/
theorem RestrictScalars.smul_def (c : R) (x : RestrictScalars R S M) :
    c • x = (RestrictScalars.addEquiv R S M).symm
      (algebraMap R S c • RestrictScalars.addEquiv R S M x) :=
  rfl

@[simp]
/--
theorem `RestrictScalars.addEquiv_map_smul` / 定理 `RestrictScalars.addEquiv_map_smul`

English:
theorem RestrictScalars.addEquiv_map_smul
  given: (c : R) (x : RestrictScalars R S M)
  proof: rfl

中文:
定理 RestrictScalars.addEquiv_map_smul
  条件: (c : R) (x : RestrictScalars R S M)
  证明: rfl
-/
theorem RestrictScalars.addEquiv_map_smul (c : R) (x : RestrictScalars R S M) :
    RestrictScalars.addEquiv R S M (c • x) = algebraMap R S c • RestrictScalars.addEquiv R S M x :=
  rfl

/--
theorem `RestrictScalars.addEquiv_symm_map_algebraMap_smul` / 定理 `RestrictScalars.addEquiv_symm_map_algebraMap_smul`

English:
theorem RestrictScalars.addEquiv_symm_map_algebraMap_smul
  given: (r : R) (x : M)
  proof: rfl

中文:
定理 RestrictScalars.addEquiv_symm_map_algebraMap_smul
  条件: (r : R) (x : M)
  证明: rfl
-/
theorem RestrictScalars.addEquiv_symm_map_algebraMap_smul (r : R) (x : M) :
    (RestrictScalars.addEquiv R S M).symm (algebraMap R S r • x) =
      r • (RestrictScalars.addEquiv R S M).symm x :=
  rfl

/--
theorem `RestrictScalars.addEquiv_symm_map_smul_smul` / 定理 `RestrictScalars.addEquiv_symm_map_smul_smul`

English:
theorem RestrictScalars.addEquiv_symm_map_smul_smul
  given: (r : R) (s : S) (x : M)
  proof: by
  rw [Algebra.smul_def]; rw [mul_smul]
  rfl

中文:
定理 RestrictScalars.addEquiv_symm_map_smul_smul
  条件: (r : R) (s : S) (x : M)
  证明: by
  rw [Algebra.smul_def]; rw [mul_smul]
  rfl

Depends on / 依赖: Algebra, Algebra.smul_def, mul_smul, smul_def
-/
theorem RestrictScalars.addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalars.addEquiv R S M).symm ((r • s) • x) =
      r • (RestrictScalars.addEquiv R S M).symm (s • x) := by
  rw [Algebra.smul_def]; rw [mul_smul]
  rfl

/--
theorem `RestrictScalars.lsmul_apply_apply` / 定理 `RestrictScalars.lsmul_apply_apply`

English:
theorem RestrictScalars.lsmul_apply_apply
  given: (s : S) (x : RestrictScalars R S M)
  proof: rfl

中文:
定理 RestrictScalars.lsmul_apply_apply
  条件: (s : S) (x : RestrictScalars R S M)
  证明: rfl
-/
theorem RestrictScalars.lsmul_apply_apply (s : S) (x : RestrictScalars R S M) :
    RestrictScalars.lsmul R S M s x =
      (RestrictScalars.addEquiv R S M).symm (s • RestrictScalars.addEquiv R S M x) :=
  rfl

end Module

section Algebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : Semiring A] : Semiring (RestrictScalars R S A)
  body: I

中文:
实例 [I
  签名: : 半环 A] : 半环 (RestrictScalars R S A)
  定义体: I
-/
instance [I : Semiring A] : Semiring (RestrictScalars R S A) := I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : Ring A] : Ring (RestrictScalars R S A)
  body: I

中文:
实例 [I
  签名: : 环 A] : 环 (RestrictScalars R S A)
  定义体: I
-/
instance [I : Ring A] : Ring (RestrictScalars R S A) := I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : CommSemiring A] : CommSemiring (RestrictScalars R S A)
  body: I

中文:
实例 [I
  签名: : 交换半环 A] : 交换半环 (RestrictScalars R S A)
  定义体: I
-/
instance [I : CommSemiring A] : CommSemiring (RestrictScalars R S A) := I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : CommRing A] : CommRing (RestrictScalars R S A)
  body: I

中文:
实例 [I
  签名: : 交换环 A] : 交换环 (RestrictScalars R S A)
  定义体: I

Depends on / 依赖: Subring, Subring.mem_center_iff, Subtype, Subtype.val, commutes, map_add, map_mul, map_one, map_zero, mem_center_iff, smul_def
-/
instance [I : CommRing A] : CommRing (RestrictScalars R S A) := I

variable [Semiring A]

/--
Definition of `RestrictScalars.ringEquiv` / `RestrictScalars.ringEquiv` 的定义

English:
definition RestrictScalars.ringEquiv
  signature: : RestrictScalars R S A ≃+* A
  body: RingEquiv.refl _

中文:
定义 RestrictScalars.ringEquiv
  签名: : RestrictScalars R S A ≃+* A
  定义体: RingEquiv.refl _

Depends on / 依赖: RingEquiv, RingEquiv.refl
-/
def RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A :=
  RingEquiv.refl _

variable [CommSemiring S] [Algebra S A] [CommSemiring R] [Algebra R S]

@[simp]
/--
theorem `RestrictScalars.ringEquiv_map_smul` / 定理 `RestrictScalars.ringEquiv_map_smul`

English:
theorem RestrictScalars.ringEquiv_map_smul
  given: (r : R) (x : RestrictScalars R S A)
  proof: rfl

中文:
定理 RestrictScalars.ringEquiv_map_smul
  条件: (r : R) (x : RestrictScalars R S A)
  证明: rfl
-/
theorem RestrictScalars.ringEquiv_map_smul (r : R) (x : RestrictScalars R S A) :
    RestrictScalars.ringEquiv R S A (r • x) =
      algebraMap R S r • RestrictScalars.ringEquiv R S A x :=
  rfl

/--
Definition of `Algebra.restrictScalars` / `Algebra.restrictScalars` 的定义

English:
abbreviation Algebra.restrictScalars
  signature: : Algebra R A
  body: Algebra.compHom A (algebraMap R S)

中文:
缩写 代数.restrictScalars
  签名: : 代数 R A
  定义体: Algebra.compHom A (algebraMap R S)

Depends on / 依赖: Algebra, Algebra.compHom, algebraMap, compHom
-/
abbrev Algebra.restrictScalars : Algebra R A :=
  Algebra.compHom A (algebraMap R S)

/--
Instance `RestrictScalars.algebra` / 实例 `RestrictScalars.algebra`

English:
instance RestrictScalars.algebra
  signature: : Algebra R (RestrictScalars R S A)
  body: Algebra.restrictScalars R S A

@[simp]

中文:
实例 RestrictScalars.algebra
  签名: : 代数 R (RestrictScalars R S A)
  定义体: Algebra.restrictScalars R S A

@[simp]

Depends on / 依赖: Algebra, Algebra.restrictScalars, restrictScalars
-/
instance RestrictScalars.algebra : Algebra R (RestrictScalars R S A) :=
  Algebra.restrictScalars R S A

@[simp]
/--
theorem `RestrictScalars.ringEquiv_algebraMap` / 定理 `RestrictScalars.ringEquiv_algebraMap`

English:
theorem RestrictScalars.ringEquiv_algebraMap
  given: (r : R)
  proof: rfl

中文:
定理 RestrictScalars.ringEquiv_algebraMap
  条件: (r : R)
  证明: rfl
-/
theorem RestrictScalars.ringEquiv_algebraMap (r : R) :
    RestrictScalars.ringEquiv R S A (algebraMap R (RestrictScalars R S A) r) =
      algebraMap S A (algebraMap R S r) :=
  rfl

end Algebra
