/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Order.Hom.PowersetCard

/-!
# Exterior Algebras

We construct the exterior algebra of a module `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-module `M` is denoted as `ExteriorAlgebra R M`.
It is endowed with the structure of an `R`-algebra.

The `n`th exterior power of the `R`-module `M` is denoted by `exteriorPower R n M`;
it is of type `Submodule R (ExteriorAlgebra R M)` and defined as
`LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n`.
We also introduce the notation `⋀[R]^n M` for `exteriorPower R n M`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `ExteriorAlgebra.lift R f cond`.

The canonical linear map `M → ExteriorAlgebra R M` is denoted `ExteriorAlgebra.ι R`.

## Theorems

The main theorems proved ensure that `ExteriorAlgebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is the fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ιMulti` is the `AlternatingMap` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as simply `CliffordAlgebra (0 : QuadraticForm R M)`,
as this avoids us having to duplicate API.
-/

@[expose] public section


universe u1 u2 u3 u4 u5

variable (R : Type u1) [CommRing R]
variable (M : Type u2) [AddCommGroup M] [Module R M]

/--
Definition of `ExteriorAlgebra` / `ExteriorAlgebra` 的定义

English:
abbreviation ExteriorAlgebra
  body: CliffordAlgebra (0 : QuadraticForm R M)

中文:
缩写 ExteriorAlgebra
  定义体: CliffordAlgebra (0 : QuadraticForm R M)

Depends on / 依赖: CliffordAlgebra, QuadraticForm
-/
abbrev ExteriorAlgebra :=
  CliffordAlgebra (0 : QuadraticForm R M)

namespace ExteriorAlgebra

variable {M}

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : M ->ₗ[R] ExteriorAlgebra R M
  body: CliffordAlgebra.ι _

中文:
缩写 ι
  签名: : M ->ₗ[R] ExteriorAlgebra R M
  定义体: CliffordAlgebra.ι _

Depends on / 依赖: CliffordAlgebra
-/
abbrev ι : M ->ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.ι _

section exteriorPower

-- New variables `n` and `M`, to get the correct order of variables in the notation.
variable (n : Nat) (M : Type u2) [AddCommGroup M] [Module R M]

/--
Definition of `exteriorPower` / `exteriorPower` 的定义

English:
abbreviation exteriorPower
  signature: : Submodule R (ExteriorAlgebra R M)
  body: LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M) ^ n

@[inherit_doc exteriorPower]
notation:max "⋀[" R "]^" n:arg => exteriorPower R n

中文:
缩写 exteriorPower
  签名: : Submodule R (ExteriorAlgebra R M)
  定义体: LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M) ^ n

@[inherit_doc exteriorPower]
notation:max "⋀[" R "]^" n:arg => exteriorPower R n

Depends on / 依赖: ExteriorAlgebra, LinearMap, LinearMap.range
-/
abbrev exteriorPower : Submodule R (ExteriorAlgebra R M) :=
  LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M) ^ n

@[inherit_doc exteriorPower]
notation:max "⋀[" R "]^" n:arg => exteriorPower R n

end exteriorPower

variable {R}

/--
theorem `ι_sq_zero` / 定理 `ι_sq_zero`

English:
theorem ι_sq_zero
  given: (m : M)
  statement: ι R m * ι R m = 0
  proof: (CliffordAlgebra.ι_sq_scalar _ m).trans map_zero _

中文:
定理 ι_sq_zero
  条件: (m : M)
  结论: ι R m * ι R m = 0
  证明: (CliffordAlgebra.ι_sq_scalar _ m).trans map_zero _

Depends on / 依赖: CliffordAlgebra, Subtype, Subtype.val_injective.smulCommClass, map_zero, smulCommClass, val_injective
-/
theorem ι_sq_zero (m : M) : ι R m * ι R m = 0 :=
(CliffordAlgebra.ι_sq_scalar _ m).trans map_zero _

section
variable {A : Type*} [Semiring A] [Algebra R A]

/--
theorem `comp_ι_sq_zero` / 定理 `comp_ι_sq_zero`

English:
theorem comp_ι_sq_zero
  given: (g : ExteriorAlgebra R M ->ₐ[R] A) (m : M)
  statement: g (ι R m) * g (ι R m) = 0
  proof: by
  rw [← map_mul]; rw [ι_sq_zero]; rw [map_zero]

中文:
定理 comp_ι_sq_zero
  条件: (g : ExteriorAlgebra R M ->ₐ[R] A) (m : M)
  结论: g (ι R m) * g (ι R m) = 0
  证明: by
  rw [← map_mul]; rw [ι_sq_zero]; rw [map_zero]

Depends on / 依赖: map_mul, map_zero
-/
theorem comp_ι_sq_zero (g : ExteriorAlgebra R M ->ₐ[R] A) (m : M) : g (ι R m) * g (ι R m) = 0 := by
  rw [← map_mul]; rw [ι_sq_zero]; rw [map_zero]

variable (R)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `ExteriorAlgebra R M` to `A`.
-/
@[simps! symm_apply]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : { f : M ->ₗ[R] A // forall m, f m * f m = 0 } ≃ (ExteriorAlgebra R M ->ₐ[R] A)
  body: Equiv.trans (Equiv.subtypeEquiv (Equiv.refl _) <| by simp) CliffordAlgebra.lift _

@[simp]

中文:
定义 lift
  签名: : { f : M ->ₗ[R] A // 对任意 m, f m * f m = 0 } ≃ (ExteriorAlgebra R M ->ₐ[R] A)
  定义体: Equiv.trans (Equiv.subtypeEquiv (Equiv.refl _) <| by simp) CliffordAlgebra.lift _

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, Equiv.refl, Equiv.subtypeEquiv, Equiv.trans, subtypeEquiv
-/
def lift : { f : M ->ₗ[R] A // forall m, f m * f m = 0 } ≃ (ExteriorAlgebra R M ->ₐ[R] A) :=
Equiv.trans (Equiv.subtypeEquiv (Equiv.refl _) <| by simp) CliffordAlgebra.lift _

@[simp]
/--
theorem `ι_comp_lift` / 定理 `ι_comp_lift`

English:
theorem ι_comp_lift
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0)
  proof: CliffordAlgebra.ι_comp_lift f _

@[simp]

中文:
定理 ι_comp_lift
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = 0)
  证明: CliffordAlgebra.ι_comp_lift f _

@[simp]

Depends on / 依赖: CliffordAlgebra
-/
theorem ι_comp_lift (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0) :
    (lift R ⟨f, cond⟩).toLinearMap.comp (ι R) = f :=
  CliffordAlgebra.ι_comp_lift f _

@[simp]
/--
theorem `lift_ι_apply` / 定理 `lift_ι_apply`

English:
theorem lift_ι_apply
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0) (x)
  proof: CliffordAlgebra.lift_ι_apply f _ x

中文:
定理 lift_ι_apply
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = 0) (x)
  证明: CliffordAlgebra.lift_ι_apply f _ x

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift_
-/
theorem lift_ι_apply (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0) (x) :
    lift R ⟨f, cond⟩ (ι R x) = f x :=
  CliffordAlgebra.lift_ι_apply f _ x

-- removing `@[simp]` because the LHS is not in simp normal form
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0) (g : ExteriorAlgebra R M ->ₐ[R] A)
  proof: CliffordAlgebra.lift_unique f _ _

中文:
定理 lift_unique
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = 0) (g : ExteriorAlgebra R M ->ₐ[R] A)
  证明: CliffordAlgebra.lift_unique f _ _

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift_unique, lift_unique
-/
theorem lift_unique (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0) (g : ExteriorAlgebra R M ->ₐ[R] A) :
    g.toLinearMap.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
  CliffordAlgebra.lift_unique f _ _

variable {R}

@[simp]
/--
theorem `lift_comp_ι` / 定理 `lift_comp_ι`

English:
theorem lift_comp_ι
  given: (g : ExteriorAlgebra R M ->ₐ[R] A)
  proof: CliffordAlgebra.lift_comp_ι g

中文:
定理 lift_comp_ι
  条件: (g : ExteriorAlgebra R M ->ₐ[R] A)
  证明: CliffordAlgebra.lift_comp_ι g

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift_comp_
-/
theorem lift_comp_ι (g : ExteriorAlgebra R M ->ₐ[R] A) :
    lift R ⟨g.toLinearMap.comp (ι R), comp_ι_sq_zero _⟩ = g :=
  CliffordAlgebra.lift_comp_ι g

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {f g : ExteriorAlgebra R M ->ₐ[R] A}
  proof: CliffordAlgebra.hom_ext h

中文:
定理 hom_ext
  结论: {f g : ExteriorAlgebra R M ->ₐ[R] A}
  证明: CliffordAlgebra.hom_ext h

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.hom_ext, hom_ext
-/
theorem hom_ext {f g : ExteriorAlgebra R M ->ₐ[R] A}
    (h : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g :=
  CliffordAlgebra.hom_ext h

/-- If `C` holds for the `algebraMap` of `r : R` into `ExteriorAlgebra R M`, the `ι` of `x : M`,
and is preserved under addition and multiplication, then it holds for all of `ExteriorAlgebra R M`.
-/
@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {C : ExteriorAlgebra R M -> Prop}
  proof: CliffordAlgebra.induction algebraMap ι mul add a

中文:
定理 induction
  结论: {C : ExteriorAlgebra R M -> 命题}
  证明: CliffordAlgebra.induction algebraMap ι mul add a

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.induction, algebraMap
-/
theorem induction {C : ExteriorAlgebra R M -> Prop}
    (algebraMap : forall r, C (algebraMap R (ExteriorAlgebra R M) r)) (ι : forall x, C (ι R x))
    (mul : forall a b, C a -> C b -> C (a * b)) (add : forall a b, C a -> C b -> C (a + b))
    (a : ExteriorAlgebra R M) : C a :=
  CliffordAlgebra.induction algebraMap ι mul add a

/--
Definition of `algebraMapInv` / `algebraMapInv` 的定义

English:
definition algebraMapInv
  signature: : ExteriorAlgebra R M ->ₐ[R] R
  body: ExteriorAlgebra.lift R ⟨(0 : M ->ₗ[R] R), fun _ => by simp⟩

中文:
定义 algebraMapInv
  签名: : ExteriorAlgebra R M ->ₐ[R] R
  定义体: ExteriorAlgebra.lift R ⟨(0 : M ->ₗ[R] R), fun _ => by simp⟩

Depends on / 依赖: ExteriorAlgebra, ExteriorAlgebra.lift
-/
def algebraMapInv : ExteriorAlgebra R M ->ₐ[R] R :=
  ExteriorAlgebra.lift R ⟨(0 : M ->ₗ[R] R), fun _ => by simp⟩

variable (M)

/--
theorem `algebraMap_leftInverse` / 定理 `algebraMap_leftInverse`

English:
theorem algebraMap_leftInverse
  proof: fun x => by
  simp [algebraMapInv]

@[simp]

中文:
定理 algebraMap_leftInverse
  证明: fun x => by
  simp [algebraMapInv]

@[simp]

Depends on / 依赖: algebraMapInv
-/
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M) := fun x => by
  simp [algebraMapInv]

@[simp]
/--
theorem `algebraMap_inj` / 定理 `algebraMap_inj`

English:
theorem algebraMap_inj
  given: (x y : R)
  proof: (algebraMap_leftInverse M).injective.eq_iff

@[simp]

中文:
定理 algebraMap_inj
  条件: (x y : R)
  证明: (algebraMap_leftInverse M).injective.eq_iff

@[simp]

Depends on / 依赖: algebraMap_leftInverse, eq_iff, injective, injective.eq_iff
-/
theorem algebraMap_inj (x y : R) :
    algebraMap R (ExteriorAlgebra R M) x = algebraMap R (ExteriorAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff

@[simp]
/--
theorem `algebraMap_eq_zero_iff` / 定理 `algebraMap_eq_zero_iff`

English:
theorem algebraMap_eq_zero_iff
  given: (x : R)
  statement: algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0
  proof: map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]

中文:
定理 algebraMap_eq_zero_iff
  条件: (x : R)
  结论: algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0
  证明: map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]

Depends on / 依赖: algebraMap, algebraMap_leftInverse, injective, map_eq_zero_iff
-/
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]
/--
theorem `algebraMap_eq_one_iff` / 定理 `algebraMap_eq_one_iff`

English:
theorem algebraMap_eq_one_iff
  given: (x : R)
  statement: algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1
  proof: map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[instance]

中文:
定理 algebraMap_eq_one_iff
  条件: (x : R)
  结论: algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1
  证明: map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[instance]

Depends on / 依赖: algebraMap, algebraMap_leftInverse, injective, map_eq_one_iff
-/
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[instance]
/--
theorem `isLocalHom_algebraMap` / 定理 `isLocalHom_algebraMap`

English:
theorem isLocalHom_algebraMap
  statement: IsLocalHom (algebraMap R (ExteriorAlgebra R M))
  proof: isLocalHom_of_leftInverse _ (algebraMap_leftInverse M)

中文:
定理 isLocalHom_algebraMap
  结论: IsLocalHom (algebraMap R (ExteriorAlgebra R M))
  证明: isLocalHom_of_leftInverse _ (algebraMap_leftInverse M)

Depends on / 依赖: algebraMap_leftInverse, isLocalHom_of_leftInverse
-/
theorem isLocalHom_algebraMap : IsLocalHom (algebraMap R (ExteriorAlgebra R M)) :=
  isLocalHom_of_leftInverse _ (algebraMap_leftInverse M)

/--
theorem `isUnit_algebraMap` / 定理 `isUnit_algebraMap`

English:
theorem isUnit_algebraMap
  given: (r : R)
  statement: IsUnit (algebraMap R (ExteriorAlgebra R M) r) ↔ IsUnit r
  proof: isUnit_map_of_leftInverse _ (algebraMap_leftInverse M)

中文:
定理 isUnit_algebraMap
  条件: (r : R)
  结论: IsUnit (algebraMap R (ExteriorAlgebra R M) r) ↔ IsUnit r
  证明: isUnit_map_of_leftInverse _ (algebraMap_leftInverse M)

Depends on / 依赖: algebraMap_leftInverse, isUnit_map_of_leftInverse
-/
theorem isUnit_algebraMap (r : R) : IsUnit (algebraMap R (ExteriorAlgebra R M) r) ↔ IsUnit r :=
  isUnit_map_of_leftInverse _ (algebraMap_leftInverse M)

/-- Invertibility in the exterior algebra is the same as invertibility of the base ring. -/
@[simps!]
/--
Definition of `invertibleAlgebraMapEquiv` / `invertibleAlgebraMapEquiv` 的定义

English:
definition invertibleAlgebraMapEquiv
  signature: (r : R)
  body: invertibleEquivOfLeftInverse _ _ _ (algebraMap_leftInverse M)

中文:
定义 invertibleAlgebraMapEquiv
  签名: (r : R)
  定义体: invertibleEquivOfLeftInverse _ _ _ (algebraMap_leftInverse M)

Depends on / 依赖: algebraMap_leftInverse, invertibleEquivOfLeftInverse
-/
def invertibleAlgebraMapEquiv (r : R) :
    Invertible (algebraMap R (ExteriorAlgebra R M) r) ≃ Invertible r :=
  invertibleEquivOfLeftInverse _ _ _ (algebraMap_leftInverse M)

variable {M}

/--
Definition of `toTrivSqZeroExt` / `toTrivSqZeroExt` 的定义

English:
definition toTrivSqZeroExt
  signature: [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  body: lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩

@[simp]

中文:
定义 toTrivSqZeroExt
  签名: [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  定义体: lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩

@[simp]

Depends on / 依赖: TrivSqZeroExt, TrivSqZeroExt.inrHom, TrivSqZeroExt.inr_mul_inr, inrHom, inr_mul_inr
-/
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    ExteriorAlgebra R M ->ₐ[R] TrivSqZeroExt R M :=
  lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩

@[simp]
/--
theorem `toTrivSqZeroExt_ι` / 定理 `toTrivSqZeroExt_ι`

English:
theorem toTrivSqZeroExt_ι
  given: [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M)
  proof: lift_ι_apply _ _ _ _

中文:
定理 toTrivSqZeroExt_ι
  条件: [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M)
  证明: lift_ι_apply _ _ _ _
-/
theorem toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M) :
    toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _ _ _

/--
Definition of `ιInv` / `ιInv` 的定义

English:
definition ιInv
  signature: : ExteriorAlgebra R M ->ₗ[R] M
  body: by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap

中文:
定义 ιInv
  签名: : ExteriorAlgebra R M ->ₗ[R] M
  定义体: by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap

Depends on / 依赖: IsCentralScalar, Module, Module.compHom, RingHom, RingHom.id, TrivSqZeroExt, TrivSqZeroExt.sndHom, compHom, fromOpposite, mul_comm, sndHom, toLinearMap, toTrivSqZeroExt, toTrivSqZeroExt.toLinearMap
-/
def ιInv : ExteriorAlgebra R M ->ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap

/--
theorem `ι_leftInverse` / 定理 `ι_leftInverse`

English:
theorem ι_leftInverse
  statement: Function.LeftInverse ιInv (ι R : M -> ExteriorAlgebra R M)
  proof: fun x => by
  simp [ιInv]

中文:
定理 ι_leftInverse
  结论: Function.LeftInverse ιInv (ι R : M -> ExteriorAlgebra R M)
  证明: fun x => by
  simp [ιInv]
-/
theorem ι_leftInverse : Function.LeftInverse ιInv (ι R : M -> ExteriorAlgebra R M) := fun x => by
  simp [ιInv]

variable (R) in
@[simp]
/--
theorem `ι_inj` / 定理 `ι_inj`

English:
theorem ι_inj
  given: (x y : M)
  statement: ι R x = ι R y ↔ x = y
  proof: ι_leftInverse.injective.eq_iff

@[simp]

中文:
定理 ι_inj
  条件: (x y : M)
  结论: ι R x = ι R y ↔ x = y
  证明: ι_leftInverse.injective.eq_iff

@[simp]

Depends on / 依赖: _leftInverse.injective.eq_iff, eq_iff, injective
-/
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.injective.eq_iff

@[simp]
/--
theorem `ι_eq_zero_iff` / 定理 `ι_eq_zero_iff`

English:
theorem ι_eq_zero_iff
  given: (x : M)
  statement: ι R x = 0 ↔ x = 0
  proof: by rw [← ι_inj R x 0, map_zero]

@[simp]

中文:
定理 ι_eq_zero_iff
  条件: (x : M)
  结论: ι R x = 0 ↔ x = 0
  证明: by rw [← ι_inj R x 0, map_zero]

@[simp]

Depends on / 依赖: map_zero
-/
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by rw [← ι_inj R x 0, map_zero]

@[simp]
/--
theorem `ι_eq_algebraMap_iff` / 定理 `ι_eq_algebraMap_iff`

English:
theorem ι_eq_algebraMap_iff
  given: (x : M) (r : R)
  statement: ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    have : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := toTrivSqZeroExt_ι _
    rw [h]; rw [AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x 

中文:
定理 ι_eq_algebraMap_iff
  条件: (x : M) (r : R)
  结论: ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    have : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := toTrivSqZeroExt_ι _
    rw [h]; rw [AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x 

Depends on / 依赖: AlgHom, AlgHom.commutes, Eq.symm, IsCentralScalar, Module, Module.compHom, Prod.ext_iff, RingHom, RingHom.id, commutes, compHom, ext_iff, fromOpposite, imp_left, map_zero, mul_comm, this.symm.imp_left, toTrivSqZeroExt
-/
theorem ι_eq_algebraMap_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    have : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := toTrivSqZeroExt_ι _
    rw [h]; rw [AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
  · rintro ⟨rfl, rfl⟩
    rw [map_zero]; rw [map_zero]

@[simp]
/--
theorem `ι_ne_one` / 定理 `ι_ne_one`

English:
theorem ι_ne_one
  given: [Nontrivial R] (x : M)
  statement: ι R x != 1
  proof: by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one]; rw [Ne]; rw [ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right

中文:
定理 ι_ne_one
  条件: [Nontrivial R] (x : M)
  结论: ι R x != 1
  证明: by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one]; rw [Ne]; rw [ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right

Depends on / 依赖: And.right, ExteriorAlgebra, algebraMap, map_one, one_ne_zero
-/
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x != 1 := by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one]; rw [Ne]; rw [ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right

/--
theorem `ι_range_disjoint_one` / 定理 `ι_range_disjoint_one`

English:
theorem ι_range_disjoint_one
  proof: by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ h
  obtain ⟨r, rfl : algebraMap R (ExteriorAlgebra R M) r = _⟩ := Submodule.mem_one.mp h
  rw [ι_eq_algebraMap_iff x] at hx
  rw [hx.2]; rw [map_zero]

@[simp]

中文:
定理 ι_range_disjoint_one
  证明: by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ h
  obtain ⟨r, rfl : algebraMap R (ExteriorAlgebra R M) r = _⟩ := Submodule.mem_one.mp h
  rw [ι_eq_algebraMap_iff x] at hx
  rw [hx.2]; rw [map_zero]

@[simp]

Depends on / 依赖: ExteriorAlgebra, Submodule, Submodule.disjoint_def, Submodule.mem_one.mp, algebraMap, disjoint_def, map_zero, mem_one
-/
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M))
      (1 : Submodule R (ExteriorAlgebra R M)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ h
  obtain ⟨r, rfl : algebraMap R (ExteriorAlgebra R M) r = _⟩ := Submodule.mem_one.mp h
  rw [ι_eq_algebraMap_iff x] at hx
  rw [hx.2]; rw [map_zero]

@[simp]
/--
theorem `ι_add_mul_swap` / 定理 `ι_add_mul_swap`

English:
theorem ι_add_mul_swap
  given: (x y : M)
  statement: ι R x * ι R y + ι R y * ι R x = 0
  proof: CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho .all _ _

中文:
定理 ι_add_mul_swap
  条件: (x y : M)
  结论: ι R x * ι R y + ι R y * ι R x = 0
  证明: CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho .all _ _

Depends on / 依赖: CliffordAlgebra
-/
theorem ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho .all _ _

/--
theorem `ι_mul_prod_list` / 定理 `ι_mul_prod_list`

English:
theorem ι_mul_prod_list
  given: {n : Nat} (f : Fin n -> M) (i : Fin n)
  proof: by
  induction n with
  | zero => exact i.elim0
  | succ n hn =>
    rw [List.ofFn_succ]; rw [List.prod_cons]; rw [← mul_assoc]
    by_cases h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
    · replace hn :=
congr_arg (ι R (f 0) * ·) hn (fun i => f <| Fin.succ i) (i.pred h)
      rw [Fin.succ_pred]; rw

中文:
定理 ι_mul_prod_list
  条件: {n : 自然数} (f : Fin n -> M) (i : Fin n)
  证明: by
  induction n with
  | zero => exact i.elim0
  | succ n hn =>
    rw [List.ofFn_succ]; rw [List.prod_cons]; rw [← mul_assoc]
    by_cases h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
    · replace hn :=
congr_arg (ι R (f 0) * ·) hn (fun i => f <| Fin.succ i) (i.pred h)
      rw [Fin.succ_pred]; rw

Depends on / 依赖: Fin.succ, Fin.succ_pred, List.ofFn_succ, List.prod_cons, add_mul, congr_arg, eq_zero_iff_eq_zero_of_add_eq_zero, i.elim0, i.pred, mul_assoc, mul_zero, ofFn_succ, prod_cons, replace, succ_pred, zero_mul
-/
theorem ι_mul_prod_list {n : Nat} (f : Fin n -> M) (i : Fin n) :
    (ι R <| f i) * (List.ofFn fun i => ι R <| f i).prod = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n hn =>
    rw [List.ofFn_succ]; rw [List.prod_cons]; rw [← mul_assoc]
    by_cases h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
    · replace hn :=
congr_arg (ι R (f 0) * ·) hn (fun i => f <| Fin.succ i) (i.pred h)
      rw [Fin.succ_pred]; rw [← mul_assoc]; rw [mul_zero] at hn
      refine (eq_zero_iff_eq_zero_of_add_eq_zero ?_).mp hn
      rw [← add_mul]; rw [ι_add_mul_swap]; rw [zero_mul]

end

variable (R) in
/--
Definition of `ιMulti` / `ιMulti` 的定义

English:
definition ιMulti
  signature: (n : Nat)
  body: let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun _ => ι R
  { F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      dsimp [F]
      clear F
      wlog h : x < y
      · exact this R n f y x hfxy.symm hxy.symm (hxy.lt_or_gt.resolve_left h)
      clear hxy

中文:
定义 ιMulti
  签名: (n : 自然数)
  定义体: let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun _ => ι R
  { F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      dsimp [F]
      clear F
      wlog h : x < y
      · exact this R n f y x hfxy.symm hxy.symm (hxy.lt_or_gt.resolve_left h)
      clear hxy

Depends on / 依赖: ExteriorAlgebra, List.ofFn_succ, List.prod_cons, MultilinearMap, MultilinearMap.mkPiAlgebraFin, compLinearMap, hfxy.symm, hxy.lt_or_gt.resolve_left, hxy.symm, lt_or_gt, map_eq_zero_of_eq, mkPiAlgebraFin, ofFn_succ, prod_cons, resolve_left, x.elim0
-/
def ιMulti (n : Nat) : M [⋀^Fin n]->ₗ[R] ExteriorAlgebra R M :=
  let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun _ => ι R
  { F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      dsimp [F]
      clear F
      wlog h : x < y
      · exact this R n f y x hfxy.symm hxy.symm (hxy.lt_or_gt.resolve_left h)
      clear hxy
      induction n with
      | zero => exact x.elim0
      | succ n hn =>
        rw [List.ofFn_succ]; rw [List.prod_cons]
        by_cases hx : x = 0
        -- one of the repeated terms is on the left
        · rw [hx] at hfxy h
          rw [hfxy]; rw [← Fin.succ_pred y (ne_of_lt h).symm]
          exact ι_mul_prod_list (f ∘ Fin.succ) _
        -- ignore the left-most term and induct on the remaining ones, decrementing indices
        · convert! mul_zero (ι R (f 0))
          refine
            hn
              (fun i => f <| Fin.succ i) (x.pred hx)
              (y.pred (ne_of_lt <| lt_of_le_of_lt x.zero_le h).symm) ?_
              (Fin.pred_lt_pred_iff.mpr h)
          simp only [Fin.succ_pred]
          exact hfxy
    toFun := F }

/--
theorem `ιMulti_apply` / 定理 `ιMulti_apply`

English:
theorem ιMulti_apply
  given: {n : Nat} (v : Fin n -> M)
  statement: ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod
  proof: rfl

@[simp]

中文:
定理 ιMulti_apply
  条件: {n : 自然数} (v : Fin n -> M)
  结论: ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod
  证明: rfl

@[simp]
-/
theorem ιMulti_apply {n : Nat} (v : Fin n -> M) : ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod :=
  rfl

@[simp]
/--
theorem `ιMulti_zero_apply` / 定理 `ιMulti_zero_apply`

English:
theorem ιMulti_zero_apply
  given: (v : Fin 0 -> M)
  statement: ιMulti R 0 v = 1
  proof: by
  simp [ιMulti]

@[simp]

中文:
定理 ιMulti_zero_apply
  条件: (v : Fin 0 -> M)
  结论: ιMulti R 0 v = 1
  证明: by
  simp [ιMulti]

@[simp]
-/
theorem ιMulti_zero_apply (v : Fin 0 -> M) : ιMulti R 0 v = 1 := by
  simp [ιMulti]

@[simp]
/--
theorem `ιMulti_succ_apply` / 定理 `ιMulti_succ_apply`

English:
theorem ιMulti_succ_apply
  given: {n : Nat} (v : Fin n.succ -> M)
  proof: by
  simp [ιMulti, Matrix.vecTail]

中文:
定理 ιMulti_succ_apply
  条件: {n : 自然数} (v : Fin n.succ -> M)
  证明: by
  simp [ιMulti, Matrix.vecTail]

Depends on / 依赖: Matrix, Matrix.vecTail, vecTail
-/
theorem ιMulti_succ_apply {n : Nat} (v : Fin n.succ -> M) :
    ιMulti R _ v = ι R (v 0) * ιMulti R _ (Matrix.vecTail v) := by
  simp [ιMulti, Matrix.vecTail]

/--
theorem `ιMulti_succ_curryLeft` / 定理 `ιMulti_succ_curryLeft`

English:
theorem ιMulti_succ_curryLeft
  given: {n : Nat} (m : M)
  proof: by
  ext; simp

中文:
定理 ιMulti_succ_curryLeft
  条件: {n : 自然数} (m : M)
  证明: by
  ext; simp
-/
theorem ιMulti_succ_curryLeft {n : Nat} (m : M) :
    (ιMulti R n.succ).curryLeft m =
      (LinearMap.mulLeft R (ι R m)).compAlternatingMap (ιMulti R n) := by
  ext; simp

/--
lemma `ιMulti_eq_zero_of_not_inj` / 引理 `ιMulti_eq_zero_of_not_inj`

English:
lemma ιMulti_eq_zero_of_not_inj
  given: {n : Nat} {v : Fin n -> M} (hv : ¬Function.Injective v)
  proof: (ιMulti R n).map_eq_zero_of_not_injective v hv

中文:
引理 ιMulti_eq_zero_of_not_inj
  条件: {n : 自然数} {v : Fin n -> M} (hv : ¬Function.Injective v)
  证明: (ιMulti R n).map_eq_zero_of_not_injective v hv

Depends on / 依赖: map_eq_zero_of_not_injective
-/
lemma ιMulti_eq_zero_of_not_inj {n : Nat} {v : Fin n -> M} (hv : ¬Function.Injective v) :
    ιMulti R n v = 0 :=
  (ιMulti R n).map_eq_zero_of_not_injective v hv

/--
lemma `ιMulti_mul_ιMulti` / 引理 `ιMulti_mul_ιMulti`

English:
lemma ιMulti_mul_ιMulti
  given: {m n : Nat} (a : Fin m -> M) (b : Fin n -> M)
  proof: by
  simp only [ιMulti_apply]
  change _ = (List.ofFn ((ι R) ∘ Fin.append a b)).prod
  rw [← List.map_ofFn]; rw [List.ofFn_fin_append]; rw [List.map_append]; rw [List.prod_append]
  simp only [List.map_ofFn]
  congr

中文:
引理 ιMulti_mul_ιMulti
  条件: {m n : 自然数} (a : Fin m -> M) (b : Fin n -> M)
  证明: by
  simp only [ιMulti_apply]
  change _ = (List.ofFn ((ι R) ∘ Fin.append a b)).prod
  rw [← List.map_ofFn]; rw [List.ofFn_fin_append]; rw [List.map_append]; rw [List.prod_append]
  simp only [List.map_ofFn]
  congr

Depends on / 依赖: Fin.append, List.map_append, List.map_ofFn, List.ofFn, List.ofFn_fin_append, List.prod_append, append, map_append, map_ofFn, ofFn_fin_append, prod_append
-/
lemma ιMulti_mul_ιMulti {m n : Nat} (a : Fin m -> M) (b : Fin n -> M) :
    ιMulti R m a * ιMulti R n b = ιMulti R (m + n) (Fin.append a b) := by
  simp only [ιMulti_apply]
  change _ = (List.ofFn ((ι R) ∘ Fin.append a b)).prod
  rw [← List.map_ofFn]; rw [List.ofFn_fin_append]; rw [List.map_append]; rw [List.prod_append]
  simp only [List.map_ofFn]
  congr

variable (R)

/--
lemma `ιMulti_range` / 引理 `ιMulti_range`

English:
lemma ιMulti_range
  given: (n : Nat)
  proof: by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  exact ⟨fun i => ⟨ι R (v i), LinearMap.mem_range_self _ _⟩, rfl⟩

中文:
引理 ιMulti_range
  条件: (n : 自然数)
  证明: by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  exact ⟨fun i => ⟨ι R (v i), LinearMap.mem_range_self _ _⟩, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, Set.mem_pow, Set.range_subset_iff, Submodule, Submodule.pow_subset_pow, mem_pow, mem_range_self, pow_subset_pow, range_subset_iff, subseteq
-/
lemma ιMulti_range (n : Nat) :
    Set.range (ιMulti R n (M := M)) subseteq ↑(⋀[R]^n M) := by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  exact ⟨fun i => ⟨ι R (v i), LinearMap.mem_range_self _ _⟩, rfl⟩

/--
lemma `ιMulti_span_fixedDegree` / 引理 `ιMulti_span_fixedDegree`

English:
lemma ιMulti_span_fixedDegree
  given: (n : Nat)
  proof: by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R n)) ?_
  rw [exteriorPower]; rw [Submodule.pow_eq_span_pow_set]; rw [Submodule.span_le]
  refine fun u hu => Submodule.subset_span ?_
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hu
  refine ⟨fun i => ιInv (f i).1, ?_⟩
  rw [ιMulti_apply]
  congr w

中文:
引理 ιMulti_span_fixedDegree
  条件: (n : 自然数)
  证明: by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R n)) ?_
  rw [exteriorPower]; rw [Submodule.pow_eq_span_pow_set]; rw [Submodule.span_le]
  refine fun u hu => Submodule.subset_span ?_
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hu
  refine ⟨fun i => ιInv (f i).1, ?_⟩
  rw [ιMulti_apply]
  congr w

Depends on / 依赖: Set.mem_pow.mp, Submodule, Submodule.pow_eq_span_pow_set, Submodule.span_le, Submodule.subset_span, exteriorPower, le_antisymm, mem_pow, pow_eq_span_pow_set, span_le, subset_span
-/
lemma ιMulti_span_fixedDegree (n : Nat) :
    Submodule.span R (Set.range (ιMulti R n)) = ⋀[R]^n M := by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R n)) ?_
  rw [exteriorPower]; rw [Submodule.pow_eq_span_pow_set]; rw [Submodule.span_le]
  refine fun u hu => Submodule.subset_span ?_
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hu
  refine ⟨fun i => ιInv (f i).1, ?_⟩
  rw [ιMulti_apply]
  congr with i
  obtain ⟨v, hv⟩ := (f i).prop
  rw [← hv]; rw [ι_leftInverse]

/--
Definition of `ιMulti_family` / `ιMulti_family` 的定义

English:
abbreviation ιMulti_family
  signature: (n : Nat) {I : Type*} [LinearOrder I] (v : I -> M)
  body: ιMulti R n (v ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))

中文:
缩写 ιMulti_family
  签名: (n : 自然数) {I : 类型} [LinearOrder I] (v : I -> M)
  定义体: ιMulti R n (v ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))

Depends on / 依赖: Set.powersetCard.ofFinEmbEquiv.symm, ofFinEmbEquiv, powersetCard
-/
abbrev ιMulti_family (n : Nat) {I : Type*} [LinearOrder I] (v : I -> M)
    (s : Set.powersetCard I n) : ExteriorAlgebra R M :=
  ιMulti R n (v ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))

open Set Set.powersetCard

/--
lemma `ιMulti_family_mul_of_not_disjoint` / 引理 `ιMulti_family_mul_of_not_disjoint`

English:
lemma ιMulti_family_mul_of_not_disjoint
  statement: {m n : Nat} {I : Type*} [LinearOrder I] (v : I -> M)
  proof: by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨i, his, hit⟩ := h
  obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  obtain ⟨k, hk⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  apply AlternatingMap.map_eq_zero_of_eq (i 

中文:
引理 ιMulti_family_mul_of_not_disjoint
  结论: {m n : 自然数} {I : 类型} [LinearOrder I] (v : I -> M)
  证明: by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨i, his, hit⟩ := h
  obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  obtain ⟨k, hk⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  apply AlternatingMap.map_eq_zero_of_eq (i 

Depends on / 依赖: AlternatingMap, AlternatingMap.map_eq_zero_of_eq, Fin.castAdd, Fin.natAdd, Finset, Finset.not_disjoint_iff, castAdd, lt_of_lt_of_le, map_eq_zero_of_eq, mem_range_ofFinEmbEquiv_symm_iff_mem, natAdd, ne_of_lt, not_disjoint_iff
-/
lemma ιMulti_family_mul_of_not_disjoint {m n : Nat} {I : Type*} [LinearOrder I] (v : I -> M)
    (s : powersetCard I m) (t : powersetCard I n) (h : ¬Disjoint s.val t.val) :
    ιMulti_family R m v s * ιMulti_family R n v t = 0 := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨i, his, hit⟩ := h
  obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  obtain ⟨k, hk⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  apply AlternatingMap.map_eq_zero_of_eq (i := Fin.castAdd n j) (j := Fin.natAdd m k)
  · simp [hj, hk]
  · apply ne_of_lt
    apply lt_of_lt_of_le (b := m) <;> simp

/--
lemma `ιMulti_family_mul_of_disjoint` / 引理 `ιMulti_family_mul_of_disjoint`

English:
lemma ιMulti_family_mul_of_disjoint
  statement: {m n : Nat} {I : Type*} [LinearOrder I] (v : I -> M)
  proof: by
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  rw [← AlternatingMap.map_perm]; rw [permOfDisjoint]
  congr
  ext i
  let e := powersetCard.orderIsoOfFin (powersetCard.disjUnion h)
  change _ = v (e (e.symm _))
  by_cases! hi : i < m
  · rw [← Fin.castAdd_castLT n i hi, Fin.append_left, OrderIso

中文:
引理 ιMulti_family_mul_of_disjoint
  结论: {m n : 自然数} {I : 类型} [LinearOrder I] (v : I -> M)
  证明: by
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  rw [← AlternatingMap.map_perm]; rw [permOfDisjoint]
  congr
  ext i
  let e := powersetCard.orderIsoOfFin (powersetCard.disjUnion h)
  change _ = v (e (e.symm _))
  by_cases! hi : i < m
  · rw [← Fin.castAdd_castLT n i hi, Fin.append_left, OrderIso

Depends on / 依赖: AlternatingMap, AlternatingMap.map_perm, Fin.append_left, Fin.append_right, Fin.castAdd_castLT, Fin.natAdd_subNat_cast, OrderIso, OrderIso.apply_symm_apply, append_left, append_right, apply_symm_apply, castAdd_castLT, disjUnion, e.symm, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, map_perm, natAdd_subNat_cast, orderIsoOfFin, permOfDisjoint
-/
lemma ιMulti_family_mul_of_disjoint {m n : Nat} {I : Type*} [LinearOrder I] (v : I -> M)
    (s : powersetCard I m) (t : powersetCard I n) (h : Disjoint s.val t.val) :
    ιMulti_family R m v s * ιMulti_family R n v t =
      (permOfDisjoint h).sign • ιMulti_family R (m + n) v (disjUnion h) := by
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  rw [← AlternatingMap.map_perm]; rw [permOfDisjoint]
  congr
  ext i
  let e := powersetCard.orderIsoOfFin (powersetCard.disjUnion h)
  change _ = v (e (e.symm _))
  by_cases! hi : i < m
  · rw [← Fin.castAdd_castLT n i hi, Fin.append_left, OrderIso.apply_symm_apply,
      finSumFinEquiv_symm_apply_castAdd]
    aesop
  · rw [← Fin.natAdd_subNat_cast hi, Fin.append_right, OrderIso.apply_symm_apply,
      finSumFinEquiv_symm_apply_natAdd]
    aesop

variable {R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (ExteriorAlgebra R M)
  body: (algebraMap_leftInverse M).injective.nontrivial

中文:
实例 [Nontrivial
  签名: R] : Nontrivial (ExteriorAlgebra R M)
  定义体: (algebraMap_leftInverse M).injective.nontrivial

Depends on / 依赖: algebraMap_leftInverse, injective, injective.nontrivial, nontrivial
-/
instance [Nontrivial R] : Nontrivial (ExteriorAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

/-! Functoriality of the exterior algebra. -/

variable {N : Type u4} {N' : Type u5} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R] N)
  body: CliffordAlgebra.map { f with map_app' := fun _ => rfl }

@[simp]

中文:
定义 map
  签名: (f : M ->ₗ[R] N)
  定义体: CliffordAlgebra.map { f with map_app' := fun _ => rfl }

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map, map_app
-/
def map (f : M ->ₗ[R] N) : ExteriorAlgebra R M ->ₐ[R] ExteriorAlgebra R N :=
  CliffordAlgebra.map { f with map_app' := fun _ => rfl }

@[simp]
/--
theorem `map_comp_ι` / 定理 `map_comp_ι`

English:
theorem map_comp_ι
  given: (f : M ->ₗ[R] N)
  statement: (map f).toLinearMap ∘ₗ ι R = ι R ∘ₗ f
  proof: CliffordAlgebra.map_comp_ι _

@[simp]

中文:
定理 map_comp_ι
  条件: (f : M ->ₗ[R] N)
  结论: (map f).toLinearMap ∘ₗ ι R = ι R ∘ₗ f
  证明: CliffordAlgebra.map_comp_ι _

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map_comp_
-/
theorem map_comp_ι (f : M ->ₗ[R] N) : (map f).toLinearMap ∘ₗ ι R = ι R ∘ₗ f :=
  CliffordAlgebra.map_comp_ι _

@[simp]
/--
theorem `map_apply_ι` / 定理 `map_apply_ι`

English:
theorem map_apply_ι
  given: (f : M ->ₗ[R] N) (m : M)
  statement: map f (ι R m) = ι R (f m)
  proof: CliffordAlgebra.map_apply_ι _ m

@[simp]

中文:
定理 map_apply_ι
  条件: (f : M ->ₗ[R] N) (m : M)
  结论: map f (ι R m) = ι R (f m)
  证明: CliffordAlgebra.map_apply_ι _ m

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map_apply_
-/
theorem map_apply_ι (f : M ->ₗ[R] N) (m : M) : map f (ι R m) = ι R (f m) :=
  CliffordAlgebra.map_apply_ι _ m

@[simp]
/--
theorem `map_apply_ιMulti` / 定理 `map_apply_ιMulti`

English:
theorem map_apply_ιMulti
  given: {n : Nat} (f : M ->ₗ[R] N) (m : Fin n -> M)
  proof: by
  rw [ιMulti_apply]; rw [ιMulti_apply]; rw [map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, map_apply_ι]

@[simp]

中文:
定理 map_apply_ιMulti
  条件: {n : 自然数} (f : M ->ₗ[R] N) (m : Fin n -> M)
  证明: by
  rw [ιMulti_apply]; rw [ιMulti_apply]; rw [map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, map_apply_ι]

@[simp]

Depends on / 依赖: Function, Function.comp_def, List.map_ofFn, comp_def, map_list_prod, map_ofFn
-/
theorem map_apply_ιMulti {n : Nat} (f : M ->ₗ[R] N) (m : Fin n -> M) :
    map f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  rw [ιMulti_apply]; rw [ιMulti_apply]; rw [map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, map_apply_ι]

@[simp]
/--
theorem `map_comp_ιMulti` / 定理 `map_comp_ιMulti`

English:
theorem map_comp_ιMulti
  given: {n : Nat} (f : M ->ₗ[R] N)
  proof: by
  ext m
  exact map_apply_ιMulti _ _

@[simp]

中文:
定理 map_comp_ιMulti
  条件: {n : 自然数} (f : M ->ₗ[R] N)
  证明: by
  ext m
  exact map_apply_ιMulti _ _

@[simp]
-/
theorem map_comp_ιMulti {n : Nat} (f : M ->ₗ[R] N) :
    (map f).toLinearMap.compAlternatingMap (ιMulti R n (M := M)) =
    (ιMulti R n (M := N)).compLinearMap f := by
  ext m
  exact map_apply_ιMulti _ _

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  proof: CliffordAlgebra.map_id 0

@[simp]

中文:
定理 map_id
  证明: CliffordAlgebra.map_id 0

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map_id, map_id
-/
theorem map_id :
    map LinearMap.id = AlgHom.id R (ExteriorAlgebra R M) :=
  CliffordAlgebra.map_id 0

@[simp]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] N')
  proof: CliffordAlgebra.map_comp_map _ _

@[simp]

中文:
定理 map_comp_map
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] N')
  证明: CliffordAlgebra.map_comp_map _ _

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map_comp_map, map_comp_map
-/
theorem map_comp_map (f : M ->ₗ[R] N) (g : N ->ₗ[R] N') :
    AlgHom.comp (map g) (map f) = map (LinearMap.comp g f) :=
  CliffordAlgebra.map_comp_map _ _

@[simp]
/--
theorem `ι_range_map_map` / 定理 `ι_range_map_map`

English:
theorem ι_range_map_map
  given: (f : M ->ₗ[R] N)
  proof: CliffordAlgebra.ι_range_map_map _

中文:
定理 ι_range_map_map
  条件: (f : M ->ₗ[R] N)
  证明: CliffordAlgebra.ι_range_map_map _
-/
theorem ι_range_map_map (f : M ->ₗ[R] N) :
    Submodule.map (AlgHom.toLinearMap (map f)) (LinearMap.range (ι R (M := M))) =
    Submodule.map (ι R) (LinearMap.range f) :=
  CliffordAlgebra.ι_range_map_map _

/--
theorem `toTrivSqZeroExt_comp_map` / 定理 `toTrivSqZeroExt_comp_map`

English:
theorem toTrivSqZeroExt_comp_map
  statement: [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒᵖ N]
  proof: by
  apply hom_ext
  apply LinearMap.ext
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, toTrivSqZeroExt_ι, TrivSqZeroExt.map_inr, forall_const]

中文:
定理 toTrivSqZeroExt_comp_map
  结论: [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒᵖ N]
  证明: by
  apply hom_ext
  apply LinearMap.ext
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, toTrivSqZeroExt_ι, TrivSqZeroExt.map_inr, forall_const]

Depends on / 依赖: AlgHom, AlgHom.comp_toLinearMap, AlgHom.toLinearMap_apply, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.ext, TrivSqZeroExt, TrivSqZeroExt.map_inr, coe_comp, comp_apply, comp_toLinearMap, forall_const, hom_ext, map_inr, toLinearMap_apply
-/
theorem toTrivSqZeroExt_comp_map [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] (f : M ->ₗ[R] N) :
    toTrivSqZeroExt.comp (map f) = (TrivSqZeroExt.map f).comp toTrivSqZeroExt := by
  apply hom_ext
  apply LinearMap.ext
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, toTrivSqZeroExt_ι, TrivSqZeroExt.map_inr, forall_const]

/--
theorem `ιInv_comp_map` / 定理 `ιInv_comp_map`

English:
theorem ιInv_comp_map
  given: (f : M ->ₗ[R] N)
  proof: by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun r m => rfl⟩
  let : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R N := ⟨fun r m => rfl⟩
  unfold ιInv
  conv_lhs => rw [Linea

中文:
定理 ιInv_comp_map
  条件: (f : M ->ₗ[R] N)
  证明: by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun r m => rfl⟩
  let : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R N := ⟨fun r m => rfl⟩
  unfold ιInv
  conv_lhs => rw [Linea

Depends on / 依赖: AlgHom, AlgHom.comp_toLinearMap, IsCentralScalar, LinearMap, LinearMap.comp_assoc, Module, Module.compHom, RingHom, RingHom.id, TrivSqZeroExt, TrivSqZeroExt.sndHom_comp_map, compHom, comp_assoc, comp_toLinearMap, conv_lhs, fromOpposite, mul_comm, sndHom_comp_map, toTrivSqZeroExt_comp_map
-/
theorem ιInv_comp_map (f : M ->ₗ[R] N) :
    ιInv.comp (map f).toLinearMap = f.comp ιInv := by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun r m => rfl⟩
  let : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R N := ⟨fun r m => rfl⟩
  unfold ιInv
  conv_lhs => rw [LinearMap.comp_assoc, ← AlgHom.comp_toLinearMap, toTrivSqZeroExt_comp_map,
                AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc, TrivSqZeroExt.sndHom_comp_map]
  rfl

open Function in
/-- For a linear map `f` from `M` to `N`,
`ExteriorAlgebra.map g` is a retraction of `ExteriorAlgebra.map f` iff
`g` is a retraction of `f`. -/
@[simp]
/--
lemma `leftInverse_map_iff` / 引理 `leftInverse_map_iff`

English:
lemma leftInverse_map_iff
  given: {f : M ->ₗ[R] N} {g : N ->ₗ[R] M}
  proof: by
  refine ⟨fun h x => ?_, fun h => CliffordAlgebra.leftInverse_map_of_leftInverse _ _ h⟩
  simpa using h (ι _ x)

中文:
引理 leftInverse_map_iff
  条件: {f : M ->ₗ[R] N} {g : N ->ₗ[R] M}
  证明: by
  refine ⟨fun h x => ?_, fun h => CliffordAlgebra.leftInverse_map_of_leftInverse _ _ h⟩
  simpa using h (ι _ x)

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.leftInverse_map_of_leftInverse, leftInverse_map_of_leftInverse
-/
lemma leftInverse_map_iff {f : M ->ₗ[R] N} {g : N ->ₗ[R] M} :
    LeftInverse (map g) (map f) ↔ LeftInverse g f := by
  refine ⟨fun h x => ?_, fun h => CliffordAlgebra.leftInverse_map_of_leftInverse _ _ h⟩
  simpa using h (ι _ x)

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: {f : M ->ₗ[R] N} (hf : exists (g : N ->ₗ[R] M), g.comp f = LinearMap.id)
  proof: let ⟨_, hgf⟩ := hf; (leftInverse_map_iff.mpr (DFunLike.congr_fun hgf)).injective

中文:
引理 map_injective
  条件: {f : M ->ₗ[R] N} (hf : 存在 (g : N ->ₗ[R] M), g.comp f = LinearMap.id)
  证明: let ⟨_, hgf⟩ := hf; (leftInverse_map_iff.mpr (DFunLike.congr_fun hgf)).injective

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, injective, leftInverse_map_iff, leftInverse_map_iff.mpr
-/
lemma map_injective {f : M ->ₗ[R] N} (hf : exists (g : N ->ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map f) :=
  let ⟨_, hgf⟩ := hf; (leftInverse_map_iff.mpr (DFunLike.congr_fun hgf)).injective

/-- A morphism of modules is surjective if and only the morphism of exterior algebras that it
induces is surjective. -/
@[simp]
/--
lemma `map_surjective_iff` / 引理 `map_surjective_iff`

English:
lemma map_surjective_iff
  given: {f : M ->ₗ[R] N}
  proof: by
  refine ⟨fun h y => ?_, fun h => CliffordAlgebra.map_surjective _ h⟩
  obtain ⟨x, hx⟩ := h (ι R y)
  existsi ιInv x
  rw [← LinearMap.comp_apply]; rw [← ιInv_comp_map]; rw [LinearMap.comp_apply]
  simp [hx, ιInv]

中文:
引理 map_surjective_iff
  条件: {f : M ->ₗ[R] N}
  证明: by
  refine ⟨fun h y => ?_, fun h => CliffordAlgebra.map_surjective _ h⟩
  obtain ⟨x, hx⟩ := h (ι R y)
  existsi ιInv x
  rw [← LinearMap.comp_apply]; rw [← ιInv_comp_map]; rw [LinearMap.comp_apply]
  simp [hx, ιInv]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map_surjective, LinearMap, LinearMap.comp_apply, comp_apply, existsi, map_surjective
-/
lemma map_surjective_iff {f : M ->ₗ[R] N} :
    Function.Surjective (map f) ↔ Function.Surjective f := by
  refine ⟨fun h y => ?_, fun h => CliffordAlgebra.map_surjective _ h⟩
  obtain ⟨x, hx⟩ := h (ι R y)
  existsi ιInv x
  rw [← LinearMap.comp_apply]; rw [← ιInv_comp_map]; rw [LinearMap.comp_apply]
  simp [hx, ιInv]

variable {K E F : Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F]

/--
lemma `map_injective_field` / 引理 `map_injective_field`

English:
lemma map_injective_field
  given: {f : E ->ₗ[K] F} (hf : LinearMap.ker f = ⊥)
  proof: map_injective (LinearMap.exists_leftInverse_of_injective f hf)

中文:
引理 map_injective_field
  条件: {f : E ->ₗ[K] F} (hf : LinearMap.ker f = ⊥)
  证明: map_injective (LinearMap.exists_leftInverse_of_injective f hf)

Depends on / 依赖: LinearMap, LinearMap.exists_leftInverse_of_injective, exists_leftInverse_of_injective, map_injective
-/
lemma map_injective_field {f : E ->ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map f) :=
  map_injective (LinearMap.exists_leftInverse_of_injective f hf)

end ExteriorAlgebra

namespace TensorAlgebra

variable {R M}

/--
Definition of `toExterior` / `toExterior` 的定义

English:
definition toExterior
  signature: : TensorAlgebra R M ->ₐ[R] ExteriorAlgebra R M
  body: TensorAlgebra.lift R (ExteriorAlgebra.ι R : M ->ₗ[R] ExteriorAlgebra R M)

@[simp]

中文:
定义 toExterior
  签名: : TensorAlgebra R M ->ₐ[R] ExteriorAlgebra R M
  定义体: TensorAlgebra.lift R (ExteriorAlgebra.ι R : M ->ₗ[R] ExteriorAlgebra R M)

@[simp]

Depends on / 依赖: ExteriorAlgebra, TensorAlgebra, TensorAlgebra.lift
-/
def toExterior : TensorAlgebra R M ->ₐ[R] ExteriorAlgebra R M :=
  TensorAlgebra.lift R (ExteriorAlgebra.ι R : M ->ₗ[R] ExteriorAlgebra R M)

@[simp]
/--
theorem `toExterior_ι` / 定理 `toExterior_ι`

English:
theorem toExterior_ι
  given: (m : M)
  proof: by
  simp [toExterior]

中文:
定理 toExterior_ι
  条件: (m : M)
  证明: by
  simp [toExterior]

Depends on / 依赖: toExterior
-/
theorem toExterior_ι (m : M) :
    TensorAlgebra.toExterior (TensorAlgebra.ι R m) = ExteriorAlgebra.ι R m := by
  simp [toExterior]

end TensorAlgebra
