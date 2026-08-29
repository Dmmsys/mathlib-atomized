/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The `A`-module structure on `M ⊗[R] N`

When `M` is both an `R`-module and an `A`-module, and `Algebra R A`, then many of the morphisms
preserve the actions by `A`.

The `Module` instance itself is provided elsewhere as `TensorProduct.leftModule`. This file provides
more general versions of the definitions already in `LinearAlgebra/TensorProduct`.

In this file, we use the convention that `M`, `N`, `P`, `Q` are all `R`-modules, but only `M` and
`P` are simultaneously `A`-modules.

## Main definitions

* `TensorProduct.AlgebraTensorModule.curry`
* `TensorProduct.AlgebraTensorModule.uncurry`
* `TensorProduct.AlgebraTensorModule.lcurry`
* `TensorProduct.AlgebraTensorModule.lift`
* `TensorProduct.AlgebraTensorModule.lift.equiv`
* `TensorProduct.AlgebraTensorModule.mk`
* `TensorProduct.AlgebraTensorModule.map`
* `TensorProduct.AlgebraTensorModule.mapBilinear`
* `TensorProduct.AlgebraTensorModule.congr`
* `TensorProduct.AlgebraTensorModule.rid`
* `TensorProduct.AlgebraTensorModule.homTensorHomMap`
* `TensorProduct.AlgebraTensorModule.assoc`
* `TensorProduct.AlgebraTensorModule.leftComm`
* `TensorProduct.AlgebraTensorModule.rightComm`
* `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`
* `LinearMap.baseChange A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

## Implementation notes

We could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

@[expose] public section

namespace TensorProduct

namespace AlgebraTensorModule

universe uR uS uA uB uM uN uP uQ uP' uQ'
variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}

open LinearMap
open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M]
variable [IsScalarTower R A M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P] [Module A P]
variable [IsScalarTower R A P]
variable [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid P'] [Module R P'] [Module A P'] [Module B P']
variable [IsScalarTower R A P'] [IsScalarTower R B P'] [SMulCommClass A B P']
variable [AddCommMonoid Q'] [Module R Q']

/--
theorem `smul_eq_lsmul_rTensor` / 定理 `smul_eq_lsmul_rTensor`

English:
theorem smul_eq_lsmul_rTensor
  given: (a : A) (x : M otimes[R] N)
  statement: a • x = (lsmul R R M a).rTensor N x
  proof: rfl

中文:
定理 smul_eq_lsmul_rTensor
  条件: (a : A) (x : M otimes[R] N)
  结论: a • x = (lsmul R R M a).rTensor N x
  证明: rfl
-/
theorem smul_eq_lsmul_rTensor (a : A) (x : M otimes[R] N) : a • x = (lsmul R R M a).rTensor N x :=
  rfl

/-- Heterobasic version of `TensorProduct.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
nonrec def curry (f : M otimes[R] N ->ₗ[A] P) : M ->ₗ[A] N ->ₗ[R] P :=
  { curry (f.restrictScalars R) with
    toFun := curry (f.restrictScalars R)
    map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x otimesₜ y) }

/--
theorem `restrictScalars_curry` / 定理 `restrictScalars_curry`

English:
theorem restrictScalars_curry
  given: (f : M otimes[R] N ->ₗ[A] P)
  proof: rfl

中文:
定理 restrictScalars_curry
  条件: (f : M otimes[R] N ->ₗ[A] P)
  证明: rfl
-/
theorem restrictScalars_curry (f : M otimes[R] N ->ₗ[A] P) :
    restrictScalars R (curry f) = TensorProduct.curry (f.restrictScalars R) :=
  rfl

/-- Just as `TensorProduct.ext` is marked `ext` instead of `TensorProduct.ext'`, this is
a better `ext` lemma than `TensorProduct.AlgebraTensorModule.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext high]
nonrec theorem curry_injective : Function.Injective (curry : (M otimes N ->ₗ[A] P) -> M ->ₗ[A] N ->ₗ[R] P) :=
  fun _ _ h =>
LinearMap.restrictScalars_injective R
curry_injective (congr_arg (LinearMap.restrictScalars R) h :)

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {g h : M otimes[R] N ->ₗ[A] P} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y))
  statement: g = h
  proof: curry_injective LinearMap.ext₂ H

中文:
定理 ext
  条件: {g h : M otimes[R] N ->ₗ[A] P} (H : 对任意 x y, g (x otimesₜ y) = h (x otimesₜ y))
  结论: g = h
  证明: curry_injective LinearMap.ext₂ H

Depends on / 依赖: LinearMap, LinearMap.ext, curry_injective
-/
theorem ext {g h : M otimes[R] N ->ₗ[A] P} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h :=
curry_injective LinearMap.ext₂ H

/-- Heterobasic version of `TensorProduct.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
nonrec def lift (f : M ->ₗ[A] N ->ₗ[R] P) : M otimes[R] N ->ₗ[A] P :=
  { lift (f.restrictScalars R) with
    map_smul' := fun c =>
      show
        forall x : M otimes[R] N,
          (lift (f.restrictScalars R)).comp (lsmul R R _ c) x =
            (lsmul R R _ c).comp (lift (f.restrictScalars R)) x
        from
LinearMap.ext_iff.1
          TensorProduct.ext' fun x y => by
            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,
              coe_restrictScalars, f.map_smul, smul_apply] }

@[simp]
/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (f : M ->ₗ[A] N ->ₗ[R] P) (a : M otimes[R] N)
  proof: rfl

@[simp]

中文:
定理 lift_apply
  条件: (f : M ->ₗ[A] N ->ₗ[R] P) (a : M otimes[R] N)
  证明: rfl

@[simp]
-/
theorem lift_apply (f : M ->ₗ[A] N ->ₗ[R] P) (a : M otimes[R] N) :
    AlgebraTensorModule.lift f a = TensorProduct.lift (LinearMap.restrictScalars R f) a :=
  rfl

@[simp]
/--
theorem `lift_tmul` / 定理 `lift_tmul`

English:
theorem lift_tmul
  given: (f : M ->ₗ[A] N ->ₗ[R] P) (x : M) (y : N)
  statement: lift f (x otimesₜ y) = f x y
  proof: rfl

中文:
定理 lift_tmul
  条件: (f : M ->ₗ[A] N ->ₗ[R] P) (x : M) (y : N)
  结论: lift f (x otimesₜ y) = f x y
  证明: rfl
-/
theorem lift_tmul (f : M ->ₗ[A] N ->ₗ[R] P) (x : M) (y : N) : lift f (x otimesₜ y) = f x y :=
  rfl

variable (R A B M N P Q)

section
variable [Module B P] [IsScalarTower R B P] [SMulCommClass A B P]

/-- Heterobasic version of `TensorProduct.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: : (M ->ₗ[A] N ->ₗ[R] P) ->ₗ[B] M otimes[R] N ->ₗ[A] P where
  body: lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]

中文:
定义 uncurry
  签名: : (M ->ₗ[A] N ->ₗ[R] P) ->ₗ[B] M otimes[R] N ->ₗ[A] P where
  定义体: lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]
-/
def uncurry : (M ->ₗ[A] N ->ₗ[R] P) ->ₗ[B] M otimes[R] N ->ₗ[A] P where
  toFun := lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]

/-- Heterobasic version of `TensorProduct.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
/--
Definition of `lcurry` / `lcurry` 的定义

English:
definition lcurry
  signature: : (M otimes[R] N ->ₗ[A] P) ->ₗ[B] M ->ₗ[A] N ->ₗ[R] P where
  body: curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 lcurry
  签名: : (M otimes[R] N ->ₗ[A] P) ->ₗ[B] M ->ₗ[A] N ->ₗ[R] P where
  定义体: curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def lcurry : (M otimes[R] N ->ₗ[A] P) ->ₗ[B] M ->ₗ[A] N ->ₗ[R] P where
  toFun := curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Definition of `lift.equiv` / `lift.equiv` 的定义

English:
definition lift.equiv
  signature: : (M ->ₗ[A] N ->ₗ[R] P) ≃ₗ[B] M otimes[R] N ->ₗ[A] P
  body: LinearEquiv.ofLinearMap (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)

中文:
定义 lift.equiv
  签名: : (M ->ₗ[A] N ->ₗ[R] P) ≃ₗ[B] M otimes[R] N ->ₗ[A] P
  定义体: LinearEquiv.ofLinearMap (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)
-/
def lift.equiv : (M ->ₗ[A] N ->ₗ[R] P) ≃ₗ[B] M otimes[R] N ->ₗ[A] P :=
  LinearEquiv.ofLinearMap (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)

/-- Heterobasic version of `TensorProduct.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps! apply]
nonrec def mk (A M N : Type*) [Semiring A]
    [AddCommMonoid M] [Module R M] [Module A M] [SMulCommClass R A M]
    [AddCommMonoid N] [Module R N] : M ->ₗ[A] N ->ₗ[R] M otimes[R] N :=
  { mk R M N with map_smul' := fun _ _ => rfl }

variable {R A B M N P Q}

/--
lemma `mk_eq` / 引理 `mk_eq`

English:
lemma mk_eq
  statement: mk R R M N = TensorProduct.mk R M N
  proof: rfl

中文:
引理 mk_eq
  结论: mk R R M N = TensorProduct.mk R M N
  证明: rfl
-/
lemma mk_eq : mk R R M N = TensorProduct.mk R M N := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  body: lift
    { toFun := fun h => h ∘ₗ g,
      map_add' := fun h₁ h₂ => LinearMap.add_comp g h₂ h₁,
      map_smul' := fun c h => LinearMap.smul_comp c h g } ∘ₗ mk R A P Q ∘ₗ f

中文:
定义 map
  签名: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  定义体: lift
    { toFun := fun h => h ∘ₗ g,
      map_add' := fun h₁ h₂ => LinearMap.add_comp g h₂ h₁,
      map_smul' := fun c h => LinearMap.smul_comp c h g } ∘ₗ mk R A P Q ∘ₗ f

Depends on / 依赖: LinearMap, LinearMap.add_comp, LinearMap.smul_comp, add_comp, map_add, map_smul, smul_comp
-/
def map (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : M otimes[R] N ->ₗ[A] P otimes[R] Q :=
lift
    { toFun := fun h => h ∘ₗ g,
      map_add' := fun h₁ h₂ => LinearMap.add_comp g h₂ h₁,
      map_smul' := fun c h => LinearMap.smul_comp c h g } ∘ₗ mk R A P Q ∘ₗ f

/--
theorem `map_tmul` / 定理 `map_tmul`

English:
theorem map_tmul
  given: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) (m : M) (n : N)
  proof: rfl

@[simp]

中文:
定理 map_tmul
  条件: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) (m : M) (n : N)
  证明: rfl

@[simp]
-/
@[simp] theorem map_tmul (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) (m : M) (n : N) :
    map f g (m otimesₜ n) = f m otimesₜ g n :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (id : M ->ₗ[A] M) (id : N ->ₗ[R] N) = .id
  proof: ext fun _ _ => rfl

中文:
定理 map_id
  结论: map (id : M ->ₗ[A] M) (id : N ->ₗ[R] N) = .id
  证明: ext fun _ _ => rfl
-/
theorem map_id : map (id : M ->ₗ[A] M) (id : N ->ₗ[R] N) = .id :=
  ext fun _ _ => rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q)
  proof: ext fun _ _ => rfl

@[simp]

中文:
定理 map_comp
  条件: (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q)
  证明: ext fun _ _ => rfl

@[simp]
-/
theorem map_comp (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext fun _ _ => rfl

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: map (1 : M ->ₗ[A] M) (1 : N ->ₗ[R] N) = 1
  proof: map_id

中文:
定理 map_one
  结论: map (1 : M ->ₗ[A] M) (1 : N ->ₗ[R] N) = 1
  证明: map_id
-/
protected theorem map_one : map (1 : M ->ₗ[A] M) (1 : N ->ₗ[R] N) = 1 := map_id

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f₁ f₂ : M ->ₗ[A] M) (g₁ g₂ : N ->ₗ[R] N)
  proof: map_comp _ _ _ _

中文:
定理 map_mul
  条件: (f₁ f₂ : M ->ₗ[A] M) (g₁ g₂ : N ->ₗ[R] N)
  证明: map_comp _ _ _ _
-/
protected theorem map_mul (f₁ f₂ : M ->ₗ[A] M) (g₁ g₂ : N ->ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ := map_comp _ _ _ _

/--
theorem `map_add_left` / 定理 `map_add_left`

English:
theorem map_add_left
  given: (f₁ f₂ : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  proof: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, add_tmul]

中文:
定理 map_add_left
  条件: (f₁ f₂ : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  证明: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, add_tmul]

Depends on / 依赖: TensorProduct, TensorProduct.curry_apply, add_apply, add_tmul, curry_apply, map_tmul, restrictScalars_apply, simp_rw
-/
theorem map_add_left (f₁ f₂ : M ->ₗ[A] P) (g : N ->ₗ[R] Q) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, add_tmul]

/--
theorem `map_add_right` / 定理 `map_add_right`

English:
theorem map_add_right
  given: (f : M ->ₗ[A] P) (g₁ g₂ : N ->ₗ[R] Q)
  proof: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, tmul_add]

中文:
定理 map_add_right
  条件: (f : M ->ₗ[A] P) (g₁ g₂ : N ->ₗ[R] Q)
  证明: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, tmul_add]

Depends on / 依赖: TensorProduct, TensorProduct.curry_apply, add_apply, curry_apply, map_tmul, restrictScalars_apply, simp_rw, tmul_add
-/
theorem map_add_right (f : M ->ₗ[A] P) (g₁ g₂ : N ->ₗ[R] Q) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, tmul_add]

/--
theorem `map_smul_right` / 定理 `map_smul_right`

English:
theorem map_smul_right
  given: (r : R) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  statement: map f (r • g) = r • map f g
  proof: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul]

中文:
定理 map_smul_right
  条件: (r : R) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  结论: map f (r • g) = r • map f g
  证明: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul]

Depends on / 依赖: TensorProduct, TensorProduct.curry_apply, curry_apply, map_tmul, restrictScalars_apply, simp_rw, smul_apply, tmul_smul
-/
theorem map_smul_right (r : R) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map f (r • g) = r • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul]

/--
theorem `map_smul_left` / 定理 `map_smul_left`

English:
theorem map_smul_left
  given: (b : B) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  statement: map (b • f) g = b • map f g
  proof: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul']

中文:
定理 map_smul_left
  条件: (b : B) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  结论: map (b • f) g = b • map f g
  证明: by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul']

Depends on / 依赖: TensorProduct, TensorProduct.curry_apply, curry_apply, map_tmul, restrictScalars_apply, simp_rw, smul_apply, smul_tmul
-/
theorem map_smul_left (b : B) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map (b • f) g = b • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul']

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  statement: map f g = TensorProduct.map f g
  proof: rfl

中文:
定理 map_eq
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  结论: map f g = TensorProduct.map f g
  证明: rfl
-/
theorem map_eq (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : map f g = TensorProduct.map f g := rfl

variable (A M) in
/--
Definition of `lTensor` / `lTensor` 的定义

English:
definition lTensor
  signature: : (N ->ₗ[R] Q) ->ₗ[R] M otimes[R] N ->ₗ[A] M otimes[R] Q where
  body: map LinearMap.id f
  map_add' f₁ f₂ := map_add_right _ f₁ f₂
  map_smul' _ _ := map_smul_right _ _ _

@[simp]

中文:
定义 lTensor
  签名: : (N ->ₗ[R] Q) ->ₗ[R] M otimes[R] N ->ₗ[A] M otimes[R] Q where
  定义体: map LinearMap.id f
  map_add' f₁ f₂ := map_add_right _ f₁ f₂
  map_smul' _ _ := map_smul_right _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def lTensor : (N ->ₗ[R] Q) ->ₗ[R] M otimes[R] N ->ₗ[A] M otimes[R] Q where
  toFun f := map LinearMap.id f
  map_add' f₁ f₂ := map_add_right _ f₁ f₂
  map_smul' _ _ := map_smul_right _ _ _

@[simp]
/--
lemma `coe_lTensor` / 引理 `coe_lTensor`

English:
lemma coe_lTensor
  given: (f : N ->ₗ[R] Q)
  proof: rfl

@[simp]

中文:
引理 coe_lTensor
  条件: (f : N ->ₗ[R] Q)
  证明: rfl

@[simp]
-/
lemma coe_lTensor (f : N ->ₗ[R] Q) :
    (lTensor A M f : M otimes[R] N -> M otimes[R] Q) = f.lTensor M := rfl

@[simp]
/--
lemma `restrictScalars_lTensor` / 引理 `restrictScalars_lTensor`

English:
lemma restrictScalars_lTensor
  given: (f : N ->ₗ[R] Q)
  proof: rfl

中文:
引理 restrictScalars_lTensor
  条件: (f : N ->ₗ[R] Q)
  证明: rfl
-/
lemma restrictScalars_lTensor (f : N ->ₗ[R] Q) :
    (lTensor A M f).restrictScalars R = f.lTensor M := rfl

/--
lemma `lTensor_tmul` / 引理 `lTensor_tmul`

English:
lemma lTensor_tmul
  given: (f : N ->ₗ[R] Q) (m : M) (n : N)
  proof: rfl

中文:
引理 lTensor_tmul
  条件: (f : N ->ₗ[R] Q) (m : M) (n : N)
  证明: rfl
-/
@[simp] lemma lTensor_tmul (f : N ->ₗ[R] Q) (m : M) (n : N) :
    lTensor A M f (m otimesₜ[R] n) = m otimesₜ f n :=
  rfl

/--
lemma `lTensor_id` / 引理 `lTensor_id`

English:
lemma lTensor_id
  statement: lTensor A M (id : N ->ₗ[R] N) = .id
  proof: ext fun _ _ => rfl

中文:
引理 lTensor_id
  结论: lTensor A M (id : N ->ₗ[R] N) = .id
  证明: ext fun _ _ => rfl
-/
@[simp] lemma lTensor_id : lTensor A M (id : N ->ₗ[R] N) = .id :=
  ext fun _ _ => rfl

/--
lemma `lTensor_comp` / 引理 `lTensor_comp`

English:
lemma lTensor_comp
  given: (f₂ : Q ->ₗ[R] Q') (f₁ : N ->ₗ[R] Q)
  proof: ext fun _ _ => rfl

@[simp]

中文:
引理 lTensor_comp
  条件: (f₂ : Q ->ₗ[R] Q') (f₁ : N ->ₗ[R] Q)
  证明: ext fun _ _ => rfl

@[simp]
-/
lemma lTensor_comp (f₂ : Q ->ₗ[R] Q') (f₁ : N ->ₗ[R] Q) :
    lTensor A M (f₂.comp f₁) = (lTensor A M f₂).comp (lTensor A M f₁) :=
  ext fun _ _ => rfl

@[simp]
/--
lemma `lTensor_one` / 引理 `lTensor_one`

English:
lemma lTensor_one
  statement: lTensor A M (1 : N ->ₗ[R] N) = 1
  proof: map_id

中文:
引理 lTensor_one
  结论: lTensor A M (1 : N ->ₗ[R] N) = 1
  证明: map_id

Depends on / 依赖: map_id
-/
lemma lTensor_one : lTensor A M (1 : N ->ₗ[R] N) = 1 := map_id

/--
lemma `lTensor_mul` / 引理 `lTensor_mul`

English:
lemma lTensor_mul
  given: (f₁ f₂ : N ->ₗ[R] N)
  proof: lTensor_comp _ _

中文:
引理 lTensor_mul
  条件: (f₁ f₂ : N ->ₗ[R] N)
  证明: lTensor_comp _ _

Depends on / 依赖: lTensor_comp
-/
lemma lTensor_mul (f₁ f₂ : N ->ₗ[R] N) :
    lTensor A M (f₁ * f₂) = lTensor A M f₁ * lTensor A M f₂ := lTensor_comp _ _

variable (R N) in
/--
Definition of `rTensor` / `rTensor` 的定义

English:
definition rTensor
  signature: : (M ->ₗ[A] P) ->ₗ[R] M otimes[R] N ->ₗ[A] P otimes[R] N where
  body: map f LinearMap.id
  map_add' f₁ f₂ := map_add_left f₁ f₂ _
  map_smul' _ _ := map_smul_left _ _ _

@[simp]

中文:
定义 rTensor
  签名: : (M ->ₗ[A] P) ->ₗ[R] M otimes[R] N ->ₗ[A] P otimes[R] N where
  定义体: map f LinearMap.id
  map_add' f₁ f₂ := map_add_left f₁ f₂ _
  map_smul' _ _ := map_smul_left _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def rTensor : (M ->ₗ[A] P) ->ₗ[R] M otimes[R] N ->ₗ[A] P otimes[R] N where
  toFun f := map f LinearMap.id
  map_add' f₁ f₂ := map_add_left f₁ f₂ _
  map_smul' _ _ := map_smul_left _ _ _

@[simp]
/--
lemma `coe_rTensor` / 引理 `coe_rTensor`

English:
lemma coe_rTensor
  given: (f : M ->ₗ[A] P)
  proof: rfl

@[simp]

中文:
引理 coe_rTensor
  条件: (f : M ->ₗ[A] P)
  证明: rfl

@[simp]
-/
lemma coe_rTensor (f : M ->ₗ[A] P) :
    (rTensor R N f : M otimes[R] N -> P otimes[R] N) = f.rTensor N := rfl

@[simp]
/--
lemma `restrictScalars_rTensor` / 引理 `restrictScalars_rTensor`

English:
lemma restrictScalars_rTensor
  given: (f : M ->ₗ[A] P)
  proof: rfl

中文:
引理 restrictScalars_rTensor
  条件: (f : M ->ₗ[A] P)
  证明: rfl
-/
lemma restrictScalars_rTensor (f : M ->ₗ[A] P) :
    (rTensor R N f).restrictScalars R = f.rTensor N := rfl

/--
lemma `rTensor_tmul` / 引理 `rTensor_tmul`

English:
lemma rTensor_tmul
  given: (f : M ->ₗ[A] P) (m : M) (n : N)
  proof: rfl

中文:
引理 rTensor_tmul
  条件: (f : M ->ₗ[A] P) (m : M) (n : N)
  证明: rfl
-/
@[simp] lemma rTensor_tmul (f : M ->ₗ[A] P) (m : M) (n : N) :
    rTensor R N f (m otimesₜ[R] n) = f m otimesₜ n :=
  rfl

/--
lemma `rTensor_id` / 引理 `rTensor_id`

English:
lemma rTensor_id
  statement: rTensor R N (id : M ->ₗ[A] M) = .id
  proof: ext fun _ _ => rfl

中文:
引理 rTensor_id
  结论: rTensor R N (id : M ->ₗ[A] M) = .id
  证明: ext fun _ _ => rfl
-/
@[simp] lemma rTensor_id : rTensor R N (id : M ->ₗ[A] M) = .id :=
  ext fun _ _ => rfl

/--
lemma `rTensor_comp` / 引理 `rTensor_comp`

English:
lemma rTensor_comp
  given: (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P)
  proof: ext fun _ _ => rfl

@[simp]

中文:
引理 rTensor_comp
  条件: (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P)
  证明: ext fun _ _ => rfl

@[simp]
-/
lemma rTensor_comp (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P) :
    rTensor R N (f₂.comp f₁) = (rTensor R N f₂).comp (rTensor R N f₁) :=
  ext fun _ _ => rfl

@[simp]
/--
lemma `rTensor_one` / 引理 `rTensor_one`

English:
lemma rTensor_one
  statement: rTensor R N (1 : M ->ₗ[A] M) = 1
  proof: map_id

中文:
引理 rTensor_one
  结论: rTensor R N (1 : M ->ₗ[A] M) = 1
  证明: map_id

Depends on / 依赖: map_id
-/
lemma rTensor_one : rTensor R N (1 : M ->ₗ[A] M) = 1 := map_id

/--
lemma `rTensor_mul` / 引理 `rTensor_mul`

English:
lemma rTensor_mul
  given: (f₁ f₂ : M ->ₗ[A] M)
  proof: rTensor_comp _ _

中文:
引理 rTensor_mul
  条件: (f₁ f₂ : M ->ₗ[A] M)
  证明: rTensor_comp _ _

Depends on / 依赖: rTensor_comp
-/
lemma rTensor_mul (f₁ f₂ : M ->ₗ[A] M) :
    rTensor R M (f₁ * f₂) = rTensor R M f₁ * rTensor R M f₂ := rTensor_comp _ _

variable (R A B M N P Q)

/--
Definition of `mapBilinear` / `mapBilinear` 的定义

English:
definition mapBilinear
  signature: : (M ->ₗ[A] P) ->ₗ[B] (N ->ₗ[R] Q) ->ₗ[R] (M otimes[R] N ->ₗ[A] P otimes[R] Q)
  body: LinearMap.mk₂' _ _ map map_add_left map_smul_left map_add_right map_smul_right

中文:
定义 mapBilinear
  签名: : (M ->ₗ[A] P) ->ₗ[B] (N ->ₗ[R] Q) ->ₗ[R] (M otimes[R] N ->ₗ[A] P otimes[R] Q)
  定义体: LinearMap.mk₂' _ _ map map_add_left map_smul_left map_add_right map_smul_right

Depends on / 依赖: LinearMap, LinearMap.mk, map_add_left, map_add_right, map_smul_left, map_smul_right
-/
def mapBilinear : (M ->ₗ[A] P) ->ₗ[B] (N ->ₗ[R] Q) ->ₗ[R] (M otimes[R] N ->ₗ[A] P otimes[R] Q) :=
  LinearMap.mk₂' _ _ map map_add_left map_smul_left map_add_right map_smul_right

variable {R A B M N P Q}

@[simp]
/--
theorem `mapBilinear_apply` / 定理 `mapBilinear_apply`

English:
theorem mapBilinear_apply
  given: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  proof: rfl

中文:
定理 mapBilinear_apply
  条件: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  证明: rfl
-/
theorem mapBilinear_apply (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) :
    mapBilinear R A B M N P Q f g = map f g :=
  rfl

variable (R A B M N P Q)

/--
Definition of `homTensorHomMap` / `homTensorHomMap` 的定义

English:
definition homTensorHomMap
  signature: : ((M ->ₗ[A] P) otimes[R] (N ->ₗ[R] Q)) ->ₗ[B] (M otimes[R] N ->ₗ[A] P otimes[R] Q)
  body: lift mapBilinear R A B M N P Q

中文:
定义 homTensorHomMap
  签名: : ((M ->ₗ[A] P) otimes[R] (N ->ₗ[R] Q)) ->ₗ[B] (M otimes[R] N ->ₗ[A] P otimes[R] Q)
  定义体: lift mapBilinear R A B M N P Q

Depends on / 依赖: mapBilinear
-/
def homTensorHomMap : ((M ->ₗ[A] P) otimes[R] (N ->ₗ[R] Q)) ->ₗ[B] (M otimes[R] N ->ₗ[A] P otimes[R] Q) :=
lift mapBilinear R A B M N P Q

variable {R A B M N P Q}

/--
theorem `homTensorHomMap_apply` / 定理 `homTensorHomMap_apply`

English:
theorem homTensorHomMap_apply
  given: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  proof: rfl

中文:
定理 homTensorHomMap_apply
  条件: (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q)
  证明: rfl
-/
@[simp] theorem homTensorHomMap_apply (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) :
    homTensorHomMap R A B M N P Q (f otimesₜ g) = map f g :=
  rfl

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q)
  body: LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext fun _m _n => congr_arg₂ (· otimesₜ ·) (f.apply_symm_apply _) (g.apply_symm_apply _))
    (ext fun _m _n => congr_arg₂ (· otimesₜ ·) (f.symm_apply_apply _) (g.symm_apply_apply _))

@[simp]

中文:
定义 congr
  签名: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q)
  定义体: LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext fun _m _n => congr_arg₂ (· otimesₜ ·) (f.apply_symm_apply _) (g.apply_symm_apply _))
    (ext fun _m _n => congr_arg₂ (· otimesₜ ·) (f.symm_apply_apply _) (g.symm_apply_apply _))

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, apply_symm_apply, f.apply_symm_apply, f.symm, f.symm_apply_apply, g.apply_symm_apply, g.symm, g.symm_apply_apply, ofLinearMap, symm_apply_apply
-/
def congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M otimes[R] N) ≃ₗ[A] (P otimes[R] Q) :=
  LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext fun _m _n => congr_arg₂ (· otimesₜ ·) (f.apply_symm_apply _) (g.apply_symm_apply _))
    (ext fun _m _n => congr_arg₂ (· otimesₜ ·) (f.symm_apply_apply _) (g.symm_apply_apply _))

@[simp]
/--
theorem `congr_refl` / 定理 `congr_refl`

English:
theorem congr_refl
  statement: congr (.refl A M) (.refl R N) = .refl A _
  proof: LinearEquiv.toLinearMap_injective map_id

中文:
定理 congr_refl
  结论: congr (.refl A M) (.refl R N) = .refl A _
  证明: LinearEquiv.toLinearMap_injective map_id

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, map_id, toLinearMap_injective
-/
theorem congr_refl : congr (.refl A M) (.refl R N) = .refl A _ :=
LinearEquiv.toLinearMap_injective map_id

/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  given: (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q')
  proof: LinearEquiv.toLinearMap_injective map_comp _ _ _ _

中文:
定理 congr_trans
  条件: (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q')
  证明: LinearEquiv.toLinearMap_injective map_comp _ _ _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, map_comp, toLinearMap_injective
-/
theorem congr_trans (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q') :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
LinearEquiv.toLinearMap_injective map_comp _ _ _ _

/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q)
  statement: congr f.symm g.symm = (congr f g).symm
  proof: rfl

@[simp]

中文:
定理 congr_symm
  条件: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q)
  结论: congr f.symm g.symm = (congr f g).symm
  证明: rfl

@[simp]
-/
theorem congr_symm (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : congr f.symm g.symm = (congr f g).symm := rfl

@[simp]
/--
theorem `congr_one` / 定理 `congr_one`

English:
theorem congr_one
  statement: congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1
  proof: congr_refl

中文:
定理 congr_one
  结论: congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1
  证明: congr_refl

Depends on / 依赖: congr_refl
-/
theorem congr_one : congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1 := congr_refl

/--
theorem `congr_mul` / 定理 `congr_mul`

English:
theorem congr_mul
  given: (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N)
  proof: congr_trans _ _ _ _

中文:
定理 congr_mul
  条件: (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N)
  证明: congr_trans _ _ _ _

Depends on / 依赖: congr_trans
-/
theorem congr_mul (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N) :
    congr (f₁ * f₂) (g₁ * g₂) = congr f₁ g₁ * congr f₂ g₂ := congr_trans _ _ _ _

/--
theorem `congr_tmul` / 定理 `congr_tmul`

English:
theorem congr_tmul
  given: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N)
  proof: rfl

中文:
定理 congr_tmul
  条件: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N)
  证明: rfl
-/
@[simp] theorem congr_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m otimesₜ n) = f m otimesₜ g n :=
  rfl

/--
theorem `congr_symm_tmul` / 定理 `congr_symm_tmul`

English:
theorem congr_symm_tmul
  given: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q)
  proof: rfl

中文:
定理 congr_symm_tmul
  条件: (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q)
  证明: rfl

Depends on / 依赖: Structure, isExpansionOn_reduct
-/
@[simp] theorem congr_symm_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p otimesₜ q) = f.symm p otimesₜ g.symm q :=
  rfl

/--
theorem `congr_eq` / 定理 `congr_eq`

English:
theorem congr_eq
  given: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  proof: rfl

中文:
定理 congr_eq
  条件: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  证明: rfl
-/
theorem congr_eq (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    congr f g = TensorProduct.congr f g := rfl

variable (R A M)

/--
Definition of `rid` / `rid` 的定义

English:
definition rid
  signature: : M otimes[R] R ≃ₗ[A] M
  body: LinearEquiv.ofLinearMap
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)

中文:
定义 rid
  签名: : M otimes[R] R ≃ₗ[A] M
  定义体: LinearEquiv.ofLinearMap
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)
-/
protected def rid : M otimes[R] R ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)

/--
theorem `rid_eq_rid` / 定理 `rid_eq_rid`

English:
theorem rid_eq_rid
  statement: AlgebraTensorModule.rid R R M = TensorProduct.rid R M
  proof: rfl

中文:
定理 rid_eq_rid
  结论: AlgebraTensorModule.rid R R M = TensorProduct.rid R M
  证明: rfl
-/
theorem rid_eq_rid : AlgebraTensorModule.rid R R M = TensorProduct.rid R M := rfl

variable {R M} in
@[simp]
/--
theorem `rid_tmul` / 定理 `rid_tmul`

English:
theorem rid_tmul
  given: (r : R) (m : M)
  statement: AlgebraTensorModule.rid R A M (m otimesₜ r) = r • m
  proof: rfl

中文:
定理 rid_tmul
  条件: (r : R) (m : M)
  结论: AlgebraTensorModule.rid R A M (m otimesₜ r) = r • m
  证明: rfl
-/
theorem rid_tmul (r : R) (m : M) : AlgebraTensorModule.rid R A M (m otimesₜ r) = r • m := rfl

variable {M} in
@[simp]
/--
theorem `rid_symm_apply` / 定理 `rid_symm_apply`

English:
theorem rid_symm_apply
  given: (m : M)
  statement: (AlgebraTensorModule.rid R A M).symm m = m otimesₜ 1
  proof: rfl

中文:
定理 rid_symm_apply
  条件: (m : M)
  结论: (AlgebraTensorModule.rid R A M).symm m = m otimesₜ 1
  证明: rfl
-/
theorem rid_symm_apply (m : M) : (AlgebraTensorModule.rid R A M).symm m = m otimesₜ 1 := rfl

end

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module A P]
variable [AddCommMonoid P'] [Module A P']
variable [AddCommMonoid Q] [Module R Q]
variable (R A B M N P P' Q)

attribute [local ext high] TensorProduct.ext

section assoc
variable [Module R P] [IsScalarTower R A P]
variable [Algebra A B] [IsScalarTower A B M]

/--
Definition of `assoc` / `assoc` 的定义

English:
definition assoc
  signature: : (M otimes[A] P) otimes[R] Q ≃ₗ[B] M otimes[A] (P otimes[R] Q)
  body: LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P otimes[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)

中文:
定义 assoc
  签名: : (M otimes[A] P) otimes[R] Q ≃ₗ[B] M otimes[A] (P otimes[R] Q)
  定义体: LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P otimes[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, lcurry, ofLinearMap, otimes, uncurry
-/
def assoc : (M otimes[A] P) otimes[R] Q ≃ₗ[B] M otimes[A] (P otimes[R] Q) :=
  LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P otimes[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)

variable {M P N Q}

@[simp]
/--
theorem `assoc_tmul` / 定理 `assoc_tmul`

English:
theorem assoc_tmul
  given: (m : M) (p : P) (q : Q)
  proof: rfl

@[simp]

中文:
定理 assoc_tmul
  条件: (m : M) (p : P) (q : Q)
  证明: rfl

@[simp]
-/
theorem assoc_tmul (m : M) (p : P) (q : Q) :
    assoc R A B M P Q ((m otimesₜ p) otimesₜ q) = m otimesₜ (p otimesₜ q) :=
  rfl

@[simp]
/--
theorem `assoc_symm_tmul` / 定理 `assoc_symm_tmul`

English:
theorem assoc_symm_tmul
  given: (m : M) (p : P) (q : Q)
  proof: rfl

中文:
定理 assoc_symm_tmul
  条件: (m : M) (p : P) (q : Q)
  证明: rfl
-/
theorem assoc_symm_tmul (m : M) (p : P) (q : Q) :
    (assoc R A B M P Q).symm (m otimesₜ (p otimesₜ q)) = (m otimesₜ p) otimesₜ q :=
  rfl

/--
theorem `assoc_eq` / 定理 `assoc_eq`

English:
theorem assoc_eq
  statement: assoc R R R M P Q = TensorProduct.assoc R M P Q
  proof: rfl

中文:
定理 assoc_eq
  结论: assoc R R R M P Q = TensorProduct.assoc R M P Q
  证明: rfl
-/
theorem assoc_eq : assoc R R R M P Q = TensorProduct.assoc R M P Q := rfl

/--
theorem `rTensor_tensor` / 定理 `rTensor_tensor`

English:
theorem rTensor_tensor
  given: [Module R P'] [IsScalarTower R A P'] (g : P ->ₗ[A] P')
  proof: TensorProduct.ext LinearMap.ext fun _ => ext fun _ _ => rfl

中文:
定理 rTensor_tensor
  条件: [Module R P'] [IsScalarTower R A P'] (g : P ->ₗ[A] P')
  证明: TensorProduct.ext LinearMap.ext fun _ => ext fun _ _ => rfl

Depends on / 依赖: LinearMap, LinearMap.ext, TensorProduct, TensorProduct.ext
-/
theorem rTensor_tensor [Module R P'] [IsScalarTower R A P'] (g : P ->ₗ[A] P') :
    g.rTensor (M otimes[R] N) =
      assoc R A A P' M N ∘ₗ map (g.rTensor M) id ∘ₗ (assoc R A A P M N).symm.toLinearMap :=
TensorProduct.ext LinearMap.ext fun _ => ext fun _ _ => rfl

end assoc

section cancelBaseChange
variable [Algebra A B] [IsScalarTower A B M]

/--
Definition of `cancelBaseChange` / `cancelBaseChange` 的定义

English:
definition cancelBaseChange
  signature: : M otimes[A] (A otimes[R] N) ≃ₗ[B] M otimes[R] N
  body: letI g : (M otimes[A] A) otimes[R] N ≃ₗ[B] M otimes[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g

中文:
定义 cancelBaseChange
  签名: : M otimes[A] (A otimes[R] N) ≃ₗ[B] M otimes[R] N
  定义体: letI g : (M otimes[A] A) otimes[R] N ≃ₗ[B] M otimes[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rid, otimes
-/
def cancelBaseChange : M otimes[A] (A otimes[R] N) ≃ₗ[B] M otimes[R] N :=
  letI g : (M otimes[A] A) otimes[R] N ≃ₗ[B] M otimes[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g

/--
Definition of `distribBaseChange` / `distribBaseChange` 的定义

English:
definition distribBaseChange
  signature: : A otimes[R] (N otimes[R] Q) ≃ₗ[A] (A otimes[R] N) otimes[A] (A otimes[R] Q)
  body: (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm

中文:
定义 distribBaseChange
  签名: : A otimes[R] (N otimes[R] Q) ≃ₗ[A] (A otimes[R] N) otimes[A] (A otimes[R] Q)
  定义体: (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm

Depends on / 依赖: cancelBaseChange
-/
def distribBaseChange : A otimes[R] (N otimes[R] Q) ≃ₗ[A] (A otimes[R] N) otimes[A] (A otimes[R] Q) :=
  (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm

variable {M P N Q}

@[simp]
/--
theorem `cancelBaseChange_tmul` / 定理 `cancelBaseChange_tmul`

English:
theorem cancelBaseChange_tmul
  given: (m : M) (n : N) (a : A)
  proof: rfl

@[simp]

中文:
定理 cancelBaseChange_tmul
  条件: (m : M) (n : N) (a : A)
  证明: rfl

@[simp]
-/
theorem cancelBaseChange_tmul (m : M) (n : N) (a : A) :
    cancelBaseChange R A B M N (m otimesₜ (a otimesₜ n)) = (a • m) otimesₜ n :=
  rfl

@[simp]
/--
theorem `cancelBaseChange_symm_tmul` / 定理 `cancelBaseChange_symm_tmul`

English:
theorem cancelBaseChange_symm_tmul
  given: (m : M) (n : N)
  proof: rfl

中文:
定理 cancelBaseChange_symm_tmul
  条件: (m : M) (n : N)
  证明: rfl
-/
theorem cancelBaseChange_symm_tmul (m : M) (n : N) :
    (cancelBaseChange R A B M N).symm (m otimesₜ n) = m otimesₜ (1 otimesₜ n) :=
  rfl

/--
theorem `lTensor_comp_cancelBaseChange` / 定理 `lTensor_comp_cancelBaseChange`

English:
theorem lTensor_comp_cancelBaseChange
  given: (f : N ->ₗ[R] Q)
  proof: by
  ext; simp

@[simp]

中文:
定理 lTensor_comp_cancelBaseChange
  条件: (f : N ->ₗ[R] Q)
  证明: by
  ext; simp

@[simp]
-/
theorem lTensor_comp_cancelBaseChange (f : N ->ₗ[R] Q) :
    lTensor _ _ f ∘ₗ cancelBaseChange R A B M N =
      (cancelBaseChange R A B M Q).toLinearMap ∘ₗ lTensor _ _ (lTensor _ _ f) := by
  ext; simp

@[simp]
/--
theorem `distribBaseChange_tmul` / 定理 `distribBaseChange_tmul`

English:
theorem distribBaseChange_tmul
  given: (n : N) (q : Q) (a : A)
  proof: rfl

@[simp]

中文:
定理 distribBaseChange_tmul
  条件: (n : N) (q : Q) (a : A)
  证明: rfl

@[simp]
-/
theorem distribBaseChange_tmul (n : N) (q : Q) (a : A) :
    distribBaseChange R A N Q (a otimesₜ (n otimesₜ q)) = (a otimesₜ n) otimesₜ (1 otimesₜ q) :=
  rfl

@[simp]
/--
theorem `distribBaseChange_symm_tmul` / 定理 `distribBaseChange_symm_tmul`

English:
theorem distribBaseChange_symm_tmul
  proof: by
  apply ((distribBaseChange R A N Q).eq_symm_apply.mpr ?_).symm
  rw [tmul_eq_smul_one_tmul b]; rw [← smul_tmul]; rw [smul_tmul']; rw [mul_comm]
  simp

中文:
定理 distribBaseChange_symm_tmul
  证明: by
  apply ((distribBaseChange R A N Q).eq_symm_apply.mpr ?_).symm
  rw [tmul_eq_smul_one_tmul b]; rw [← smul_tmul]; rw [smul_tmul']; rw [mul_comm]
  simp

Depends on / 依赖: distribBaseChange, eq_symm_apply, eq_symm_apply.mpr, mul_comm, smul_tmul, tmul_eq_smul_one_tmul
-/
theorem distribBaseChange_symm_tmul
    (n : N) (q : Q) (a b : A) :
    (distribBaseChange R A N Q).symm ((a otimesₜ n) otimesₜ (b otimesₜ q)) = (a * b) otimesₜ (n otimesₜ q) := by
  apply ((distribBaseChange R A N Q).eq_symm_apply.mpr ?_).symm
  rw [tmul_eq_smul_one_tmul b]; rw [← smul_tmul]; rw [smul_tmul']; rw [mul_comm]
  simp

/--
lemma `cancelBaseChange_self_eq_lid` / 引理 `cancelBaseChange_self_eq_lid`

English:
lemma cancelBaseChange_self_eq_lid
  proof: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [cancelBaseChange_tmul, lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
    | add x 

中文:
引理 cancelBaseChange_self_eq_lid
  证明: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [cancelBaseChange_tmul, lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
    | add x 

Depends on / 依赖: TensorProduct, TensorProduct.induction_on, cancelBaseChange_tmul, induction_on, lid_tmul, map_add, map_zero, mul_comm, smul_eq_mul, smul_tmul, tmul_add
-/
lemma cancelBaseChange_self_eq_lid :
    cancelBaseChange R A A A N = TensorProduct.lid A (A otimes[R] N) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [cancelBaseChange_tmul, lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
    | add x y hx hy =>
      simp only [tmul_add, map_add, lid_tmul, hx, hy]
  | add x y hx hy => simp [hx, hy]

end cancelBaseChange

section leftComm
variable [Module R P] [IsScalarTower R A P]

/--
Definition of `leftComm` / `leftComm` 的定义

English:
definition leftComm
  signature: : M otimes[A] (P otimes[R] Q) ≃ₗ[A] P otimes[A] (M otimes[R] Q)
  body: let e₁ := (assoc R A A M P Q).symm
  let e₂ := congr (TensorProduct.comm A M P) (1 : Q ≃ₗ[R] Q)
  let e₃ := assoc R A A P M Q
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

中文:
定义 leftComm
  签名: : M otimes[A] (P otimes[R] Q) ≃ₗ[A] P otimes[A] (M otimes[R] Q)
  定义体: let e₁ := (assoc R A A M P Q).symm
  let e₂ := congr (TensorProduct.comm A M P) (1 : Q ≃ₗ[R] Q)
  let e₃ := assoc R A A P M Q
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

Depends on / 依赖: TensorProduct, TensorProduct.comm
-/
def leftComm : M otimes[A] (P otimes[R] Q) ≃ₗ[A] P otimes[A] (M otimes[R] Q) :=
  let e₁ := (assoc R A A M P Q).symm
  let e₂ := congr (TensorProduct.comm A M P) (1 : Q ≃ₗ[R] Q)
  let e₃ := assoc R A A P M Q
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

variable {M N P Q}

@[simp]
/--
theorem `leftComm_tmul` / 定理 `leftComm_tmul`

English:
theorem leftComm_tmul
  given: (m : M) (p : P) (q : Q)
  proof: rfl

@[simp]

中文:
定理 leftComm_tmul
  条件: (m : M) (p : P) (q : Q)
  证明: rfl

@[simp]
-/
theorem leftComm_tmul (m : M) (p : P) (q : Q) :
    leftComm R A M P Q (m otimesₜ (p otimesₜ q)) = p otimesₜ (m otimesₜ q) :=
  rfl

@[simp]
/--
theorem `leftComm_symm_tmul` / 定理 `leftComm_symm_tmul`

English:
theorem leftComm_symm_tmul
  given: (m : M) (p : P) (q : Q)
  proof: rfl

中文:
定理 leftComm_symm_tmul
  条件: (m : M) (p : P) (q : Q)
  证明: rfl
-/
theorem leftComm_symm_tmul (m : M) (p : P) (q : Q) :
    (leftComm R A M P Q).symm (p otimesₜ (m otimesₜ q)) = m otimesₜ (p otimesₜ q) :=
  rfl

/--
theorem `leftComm_eq` / 定理 `leftComm_eq`

English:
theorem leftComm_eq
  statement: leftComm R R M P Q = TensorProduct.leftComm R M P Q
  proof: rfl

中文:
定理 leftComm_eq
  结论: leftComm R R M P Q = TensorProduct.leftComm R M P Q
  证明: rfl
-/
theorem leftComm_eq : leftComm R R M P Q = TensorProduct.leftComm R M P Q := rfl

end leftComm

section rightComm

variable [CommSemiring S] [Module S M] [Module S P] [Algebra S B]
  [IsScalarTower S B M] [SMulCommClass R S M] [SMulCommClass S R M]

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/--
Definition of `rightComm` / `rightComm` 的定义

English:
definition rightComm
  signature: : (M otimes[S] P) otimes[R] Q ≃ₗ[B] (M otimes[R] Q) otimes[S] P
  body: LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (by ext; sim

中文:
定义 rightComm
  签名: : (M otimes[S] P) otimes[R] Q ≃ₗ[B] (M otimes[R] Q) otimes[S] P
  定义体: LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (by ext; sim

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.mk, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.lflip.toLinearMap, ofLinearMap, toLinearMap
-/
def rightComm : (M otimes[S] P) otimes[R] Q ≃ₗ[B] (M otimes[R] Q) otimes[S] P :=
  LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (by ext; simp) (by ext; simp)

variable {M N P Q}

@[simp]
/--
theorem `rightComm_tmul` / 定理 `rightComm_tmul`

English:
theorem rightComm_tmul
  given: (m : M) (p : P) (q : Q)
  proof: rfl

@[simp]

中文:
定理 rightComm_tmul
  条件: (m : M) (p : P) (q : Q)
  证明: rfl

@[simp]
-/
theorem rightComm_tmul (m : M) (p : P) (q : Q) :
    rightComm R S B M P Q ((m otimesₜ p) otimesₜ q) = (m otimesₜ q) otimesₜ p :=
  rfl

@[simp]
/--
theorem `rightComm_symm` / 定理 `rightComm_symm`

English:
theorem rightComm_symm
  proof: rfl

中文:
定理 rightComm_symm
  证明: rfl
-/
theorem rightComm_symm :
    (rightComm R S B M P Q).symm = rightComm S R B M Q P :=
  rfl

/--
theorem `rightComm_symm_tmul` / 定理 `rightComm_symm_tmul`

English:
theorem rightComm_symm_tmul
  given: (m : M) (p : P) (q : Q)
  proof: rfl

中文:
定理 rightComm_symm_tmul
  条件: (m : M) (p : P) (q : Q)
  证明: rfl
-/
theorem rightComm_symm_tmul (m : M) (p : P) (q : Q) :
    (rightComm R S B M P Q).symm ((m otimesₜ q) otimesₜ p) = (m otimesₜ p) otimesₜ q :=
  rfl

/--
theorem `rightComm_eq` / 定理 `rightComm_eq`

English:
theorem rightComm_eq
  given: [Module R P]
  statement: rightComm R R R M P Q = TensorProduct.rightComm R M P Q
  proof: rfl

中文:
定理 rightComm_eq
  条件: [Module R P]
  结论: rightComm R R R M P Q = TensorProduct.rightComm R M P Q
  证明: rfl
-/
theorem rightComm_eq [Module R P] : rightComm R R R M P Q = TensorProduct.rightComm R M P Q := rfl

end rightComm

section tensorTensorTensorComm
variable [Module R P] [IsScalarTower R A P]

variable [Algebra A B] [IsScalarTower A B M]
variable [CommSemiring S] [Algebra R S] [Algebra S B] [Module S M] [Module S N]
variable [IsScalarTower R S M] [SMulCommClass A S M] [SMulCommClass S A M]
  [IsScalarTower S B M] [IsScalarTower R S N]

variable (S)

/--
Definition of `tensorTensorTensorComm` / `tensorTensorTensorComm` 的定义

English:
definition tensorTensorTensorComm
  signature: :
  body: (assoc R A B (M otimes[S] N) P Q).symm
    ≪≫ₗ congr (rightComm A S B M N P) (.refl R Q)
    ≪≫ₗ assoc R _ _ (M otimes[A] P) N Q

中文:
定义 tensorTensorTensorComm
  签名: :
  定义体: (assoc R A B (M otimes[S] N) P Q).symm
    ≪≫ₗ congr (rightComm A S B M N P) (.refl R Q)
    ≪≫ₗ assoc R _ _ (M otimes[A] P) N Q

Depends on / 依赖: otimes, rightComm
-/
def tensorTensorTensorComm :
    (M otimes[S] N) otimes[A] (P otimes[R] Q) ≃ₗ[B] (M otimes[A] P) otimes[S] (N otimes[R] Q) :=
  (assoc R A B (M otimes[S] N) P Q).symm
    ≪≫ₗ congr (rightComm A S B M N P) (.refl R Q)
    ≪≫ₗ assoc R _ _ (M otimes[A] P) N Q

variable {M N P Q}

@[simp]
/--
theorem `tensorTensorTensorComm_tmul` / 定理 `tensorTensorTensorComm_tmul`

English:
theorem tensorTensorTensorComm_tmul
  given: (m : M) (n : N) (p : P) (q : Q)
  proof: rfl

@[simp]

中文:
定理 tensorTensorTensorComm_tmul
  条件: (m : M) (n : N) (p : P) (q : Q)
  证明: rfl

@[simp]
-/
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R S A B M N P Q ((m otimesₜ n) otimesₜ (p otimesₜ q)) = (m otimesₜ p) otimesₜ (n otimesₜ q) :=
  rfl

@[simp]
/--
theorem `tensorTensorTensorComm_symm` / 定理 `tensorTensorTensorComm_symm`

English:
theorem tensorTensorTensorComm_symm
  proof: rfl

中文:
定理 tensorTensorTensorComm_symm
  证明: rfl
-/
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R S A B M N P Q).symm = tensorTensorTensorComm R A S B M P N Q := rfl

/--
theorem `tensorTensorTensorComm_symm_tmul` / 定理 `tensorTensorTensorComm_symm_tmul`

English:
theorem tensorTensorTensorComm_symm_tmul
  given: (m : M) (n : N) (p : P) (q : Q)
  proof: rfl

中文:
定理 tensorTensorTensorComm_symm_tmul
  条件: (m : M) (n : N) (p : P) (q : Q)
  证明: rfl
-/
theorem tensorTensorTensorComm_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorComm R S A B M N P Q).symm ((m otimesₜ p) otimesₜ (n otimesₜ q)) = (m otimesₜ n) otimesₜ (p otimesₜ q) :=
  rfl

/--
theorem `tensorTensorTensorComm_eq` / 定理 `tensorTensorTensorComm_eq`

English:
theorem tensorTensorTensorComm_eq
  proof: rfl

中文:
定理 tensorTensorTensorComm_eq
  证明: rfl
-/
theorem tensorTensorTensorComm_eq :
    tensorTensorTensorComm R R R R M N P Q = TensorProduct.tensorTensorTensorComm R M N P Q := rfl

end tensorTensorTensorComm

section

universe u₁ u₂ u₃ u₄

attribute [local instance] ULift.algebra' in
/--
Definition of `uliftEquiv` / `uliftEquiv` 的定义

English:
definition uliftEquiv
  signature: : ULift.{u₁} (M otimes[R] N) ≃ₗ[A] ULift.{u₂} M otimes[ULift.{u₃} R] ULift.{u₄} N
  body: ULift.moduleEquiv ≪≫ₗ
    AlgebraTensorModule.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    (equivOfCompatibleSMul _ _ _ _ _)

中文:
定义 uliftEquiv
  签名: : ULift.{u₁} (M otimes[R] N) ≃ₗ[A] ULift.{u₂} M otimes[ULift.{u₃} R] ULift.{u₄} N
  定义体: ULift.moduleEquiv ≪≫ₗ
    AlgebraTensorModule.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    (equivOfCompatibleSMul _ _ _ _ _)

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr, ULift.moduleEquiv, ULift.moduleEquiv.symm, equivOfCompatibleSMul, moduleEquiv
-/
def uliftEquiv : ULift.{u₁} (M otimes[R] N) ≃ₗ[A] ULift.{u₂} M otimes[ULift.{u₃} R] ULift.{u₄} N :=
  ULift.moduleEquiv ≪≫ₗ
    AlgebraTensorModule.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    (equivOfCompatibleSMul _ _ _ _ _)

variable {M N}

@[simp]
/--
lemma `down_uliftEquiv_symm_tmul` / 引理 `down_uliftEquiv_symm_tmul`

English:
lemma down_uliftEquiv_symm_tmul
  given: (m : ULift M) (n : ULift N)
  proof: rfl

@[simp]

中文:
引理 down_uliftEquiv_symm_tmul
  条件: (m : ULift M) (n : ULift N)
  证明: rfl

@[simp]
-/
lemma down_uliftEquiv_symm_tmul (m : ULift M) (n : ULift N) :
    ((uliftEquiv R A M N).symm (m otimesₜ n)).down = m.down otimesₜ n.down :=
  rfl

@[simp]
/--
lemma `uliftEquiv_tmul` / 引理 `uliftEquiv_tmul`

English:
lemma uliftEquiv_tmul
  given: (m : M) (n : N)
  statement: uliftEquiv R A M N ⟨m otimesₜ n⟩ = ⟨m⟩ otimesₜ ⟨n⟩
  proof: rfl

中文:
引理 uliftEquiv_tmul
  条件: (m : M) (n : N)
  结论: uliftEquiv R A M N ⟨m otimesₜ n⟩ = ⟨m⟩ otimesₜ ⟨n⟩
  证明: rfl

Depends on / 依赖: constantsOn, constantsOn.structure, fast_instance, structure
-/
lemma uliftEquiv_tmul (m : M) (n : N) : uliftEquiv R A M N ⟨m otimesₜ n⟩ = ⟨m⟩ otimesₜ ⟨n⟩ :=
  rfl

end

end CommSemiring

end AlgebraTensorModule

end TensorProduct

namespace LinearMap

open TensorProduct

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/


section Semiring

variable {R A B M N P : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]
variable (r : R) (f g : M ->ₗ[R] N)

variable (A) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (f : M ->ₗ[R] N)
  body: AlgebraTensorModule.map (LinearMap.id : A ->ₗ[A] A) f

@[simp]

中文:
定义 baseChange
  签名: (f : M ->ₗ[R] N)
  定义体: AlgebraTensorModule.map (LinearMap.id : A ->ₗ[A] A) f

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, LinearMap, LinearMap.id
-/
def baseChange (f : M ->ₗ[R] N) : A otimes[R] M ->ₗ[A] A otimes[R] N :=
  AlgebraTensorModule.map (LinearMap.id : A ->ₗ[A] A) f

@[simp]
/--
theorem `baseChange_tmul` / 定理 `baseChange_tmul`

English:
theorem baseChange_tmul
  given: (a : A) (x : M)
  statement: f.baseChange A (a otimesₜ x) = a otimesₜ f x
  proof: rfl

中文:
定理 baseChange_tmul
  条件: (a : A) (x : M)
  结论: f.baseChange A (a otimesₜ x) = a otimesₜ f x
  证明: rfl
-/
theorem baseChange_tmul (a : A) (x : M) : f.baseChange A (a otimesₜ x) = a otimesₜ f x :=
  rfl

/--
theorem `baseChange_eq_ltensor` / 定理 `baseChange_eq_ltensor`

English:
theorem baseChange_eq_ltensor
  statement: (f.baseChange A : A otimes M -> A otimes N) = f.lTensor A
  proof: rfl

@[simp]

中文:
定理 baseChange_eq_ltensor
  结论: (f.baseChange A : A otimes M -> A otimes N) = f.lTensor A
  证明: rfl

@[simp]
-/
theorem baseChange_eq_ltensor : (f.baseChange A : A otimes M -> A otimes N) = f.lTensor A :=
  rfl

@[simp]
/--
theorem `baseChange_add` / 定理 `baseChange_add`

English:
theorem baseChange_add
  statement: (f + g).baseChange A = f.baseChange A + g.baseChange A
  proof: by
  ext
  simp [baseChange_eq_ltensor, -baseChange_tmul]

@[simp]

中文:
定理 baseChange_add
  结论: (f + g).baseChange A = f.baseChange A + g.baseChange A
  证明: by
  ext
  simp [baseChange_eq_ltensor, -baseChange_tmul]

@[simp]

Depends on / 依赖: baseChange_eq_ltensor, baseChange_tmul
-/
theorem baseChange_add : (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  ext
  simp [baseChange_eq_ltensor, -baseChange_tmul]

@[simp]
/--
theorem `baseChange_zero` / 定理 `baseChange_zero`

English:
theorem baseChange_zero
  statement: baseChange A (0 : M ->ₗ[R] N) = 0
  proof: by
  ext
  simp

@[simp]

中文:
定理 baseChange_zero
  结论: baseChange A (0 : M ->ₗ[R] N) = 0
  证明: by
  ext
  simp

@[simp]
-/
theorem baseChange_zero : baseChange A (0 : M ->ₗ[R] N) = 0 := by
  ext
  simp

@[simp]
/--
theorem `baseChange_smul` / 定理 `baseChange_smul`

English:
theorem baseChange_smul
  statement: (r • f).baseChange A = r • f.baseChange A
  proof: by
  ext
  simp

@[simp]

中文:
定理 baseChange_smul
  结论: (r • f).baseChange A = r • f.baseChange A
  证明: by
  ext
  simp

@[simp]
-/
theorem baseChange_smul : (r • f).baseChange A = r • f.baseChange A := by
  ext
  simp

@[simp]
/--
lemma `baseChange_id` / 引理 `baseChange_id`

English:
lemma baseChange_id
  statement: (.id : M ->ₗ[R] M).baseChange A = .id
  proof: by
  ext; simp

中文:
引理 baseChange_id
  结论: (.id : M ->ₗ[R] M).baseChange A = .id
  证明: by
  ext; simp
-/
lemma baseChange_id : (.id : M ->ₗ[R] M).baseChange A = .id := by
  ext; simp

/--
lemma `baseChange_comp` / 引理 `baseChange_comp`

English:
lemma baseChange_comp
  given: (g : N ->ₗ[R] P)
  proof: by
  ext; simp

中文:
引理 baseChange_comp
  条件: (g : N ->ₗ[R] P)
  证明: by
  ext; simp
-/
lemma baseChange_comp (g : N ->ₗ[R] P) :
    (g ∘ₗ f).baseChange A = g.baseChange A ∘ₗ f.baseChange A := by
  ext; simp

open AlgebraTensorModule in
/--
lemma `baseChange_baseChange` / 引理 `baseChange_baseChange`

English:
lemma baseChange_baseChange
  statement: {A B : Type*} [CommSemiring A] [Algebra R A]
  proof: by
  ext; simp

中文:
引理 baseChange_baseChange
  结论: {A B : 类型} [CommSemiring A] [Algebra R A]
  证明: by
  ext; simp
-/
lemma baseChange_baseChange {A B : Type*} [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (f : M ->ₗ[R] N) :
    ((f.baseChange A).baseChange B) =
    (cancelBaseChange R A B B N).symm ∘ₗ
      (f.baseChange B) ∘ₗ (cancelBaseChange R A B B M) := by
  ext; simp

variable (R M) in
@[simp]
/--
lemma `baseChange_one` / 引理 `baseChange_one`

English:
lemma baseChange_one
  statement: (1 : Module.End R M).baseChange A = 1
  proof: baseChange_id

中文:
引理 baseChange_one
  结论: (1 : Module.End R M).baseChange A = 1
  证明: baseChange_id

Depends on / 依赖: baseChange_id
-/
lemma baseChange_one : (1 : Module.End R M).baseChange A = 1 := baseChange_id

/--
lemma `baseChange_mul` / 引理 `baseChange_mul`

English:
lemma baseChange_mul
  given: (f g : Module.End R M)
  proof: by
  ext; simp

中文:
引理 baseChange_mul
  条件: (f g : Module.End R M)
  证明: by
  ext; simp
-/
lemma baseChange_mul (f g : Module.End R M) :
    (f * g).baseChange A = f.baseChange A * g.baseChange A := by
  ext; simp

variable (R A M N)

/-- `baseChange` as a linear map.

When `M = N`, this is true more strongly as `Module.End.baseChangeHom`. -/
@[simps]
/--
Definition of `baseChangeHom` / `baseChangeHom` 的定义

English:
definition baseChangeHom
  signature: : (M ->ₗ[R] N) ->ₗ[R] A otimes[R] M ->ₗ[A] A otimes[R] N where
  body: baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul

中文:
定义 baseChangeHom
  签名: : (M ->ₗ[R] N) ->ₗ[R] A otimes[R] M ->ₗ[A] A otimes[R] N where
  定义体: baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul

Depends on / 依赖: baseChange
-/
def baseChangeHom : (M ->ₗ[R] N) ->ₗ[R] A otimes[R] M ->ₗ[A] A otimes[R] N where
  toFun := baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul

/-- `baseChange` as an `AlgHom`. -/
@[simps!]
/--
Definition of `_root_.Module.End.baseChangeHom` / `_root_.Module.End.baseChangeHom` 的定义

English:
definition _root_.Module.End.baseChangeHom
  signature: : Module.End R M ->ₐ[R] Module.End A (A otimes[R] M)
  body: .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul

中文:
定义 _root_.Module.End.baseChangeHom
  签名: : Module.End R M ->ₐ[R] Module.End A (A otimes[R] M)
  定义体: .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul

Depends on / 依赖: LinearMap, LinearMap.baseChangeHom, baseChangeHom, baseChange_mul, baseChange_one, ofLinearMap
-/
def _root_.Module.End.baseChangeHom : Module.End R M ->ₐ[R] Module.End A (A otimes[R] M) :=
  .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul

/--
lemma `baseChange_pow` / 引理 `baseChange_pow`

English:
lemma baseChange_pow
  given: (f : Module.End R M) (n : Nat)
  proof: map_pow (Module.End.baseChangeHom _ _ _) f n

中文:
引理 baseChange_pow
  条件: (f : Module.End R M) (n : 自然数)
  证明: map_pow (Module.End.baseChangeHom _ _ _) f n

Depends on / 依赖: Module, Module.End.baseChangeHom, baseChangeHom, map_pow
-/
lemma baseChange_pow (f : Module.End R M) (n : Nat) :
    (f ^ n).baseChange A = f.baseChange A ^ n :=
  map_pow (Module.End.baseChangeHom _ _ _) f n

/--
Definition of `_root_.LinearEquiv.baseChange` / `_root_.LinearEquiv.baseChange` 的定义

English:
definition _root_.LinearEquiv.baseChange
  signature: (e : M ≃ₗ[R] N)
  body: AlgebraTensorModule.congr (.refl _ _) e

@[simp]

中文:
定义 _root_.LinearEquiv.baseChange
  签名: (e : M ≃ₗ[R] N)
  定义体: AlgebraTensorModule.congr (.refl _ _) e

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr
-/
def _root_.LinearEquiv.baseChange (e : M ≃ₗ[R] N) : A otimes[R] M ≃ₗ[A] A otimes[R] N :=
  AlgebraTensorModule.congr (.refl _ _) e

@[simp]
/--
theorem `_root_.LinearEquiv.coe_baseChange` / 定理 `_root_.LinearEquiv.coe_baseChange`

English:
theorem _root_.LinearEquiv.coe_baseChange
  given: (f : M ≃ₗ[R] N)
  proof: rfl

中文:
定理 _root_.LinearEquiv.coe_baseChange
  条件: (f : M ≃ₗ[R] N)
  证明: rfl
-/
theorem _root_.LinearEquiv.coe_baseChange (f : M ≃ₗ[R] N) :
    f.baseChange R A M N = f.toLinearMap.baseChange A :=
   rfl

/--
lemma `_root_.LinearEquiv.baseChange_tmul` / 引理 `_root_.LinearEquiv.baseChange_tmul`

English:
lemma _root_.LinearEquiv.baseChange_tmul
  given: {e : M ≃ₗ[R] N} (a : A) (m : M)
  proof: rfl

中文:
引理 _root_.LinearEquiv.baseChange_tmul
  条件: {e : M ≃ₗ[R] N} (a : A) (m : M)
  证明: rfl
-/
@[simp] lemma _root_.LinearEquiv.baseChange_tmul {e : M ≃ₗ[R] N} (a : A) (m : M) :
    e.baseChange R A M N (a otimesₜ m) = a otimesₜ e m :=
  rfl

/--
lemma `_root_.LinearEquiv.baseChange_symm_tmul` / 引理 `_root_.LinearEquiv.baseChange_symm_tmul`

English:
lemma _root_.LinearEquiv.baseChange_symm_tmul
  given: {e : M ≃ₗ[R] N} (a : A) (n : N)
  proof: rfl

@[simp]

中文:
引理 _root_.LinearEquiv.baseChange_symm_tmul
  条件: {e : M ≃ₗ[R] N} (a : A) (n : N)
  证明: rfl

@[simp]
-/
@[simp] lemma _root_.LinearEquiv.baseChange_symm_tmul {e : M ≃ₗ[R] N} (a : A) (n : N) :
    (e.baseChange R A).symm (a otimesₜ n) = a otimesₜ e.symm n :=
  rfl

@[simp]
/--
theorem `_root_.LinearEquiv.baseChange_one` / 定理 `_root_.LinearEquiv.baseChange_one`

English:
theorem _root_.LinearEquiv.baseChange_one
  proof: by
  ext x
  simp [← LinearEquiv.coe_toLinearMap]

中文:
定理 _root_.LinearEquiv.baseChange_one
  证明: by
  ext x
  simp [← LinearEquiv.coe_toLinearMap]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, coe_toLinearMap
-/
theorem _root_.LinearEquiv.baseChange_one :
    (1 : M ≃ₗ[R] M).baseChange R A M M = 1 := by
  ext x
  simp [← LinearEquiv.coe_toLinearMap]

/--
theorem `_root_.LinearEquiv.baseChange_trans` / 定理 `_root_.LinearEquiv.baseChange_trans`

English:
theorem _root_.LinearEquiv.baseChange_trans
  given: (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P)
  proof: by
  ext x
  simp only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange, LinearEquiv.trans_apply,
    LinearEquiv.coe_trans, baseChange_eq_ltensor, lTensor_comp_apply]

中文:
定理 _root_.LinearEquiv.baseChange_trans
  条件: (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P)
  证明: by
  ext x
  simp only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange, LinearEquiv.trans_apply,
    LinearEquiv.coe_trans, baseChange_eq_ltensor, lTensor_comp_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_baseChange, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_trans, LinearEquiv.trans_apply, baseChange_eq_ltensor, coe_baseChange, coe_toLinearMap, coe_trans, lTensor_comp_apply, trans_apply
-/
theorem _root_.LinearEquiv.baseChange_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    (e.trans f).baseChange R A M P = (e.baseChange R A M N).trans (f.baseChange R A N P) := by
  ext x
  simp only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange, LinearEquiv.trans_apply,
    LinearEquiv.coe_trans, baseChange_eq_ltensor, lTensor_comp_apply]

/--
theorem `_root_.LinearEquiv.baseChange_mul` / 定理 `_root_.LinearEquiv.baseChange_mul`

English:
theorem _root_.LinearEquiv.baseChange_mul
  given: (e : M ≃ₗ[R] M) (f : M ≃ₗ[R] M)
  proof: by
  simp [LinearEquiv.mul_eq_trans, LinearEquiv.baseChange_trans]

中文:
定理 _root_.LinearEquiv.baseChange_mul
  条件: (e : M ≃ₗ[R] M) (f : M ≃ₗ[R] M)
  证明: by
  simp [LinearEquiv.mul_eq_trans, LinearEquiv.baseChange_trans]

Depends on / 依赖: LinearEquiv, LinearEquiv.baseChange_trans, LinearEquiv.mul_eq_trans, baseChange_trans, mul_eq_trans
-/
theorem _root_.LinearEquiv.baseChange_mul (e : M ≃ₗ[R] M) (f : M ≃ₗ[R] M) :
    (e * f).baseChange R A M M = (e.baseChange R A M M) * (f.baseChange R A M M) := by
  simp [LinearEquiv.mul_eq_trans, LinearEquiv.baseChange_trans]

/--
theorem `_root_.LinearEquiv.baseChange_symm` / 定理 `_root_.LinearEquiv.baseChange_symm`

English:
theorem _root_.LinearEquiv.baseChange_symm
  given: (e : M ≃ₗ[R] N)
  proof: by
  ext x
  rw [LinearEquiv.eq_symm_apply]
  simp [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange,
    baseChange_eq_ltensor, ← lTensor_comp_apply]

中文:
定理 _root_.LinearEquiv.baseChange_symm
  条件: (e : M ≃ₗ[R] N)
  证明: by
  ext x
  rw [LinearEquiv.eq_symm_apply]
  simp [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange,
    baseChange_eq_ltensor, ← lTensor_comp_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_baseChange, LinearEquiv.coe_toLinearMap, LinearEquiv.eq_symm_apply, baseChange_eq_ltensor, coe_baseChange, coe_toLinearMap, eq_symm_apply, lTensor_comp_apply
-/
theorem _root_.LinearEquiv.baseChange_symm (e : M ≃ₗ[R] N) :
    e.symm.baseChange R A N M = (e.baseChange R A M N).symm := by
  ext x
  rw [LinearEquiv.eq_symm_apply]
  simp [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange,
    baseChange_eq_ltensor, ← lTensor_comp_apply]

/--
theorem `_root_.LinearEquiv.baseChange_inv` / 定理 `_root_.LinearEquiv.baseChange_inv`

English:
theorem _root_.LinearEquiv.baseChange_inv
  given: (e : M ≃ₗ[R] M)
  proof: LinearEquiv.baseChange_symm R A M M e

中文:
定理 _root_.LinearEquiv.baseChange_inv
  条件: (e : M ≃ₗ[R] M)
  证明: LinearEquiv.baseChange_symm R A M M e

Depends on / 依赖: LinearEquiv, LinearEquiv.baseChange_symm, baseChange_symm
-/
theorem _root_.LinearEquiv.baseChange_inv (e : M ≃ₗ[R] M) :
    (e⁻¹).baseChange R A M M = (e.baseChange R A M M)⁻¹ :=
  LinearEquiv.baseChange_symm R A M M e

/--
lemma `_root_.LinearEquiv.baseChange_pow` / 引理 `_root_.LinearEquiv.baseChange_pow`

English:
lemma _root_.LinearEquiv.baseChange_pow
  given: (f : M ≃ₗ[R] M) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n h =>
    simp [pow_succ, LinearEquiv.baseChange_mul, h]

中文:
引理 _root_.LinearEquiv.baseChange_pow
  条件: (f : M ≃ₗ[R] M) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n h =>
    simp [pow_succ, LinearEquiv.baseChange_mul, h]

Depends on / 依赖: LinearEquiv, LinearEquiv.baseChange_mul, baseChange_mul, pow_succ
-/
lemma _root_.LinearEquiv.baseChange_pow (f : M ≃ₗ[R] M) (n : Nat) :
    (f ^ n).baseChange R A M M = f.baseChange R A M M ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    simp [pow_succ, LinearEquiv.baseChange_mul, h]

/--
lemma `_root_.LinearEquiv.baseChange_zpow` / 引理 `_root_.LinearEquiv.baseChange_zpow`

English:
lemma _root_.LinearEquiv.baseChange_zpow
  given: (f : M ≃ₗ[R] M) (n : Int)
  proof: by
  induction n with
  | zero => simp
  | succ n h =>
    simp only [zpow_add_one, LinearEquiv.baseChange_mul, h]
  | pred n h =>
    simp only [zpow_sub_one, LinearEquiv.baseChange_mul, h, LinearEquiv.baseChange_inv]

中文:
引理 _root_.LinearEquiv.baseChange_zpow
  条件: (f : M ≃ₗ[R] M) (n : 整数)
  证明: by
  induction n with
  | zero => simp
  | succ n h =>
    simp only [zpow_add_one, LinearEquiv.baseChange_mul, h]
  | pred n h =>
    simp only [zpow_sub_one, LinearEquiv.baseChange_mul, h, LinearEquiv.baseChange_inv]

Depends on / 依赖: LinearEquiv, LinearEquiv.baseChange_inv, LinearEquiv.baseChange_mul, baseChange_inv, baseChange_mul, zpow_add_one, zpow_sub_one
-/
lemma _root_.LinearEquiv.baseChange_zpow (f : M ≃ₗ[R] M) (n : Int) :
    (f ^ n).baseChange R A M M = f.baseChange R A M M ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    simp only [zpow_add_one, LinearEquiv.baseChange_mul, h]
  | pred n h =>
    simp only [zpow_sub_one, LinearEquiv.baseChange_mul, h, LinearEquiv.baseChange_inv]

variable {R A M N} in
/--
theorem `rTensor_baseChange` / 定理 `rTensor_baseChange`

English:
theorem rTensor_baseChange
  given: (φ : A ->ₐ[R] B) (t : A otimes[R] M) (f : M ->ₗ[R] N)
  proof: by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply]

中文:
定理 rTensor_baseChange
  条件: (φ : A ->ₐ[R] B) (t : A otimes[R] M) (f : M ->ₗ[R] N)
  证明: by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply]

Depends on / 依赖: LinearMap, LinearMap.baseChange_eq_ltensor, LinearMap.comp_apply, baseChange_eq_ltensor, comp_apply
-/
theorem rTensor_baseChange (φ : A ->ₐ[R] B) (t : A otimes[R] M) (f : M ->ₗ[R] N) :
    (φ.toLinearMap.rTensor N) (f.baseChange A t) =
      (f.baseChange B) (φ.toLinearMap.rTensor M t) := by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply]

end Semiring

section Ring

variable {R A B M N : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f g : M ->ₗ[R] N)

@[simp]
/--
theorem `baseChange_sub` / 定理 `baseChange_sub`

English:
theorem baseChange_sub
  statement: (f - g).baseChange A = f.baseChange A - g.baseChange A
  proof: by
  ext
  simp [tmul_sub]

@[simp]

中文:
定理 baseChange_sub
  结论: (f - g).baseChange A = f.baseChange A - g.baseChange A
  证明: by
  ext
  simp [tmul_sub]

@[simp]

Depends on / 依赖: tmul_sub
-/
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  simp [tmul_sub]

@[simp]
/--
theorem `baseChange_neg` / 定理 `baseChange_neg`

English:
theorem baseChange_neg
  statement: (-f).baseChange A = -f.baseChange A
  proof: by
  ext
  simp [tmul_neg]

中文:
定理 baseChange_neg
  结论: (-f).baseChange A = -f.baseChange A
  证明: by
  ext
  simp [tmul_neg]

Depends on / 依赖: tmul_neg
-/
theorem baseChange_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  simp [tmul_neg]

end Ring

end LinearMap

namespace Submodule

open TensorProduct

variable {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] (p q : Submodule R M)

/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: : Submodule A (A otimes[R] M)
  body: LinearMap.range (p.subtype.baseChange A)

中文:
定义 baseChange
  签名: : Submodule A (A otimes[R] M)
  定义体: LinearMap.range (p.subtype.baseChange A)

Depends on / 依赖: LinearMap, LinearMap.range, baseChange, p.subtype.baseChange, subtype
-/
def baseChange : Submodule A (A otimes[R] M) :=
  LinearMap.range (p.subtype.baseChange A)

variable {A p} in
/--
lemma `tmul_mem_baseChange_of_mem` / 引理 `tmul_mem_baseChange_of_mem`

English:
lemma tmul_mem_baseChange_of_mem
  given: (a : A) {m : M} (hm : m in p)
  proof: ⟨a otimesₜ[R] ⟨m, hm⟩, rfl⟩

中文:
引理 tmul_mem_baseChange_of_mem
  条件: (a : A) {m : M} (hm : m in p)
  证明: ⟨a otimesₜ[R] ⟨m, hm⟩, rfl⟩
-/
lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m in p) :
    a otimesₜ[R] m in p.baseChange A :=
  ⟨a otimesₜ[R] ⟨m, hm⟩, rfl⟩

/--
lemma `baseChange_eq_span` / 引理 `baseChange_eq_span`

English:
lemma baseChange_eq_span
  statement: p.baseChange A = span A (p.map (TensorProduct.mk R A M 1))
  proof: by
  refine le_antisymm ?_ ?_
  · rw [baseChange, LinearMap.range_le_iff_comap, eq_top_iff,
      ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..), span_le]
    refine fun _ ⟨a, m, h⟩ => ?_
    rw [← h]; rw [SetLike.mem_coe]; rw [mem_comap]; rw [LinearMap.baseChange_tmul]; rw [← mul_one a]

中文:
引理 baseChange_eq_span
  结论: p.baseChange A = span A (p.map (TensorProduct.mk R A M 1))
  证明: by
  refine le_antisymm ?_ ?_
  · rw [baseChange, LinearMap.range_le_iff_comap, eq_top_iff,
      ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..), span_le]
    refine fun _ ⟨a, m, h⟩ => ?_
    rw [← h]; rw [SetLike.mem_coe]; rw [mem_comap]; rw [LinearMap.baseChange_tmul]; rw [← mul_one a]

Depends on / 依赖: LinearMap, LinearMap.baseChange_tmul, LinearMap.range_le_iff_comap, S.subtype, SetLike, SetLike.mem_coe, baseChange, baseChange_tmul, eq_top_iff, le_antisymm, mem_coe, mem_comap, mul_one, range_le_iff_comap, relMap_leSymb, smul_eq_mul, smul_mem, smul_tmul, span_eq_top_of_span_eq_top, span_le
-/
lemma baseChange_eq_span : p.baseChange A = span A (p.map (TensorProduct.mk R A M 1)) := by
  refine le_antisymm ?_ ?_
  · rw [baseChange, LinearMap.range_le_iff_comap, eq_top_iff,
      ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..), span_le]
    refine fun _ ⟨a, m, h⟩ => ?_
    rw [← h]; rw [SetLike.mem_coe]; rw [mem_comap]; rw [LinearMap.baseChange_tmul]; rw [← mul_one a]; rw [← smul_eq_mul]; rw [← smul_tmul']
    exact smul_mem _ a (subset_span ⟨m, m.2, rfl⟩)
  · refine span_le.2 fun _ ⟨m, hm, h⟩ => h ▸ ⟨1 otimesₜ[R] ⟨m, hm⟩, rfl⟩

@[simp]
/--
lemma `baseChange_bot` / 引理 `baseChange_bot`

English:
lemma baseChange_bot
  statement: (⊥ : Submodule R M).baseChange A = ⊥
  proof: by simp [baseChange_eq_span]

@[simp]

中文:
引理 baseChange_bot
  结论: (⊥ : Submodule R M).baseChange A = ⊥
  证明: by simp [baseChange_eq_span]

@[simp]

Depends on / 依赖: baseChange_eq_span
-/
lemma baseChange_bot : (⊥ : Submodule R M).baseChange A = ⊥ := by simp [baseChange_eq_span]

@[simp]
/--
lemma `baseChange_top` / 引理 `baseChange_top`

English:
lemma baseChange_top
  statement: (⊤ : Submodule R M).baseChange A = ⊤
  proof: by
  rw [eq_top_iff]; rw [← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..)]
  exact span_le.2 fun _ ⟨a, m, h⟩ => h ▸ tmul_mem_baseChange_of_mem _ trivial

中文:
引理 baseChange_top
  结论: (⊤ : Submodule R M).baseChange A = ⊤
  证明: by
  rw [eq_top_iff]; rw [← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..)]
  exact span_le.2 fun _ ⟨a, m, h⟩ => h ▸ tmul_mem_baseChange_of_mem _ trivial

Depends on / 依赖: eq_top_iff, span_eq_top_of_span_eq_top, span_le, span_tmul_eq_top, tmul_mem_baseChange_of_mem
-/
lemma baseChange_top : (⊤ : Submodule R M).baseChange A = ⊤ := by
  rw [eq_top_iff]; rw [← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..)]
  exact span_le.2 fun _ ⟨a, m, h⟩ => h ▸ tmul_mem_baseChange_of_mem _ trivial

variable {p q} in
/--
theorem `baseChange_mono` / 定理 `baseChange_mono`

English:
theorem baseChange_mono
  given: (h : p <= q)
  statement: p.baseChange A <= q.baseChange A
  proof: by
  rw [baseChange]; rw [LinearMap.baseChange]; rw [← subtype_comp_inclusion p q h]; rw [← LinearMap.id_comp LinearMap.id]; rw [AlgebraTensorModule.map_comp]
  apply LinearMap.range_comp_le_range

@[simp]

中文:
定理 baseChange_mono
  条件: (h : p <= q)
  结论: p.baseChange A <= q.baseChange A
  证明: by
  rw [baseChange]; rw [LinearMap.baseChange]; rw [← subtype_comp_inclusion p q h]; rw [← LinearMap.id_comp LinearMap.id]; rw [AlgebraTensorModule.map_comp]
  apply LinearMap.range_comp_le_range

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map_comp, LinearMap, LinearMap.baseChange, LinearMap.id, LinearMap.id_comp, LinearMap.range_comp_le_range, baseChange, id_comp, map_comp, range_comp_le_range, subtype_comp_inclusion
-/
theorem baseChange_mono (h : p <= q) : p.baseChange A <= q.baseChange A := by
  rw [baseChange]; rw [LinearMap.baseChange]; rw [← subtype_comp_inclusion p q h]; rw [← LinearMap.id_comp LinearMap.id]; rw [AlgebraTensorModule.map_comp]
  apply LinearMap.range_comp_le_range

@[simp]
/--
lemma `baseChange_span` / 引理 `baseChange_span`

English:
lemma baseChange_span
  given: (s : Set M)
  proof: by
  rw [baseChange_eq_span]; rw [map_span]; rw [span_span_of_tower]

中文:
引理 baseChange_span
  条件: (s : Set M)
  证明: by
  rw [baseChange_eq_span]; rw [map_span]; rw [span_span_of_tower]

Depends on / 依赖: baseChange_eq_span, map_span, span_span_of_tower
-/
lemma baseChange_span (s : Set M) :
    (span R s).baseChange A = span A (TensorProduct.mk R A M 1 '' s) := by
  rw [baseChange_eq_span]; rw [map_span]; rw [span_span_of_tower]

/--
Definition of `toBaseChange` / `toBaseChange` 的定义

English:
definition toBaseChange
  signature: : A otimes[R] p ->ₗ[A] p.baseChange A
  body: LinearMap.rangeRestrict _

中文:
定义 toBaseChange
  签名: : A otimes[R] p ->ₗ[A] p.baseChange A
  定义体: LinearMap.rangeRestrict _

Depends on / 依赖: LinearMap, LinearMap.rangeRestrict, rangeRestrict
-/
def toBaseChange : A otimes[R] p ->ₗ[A] p.baseChange A :=
  LinearMap.rangeRestrict _

/--
lemma `coe_toBaseChange_tmul` / 引理 `coe_toBaseChange_tmul`

English:
lemma coe_toBaseChange_tmul
  given: (a : A) (x : p)
  proof: rfl

中文:
引理 coe_toBaseChange_tmul
  条件: (a : A) (x : p)
  证明: rfl
-/
@[simp] lemma coe_toBaseChange_tmul (a : A) (x : p) :
    (p.toBaseChange A (a otimesₜ x) : A otimes[R] M) = a otimesₜ (x : M) := rfl

/--
lemma `toBaseChange_surjective` / 引理 `toBaseChange_surjective`

English:
lemma toBaseChange_surjective
  statement: Function.Surjective (p.toBaseChange A)
  proof: LinearMap.surjective_rangeRestrict _

中文:
引理 toBaseChange_surjective
  结论: Function.Surjective (p.toBaseChange A)
  证明: LinearMap.surjective_rangeRestrict _

Depends on / 依赖: LinearMap, LinearMap.surjective_rangeRestrict, surjective_rangeRestrict
-/
lemma toBaseChange_surjective : Function.Surjective (p.toBaseChange A) :=
  LinearMap.surjective_rangeRestrict _

/--
lemma `toBaseChange_surjective'` / 引理 `toBaseChange_surjective'`

English:
lemma toBaseChange_surjective'
  given: {y : A otimes[R] M} (hy : y in p.baseChange A)
  proof: by
  obtain ⟨x, hx⟩ := toBaseChange_surjective A p ⟨y, hy⟩
  exact ⟨x, congr($hx)⟩

中文:
引理 toBaseChange_surjective'
  条件: {y : A otimes[R] M} (hy : y in p.baseChange A)
  证明: by
  obtain ⟨x, hx⟩ := toBaseChange_surjective A p ⟨y, hy⟩
  exact ⟨x, congr($hx)⟩

Depends on / 依赖: toBaseChange_surjective
-/
lemma toBaseChange_surjective' {y : A otimes[R] M} (hy : y in p.baseChange A) :
    exists x : A otimes[R] p, p.toBaseChange A x = y := by
  obtain ⟨x, hx⟩ := toBaseChange_surjective A p ⟨y, hy⟩
  exact ⟨x, congr($hx)⟩

end Submodule

namespace TensorProduct.AlgebraTensorModule

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module A N]

/--
lemma `baseChange_comp_cancelBaseChange_symm_self` / 引理 `baseChange_comp_cancelBaseChange_symm_self`

English:
lemma baseChange_comp_cancelBaseChange_symm_self
  given: (f : (A otimes[R] M) ->ₗ[A] N)
  proof: by
  rw [cancelBaseChange_self_eq_lid]
  ext x
  simp

中文:
引理 baseChange_comp_cancelBaseChange_symm_self
  条件: (f : (A otimes[R] M) ->ₗ[A] N)
  证明: by
  rw [cancelBaseChange_self_eq_lid]
  ext x
  simp

Depends on / 依赖: cancelBaseChange_self_eq_lid
-/
lemma baseChange_comp_cancelBaseChange_symm_self (f : (A otimes[R] M) ->ₗ[A] N) :
    f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm = (TensorProduct.lid A N).symm ∘ₗ f := by
  rw [cancelBaseChange_self_eq_lid]
  ext x
  simp

/--
lemma `ker_baseChange_comp_cancelBaseChange_symm` / 引理 `ker_baseChange_comp_cancelBaseChange_symm`

English:
lemma ker_baseChange_comp_cancelBaseChange_symm
  given: (f : (A otimes[R] M) ->ₗ[A] N)
  proof: by
  rw [baseChange_comp_cancelBaseChange_symm_self]; rw [LinearMap.ker_comp]; rw [LinearEquiv.ker]; rw [Submodule.comap_bot]

中文:
引理 ker_baseChange_comp_cancelBaseChange_symm
  条件: (f : (A otimes[R] M) ->ₗ[A] N)
  证明: by
  rw [baseChange_comp_cancelBaseChange_symm_self]; rw [LinearMap.ker_comp]; rw [LinearEquiv.ker]; rw [Submodule.comap_bot]

Depends on / 依赖: LinearEquiv, LinearEquiv.ker, LinearMap, LinearMap.ker_comp, Submodule, Submodule.comap_bot, baseChange_comp_cancelBaseChange_symm_self, comap_bot, ker_comp
-/
lemma ker_baseChange_comp_cancelBaseChange_symm (f : (A otimes[R] M) ->ₗ[A] N) :
    (f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm).ker = f.ker := by
  rw [baseChange_comp_cancelBaseChange_symm_self]; rw [LinearMap.ker_comp]; rw [LinearEquiv.ker]; rw [Submodule.comap_bot]

end TensorProduct.AlgebraTensorModule
