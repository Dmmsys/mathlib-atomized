/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Module.Rat
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Maps between tensor products of R-algebras

This file provides results about maps between tensor products of `R`-algebras.

## Main declarations

- the structure isomorphisms
  * `Algebra.TensorProduct.lid : R ⊗[R] A ≃ₐ[R] A`
  * `Algebra.TensorProduct.rid : A ⊗[R] R ≃ₐ[S] A` (usually used with `S = R` or `S = A`)
  * `Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `Algebra.TensorProduct.assoc : ((A ⊗[S] C) ⊗[R] D) ≃ₐ[T] (A ⊗[S] (C ⊗[R] D))`
- `Algebra.TensorProduct.liftEquiv`: a universal property for the tensor product of algebras.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

@[expose] public section

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct

namespace Module.End

open LinearMap

variable (R M N : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The map `LinearMap.lTensorHom` which sends `f ↦ 1 ⊗ f` as a morphism of algebras. -/
@[simps!]
/--
Definition of `lTensorAlgHom` / `lTensorAlgHom` 的定义

English:
definition lTensorAlgHom
  signature: : Module.End R M ->ₐ[R] Module.End R (N otimes[R] M)
  body: .ofLinearMap (lTensorHom (M := N)) (lTensor_id N M) (lTensor_mul N)

中文:
定义 lTensorAlgHom
  签名: : 模.End R M ->ₐ[R] 模.End R (N otimes[R] M)
  定义体: .ofLinearMap (lTensorHom (M := N)) (lTensor_id N M) (lTensor_mul N)

Depends on / 依赖: lTensorHom, lTensor_id, lTensor_mul, ofLinearMap
-/
def lTensorAlgHom : Module.End R M ->ₐ[R] Module.End R (N otimes[R] M) :=
  .ofLinearMap (lTensorHom (M := N)) (lTensor_id N M) (lTensor_mul N)

/-- The map `LinearMap.rTensorHom` which sends `f ↦ f ⊗ 1` as a morphism of algebras. -/
@[simps!]
/--
Definition of `rTensorAlgHom` / `rTensorAlgHom` 的定义

English:
definition rTensorAlgHom
  signature: : Module.End R M ->ₐ[R] Module.End R (M otimes[R] N)
  body: .ofLinearMap (rTensorHom (M := N)) (rTensor_id N M) (rTensor_mul N)

中文:
定义 rTensorAlgHom
  签名: : 模.End R M ->ₐ[R] 模.End R (M otimes[R] N)
  定义体: .ofLinearMap (rTensorHom (M := N)) (rTensor_id N M) (rTensor_mul N)

Depends on / 依赖: ofLinearMap, rTensorHom, rTensor_id, rTensor_mul
-/
def rTensorAlgHom : Module.End R M ->ₐ[R] Module.End R (M otimes[R] N) :=
  .ofLinearMap (rTensorHom (M := N)) (rTensor_id N M) (rTensor_mul N)

end Module.End

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
We build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra S C]
variable [Semiring D] [Algebra R D]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `_root_.LinearMap.map_mul_of_map_mul_tmul` / 引理 `_root_.LinearMap.map_mul_of_map_mul_tmul`

English:
lemma _root_.LinearMap.map_mul_of_map_mul_tmul
  statement: {f : A otimes[R] B ->ₗ[S] C}
  proof: f.map_mul_iff.2 (by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    let : Algebra R C := .restrictScalars R S C
    let : IsScalarTower R S C := .restrictScalars R S C
    ext
    dsimp
    exact hf _ _ _ _) x y

中文:
引理 _root_.线性映射.map_mul_of_map_mul_tmul
  结论: {f : A otimes[R] B ->ₗ[S] C}
  证明: f.map_mul_iff.2 (by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    let : Algebra R C := .restrictScalars R S C
    let : IsScalarTower R S C := .restrictScalars R S C
    ext
    dsimp
    exact hf _ _ _ _) x y

Depends on / 依赖: f.map_mul_iff, map_mul_iff
-/
lemma _root_.LinearMap.map_mul_of_map_mul_tmul {f : A otimes[R] B ->ₗ[S] C}
    (hf : forall (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁) * f (a₂ otimesₜ b₂))
    (x y : A otimes[R] B) : f (x * y) = f x * f y :=
  f.map_mul_iff.2 (by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    let : Algebra R C := .restrictScalars R S C
    let : IsScalarTower R S C := .restrictScalars R S C
    ext
    dsimp
    exact hf _ _ _ _) x y

/--
Definition of `algHomOfLinearMapTensorProduct` / `algHomOfLinearMapTensorProduct` 的定义

English:
definition algHomOfLinearMapTensorProduct
  signature: (f : A otimes[R] B ->ₗ[S] C)
  body: AlgHom.ofLinearMap f h_one (f.map_mul_of_map_mul_tmul h_mul)

@[simp]

中文:
定义 algHomOfLinearMapTensorProduct
  签名: (f : A otimes[R] B ->ₗ[S] C)
  定义体: AlgHom.ofLinearMap f h_one (f.map_mul_of_map_mul_tmul h_mul)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, f.map_mul_of_map_mul_tmul, h_mul, h_one, map_mul_of_map_mul_tmul, ofLinearMap
-/
def algHomOfLinearMapTensorProduct (f : A otimes[R] B ->ₗ[S] C)
    (h_mul : forall (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁) * f (a₂ otimesₜ b₂))
    (h_one : f (1 otimesₜ[R] 1) = 1) : A otimes[R] B ->ₐ[S] C :=
  AlgHom.ofLinearMap f h_one (f.map_mul_of_map_mul_tmul h_mul)

@[simp]
/--
theorem `algHomOfLinearMapTensorProduct_apply` / 定理 `algHomOfLinearMapTensorProduct_apply`

English:
theorem algHomOfLinearMapTensorProduct_apply
  given: (f h_mul h_one x)
  proof: rfl

中文:
定理 algHomOfLinearMapTensorProduct_apply
  条件: (f h_mul h_one x)
  证明: rfl
-/
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A otimes[R] B ->ₐ[S] C) x = f x :=
  rfl

/--
Definition of `algEquivOfLinearEquivTensorProduct` / `algEquivOfLinearEquivTensorProduct` 的定义

English:
definition algEquivOfLinearEquivTensorProduct
  signature: (f : A otimes[R] B ≃ₗ[S] C)
  body: { algHomOfLinearMapTensorProduct (f : A otimes[R] B ->ₗ[S] C) h_mul h_one, f with }

@[simp]

中文:
定义 algEquivOfLinearEquivTensorProduct
  签名: (f : A otimes[R] B ≃ₗ[S] C)
  定义体: { algHomOfLinearMapTensorProduct (f : A otimes[R] B ->ₗ[S] C) h_mul h_one, f with }

@[simp]

Depends on / 依赖: algHomOfLinearMapTensorProduct, h_mul, h_one, otimes
-/
def algEquivOfLinearEquivTensorProduct (f : A otimes[R] B ≃ₗ[S] C)
    (h_mul : forall (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁) * f (a₂ otimesₜ b₂))
    (h_one : f (1 otimesₜ[R] 1) = 1) : A otimes[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A otimes[R] B ->ₗ[S] C) h_mul h_one, f with }

@[simp]
/--
theorem `algEquivOfLinearEquivTensorProduct_apply` / 定理 `algEquivOfLinearEquivTensorProduct_apply`

English:
theorem algEquivOfLinearEquivTensorProduct_apply
  given: (f h_mul h_one x)
  proof: rfl

中文:
定理 algEquivOfLinearEquivTensorProduct_apply
  条件: (f h_mul h_one x)
  证明: rfl
-/
theorem algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTensorProduct f h_mul h_one : A otimes[R] B ≃ₐ[S] C) x = f x :=
  rfl

variable [Algebra R C]
/--
Definition of `algEquivOfLinearEquivTripleTensorProduct` / `algEquivOfLinearEquivTripleTensorProduct` 的定义

English:
definition algEquivOfLinearEquivTripleTensorProduct
  signature: (f : A otimes[R] B otimes[R] C ≃ₗ[R] D)
  body: AlgEquiv.ofLinearEquiv f h_one f.map_mul_iff.2 by
    ext
    simpa using h_mul _ _ _ _ _ _

@[simp]

中文:
定义 algEquivOfLinearEquivTripleTensorProduct
  签名: (f : A otimes[R] B otimes[R] C ≃ₗ[R] D)
  定义体: AlgEquiv.ofLinearEquiv f h_one f.map_mul_iff.2 by
    ext
    simpa using h_mul _ _ _ _ _ _

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, f.map_mul_iff, h_mul, h_one, map_mul_iff, ofLinearEquiv
-/
def algEquivOfLinearEquivTripleTensorProduct (f : A otimes[R] B otimes[R] C ≃ₗ[R] D)
    (h_mul :
      forall (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) otimesₜ (b₁ * b₂) otimesₜ (c₁ * c₂)) = f (a₁ otimesₜ b₁ otimesₜ c₁) * f (a₂ otimesₜ b₂ otimesₜ c₂))
    (h_one : f (((1 : A) otimesₜ[R] (1 : B)) otimesₜ[R] (1 : C)) = 1) :
    A otimes[R] B otimes[R] C ≃ₐ[R] D :=
AlgEquiv.ofLinearEquiv f h_one f.map_mul_iff.2 by
    ext
    simpa using h_mul _ _ _ _ _ _

@[simp]
/--
theorem `algEquivOfLinearEquivTripleTensorProduct_apply` / 定理 `algEquivOfLinearEquivTripleTensorProduct_apply`

English:
theorem algEquivOfLinearEquivTripleTensorProduct_apply
  given: (f h_mul h_one x)
  proof: rfl

中文:
定理 algEquivOfLinearEquivTripleTensorProduct_apply
  条件: (f h_mul h_one x)
  证明: rfl
-/
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTripleTensorProduct f h_mul h_one : A otimes[R] B otimes[R] C ≃ₐ[R] D) x = f x :=
  rfl

section lift
variable [IsScalarTower R S C]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y))
  body: algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C ->ₗ[S] C) ->ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
LinearMap.flip (restr ∘ₗ Lin

中文:
定义 lift
  签名: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : 对任意 x y, Commute (f x) (g y))
  定义体: algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C ->ₗ[S] C) ->ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
LinearMap.flip (restr ∘ₗ Lin

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, LinearMap, LinearMap.ext, LinearMap.flip, LinearMap.mul, algHomOfLinearMapTensorProduct, f.toLinearMap, map_add, map_mul, map_one, map_smul, mul_mul_mul_comm, restrictScalars, toLinearMap
-/
def lift (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) : (A otimes[R] B) ->ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C ->ₗ[S] C) ->ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
LinearMap.flip (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [map_mul]; rw [map_mul]; rw [(hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [map_one, map_one, one_mul])

@[simp]
/--
theorem `lift_tmul` / 定理 `lift_tmul`

English:
theorem lift_tmul
  statement: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y))
  proof: rfl

中文:
定理 lift_tmul
  结论: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : 对任意 x y, Commute (f x) (g y))
  证明: rfl
-/
theorem lift_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a otimesₜ b) = f a * g b :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lift_includeLeft_includeRight` / 定理 `lift_includeLeft_includeRight`

English:
theorem lift_includeLeft_includeRight
  proof: by
  ext <;> simp

@[simp]

中文:
定理 lift_includeLeft_includeRight
  证明: by
  ext <;> simp

@[simp]
-/
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun _ _ => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A otimes[R] B) := by
  ext <;> simp

@[simp]
/--
theorem `lift_comp_includeLeft` / 定理 `lift_comp_includeLeft`

English:
theorem lift_comp_includeLeft
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y))
  proof: AlgHom.ext by simp

@[simp]

中文:
定理 lift_comp_includeLeft
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : 对任意 x y, Commute (f x) (g y))
  证明: AlgHom.ext by simp

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem lift_comp_includeLeft (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
AlgHom.ext by simp

@[simp]
/--
theorem `lift_comp_includeRight` / 定理 `lift_comp_includeRight`

English:
theorem lift_comp_includeRight
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y))
  proof: AlgHom.ext by simp

中文:
定理 lift_comp_includeRight
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : 对任意 x y, Commute (f x) (g y))
  证明: AlgHom.ext by simp

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem lift_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
AlgHom.ext by simp

/-- Variant with the same base that doesn't need `restrictScalars`. -/
@[simp]
/--
theorem `lift_comp_includeRight'` / 定理 `lift_comp_includeRight'`

English:
theorem lift_comp_includeRight'
  given: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y))
  proof: AlgHom.ext by simp

中文:
定理 lift_comp_includeRight'
  条件: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (hfg : 对任意 x y, Commute (f x) (g y))
  证明: AlgHom.ext by simp

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem lift_comp_includeRight' (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeRight = g :=
AlgHom.ext by simp

/-- The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requirement for graded
algebra. -/
@[simps]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : {fg : (A ->ₐ[S] C) × (B ->ₐ[R] C) // forall x y, Commute (fg.1 x) (fg.2 y)}
  body: lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

中文:
定义 liftEquiv
  签名: : {fg : (A ->ₐ[S] C) × (B ->ₐ[R] C) // 对任意 x y, Commute (fg.1 x) (fg.2 y)}
  定义体: lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

Depends on / 依赖: fg.prop, fg.val
-/
def liftEquiv : {fg : (A ->ₐ[S] C) × (B ->ₐ[R] C) // forall x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A otimes[R] B) ->ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

variable (R S B) in
/--
Algebra maps `S ⊗[R] B →ₐ[S] C` are the same as algebra maps `B →ₐ[R] C`.
Variant of `Algebra.TensorProduct.liftEquiv` where the left map is fixed.
-/
@[simps]
/--
Definition of `liftEquivRight` / `liftEquivRight` 的定义

English:
definition liftEquivRight
  signature: (C : Type*) [CommRing C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
  body: Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => .all _ _
  invFun f := AlgHom.comp (f.restrictScalars R) Algebra.TensorProduct.includeRight
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 liftEquivRight
  签名: (C : 类型) [交换环 C] [代数 R C] [代数 S C] [标量塔 R S C]
  定义体: Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => .all _ _
  invFun f := AlgHom.comp (f.restrictScalars R) Algebra.TensorProduct.includeRight
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.ofId, TensorProduct
-/
def liftEquivRight (C : Type*) [CommRing C] [Algebra R C] [Algebra S C] [IsScalarTower R S C] :
    (B ->ₐ[R] C) ≃ (S otimes[R] B ->ₐ[S] C) where
  toFun f := Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => .all _ _
  invFun f := AlgHom.comp (f.restrictScalars R) Algebra.TensorProduct.includeRight
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/--
theorem `restrictScalars_lift` / 定理 `restrictScalars_lift`

English:
theorem restrictScalars_lift
  statement: [CommSemiring R'] [Algebra R R'] [Algebra R' S]
  proof: rfl

中文:
定理 restrictScalars_lift
  结论: [交换半环 R'] [代数 R R'] [代数 R' S]
  证明: rfl
-/
theorem restrictScalars_lift [CommSemiring R'] [Algebra R R'] [Algebra R' S]
    [Algebra R' A] [IsScalarTower R R' A] [IsScalarTower R' S A]
    [Algebra R' C] [IsScalarTower R R' C] [IsScalarTower R' S C]
    (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall (x : A) (y : B), Commute (f x) (g y)) :
    (Algebra.TensorProduct.lift f g hfg).restrictScalars R' =
      Algebra.TensorProduct.lift (f.restrictScalars R') g hfg :=
  rfl

end lift

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
variable [Semiring F] [Algebra R F]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected nonrec def lid : R otimes[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])

/--
theorem `lid_toLinearEquiv` / 定理 `lid_toLinearEquiv`

English:
theorem lid_toLinearEquiv
  proof: rfl

中文:
定理 lid_toLinearEquiv
  证明: rfl
-/
@[simp] theorem lid_toLinearEquiv :
    (TensorProduct.lid R A).toLinearEquiv = _root_.TensorProduct.lid R A := rfl

variable {R} {A} in
@[simp]
/--
theorem `lid_tmul` / 定理 `lid_tmul`

English:
theorem lid_tmul
  given: (r : R) (a : A)
  statement: TensorProduct.lid R A (r otimesₜ a) = r • a
  proof: rfl

中文:
定理 lid_tmul
  条件: (r : R) (a : A)
  结论: 张量积.lid R A (r otimesₜ a) = r • a
  证明: rfl
-/
theorem lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r otimesₜ a) = r • a := rfl

variable {A} in
@[simp]
/--
theorem `lid_symm_apply` / 定理 `lid_symm_apply`

English:
theorem lid_symm_apply
  given: (a : A)
  statement: (TensorProduct.lid R A).symm a = 1 otimesₜ a
  proof: rfl

中文:
定理 lid_symm_apply
  条件: (a : A)
  结论: (张量积.lid R A).symm a = 1 otimesₜ a
  证明: rfl
-/
theorem lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 otimesₜ a := rfl

variable (S)

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.

Note that if `A` is commutative this can be instantiated with `S = A`.
-/
protected nonrec def rid : A otimes[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun a₁ a₂ r₁ r₂ => smul_mul_smul_comm r₁ a₁ r₂ a₂ |>.symm)
    (one_smul R _)

/--
theorem `rid_toLinearEquiv` / 定理 `rid_toLinearEquiv`

English:
theorem rid_toLinearEquiv
  proof: rfl

中文:
定理 rid_toLinearEquiv
  证明: rfl
-/
@[simp] theorem rid_toLinearEquiv :
    (TensorProduct.rid R S A).toLinearEquiv = AlgebraTensorModule.rid R S A := rfl

variable {R A} in
@[simp]
/--
theorem `rid_tmul` / 定理 `rid_tmul`

English:
theorem rid_tmul
  given: (r : R) (a : A)
  statement: TensorProduct.rid R S A (a otimesₜ r) = r • a
  proof: rfl

中文:
定理 rid_tmul
  条件: (r : R) (a : A)
  结论: 张量积.rid R S A (a otimesₜ r) = r • a
  证明: rfl
-/
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a otimesₜ r) = r • a := rfl

variable {A} in
@[simp]
/--
theorem `rid_symm_apply` / 定理 `rid_symm_apply`

English:
theorem rid_symm_apply
  given: (a : A)
  statement: (TensorProduct.rid R S A).symm a = a otimesₜ 1
  proof: rfl

中文:
定理 rid_symm_apply
  条件: (a : A)
  结论: (张量积.rid R S A).symm a = a otimesₜ 1
  证明: rfl
-/
theorem rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a otimesₜ 1 := rfl

variable (T) in
/--
lemma `linearMap_comp_rid` / 引理 `linearMap_comp_rid`

English:
lemma linearMap_comp_rid
  statement: (Algebra.linearMap S (S otimes[R] B)).restrictScalars R ∘ₗ
  proof: by
  ext; simp

中文:
引理 linearMap_comp_rid
  结论: (代数.linearMap S (S otimes[R] B)).restrictScalars R ∘ₗ
  证明: by
  ext; simp
-/
lemma linearMap_comp_rid : (Algebra.linearMap S (S otimes[R] B)).restrictScalars R ∘ₗ
    (TensorProduct.rid R R S).toLinearMap = (Algebra.linearMap R B).lTensor S := by
  ext; simp

/--
lemma `rid_comp_includeLeftRingHom` / 引理 `rid_comp_includeLeftRingHom`

English:
lemma rid_comp_includeLeftRingHom
  proof: by
  ext; simp

中文:
引理 rid_comp_includeLeftRingHom
  证明: by
  ext; simp
-/
@[simp] lemma rid_comp_includeLeftRingHom :
    (Algebra.TensorProduct.rid R S A : A otimes[R] R ->+* A).comp includeLeftRingHom = .id A := by
  ext; simp

section

variable (R A B C : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [Semiring C] [Algebra R C]

/--
lemma `tmul_one_tmul_one_tmul` / 引理 `tmul_one_tmul_one_tmul`

English:
lemma tmul_one_tmul_one_tmul
  given: (x : A) (y : C)
  proof: by
  trans x • 1 otimesₜ[A] (1 otimesₜ[R] y)
  · simp [Algebra.smul_def]
  · simp [← tmul_smul, smul_tmul' (M := A)]

中文:
引理 tmul_one_tmul_one_tmul
  条件: (x : A) (y : C)
  证明: by
  trans x • 1 otimesₜ[A] (1 otimesₜ[R] y)
  · simp [Algebra.smul_def]
  · simp [← tmul_smul, smul_tmul' (M := A)]

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def, smul_tmul, tmul_smul
-/
lemma tmul_one_tmul_one_tmul (x : A) (y : C) :
    x otimesₜ[R] (1 : B) otimesₜ[A] ((1 : A) otimesₜ[R] y) = 1 otimesₜ[A] (x otimesₜ[R] y) := by
  trans x • 1 otimesₜ[A] (1 otimesₜ[R] y)
  · simp [Algebra.smul_def]
  · simp [← tmul_smul, smul_tmul' (M := A)]

end

section CompatibleSMul

variable (R S T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T] [Semiring A]
  [Semiring B]
variable [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
variable [Algebra T A] [SMulCommClass R T A] [SMulCommClass S T A]
variable [SMulCommClass R S A] [CompatibleSMul R S A B]

/--
Definition of `mapOfCompatibleSMul` / `mapOfCompatibleSMul` 的定义

English:
definition mapOfCompatibleSMul
  signature: : A otimes[S] B ->ₐ[T] A otimes[R] B
  body: .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul R S T A B) rfl fun x =>
    x.induction_on (by simp) (fun _ _ y => y.induction_on (by simp) (by simp)
      fun _ _ h h' => by simp only [mul_add, map_add, h, h'])
      fun _ _ h h' _ => by simp only [add_mul, map_add, h, h']

中文:
定义 mapOfCompatibleSMul
  签名: : A otimes[S] B ->ₐ[T] A otimes[R] B
  定义体: .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul R S T A B) rfl fun x =>
    x.induction_on (by simp) (fun _ _ y => y.induction_on (by simp) (by simp)
      fun _ _ h h' => by simp only [mul_add, map_add, h, h'])
      fun _ _ h h' _ => by simp only [add_mul, map_add, h, h']

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.mapOfCompatibleSMul, add_mul, induction_on, mapOfCompatibleSMul, map_add, mul_add, ofLinearMap, x.induction_on, y.induction_on
-/
def mapOfCompatibleSMul : A otimes[S] B ->ₐ[T] A otimes[R] B :=
  .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul R S T A B) rfl fun x =>
    x.induction_on (by simp) (fun _ _ y => y.induction_on (by simp) (by simp)
      fun _ _ h h' => by simp only [mul_add, map_add, h, h'])
      fun _ _ h h' _ => by simp only [add_mul, map_add, h, h']

/--
theorem `mapOfCompatibleSMul_tmul` / 定理 `mapOfCompatibleSMul_tmul`

English:
theorem mapOfCompatibleSMul_tmul
  given: (m n)
  statement: mapOfCompatibleSMul R S T A B (m otimesₜ n) = m otimesₜ n
  proof: rfl

中文:
定理 mapOfCompatibleSMul_tmul
  条件: (m n)
  结论: mapOfCompatibleSMul R S T A B (m otimesₜ n) = m otimesₜ n
  证明: rfl
-/
@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R S T A B (m otimesₜ n) = m otimesₜ n :=
  rfl

/--
theorem `mapOfCompatibleSMul_surjective` / 定理 `mapOfCompatibleSMul_surjective`

English:
theorem mapOfCompatibleSMul_surjective
  statement: Function.Surjective (mapOfCompatibleSMul R S T A B)
  proof: _root_.TensorProduct.mapOfCompatibleSMul_surjective R S T A B

中文:
定理 mapOfCompatibleSMul_surjective
  结论: 函数.满射 (mapOfCompatibleSMul R S T A B)
  证明: _root_.TensorProduct.mapOfCompatibleSMul_surjective R S T A B

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.mapOfCompatibleSMul_surjective, mapOfCompatibleSMul_surjective
-/
theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R S T A B) :=
  _root_.TensorProduct.mapOfCompatibleSMul_surjective R S T A B

attribute [local instance] SMulCommClass.symm

@[deprecated (since := "2026-02-21")]
alias mapOfCompatibleSMul' := mapOfCompatibleSMul

/--
Definition of `equivOfCompatibleSMul` / `equivOfCompatibleSMul` 的定义

English:
definition equivOfCompatibleSMul
  signature: [CompatibleSMul S R A B]
  body: mapOfCompatibleSMul R S T A B
  invFun := mapOfCompatibleSMul S R T A B
  __ := _root_.TensorProduct.equivOfCompatibleSMul R S T A B

中文:
定义 equivOfCompatibleSMul
  签名: [余mpatibleSMul S R A B]
  定义体: mapOfCompatibleSMul R S T A B
  invFun := mapOfCompatibleSMul S R T A B
  __ := _root_.TensorProduct.equivOfCompatibleSMul R S T A B

Depends on / 依赖: mapOfCompatibleSMul
-/
def equivOfCompatibleSMul [CompatibleSMul S R A B] : A otimes[S] B ≃ₐ[T] A otimes[R] B where
  __ := mapOfCompatibleSMul R S T A B
  invFun := mapOfCompatibleSMul S R T A B
  __ := _root_.TensorProduct.equivOfCompatibleSMul R S T A B

variable [Algebra R S] [CompatibleSMul R S S A] [CompatibleSMul S R S A]
omit [SMulCommClass R S A]

/--
Definition of `lidOfCompatibleSMul` / `lidOfCompatibleSMul` 的定义

English:
definition lidOfCompatibleSMul
  signature: : S otimes[R] A ≃ₐ[S] A
  body: (equivOfCompatibleSMul R S S S A).symm.trans (TensorProduct.lid _ _)

中文:
定义 lidOfCompatibleSMul
  签名: : S otimes[R] A ≃ₐ[S] A
  定义体: (equivOfCompatibleSMul R S S S A).symm.trans (TensorProduct.lid _ _)

Depends on / 依赖: TensorProduct, TensorProduct.lid, equivOfCompatibleSMul, symm.trans
-/
def lidOfCompatibleSMul : S otimes[R] A ≃ₐ[S] A :=
  (equivOfCompatibleSMul R S S S A).symm.trans (TensorProduct.lid _ _)

/--
theorem `lidOfCompatibleSMul_tmul` / 定理 `lidOfCompatibleSMul_tmul`

English:
theorem lidOfCompatibleSMul_tmul
  given: (s a)
  statement: lidOfCompatibleSMul R S A (s otimesₜ[R] a) = s • a
  proof: rfl

中文:
定理 lidOfCompatibleSMul_tmul
  条件: (s a)
  结论: lidOfCompatibleSMul R S A (s otimesₜ[R] a) = s • a
  证明: rfl
-/
theorem lidOfCompatibleSMul_tmul (s a) : lidOfCompatibleSMul R S A (s otimesₜ[R] a) = s • a := rfl

set_option backward.isDefEq.respectTransparency false in
instance {R M N : Type*} [CommSemiring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module Rat M] [Module Rat N] : CompatibleSMul R Rat M N where
  smul_tmul q m n := by
    have : IsAddTorsionFree (M otimes[R] N) := .of_module_rat _
    suffices q.den • ((q • m) otimesₜ[R] n) = q.den • (m otimesₜ[R] (q • n)) from
smul_right_injective (M otimes[R] N) q.den_nz by norm_cast
    rw [smul_tmul']; rw [← tmul_smul]; rw [← smul_assoc]; rw [← smul_assoc]; rw [nsmul_eq_mul]; rw [Rat.den_mul_eq_num]
    norm_cast
    rw [smul_tmul]

end CompatibleSMul

section

variable (B)

unseal mul in
/--
Definition of `comm` / `comm` 的定义

English:
definition comm
  signature: : A otimes[R] B ≃ₐ[R] B otimes[R] A
  body: algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl

中文:
定义 comm
  签名: : A otimes[R] B ≃ₐ[R] B otimes[R] A
  定义体: algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl
-/
protected def comm : A otimes[R] B ≃ₐ[R] B otimes[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl

/--
theorem `comm_toLinearEquiv` / 定理 `comm_toLinearEquiv`

English:
theorem comm_toLinearEquiv
  proof: rfl

中文:
定理 comm_toLinearEquiv
  证明: rfl
-/
@[simp] theorem comm_toLinearEquiv :
    (Algebra.TensorProduct.comm R A B).toLinearEquiv = _root_.TensorProduct.comm R A B := rfl

variable {A B} in
@[simp]
/--
theorem `comm_tmul` / 定理 `comm_tmul`

English:
theorem comm_tmul
  given: (a : A) (b : B)
  proof: rfl

中文:
定理 comm_tmul
  条件: (a : A) (b : B)
  证明: rfl
-/
theorem comm_tmul (a : A) (b : B) :
    TensorProduct.comm R A B (a otimesₜ b) = b otimesₜ a :=
  rfl

variable {A B} in
@[simp]
/--
theorem `comm_symm_tmul` / 定理 `comm_symm_tmul`

English:
theorem comm_symm_tmul
  given: (a : A) (b : B)
  proof: rfl

中文:
定理 comm_symm_tmul
  条件: (a : A) (b : B)
  证明: rfl
-/
theorem comm_symm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B).symm (b otimesₜ a) = a otimesₜ b :=
  rfl

/--
theorem `comm_symm` / 定理 `comm_symm`

English:
theorem comm_symm
  proof: by
  ext; rfl

@[simp]

中文:
定理 comm_symm
  证明: by
  ext; rfl

@[simp]
-/
theorem comm_symm :
    (TensorProduct.comm R A B).symm = TensorProduct.comm R B A := by
  ext; rfl

@[simp]
/--
lemma `comm_comp_includeLeft` / 引理 `comm_comp_includeLeft`

English:
lemma comm_comp_includeLeft
  proof: rfl

@[simp]

中文:
引理 comm_comp_includeLeft
  证明: rfl

@[simp]
-/
lemma comm_comp_includeLeft :
    (TensorProduct.comm R A B : A otimes[R] B ->ₐ[R] B otimes[R] A).comp includeLeft = includeRight := rfl

@[simp]
/--
lemma `comm_comp_includeRight` / 引理 `comm_comp_includeRight`

English:
lemma comm_comp_includeRight
  proof: rfl

中文:
引理 comm_comp_includeRight
  证明: rfl
-/
lemma comm_comp_includeRight :
    (TensorProduct.comm R A B : A otimes[R] B ->ₐ[R] B otimes[R] A).comp includeRight = includeLeft := rfl

/--
theorem `adjoin_tmul_eq_top` / 定理 `adjoin_tmul_eq_top`

English:
theorem adjoin_tmul_eq_top
  statement: adjoin R { t : A otimes[R] B | exists a b, a otimesₜ[R] b = t } = ⊤
  proof: top_le_iff.mp (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

中文:
定理 adjoin_tmul_eq_top
  结论: adjoin R { t : A otimes[R] B | 存在 a b, a otimesₜ[R] b = t } = ⊤
  证明: top_le_iff.mp (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

Depends on / 依赖: span_le_adjoin, span_tmul_eq_top, top_le_iff, top_le_iff.mp, top_le_iff.mpr
-/
theorem adjoin_tmul_eq_top : adjoin R { t : A otimes[R] B | exists a b, a otimesₜ[R] b = t } = ⊤ :=
top_le_iff.mp (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

section

omit [Algebra S A] [IsScalarTower R S A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Definition of `commRight` / `commRight` 的定义

English:
definition commRight
  signature: : S otimes[R] A ≃ₐ[S] A otimes[R] S where
  body: Algebra.TensorProduct.comm R S A
  commutes' _ := rfl

中文:
定义 commRight
  签名: : S otimes[R] A ≃ₐ[S] A otimes[R] S where
  定义体: Algebra.TensorProduct.comm R S A
  commutes' _ := rfl

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, TensorProduct
-/
def commRight : S otimes[R] A ≃ₐ[S] A otimes[R] S where
  __ := Algebra.TensorProduct.comm R S A
  commutes' _ := rfl

variable {S A} in
@[simp]
/--
lemma `commRight_tmul` / 引理 `commRight_tmul`

English:
lemma commRight_tmul
  given: (s : S) (a : A)
  statement: commRight R S A (s otimesₜ a) = a otimesₜ s
  proof: rfl

中文:
引理 commRight_tmul
  条件: (s : S) (a : A)
  结论: commRight R S A (s otimesₜ a) = a otimesₜ s
  证明: rfl
-/
lemma commRight_tmul (s : S) (a : A) : commRight R S A (s otimesₜ a) = a otimesₜ s := rfl

variable {S A} in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `commRight_symm_tmul` / 引理 `commRight_symm_tmul`

English:
lemma commRight_symm_tmul
  given: (s : S) (a : A)
  proof: rfl

中文:
引理 commRight_symm_tmul
  条件: (s : S) (a : A)
  证明: rfl
-/
lemma commRight_symm_tmul (s : S) (a : A) :
    (commRight R S A).symm (a otimesₜ[R] s) = s otimesₜ a := rfl

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias Algebra.TensorProduct.commRight_symm_tmul := commRight_symm_tmul

end

end

section

variable [CommSemiring T] [Algebra R T] [Algebra S T]
    [Algebra T A] [IsScalarTower R T A] [IsScalarTower S T A]

variable (T C D) in
/--
Definition of `assoc` / `assoc` 的定义

English:
definition assoc
  signature: : (A otimes[S] C) otimes[R] D ≃ₐ[T] A otimes[S] (C otimes[R] D)
  body: AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

中文:
定义 assoc
  签名: : (A otimes[S] C) otimes[R] D ≃ₐ[T] A otimes[S] (C otimes[R] D)
  定义体: AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)
-/
protected def assoc : (A otimes[S] C) otimes[R] D ≃ₐ[T] A otimes[S] (C otimes[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

variable (T C D) in
/--
theorem `assoc_toLinearEquiv` / 定理 `assoc_toLinearEquiv`

English:
theorem assoc_toLinearEquiv
  proof: rfl

@[simp]

中文:
定理 assoc_toLinearEquiv
  证明: rfl

@[simp]

Depends on / 依赖: dist_mkOfCompact, dist_pair_smul, dist_smul_pair, mkOfCompact
-/
@[simp] theorem assoc_toLinearEquiv :
    (TensorProduct.assoc R S T A C D).toLinearEquiv = AlgebraTensorModule.assoc R S T A C D := rfl

@[simp]
/--
theorem `assoc_tmul` / 定理 `assoc_tmul`

English:
theorem assoc_tmul
  given: (a : A) (b : C) (c : D)
  proof: rfl

@[simp]

中文:
定理 assoc_tmul
  条件: (a : A) (b : C) (c : D)
  证明: rfl

@[simp]
-/
theorem assoc_tmul (a : A) (b : C) (c : D) :
    TensorProduct.assoc R S T A C D ((a otimesₜ b) otimesₜ c) = a otimesₜ (b otimesₜ c) := rfl

@[simp]
/--
theorem `assoc_symm_tmul` / 定理 `assoc_symm_tmul`

English:
theorem assoc_symm_tmul
  given: (a : A) (b : C) (c : D)
  proof: rfl

中文:
定理 assoc_symm_tmul
  条件: (a : A) (b : C) (c : D)
  证明: rfl
-/
theorem assoc_symm_tmul (a : A) (b : C) (c : D) :
    (TensorProduct.assoc R S T A C D).symm (a otimesₜ (b otimesₜ c)) = (a otimesₜ b) otimesₜ c := rfl

end

section

variable (T A B : Type*) [CommSemiring T] [CommSemiring A] [CommSemiring B]
  [Algebra R T] [Algebra R A] [Algebra R B] [Algebra T A] [IsScalarTower R T A] [Algebra S A]
  [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A]

/--
Definition of `cancelBaseChange` / `cancelBaseChange` 的定义

English:
definition cancelBaseChange
  signature: : A otimes[S] (S otimes[R] B) ≃ₐ[T] A otimes[R] B
  body: AlgEquiv.symm AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
(by simp [Algebra.TensorProduct.one_def])
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp)

@[simp]

中文:
定义 cancelBaseChange
  签名: : A otimes[S] (S otimes[R] B) ≃ₐ[T] A otimes[R] B
  定义体: AlgEquiv.symm AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
(by simp [Algebra.TensorProduct.one_def])
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, AlgEquiv.symm, Algebra, Algebra.TensorProduct.one_def, AlgebraTensorModule, LinearMap, LinearMap.map_mul_of_map_mul_tmul, TensorProduct, TensorProduct.AlgebraTensorModule.cancelBaseChange, cancelBaseChange, map_mul_of_map_mul_tmul, ofLinearEquiv, one_def
-/
def cancelBaseChange : A otimes[S] (S otimes[R] B) ≃ₐ[T] A otimes[R] B :=
AlgEquiv.symm AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
(by simp [Algebra.TensorProduct.one_def])
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp)

@[simp]
/--
lemma `cancelBaseChange_tmul` / 引理 `cancelBaseChange_tmul`

English:
lemma cancelBaseChange_tmul
  given: (a : A) (s : S) (b : B)
  proof: TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]

中文:
引理 cancelBaseChange_tmul
  条件: (a : A) (s : S) (b : B)
  证明: TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]

Depends on / 依赖: AlgebraTensorModule, TensorProduct, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, cancelBaseChange_tmul
-/
lemma cancelBaseChange_tmul (a : A) (s : S) (b : B) :
    Algebra.TensorProduct.cancelBaseChange R S T A B (a otimesₜ (s otimesₜ b)) = (s • a) otimesₜ b :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]
/--
lemma `cancelBaseChange_symm_tmul` / 引理 `cancelBaseChange_symm_tmul`

English:
lemma cancelBaseChange_symm_tmul
  given: (a : A) (b : B)
  proof: TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b

中文:
引理 cancelBaseChange_symm_tmul
  条件: (a : A) (b : B)
  证明: TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b

Depends on / 依赖: AlgebraTensorModule, TensorProduct, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, cancelBaseChange_symm_tmul
-/
lemma cancelBaseChange_symm_tmul (a : A) (b : B) :
    (Algebra.TensorProduct.cancelBaseChange R S T A B).symm (a otimesₜ b) = a otimesₜ (1 otimesₜ b) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b

end

variable {R S A}

section mapRingHom
variable {R S T R' S' T' : Type*}
  [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra R T]
  [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra R' T']
  (fR : R ->+* R') (fS : S ->+* S') (fT : T ->+* T')
  (HS : fS.comp (algebraMap _ _) = (algebraMap _ _).comp fR)
  (HT : fT.comp (algebraMap _ _) = (algebraMap _ _).comp fR)

/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: : S otimes[R] T ->+* S' otimes[R'] T'
  body: letI := fR.toAlgebra
  letI := ((algebraMap R' S').comp fR).toAlgebra
  letI := ((algebraMap R' T').comp fR).toAlgebra
  letI := fS.toAlgebra
  letI := fT.toAlgebra
  letI : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R R' T' := .of_algebraMap_eq' rfl
  letI : IsScalarTowe

中文:
定义 mapRingHom
  签名: : S otimes[R] T ->+* S' otimes[R'] T'
  定义体: letI := fR.toAlgebra
  letI := ((algebraMap R' S').comp fR).toAlgebra
  letI := ((algebraMap R' T').comp fR).toAlgebra
  letI := fS.toAlgebra
  letI := fT.toAlgebra
  letI : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R R' T' := .of_algebraMap_eq' rfl
  letI : IsScalarTowe

Depends on / 依赖: HS.symm, HT.symm, IsScalarTower, IsScalarTower.toAlgHom, algebraMap, fR.toAlgebra, fS.toAlgebra, fT.toAlgebra, includeLeft, includeLeft.comp, includeRight, includeRight.restrictScalars, of_algebraMap_eq, restrictScalars, toAlgHom, toAlgebra
-/
def mapRingHom : S otimes[R] T ->+* S' otimes[R'] T' :=
  letI := fR.toAlgebra
  letI := ((algebraMap R' S').comp fR).toAlgebra
  letI := ((algebraMap R' T').comp fR).toAlgebra
  letI := fS.toAlgebra
  letI := fT.toAlgebra
  letI : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R R' T' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R S S' := .of_algebraMap_eq' HS.symm
  letI : IsScalarTower R T T' := .of_algebraMap_eq' HT.symm
  (lift (R := R) (S := R) (includeLeft.comp (IsScalarTower.toAlgHom R S S'))
    ((includeRight.restrictScalars R).comp (IsScalarTower.toAlgHom R T T'))
    (fun _ _ => .all _ _)).toRingHom

@[simp]
/--
lemma `mapRingHom_tmul` / 引理 `mapRingHom_tmul`

English:
lemma mapRingHom_tmul
  given: (s : S) (t : T)
  statement: mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
  proof: by
  trans (fS s * 1 : S') otimesₜ[R'] (1 * fT t : T')
  · dsimp [mapRingHom, lift_tmul, algebraMap]
  · simp

@[simp]

中文:
引理 mapRingHom_tmul
  条件: (s : S) (t : T)
  结论: mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
  证明: by
  trans (fS s * 1 : S') otimesₜ[R'] (1 * fT t : T')
  · dsimp [mapRingHom, lift_tmul, algebraMap]
  · simp

@[simp]

Depends on / 依赖: algebraMap, lift_tmul, mapRingHom
-/
lemma mapRingHom_tmul (s : S) (t : T) : mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t := by
  trans (fS s * 1 : S') otimesₜ[R'] (1 * fT t : T')
  · dsimp [mapRingHom, lift_tmul, algebraMap]
  · simp

@[simp]
/--
lemma `mapRingHom_comp_includeLeftRingHom` / 引理 `mapRingHom_comp_includeLeftRingHom`

English:
lemma mapRingHom_comp_includeLeftRingHom
  proof: by
  ext; simp

@[simp]

中文:
引理 mapRingHom_comp_includeLeftRingHom
  证明: by
  ext; simp

@[simp]
-/
lemma mapRingHom_comp_includeLeftRingHom :
    (mapRingHom fR fS fT HS HT).comp (includeLeftRingHom) = includeLeftRingHom.comp fS := by
  ext; simp

@[simp]
/--
lemma `mapRingHom_comp_includeRight` / 引理 `mapRingHom_comp_includeRight`

English:
lemma mapRingHom_comp_includeRight
  proof: by ext; simp

中文:
引理 mapRingHom_comp_includeRight
  证明: by ext; simp
-/
lemma mapRingHom_comp_includeRight :
    (mapRingHom fR fS fT HS HT).comp (RingHomClass.toRingHom includeRight) =
      (RingHomClass.toRingHom includeRight).comp fT := by ext; simp

end mapRingHom

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  body: algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])

中文:
定义 map
  签名: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  定义体: algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, algHomOfLinearMapTensorProduct, f.toLinearMap, g.toLinearMap, one_def, toLinearMap
-/
def map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : A otimes[R] B ->ₐ[S] C otimes[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])

/--
lemma `toLinearMap_map` / 引理 `toLinearMap_map`

English:
lemma toLinearMap_map
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_map
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  证明: rfl

@[simp]
-/
@[simp] lemma toLinearMap_map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) :
    (map f g).toLinearMap = TensorProduct.AlgebraTensorModule.map f.toLinearMap g.toLinearMap := rfl

@[simp]
/--
theorem `map_tmul` / 定理 `map_tmul`

English:
theorem map_tmul
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) (a : A) (b : B)
  statement: map f g (a otimesₜ b) = f a otimesₜ g b
  proof: rfl

@[simp]

中文:
定理 map_tmul
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) (a : A) (b : B)
  结论: map f g (a otimesₜ b) = f a otimesₜ g b
  证明: rfl

@[simp]
-/
theorem map_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) (a : A) (b : B) : map f g (a otimesₜ b) = f a otimesₜ g b :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (.id S A) (.id R B) = .id S _
  proof: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

中文:
定理 map_id
  结论: map (.id S A) (.id R B) = .id S _
  证明: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem map_id : map (.id S A) (.id R B) = .id S _ :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  proof: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

中文:
定理 map_comp
  证明: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem map_comp
    (f₂ : C ->ₐ[S] E) (f₁ : A ->ₐ[S] C) (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

/--
lemma `map_id_comp` / 引理 `map_id_comp`

English:
lemma map_id_comp
  given: (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D)
  proof: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

中文:
引理 map_id_comp
  条件: (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D)
  证明: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

Depends on / 依赖: AlgHom, AlgHom.ext
-/
lemma map_id_comp (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D) :
    map (AlgHom.id S A) (g₂.comp g₁) = (map (AlgHom.id S A) g₂).comp (map (AlgHom.id S A) g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

/--
lemma `map_comp_id` / 引理 `map_comp_id`

English:
lemma map_comp_id
  proof: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]

中文:
引理 map_comp_id
  证明: ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext
-/
lemma map_comp_id
    (f₂ : C ->ₐ[S] E) (f₁ : A ->ₐ[S] C) :
    map (f₂.comp f₁) (AlgHom.id R E) = (map f₂ (AlgHom.id R E)).comp (map f₁ (AlgHom.id R E)) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]
/--
theorem `map_comp_includeLeft` / 定理 `map_comp_includeLeft`

English:
theorem map_comp_includeLeft
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  proof: AlgHom.ext by simp

中文:
定理 map_comp_includeLeft
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  证明: AlgHom.ext by simp

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem map_comp_includeLeft (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) :
    (map f g).comp includeLeft = includeLeft.comp f :=
AlgHom.ext by simp

/--
lemma `map_comp_includeLeftRingHom` / 引理 `map_comp_includeLeftRingHom`

English:
lemma map_comp_includeLeftRingHom
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  proof: by ext; simp

@[simp]

中文:
引理 map_comp_includeLeftRingHom
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  证明: by ext; simp

@[simp]
-/
@[simp] lemma map_comp_includeLeftRingHom (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) :
    (map f g : A otimes[R] B ->+* C otimes[R] D).comp includeLeftRingHom =
      includeLeftRingHom.comp (f : A ->+* C) := by ext; simp

@[simp]
/--
theorem `map_restrictScalars_comp_includeRight` / 定理 `map_restrictScalars_comp_includeRight`

English:
theorem map_restrictScalars_comp_includeRight
  given: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  proof: AlgHom.ext by simp

@[simp]

中文:
定理 map_restrictScalars_comp_includeRight
  条件: (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)
  证明: AlgHom.ext by simp

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem map_restrictScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) :
    ((map f g).restrictScalars R).comp includeRight = includeRight.comp g :=
AlgHom.ext by simp

@[simp]
/--
theorem `map_comp_includeRight` / 定理 `map_comp_includeRight`

English:
theorem map_comp_includeRight
  given: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D)
  proof: map_restrictScalars_comp_includeRight f g

中文:
定理 map_comp_includeRight
  条件: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D)
  证明: map_restrictScalars_comp_includeRight f g

Depends on / 依赖: map_restrictScalars_comp_includeRight
-/
theorem map_comp_includeRight (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) :
    (map f g).comp includeRight = includeRight.comp g :=
  map_restrictScalars_comp_includeRight f g

/--
theorem `map_range` / 定理 `map_range`

English:
theorem map_range
  given: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D)
  proof: by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul]; rw [← mul_one (f a)]; rw [← one_mul (g b)]; rw [← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [

中文:
定理 map_range
  条件: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D)
  证明: by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul]; rw [← mul_one (f a)]; rw [← one_mul (g b)]; rw [← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [

Depends on / 依赖: AlgHom, AlgHom.mem_range_self, AlgHom.range_comp_le_range, Compacts, TopologicalSpace, TopologicalSpace.Compacts.instCompactSpaceSubtypeMem, adjoin_image, adjoin_le_iff, adjoin_tmul_eq_top, instCompactSpaceSubtypeMem, le_antisymm, map_comp_includeLeft, map_comp_includeRight, map_tmul, map_top, mem_range_self, mul_mem_sup, mul_one, one_mul, range_comp_le_range
-/
theorem map_range (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).range := by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul]; rw [← mul_one (f a)]; rw [← one_mul (g b)]; rw [← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [← map_comp_includeLeft f g, ← map_comp_includeRight f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)

/--
lemma `comm_comp_map` / 引理 `comm_comp_map`

English:
lemma comm_comp_map
  given: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D)
  proof: by
  ext <;> rfl

中文:
引理 comm_comp_map
  条件: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D)
  证明: by
  ext <;> rfl
-/
lemma comm_comp_map (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) :
    (TensorProduct.comm R C D : C otimes[R] D ->ₐ[R] D otimes[R] C).comp (Algebra.TensorProduct.map f g) =
    (Algebra.TensorProduct.map g f).comp (TensorProduct.comm R A B).toAlgHom := by
  ext <;> rfl

/--
lemma `comm_comp_map_apply` / 引理 `comm_comp_map_apply`

English:
lemma comm_comp_map_apply
  given: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) (x)
  proof: congr($(comm_comp_map f g) x)

中文:
引理 comm_comp_map_apply
  条件: (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) (x)
  证明: congr($(comm_comp_map f g) x)

Depends on / 依赖: comm_comp_map
-/
lemma comm_comp_map_apply (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) (x) :
    TensorProduct.comm R C D (Algebra.TensorProduct.map f g x) =
    (Algebra.TensorProduct.map g f) (TensorProduct.comm R A B x) :=
  congr($(comm_comp_map f g) x)

variable (A) in
/--
Definition of `lTensor` / `lTensor` 的定义

English:
abbreviation lTensor
  signature: (g : B ->ₐ[R] D)
  body: map (.id S A) g

中文:
缩写 lTensor
  签名: (g : B ->ₐ[R] D)
  定义体: map (.id S A) g
-/
abbrev lTensor (g : B ->ₐ[R] D) : (A otimes[R] B) ->ₐ[S] (A otimes[R] D) := map (.id S A) g

variable (B) in
/--
Definition of `rTensor` / `rTensor` 的定义

English:
abbreviation rTensor
  signature: (f : A ->ₐ[S] C)
  body: map f (.id R B)

中文:
缩写 rTensor
  签名: (f : A ->ₐ[S] C)
  定义体: map f (.id R B)
-/
abbrev rTensor (f : A ->ₐ[S] C) : A otimes[R] B ->ₐ[S] C otimes[R] B := map f (.id R B)

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D)
  body: AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)

中文:
定义 congr
  签名: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D)
  定义体: AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, f.symm, g.symm, ofAlgHom
-/
def congr (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : A otimes[R] B ≃ₐ[S] C otimes[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)

/--
theorem `congr_toLinearEquiv` / 定理 `congr_toLinearEquiv`

English:
theorem congr_toLinearEquiv
  given: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D)
  proof: rfl

@[simp]

中文:
定理 congr_toLinearEquiv
  条件: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D)
  证明: rfl

@[simp]
-/
@[simp] theorem congr_toLinearEquiv (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) :
    (Algebra.TensorProduct.congr f g).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr f.toLinearEquiv g.toLinearEquiv := rfl

@[simp]
/--
theorem `congr_apply` / 定理 `congr_apply`

English:
theorem congr_apply
  given: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x)
  proof: rfl

@[simp]

中文:
定理 congr_apply
  条件: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x)
  证明: rfl

@[simp]
-/
theorem congr_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    congr f g x = (map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D)) x :=
  rfl

@[simp]
/--
theorem `congr_symm_apply` / 定理 `congr_symm_apply`

English:
theorem congr_symm_apply
  given: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x)
  proof: rfl

@[simp]

中文:
定理 congr_symm_apply
  条件: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x)
  证明: rfl

@[simp]
-/
theorem congr_symm_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : C ->ₐ[S] A) (g.symm : D ->ₐ[R] B)) x :=
  rfl

@[simp]
/--
theorem `congr_refl` / 定理 `congr_refl`

English:
theorem congr_refl
  statement: congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl
  proof: AlgEquiv.coe_toAlgHom_injective map_id

中文:
定理 congr_refl
  结论: congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl
  证明: AlgEquiv.coe_toAlgHom_injective map_id

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom_injective, coe_toAlgHom_injective, map_id
-/
theorem congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl :=
AlgEquiv.coe_toAlgHom_injective map_id

/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  proof: AlgEquiv.coe_toAlgHom_injective map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom

中文:
定理 congr_trans
  证明: AlgEquiv.coe_toAlgHom_injective map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom_injective, coe_toAlgHom_injective, map_comp, toAlgHom
-/
theorem congr_trans
    (f₁ : A ≃ₐ[S] C) (f₂ : C ≃ₐ[S] E) (g₁ : B ≃ₐ[R] D) (g₂ : D ≃ₐ[R] F) :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
AlgEquiv.coe_toAlgHom_injective map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom

/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D)
  statement: congr f.symm g.symm = (congr f g).symm
  proof: rfl

中文:
定理 congr_symm
  条件: (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D)
  结论: congr f.symm g.symm = (congr f g).symm
  证明: rfl
-/
theorem congr_symm (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : congr f.symm g.symm = (congr f g).symm := rfl

variable (R A B C) in
/--
Definition of `leftComm` / `leftComm` 的定义

English:
definition leftComm
  signature: : A otimes[R] (B otimes[R] C) ≃ₐ[R] B otimes[R] (A otimes[R] C)
  body: (Algebra.TensorProduct.assoc R R R A B C).symm.trans
(congr (Algebra.TensorProduct.comm R A B) .refl).trans TensorProduct.assoc R R R B A C

@[simp]

中文:
定义 leftComm
  签名: : A otimes[R] (B otimes[R] C) ≃ₐ[R] B otimes[R] (A otimes[R] C)
  定义体: (Algebra.TensorProduct.assoc R R R A B C).symm.trans
(congr (Algebra.TensorProduct.comm R A B) .refl).trans TensorProduct.assoc R R R B A C

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.assoc, Algebra.TensorProduct.comm, TensorProduct, TensorProduct.assoc, symm.trans
-/
def leftComm : A otimes[R] (B otimes[R] C) ≃ₐ[R] B otimes[R] (A otimes[R] C) :=
(Algebra.TensorProduct.assoc R R R A B C).symm.trans
(congr (Algebra.TensorProduct.comm R A B) .refl).trans TensorProduct.assoc R R R B A C

@[simp]
/--
theorem `leftComm_tmul` / 定理 `leftComm_tmul`

English:
theorem leftComm_tmul
  given: (m : A) (n : B) (p : C)
  proof: rfl

@[simp]

中文:
定理 leftComm_tmul
  条件: (m : A) (n : B) (p : C)
  证明: rfl

@[simp]
-/
theorem leftComm_tmul (m : A) (n : B) (p : C) :
    leftComm R A B C (m otimesₜ (n otimesₜ p)) = n otimesₜ (m otimesₜ p) :=
  rfl

@[simp]
/--
theorem `leftComm_symm_tmul` / 定理 `leftComm_symm_tmul`

English:
theorem leftComm_symm_tmul
  given: (m : A) (n : B) (p : C)
  proof: rfl

@[simp]

中文:
定理 leftComm_symm_tmul
  条件: (m : A) (n : B) (p : C)
  证明: rfl

@[simp]
-/
theorem leftComm_symm_tmul (m : A) (n : B) (p : C) :
    (leftComm R A B C).symm (n otimesₜ (m otimesₜ p)) = m otimesₜ (n otimesₜ p) :=
  rfl

@[simp]
/--
theorem `leftComm_toLinearEquiv` / 定理 `leftComm_toLinearEquiv`

English:
theorem leftComm_toLinearEquiv
  statement: ↑(leftComm R A B C) = _root_.TensorProduct.leftComm R A B C
  proof: LinearEquiv.toLinearMap_injective (by ext; rfl)

中文:
定理 leftComm_toLinearEquiv
  结论: ↑(leftComm R A B C) = _root_.张量积.leftComm R A B C
  证明: LinearEquiv.toLinearMap_injective (by ext; rfl)

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, toLinearMap_injective
-/
theorem leftComm_toLinearEquiv : ↑(leftComm R A B C) = _root_.TensorProduct.leftComm R A B C :=
  LinearEquiv.toLinearMap_injective (by ext; rfl)

variable [CommSemiring T] [Algebra R T] [Algebra T A] [IsScalarTower R T A] [SMulCommClass S T A]
  [Algebra S T] [IsScalarTower S T A] [CommSemiring R'] [Algebra R R'] [Algebra R' T] [Algebra R' A]
  [Algebra R' B] [IsScalarTower R R' A] [SMulCommClass S R' A] [SMulCommClass R' S A]
  [IsScalarTower R' T A] [IsScalarTower R R' B]

variable (R R' S T A B C D) in
/--
Definition of `tensorTensorTensorComm` / `tensorTensorTensorComm` 的定义

English:
definition tensorTensorTensorComm
  signature: : A otimes[R'] B otimes[S] (C otimes[R] D) ≃ₐ[T] A otimes[S] C otimes[R'] (B otimes[R] D)
  body: AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D)
    rfl (LinearMap.map_mul_iff _ |>.mpr <| by ext; simp)

@[simp]

中文:
定义 tensorTensorTensorComm
  签名: : A otimes[R'] B otimes[S] (C otimes[R] D) ≃ₐ[T] A otimes[S] C otimes[R'] (B otimes[R] D)
  定义体: AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D)
    rfl (LinearMap.map_mul_iff _ |>.mpr <| by ext; simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, AlgebraTensorModule, LinearMap, LinearMap.map_mul_iff, TensorProduct, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm, map_mul_iff, ofLinearEquiv, tensorTensorTensorComm
-/
def tensorTensorTensorComm : A otimes[R'] B otimes[S] (C otimes[R] D) ≃ₐ[T] A otimes[S] C otimes[R'] (B otimes[R] D) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D)
    rfl (LinearMap.map_mul_iff _ |>.mpr <| by ext; simp)

@[simp]
/--
theorem `tensorTensorTensorComm_tmul` / 定理 `tensorTensorTensorComm_tmul`

English:
theorem tensorTensorTensorComm_tmul
  given: (m : A) (n : B) (p : C) (q : D)
  proof: rfl

@[simp]

中文:
定理 tensorTensorTensorComm_tmul
  条件: (m : A) (n : B) (p : C) (q : D)
  证明: rfl

@[simp]
-/
theorem tensorTensorTensorComm_tmul (m : A) (n : B) (p : C) (q : D) :
    tensorTensorTensorComm R R' S T A B C D (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ p otimesₜ (n otimesₜ q) :=
  rfl

@[simp]
/--
theorem `tensorTensorTensorComm_symm_tmul` / 定理 `tensorTensorTensorComm_symm_tmul`

English:
theorem tensorTensorTensorComm_symm_tmul
  given: (m : A) (n : C) (p : B) (q : D)
  proof: rfl

中文:
定理 tensorTensorTensorComm_symm_tmul
  条件: (m : A) (n : C) (p : B) (q : D)
  证明: rfl
-/
theorem tensorTensorTensorComm_symm_tmul (m : A) (n : C) (p : B) (q : D) :
    (tensorTensorTensorComm R R' S T A B C D).symm (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ p otimesₜ (n otimesₜ q) :=
  rfl

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
    (tensorTensorTensorComm R R' S T A B C D).symm = tensorTensorTensorComm R S R' T A C B D := rfl

/--
theorem `tensorTensorTensorComm_toLinearEquiv` / 定理 `tensorTensorTensorComm_toLinearEquiv`

English:
theorem tensorTensorTensorComm_toLinearEquiv
  proof: rfl

@[simp]

中文:
定理 tensorTensorTensorComm_toLinearEquiv
  证明: rfl

@[simp]
-/
theorem tensorTensorTensorComm_toLinearEquiv :
    (tensorTensorTensorComm R R' S T A B C D).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D := rfl

@[simp]
/--
theorem `toLinearEquiv_tensorTensorTensorComm` / 定理 `toLinearEquiv_tensorTensorTensorComm`

English:
theorem toLinearEquiv_tensorTensorTensorComm
  proof: rfl

中文:
定理 toLinearEquiv_tensorTensorTensorComm
  证明: rfl
-/
theorem toLinearEquiv_tensorTensorTensorComm :
    (tensorTensorTensorComm R R R R A B C D).toLinearEquiv =
      _root_.TensorProduct.tensorTensorTensorComm R A B C D := rfl

/--
lemma `map_bijective` / 引理 `map_bijective`

English:
lemma map_bijective
  statement: {f : A ->ₐ[R] B} {g : C ->ₐ[R] D}
  proof: _root_.TensorProduct.map_bijective hf hg

中文:
引理 map_bijective
  结论: {f : A ->ₐ[R] B} {g : C ->ₐ[R] D}
  证明: _root_.TensorProduct.map_bijective hf hg

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.map_bijective, map_bijective
-/
lemma map_bijective {f : A ->ₐ[R] B} {g : C ->ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  _root_.TensorProduct.map_bijective hf hg

/--
lemma `includeLeft_bijective` / 引理 `includeLeft_bijective`

English:
lemma includeLeft_bijective
  given: (h : Function.Bijective (algebraMap R B))
  proof: by
  have : (includeLeft : A ->ₐ[S] A otimes[R] B).comp (TensorProduct.rid R S A).toAlgHom =
      map (.id S A) (Algebra.ofId R B) := by ext; simp
  rw [← Function.Bijective.of_comp_iff _ (TensorProduct.rid R S A).bijective]
  convert_to Function.Bijective (map (.id R A) (Algebra.ofId R B))
  · exa

中文:
引理 includeLeft_bijective
  条件: (h : 函数.双射 (algebraMap R B))
  证明: by
  have : (includeLeft : A ->ₐ[S] A otimes[R] B).comp (TensorProduct.rid R S A).toAlgHom =
      map (.id S A) (Algebra.ofId R B) := by ext; simp
  rw [← Function.Bijective.of_comp_iff _ (TensorProduct.rid R S A).bijective]
  convert_to Function.Bijective (map (.id R A) (Algebra.ofId R B))
  · exa

Depends on / 依赖: Algebra, Algebra.TensorProduct.map_bijective, Algebra.ofId, Bijective, DFunLike, DFunLike.coe_fn_eq.mpr, Function, Function.Bijective, Function.Bijective.of_comp_iff, Function.bijective_id, TensorProduct, TensorProduct.rid, bijective, bijective_id, coe_fn_eq, convert_to, includeLeft, map_bijective, of_comp_iff, otimes
-/
lemma includeLeft_bijective (h : Function.Bijective (algebraMap R B)) :
    Function.Bijective (includeLeft : A ->ₐ[S] A otimes[R] B) := by
  have : (includeLeft : A ->ₐ[S] A otimes[R] B).comp (TensorProduct.rid R S A).toAlgHom =
      map (.id S A) (Algebra.ofId R B) := by ext; simp
  rw [← Function.Bijective.of_comp_iff _ (TensorProduct.rid R S A).bijective]
  convert_to Function.Bijective (map (.id R A) (Algebra.ofId R B))
  · exact DFunLike.coe_fn_eq.mpr this
  · exact Algebra.TensorProduct.map_bijective Function.bijective_id h

/--
lemma `includeRight_bijective` / 引理 `includeRight_bijective`

English:
lemma includeRight_bijective
  given: (h : Function.Bijective (algebraMap R A))
  proof: by
  rw [← Function.Bijective.of_comp_iff' (TensorProduct.comm R A B).bijective]
  exact Algebra.TensorProduct.includeLeft_bijective (S := R) h

中文:
引理 includeRight_bijective
  条件: (h : 函数.双射 (algebraMap R A))
  证明: by
  rw [← Function.Bijective.of_comp_iff' (TensorProduct.comm R A B).bijective]
  exact Algebra.TensorProduct.includeLeft_bijective (S := R) h

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft_bijective, Bijective, Function, Function.Bijective.of_comp_iff, TensorProduct, TensorProduct.comm, bijective, includeLeft_bijective, of_comp_iff
-/
lemma includeRight_bijective (h : Function.Bijective (algebraMap R A)) :
    Function.Bijective (includeRight : B ->ₐ[R] A otimes[R] B) := by
  rw [← Function.Bijective.of_comp_iff' (TensorProduct.comm R A B).bijective]
  exact Algebra.TensorProduct.includeLeft_bijective (S := R) h

end

end Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/--
Definition of `productLeftAlgHom` / `productLeftAlgHom` 的定义

English:
abbreviation productLeftAlgHom
  signature: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C)
  body: lift f g (fun _ _ => Commute.all _ _)

中文:
缩写 productLeftAlgHom
  签名: (f : A ->ₐ[S] C) (g : B ->ₐ[R] C)
  定义体: lift f g (fun _ _ => Commute.all _ _)

Depends on / 依赖: Commute, Commute.all
-/
abbrev productLeftAlgHom (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) : A otimes[R] B ->ₐ[S] C :=
  lift f g (fun _ _ => Commute.all _ _)

/--
lemma `tmul_one_eq_one_tmul` / 引理 `tmul_one_eq_one_tmul`

English:
lemma tmul_one_eq_one_tmul
  given: (r : R)
  statement: algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]

中文:
引理 tmul_one_eq_one_tmul
  条件: (r : R)
  结论: algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, smul_tmul
-/
lemma tmul_one_eq_one_tmul (r : R) : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r := by
  rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]

end

section

variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]
variable [Algebra R A] [Algebra R B] [Algebra R S]
variable (f : A ->ₐ[R] S) (g : B ->ₐ[R] S)
variable (R)

/--
Definition of `lmul''` / `lmul''` 的定义

English:
definition lmul''
  signature: : S otimes[R] S ->ₐ[S] S
  body: algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x => x.induction_on (by simp)
        (fun _ _ => by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy => by simp_all [mul_add] }
(fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) by simp

中文:
定义 lmul''
  签名: : S otimes[R] S ->ₐ[S] S
  定义体: algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x => x.induction_on (by simp)
        (fun _ _ => by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy => by simp_all [mul_add] }
(fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) by simp

Depends on / 依赖: LinearMap, LinearMap.mul, TensorProduct, TensorProduct.smul_tmul, algHomOfLinearMapTensorProduct, induction_on, map_smul, mul_add, mul_assoc, mul_mul_mul_comm, smul_tmul, x.induction_on
-/
def lmul'' : S otimes[R] S ->ₐ[S] S :=
  algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x => x.induction_on (by simp)
        (fun _ _ => by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy => by simp_all [mul_add] }
(fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) by simp

/--
theorem `lmul''_eq_lid_comp_mapOfCompatibleSMul` / 定理 `lmul''_eq_lid_comp_mapOfCompatibleSMul`

English:
theorem lmul''_eq_lid_comp_mapOfCompatibleSMul
  proof: by
  ext; rfl

中文:
定理 lmul''_eq_lid_comp_mapOfCompatibleSMul
  证明: by
  ext; rfl
-/
theorem lmul''_eq_lid_comp_mapOfCompatibleSMul :
    lmul'' R = (TensorProduct.lid S S).toAlgHom.comp (mapOfCompatibleSMul ..) := by
  ext; rfl

/--
Definition of `lmul'` / `lmul'` 的定义

English:
definition lmul'
  signature: : S otimes[R] S ->ₐ[R] S
  body: (lmul'' R).restrictScalars R

中文:
定义 lmul'
  签名: : S otimes[R] S ->ₐ[R] S
  定义体: (lmul'' R).restrictScalars R

Depends on / 依赖: restrictScalars
-/
def lmul' : S otimes[R] S ->ₐ[R] S := (lmul'' R).restrictScalars R

variable {R}

/--
theorem `lmul'_toLinearMap` / 定理 `lmul'_toLinearMap`

English:
theorem lmul'_toLinearMap
  statement: (lmul' R : _ ->ₐ[R] S).toLinearMap = LinearMap.mul' R S
  proof: rfl

@[simp]

中文:
定理 lmul'_toLinearMap
  结论: (lmul' R : _ ->ₐ[R] S).toLinearMap = 线性映射.mul' R S
  证明: rfl

@[simp]
-/
theorem lmul'_toLinearMap : (lmul' R : _ ->ₐ[R] S).toLinearMap = LinearMap.mul' R S :=
  rfl

@[simp]
/--
theorem `lmul'_apply_tmul` / 定理 `lmul'_apply_tmul`

English:
theorem lmul'_apply_tmul
  given: (a b : S)
  statement: lmul' (S := S) R (a otimesₜ[R] b) = a * b
  proof: rfl

@[simp]

中文:
定理 lmul'_apply_tmul
  条件: (a b : S)
  结论: lmul' (S := S) R (a otimesₜ[R] b) = a * b
  证明: rfl

@[simp]
-/
theorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a otimesₜ[R] b) = a * b :=
  rfl

@[simp]
/--
theorem `lmul'_comp_includeLeft` / 定理 `lmul'_comp_includeLeft`

English:
theorem lmul'_comp_includeLeft
  statement: (lmul' R : _ ->ₐ[R] S).comp includeLeft = AlgHom.id R S
  proof: AlgHom.ext mul_one

@[simp]

中文:
定理 lmul'_comp_includeLeft
  结论: (lmul' R : _ ->ₐ[R] S).comp includeLeft = 代数态射.id R S
  证明: AlgHom.ext mul_one

@[simp]
-/
theorem lmul'_comp_includeLeft : (lmul' R : _ ->ₐ[R] S).comp includeLeft = AlgHom.id R S :=
AlgHom.ext mul_one

@[simp]
/--
theorem `lmul'_comp_includeRight` / 定理 `lmul'_comp_includeRight`

English:
theorem lmul'_comp_includeRight
  statement: (lmul' R : _ ->ₐ[R] S).comp includeRight = AlgHom.id R S
  proof: AlgHom.ext one_mul

中文:
定理 lmul'_comp_includeRight
  结论: (lmul' R : _ ->ₐ[R] S).comp includeRight = 代数态射.id R S
  证明: AlgHom.ext one_mul
-/
theorem lmul'_comp_includeRight : (lmul' R : _ ->ₐ[R] S).comp includeRight = AlgHom.id R S :=
AlgHom.ext one_mul

/--
lemma `lmul'_comp_map` / 引理 `lmul'_comp_map`

English:
lemma lmul'_comp_map
  given: (f : A ->ₐ[R] S) (g : B ->ₐ[R] S)
  proof: by ext <;> rfl

中文:
引理 lmul'_comp_map
  条件: (f : A ->ₐ[R] S) (g : B ->ₐ[R] S)
  证明: by ext <;> rfl
-/
lemma lmul'_comp_map (f : A ->ₐ[R] S) (g : B ->ₐ[R] S) :
    (lmul' R).comp (map f g) = lift f g (fun _ _ => .all _ _) := by ext <;> rfl

variable (R S) in
/--
Definition of `lmulEquiv` / `lmulEquiv` 的定义

English:
definition lmulEquiv
  signature: [CompatibleSMul R S S S]
  body: .ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft AlgHom.ext fun x => x.induction_on
    (by simp) (fun x y => show (x * y) otimesₜ[R] 1 = x otimesₜ[R] y by
      rw [mul_comm]; rw [← smul_eq_mul]; rw [smul_tmul]; rw [smul_eq_mul]; rw [mul_one])
    fun _ _ hx hy => by simp_all [add_tmul]

中文:
定义 lmulEquiv
  签名: [余mpatibleSMul R S S S]
  定义体: .ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft AlgHom.ext fun x => x.induction_on
    (by simp) (fun x y => show (x * y) otimesₜ[R] 1 = x otimesₜ[R] y by
      rw [mul_comm]; rw [← smul_eq_mul]; rw [smul_tmul]; rw [smul_eq_mul]; rw [mul_one])
    fun _ _ hx hy => by simp_all [add_tmul]

Depends on / 依赖: AlgHom, AlgHom.ext, _comp_includeLeft, add_tmul, includeLeft, induction_on, mul_comm, mul_one, ofAlgHom, smul_eq_mul, smul_tmul, x.induction_on
-/
def lmulEquiv [CompatibleSMul R S S S] : S otimes[R] S ≃ₐ[S] S :=
.ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft AlgHom.ext fun x => x.induction_on
    (by simp) (fun x y => show (x * y) otimesₜ[R] 1 = x otimesₜ[R] y by
      rw [mul_comm]; rw [← smul_eq_mul]; rw [smul_tmul]; rw [smul_eq_mul]; rw [mul_one])
    fun _ _ hx hy => by simp_all [add_tmul]

/--
theorem `lmulEquiv_eq_lidOfCompatibleSMul` / 定理 `lmulEquiv_eq_lidOfCompatibleSMul`

English:
theorem lmulEquiv_eq_lidOfCompatibleSMul
  given: [CompatibleSMul R S S S]
  proof: AlgEquiv.coe_toAlgHom_injective by ext; rfl

中文:
定理 lmulEquiv_eq_lidOfCompatibleSMul
  条件: [余mpatibleSMul R S S S]
  证明: AlgEquiv.coe_toAlgHom_injective by ext; rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom_injective, coe_toAlgHom_injective
-/
theorem lmulEquiv_eq_lidOfCompatibleSMul [CompatibleSMul R S S S] :
    lmulEquiv R S = lidOfCompatibleSMul R S S :=
AlgEquiv.coe_toAlgHom_injective by ext; rfl

/--
Definition of `productMap` / `productMap` 的定义

English:
definition productMap
  signature: : A otimes[R] B ->ₐ[R] S
  body: productLeftAlgHom f g

中文:
定义 productMap
  签名: : A otimes[R] B ->ₐ[R] S
  定义体: productLeftAlgHom f g

Depends on / 依赖: productLeftAlgHom
-/
def productMap : A otimes[R] B ->ₐ[R] S := productLeftAlgHom f g

/--
theorem `productMap_eq_comp_map` / 定理 `productMap_eq_comp_map`

English:
theorem productMap_eq_comp_map
  statement: productMap f g = (lmul' R).comp (TensorProduct.map f g)
  proof: by
  ext <;> rfl

@[simp]

中文:
定理 productMap_eq_comp_map
  结论: productMap f g = (lmul' R).comp (张量积.map f g)
  证明: by
  ext <;> rfl

@[simp]
-/
theorem productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.map f g) := by
  ext <;> rfl

@[simp]
/--
theorem `productMap_apply_tmul` / 定理 `productMap_apply_tmul`

English:
theorem productMap_apply_tmul
  given: (a : A) (b : B)
  statement: productMap f g (a otimesₜ b) = f a * g b
  proof: rfl

中文:
定理 productMap_apply_tmul
  条件: (a : A) (b : B)
  结论: productMap f g (a otimesₜ b) = f a * g b
  证明: rfl
-/
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a otimesₜ b) = f a * g b := rfl

/--
theorem `productMap_left_apply` / 定理 `productMap_left_apply`

English:
theorem productMap_left_apply
  given: (a : A)
  statement: productMap f g (a otimesₜ 1) = f a
  proof: by
  simp

@[simp]

中文:
定理 productMap_left_apply
  条件: (a : A)
  结论: productMap f g (a otimesₜ 1) = f a
  证明: by
  simp

@[simp]
-/
theorem productMap_left_apply (a : A) : productMap f g (a otimesₜ 1) = f a := by
  simp

@[simp]
/--
theorem `productMap_left` / 定理 `productMap_left`

English:
theorem productMap_left
  statement: (productMap f g).comp includeLeft = f
  proof: lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

中文:
定理 productMap_left
  结论: (productMap f g).comp includeLeft = f
  证明: lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

Depends on / 依赖: Commute, Commute.all, lift_comp_includeLeft
-/
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

/--
theorem `productMap_right_apply` / 定理 `productMap_right_apply`

English:
theorem productMap_right_apply
  given: (b : B)
  proof: by simp

@[simp]

中文:
定理 productMap_right_apply
  条件: (b : B)
  证明: by simp

@[simp]
-/
theorem productMap_right_apply (b : B) :
    productMap f g (1 otimesₜ b) = g b := by simp

@[simp]
/--
theorem `productMap_right` / 定理 `productMap_right`

English:
theorem productMap_right
  statement: (productMap f g).comp includeRight = g
  proof: lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

中文:
定理 productMap_right
  结论: (productMap f g).comp includeRight = g
  证明: lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

Depends on / 依赖: Commute, Commute.all, lift_comp_includeRight
-/
theorem productMap_right : (productMap f g).comp includeRight = g :=
  lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

/--
theorem `productMap_range` / 定理 `productMap_range`

English:
theorem productMap_range
  statement: (productMap f g).range = f.range ⊔ g.range
  proof: by
  rw [productMap_eq_comp_map]; rw [AlgHom.range_comp]; rw [map_range]; rw [map_sup]; rw [← AlgHom.range_comp]; rw [← AlgHom.range_comp]; rw [← AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc]; rw [lmul'_comp_includeLeft]; rw [lmul'_comp_includeRight]; rw [AlgHom.id_comp]; rw [AlgHom.id_comp]

中文:
定理 productMap_range
  结论: (productMap f g).range = f.range ⊔ g.range
  证明: by
  rw [productMap_eq_comp_map]; rw [AlgHom.range_comp]; rw [map_range]; rw [map_sup]; rw [← AlgHom.range_comp]; rw [← AlgHom.range_comp]; rw [← AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc]; rw [lmul'_comp_includeLeft]; rw [lmul'_comp_includeRight]; rw [AlgHom.id_comp]; rw [AlgHom.id_comp]

Depends on / 依赖: AlgHom, AlgHom.comp_assoc, AlgHom.id_comp, AlgHom.range_comp, _comp_includeLeft, _comp_includeRight, comp_assoc, id_comp, map_range, map_sup, productMap_eq_comp_map, range_comp
-/
theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap_eq_comp_map]; rw [AlgHom.range_comp]; rw [map_range]; rw [map_sup]; rw [← AlgHom.range_comp]; rw [← AlgHom.range_comp]; rw [← AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc]; rw [lmul'_comp_includeLeft]; rw [lmul'_comp_includeRight]; rw [AlgHom.id_comp]; rw [AlgHom.id_comp]

end

end TensorProduct

end Algebra

namespace LinearMap

variable (R A M N : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Module
open scoped TensorProduct

/-- The natural linear map $A ⊗ \text{Hom}_R(M, N) → \text{Hom}_A (M_A, N_A)$,
where $M_A$ and $N_A$ are the respective modules over $A$ obtained by extension of scalars.

See `LinearMap.tensorProductEnd` for this map specialized to endomorphisms,
and bundled as `A`-algebra homomorphism. -/
@[simps!]
/--
Definition of `tensorProduct` / `tensorProduct` 的定义

English:
definition tensorProduct
  signature: : A otimes[R] (M ->ₗ[R] N) ->ₗ[A] (A otimes[R] M) ->ₗ[A] (A otimes[R] N)
  body: TensorProduct.AlgebraTensorModule.lift
  { toFun := fun a => a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

中文:
定义 tensorProduct
  签名: : A otimes[R] (M ->ₗ[R] N) ->ₗ[A] (A otimes[R] M) ->ₗ[A] (A otimes[R] N)
  定义体: TensorProduct.AlgebraTensorModule.lift
  { toFun := fun a => a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

Depends on / 依赖: AlgebraTensorModule, RingHom, RingHom.id_apply, TensorProduct, TensorProduct.AlgebraTensorModule.lift, add_smul, baseChangeHom, forall_true_iff, id_apply, map_add, map_smul, smul_assoc
-/
def tensorProduct : A otimes[R] (M ->ₗ[R] N) ->ₗ[A] (A otimes[R] M) ->ₗ[A] (A otimes[R] N) :=
TensorProduct.AlgebraTensorModule.lift
  { toFun := fun a => a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

/-- The natural `A`-algebra homomorphism $A ⊗ (\text{End}_R M) → \text{End}_A (A ⊗ M)$,
where `M` is an `R`-module, and `A` an `R`-algebra. -/
@[simps!]
/--
Definition of `tensorProductEnd` / `tensorProductEnd` 的定义

English:
definition tensorProductEnd
  signature: : A otimes[R] (End R M) ->ₐ[A] End A (A otimes[R] M)
  body: Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g => by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, Module.End.mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmu

中文:
定义 tensorProductEnd
  签名: : A otimes[R] (End R M) ->ₐ[A] End A (A otimes[R] M)
  定义体: Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g => by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, Module.End.mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmu

Depends on / 依赖: AddHom, AddHom.coe_mk, Algebra, Algebra.TensorProduct.algHomOfLinearMapTensorProduct, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, AlgebraTensorModule, LinearMap, LinearMap.ext, LinearMap.tensorProduct, Module, Module.End.mul_eq_comp, TensorPro, TensorProduct, TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, algHomOfLinearMapTensorProduct, baseChangeHom_apply, baseChange_comp, coe_mk
-/
def tensorProductEnd : A otimes[R] (End R M) ->ₐ[A] End A (A otimes[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g => by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, Module.End.mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, Module.End.one_eq_id,
        lTensor_id, LinearMap.id_apply])

/--
lemma `mul'_bijective_of_surjective` / 引理 `mul'_bijective_of_surjective`

English:
lemma mul'_bijective_of_surjective
  given: (h : Function.Surjective (algebraMap R A))
  proof: have : TensorProduct.CompatibleSMul R A A A := .of_algebraMap_surjective _ _ h
  (Algebra.TensorProduct.lmulEquiv R A).bijective

中文:
引理 mul'_bijective_of_surjective
  条件: (h : 函数.满射 (algebraMap R A))
  证明: have : TensorProduct.CompatibleSMul R A A A := .of_algebraMap_surjective _ _ h
  (Algebra.TensorProduct.lmulEquiv R A).bijective
-/
lemma mul'_bijective_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Function.Bijective (LinearMap.mul' R A) :=
  have : TensorProduct.CompatibleSMul R A A A := .of_algebraMap_surjective _ _ h
  (Algebra.TensorProduct.lmulEquiv R A).bijective

end LinearMap

namespace Module

variable {R S A M N : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [Module R M] [Module S M] [Module A M] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S M]

/--
Definition of `endTensorEndAlgHom` / `endTensorEndAlgHom` 的定义

English:
definition endTensorEndAlgHom
  signature: : End A M otimes[R] End R N ->ₐ[S] End A (M otimes[R] N)
  body: Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)

中文:
定义 endTensorEndAlgHom
  签名: : End A M otimes[R] End R N ->ₐ[S] End A (M otimes[R] N)
  定义体: Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)

Depends on / 依赖: Algebra, Algebra.TensorProduct.algHomOfLinearMapTensorProduct, AlgebraTensorModule, AlgebraTensorModule.ext, AlgebraTensorModule.homTensorHomMap, TensorProduct, algHomOfLinearMapTensorProduct, homTensorHomMap
-/
def endTensorEndAlgHom : End A M otimes[R] End R N ->ₐ[S] End A (M otimes[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)

/--
theorem `endTensorEndAlgHom_apply` / 定理 `endTensorEndAlgHom_apply`

English:
theorem endTensorEndAlgHom_apply
  given: (f : End A M) (g : End R N)
  proof: rfl

中文:
定理 endTensorEndAlgHom_apply
  条件: (f : End A M) (g : End R N)
  证明: rfl
-/
theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f otimesₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl

end Module

/--
Definition of `Subalgebra.baseChange` / `Subalgebra.baseChange` 的定义

English:
definition Subalgebra.baseChange
  signature: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  body: AlgHom.range (Algebra.TensorProduct.map (AlgHom.id B B) C.val)

中文:
定义 子代数.baseChange
  签名: {R A : 类型} [交换半环 R] [半环 A] [代数 R A]
  定义体: AlgHom.range (Algebra.TensorProduct.map (AlgHom.id B B) C.val)

Depends on / 依赖: AlgHom, AlgHom.id, AlgHom.range, Algebra, Algebra.TensorProduct.map, C.val, TensorProduct
-/
def Subalgebra.baseChange {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (B : Type*) [CommSemiring B] [Algebra R B] (C : Subalgebra R A) : Subalgebra B (B otimes[R] A) :=
  AlgHom.range (Algebra.TensorProduct.map (AlgHom.id B B) C.val)

variable {R A B : Type*} [CommSemiring R] [Semiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
variable {C : Subalgebra R A}

/--
lemma `Subalgebra.tmul_mem_baseChange` / 引理 `Subalgebra.tmul_mem_baseChange`

English:
lemma Subalgebra.tmul_mem_baseChange
  given: {x : A} (hx : x in C) (b : B)
  statement: b otimesₜ[R] x in C.baseChange B
  proof: ⟨(b otimesₜ[R] ⟨x, hx⟩), rfl⟩

中文:
引理 子代数.tmul_mem_baseChange
  条件: {x : A} (hx : x in C) (b : B)
  结论: b otimesₜ[R] x in C.baseChange B
  证明: ⟨(b otimesₜ[R] ⟨x, hx⟩), rfl⟩
-/
lemma Subalgebra.tmul_mem_baseChange {x : A} (hx : x in C) (b : B) : b otimesₜ[R] x in C.baseChange B :=
  ⟨(b otimesₜ[R] ⟨x, hx⟩), rfl⟩

section

universe u₁ u₂ u₃ u₄ u₅

variable (R S A B : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B]

attribute [local instance] ULift.algebra' in
/--
Definition of `Algebra.TensorProduct.uliftEquiv` / `Algebra.TensorProduct.uliftEquiv` 的定义

English:
definition Algebra.TensorProduct.uliftEquiv
  signature: :
  body: AlgEquiv.trans ULift.algEquiv
    (.trans (congr ULift.algEquiv.symm ULift.algEquiv.symm) <|
      Algebra.TensorProduct.equivOfCompatibleSMul _ _ _ _ _)

中文:
定义 代数.张量积.uliftEquiv
  签名: :
  定义体: AlgEquiv.trans ULift.algEquiv
    (.trans (congr ULift.algEquiv.symm ULift.algEquiv.symm) <|
      Algebra.TensorProduct.equivOfCompatibleSMul _ _ _ _ _)

Depends on / 依赖: AlgEquiv, AlgEquiv.trans, Algebra, Algebra.TensorProduct.equivOfCompatibleSMul, TensorProduct, ULift.algEquiv, ULift.algEquiv.symm, algEquiv, equivOfCompatibleSMul
-/
def Algebra.TensorProduct.uliftEquiv :
    ULift.{u₁} (A otimes[R] B) ≃ₐ[S] ULift.{u₂} A otimes[ULift.{u₃} R] ULift.{u₄} B :=
  AlgEquiv.trans ULift.algEquiv
    (.trans (congr ULift.algEquiv.symm ULift.algEquiv.symm) <|
      Algebra.TensorProduct.equivOfCompatibleSMul _ _ _ _ _)

variable {A B}

@[simp]
/--
lemma `Algebra.TensorProduct.uliftEquiv_tmul` / 引理 `Algebra.TensorProduct.uliftEquiv_tmul`

English:
lemma Algebra.TensorProduct.uliftEquiv_tmul
  given: (a : A) (b : B)
  proof: rfl

中文:
引理 代数.张量积.uliftEquiv_tmul
  条件: (a : A) (b : B)
  证明: rfl
-/
lemma Algebra.TensorProduct.uliftEquiv_tmul (a : A) (b : B) :
    uliftEquiv R S A B ⟨a otimesₜ b⟩ = ⟨a⟩ otimesₜ ⟨b⟩ :=
  rfl

attribute [local instance] ULift.algebra' in
@[simp]
/--
lemma `Algebra.TensorProduct.down_uliftEquiv_symm_tmul` / 引理 `Algebra.TensorProduct.down_uliftEquiv_symm_tmul`

English:
lemma Algebra.TensorProduct.down_uliftEquiv_symm_tmul
  given: (a : ULift A) (b : ULift B)
  proof: rfl

中文:
引理 代数.张量积.down_uliftEquiv_symm_tmul
  条件: (a : 类型层提升 A) (b : 类型层提升 B)
  证明: rfl
-/
lemma Algebra.TensorProduct.down_uliftEquiv_symm_tmul (a : ULift A) (b : ULift B) :
    ((uliftEquiv R S A B).symm (a otimesₜ b)).down = a.down otimesₜ b.down :=
  rfl

attribute [local instance] ULift.algebra' in
/--
lemma `Algebra.TensorProduct.uliftEquiv_symm_tmul` / 引理 `Algebra.TensorProduct.uliftEquiv_symm_tmul`

English:
lemma Algebra.TensorProduct.uliftEquiv_symm_tmul
  given: (a : ULift A) (b : ULift B)
  proof: rfl

中文:
引理 代数.张量积.uliftEquiv_symm_tmul
  条件: (a : 类型层提升 A) (b : 类型层提升 B)
  证明: rfl
-/
lemma Algebra.TensorProduct.uliftEquiv_symm_tmul (a : ULift A) (b : ULift B) :
    (uliftEquiv R S A B).symm (a otimesₜ b) = ⟨a.down otimesₜ b.down⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] ULift.algebra' in
/--
lemma `Algebra.TensorProduct.lmul'_ulift` / 引理 `Algebra.TensorProduct.lmul'_ulift`

English:
lemma Algebra.TensorProduct.lmul'_ulift
  proof: by
  ext <;> simp

中文:
引理 代数.张量积.lmul'_ulift
  证明: by
  ext <;> simp
-/
lemma Algebra.TensorProduct.lmul'_ulift :
    TensorProduct.lmul' (S := ULift.{u₂} S) (ULift.{u₁} R) =
      (TensorProduct.lmul' (S := S) R).ulift.comp
        (uliftEquiv _ _ _ _).symm.toAlgHom := by
  ext <;> simp

end
