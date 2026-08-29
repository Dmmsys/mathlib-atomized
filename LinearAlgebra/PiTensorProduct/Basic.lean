/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Multilinear.TensorProduct
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Tensor product of an indexed family of modules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of modules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `FreeAddMonoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.

## Main definitions

* `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `liftAddHom` constructs an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : MultilinearMap R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.
* `PiTensorProduct.reindex e` re-indexes the components of `⨂[R] i : ι, M` along `e : ι ≃ ι₂`.
* `PiTensorProduct.tmulEquiv` equivalence between a `TensorProduct` of `PiTensorProduct`s and
  a single `PiTensorProduct`.

## Notation

* `⨂[R] i, s i` is defined as localized notation in scope `TensorProduct`.
* `⨂ₜ[R] i, f i` with `f : ∀ i, s i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `FreeAddMonoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `FreeAddMonoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `Fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.
* Instead of requiring `DecidableEq ι` as an argument to `PiTensorProduct` itself, we include it
  as an argument in the constructors of the relation. A decidability instance still has to come
  from somewhere due to the use of `Function.update`, but this hides it from the downstream user.
  See the implementation notes for `MultilinearMap` for an extended discussion of this choice.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

@[expose] public section

open Function

section Semiring

variable {ι ι₂ ι₃ : Type*}
variable {R : Type*} [CommSemiring R]
variable {R₁ R₂ : Type*}
variable {s : ι -> Type*} [forall i, AddCommMonoid (s i)] [forall i, Module R (s i)]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {E : Type*} [AddCommMonoid E] [Module R E]
variable {F : Type*} [AddCommMonoid F]

namespace PiTensorProduct

variable (R) (s)

/--
Inductive type `Eqv` / 归纳类型 `Eqv`

English:
inductive Eqv
  parameters: : FreeAddMonoid (R × Π i, s i) -> FreeAddMonoid (R × Π i, s i) -> Prop
  constructors (6):
    - of_zero: forall (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
    - of_zero_scalar: forall f : Π i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
    - of_add: forall (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂)) (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
    - of_add_scalar: forall (r r' : R) (f : Π i, s i), Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
    - of_smul: forall (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (r' : R), Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
    - add_comm: forall x y, Eqv (x + y) (y + x)

中文:
归纳类型 Eqv
  参数: : FreeAddMonoid (R × Π i, s i) -> FreeAddMonoid (R × Π i, s i) -> 命题
  构造子 (6 个):
    - of_zero: 对任意 (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
    - of_zero_scalar: 对任意 f : Π i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
    - of_add: 对任意 (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂)) (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
    - of_add_scalar: 对任意 (r r' : R) (f : Π i, s i), Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
    - of_smul: 对任意 (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (r' : R), Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
    - add_comm: 对任意 x y, Eqv (x + y) (y + x)
-/
inductive Eqv : FreeAddMonoid (R × Π i, s i) -> FreeAddMonoid (R × Π i, s i) -> Prop
  | of_zero : forall (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
  | of_zero_scalar : forall f : Π i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
  | of_add : forall (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂))
        (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
  | of_add_scalar : forall (r r' : R) (f : Π i, s i),
      Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
  | of_smul : forall (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (r' : R),
      Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
  | add_comm : forall x y, Eqv (x + y) (y + x)

end PiTensorProduct

variable (R) (s)

/--
Definition of `PiTensorProduct` / `PiTensorProduct` 的定义

English:
definition PiTensorProduct
  signature: : Type _
  body: (addConGen (PiTensorProduct.Eqv R s)).Quotient

中文:
定义 PiTensorProduct
  签名: : Type _
  定义体: (addConGen (PiTensorProduct.Eqv R s)).Quotient

Depends on / 依赖: PiTensorProduct, PiTensorProduct.Eqv, Quotient, addConGen
-/
def PiTensorProduct : Type _ :=
  (addConGen (PiTensorProduct.Eqv R s)).Quotient

variable {R}

/-- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product `PiTensorProduct`,
given an indexed family of types `s : ι → Type*`. -/
scoped[TensorProduct] notation3:100"⨂["R"] "(...)", "r:(scoped f => PiTensorProduct R f) => r

open TensorProduct

namespace PiTensorProduct

section Module

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (⨂[R] i, s i)
  body: { (addConGen (PiTensorProduct.Eqv R s)).addMonoid with
    add_comm := fun x y =>
      AddCon.induction_on₂ x y fun _ _ =>
Quotient.sound' AddConGen.Rel.of _ _ Eqv.add_comm _ _ }

中文:
实例 :
  签名: AddCommMonoid (⨂[R] i, s i)
  定义体: { (addConGen (PiTensorProduct.Eqv R s)).addMonoid with
    add_comm := fun x y =>
      AddCon.induction_on₂ x y fun _ _ =>
Quotient.sound' AddConGen.Rel.of _ _ Eqv.add_comm _ _ }

Depends on / 依赖: AddCon, AddCon.induction_on, AddConGen, AddConGen.Rel.of, Eqv.add_comm, PiTensorProduct, PiTensorProduct.Eqv, Quotient, Quotient.sound, addConGen, addMonoid, add_comm
-/
instance : AddCommMonoid (⨂[R] i, s i) :=
  { (addConGen (PiTensorProduct.Eqv R s)).addMonoid with
    add_comm := fun x y =>
      AddCon.induction_on₂ x y fun _ _ =>
Quotient.sound' AddConGen.Rel.of _ _ Eqv.add_comm _ _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (⨂[R] i, s i)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (⨂[R] i, s i)
  定义体: ⟨0⟩
-/
instance : Inhabited (⨂[R] i, s i) := ⟨0⟩

variable (R) {s}

/--
Definition of `tprodCoeff` / `tprodCoeff` 的定义

English:
definition tprodCoeff
  signature: (r : R) (f : Π i, s i)
  body: AddCon.mk' _ FreeAddMonoid.of (r, f)

中文:
定义 tprodCoeff
  签名: (r : R) (f : Π i, s i)
  定义体: AddCon.mk' _ FreeAddMonoid.of (r, f)

Depends on / 依赖: AddCon, AddCon.mk, FreeAddMonoid, FreeAddMonoid.of
-/
def tprodCoeff (r : R) (f : Π i, s i) : ⨂[R] i, s i :=
AddCon.mk' _ FreeAddMonoid.of (r, f)

variable {R}

/--
theorem `zero_tprodCoeff` / 定理 `zero_tprodCoeff`

English:
theorem zero_tprodCoeff
  given: (f : Π i, s i)
  statement: tprodCoeff R 0 f = 0
  proof: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_scalar _

中文:
定理 zero_tprodCoeff
  条件: (f : Π i, s i)
  结论: tprodCoeff R 0 f = 0
  证明: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_scalar _

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_zero_scalar, Quotient, Quotient.sound, of_zero_scalar
-/
theorem zero_tprodCoeff (f : Π i, s i) : tprodCoeff R 0 f = 0 :=
Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_scalar _

/--
theorem `zero_tprodCoeff'` / 定理 `zero_tprodCoeff'`

English:
theorem zero_tprodCoeff'
  given: (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0)
  statement: tprodCoeff R z f = 0
  proof: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero _ _ i hf

中文:
定理 zero_tprodCoeff'
  条件: (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0)
  结论: tprodCoeff R z f = 0
  证明: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero _ _ i hf

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_zero, Quotient, Quotient.sound, of_zero
-/
theorem zero_tprodCoeff' (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0) : tprodCoeff R z f = 0 :=
Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero _ _ i hf

/--
theorem `add_tprodCoeff` / 定理 `add_tprodCoeff`

English:
theorem add_tprodCoeff
  given: [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i)
  proof: Quotient.sound' AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)

中文:
定理 add_tprodCoeff
  条件: [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i)
  证明: Quotient.sound' AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_add, Quotient, Quotient.sound, of_add
-/
theorem add_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
    tprodCoeff R z (update f i m₁) + tprodCoeff R z (update f i m₂) =
      tprodCoeff R z (update f i (m₁ + m₂)) :=
Quotient.sound' AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)

/--
theorem `add_tprodCoeff'` / 定理 `add_tprodCoeff'`

English:
theorem add_tprodCoeff'
  given: (z₁ z₂ : R) (f : Π i, s i)
  proof: Quotient.sound' AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)

中文:
定理 add_tprodCoeff'
  条件: (z₁ z₂ : R) (f : Π i, s i)
  证明: Quotient.sound' AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_add_scalar, Quotient, Quotient.sound, of_add_scalar
-/
theorem add_tprodCoeff' (z₁ z₂ : R) (f : Π i, s i) :
    tprodCoeff R z₁ f + tprodCoeff R z₂ f = tprodCoeff R (z₁ + z₂) f :=
Quotient.sound' AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)

/--
theorem `smul_tprodCoeff_aux` / 定理 `smul_tprodCoeff_aux`

English:
theorem smul_tprodCoeff_aux
  given: [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R)
  proof: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_smul _ _ _ _ _

中文:
定理 smul_tprodCoeff_aux
  条件: [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R)
  证明: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_smul _ _ _ _ _

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_smul, Quotient, Quotient.sound, of_smul
-/
theorem smul_tprodCoeff_aux [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R) :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r * z) f :=
Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_smul _ _ _ _ _

/--
theorem `smul_tprodCoeff` / 定理 `smul_tprodCoeff`

English:
theorem smul_tprodCoeff
  statement: [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [SMul R₁ R]
  proof: by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  rw [h₁]; rw [h₂]
  exact smul_tprodCoeff_aux z f i _

中文:
定理 smul_tprodCoeff
  结论: [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [SMul R₁ R]
  证明: by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  rw [h₁]; rw [h₂]
  exact smul_tprodCoeff_aux z f i _

Depends on / 依赖: one_mul, smul_mul_assoc, smul_one_smul, smul_tprodCoeff_aux
-/
theorem smul_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [SMul R₁ R]
    [IsScalarTower R₁ R R] [SMul R₁ (s i)] [IsScalarTower R₁ R (s i)] :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f := by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  rw [h₁]; rw [h₂]
  exact smul_tprodCoeff_aux z f i _

/--
Definition of `liftAddHom` / `liftAddHom` 的定义

English:
definition liftAddHom
  signature: (φ : (R × Π i, s i) -> F)
  body: (addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ)
    AddCon.addConGen_le.2 fun x y hxy =>
      match hxy with
      | Eqv.of_zero r' f i hf =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
      | Eqv.of_zero_scalar f =>
(AddCon.ker_rel _).2 by simp [FreeA

中文:
定义 liftAddHom
  签名: (φ : (R × Π i, s i) -> F)
  定义体: (addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ)
    AddCon.addConGen_le.2 fun x y hxy =>
      match hxy with
      | Eqv.of_zero r' f i hf =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
      | Eqv.of_zero_scalar f =>
(AddCon.ker_rel _).2 by simp [FreeA

Depends on / 依赖: AddCon, AddCon.addConGen_le, AddCon.ker_rel, C_add, Eqv.of_add, Eqv.of_add_scalar, Eqv.of_zero, Eqv.of_zero_scalar, FreeAddMonoid, FreeAddMonoid.lift, FreeAddMonoid.lift_eval_of, PiTensorProduct, PiTensorProduct.Eqv, addConGen, addConGen_le, ker_rel, lift_eval_of, of_add, of_add_scalar, of_zero
-/
def liftAddHom (φ : (R × Π i, s i) -> F)
    (C0 : forall (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), φ (r, f) = 0)
    (C0' : forall f : Π i, s i, φ (0, f) = 0)
    (C_add : forall [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
    (C_add_scalar : forall (r r' : R) (f : Π i, s i), φ (r, f) + φ (r', f) = φ (r + r', f))
    (C_smul : forall [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (r' : R),
      φ (r, update f i (r' • f i)) = φ (r' * r, f)) :
    (⨂[R] i, s i) ->+ F :=
(addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ)
    AddCon.addConGen_le.2 fun x y hxy =>
      match hxy with
      | Eqv.of_zero r' f i hf =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
      | Eqv.of_zero_scalar f =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, C0']
      | Eqv.of_add inst z f i m₁ m₂ =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, @C_add inst]
      | Eqv.of_add_scalar z₁ z₂ f =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, C_add_scalar]
      | Eqv.of_smul inst z f i r' =>
(AddCon.ker_rel _).2 by simp [FreeAddMonoid.lift_eval_of, @C_smul inst]
      | Eqv.add_comm x y =>
(AddCon.ker_rel _).2 by simp_rw [map_add, add_comm]

/-- Induct using `tprodCoeff` -/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {motive : (⨂[R] i, s i) -> Prop} (z : ⨂[R] i, s i)
  proof: by
  have C0 : motive 0 := by
    have h₁ := tprodCoeff 0 0
    rwa [zero_tprodCoeff] at h₁
  refine AddCon.induction_on z fun x => FreeAddMonoid.recOn x C0 ?_
  simp_rw [AddCon.coe_add]
  refine fun f y ih => add _ _ ?_ ih
  convert! tprodCoeff f.1 f.2

中文:
定理 induction_on'
  结论: {motive : (⨂[R] i, s i) -> 命题} (z : ⨂[R] i, s i)
  证明: by
  have C0 : motive 0 := by
    have h₁ := tprodCoeff 0 0
    rwa [zero_tprodCoeff] at h₁
  refine AddCon.induction_on z fun x => FreeAddMonoid.recOn x C0 ?_
  simp_rw [AddCon.coe_add]
  refine fun f y ih => add _ _ ?_ ih
  convert! tprodCoeff f.1 f.2
-/
protected theorem induction_on' {motive : (⨂[R] i, s i) -> Prop} (z : ⨂[R] i, s i)
    (tprodCoeff : forall (r : R) (f : Π i, s i), motive (tprodCoeff R r f))
    (add : forall x y, motive x -> motive y -> motive (x + y)) :
    motive z := by
  have C0 : motive 0 := by
    have h₁ := tprodCoeff 0 0
    rwa [zero_tprodCoeff] at h₁
  refine AddCon.induction_on z fun x => FreeAddMonoid.recOn x C0 ?_
  simp_rw [AddCon.coe_add]
  refine fun f y ih => add _ _ ?_ ih
  convert! tprodCoeff f.1 f.2

section DistribMulAction

variable [Monoid R₁] [DistribMulAction R₁ R] [SMulCommClass R₁ R R]
variable [Monoid R₂] [DistribMulAction R₂ R] [SMulCommClass R₂ R R]

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
/--
Instance `hasSMul'` / 实例 `hasSMul'`

English:
instance hasSMul'
  signature: : SMul R₁ (⨂[R] i, s i)
  body: ⟨fun r =>
    liftAddHom (fun f : R × Π i, s i => tprodCoeff R (r • f.1) f.2)
      (fun r' f i hf => by simp_rw [zero_tprodCoeff' _ f i hf])
      (fun f => by simp [zero_tprodCoeff]) (fun r' f i m₁ m₂ => by simp [add_tprodCoeff])
      (fun r' r'' f => by simp [add_tprodCoeff']) fun z f i r' => by

中文:
实例 hasSMul'
  签名: : SMul R₁ (⨂[R] i, s i)
  定义体: ⟨fun r =>
    liftAddHom (fun f : R × Π i, s i => tprodCoeff R (r • f.1) f.2)
      (fun r' f i hf => by simp_rw [zero_tprodCoeff' _ f i hf])
      (fun f => by simp [zero_tprodCoeff]) (fun r' f i m₁ m₂ => by simp [add_tprodCoeff])
      (fun r' r'' f => by simp [add_tprodCoeff']) fun z f i r' => by

Depends on / 依赖: add_tprodCoeff, liftAddHom, mul_smul_comm, simp_rw, smul_tprodCoeff, tprodCoeff, zero_tprodCoeff
-/
instance hasSMul' : SMul R₁ (⨂[R] i, s i) :=
  ⟨fun r =>
    liftAddHom (fun f : R × Π i, s i => tprodCoeff R (r • f.1) f.2)
      (fun r' f i hf => by simp_rw [zero_tprodCoeff' _ f i hf])
      (fun f => by simp [zero_tprodCoeff]) (fun r' f i m₁ m₂ => by simp [add_tprodCoeff])
      (fun r' r'' f => by simp [add_tprodCoeff']) fun z f i r' => by
      simp [smul_tprodCoeff, mul_smul_comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (⨂[R] i, s i)
  body: PiTensorProduct.hasSMul'

中文:
实例 :
  签名: SMul R (⨂[R] i, s i)
  定义体: PiTensorProduct.hasSMul'

Depends on / 依赖: PiTensorProduct, PiTensorProduct.hasSMul, hasSMul
-/
instance : SMul R (⨂[R] i, s i) :=
  PiTensorProduct.hasSMul'

/--
theorem `smul_tprodCoeff'` / 定理 `smul_tprodCoeff'`

English:
theorem smul_tprodCoeff'
  given: (r : R₁) (z : R) (f : Π i, s i)
  proof: rfl

中文:
定理 smul_tprodCoeff'
  条件: (r : R₁) (z : R) (f : Π i, s i)
  证明: rfl
-/
theorem smul_tprodCoeff' (r : R₁) (z : R) (f : Π i, s i) :
    r • tprodCoeff R z f = tprodCoeff R (r • z) f := rfl

/--
theorem `smul_add` / 定理 `smul_add`

English:
theorem smul_add
  given: (r : R₁) (x y : ⨂[R] i, s i)
  statement: r • (x + y) = r • x + r • y
  proof: map_add _ _ _

中文:
定理 smul_add
  条件: (r : R₁) (x y : ⨂[R] i, s i)
  结论: r • (x + y) = r • x + r • y
  证明: map_add _ _ _
-/
protected theorem smul_add (r : R₁) (x y : ⨂[R] i, s i) : r • (x + y) = r • x + r • y :=
  map_add _ _ _

/--
Instance `distribMulAction'` / 实例 `distribMulAction'`

English:
instance distribMulAction'
  signature: : DistribMulAction R₁ (⨂[R] i, s i) where
  body: map_add _ _ _
  mul_smul r r' x :=
    PiTensorProduct.induction_on' x (fun {r'' f} => by simp [smul_tprodCoeff', smul_smul])
      fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy]
  one_smul x :=
    PiTensorProduct.induction_on' x (fun {r f} => by rw [smul_tprodCoeff', one_smul

中文:
实例 distribMulAction'
  签名: : DistribMulAction R₁ (⨂[R] i, s i) where
  定义体: map_add _ _ _
  mul_smul r r' x :=
    PiTensorProduct.induction_on' x (fun {r'' f} => by simp [smul_tprodCoeff', smul_smul])
      fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy]
  one_smul x :=
    PiTensorProduct.induction_on' x (fun {r f} => by rw [smul_tprodCoeff', one_smul

Depends on / 依赖: map_add
-/
instance distribMulAction' : DistribMulAction R₁ (⨂[R] i, s i) where
  smul_add _ _ _ := map_add _ _ _
  mul_smul r r' x :=
    PiTensorProduct.induction_on' x (fun {r'' f} => by simp [smul_tprodCoeff', smul_smul])
      fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy]
  one_smul x :=
    PiTensorProduct.induction_on' x (fun {r f} => by rw [smul_tprodCoeff', one_smul])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]
  smul_zero _ := map_zero _

/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: [SMulCommClass R₁ R₂ R]
  body: ⟨fun {r' r''} x =>
    PiTensorProduct.induction_on' x (fun {xr xf} => by simp only [smul_tprodCoeff', smul_comm])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

中文:
实例 smulCommClass'
  签名: [SMulCommClass R₁ R₂ R]
  定义体: ⟨fun {r' r''} x =>
    PiTensorProduct.induction_on' x (fun {xr xf} => by simp only [smul_tprodCoeff', smul_comm])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

Depends on / 依赖: PiTensorProduct, PiTensorProduct.induction_on, PiTensorProduct.smul_add, induction_on, simp_rw, smul_add, smul_comm, smul_tprodCoeff
-/
instance smulCommClass' [SMulCommClass R₁ R₂ R] : SMulCommClass R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x =>
    PiTensorProduct.induction_on' x (fun {xr xf} => by simp only [smul_tprodCoeff', smul_comm])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: [SMul R₁ R₂] [IsScalarTower R₁ R₂ R]
  body: ⟨fun {r' r''} x =>
    PiTensorProduct.induction_on' x (fun {xr xf} => by simp only [smul_tprodCoeff', smul_assoc])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

中文:
实例 isScalarTower'
  签名: [SMul R₁ R₂] [IsScalarTower R₁ R₂ R]
  定义体: ⟨fun {r' r''} x =>
    PiTensorProduct.induction_on' x (fun {xr xf} => by simp only [smul_tprodCoeff', smul_assoc])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

Depends on / 依赖: PiTensorProduct, PiTensorProduct.induction_on, PiTensorProduct.smul_add, induction_on, simp_rw, smul_add, smul_assoc, smul_tprodCoeff
-/
instance isScalarTower' [SMul R₁ R₂] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x =>
    PiTensorProduct.induction_on' x (fun {xr xf} => by simp only [smul_tprodCoeff', smul_assoc])
      fun {z y} ihz ihy => by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

end DistribMulAction

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R]
  body: { PiTensorProduct.distribMulAction' with
    add_smul := fun r r' x =>
      PiTensorProduct.induction_on' x
        (fun {r f} => by simp_rw [smul_tprodCoeff', add_smul, add_tprodCoeff'])
        fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_add_add_comm]
    zero_smul :=

中文:
实例 module'
  签名: [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R]
  定义体: { PiTensorProduct.distribMulAction' with
    add_smul := fun r r' x =>
      PiTensorProduct.induction_on' x
        (fun {r f} => by simp_rw [smul_tprodCoeff', add_smul, add_tprodCoeff'])
        fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_add_add_comm]
    zero_smul :=

Depends on / 依赖: PiTensorProduct, PiTensorProduct.distribMulAction, PiTensorProduct.induction_on, PiTensorProduct.smul_add, add_add_add_comm, add_smul, add_tprodCoeff, add_zero, distribMulAction, induction_on, simp_rw, smul_add, smul_tprodCoeff, zero_smul, zero_tprodCoeff
-/
instance module' [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R] : Module R₁ (⨂[R] i, s i) :=
  { PiTensorProduct.distribMulAction' with
    add_smul := fun r r' x =>
      PiTensorProduct.induction_on' x
        (fun {r f} => by simp_rw [smul_tprodCoeff', add_smul, add_tprodCoeff'])
        fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_add_add_comm]
    zero_smul := fun x =>
      PiTensorProduct.induction_on' x
        (fun {r f} => by simp_rw [smul_tprodCoeff', zero_smul, zero_tprodCoeff])
        fun {x y} ihx ihy => by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_zero] }

-- shortcut instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (⨂[R] i, s i)
  body: PiTensorProduct.module'

中文:
实例 :
  签名: Module R (⨂[R] i, s i)
  定义体: PiTensorProduct.module'

Depends on / 依赖: PiTensorProduct, PiTensorProduct.module, module
-/
instance : Module R (⨂[R] i, s i) :=
  PiTensorProduct.module'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass R R (⨂[R] i, s i)
  body: PiTensorProduct.smulCommClass'

中文:
实例 :
  签名: SMulCommClass R R (⨂[R] i, s i)
  定义体: PiTensorProduct.smulCommClass'

Depends on / 依赖: PiTensorProduct, PiTensorProduct.smulCommClass, smulCommClass
-/
instance : SMulCommClass R R (⨂[R] i, s i) :=
  PiTensorProduct.smulCommClass'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R R (⨂[R] i, s i)
  body: PiTensorProduct.isScalarTower'

中文:
实例 :
  签名: IsScalarTower R R (⨂[R] i, s i)
  定义体: PiTensorProduct.isScalarTower'

Depends on / 依赖: PiTensorProduct, PiTensorProduct.isScalarTower, isScalarTower
-/
instance : IsScalarTower R R (⨂[R] i, s i) :=
  PiTensorProduct.isScalarTower'

variable (R) in
/--
Definition of `tprod` / `tprod` 的定义

English:
definition tprod
  signature: : MultilinearMap R s (⨂[R] i, s i) where
  body: tprodCoeff R 1
  map_update_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_update_smul' {_ f} i r x := by
    rw [smul_tprodCoeff']; rw [← smul_tprodCoeff (1 : R) _ i]; rw [update_idem]; rw [update_self]

@[inherit_doc tprod]
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => tprod R f

中文:
定义 tprod
  签名: : MultilinearMap R s (⨂[R] i, s i) where
  定义体: tprodCoeff R 1
  map_update_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_update_smul' {_ f} i r x := by
    rw [smul_tprodCoeff']; rw [← smul_tprodCoeff (1 : R) _ i]; rw [update_idem]; rw [update_self]

@[inherit_doc tprod]
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => tprod R f

Depends on / 依赖: tprodCoeff
-/
def tprod : MultilinearMap R s (⨂[R] i, s i) where
  toFun := tprodCoeff R 1
  map_update_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_update_smul' {_ f} i r x := by
    rw [smul_tprodCoeff']; rw [← smul_tprodCoeff (1 : R) _ i]; rw [update_idem]; rw [update_self]

@[inherit_doc tprod]
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => tprod R f) => r

/--
theorem `tprod_eq_tprodCoeff_one` / 定理 `tprod_eq_tprodCoeff_one`

English:
theorem tprod_eq_tprodCoeff_one
  proof: rfl

@[simp]

中文:
定理 tprod_eq_tprodCoeff_one
  证明: rfl

@[simp]
-/
theorem tprod_eq_tprodCoeff_one :
    ⇑(tprod R : MultilinearMap R s (⨂[R] i, s i)) = tprodCoeff R 1 := rfl

@[simp]
/--
theorem `tprodCoeff_eq_smul_tprod` / 定理 `tprodCoeff_eq_smul_tprod`

English:
theorem tprodCoeff_eq_smul_tprod
  given: (z : R) (f : Π i, s i)
  statement: tprodCoeff R z f = z • tprod R f
  proof: by
  have : z = z • (1 : R) := by simp only [mul_one, smul_eq_mul]
  conv_lhs => rw [this]
  rfl

中文:
定理 tprodCoeff_eq_smul_tprod
  条件: (z : R) (f : Π i, s i)
  结论: tprodCoeff R z f = z • tprod R f
  证明: by
  have : z = z • (1 : R) := by simp only [mul_one, smul_eq_mul]
  conv_lhs => rw [this]
  rfl

Depends on / 依赖: conv_lhs, mul_one, smul_eq_mul
-/
theorem tprodCoeff_eq_smul_tprod (z : R) (f : Π i, s i) : tprodCoeff R z f = z • tprod R f := by
  have : z = z • (1 : R) := by simp only [mul_one, smul_eq_mul]
  conv_lhs => rw [this]
  rfl

/--
lemma `_root_.FreeAddMonoid.toPiTensorProduct` / 引理 `_root_.FreeAddMonoid.toPiTensorProduct`

English:
lemma _root_.FreeAddMonoid.toPiTensorProduct
  given: (p : FreeAddMonoid (R × Π i, s i))
  proof: by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => rfl
  | of_add b a ih =>
    rw [FreeAddMonoid.toList_of_add]; rw [List.map_cons]; rw [List.sum_cons]; rw [← ih]; rw [← tprodCoeff_eq_smul_tprod]
    rfl

中文:
引理 _root_.FreeAddMonoid.toPiTensorProduct
  条件: (p : FreeAddMonoid (R × Π i, s i))
  证明: by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => rfl
  | of_add b a ih =>
    rw [FreeAddMonoid.toList_of_add]; rw [List.map_cons]; rw [List.sum_cons]; rw [← ih]; rw [← tprodCoeff_eq_smul_tprod]
    rfl

Depends on / 依赖: PiTensorProduct, PiTensorProduct.Eqv, addConGen
-/
lemma _root_.FreeAddMonoid.toPiTensorProduct (p : FreeAddMonoid (R × Π i, s i)) :
    AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p =
    List.sum (List.map (fun x => x.1 • ⨂ₜ[R] i, x.2 i) p.toList) := by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => rfl
  | of_add b a ih =>
    rw [FreeAddMonoid.toList_of_add]; rw [List.map_cons]; rw [List.sum_cons]; rw [← ih]; rw [← tprodCoeff_eq_smul_tprod]
    rfl

/--
Definition of `lifts` / `lifts` 的定义

English:
definition lifts
  signature: (x : ⨂[R] i, s i)
  body: {p | AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p = x}

中文:
定义 lifts
  签名: (x : ⨂[R] i, s i)
  定义体: {p | AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p = x}

Depends on / 依赖: AddCon, AddCon.toQuotient, PiTensorProduct, PiTensorProduct.Eqv, addConGen, toQuotient
-/
def lifts (x : ⨂[R] i, s i) : Set (FreeAddMonoid (R × Π i, s i)) :=
  {p | AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p = x}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_lifts_iff` / 引理 `mem_lifts_iff`

English:
lemma mem_lifts_iff
  given: (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i))
  proof: by
  simp only [lifts, Set.mem_ofPred_eq, FreeAddMonoid.toPiTensorProduct]

中文:
引理 mem_lifts_iff
  条件: (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i))
  证明: by
  simp only [lifts, Set.mem_ofPred_eq, FreeAddMonoid.toPiTensorProduct]

Depends on / 依赖: FreeAddMonoid, FreeAddMonoid.toPiTensorProduct, Set.mem_ofPred_eq, mem_ofPred_eq, toPiTensorProduct
-/
lemma mem_lifts_iff (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i)) :
    p in lifts x ↔ List.sum (List.map (fun x => x.1 • ⨂ₜ[R] i, x.2 i) p.toList) = x := by
  simp only [lifts, Set.mem_ofPred_eq, FreeAddMonoid.toPiTensorProduct]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `nonempty_lifts` / 引理 `nonempty_lifts`

English:
lemma nonempty_lifts
  given: (x : ⨂[R] i, s i)
  statement: Set.Nonempty (lifts x)
  proof: by
  existsi Quot.out x
  simp [lifts, ← AddCon.quot_mk_eq_coe]

中文:
引理 nonempty_lifts
  条件: (x : ⨂[R] i, s i)
  结论: Set.Nonempty (lifts x)
  证明: by
  existsi Quot.out x
  simp [lifts, ← AddCon.quot_mk_eq_coe]

Depends on / 依赖: AddCon, AddCon.quot_mk_eq_coe, Quot.out, existsi, quot_mk_eq_coe
-/
lemma nonempty_lifts (x : ⨂[R] i, s i) : Set.Nonempty (lifts x) := by
  existsi Quot.out x
  simp [lifts, ← AddCon.quot_mk_eq_coe]

instance (x : ⨂[R] i, s i) : Nonempty ↑x.lifts := nonempty_subtype.mpr (nonempty_lifts x)

/--
lemma `lifts_zero` / 引理 `lifts_zero`

English:
lemma lifts_zero
  statement: 0 in lifts (0 : ⨂[R] i, s i)
  proof: by
  rw [mem_lifts_iff]; rw [FreeAddMonoid.toList_zero]; rw [List.map_nil]; rw [List.sum_nil]

中文:
引理 lifts_zero
  结论: 0 in lifts (0 : ⨂[R] i, s i)
  证明: by
  rw [mem_lifts_iff]; rw [FreeAddMonoid.toList_zero]; rw [List.map_nil]; rw [List.sum_nil]

Depends on / 依赖: FreeAddMonoid, FreeAddMonoid.toList_zero, List.map_nil, List.sum_nil, map_nil, mem_lifts_iff, sum_nil, toList_zero
-/
lemma lifts_zero : 0 in lifts (0 : ⨂[R] i, s i) := by
  rw [mem_lifts_iff]; rw [FreeAddMonoid.toList_zero]; rw [List.map_nil]; rw [List.sum_nil]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `lifts_add` / 引理 `lifts_add`

English:
lemma lifts_add
  statement: {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)}
  proof: by
  simp only [lifts, Set.mem_ofPred_eq, AddCon.coe_add]
  rw [hp]; rw [hq]

中文:
引理 lifts_add
  结论: {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)}
  证明: by
  simp only [lifts, Set.mem_ofPred_eq, AddCon.coe_add]
  rw [hp]; rw [hq]

Depends on / 依赖: AddCon, AddCon.coe_add, Set.mem_ofPred_eq, coe_add, mem_ofPred_eq
-/
lemma lifts_add {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)}
    (hp : p in lifts x) (hq : q in lifts y) : p + q in lifts (x + y) := by
  simp only [lifts, Set.mem_ofPred_eq, AddCon.coe_add]
  rw [hp]; rw [hq]

/--
lemma `lifts_smul` / 引理 `lifts_smul`

English:
lemma lifts_smul
  given: {x : ⨂[R] i, s i} {p : FreeAddMonoid (R × Π i, s i)} (h : p in lifts x) (a : R)
  proof: by
  rw [mem_lifts_iff] at h ⊢
  rw [← h]
  simp [Function.comp_def, mul_smul, List.smul_sum]

中文:
引理 lifts_smul
  条件: {x : ⨂[R] i, s i} {p : FreeAddMonoid (R × Π i, s i)} (h : p in lifts x) (a : R)
  证明: by
  rw [mem_lifts_iff] at h ⊢
  rw [← h]
  simp [Function.comp_def, mul_smul, List.smul_sum]

Depends on / 依赖: Function, Function.comp_def, List.smul_sum, comp_def, mem_lifts_iff, mul_smul, smul_sum
-/
lemma lifts_smul {x : ⨂[R] i, s i} {p : FreeAddMonoid (R × Π i, s i)} (h : p in lifts x) (a : R) :
    p.map (fun (y : R × Π i, s i) => (a * y.1, y.2)) in lifts (a • x) := by
  rw [mem_lifts_iff] at h ⊢
  rw [← h]
  simp [Function.comp_def, mul_smul, List.smul_sum]

/-- Induct using scaled versions of `PiTensorProduct.tprod`. -/
@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : (⨂[R] i, s i) -> Prop} (z : ⨂[R] i, s i)
  proof: by
  simp_rw [← tprodCoeff_eq_smul_tprod] at smul_tprod
  exact PiTensorProduct.induction_on' z smul_tprod add

@[ext]

中文:
定理 induction_on
  结论: {motive : (⨂[R] i, s i) -> 命题} (z : ⨂[R] i, s i)
  证明: by
  simp_rw [← tprodCoeff_eq_smul_tprod] at smul_tprod
  exact PiTensorProduct.induction_on' z smul_tprod add

@[ext]
-/
protected theorem induction_on {motive : (⨂[R] i, s i) -> Prop} (z : ⨂[R] i, s i)
    (smul_tprod : forall (r : R) (f : Π i, s i), motive (r • tprod R f))
    (add : forall x y, motive x -> motive y -> motive (x + y)) :
    motive z := by
  simp_rw [← tprodCoeff_eq_smul_tprod] at smul_tprod
  exact PiTensorProduct.induction_on' z smul_tprod add

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E}
  proof: by
  refine LinearMap.ext ?_
  refine fun z =>
    PiTensorProduct.induction_on' z ?_ fun {x y} hx hy => by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    rw [tprodCoeff_eq_smul_tprod]; rw [φ₁.map_smul]; rw [φ₂.map_smul]
    apply congr_arg
    exact MultilinearMap.congr_fun H f

中文:
定理 ext
  结论: {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E}
  证明: by
  refine LinearMap.ext ?_
  refine fun z =>
    PiTensorProduct.induction_on' z ?_ fun {x y} hx hy => by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    rw [tprodCoeff_eq_smul_tprod]; rw [φ₁.map_smul]; rw [φ₂.map_smul]
    apply congr_arg
    exact MultilinearMap.congr_fun H f

Depends on / 依赖: LinearMap, LinearMap.ext, MultilinearMap, MultilinearMap.congr_fun, PiTensorProduct, PiTensorProduct.induction_on, congr_arg, congr_fun, induction_on, map_add, map_smul, tprodCoeff_eq_smul_tprod
-/
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E}
    (H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂ := by
  refine LinearMap.ext ?_
  refine fun z =>
    PiTensorProduct.induction_on' z ?_ fun {x y} hx hy => by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    rw [tprodCoeff_eq_smul_tprod]; rw [φ₁.map_smul]; rw [φ₂.map_smul]
    apply congr_arg
    exact MultilinearMap.congr_fun H f

/--
theorem `span_tprod_eq_top` / 定理 `span_tprod_eq_top`

English:
theorem span_tprod_eq_top
  proof: Submodule.eq_top_iff'.mpr fun t => t.induction_on
    (fun _ _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simp only [Set.mem_range, exists_apply_eq_apply])))
    (fun _ _ hx hy => Submodule.add_mem _ hx hy)

中文:
定理 span_tprod_eq_top
  证明: Submodule.eq_top_iff'.mpr fun t => t.induction_on
    (fun _ _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simp only [Set.mem_range, exists_apply_eq_apply])))
    (fun _ _ hx hy => Submodule.add_mem _ hx hy)

Depends on / 依赖: Set.mem_range, Submodule, Submodule.add_mem, Submodule.eq_top_iff, Submodule.smul_mem, Submodule.subset_span, add_mem, eq_top_iff, exists_apply_eq_apply, induction_on, mem_range, smul_mem, subset_span, t.induction_on
-/
theorem span_tprod_eq_top :
    Submodule.span R (Set.range (tprod R)) = (⊤ : Submodule R (⨂[R] i, s i)) :=
  Submodule.eq_top_iff'.mpr fun t => t.induction_on
    (fun _ _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simp only [Set.mem_range, exists_apply_eq_apply])))
    (fun _ _ hx hy => Submodule.add_mem _ hx hy)

end Module

section Multilinear

open MultilinearMap

variable {s}

section lift

/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: (φ : MultilinearMap R s E)
  body: liftAddHom (fun p : R × Π i, s i => p.1 • φ p.2)
    (fun z f i hf => by simp_rw [map_coord_zero φ i hf, smul_zero])
    (fun f => by simp_rw [zero_smul])
    (fun z f i m₁ m₂ => by simp_rw [← smul_add, φ.map_update_add])
    (fun z₁ z₂ f => by rw [← add_smul])
    fun z f i r => by simp [φ.map_upda

中文:
定义 liftAux
  签名: (φ : MultilinearMap R s E)
  定义体: liftAddHom (fun p : R × Π i, s i => p.1 • φ p.2)
    (fun z f i hf => by simp_rw [map_coord_zero φ i hf, smul_zero])
    (fun f => by simp_rw [zero_smul])
    (fun z f i m₁ m₂ => by simp_rw [← smul_add, φ.map_update_add])
    (fun z₁ z₂ f => by rw [← add_smul])
    fun z f i r => by simp [φ.map_upda

Depends on / 依赖: add_smul, liftAddHom, map_coord_zero, map_update_add, map_update_smul, mul_comm, simp_rw, smul_add, smul_smul, smul_zero, zero_smul
-/
def liftAux (φ : MultilinearMap R s E) : (⨂[R] i, s i) ->+ E :=
  liftAddHom (fun p : R × Π i, s i => p.1 • φ p.2)
    (fun z f i hf => by simp_rw [map_coord_zero φ i hf, smul_zero])
    (fun f => by simp_rw [zero_smul])
    (fun z f i m₁ m₂ => by simp_rw [← smul_add, φ.map_update_add])
    (fun z₁ z₂ f => by rw [← add_smul])
    fun z f i r => by simp [φ.map_update_smul, smul_smul, mul_comm]

/--
theorem `liftAux_tprod` / 定理 `liftAux_tprod`

English:
theorem liftAux_tprod
  given: (φ : MultilinearMap R s E) (f : Π i, s i)
  statement: liftAux φ (tprod R f) = φ f
  proof: by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- The end of this proof was very different before https://github.com/leanprover/lean4/pull/2644:
  -- rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- dsimp [FreeAddMonoid.

中文:
定理 liftAux_tprod
  条件: (φ : MultilinearMap R s E) (f : Π i, s i)
  结论: liftAux φ (tprod R f) = φ f
  证明: by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- The end of this proof was very different before https://github.com/leanprover/lean4/pull/2644:
  -- rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- dsimp [FreeAddMonoid.

Depends on / 依赖: AddCon, AddCon.coe_mk, coe_mk, liftAddHom, liftAux, tprodCoeff, tprod_eq_tprodCoeff_one
-/
theorem liftAux_tprod (φ : MultilinearMap R s E) (f : Π i, s i) : liftAux φ (tprod R f) = φ f := by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- The end of this proof was very different before https://github.com/leanprover/lean4/pull/2644:
  -- rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- dsimp [FreeAddMonoid.lift, FreeAddMonoid.sumAux]
  -- show _ • _ = _
  -- rw [one_smul]
  conv_lhs => apply AddCon.lift_coe
  simp

/--
theorem `liftAux_tprodCoeff` / 定理 `liftAux_tprodCoeff`

English:
theorem liftAux_tprodCoeff
  given: (φ : MultilinearMap R s E) (z : R) (f : Π i, s i)
  proof: rfl

中文:
定理 liftAux_tprodCoeff
  条件: (φ : MultilinearMap R s E) (z : R) (f : Π i, s i)
  证明: rfl
-/
theorem liftAux_tprodCoeff (φ : MultilinearMap R s E) (z : R) (f : Π i, s i) :
    liftAux φ (tprodCoeff R z f) = z • φ f := rfl

/--
theorem `liftAux.smul` / 定理 `liftAux.smul`

English:
theorem liftAux.smul
  given: {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i)
  proof: by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro z f
    rw [smul_tprodCoeff' r z f]; rw [liftAux_tprodCoeff]; rw [liftAux_tprodCoeff]; rw [smul_assoc]
  · intro z y ihz ihy
    rw [smul_add]; rw [(liftAux φ).map_add]; rw [ihz]; rw [ihy]; rw [(liftAux φ).map_add]; rw [smul_add]

中文:
定理 liftAux.smul
  条件: {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i)
  证明: by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro z f
    rw [smul_tprodCoeff' r z f]; rw [liftAux_tprodCoeff]; rw [liftAux_tprodCoeff]; rw [smul_assoc]
  · intro z y ihz ihy
    rw [smul_add]; rw [(liftAux φ).map_add]; rw [ihz]; rw [ihy]; rw [(liftAux φ).map_add]; rw [smul_add]

Depends on / 依赖: PiTensorProduct, PiTensorProduct.induction_on, induction_on, liftAux, liftAux_tprodCoeff, map_add, smul_add, smul_assoc, smul_tprodCoeff
-/
theorem liftAux.smul {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i) :
    liftAux φ (r • x) = r • liftAux φ x := by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro z f
    rw [smul_tprodCoeff' r z f]; rw [liftAux_tprodCoeff]; rw [liftAux_tprodCoeff]; rw [smul_assoc]
  · intro z y ihz ihy
    rw [smul_add]; rw [(liftAux φ).map_add]; rw [ihz]; rw [ihy]; rw [(liftAux φ).map_add]; rw [smul_add]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) ->ₗ[R] E where
  body: { liftAux φ with map_smul' := liftAux.smul }
  invFun φ' := φ'.compMultilinearMap (tprod R)
  left_inv φ := by
    ext
    simp [liftAux_tprod, LinearMap.compMultilinearMap]
  right_inv φ := by
    ext
    simp [liftAux_tprod]
  map_add' φ₁ φ₂ := by
    ext
    simp [liftAux_tprod]
  map_smul' r φ₂ 

中文:
定义 lift
  签名: : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) ->ₗ[R] E where
  定义体: { liftAux φ with map_smul' := liftAux.smul }
  invFun φ' := φ'.compMultilinearMap (tprod R)
  left_inv φ := by
    ext
    simp [liftAux_tprod, LinearMap.compMultilinearMap]
  right_inv φ := by
    ext
    simp [liftAux_tprod]
  map_add' φ₁ φ₂ := by
    ext
    simp [liftAux_tprod]
  map_smul' r φ₂ 

Depends on / 依赖: liftAux, liftAux.smul, map_smul
-/
def lift : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) ->ₗ[R] E where
  toFun φ := { liftAux φ with map_smul' := liftAux.smul }
  invFun φ' := φ'.compMultilinearMap (tprod R)
  left_inv φ := by
    ext
    simp [liftAux_tprod, LinearMap.compMultilinearMap]
  right_inv φ := by
    ext
    simp [liftAux_tprod]
  map_add' φ₁ φ₂ := by
    ext
    simp [liftAux_tprod]
  map_smul' r φ₂ := by
    ext
    simp [liftAux_tprod]

variable {φ : MultilinearMap R s E}

@[simp]
/--
theorem `lift.tprod` / 定理 `lift.tprod`

English:
theorem lift.tprod
  given: (f : Π i, s i)
  statement: lift φ (tprod R f) = φ f
  proof: liftAux_tprod φ f

中文:
定理 lift.tprod
  条件: (f : Π i, s i)
  结论: lift φ (tprod R f) = φ f
  证明: liftAux_tprod φ f

Depends on / 依赖: liftAux_tprod
-/
theorem lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f :=
  liftAux_tprod φ f

/--
theorem `lift.unique'` / 定理 `lift.unique'`

English:
theorem lift.unique'
  statement: {φ' : (⨂[R] i, s i) ->ₗ[R] E}
  proof: ext H.symm ▸ (lift.symm_apply_apply φ).symm

中文:
定理 lift.unique'
  结论: {φ' : (⨂[R] i, s i) ->ₗ[R] E}
  证明: ext H.symm ▸ (lift.symm_apply_apply φ).symm

Depends on / 依赖: H.symm, lift.symm_apply_apply, symm_apply_apply
-/
theorem lift.unique' {φ' : (⨂[R] i, s i) ->ₗ[R] E}
    (H : φ'.compMultilinearMap (PiTensorProduct.tprod R) = φ) : φ' = lift φ :=
ext H.symm ▸ (lift.symm_apply_apply φ).symm

/--
theorem `lift.unique` / 定理 `lift.unique`

English:
theorem lift.unique
  given: {φ' : (⨂[R] i, s i) ->ₗ[R] E} (H : forall f, φ' (PiTensorProduct.tprod R f) = φ f)
  proof: lift.unique' (MultilinearMap.ext H)

@[simp]

中文:
定理 lift.unique
  条件: {φ' : (⨂[R] i, s i) ->ₗ[R] E} (H : 对任意 f, φ' (PiTensorProduct.tprod R f) = φ f)
  证明: lift.unique' (MultilinearMap.ext H)

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.ext, lift.unique, unique
-/
theorem lift.unique {φ' : (⨂[R] i, s i) ->ₗ[R] E} (H : forall f, φ' (PiTensorProduct.tprod R f) = φ f) :
    φ' = lift φ :=
  lift.unique' (MultilinearMap.ext H)

@[simp]
/--
theorem `lift_symm` / 定理 `lift_symm`

English:
theorem lift_symm
  given: (φ' : (⨂[R] i, s i) ->ₗ[R] E)
  statement: lift.symm φ' = φ'.compMultilinearMap (tprod R)
  proof: rfl

@[simp]

中文:
定理 lift_symm
  条件: (φ' : (⨂[R] i, s i) ->ₗ[R] E)
  结论: lift.symm φ' = φ'.compMultilinearMap (tprod R)
  证明: rfl

@[simp]
-/
theorem lift_symm (φ' : (⨂[R] i, s i) ->ₗ[R] E) : lift.symm φ' = φ'.compMultilinearMap (tprod R) :=
  rfl

@[simp]
/--
theorem `lift_tprod` / 定理 `lift_tprod`

English:
theorem lift_tprod
  statement: lift (tprod R : MultilinearMap R s _) = LinearMap.id
  proof: Eq.symm lift.unique' rfl

中文:
定理 lift_tprod
  结论: lift (tprod R : MultilinearMap R s _) = LinearMap.id
  证明: Eq.symm lift.unique' rfl

Depends on / 依赖: Eq.symm, lift.unique, unique
-/
theorem lift_tprod : lift (tprod R : MultilinearMap R s _) = LinearMap.id :=
Eq.symm lift.unique' rfl

end lift

section map

variable {t t' : ι -> Type*}
variable [forall i, AddCommMonoid (t i)] [forall i, Module R (t i)]
variable [forall i, AddCommMonoid (t' i)] [forall i, Module R (t' i)]
variable (g : Π i, t i ->ₗ[R] t' i) (f : Π i, s i ->ₗ[R] t i)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
  body: lift (tprod R).compLinearMap f

中文:
定义 map
  签名: : (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
  定义体: lift (tprod R).compLinearMap f

Depends on / 依赖: compLinearMap
-/
def map : (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i :=
lift (tprod R).compLinearMap f

/--
lemma `map_tprod` / 引理 `map_tprod`

English:
lemma map_tprod
  given: (x : Π i, s i)
  proof: lift.tprod _

中文:
引理 map_tprod
  条件: (x : Π i, s i)
  证明: lift.tprod _
-/
@[simp] lemma map_tprod (x : Π i, s i) :
    map f (tprod R x) = tprod R fun i => f i (x i) :=
  lift.tprod _

-- No lemmas about associativity, because we don't have associativity of `PiTensorProduct` yet.

/--
theorem `map_range_eq_span_tprod` / 定理 `map_range_eq_span_tprod`

English:
theorem map_range_eq_span_tprod
  proof: by
  rw [← Submodule.map_top]; rw [← span_tprod_eq_top]; rw [Submodule.map_span]; rw [← Set.range_comp]
  apply congrArg; ext x
  simp only [Set.mem_range, comp_apply, map_tprod, Set.mem_ofPred_eq]

中文:
定理 map_range_eq_span_tprod
  证明: by
  rw [← Submodule.map_top]; rw [← span_tprod_eq_top]; rw [Submodule.map_span]; rw [← Set.range_comp]
  apply congrArg; ext x
  simp only [Set.mem_range, comp_apply, map_tprod, Set.mem_ofPred_eq]

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_range, Set.range_comp, Submodule, Submodule.map_span, Submodule.map_top, comp_apply, map_span, map_top, map_tprod, mem_ofPred_eq, mem_range, range_comp, span_tprod_eq_top
-/
theorem map_range_eq_span_tprod :
    LinearMap.range (map f) =
      Submodule.span R {t | exists (m : Π i, s i), tprod R (fun i => f i (m i)) = t} := by
  rw [← Submodule.map_top]; rw [← span_tprod_eq_top]; rw [Submodule.map_span]; rw [← Set.range_comp]
  apply congrArg; ext x
  simp only [Set.mem_range, comp_apply, map_tprod, Set.mem_ofPred_eq]

/-- Given submodules `p i ⊆ s i`, this is the natural map: `⨂[R] i, p i → ⨂[R] i, s i`.
This is `TensorProduct.mapIncl` for an arbitrary family of modules.
-/
@[simp]
/--
Definition of `mapIncl` / `mapIncl` 的定义

English:
definition mapIncl
  signature: (p : Π i, Submodule R (s i))
  body: map fun (i : ι) => (p i).subtype

中文:
定义 mapIncl
  签名: (p : Π i, Submodule R (s i))
  定义体: map fun (i : ι) => (p i).subtype

Depends on / 依赖: subtype
-/
def mapIncl (p : Π i, Submodule R (s i)) : (⨂[R] i, p i) ->ₗ[R] ⨂[R] i, s i :=
  map fun (i : ι) => (p i).subtype

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: map (fun (i : ι) => g i ∘ₗ f i) = map g ∘ₗ map f
  proof: by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.coe_comp, Function.comp_apply]

中文:
定理 map_comp
  结论: map (fun (i : ι) => g i ∘ₗ f i) = map g ∘ₗ map f
  证明: by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.coe_comp, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.compMultilinearMap_apply, coe_comp, compMultilinearMap_apply, comp_apply, map_tprod
-/
theorem map_comp : map (fun (i : ι) => g i ∘ₗ f i) = map g ∘ₗ map f := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.coe_comp, Function.comp_apply]

/--
theorem `lift_comp_map` / 定理 `lift_comp_map`

English:
theorem lift_comp_map
  given: (h : MultilinearMap R t E)
  proof: by
  ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    map_tprod, lift.tprod, MultilinearMap.compLinearMap_apply]

中文:
定理 lift_comp_map
  条件: (h : MultilinearMap R t E)
  证明: by
  ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    map_tprod, lift.tprod, MultilinearMap.compLinearMap_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.compMultilinearMap_apply, MultilinearMap, MultilinearMap.compLinearMap_apply, coe_comp, compLinearMap_apply, compMultilinearMap_apply, comp_apply, lift.tprod, map_tprod
-/
theorem lift_comp_map (h : MultilinearMap R t E) :
    lift h ∘ₗ map f = lift (h.compLinearMap f) := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    map_tprod, lift.tprod, MultilinearMap.compLinearMap_apply]

attribute [local ext high] ext

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (fun i => (LinearMap.id : s i ->ₗ[R] s i)) = .id
  proof: by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.id_coe, id_eq]

@[simp]

中文:
定理 map_id
  结论: map (fun i => (LinearMap.id : s i ->ₗ[R] s i)) = .id
  证明: by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.id_coe, id_eq]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.compMultilinearMap_apply, LinearMap.id_coe, compMultilinearMap_apply, id_coe, id_eq, map_tprod
-/
theorem map_id : map (fun i => (LinearMap.id : s i ->ₗ[R] s i)) = .id := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.id_coe, id_eq]

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: map (fun (i : ι) => (1 : s i ->ₗ[R] s i)) = 1
  proof: map_id

中文:
定理 map_one
  结论: map (fun (i : ι) => (1 : s i ->ₗ[R] s i)) = 1
  证明: map_id
-/
protected theorem map_one : map (fun (i : ι) => (1 : s i ->ₗ[R] s i)) = 1 :=
  map_id

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f₁ f₂ : Π i, s i ->ₗ[R] s i)
  proof: map_comp f₁ f₂

中文:
定理 map_mul
  条件: (f₁ f₂ : Π i, s i ->ₗ[R] s i)
  证明: map_comp f₁ f₂
-/
protected theorem map_mul (f₁ f₂ : Π i, s i ->ₗ[R] s i) :
    map (fun i => f₁ i * f₂ i) = map f₁ * map f₂ :=
  map_comp f₁ f₂

/-- Upgrading `PiTensorProduct.map` to a `MonoidHom` when `s = t`. -/
@[simps]
/--
Definition of `mapMonoidHom` / `mapMonoidHom` 的定义

English:
definition mapMonoidHom
  signature: : (Π i, s i ->ₗ[R] s i) ->* ((⨂[R] i, s i) ->ₗ[R] ⨂[R] i, s i) where
  body: map
  map_one' := PiTensorProduct.map_one
  map_mul' := PiTensorProduct.map_mul

@[simp]

中文:
定义 mapMonoidHom
  签名: : (Π i, s i ->ₗ[R] s i) ->* ((⨂[R] i, s i) ->ₗ[R] ⨂[R] i, s i) where
  定义体: map
  map_one' := PiTensorProduct.map_one
  map_mul' := PiTensorProduct.map_mul

@[simp]
-/
def mapMonoidHom : (Π i, s i ->ₗ[R] s i) ->* ((⨂[R] i, s i) ->ₗ[R] ⨂[R] i, s i) where
  toFun := map
  map_one' := PiTensorProduct.map_one
  map_mul' := PiTensorProduct.map_mul

@[simp]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (f : Π i, s i ->ₗ[R] s i) (n : Nat)
  proof: map_pow mapMonoidHom _ _

中文:
定理 map_pow
  条件: (f : Π i, s i ->ₗ[R] s i) (n : 自然数)
  证明: map_pow mapMonoidHom _ _
-/
protected theorem map_pow (f : Π i, s i ->ₗ[R] s i) (n : Nat) :
    map (f ^ n) = map f ^ n := map_pow mapMonoidHom _ _

open Function in
/--
theorem `map_add_smul_aux` / 定理 `map_add_smul_aux`

English:
theorem map_add_smul_aux
  given: [DecidableEq ι] (i : ι) (x : Π i, s i) (u : s i ->ₗ[R] t i)
  proof: by
  ext j
  exact apply_update (fun i F => F (x i)) f i u j

中文:
定理 map_add_smul_aux
  条件: [DecidableEq ι] (i : ι) (x : Π i, s i) (u : s i ->ₗ[R] t i)
  证明: by
  ext j
  exact apply_update (fun i F => F (x i)) f i u j
-/
private theorem map_add_smul_aux [DecidableEq ι] (i : ι) (x : Π i, s i) (u : s i ->ₗ[R] t i) :
    (fun j => update f i u j (x j)) = update (fun j => (f j) (x j)) i (u (x i)) := by
  ext j
  exact apply_update (fun i F => F (x i)) f i u j

open Function in
/--
theorem `map_update_add` / 定理 `map_update_add`

English:
theorem map_update_add
  given: [DecidableEq ι] (i : ι) (u v : s i ->ₗ[R] t i)
  proof: by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.add_apply,
    MultilinearMap.map_update_add]

中文:
定理 map_update_add
  条件: [DecidableEq ι] (i : ι) (u v : s i ->ₗ[R] t i)
  证明: by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.add_apply,
    MultilinearMap.map_update_add]
-/
protected theorem map_update_add [DecidableEq ι] (i : ι) (u v : s i ->ₗ[R] t i) :
    map (update f i (u + v)) = map (update f i u) + map (update f i v) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.add_apply,
    MultilinearMap.map_update_add]

open Function in
/--
theorem `map_update_smul` / 定理 `map_update_smul`

English:
theorem map_update_smul
  given: [DecidableEq ι] (i : ι) (c : R) (u : s i ->ₗ[R] t i)
  proof: by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.smul_apply,
    MultilinearMap.map_update_smul]

中文:
定理 map_update_smul
  条件: [DecidableEq ι] (i : ι) (c : R) (u : s i ->ₗ[R] t i)
  证明: by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.smul_apply,
    MultilinearMap.map_update_smul]
-/
protected theorem map_update_smul [DecidableEq ι] (i : ι) (c : R) (u : s i ->ₗ[R] t i) :
    map (update f i (c • u)) = c • map (update f i u) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.smul_apply,
    MultilinearMap.map_update_smul]

variable (R s t)

/-- The tensor of a family of linear maps from `sᵢ` to `tᵢ`, as a multilinear map of
the family.
-/
@[simps]
/--
Definition of `mapMultilinear` / `mapMultilinear` 的定义

English:
definition mapMultilinear
  signature: :
  body: map
  map_update_smul' _ _ _ _ := PiTensorProduct.map_update_smul _ _ _ _
  map_update_add' _ _ _ _ := PiTensorProduct.map_update_add _ _ _ _

中文:
定义 mapMultilinear
  签名: :
  定义体: map
  map_update_smul' _ _ _ _ := PiTensorProduct.map_update_smul _ _ _ _
  map_update_add' _ _ _ _ := PiTensorProduct.map_update_add _ _ _ _
-/
noncomputable def mapMultilinear :
    MultilinearMap R (fun (i : ι) => s i ->ₗ[R] t i) ((⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i) where
  toFun := map
  map_update_smul' _ _ _ _ := PiTensorProduct.map_update_smul _ _ _ _
  map_update_add' _ _ _ _ := PiTensorProduct.map_update_add _ _ _ _

variable {R s t}

/--
Definition of `piTensorHomMap` / `piTensorHomMap` 的定义

English:
definition piTensorHomMap
  signature: : (⨂[R] i, s i ->ₗ[R] t i) ->ₗ[R] (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
  body: lift.toLinearMap ∘ₗ lift (MultilinearMap.piLinearMap <| tprod R)

中文:
定义 piTensorHomMap
  签名: : (⨂[R] i, s i ->ₗ[R] t i) ->ₗ[R] (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i
  定义体: lift.toLinearMap ∘ₗ lift (MultilinearMap.piLinearMap <| tprod R)

Depends on / 依赖: MultilinearMap, MultilinearMap.piLinearMap, lift.toLinearMap, piLinearMap, toLinearMap
-/
def piTensorHomMap : (⨂[R] i, s i ->ₗ[R] t i) ->ₗ[R] (⨂[R] i, s i) ->ₗ[R] ⨂[R] i, t i :=
  lift.toLinearMap ∘ₗ lift (MultilinearMap.piLinearMap <| tprod R)

/--
lemma `piTensorHomMap_tprod_tprod` / 引理 `piTensorHomMap_tprod_tprod`

English:
lemma piTensorHomMap_tprod_tprod
  given: (f : Π i, s i ->ₗ[R] t i) (x : Π i, s i)
  proof: by
  simp [piTensorHomMap]

中文:
引理 piTensorHomMap_tprod_tprod
  条件: (f : Π i, s i ->ₗ[R] t i) (x : Π i, s i)
  证明: by
  simp [piTensorHomMap]
-/
@[simp] lemma piTensorHomMap_tprod_tprod (f : Π i, s i ->ₗ[R] t i) (x : Π i, s i) :
    piTensorHomMap (tprod R f) (tprod R x) = tprod R fun i => f i (x i) := by
  simp [piTensorHomMap]

/--
lemma `piTensorHomMap_tprod_eq_map` / 引理 `piTensorHomMap_tprod_eq_map`

English:
lemma piTensorHomMap_tprod_eq_map
  given: (f : Π i, s i ->ₗ[R] t i)
  proof: by
  ext; simp

中文:
引理 piTensorHomMap_tprod_eq_map
  条件: (f : Π i, s i ->ₗ[R] t i)
  证明: by
  ext; simp
-/
lemma piTensorHomMap_tprod_eq_map (f : Π i, s i ->ₗ[R] t i) :
    piTensorHomMap (tprod R f) = map f := by
  ext; simp

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : Π i, s i ≃ₗ[R] t i)
  body: .ofLinearMap
    (map (fun i => f i))
    (map (fun i => (f i).symm))
    (by ext; simp)
    (by ext; simp)

@[simp]

中文:
定义 congr
  签名: (f : Π i, s i ≃ₗ[R] t i)
  定义体: .ofLinearMap
    (map (fun i => f i))
    (map (fun i => (f i).symm))
    (by ext; simp)
    (by ext; simp)

@[simp]

Depends on / 依赖: ofLinearMap
-/
noncomputable def congr (f : Π i, s i ≃ₗ[R] t i) :
    (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i, t i :=
  .ofLinearMap
    (map (fun i => f i))
    (map (fun i => (f i).symm))
    (by ext; simp)
    (by ext; simp)

@[simp]
/--
theorem `congr_tprod` / 定理 `congr_tprod`

English:
theorem congr_tprod
  given: (f : Π i, s i ≃ₗ[R] t i) (m : Π i, s i)
  proof: by
  simp only [congr, LinearEquiv.coe_ofLinearMap, map_tprod, LinearEquiv.coe_coe]

@[simp]

中文:
定理 congr_tprod
  条件: (f : Π i, s i ≃ₗ[R] t i) (m : Π i, s i)
  证明: by
  simp only [congr, LinearEquiv.coe_ofLinearMap, map_tprod, LinearEquiv.coe_coe]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_ofLinearMap, coe_coe, coe_ofLinearMap, map_tprod
-/
theorem congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π i, s i) :
    congr f (tprod R m) = tprod R (fun (i : ι) => (f i) (m i)) := by
  simp only [congr, LinearEquiv.coe_ofLinearMap, map_tprod, LinearEquiv.coe_coe]

@[simp]
/--
theorem `congr_symm_tprod` / 定理 `congr_symm_tprod`

English:
theorem congr_symm_tprod
  given: (f : Π i, s i ≃ₗ[R] t i) (p : Π i, t i)
  proof: by
  simp only [congr, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap, map_tprod,
    LinearEquiv.coe_coe]

中文:
定理 congr_symm_tprod
  条件: (f : Π i, s i ≃ₗ[R] t i) (p : Π i, t i)
  证明: by
  simp only [congr, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap, map_tprod,
    LinearEquiv.coe_coe]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_ofLinearMap, LinearEquiv.symm_ofLinearMap, coe_coe, coe_ofLinearMap, map_tprod, symm_ofLinearMap
-/
theorem congr_symm_tprod (f : Π i, s i ≃ₗ[R] t i) (p : Π i, t i) :
    (congr f).symm (tprod R p) = tprod R (fun (i : ι) => (f i).symm (p i)) := by
  simp only [congr, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap, map_tprod,
    LinearEquiv.coe_coe]

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : Π i, s i ->ₗ[R] t i ->ₗ[R] t' i)
  body: lift LinearMap.compMultilinearMap piTensorHomMap (tprod R).compLinearMap f

中文:
定义 map₂
  签名: (f : Π i, s i ->ₗ[R] t i ->ₗ[R] t' i)
  定义体: lift LinearMap.compMultilinearMap piTensorHomMap (tprod R).compLinearMap f

Depends on / 依赖: LinearMap, LinearMap.compMultilinearMap, compLinearMap, compMultilinearMap, piTensorHomMap
-/
def map₂ (f : Π i, s i ->ₗ[R] t i ->ₗ[R] t' i) :
    (⨂[R] i, s i) ->ₗ[R] (⨂[R] i, t i) ->ₗ[R] ⨂[R] i, t' i :=
lift LinearMap.compMultilinearMap piTensorHomMap (tprod R).compLinearMap f

/--
lemma `map₂_tprod_tprod` / 引理 `map₂_tprod_tprod`

English:
lemma map₂_tprod_tprod
  given: (f : Π i, s i ->ₗ[R] t i ->ₗ[R] t' i) (x : Π i, s i) (y : Π i, t i)
  proof: by
  simp [map₂]

中文:
引理 map₂_tprod_tprod
  条件: (f : Π i, s i ->ₗ[R] t i ->ₗ[R] t' i) (x : Π i, s i) (y : Π i, t i)
  证明: by
  simp [map₂]
-/
lemma map₂_tprod_tprod (f : Π i, s i ->ₗ[R] t i ->ₗ[R] t' i) (x : Π i, s i) (y : Π i, t i) :
    map₂ f (tprod R x) (tprod R y) = tprod R fun i => f i (x i) (y i) := by
  simp [map₂]

/--
Definition of `piTensorHomMapFun₂` / `piTensorHomMapFun₂` 的定义

English:
definition piTensorHomMapFun₂
  signature: : (⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) ->
  body: fun φ => lift LinearMap.compMultilinearMap piTensorHomMap
    (lift <| MultilinearMap.piLinearMap <| tprod R) φ

中文:
定义 piTensorHomMapFun₂
  签名: : (⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) ->
  定义体: fun φ => lift LinearMap.compMultilinearMap piTensorHomMap
    (lift <| MultilinearMap.piLinearMap <| tprod R) φ

Depends on / 依赖: LinearMap, LinearMap.compMultilinearMap, MultilinearMap, MultilinearMap.piLinearMap, compMultilinearMap, piLinearMap, piTensorHomMap
-/
def piTensorHomMapFun₂ : (⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) ->
    (⨂[R] i, s i) ->ₗ[R] (⨂[R] i, t i) ->ₗ[R] (⨂[R] i, t' i) :=
fun φ => lift LinearMap.compMultilinearMap piTensorHomMap
    (lift <| MultilinearMap.piLinearMap <| tprod R) φ

/--
theorem `piTensorHomMapFun₂_add` / 定理 `piTensorHomMapFun₂_add`

English:
theorem piTensorHomMapFun₂_add
  given: (φ ψ : ⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i)
  proof: by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_add, LinearMap.compMultilinearMap_apply,
    lift.tprod, add_apply, LinearMap.add_apply]

中文:
定理 piTensorHomMapFun₂_add
  条件: (φ ψ : ⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i)
  证明: by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_add, LinearMap.compMultilinearMap_apply,
    lift.tprod, add_apply, LinearMap.add_apply]

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.compMultilinearMap_apply, add_apply, compMultilinearMap_apply, lift.tprod, map_add
-/
theorem piTensorHomMapFun₂_add (φ ψ : ⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) :
    piTensorHomMapFun₂ (φ + ψ) = piTensorHomMapFun₂ φ + piTensorHomMapFun₂ ψ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_add, LinearMap.compMultilinearMap_apply,
    lift.tprod, add_apply, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `piTensorHomMapFun₂_smul` / 定理 `piTensorHomMapFun₂_smul`

English:
theorem piTensorHomMapFun₂_smul
  given: (r : R) (φ : ⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i)
  proof: by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_smul, LinearMap.compMultilinearMap_apply,
    lift.tprod, smul_apply, LinearMap.smul_apply]

中文:
定理 piTensorHomMapFun₂_smul
  条件: (r : R) (φ : ⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i)
  证明: by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_smul, LinearMap.compMultilinearMap_apply,
    lift.tprod, smul_apply, LinearMap.smul_apply]

Depends on / 依赖: LinearMap, LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, compMultilinearMap_apply, lift.tprod, map_smul, smul_apply
-/
theorem piTensorHomMapFun₂_smul (r : R) (φ : ⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) :
    piTensorHomMapFun₂ (r • φ) = r • piTensorHomMapFun₂ φ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_smul, LinearMap.compMultilinearMap_apply,
    lift.tprod, smul_apply, LinearMap.smul_apply]

/--
Definition of `piTensorHomMap₂` / `piTensorHomMap₂` 的定义

English:
definition piTensorHomMap₂
  signature: : (⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) ->ₗ[R]
  body: piTensorHomMapFun₂
  map_add' x y := piTensorHomMapFun₂_add x y
  map_smul' x y := piTensorHomMapFun₂_smul x y

中文:
定义 piTensorHomMap₂
  签名: : (⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) ->ₗ[R]
  定义体: piTensorHomMapFun₂
  map_add' x y := piTensorHomMapFun₂_add x y
  map_smul' x y := piTensorHomMapFun₂_smul x y
-/
def piTensorHomMap₂ : (⨂[R] i, s i ->ₗ[R] t i ->ₗ[R] t' i) ->ₗ[R]
    (⨂[R] i, s i) ->ₗ[R] (⨂[R] i, t i) ->ₗ[R] (⨂[R] i, t' i) where
  toFun := piTensorHomMapFun₂
  map_add' x y := piTensorHomMapFun₂_add x y
  map_smul' x y := piTensorHomMapFun₂_smul x y

set_option backward.isDefEq.respectTransparency false in
/--
lemma `piTensorHomMap₂_tprod_tprod_tprod` / 引理 `piTensorHomMap₂_tprod_tprod_tprod`

English:
lemma piTensorHomMap₂_tprod_tprod_tprod
  proof: by
  simp [piTensorHomMapFun₂, piTensorHomMap₂]

中文:
引理 piTensorHomMap₂_tprod_tprod_tprod
  证明: by
  simp [piTensorHomMapFun₂, piTensorHomMap₂]
-/
@[simp] lemma piTensorHomMap₂_tprod_tprod_tprod
    (f : forall i, s i ->ₗ[R] t i ->ₗ[R] t' i) (a : forall i, s i) (b : forall i, t i) :
    piTensorHomMap₂ (tprod R f) (tprod R a) (tprod R b) = tprod R (fun i => f i (a i) (b i)) := by
  simp [piTensorHomMapFun₂, piTensorHomMap₂]

end map

section

variable (R M)

variable (s) in
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (e : ι ≃ ι₂)
  body: let f := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι₂), s (e.symm i)) e
  let g := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι), s i) e
  LinearEquiv.ofLinearMap (lift <| f.symm <| tprod R) (lift <| g <| tprod R) (by aesop) (by aesop)

中文:
定义 reindex
  签名: (e : ι ≃ ι₂)
  定义体: let f := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι₂), s (e.symm i)) e
  let g := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι), s i) e
  LinearEquiv.ofLinearMap (lift <| f.symm <| tprod R) (lift <| g <| tprod R) (by aesop) (by aesop)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, domDomCongrLinearEquiv, e.symm, f.symm, ofLinearMap
-/
def reindex (e : ι ≃ ι₂) : (⨂[R] i : ι, s i) ≃ₗ[R] ⨂[R] i : ι₂, s (e.symm i) :=
  let f := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι₂), s (e.symm i)) e
  let g := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι), s i) e
  LinearEquiv.ofLinearMap (lift <| f.symm <| tprod R) (lift <| g <| tprod R) (by aesop) (by aesop)

end

@[simp]
/--
theorem `reindex_tprod` / 定理 `reindex_tprod`

English:
theorem reindex_tprod
  given: (e : ι ≃ ι₂) (f : Π i, s i)
  proof: by
  dsimp [reindex]
  exact liftAux_tprod _ f

@[simp]

中文:
定理 reindex_tprod
  条件: (e : ι ≃ ι₂) (f : Π i, s i)
  证明: by
  dsimp [reindex]
  exact liftAux_tprod _ f

@[simp]

Depends on / 依赖: liftAux_tprod, reindex
-/
theorem reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i) :
    reindex R s e (tprod R f) = tprod R fun i => f (e.symm i) := by
  dsimp [reindex]
  exact liftAux_tprod _ f

@[simp]
/--
theorem `reindex_comp_tprod` / 定理 `reindex_comp_tprod`

English:
theorem reindex_comp_tprod
  given: (e : ι ≃ ι₂)
  proof: MultilinearMap.ext reindex_tprod e

中文:
定理 reindex_comp_tprod
  条件: (e : ι ≃ ι₂)
  证明: MultilinearMap.ext reindex_tprod e

Depends on / 依赖: MultilinearMap, MultilinearMap.ext, reindex_tprod
-/
theorem reindex_comp_tprod (e : ι ≃ ι₂) :
    (reindex R s e).compMultilinearMap (tprod R) =
    (domDomCongrLinearEquiv' R R s _ e).symm (tprod R) :=
MultilinearMap.ext reindex_tprod e

/--
theorem `lift_comp_reindex` / 定理 `lift_comp_reindex`

English:
theorem lift_comp_reindex
  given: (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i => s (e.symm i)) E)
  proof: by
  ext; simp [reindex]

@[simp]

中文:
定理 lift_comp_reindex
  条件: (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i => s (e.symm i)) E)
  证明: by
  ext; simp [reindex]

@[simp]

Depends on / 依赖: reindex
-/
theorem lift_comp_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i => s (e.symm i)) E) :
    lift φ ∘ₗ (reindex R s e) = lift ((domDomCongrLinearEquiv' R R s _ e).symm φ) := by
  ext; simp [reindex]

@[simp]
/--
theorem `lift_comp_reindex_symm` / 定理 `lift_comp_reindex_symm`

English:
theorem lift_comp_reindex_symm
  given: (e : ι ≃ ι₂) (φ : MultilinearMap R s E)
  proof: by
  ext; simp [reindex]

中文:
定理 lift_comp_reindex_symm
  条件: (e : ι ≃ ι₂) (φ : MultilinearMap R s E)
  证明: by
  ext; simp [reindex]

Depends on / 依赖: reindex
-/
theorem lift_comp_reindex_symm (e : ι ≃ ι₂) (φ : MultilinearMap R s E) :
    lift φ ∘ₗ (reindex R s e).symm = lift (domDomCongrLinearEquiv' R R s _ e φ) := by
  ext; simp [reindex]

/--
theorem `lift_reindex` / 定理 `lift_reindex`

English:
theorem lift_reindex
  proof: LinearMap.congr_fun (lift_comp_reindex e φ) x

@[simp]

中文:
定理 lift_reindex
  证明: LinearMap.congr_fun (lift_comp_reindex e φ) x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lift_comp_reindex
-/
theorem lift_reindex
    (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i => s (e.symm i)) E) (x : ⨂[R] i, s i) :
    lift φ (reindex R s e x) = lift ((domDomCongrLinearEquiv' R R s _ e).symm φ) x :=
  LinearMap.congr_fun (lift_comp_reindex e φ) x

@[simp]
/--
theorem `lift_reindex_symm` / 定理 `lift_reindex_symm`

English:
theorem lift_reindex_symm
  proof: LinearMap.congr_fun (lift_comp_reindex_symm e φ) x

中文:
定理 lift_reindex_symm
  证明: LinearMap.congr_fun (lift_comp_reindex_symm e φ) x

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lift_comp_reindex_symm
-/
theorem lift_reindex_symm
    (e : ι ≃ ι₂) (φ : MultilinearMap R s E) (x : ⨂[R] i, s (e.symm i)) :
    lift φ (reindex R s e |>.symm x) = lift (domDomCongrLinearEquiv' R R s _ e φ) x :=
  LinearMap.congr_fun (lift_comp_reindex_symm e φ) x

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `reindex_trans` / 定理 `reindex_trans`

English:
theorem reindex_trans
  given: (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃)
  proof: by
  apply LinearEquiv.toLinearMap_injective
  ext f
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, reindex_tprod,
    LinearMap.coe_compMultilinearMap, Function.comp_apply,
    reindex_comp_tprod]
  congr

中文:
定理 reindex_trans
  条件: (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃)
  证明: by
  apply LinearEquiv.toLinearMap_injective
  ext f
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, reindex_tprod,
    LinearMap.coe_compMultilinearMap, Function.comp_apply,
    reindex_comp_tprod]
  congr

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.toLinearMap_injective, LinearEquiv.trans_apply, LinearMap, LinearMap.coe_compMultilinearMap, coe_coe, coe_compMultilinearMap, comp_apply, reindex_comp_tprod, reindex_tprod, toLinearMap_injective, trans_apply
-/
theorem reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) :
    (reindex R s e).trans (reindex R _ e') = reindex R s (e.trans e') := by
  apply LinearEquiv.toLinearMap_injective
  ext f
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, reindex_tprod,
    LinearMap.coe_compMultilinearMap, Function.comp_apply,
    reindex_comp_tprod]
  congr

/--
theorem `reindex_reindex` / 定理 `reindex_reindex`

English:
theorem reindex_reindex
  given: (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, s i)
  proof: LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R s (e.trans e')) x

中文:
定理 reindex_reindex
  条件: (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, s i)
  证明: LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R s (e.trans e')) x

Depends on / 依赖: LinearEquiv, LinearEquiv.congr_fun, congr_fun, e.trans, reindex, reindex_trans
-/
theorem reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, s i) :
    reindex R _ e' (reindex R s e x) = reindex R s (e.trans e') x :=
  LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R s (e.trans e')) x

/-- This lemma is impractical to state in the dependent case. -/
@[simp]
/--
theorem `reindex_symm` / 定理 `reindex_symm`

English:
theorem reindex_symm
  given: (e : ι ≃ ι₂)
  proof: by
  ext x
  simp [reindex]

中文:
定理 reindex_symm
  条件: (e : ι ≃ ι₂)
  证明: by
  ext x
  simp [reindex]

Depends on / 依赖: reindex
-/
theorem reindex_symm (e : ι ≃ ι₂) :
    (reindex R (fun _ => M) e).symm = reindex R (fun _ => M) e.symm := by
  ext x
  simp [reindex]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `reindex_refl` / 定理 `reindex_refl`

English:
theorem reindex_refl
  statement: reindex R s (Equiv.refl ι) = LinearEquiv.refl R _
  proof: by
  ext
  simp [reindex, domDomCongrLinearEquiv']

中文:
定理 reindex_refl
  结论: reindex R s (Equiv.refl ι) = LinearEquiv.refl R _
  证明: by
  ext
  simp [reindex, domDomCongrLinearEquiv']

Depends on / 依赖: domDomCongrLinearEquiv, reindex
-/
theorem reindex_refl : reindex R s (Equiv.refl ι) = LinearEquiv.refl R _ := by
  ext
  simp [reindex, domDomCongrLinearEquiv']

variable {t : ι -> Type*}
variable [forall i, AddCommMonoid (t i)] [forall i, Module R (t i)]

/--
theorem `map_comp_reindex_eq` / 定理 `map_comp_reindex_eq`

English:
theorem map_comp_reindex_eq
  given: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂)
  proof: by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.comp_apply, reindex_tprod, map_tprod]

中文:
定理 map_comp_reindex_eq
  条件: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂)
  证明: by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.comp_apply, reindex_tprod, map_tprod]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, coe_coe, compMultilinearMap_apply, comp_apply, map_tprod, reindex_tprod
-/
theorem map_comp_reindex_eq (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) :
    map (fun i => f (e.symm i)) ∘ₗ reindex R s e = reindex R t e ∘ₗ map f := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.comp_apply, reindex_tprod, map_tprod]

/--
theorem `map_reindex` / 定理 `map_reindex`

English:
theorem map_reindex
  given: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s i)
  proof: DFunLike.congr_fun (map_comp_reindex_eq _ _) _

中文:
定理 map_reindex
  条件: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s i)
  证明: DFunLike.congr_fun (map_comp_reindex_eq _ _) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp_reindex_eq
-/
theorem map_reindex (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s i) :
    map (fun i => f (e.symm i)) (reindex R s e x) = reindex R t e (map f x) :=
  DFunLike.congr_fun (map_comp_reindex_eq _ _) _

/--
theorem `map_comp_reindex_symm` / 定理 `map_comp_reindex_symm`

English:
theorem map_comp_reindex_symm
  given: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂)
  proof: by
  ext m
  apply LinearEquiv.injective (reindex R t e)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, ← map_reindex, LinearEquiv.apply_symm_apply, map_tprod]

中文:
定理 map_comp_reindex_symm
  条件: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂)
  证明: by
  ext m
  apply LinearEquiv.injective (reindex R t e)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, ← map_reindex, LinearEquiv.apply_symm_apply, map_tprod]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe, LinearEquiv.injective, LinearMap, LinearMap.coe_comp, LinearMap.compMultilinearMap_apply, apply_symm_apply, coe_coe, coe_comp, compMultilinearMap_apply, comp_apply, injective, map_reindex, map_tprod, reindex
-/
theorem map_comp_reindex_symm (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) :
    map f ∘ₗ (reindex R s e).symm = (reindex R t e).symm ∘ₗ map (fun i => f (e.symm i)) := by
  ext m
  apply LinearEquiv.injective (reindex R t e)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, ← map_reindex, LinearEquiv.apply_symm_apply, map_tprod]

/--
theorem `map_reindex_symm` / 定理 `map_reindex_symm`

English:
theorem map_reindex_symm
  given: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s (e.symm i))
  proof: DFunLike.congr_fun (map_comp_reindex_symm _ _) _

中文:
定理 map_reindex_symm
  条件: (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s (e.symm i))
  证明: DFunLike.congr_fun (map_comp_reindex_symm _ _) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp_reindex_symm
-/
theorem map_reindex_symm (f : Π i, s i ->ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s (e.symm i)) :
    map f ((reindex R s e).symm x) = (reindex R t e).symm (map (fun i => f (e.symm i)) x) :=
  DFunLike.congr_fun (map_comp_reindex_symm _ _) _

variable (ι)

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The tensor product over an empty index type `ι` is isomorphic to the base ring. -/
@[simps symm_apply]
/--
Definition of `isEmptyEquiv` / `isEmptyEquiv` 的定义

English:
definition isEmptyEquiv
  signature: [IsEmpty ι]
  body: lift (constOfIsEmpty R _ 1)
  invFun r := r • tprod R (@isEmptyElim _ _ _)
  left_inv x := by
    refine x.induction_on ?_ ?_
    · intro x y
      simp only [map_smulₛₗ, RingHom.id_apply, lift.tprod, constOfIsEmpty_apply, const_apply,
        smul_eq_mul, mul_one]
      congr
      aesop
    · simp

中文:
定义 isEmptyEquiv
  签名: [IsEmpty ι]
  定义体: lift (constOfIsEmpty R _ 1)
  invFun r := r • tprod R (@isEmptyElim _ _ _)
  left_inv x := by
    refine x.induction_on ?_ ?_
    · intro x y
      simp only [map_smulₛₗ, RingHom.id_apply, lift.tprod, constOfIsEmpty_apply, const_apply,
        smul_eq_mul, mul_one]
      congr
      aesop
    · simp

Depends on / 依赖: constOfIsEmpty
-/
def isEmptyEquiv [IsEmpty ι] : (⨂[R] i : ι, s i) ≃ₗ[R] R where
  toFun := lift (constOfIsEmpty R _ 1)
  invFun r := r • tprod R (@isEmptyElim _ _ _)
  left_inv x := by
    refine x.induction_on ?_ ?_
    · intro x y
      simp only [map_smulₛₗ, RingHom.id_apply, lift.tprod, constOfIsEmpty_apply, const_apply,
        smul_eq_mul, mul_one]
      congr
      aesop
    · simp only
      intro x y hx hy
      rw [map_add]; rw [add_smul]; rw [hx]; rw [hy]
  right_inv t := by simp
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
/--
theorem `isEmptyEquiv_apply_tprod` / 定理 `isEmptyEquiv_apply_tprod`

English:
theorem isEmptyEquiv_apply_tprod
  given: [IsEmpty ι] (f : Π i, s i)
  proof: lift.tprod _

中文:
定理 isEmptyEquiv_apply_tprod
  条件: [IsEmpty ι] (f : Π i, s i)
  证明: lift.tprod _

Depends on / 依赖: lift.tprod
-/
theorem isEmptyEquiv_apply_tprod [IsEmpty ι] (f : Π i, s i) :
    isEmptyEquiv ι (tprod R f) = 1 :=
  lift.tprod _

variable {ι}

section subsingleton

variable [Subsingleton ι] (i₀ : ι)

/--
Definition of `subsingletonEquiv` / `subsingletonEquiv` 的定义

English:
definition subsingletonEquiv
  signature: : (⨂[R] i : ι, s i) ≃ₗ[R] s i₀
  body: LinearEquiv.ofLinearMap
    (lift
      { toFun f := f i₀
        map_update_add' m i := by rw [Subsingleton.elim i i₀]; simp
        map_update_smul' m i := by rw [Subsingleton.elim i i₀]; simp })
    ({ toFun x := tprod R (update (0 : (i : ι) -> s i) i₀ x)
       map_add' := by simp
       map_smu

中文:
定义 subsingletonEquiv
  签名: : (⨂[R] i : ι, s i) ≃ₗ[R] s i₀
  定义体: LinearEquiv.ofLinearMap
    (lift
      { toFun f := f i₀
        map_update_add' m i := by rw [Subsingleton.elim i i₀]; simp
        map_update_smul' m i := by rw [Subsingleton.elim i i₀]; simp })
    ({ toFun x := tprod R (update (0 : (i : ι) -> s i) i₀ x)
       map_add' := by simp
       map_smu

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, Subsingleton, Subsingleton.elim, map_add, map_smul, map_update_add, map_update_smul, ofLinearMap, update, update_eq_self
-/
def subsingletonEquiv : (⨂[R] i : ι, s i) ≃ₗ[R] s i₀ :=
  LinearEquiv.ofLinearMap
    (lift
      { toFun f := f i₀
        map_update_add' m i := by rw [Subsingleton.elim i i₀]; simp
        map_update_smul' m i := by rw [Subsingleton.elim i i₀]; simp })
    ({ toFun x := tprod R (update (0 : (i : ι) -> s i) i₀ x)
       map_add' := by simp
       map_smul' := by simp })
    (by ext _; simp)
    (by
      ext f
      have h : update (0 : (i : ι) -> s i) i₀ (f i₀) = f := update_eq_self i₀ f
      simp [h])

@[simp]
/--
theorem `subsingletonEquiv_apply_tprod` / 定理 `subsingletonEquiv_apply_tprod`

English:
theorem subsingletonEquiv_apply_tprod
  given: (f : (i : ι) -> s i)
  proof: lift.tprod _

中文:
定理 subsingletonEquiv_apply_tprod
  条件: (f : (i : ι) -> s i)
  证明: lift.tprod _

Depends on / 依赖: lift.tprod
-/
theorem subsingletonEquiv_apply_tprod (f : (i : ι) -> s i) :
    subsingletonEquiv i₀ (⨂ₜ[R] i, f i) = f i₀ := lift.tprod _

/--
theorem `subsingletonEquiv_symm_apply` / 定理 `subsingletonEquiv_symm_apply`

English:
theorem subsingletonEquiv_symm_apply
  given: (x : s i₀)
  proof: rfl

@[simp]

中文:
定理 subsingletonEquiv_symm_apply
  条件: (x : s i₀)
  证明: rfl

@[simp]
-/
theorem subsingletonEquiv_symm_apply (x : s i₀) :
    (subsingletonEquiv i₀).symm x = tprod R (fun i => update (0 : (j : ι) -> s j) i₀ x i) := rfl

@[simp]
/--
lemma `subsingletonEquiv_symm_apply'` / 引理 `subsingletonEquiv_symm_apply'`

English:
lemma subsingletonEquiv_symm_apply'
  given: (x : M)
  proof: by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod]

中文:
引理 subsingletonEquiv_symm_apply'
  条件: (x : M)
  证明: by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod, symm_apply_eq
-/
lemma subsingletonEquiv_symm_apply' (x : M) :
  (subsingletonEquiv (s := fun _ => M) i₀).symm x = (tprod R fun _ => x) := by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod]

end subsingleton

variable (R M)

section tmulEquivDep

variable (N : ι oplus ι₂ -> Type*) [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tmulEquivDep` / `tmulEquivDep` 的定义

English:
definition tmulEquivDep
  signature: :
  body: LinearEquiv.ofLinearMap
    (TensorProduct.lift
      { toFun a := PiTensorProduct.lift (PiTensorProduct.lift
          (MultilinearMap.currySumEquiv (tprod R)) a)
        map_add' := by simp
        map_smul' := by simp })
    (PiTensorProduct.lift (MultilinearMap.domCoprodDep (tprod R) (tprod R)))

中文:
定义 tmulEquivDep
  签名: :
  定义体: LinearEquiv.ofLinearMap
    (TensorProduct.lift
      { toFun a := PiTensorProduct.lift (PiTensorProduct.lift
          (MultilinearMap.currySumEquiv (tprod R)) a)
        map_add' := by simp
        map_smul' := by simp })
    (PiTensorProduct.lift (MultilinearMap.domCoprodDep (tprod R) (tprod R)))

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.coe_mk, MultilinearMap, MultilinearMap.currySumEquiv, MultilinearMap.domCoprodDep, PiTensorProduct, PiTensorProduct.lift, TensorProduct, TensorProduct.ext, TensorProduct.lift, coe_mk, currySumEquiv, currySum_apply, domCoprodDep, domCoprodDep_apply, lift.tmul
-/
def tmulEquivDep :
    (⨂[R] i₁, N (.inl i₁)) otimes[R] (⨂[R] i₂, N (.inr i₂)) ≃ₗ[R] ⨂[R] i, N i :=
  LinearEquiv.ofLinearMap
    (TensorProduct.lift
      { toFun a := PiTensorProduct.lift (PiTensorProduct.lift
          (MultilinearMap.currySumEquiv (tprod R)) a)
        map_add' := by simp
        map_smul' := by simp })
    (PiTensorProduct.lift (MultilinearMap.domCoprodDep (tprod R) (tprod R))) (by
      ext
      dsimp
      simp only [lift.tprod, domCoprodDep_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
        currySum_apply]
      congr
      ext (_ | _) <;> simp)
    (TensorProduct.ext (by aesop))

@[simp]
/--
lemma `tmulEquivDep_apply` / 引理 `tmulEquivDep_apply`

English:
lemma tmulEquivDep_apply
  statement: (a : (i₁ : ι) -> N (.inl i₁))
  proof: by
  simp [tmulEquivDep]

@[simp]

中文:
引理 tmulEquivDep_apply
  结论: (a : (i₁ : ι) -> N (.inl i₁))
  证明: by
  simp [tmulEquivDep]

@[simp]

Depends on / 依赖: tmulEquivDep
-/
lemma tmulEquivDep_apply (a : (i₁ : ι) -> N (.inl i₁))
    (b : (i₂ : ι₂) -> N (.inr i₂)) :
      tmulEquivDep R N ((⨂ₜ[R] i₁, a i₁) otimesₜ (⨂ₜ[R] i₂, b i₂)) =
        (⨂ₜ[R] i, Sum.rec a b i) := by
  simp [tmulEquivDep]

@[simp]
/--
lemma `tmulEquivDep_symm_apply` / 引理 `tmulEquivDep_symm_apply`

English:
lemma tmulEquivDep_symm_apply
  given: (f : (i : ι oplus ι₂) -> N i)
  proof: by
  simp [tmulEquivDep]

中文:
引理 tmulEquivDep_symm_apply
  条件: (f : (i : ι oplus ι₂) -> N i)
  证明: by
  simp [tmulEquivDep]

Depends on / 依赖: tmulEquivDep
-/
lemma tmulEquivDep_symm_apply (f : (i : ι oplus ι₂) -> N i) :
    (tmulEquivDep R N).symm (⨂ₜ[R] i, f i) =
      ((⨂ₜ[R] i₁, f (.inl i₁)) otimesₜ (⨂ₜ[R] i₂, f (.inr i₂))) := by
  simp [tmulEquivDep]

end tmulEquivDep

section tmulEquiv

/--
Definition of `tmulEquiv` / `tmulEquiv` 的定义

English:
definition tmulEquiv
  signature: :
  body: tmulEquivDep R (fun _ => M)

@[simp]

中文:
定义 tmulEquiv
  签名: :
  定义体: tmulEquivDep R (fun _ => M)

@[simp]

Depends on / 依赖: tmulEquivDep
-/
def tmulEquiv :
    (⨂[R] (_ : ι), M) otimes[R] (⨂[R] (_ : ι₂), M) ≃ₗ[R] ⨂[R] (_ : ι oplus ι₂), M :=
  tmulEquivDep R (fun _ => M)

@[simp]
/--
theorem `tmulEquiv_apply` / 定理 `tmulEquiv_apply`

English:
theorem tmulEquiv_apply
  given: (a : ι -> M) (b : ι₂ -> M)
  proof: by
  simp [tmulEquiv, Sum.elim]

@[simp]

中文:
定理 tmulEquiv_apply
  条件: (a : ι -> M) (b : ι₂ -> M)
  证明: by
  simp [tmulEquiv, Sum.elim]

@[simp]

Depends on / 依赖: Sum.elim, tmulEquiv
-/
theorem tmulEquiv_apply (a : ι -> M) (b : ι₂ -> M) :
    tmulEquiv R M ((⨂ₜ[R] i, a i) otimesₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, Sum.elim a b i := by
  simp [tmulEquiv, Sum.elim]

@[simp]
/--
theorem `tmulEquiv_symm_apply` / 定理 `tmulEquiv_symm_apply`

English:
theorem tmulEquiv_symm_apply
  given: (a : ι oplus ι₂ -> M)
  proof: by
  simp [tmulEquiv]

中文:
定理 tmulEquiv_symm_apply
  条件: (a : ι oplus ι₂ -> M)
  证明: by
  simp [tmulEquiv]

Depends on / 依赖: tmulEquiv
-/
theorem tmulEquiv_symm_apply (a : ι oplus ι₂ -> M) :
    (tmulEquiv R M).symm (⨂ₜ[R] i, a i) =
      (⨂ₜ[R] i, a (Sum.inl i)) otimesₜ[R] (⨂ₜ[R] i, a (Sum.inr i)) := by
  simp [tmulEquiv]

end tmulEquiv

end Multilinear

end PiTensorProduct

end Semiring

section Ring

namespace PiTensorProduct

open PiTensorProduct

open TensorProduct

variable {ι : Type*} {R : Type*} [CommRing R]
variable {s : ι -> Type*} [forall i, AddCommGroup (s i)] [forall i, Module R (s i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (⨂[R] i, s i)
  body: Module.addCommMonoidToAddCommGroup R

中文:
实例 :
  签名: AddCommGroup (⨂[R] i, s i)
  定义体: Module.addCommMonoidToAddCommGroup R

Depends on / 依赖: Module, Module.addCommMonoidToAddCommGroup, addCommMonoidToAddCommGroup
-/
instance : AddCommGroup (⨂[R] i, s i) :=
  Module.addCommMonoidToAddCommGroup R

end PiTensorProduct

end Ring
