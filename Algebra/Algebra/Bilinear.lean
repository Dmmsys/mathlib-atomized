/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `Algebra.Algebra.Basic`,
in order to avoid importing `LinearAlgebra.BilinearMap` and
`LinearAlgebra.TensorProduct` unnecessarily.
-/

@[expose] public section

open TensorProduct Module

variable {R A B : Type*}

namespace LinearMap

section NonUnitalNonAssoc

variable (R A) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[instance_reducible, simps!]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : A ->ₗ[R] A ->ₗ[R] A
  body: LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

中文:
定义 mul
  签名: : A ->ₗ[R] A ->ₗ[R] A
  定义体: LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

Depends on / 依赖: LinearMap, LinearMap.mk, add_mul, mul_add, mul_smul_comm, smul_mul_assoc
-/
def mul : A ->ₗ[R] A ->ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

/--
Definition of `mul'` / `mul'` 的定义

English:
definition mul'
  signature: : A otimes[R] A ->ₗ[R] A
  body: TensorProduct.lift (mul R A)

@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ" => LinearMap.mul' _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ[" R "]" => LinearMap.mul' R _

中文:
定义 mul'
  签名: : A otimes[R] A ->ₗ[R] A
  定义体: TensorProduct.lift (mul R A)

@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ" => LinearMap.mul' _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ[" R "]" => LinearMap.mul' R _

Depends on / 依赖: TensorProduct, TensorProduct.lift
-/
def mul' : A otimes[R] A ->ₗ[R] A :=
  TensorProduct.lift (mul R A)

@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ" => LinearMap.mul' _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ[" R "]" => LinearMap.mul' R _

variable {A R}

@[simp]
/--
theorem `mul_apply'` / 定理 `mul_apply'`

English:
theorem mul_apply'
  given: (a b : A)
  statement: mul R A a b = a * b
  proof: rfl

@[simp]

中文:
定理 mul_apply'
  条件: (a b : A)
  结论: mul R A a b = a * b
  证明: rfl

@[simp]
-/
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
  rfl

@[simp]
/--
theorem `mul'_apply` / 定理 `mul'_apply`

English:
theorem mul'_apply
  given: {a b : A}
  statement: mul' R A (a otimesₜ b) = a * b
  proof: rfl

中文:
定理 mul'_apply
  条件: {a b : A}
  结论: mul' R A (a otimesₜ b) = a * b
  证明: rfl
-/
theorem mul'_apply {a b : A} : mul' R A (a otimesₜ b) = a * b :=
  rfl

/--
lemma `restrictScalars_mul` / 引理 `restrictScalars_mul`

English:
lemma restrictScalars_mul
  statement: {S : Type*} [CommSemiring S] [Module S A] [SMulCommClass S A A]
  proof: by
  ext x
  simp

中文:
引理 restrictScalars_mul
  结论: {S : 类型} [交换半环 S] [模 S A] [标量交换类 S A A]
  证明: by
  ext x
  simp
-/
lemma restrictScalars_mul {S : Type*} [CommSemiring S] [Module S A] [SMulCommClass S A A]
    [IsScalarTower S A A] [CompatibleSMul A A R S] (a : A) :
    LinearMap.restrictScalars R (LinearMap.mul S A a) = LinearMap.mul R A a := by
  ext x
  simp

variable {M : Type*} [AddCommMonoid M] [Module R M]

/--
theorem `lift_lsmul_mul_eq_lsmul_lift_lsmul` / 定理 `lift_lsmul_mul_eq_lsmul_lift_lsmul`

English:
theorem lift_lsmul_mul_eq_lsmul_lift_lsmul
  given: {r : R}
  proof: by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

中文:
定理 lift_lsmul_mul_eq_lsmul_lift_lsmul
  条件: {r : R}
  证明: by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

Depends on / 依赖: TensorProduct, TensorProduct.ext, mul_comm, mul_smul
-/
theorem lift_lsmul_mul_eq_lsmul_lift_lsmul {r : R} :
    lift (lsmul R M ∘ₗ mul R R r) = lsmul R M r ∘ₗ lift (lsmul R M) := by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

end NonUnitalNonAssoc

section NonUnital

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
variable [SMulCommClass R B B] [IsScalarTower R B B]

variable (R A) in
/--
Definition of `_root_.NonUnitalAlgHom.lmul` / `_root_.NonUnitalAlgHom.lmul` 的定义

English:
definition _root_.NonUnitalAlgHom.lmul
  signature: : A ->ₙₐ[R] End R A where
  body: mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

@[simp]

中文:
定义 _root_.非幺Alg态射.lmul
  签名: : A ->ₙₐ[R] End R A where
  定义体: mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

@[simp]
-/
def _root_.NonUnitalAlgHom.lmul : A ->ₙₐ[R] End R A where
  __ := mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

@[simp]
/--
theorem `_root_.NonUnitalAlgHom.coe_lmul_eq_mul` / 定理 `_root_.NonUnitalAlgHom.coe_lmul_eq_mul`

English:
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul
  statement: ⇑(NonUnitalAlgHom.lmul R A) = mul R A
  proof: rfl

中文:
定理 _root_.非幺Alg态射.coe_lmul_eq_mul
  结论: ⇑(非幺Alg态射.lmul R A) = mul R A
  证明: rfl
-/
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl

/--
theorem `commute_mulLeft_right` / 定理 `commute_mulLeft_right`

English:
theorem commute_mulLeft_right
  given: (a b : A)
  statement: Commute (mulLeft R a) (mulRight R b)
  proof: by
  ext c
  exact (mul_assoc a c b).symm

中文:
定理 commute_mulLeft_right
  条件: (a b : A)
  结论: Commute (mulLeft R a) (mulRight R b)
  证明: by
  ext c
  exact (mul_assoc a c b).symm

Depends on / 依赖: mul_assoc
-/
theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

/--
theorem `map_mul_iff` / 定理 `map_mul_iff`

English:
theorem map_mul_iff
  given: (f : A ->ₗ[R] B)
  proof: Iff.symm LinearMap.ext_iff₂

中文:
定理 map_mul_iff
  条件: (f : A ->ₗ[R] B)
  证明: Iff.symm LinearMap.ext_iff₂

Depends on / 依赖: Iff.symm, LinearMap, LinearMap.ext_iff
-/
theorem map_mul_iff (f : A ->ₗ[R] B) :
    (forall x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f :=
  Iff.symm LinearMap.ext_iff₂

end NonUnital

section Semiring

variable (R A)
section one_side
variable [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

@[simp]
/--
theorem `pow_mulLeft` / 定理 `pow_mulLeft`

English:
theorem pow_mulLeft
  given: (a : A) (n : Nat)
  statement: mulLeft R a ^ n = mulLeft R (a ^ n)
  proof: match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

中文:
定理 pow_mulLeft
  条件: (a : A) (n : 自然数)
  结论: mulLeft R a ^ n = mulLeft R (a ^ n)
  证明: match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

Depends on / 依赖: Module, Module.End.mul_eq_comp, Module.End.one_eq_id, mulLeft_mul, mulLeft_one, mul_eq_comp, one_eq_id, pow_mulLeft, pow_succ, pow_zero
-/
theorem pow_mulLeft (a : A) (n : Nat) : mulLeft R a ^ n = mulLeft R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

end left

section right
variable [Module R A] [IsScalarTower R A A]

@[simp]
/--
theorem `pow_mulRight` / 定理 `pow_mulRight`

English:
theorem pow_mulRight
  given: (a : A) (n : Nat)
  statement: mulRight R a ^ n = mulRight R (a ^ n)
  proof: match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

中文:
定理 pow_mulRight
  条件: (a : A) (n : 自然数)
  结论: mulRight R a ^ n = mulRight R (a ^ n)
  证明: match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

Depends on / 依赖: Module, Module.End.mul_eq_comp, Module.End.one_eq_id, mulRight_mul, mulRight_one, mul_eq_comp, one_eq_id, pow_mulRight, pow_succ, pow_zero
-/
theorem pow_mulRight (a : A) (n : Nat) : mulRight R a ^ n = mulRight R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

end right

end one_side

variable [CommSemiring R] [Semiring A] [Algebra R A]

/--
Definition of `_root_.Algebra.lmul` / `_root_.Algebra.lmul` 的定义

English:
definition _root_.Algebra.lmul
  signature: : A ->ₐ[R] End R A where
  body: NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm

中文:
定义 _root_.代数.lmul
  签名: : A ->ₐ[R] End R A where
  定义体: NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.lmul
-/
def _root_.Algebra.lmul : A ->ₐ[R] End R A where
  __ := NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm

variable {R A}

@[simp]
/--
theorem `_root_.Algebra.coe_lmul_eq_mul` / 定理 `_root_.Algebra.coe_lmul_eq_mul`

English:
theorem _root_.Algebra.coe_lmul_eq_mul
  statement: ⇑(Algebra.lmul R A) = mul R A
  proof: rfl

中文:
定理 _root_.代数.coe_lmul_eq_mul
  结论: ⇑(代数.lmul R A) = mul R A
  证明: rfl
-/
theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl

/--
theorem `_root_.Algebra.lmul_injective` / 定理 `_root_.Algebra.lmul_injective`

English:
theorem _root_.Algebra.lmul_injective
  statement: Function.Injective (Algebra.lmul R A)
  proof: fun a₁ a₂ h => by simpa using DFunLike.congr_fun h 1

中文:
定理 _root_.代数.lmul_injective
  结论: 函数.单射 (代数.lmul R A)
  证明: fun a₁ a₂ h => by simpa using DFunLike.congr_fun h 1

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) :=
  fun a₁ a₂ h => by simpa using DFunLike.congr_fun h 1

/--
theorem `_root_.Algebra.lmul_isUnit_iff` / 定理 `_root_.Algebra.lmul_isUnit_iff`

English:
theorem _root_.Algebra.lmul_isUnit_iff
  given: {x : A}
  proof: by
  rw [Module.End.isUnit_iff]; rw [Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

中文:
定理 _root_.代数.lmul_isUnit_iff
  条件: {x : A}
  证明: by
  rw [Module.End.isUnit_iff]; rw [Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

Depends on / 依赖: Iff.comm, IsUnit, IsUnit.isUnit_iff_mulLeft_bijective, Module, Module.End.isUnit_iff, isUnit_iff, isUnit_iff_mulLeft_bijective
-/
theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End.isUnit_iff]; rw [Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

/--
theorem `toSpanSingleton_one_eq_algebraLinearMap` / 定理 `toSpanSingleton_one_eq_algebraLinearMap`

English:
theorem toSpanSingleton_one_eq_algebraLinearMap
  proof: by ext; simp

中文:
定理 toSpanSingleton_one_eq_algebraLinearMap
  证明: by ext; simp
-/
theorem toSpanSingleton_one_eq_algebraLinearMap :
    toSpanSingleton R A 1 = Algebra.linearMap R A := by ext; simp

variable (R A) in
/--
Definition of `mul''` / `mul''` 的定义

English:
definition mul''
  signature: : A otimes[R] A ->ₗ[A] A where
  body: mul' R A
  map_smul' a x := x.induction_on (by simp) (by simp +contextual [mul', smul_tmul', mul_assoc])
    (by simp +contextual [mul_add])

中文:
定义 mul''
  签名: : A otimes[R] A ->ₗ[A] A where
  定义体: mul' R A
  map_smul' a x := x.induction_on (by simp) (by simp +contextual [mul', smul_tmul', mul_assoc])
    (by simp +contextual [mul_add])
-/
@[simps!] def mul'' : A otimes[R] A ->ₗ[A] A where
  __ := mul' R A
  map_smul' a x := x.induction_on (by simp) (by simp +contextual [mul', smul_tmul', mul_assoc])
    (by simp +contextual [mul_add])

end Semiring

section CommSemiring
variable [CommSemiring R] [NonUnitalNonAssocCommSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/--
lemma `flip_mul` / 引理 `flip_mul`

English:
lemma flip_mul
  statement: (mul R A).flip = mul R A
  proof: by ext; simp [mul_comm]

中文:
引理 flip_mul
  结论: (mul R A).flip = mul R A
  证明: by ext; simp [mul_comm]
-/
@[simp] lemma flip_mul : (mul R A).flip = mul R A := by ext; simp [mul_comm]

/--
lemma `mul'_comp_comm` / 引理 `mul'_comp_comm`

English:
lemma mul'_comp_comm
  statement: mul' R A ∘ₗ TensorProduct.comm R A A = mul' R A
  proof: by
  simp [mul', lift_comp_comm_eq]

中文:
引理 mul'_comp_comm
  结论: mul' R A ∘ₗ 张量积.comm R A A = mul' R A
  证明: by
  simp [mul', lift_comp_comm_eq]
-/
lemma mul'_comp_comm : mul' R A ∘ₗ TensorProduct.comm R A A = mul' R A := by
  simp [mul', lift_comp_comm_eq]

/--
lemma `mul'_comm` / 引理 `mul'_comm`

English:
lemma mul'_comm
  given: (x : A otimes[R] A)
  statement: mul' R A (TensorProduct.comm R A A x) = mul' R A x
  proof: congr($mul'_comp_comm _)

中文:
引理 mul'_comm
  条件: (x : A otimes[R] A)
  结论: mul' R A (张量积.comm R A A x) = mul' R A x
  证明: congr($mul'_comp_comm _)
-/
lemma mul'_comm (x : A otimes[R] A) : mul' R A (TensorProduct.comm R A A x) = mul' R A x :=
  congr($mul'_comp_comm _)

end CommSemiring
end LinearMap

open scoped RingTheory.LinearMap

namespace NonUnitalAlgHom
variable [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/--
lemma `comp_mul'` / 引理 `comp_mul'`

English:
lemma comp_mul'
  given: (f : A ->ₙₐ[R] B)
  statement: (f : A ->ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f otimesₘ f)
  proof: TensorProduct.ext' by simp

中文:
引理 comp_mul'
  条件: (f : A ->ₙₐ[R] B)
  结论: (f : A ->ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f otimesₘ f)
  证明: TensorProduct.ext' by simp

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
lemma comp_mul' (f : A ->ₙₐ[R] B) : (f : A ->ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f otimesₘ f) :=
TensorProduct.ext' by simp

end NonUnitalAlgHom

namespace AlgHom
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
lemma `comp_mul'` / 引理 `comp_mul'`

English:
lemma comp_mul'
  given: (f : A ->ₐ B)
  statement: f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap otimesₘ f.toLinearMap)
  proof: TensorProduct.ext' by simp

中文:
引理 comp_mul'
  条件: (f : A ->ₐ B)
  结论: f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap otimesₘ f.toLinearMap)
  证明: TensorProduct.ext' by simp

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
lemma comp_mul' (f : A ->ₐ B) : f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap otimesₘ f.toLinearMap) :=
TensorProduct.ext' by simp

end AlgHom
