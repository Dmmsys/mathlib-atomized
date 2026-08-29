/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Binary products: `Prod.instCoalgebra`
* Finitely supported functions: `DFinsupp.instCoalgebra`, `Finsupp.instCoalgebra`
* Finite pi functions: `Pi.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/--
Definition of `CoalgebraStruct` / `CoalgebraStruct` 的定义

English:
class CoalgebraStruct
  parameters: (R : Type u) (A : Type v)
  axioms and operations (2):
    - comul : A ->ₗ[R] A otimes[R] A
    - counit : A ->ₗ[R] R

中文:
类 余algebraStruct
  参数: (R : 类型u) (A : 类型v)
  公理与运算 (2 个):
    - comul : A ->ₗ[R] A otimes[R] A
    - counit : A ->ₗ[R] R
-/
class CoalgebraStruct (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  comul : A ->ₗ[R] A otimes[R] A
  /-- The counit of the coalgebra -/
  counit : A ->ₗ[R] R

@[inherit_doc] scoped[RingTheory.LinearMap] notation "ε" => CoalgebraStruct.counit
@[inherit_doc] scoped[RingTheory.LinearMap] notation "δ" => CoalgebraStruct.comul

/--
Definition of `Coalgebra.Repr` / `Coalgebra.Repr` 的定义

English:
structure Coalgebra.Repr
  parameters: (R : Type u) {A : Type v}
  axioms and operations (4):
    - (index : Finset ι)
    - (left : ι -> A)
    - (right : ι -> A)
    - (eq : ∑ i in index, left i otimesₜ[R] right i = CoalgebraStruct.comul a)

中文:
结构 余algebra.Repr
  参数: (R : 类型u) {A : 类型v}
  公理与运算 (4 个):
    - (index : 有限集 ι)
    - (left : ι -> A)
    - (right : ι -> A)
    - (eq : ∑ i in index, left i otimesₜ[R] right i = 余algebraStruct.comul a)
-/
structure Coalgebra.Repr (R : Type u) {A : Type v}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) (ι : Type*) where
  /-- the finite indexing set of a representation of `comul a` -/
  (index : Finset ι)
  /-- the first coordinate of a representation of `comul a` -/
  (left : ι -> A)
  /-- the second coordinate of a representation of `comul a` -/
  (right : ι -> A)
  /-- `comul a` is equal to a finite sum of some pure tensors -/
  (eq : ∑ i in index, left i otimesₜ[R] right i = CoalgebraStruct.comul a)

/--
Definition of `Coalgebra.Repr.arbitrary` / `Coalgebra.Repr.arbitrary` 的定义

English:
definition Coalgebra.Repr.arbitrary
  signature: (R : Type u) {A : Type v}
  body: Prod.fst
  right := Prod.snd
.choose index := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a)
.choose_spec.symm eq := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a)

@[inherit_doc Coalgebra.Repr.arbitrary]
scoped[Coalgebra] notation "ℛ" => Coalgebra.Repr.arbitrary

中文:
定义 余algebra.Repr.arbitrary
  签名: (R : 类型u) {A : 类型v}
  定义体: Prod.fst
  right := Prod.snd
.choose index := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a)
.choose_spec.symm eq := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a)

@[inherit_doc Coalgebra.Repr.arbitrary]
scoped[Coalgebra] notation "ℛ" => Coalgebra.Repr.arbitrary

Depends on / 依赖: Prod.fst
-/
noncomputable def Coalgebra.Repr.arbitrary (R : Type u) {A : Type v}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) :
    Coalgebra.Repr R a (A × A) where
  left := Prod.fst
  right := Prod.snd
.choose index := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a)
.choose_spec.symm eq := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a)

@[inherit_doc Coalgebra.Repr.arbitrary]
scoped[Coalgebra] notation "ℛ" => Coalgebra.Repr.arbitrary

namespace Coalgebra
export CoalgebraStruct (comul counit)
end Coalgebra

/--
Definition of `Coalgebra` / `Coalgebra` 的定义

English:
class Coalgebra
  parameters: (R : Type u) (A : Type v)
  extends: CoalgebraStruct R A
  axioms and operations (3):
    - coassoc : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
    - rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = TensorProduct.mk R _ _ 1
    - lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (TensorProduct.mk R _ _).flip 1

中文:
类 余algebra
  参数: (R : 类型u) (A : 类型v)
  继承: 余algebraStruct R A
  公理与运算 (3 个):
    - coassoc : 张量积.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
    - rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = 张量积.mk R _ _ 1
    - lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (张量积.mk R _ _).flip 1
-/
class Coalgebra (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] extends CoalgebraStruct R A where
  /-- The comultiplication is coassociative -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
  /-- The counit satisfies the left counitality law -/
  rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = TensorProduct.mk R _ _ 1
  /-- The counit satisfies the right counitality law -/
  lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (TensorProduct.mk R _ _).flip 1

namespace Coalgebra
variable {R : Type u} {A : Type v} {ι : Type*} {κ Λ : ι -> Type*}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] {a : A}

/-- The indexing type of a representation of `comul a` -/
@[nolint unusedArguments, deprecated "The indexing type is now unbundled" (since := "2026-05-31")]
/--
Definition of `Repr.ι` / `Repr.ι` 的定义

English:
abbreviation Repr.ι
  signature: (_repr : Repr R a ι)
  body: ι

@[simp]

中文:
缩写 Repr.ι
  签名: (_repr : Repr R a ι)
  定义体: ι

@[simp]
-/
protected abbrev Repr.ι (_repr : Repr R a ι) : Type _ := ι

@[simp]
/--
theorem `coassoc_apply` / 定理 `coassoc_apply`

English:
theorem coassoc_apply
  given: (a : A)
  proof: LinearMap.congr_fun coassoc a

@[simp]

中文:
定理 coassoc_apply
  条件: (a : A)
  证明: LinearMap.congr_fun coassoc a

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, coassoc, congr_fun
-/
theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A (comul.rTensor A (comul a)) = comul.lTensor A (comul a) :=
  LinearMap.congr_fun coassoc a

@[simp]
/--
theorem `coassoc_symm_apply` / 定理 `coassoc_symm_apply`

English:
theorem coassoc_symm_apply
  given: (a : A)
  proof: by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq]; rw [coassoc_apply a]

@[simp]

中文:
定理 coassoc_symm_apply
  条件: (a : A)
  证明: by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq]; rw [coassoc_apply a]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.assoc, coassoc_apply, symm_apply_eq
-/
theorem coassoc_symm_apply (a : A) :
    (TensorProduct.assoc R A A A).symm (comul.lTensor A (comul a)) = comul.rTensor A (comul a) := by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq]; rw [coassoc_apply a]

@[simp]
/--
theorem `coassoc_symm` / 定理 `coassoc_symm`

English:
theorem coassoc_symm
  proof: LinearMap.ext coassoc_symm_apply

@[simp]

中文:
定理 coassoc_symm
  证明: LinearMap.ext coassoc_symm_apply

@[simp]
-/
theorem coassoc_symm :
    (TensorProduct.assoc R A A A).symm ∘ₗ comul.lTensor A ∘ₗ comul =
    comul.rTensor A ∘ₗ (comul (R := R)) :=
  LinearMap.ext coassoc_symm_apply

@[simp]
/--
theorem `rTensor_counit_comul` / 定理 `rTensor_counit_comul`

English:
theorem rTensor_counit_comul
  given: (a : A)
  statement: counit.rTensor A (comul a) = 1 otimesₜ[R] a
  proof: LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]

中文:
定理 rTensor_counit_comul
  条件: (a : A)
  结论: counit.rTensor A (comul a) = 1 otimesₜ[R] a
  证明: LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, rTensor_counit_comp_comul
-/
theorem rTensor_counit_comul (a : A) : counit.rTensor A (comul a) = 1 otimesₜ[R] a :=
  LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]
/--
theorem `lTensor_counit_comul` / 定理 `lTensor_counit_comul`

English:
theorem lTensor_counit_comul
  given: (a : A)
  statement: counit.lTensor A (comul a) = a otimesₜ[R] 1
  proof: LinearMap.congr_fun lTensor_counit_comp_comul a

@[simp]

中文:
定理 lTensor_counit_comul
  条件: (a : A)
  结论: counit.lTensor A (comul a) = a otimesₜ[R] 1
  证明: LinearMap.congr_fun lTensor_counit_comp_comul a

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lTensor_counit_comp_comul
-/
theorem lTensor_counit_comul (a : A) : counit.lTensor A (comul a) = a otimesₜ[R] 1 :=
  LinearMap.congr_fun lTensor_counit_comp_comul a

@[simp]
/--
lemma `sum_counit_tmul_eq` / 引理 `sum_counit_tmul_eq`

English:
lemma sum_counit_tmul_eq
  given: (repr : Repr R a ι)
  proof: by
  simpa [← repr.eq, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

@[simp]

中文:
引理 sum_counit_tmul_eq
  条件: (repr : Repr R a ι)
  证明: by
  simpa [← repr.eq, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

@[simp]

Depends on / 依赖: map_sum, rTensor_counit_comp_comul, repr.eq, repr.left, repr.right
-/
lemma sum_counit_tmul_eq (repr : Repr R a ι) :
    ∑ i in repr.index, counit (R := R) (repr.left i) otimesₜ (repr.right i) = 1 otimesₜ[R] a := by
  simpa [← repr.eq, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

@[simp]
/--
lemma `sum_tmul_counit_eq` / 引理 `sum_tmul_counit_eq`

English:
lemma sum_tmul_counit_eq
  given: (repr : Repr R a ι)
  proof: by
  simpa [← repr.eq, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

中文:
引理 sum_tmul_counit_eq
  条件: (repr : Repr R a ι)
  证明: by
  simpa [← repr.eq, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

Depends on / 依赖: lTensor_counit_comp_comul, map_sum, repr.eq, repr.right
-/
lemma sum_tmul_counit_eq (repr : Repr R a ι) :
    ∑ i in repr.index, (repr.left i) otimesₜ counit (R := R) (repr.right i) = a otimesₜ[R] 1 := by
  simpa [← repr.eq, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

-- Cannot be @[simp] because `a₂` cannot be inferred by `simp`.
/--
lemma `sum_tmul_tmul_eq` / 引理 `sum_tmul_tmul_eq`

English:
lemma sum_tmul_tmul_eq
  statement: (repr : Repr R a ι)
  proof: by
  simpa [(a₂ _).eq, ← (a₁ _).eq, ← TensorProduct.tmul_sum,
TensorProduct.sum_tmul, ← repr.eq] using congr( (coassoc (R := R)) a)

@[simp]

中文:
引理 sum_tmul_tmul_eq
  结论: (repr : Repr R a ι)
  证明: by
  simpa [(a₂ _).eq, ← (a₁ _).eq, ← TensorProduct.tmul_sum,
TensorProduct.sum_tmul, ← repr.eq] using congr( (coassoc (R := R)) a)

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.sum_tmul, TensorProduct.tmul_sum, coassoc, repr.eq, sum_tmul, tmul_sum
-/
lemma sum_tmul_tmul_eq (repr : Repr R a ι)
    (a₁ : (i : ι) -> Repr R (repr.left i) (κ i)) (a₂ : (i : ι) -> Repr R (repr.right i) (Λ i)) :
    ∑ i in repr.index, ∑ j in (a₁ i).index,
      (a₁ i).left j otimesₜ[R] ((a₁ i).right j otimesₜ[R] repr.right i)
      = ∑ i in repr.index, ∑ j in (a₂ i).index,
      repr.left i otimesₜ[R] ((a₂ i).left j otimesₜ[R] (a₂ i).right j) := by
  simpa [(a₂ _).eq, ← (a₁ _).eq, ← TensorProduct.tmul_sum,
TensorProduct.sum_tmul, ← repr.eq] using congr( (coassoc (R := R)) a)

@[simp]
/--
theorem `sum_counit_tmul_map_eq` / 定理 `sum_counit_tmul_map_eq`

English:
theorem sum_counit_tmul_map_eq
  statement: {B : Type*} [AddCommMonoid B] [Module R B]
  proof: by
  have := sum_counit_tmul_eq repr
  apply_fun LinearMap.lTensor R (f : A ->ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.lTensor_tmul, LinearMap.coe_coe]

@[simp]

中文:
定理 sum_counit_tmul_map_eq
  结论: {B : 类型} [加法交换幺半群 B] [模 R B]
  证明: by
  have := sum_counit_tmul_eq repr
  apply_fun LinearMap.lTensor R (f : A ->ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.lTensor_tmul, LinearMap.coe_coe]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.coe_coe, LinearMap.lTensor, LinearMap.lTensor_tmul, apply_fun, coe_coe, lTensor, lTensor_tmul, map_sum, repr.left, repr.right, sum_counit_tmul_eq
-/
theorem sum_counit_tmul_map_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a ι} :
    ∑ i in repr.index, counit (R := R) (repr.left i) otimesₜ f (repr.right i) = 1 otimesₜ[R] f a := by
  have := sum_counit_tmul_eq repr
  apply_fun LinearMap.lTensor R (f : A ->ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.lTensor_tmul, LinearMap.coe_coe]

@[simp]
/--
theorem `sum_map_tmul_counit_eq` / 定理 `sum_map_tmul_counit_eq`

English:
theorem sum_map_tmul_counit_eq
  statement: {B : Type*} [AddCommMonoid B] [Module R B]
  proof: by
  have := sum_tmul_counit_eq repr
  apply_fun LinearMap.rTensor R (f : A ->ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.rTensor_tmul, LinearMap.coe_coe]

中文:
定理 sum_map_tmul_counit_eq
  结论: {B : 类型} [加法交换幺半群 B] [模 R B]
  证明: by
  have := sum_tmul_counit_eq repr
  apply_fun LinearMap.rTensor R (f : A ->ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.rTensor_tmul, LinearMap.coe_coe]

Depends on / 依赖: LinearMap, LinearMap.coe_coe, LinearMap.rTensor, LinearMap.rTensor_tmul, apply_fun, coe_coe, map_sum, rTensor, rTensor_tmul, repr.right, sum_tmul_counit_eq
-/
theorem sum_map_tmul_counit_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a ι} :
    ∑ i in repr.index, f (repr.left i) otimesₜ counit (R := R) (repr.right i) = f a otimesₜ[R] 1 := by
  have := sum_tmul_counit_eq repr
  apply_fun LinearMap.rTensor R (f : A ->ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.rTensor_tmul, LinearMap.coe_coe]

-- Cannot be @[simp] because `a₁` cannot be inferred by `simp`.
/--
theorem `sum_map_tmul_tmul_eq` / 定理 `sum_map_tmul_tmul_eq`

English:
theorem sum_map_tmul_tmul_eq
  statement: {B : Type*} [AddCommMonoid B] [Module R B]
  proof: by
  have := sum_tmul_tmul_eq repr a₁ a₂
  apply_fun TensorProduct.map (f : A ->ₗ[R] B)
    (TensorProduct.map (g : A ->ₗ[R] B) (h : A ->ₗ[R] B)) at this
  simp_all only [map_sum, TensorProduct.map_tmul, LinearMap.coe_coe]

中文:
定理 sum_map_tmul_tmul_eq
  结论: {B : 类型} [加法交换幺半群 B] [模 R B]
  证明: by
  have := sum_tmul_tmul_eq repr a₁ a₂
  apply_fun TensorProduct.map (f : A ->ₗ[R] B)
    (TensorProduct.map (g : A ->ₗ[R] B) (h : A ->ₗ[R] B)) at this
  simp_all only [map_sum, TensorProduct.map_tmul, LinearMap.coe_coe]

Depends on / 依赖: LinearMap, LinearMap.coe_coe, TensorProduct, TensorProduct.map, TensorProduct.map_tmul, apply_fun, coe_coe, map_sum, map_tmul, sum_tmul_tmul_eq
-/
theorem sum_map_tmul_tmul_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f g h : F) (a : A) {repr : Repr R a ι}
    {a₁ : (i : ι) -> Repr R (repr.left i) (κ i)} {a₂ : (i : ι) -> Repr R (repr.right i) (Λ i)} :
    ∑ i in repr.index, ∑ j in (a₂ i).index,
      f (repr.left i) otimesₜ (g ((a₂ i).left j) otimesₜ h ((a₂ i).right j)) =
    ∑ i in repr.index, ∑ j in (a₁ i).index,
      f ((a₁ i).left j) otimesₜ[R] (g ((a₁ i).right j) otimesₜ[R] h (repr.right i)) := by
  have := sum_tmul_tmul_eq repr a₁ a₂
  apply_fun TensorProduct.map (f : A ->ₗ[R] B)
    (TensorProduct.map (g : A ->ₗ[R] B) (h : A ->ₗ[R] B)) at this
  simp_all only [map_sum, TensorProduct.map_tmul, LinearMap.coe_coe]

/--
lemma `sum_counit_smul` / 引理 `sum_counit_smul`

English:
lemma sum_counit_smul
  given: (𝓡 : Repr R a ι)
  proof: by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.lsmul_apply, one_smul]
    using congr(TensorProduct.lift (LinearMap.lsmul R A) $(sum_counit_tmul_eq (R := R) 𝓡))

中文:
引理 sum_counit_smul
  条件: (𝓡 : Repr R a ι)
  证明: by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.lsmul_apply, one_smul]
    using congr(TensorProduct.lift (LinearMap.lsmul R A) $(sum_counit_tmul_eq (R := R) 𝓡))

Depends on / 依赖: LinearMap, LinearMap.lsmul, LinearMap.lsmul_apply, TensorProduct, TensorProduct.lift, TensorProduct.lift.tmul, lsmul_apply, map_sum, one_smul, sum_counit_tmul_eq
-/
lemma sum_counit_smul (𝓡 : Repr R a ι) :
    ∑ x in 𝓡.index, counit (R := R) (𝓡.left x) • 𝓡.right x = a := by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.lsmul_apply, one_smul]
    using congr(TensorProduct.lift (LinearMap.lsmul R A) $(sum_counit_tmul_eq (R := R) 𝓡))

/--
lemma `lift_lsmul_comp_counit_comp_comul` / 引理 `lift_lsmul_comp_counit_comp_comul`

English:
lemma lift_lsmul_comp_counit_comp_comul
  proof: by
  have := rTensor_counit_comp_comul (R := R) (A := A)
  apply_fun (TensorProduct.lift (LinearMap.lsmul R A) ∘ₗ ·) at this
  rw [LinearMap.rTensor]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.lift_comp_map]; rw [LinearMap.compl₂_id]
    at this
  ext
  simp [this]

中文:
引理 lift_lsmul_comp_counit_comp_comul
  证明: by
  have := rTensor_counit_comp_comul (R := R) (A := A)
  apply_fun (TensorProduct.lift (LinearMap.lsmul R A) ∘ₗ ·) at this
  rw [LinearMap.rTensor]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.lift_comp_map]; rw [LinearMap.compl₂_id]
    at this
  ext
  simp [this]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, LinearMap.compl, LinearMap.lsmul, LinearMap.rTensor, TensorProduct, TensorProduct.lift, TensorProduct.lift_comp_map, apply_fun, comp_assoc, lift_comp_map, rTensor, rTensor_counit_comp_comul
-/
lemma lift_lsmul_comp_counit_comp_comul :
    TensorProduct.lift (.lsmul R A ∘ₗ counit) ∘ₗ comul = .id := by
  have := rTensor_counit_comp_comul (R := R) (A := A)
  apply_fun (TensorProduct.lift (LinearMap.lsmul R A) ∘ₗ ·) at this
  rw [LinearMap.rTensor]; rw [← LinearMap.comp_assoc]; rw [TensorProduct.lift_comp_map]; rw [LinearMap.compl₂_id]
    at this
  ext
  simp [this]

variable (R A) in
/--
Definition of `IsCocomm` / `IsCocomm` 的定义

English:
class IsCocomm
  parameters: where
  axioms and operations (1):
    - comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul

中文:
类 是余comm
  参数: where
  公理与运算 (1 个):
    - comm_comp_comul : (张量积.comm R A A).comp comul = comul
-/
class IsCocomm where
  protected comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul

variable [IsCocomm R A]

variable (R A) in
/--
lemma `comm_comp_comul` / 引理 `comm_comp_comul`

English:
lemma comm_comp_comul
  statement: (TensorProduct.comm R A A).comp comul = comul
  proof: IsCocomm.comm_comp_comul

中文:
引理 comm_comp_comul
  结论: (张量积.comm R A A).comp comul = comul
  证明: IsCocomm.comm_comp_comul
-/
@[simp] lemma comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul :=
  IsCocomm.comm_comp_comul

variable (R) in
/--
lemma `comm_comul` / 引理 `comm_comul`

English:
lemma comm_comul
  given: (a : A)
  statement: TensorProduct.comm R A A (comul a) = comul a
  proof: congr($(comm_comp_comul R A) a)

中文:
引理 comm_comul
  条件: (a : A)
  结论: 张量积.comm R A A (comul a) = comul a
  证明: congr($(comm_comp_comul R A) a)
-/
@[simp] lemma comm_comul (a : A) : TensorProduct.comm R A A (comul a) = comul a :=
  congr($(comm_comp_comul R A) a)

end Coalgebra

open Coalgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

/--
Instance `toCoalgebra` / 实例 `toCoalgebra`

English:
instance toCoalgebra
  signature: : Coalgebra R R where
  body: (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]

中文:
实例 toCoalgebra
  签名: : 余algebra R R where
  定义体: (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.mk
-/
instance toCoalgebra : Coalgebra R R where
  comul := (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]
/--
theorem `comul_apply` / 定理 `comul_apply`

English:
theorem comul_apply
  given: (r : R)
  statement: comul r = 1 otimesₜ[R] r
  proof: rfl

@[simp]

中文:
定理 comul_apply
  条件: (r : R)
  结论: comul r = 1 otimesₜ[R] r
  证明: rfl

@[simp]
-/
theorem comul_apply (r : R) : comul r = 1 otimesₜ[R] r := rfl

@[simp]
/--
theorem `counit_apply` / 定理 `counit_apply`

English:
theorem counit_apply
  given: (r : R)
  statement: counit r = r
  proof: rfl

中文:
定理 counit_apply
  条件: (r : R)
  结论: counit r = r
  证明: rfl
-/
theorem counit_apply (r : R) : counit r = r := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCocomm R R
  body: by ext; simp

中文:
实例 :
  签名: 是余comm R R
  定义体: by ext; simp
-/
instance : IsCocomm R R where comm_comp_comul := by ext; simp

end CommSemiring

namespace Prod
variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

open LinearMap

/--
Instance `instCoalgebraStruct` / 实例 `instCoalgebraStruct`

English:
instance instCoalgebraStruct
  signature: : CoalgebraStruct R (A × B) where
  body: .coprod
    (TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul)
    (TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul)
  counit := .coprod counit counit

@[simp]

中文:
实例 instCoalgebraStruct
  签名: : 余algebraStruct R (A × B) where
  定义体: .coprod
    (TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul)
    (TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul)
  counit := .coprod counit counit

@[simp]

Depends on / 依赖: coprod
-/
instance instCoalgebraStruct : CoalgebraStruct R (A × B) where
  comul := .coprod
    (TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul)
    (TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul)
  counit := .coprod counit counit

@[simp]
/--
theorem `comul_apply` / 定理 `comul_apply`

English:
theorem comul_apply
  given: (r : A × B)
  proof: rfl

@[simp]

中文:
定理 comul_apply
  条件: (r : A × B)
  证明: rfl

@[simp]
-/
theorem comul_apply (r : A × B) :
    comul r =
      TensorProduct.map (.inl R A B) (.inl R A B) (comul r.1) +
      TensorProduct.map (.inr R A B) (.inr R A B) (comul r.2) := rfl

@[simp]
/--
theorem `counit_apply` / 定理 `counit_apply`

English:
theorem counit_apply
  given: (r : A × B)
  statement: (counit r : R) = counit r.1 + counit r.2
  proof: rfl

中文:
定理 counit_apply
  条件: (r : A × B)
  结论: (counit r : R) = counit r.1 + counit r.2
  证明: rfl
-/
theorem counit_apply (r : A × B) : (counit r : R) = counit r.1 + counit r.2 := rfl

/--
theorem `comul_comp_inl` / 定理 `comul_comp_inl`

English:
theorem comul_comp_inl
  proof: by
  ext; simp

中文:
定理 comul_comp_inl
  证明: by
  ext; simp
-/
theorem comul_comp_inl :
    comul ∘ₗ inl R A B = TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul := by
  ext; simp

/--
theorem `comul_comp_inr` / 定理 `comul_comp_inr`

English:
theorem comul_comp_inr
  proof: by
  ext; simp

中文:
定理 comul_comp_inr
  证明: by
  ext; simp
-/
theorem comul_comp_inr :
    comul ∘ₗ inr R A B = TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul := by
  ext; simp

/--
theorem `comul_comp_fst` / 定理 `comul_comp_fst`

English:
theorem comul_comp_fst
  proof: by
  ext : 1
  · rw [comp_assoc, fst_comp_inl, comp_id, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inl, TensorProduct.map_id, id_comp]
  · rw [comp_assoc, fst_comp_inr, comp_zero, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inr, TensorProduct.map_zero_left, zero_comp]

中文:
定理 comul_comp_fst
  证明: by
  ext : 1
  · rw [comp_assoc, fst_comp_inl, comp_id, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inl, TensorProduct.map_id, id_comp]
  · rw [comp_assoc, fst_comp_inr, comp_zero, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inr, TensorProduct.map_zero_left, zero_comp]

Depends on / 依赖: TensorProduct, TensorProduct.map_comp, TensorProduct.map_id, TensorProduct.map_zero_left, comp_assoc, comp_id, comp_zero, comul_comp_inl, comul_comp_inr, fst_comp_inl, fst_comp_inr, id_comp, map_comp, map_id, map_zero_left, zero_comp
-/
theorem comul_comp_fst :
    comul ∘ₗ .fst R A B = TensorProduct.map (.fst R A B) (.fst R A B) ∘ₗ comul := by
  ext : 1
  · rw [comp_assoc, fst_comp_inl, comp_id, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inl, TensorProduct.map_id, id_comp]
  · rw [comp_assoc, fst_comp_inr, comp_zero, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inr, TensorProduct.map_zero_left, zero_comp]

/--
theorem `comul_comp_snd` / 定理 `comul_comp_snd`

English:
theorem comul_comp_snd
  proof: by
  ext : 1
  · rw [comp_assoc, snd_comp_inl, comp_zero, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inl, TensorProduct.map_zero_left, zero_comp]
  · rw [comp_assoc, snd_comp_inr, comp_id, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inr, TensorProduct.map_id, id_comp]

中文:
定理 comul_comp_snd
  证明: by
  ext : 1
  · rw [comp_assoc, snd_comp_inl, comp_zero, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inl, TensorProduct.map_zero_left, zero_comp]
  · rw [comp_assoc, snd_comp_inr, comp_id, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inr, TensorProduct.map_id, id_comp]

Depends on / 依赖: TensorProduct, TensorProduct.map_comp, TensorProduct.map_id, TensorProduct.map_zero_left, comp_assoc, comp_id, comp_zero, comul_comp_inl, comul_comp_inr, id_comp, map_comp, map_id, map_zero_left, snd_comp_inl, snd_comp_inr, zero_comp
-/
theorem comul_comp_snd :
    comul ∘ₗ .snd R A B = TensorProduct.map (.snd R A B) (.snd R A B) ∘ₗ comul := by
  ext : 1
  · rw [comp_assoc, snd_comp_inl, comp_zero, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inl, TensorProduct.map_zero_left, zero_comp]
  · rw [comp_assoc, snd_comp_inr, comp_id, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inr, TensorProduct.map_id, id_comp]

/--
theorem `counit_comp_inr` / 定理 `counit_comp_inr`

English:
theorem counit_comp_inr
  statement: counit ∘ₗ inr R A B = counit
  proof: by ext; simp

中文:
定理 counit_comp_inr
  结论: counit ∘ₗ inr R A B = counit
  证明: by ext; simp
-/
@[simp] theorem counit_comp_inr : counit ∘ₗ inr R A B = counit := by ext; simp

/--
theorem `counit_comp_inl` / 定理 `counit_comp_inl`

English:
theorem counit_comp_inl
  statement: counit ∘ₗ inl R A B = counit
  proof: by ext; simp

中文:
定理 counit_comp_inl
  结论: counit ∘ₗ inl R A B = counit
  证明: by ext; simp
-/
@[simp] theorem counit_comp_inl : counit ∘ₗ inl R A B = counit := by ext; simp

/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra R (A × B) where
  body: by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, rTensor_comp_map, counit_comp_inl,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, rTensor_comp_map, counit_comp_inr,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, lTensor_comp_map, counit_comp_inl,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, lTensor_comp_map, counit_comp_inr,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    dsimp +instances only [instCoalgebraStruct]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]

中文:
实例 instCoalgebra
  签名: : 余algebra R (A × B) where
  定义体: by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, rTensor_comp_map, counit_comp_inl,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, rTensor_comp_map, counit_comp_inr,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, lTensor_comp_map, counit_comp_inl,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, lTensor_comp_map, counit_comp_inr,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    dsimp +instances only [instCoalgebraStruct]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]

Depends on / 依赖: comp_assoc, comul_comp_inl, comul_comp_inr, counit_comp_inl, counit_comp_inr, lTensor_comp_map, lTensor_comp_mk, lTensor_comp_rTensor, lTensor_counit_comp_comul, rTensor_comp_lTensor, rTensor_comp_map, rTensor_counit_comp_comul
-/
instance instCoalgebra : Coalgebra R (A × B) where
  rTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, rTensor_comp_map, counit_comp_inl,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, rTensor_comp_map, counit_comp_inr,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, lTensor_comp_map, counit_comp_inl,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, lTensor_comp_map, counit_comp_inr,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    dsimp +instances only [instCoalgebraStruct]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCocomm
  signature: R A] [IsCocomm R B] : IsCocomm R (A × B) where
  body: by ext <;> simp [← TensorProduct.map_comm]

中文:
实例 [是余comm
  签名: R A] [是余comm R B] : 是余comm R (A × B) where
  定义体: by ext <;> simp [← TensorProduct.map_comm]

Depends on / 依赖: TensorProduct, TensorProduct.map_comm, map_comm
-/
instance [IsCocomm R A] [IsCocomm R B] : IsCocomm R (A × B) where
  comm_comp_comul := by ext <;> simp [← TensorProduct.map_comm]

end Prod

namespace DFinsupp
variable (R : Type u) (ι : Type v) (A : ι -> Type w)
variable [DecidableEq ι]
variable [CommSemiring R] [forall i, AddCommMonoid (A i)] [forall i, Module R (A i)]

open LinearMap

section coalgebraStruct
variable [forall i, CoalgebraStruct R (A i)]

/--
Instance `instCoalgebraStruct` / 实例 `instCoalgebraStruct`

English:
instance instCoalgebraStruct
  signature: : CoalgebraStruct R (Π₀ i, A i) where
  body: DFinsupp.lsum R fun i =>
    TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) ∘ₗ comul
  counit := DFinsupp.lsum R fun _ => counit

@[simp]

中文:
实例 instCoalgebraStruct
  签名: : 余algebraStruct R (Π₀ i, A i) where
  定义体: DFinsupp.lsum R fun i =>
    TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) ∘ₗ comul
  counit := DFinsupp.lsum R fun _ => counit

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.lsum
-/
instance instCoalgebraStruct : CoalgebraStruct R (Π₀ i, A i) where
  comul := DFinsupp.lsum R fun i =>
    TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) ∘ₗ comul
  counit := DFinsupp.lsum R fun _ => counit

@[simp]
/--
theorem `comul_single` / 定理 `comul_single`

English:
theorem comul_single
  given: (i : ι) (a : A i)
  proof: lsum_single _ _ _ _

@[simp]

中文:
定理 comul_single
  条件: (i : ι) (a : A i)
  证明: lsum_single _ _ _ _

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.single, single
-/
theorem comul_single (i : ι) (a : A i) :
    comul (R := R) (DFinsupp.single i a) =
      (TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) : _ ->ₗ[R] _) (comul a) :=
  lsum_single _ _ _ _

@[simp]
/--
theorem `counit_single` / 定理 `counit_single`

English:
theorem counit_single
  given: (i : ι) (a : A i)
  statement: counit (DFinsupp.single i a) = counit (R := R) a
  proof: lsum_single _ _ _ _

中文:
定理 counit_single
  条件: (i : ι) (a : A i)
  结论: counit (直和有限支撑.single i a) = counit (R := R) a
  证明: lsum_single _ _ _ _
-/
theorem counit_single (i : ι) (a : A i) : counit (DFinsupp.single i a) = counit (R := R) a :=
  lsum_single _ _ _ _

/--
theorem `comul_comp_lsingle` / 定理 `comul_comp_lsingle`

English:
theorem comul_comp_lsingle
  given: (i : ι)
  proof: by
  ext; simp

中文:
定理 comul_comp_lsingle
  条件: (i : ι)
  证明: by
  ext; simp
-/
theorem comul_comp_lsingle (i : ι) :
    comul ∘ₗ (lsingle i : A i ->ₗ[R] _) = TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul := by
  ext; simp

/--
theorem `comul_comp_lapply` / 定理 `comul_comp_lapply`

English:
theorem comul_comp_lapply
  given: (i : ι)
  proof: by
  ext j
  have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

中文:
定理 comul_comp_lapply
  条件: (i : ι)
  证明: by
  ext j
  have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

Depends on / 依赖: TensorProduct, TensorProduct.map_map, eq_or_ne, map_map, proj_comp_single
-/
theorem comul_comp_lapply (i : ι) :
    comul ∘ₗ (lapply i : _ ->ₗ[R] A i) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul := by
  ext j
  have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

/--
theorem `counit_comp_lsingle` / 定理 `counit_comp_lsingle`

English:
theorem counit_comp_lsingle
  given: (i : ι)
  statement: counit ∘ₗ (lsingle i : A i ->ₗ[R] _) = counit
  proof: by
  ext; simp

中文:
定理 counit_comp_lsingle
  条件: (i : ι)
  结论: counit ∘ₗ (lsingle i : A i ->ₗ[R] _) = counit
  证明: by
  ext; simp
-/
@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A i ->ₗ[R] _) = counit := by
  ext; simp

end coalgebraStruct

variable [forall i, Coalgebra R (A i)]

/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra R (Π₀ i, A i) where
  body: by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_lsingle]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_lsingle]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

中文:
实例 instCoalgebra
  签名: : 余algebra R (Π₀ i, A i) where
  定义体: by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_lsingle]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_lsingle]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

Depends on / 依赖: coassoc, comp_assoc, comul_comp_lsingle, counit_comp_lsingle, lTensor_comp_map, lTensor_comp_mk, lTensor_comp_rTensor, lTensor_counit_comp_comul, rTensor_comp_flip_mk, rTensor_comp_lTensor, rTensor_comp_map, rTensor_counit_comp_comul
-/
instance instCoalgebra : Coalgebra R (Π₀ i, A i) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_lsingle]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_lsingle]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

/--
Instance `instIsCocomm` / 实例 `instIsCocomm`

English:
instance instIsCocomm
  signature: [forall i, IsCocomm R (A i)]
  body: by ext; simp [← TensorProduct.map_comm]

中文:
实例 instIsCocomm
  签名: [对任意 i, 是余comm R (A i)]
  定义体: by ext; simp [← TensorProduct.map_comm]

Depends on / 依赖: TensorProduct, TensorProduct.map_comm, map_comm
-/
instance instIsCocomm [forall i, IsCocomm R (A i)] : IsCocomm R (Π₀ i, A i) where
  comm_comp_comul := by ext; simp [← TensorProduct.map_comm]

end DFinsupp

namespace Finsupp
variable (R : Type u) (ι : Type v) (A : Type w)
variable [CommSemiring R] [AddCommMonoid A] [Module R A]

open LinearMap

section coalgebraStruct
variable [CoalgebraStruct R A]

/--
Instance `instCoalgebraStruct` / 实例 `instCoalgebraStruct`

English:
instance instCoalgebraStruct
  signature: : CoalgebraStruct R (ι ->₀ A) where
  body: Finsupp.lsum R fun i =>
    TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) ∘ₗ comul
  counit := Finsupp.lsum R fun _ => counit

@[simp]

中文:
实例 instCoalgebraStruct
  签名: : 余algebraStruct R (ι ->₀ A) where
  定义体: Finsupp.lsum R fun i =>
    TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) ∘ₗ comul
  counit := Finsupp.lsum R fun _ => counit

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lsum
-/
noncomputable instance instCoalgebraStruct : CoalgebraStruct R (ι ->₀ A) where
  comul := Finsupp.lsum R fun i =>
    TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) ∘ₗ comul
  counit := Finsupp.lsum R fun _ => counit

@[simp]
/--
theorem `comul_single` / 定理 `comul_single`

English:
theorem comul_single
  given: (i : ι) (a : A)
  proof: lsum_single _ _ _ _

@[simp]

中文:
定理 comul_single
  条件: (i : ι) (a : A)
  证明: lsum_single _ _ _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
theorem comul_single (i : ι) (a : A) :
    comul (R := R) (Finsupp.single i a) =
      (TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) : _ ->ₗ[R] _) (comul a) :=
  lsum_single _ _ _ _

@[simp]
/--
theorem `counit_single` / 定理 `counit_single`

English:
theorem counit_single
  given: (i : ι) (a : A)
  statement: counit (Finsupp.single i a) = counit (R := R) a
  proof: lsum_single _ _ _ _

中文:
定理 counit_single
  条件: (i : ι) (a : A)
  结论: counit (有限支撑.single i a) = counit (R := R) a
  证明: lsum_single _ _ _ _
-/
theorem counit_single (i : ι) (a : A) : counit (Finsupp.single i a) = counit (R := R) a :=
  lsum_single _ _ _ _

/--
theorem `comul_comp_lsingle` / 定理 `comul_comp_lsingle`

English:
theorem comul_comp_lsingle
  given: (i : ι)
  proof: by
  ext; simp

中文:
定理 comul_comp_lsingle
  条件: (i : ι)
  证明: by
  ext; simp
-/
theorem comul_comp_lsingle (i : ι) :
    comul ∘ₗ (lsingle i : A ->ₗ[R] _) = TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul := by
  ext; simp

/--
theorem `comul_comp_lapply` / 定理 `comul_comp_lapply`

English:
theorem comul_comp_lapply
  given: (i : ι)
  proof: by
  ext j; have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

中文:
定理 comul_comp_lapply
  条件: (i : ι)
  证明: by
  ext j; have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

Depends on / 依赖: TensorProduct, TensorProduct.map_map, eq_or_ne, map_map, proj_comp_single
-/
theorem comul_comp_lapply (i : ι) :
    comul ∘ₗ (lapply i : _ ->ₗ[R] A) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul := by
  ext j; have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

/--
theorem `counit_comp_lsingle` / 定理 `counit_comp_lsingle`

English:
theorem counit_comp_lsingle
  given: (i : ι)
  statement: counit ∘ₗ (lsingle i : A ->ₗ[R] _) = counit
  proof: by
  ext; simp

中文:
定理 counit_comp_lsingle
  条件: (i : ι)
  结论: counit ∘ₗ (lsingle i : A ->ₗ[R] _) = counit
  证明: by
  ext; simp
-/
@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A ->ₗ[R] _) = counit := by
  ext; simp

end coalgebraStruct

variable [Coalgebra R A]

/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra R (ι ->₀ A) where
  body: by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_lsingle]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_lsingle]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

中文:
实例 instCoalgebra
  签名: : 余algebra R (ι ->₀ A) where
  定义体: by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_lsingle]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_lsingle]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

Depends on / 依赖: coassoc, comp_assoc, comul_comp_lsingle, counit_comp_lsingle, lTensor_comp_map, lTensor_comp_mk, lTensor_comp_rTensor, lTensor_counit_comp_comul, rTensor_comp_flip_mk, rTensor_comp_lTensor, rTensor_comp_map, rTensor_counit_comp_comul
-/
noncomputable instance instCoalgebra : Coalgebra R (ι ->₀ A) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_lsingle]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_lsingle]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_lsingle]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

/--
Instance `instIsCocomm` / 实例 `instIsCocomm`

English:
instance instIsCocomm
  signature: [IsCocomm R A]
  body: by ext; simp [← TensorProduct.map_comm]

中文:
实例 instIsCocomm
  签名: [是余comm R A]
  定义体: by ext; simp [← TensorProduct.map_comm]

Depends on / 依赖: TensorProduct, TensorProduct.map_comm, map_comm
-/
instance instIsCocomm [IsCocomm R A] : IsCocomm R (ι ->₀ A) where
  comm_comp_comul := by ext; simp [← TensorProduct.map_comm]

end Finsupp

namespace Pi
variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
  {A : n -> Type*} [Π i, AddCommMonoid (A i)] [Π i, Module R (A i)]

open TensorProduct LinearMap

section coalgebraStruct
variable [Π i, CoalgebraStruct R (A i)]

/--
Instance `instCoalgebraStruct` / 实例 `instCoalgebraStruct`

English:
instance instCoalgebraStruct
  signature: : CoalgebraStruct R (Π i, A i) where
  body: .lsum R _ R fun i => map (.single R _ i) (.single R _ i) ∘ₗ comul
  counit := .lsum R _ R fun _ => counit

中文:
实例 instCoalgebraStruct
  签名: : 余algebraStruct R (Π i, A i) where
  定义体: .lsum R _ R fun i => map (.single R _ i) (.single R _ i) ∘ₗ comul
  counit := .lsum R _ R fun _ => counit

Depends on / 依赖: single
-/
instance instCoalgebraStruct : CoalgebraStruct R (Π i, A i) where
  comul := .lsum R _ R fun i => map (.single R _ i) (.single R _ i) ∘ₗ comul
  counit := .lsum R _ R fun _ => counit

/--
theorem `comul_single` / 定理 `comul_single`

English:
theorem comul_single
  given: (i : n) (a : A i)
  proof: lsum_piSingle _ _ _ _ _ _

中文:
定理 comul_single
  条件: (i : n) (a : A i)
  证明: lsum_piSingle _ _ _ _ _ _
-/
@[simp] theorem comul_single (i : n) (a : A i) :
    comul (single i a) = map (.single R _ i) (.single R _ i) (comul a) :=
  lsum_piSingle _ _ _ _ _ _

/--
theorem `counit_single` / 定理 `counit_single`

English:
theorem counit_single
  given: (i : n) (a : A i)
  statement: counit (single i a) = counit (R := R) a
  proof: lsum_piSingle _ _ _ _ _ _

中文:
定理 counit_single
  条件: (i : n) (a : A i)
  结论: counit (single i a) = counit (R := R) a
  证明: lsum_piSingle _ _ _ _ _ _
-/
@[simp] theorem counit_single (i : n) (a : A i) : counit (single i a) = counit (R := R) a :=
  lsum_piSingle _ _ _ _ _ _

/--
theorem `comul_comp_single` / 定理 `comul_comp_single`

English:
theorem comul_comp_single
  given: (i : n)
  proof: by
  ext; simp

中文:
定理 comul_comp_single
  条件: (i : n)
  证明: by
  ext; simp
-/
theorem comul_comp_single (i : n) :
    comul ∘ₗ .single R _ i = map (.single R A i) (.single R A i) ∘ₗ comul := by
  ext; simp

/--
theorem `comul_comp_proj` / 定理 `comul_comp_proj`

English:
theorem comul_comp_proj
  given: (i : n)
  proof: by
  ext j; have := eq_or_ne i j
  aesop (add simp [map_map, proj_comp_single, diag])

中文:
定理 comul_comp_proj
  条件: (i : n)
  证明: by
  ext j; have := eq_or_ne i j
  aesop (add simp [map_map, proj_comp_single, diag])

Depends on / 依赖: eq_or_ne, map_map, proj_comp_single
-/
theorem comul_comp_proj (i : n) :
    comul ∘ₗ (proj i : (Π i, A i) ->ₗ[R] A i) = map (proj i) (proj i) ∘ₗ comul := by
  ext j; have := eq_or_ne i j
  aesop (add simp [map_map, proj_comp_single, diag])

/--
theorem `counit_comp_single` / 定理 `counit_comp_single`

English:
theorem counit_comp_single
  given: (i : n)
  statement: counit ∘ₗ .single R A i = counit
  proof: by ext; simp

中文:
定理 counit_comp_single
  条件: (i : n)
  结论: counit ∘ₗ .single R A i = counit
  证明: by ext; simp
-/
@[simp] theorem counit_comp_single (i : n) : counit ∘ₗ .single R A i = counit := by ext; simp

/--
theorem `counit_comp_dFinsuppCoeFnLinearMap` / 定理 `counit_comp_dFinsuppCoeFnLinearMap`

English:
theorem counit_comp_dFinsuppCoeFnLinearMap
  proof: by
  apply LinearMap.ext fun x => ?_
  have (i : n) (x : A i) : Decidable (x != 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  simp [DFinsupp.single_eq_pi_single]

中文:
定理 counit_comp_dFinsuppCoeFnLinearMap
  证明: by
  apply LinearMap.ext fun x => ?_
  have (i : n) (x : A i) : Decidable (x != 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  simp [DFinsupp.single_eq_pi_single]

Depends on / 依赖: Classical, Classical.propDecidable, DFinsupp, DFinsupp.coeFnLinearMap, DFinsupp.single_eq_pi_single, DFinsupp.sum_single, Decidable, LinearMap, LinearMap.ext, coeFnLinearMap, counit, propDecidable, single_eq_pi_single, sum_single
-/
theorem counit_comp_dFinsuppCoeFnLinearMap :
    counit (R := R) (A := Π i, A i) ∘ₗ DFinsupp.coeFnLinearMap _ = counit := by
  apply LinearMap.ext fun x => ?_
  have (i : n) (x : A i) : Decidable (x != 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  simp [DFinsupp.single_eq_pi_single]

/--
theorem `counit_coe_dFinsupp` / 定理 `counit_coe_dFinsupp`

English:
theorem counit_coe_dFinsupp
  given: (x : Π₀ i, A i)
  proof: congr($counit_comp_dFinsuppCoeFnLinearMap x)

中文:
定理 counit_coe_dFinsupp
  条件: (x : Π₀ i, A i)
  证明: congr($counit_comp_dFinsuppCoeFnLinearMap x)
-/
@[simp] theorem counit_coe_dFinsupp (x : Π₀ i, A i) :
    counit (R := R) ⇑x = counit x := congr($counit_comp_dFinsuppCoeFnLinearMap x)

open DFinsupp in
/--
theorem `comul_comp_dFinsuppCoeFnLinearMap` / 定理 `comul_comp_dFinsuppCoeFnLinearMap`

English:
theorem comul_comp_dFinsuppCoeFnLinearMap
  proof: by
  apply LinearMap.ext fun x => ?_
  have (i : n) (x : A i) : Decidable (x != 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  aesop (add simp [map_map, DFinsupp.single_eq_pi_single])

中文:
定理 comul_comp_dFinsuppCoeFnLinearMap
  证明: by
  apply LinearMap.ext fun x => ?_
  have (i : n) (x : A i) : Decidable (x != 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  aesop (add simp [map_map, DFinsupp.single_eq_pi_single])

Depends on / 依赖: coeFnLinearMap
-/
theorem comul_comp_dFinsuppCoeFnLinearMap :
    comul (R := R) (A := Π i, A i) ∘ₗ coeFnLinearMap _ =
      map (coeFnLinearMap _) (coeFnLinearMap _) ∘ₗ comul := by
  apply LinearMap.ext fun x => ?_
  have (i : n) (x : A i) : Decidable (x != 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  aesop (add simp [map_map, DFinsupp.single_eq_pi_single])

open DFinsupp in
/--
theorem `comul_coe_dFinsupp` / 定理 `comul_coe_dFinsupp`

English:
theorem comul_coe_dFinsupp
  given: (x : Π₀ i, A i)
  proof: congr($comul_comp_dFinsuppCoeFnLinearMap x)

中文:
定理 comul_coe_dFinsupp
  条件: (x : Π₀ i, A i)
  证明: congr($comul_comp_dFinsuppCoeFnLinearMap x)
-/
@[simp] theorem comul_coe_dFinsupp (x : Π₀ i, A i) :
    comul (R := R) ⇑x = map (coeFnLinearMap _) (coeFnLinearMap _) (comul x) :=
  congr($comul_comp_dFinsuppCoeFnLinearMap x)

variable {M : Type*} [AddCommMonoid M] [Module R M] [CoalgebraStruct R M]

/--
theorem `counit_comp_finsuppLcoeFun` / 定理 `counit_comp_finsuppLcoeFun`

English:
theorem counit_comp_finsuppLcoeFun
  proof: by
  apply LinearMap.ext fun x => ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-Finsupp.univ_sum_single, Finsupp.lcoeFun, Finsupp.single_eq_pi_single]

中文:
定理 counit_comp_finsuppLcoeFun
  证明: by
  apply LinearMap.ext fun x => ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-Finsupp.univ_sum_single, Finsupp.lcoeFun, Finsupp.single_eq_pi_single]

Depends on / 依赖: Finsupp, Finsupp.lcoeFun, Finsupp.single_eq_pi_single, Finsupp.univ_sum_single, LinearMap, LinearMap.ext, counit, lcoeFun, single_eq_pi_single, univ_sum_single
-/
theorem counit_comp_finsuppLcoeFun :
    counit (R := R) (A := n -> M) ∘ₗ Finsupp.lcoeFun = counit := by
  apply LinearMap.ext fun x => ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-Finsupp.univ_sum_single, Finsupp.lcoeFun, Finsupp.single_eq_pi_single]

/--
theorem `counit_coe_finsupp` / 定理 `counit_coe_finsupp`

English:
theorem counit_coe_finsupp
  given: (x : n ->₀ M)
  proof: congr($counit_comp_finsuppLcoeFun x)

中文:
定理 counit_coe_finsupp
  条件: (x : n ->₀ M)
  证明: congr($counit_comp_finsuppLcoeFun x)
-/
@[simp] theorem counit_coe_finsupp (x : n ->₀ M) :
    counit (R := R) ⇑x = counit x := congr($counit_comp_finsuppLcoeFun x)

open Finsupp in
/--
theorem `comul_comp_finsuppLcoeFun` / 定理 `comul_comp_finsuppLcoeFun`

English:
theorem comul_comp_finsuppLcoeFun
  proof: by
  apply LinearMap.ext fun x => ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-univ_sum_single, single_eq_pi_single, map_map]

中文:
定理 comul_comp_finsuppLcoeFun
  证明: by
  apply LinearMap.ext fun x => ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-univ_sum_single, single_eq_pi_single, map_map]

Depends on / 依赖: Finsupp, Finsupp.univ_sum_single, LinearMap, LinearMap.ext, lcoeFun, map_map, single_eq_pi_single, univ_sum_single
-/
theorem comul_comp_finsuppLcoeFun :
    comul (R := R) (A := n -> M) ∘ₗ lcoeFun = map lcoeFun lcoeFun ∘ₗ comul := by
  apply LinearMap.ext fun x => ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-univ_sum_single, single_eq_pi_single, map_map]

open Finsupp in
/--
theorem `comul_coe_finsupp` / 定理 `comul_coe_finsupp`

English:
theorem comul_coe_finsupp
  given: (x : n ->₀ M)
  proof: congr($comul_comp_finsuppLcoeFun x)

中文:
定理 comul_coe_finsupp
  条件: (x : n ->₀ M)
  证明: congr($comul_comp_finsuppLcoeFun x)
-/
@[simp] theorem comul_coe_finsupp (x : n ->₀ M) :
    comul (R := R) ⇑x = map lcoeFun lcoeFun (comul x) :=
  congr($comul_comp_finsuppLcoeFun x)

end coalgebraStruct

variable [Π i, Coalgebra R (A i)]

/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra R (Π i, A i) where
  body: by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_single]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_single]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_single]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_single]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext : 1
    simp_rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, comul_comp_single,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_single, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
      map_map_comp_assoc_eq]

中文:
实例 instCoalgebra
  签名: : 余algebra R (Π i, A i) where
  定义体: by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_single]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_single]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_single]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_single]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext : 1
    simp_rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, comul_comp_single,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_single, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
      map_map_comp_assoc_eq]

Depends on / 依赖: coassoc, comp_assoc, comul_comp_single, counit_comp_single, lTensor_comp_map, lTensor_comp_mk, lTensor_comp_rTensor, lTensor_counit_comp_comul, rTensor_comp_flip_mk, rTensor_comp_lTensor, rTensor_comp_map, rTensor_counit_comp_comul, simp_rw
-/
instance instCoalgebra : Coalgebra R (Π i, A i) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_single]; rw [← comp_assoc]; rw [rTensor_comp_map]; rw [counit_comp_single]; rw [← lTensor_comp_rTensor]; rw [comp_assoc]; rw [rTensor_counit_comp_comul]; rw [lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc]; rw [comul_comp_single]; rw [← comp_assoc]; rw [lTensor_comp_map]; rw [counit_comp_single]; rw [← rTensor_comp_lTensor]; rw [comp_assoc]; rw [lTensor_counit_comp_comul]; rw [rTensor_comp_flip_mk]
  coassoc := by
    ext : 1
    simp_rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, comul_comp_single,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_single, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
      map_map_comp_assoc_eq]

/--
Instance `instIsCocomm` / 实例 `instIsCocomm`

English:
instance instIsCocomm
  signature: [forall i, IsCocomm R (A i)]
  body: by ext; simp [← map_comm]

中文:
实例 instIsCocomm
  签名: [对任意 i, 是余comm R (A i)]
  定义体: by ext; simp [← map_comm]

Depends on / 依赖: map_comm
-/
instance instIsCocomm [forall i, IsCocomm R (A i)] : IsCocomm R (Π i, A i) where
  comm_comp_comul := by ext; simp [← map_comm]

end Pi

namespace Equiv
variable {R A B : Type*} [CommSemiring R]

variable (R) in
/--
Definition of `coalgebraStruct` / `coalgebraStruct` 的定义

English:
abbreviation coalgebraStruct
  signature: [AddCommMonoid B] [Module R B] [CoalgebraStruct R B] (e : A ≃ B)
  body: e.addCommMonoid
    letI := e.module R
    CoalgebraStruct R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { comul :=
      TensorProduct.map (e.linearEquiv R).symm.toLinearMap (e.linearEquiv R).symm.toLinearMap ∘ₗ
        comul ∘ₗ (e.linearEquiv R).toLinearMap
    counit := counit ∘ₗ (e.linearEquiv R).toLinearMap }

中文:
缩写 coalgebraStruct
  签名: [加法交换幺半群 B] [模 R B] [余algebraStruct R B] (e : A ≃ B)
  定义体: e.addCommMonoid
    letI := e.module R
    CoalgebraStruct R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { comul :=
      TensorProduct.map (e.linearEquiv R).symm.toLinearMap (e.linearEquiv R).symm.toLinearMap ∘ₗ
        comul ∘ₗ (e.linearEquiv R).toLinearMap
    counit := counit ∘ₗ (e.linearEquiv R).toLinearMap }

Depends on / 依赖: addCommMonoid, e.addCommMonoid
-/
abbrev coalgebraStruct [AddCommMonoid B] [Module R B] [CoalgebraStruct R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    CoalgebraStruct R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { comul :=
      TensorProduct.map (e.linearEquiv R).symm.toLinearMap (e.linearEquiv R).symm.toLinearMap ∘ₗ
        comul ∘ₗ (e.linearEquiv R).toLinearMap
    counit := counit ∘ₗ (e.linearEquiv R).toLinearMap }

variable (R) in
/--
Definition of `coalgebra` / `coalgebra` 的定义

English:
abbreviation coalgebra
  signature: [AddCommMonoid B] [Module R B] [Coalgebra R B] (e : A ≃ B)
  body: e.addCommMonoid
    letI := e.module R
    Coalgebra R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { __ := e.coalgebraStruct R
    rTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (f := .id) Function.bijective_id
        (e.linearEquiv R).bijective).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.rTensor] using! Coalgebra.rTensor_counit_comul _
    lTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (g := .id) (e.linearEquiv R).bijective
        Function.bijective_id).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.lTensor] using! Coalgebra.lTensor_counit_comul _
    coassoc := by
      ext
      apply (TensorProduct.map_bijective (e.linearEquiv R).bijective <|
        TensorProduct.map_bijective (e.linearEquiv R).bijective
        (e.linearEquiv R).bijective).injective
      simp +instances [coalgebraStruct, e.tensorProductAssoc_def R, TensorProduct.congr,
        ← LinearMap.comp_assoc, TensorProduct.map_map, ← TensorProduct.map_comp]
      simpa [LinearMap.comp_assoc, -coassoc_apply] using! coassoc_apply (R := R) (A := B) _ }

中文:
缩写 coalgebra
  签名: [加法交换幺半群 B] [模 R B] [余algebra R B] (e : A ≃ B)
  定义体: e.addCommMonoid
    letI := e.module R
    Coalgebra R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { __ := e.coalgebraStruct R
    rTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (f := .id) Function.bijective_id
        (e.linearEquiv R).bijective).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.rTensor] using! Coalgebra.rTensor_counit_comul _
    lTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (g := .id) (e.linearEquiv R).bijective
        Function.bijective_id).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.lTensor] using! Coalgebra.lTensor_counit_comul _
    coassoc := by
      ext
      apply (TensorProduct.map_bijective (e.linearEquiv R).bijective <|
        TensorProduct.map_bijective (e.linearEquiv R).bijective
        (e.linearEquiv R).bijective).injective
      simp +instances [coalgebraStruct, e.tensorProductAssoc_def R, TensorProduct.congr,
        ← LinearMap.comp_assoc, TensorProduct.map_map, ← TensorProduct.map_comp]
      simpa [LinearMap.comp_assoc, -coassoc_apply] using! coassoc_apply (R := R) (A := B) _ }

Depends on / 依赖: addCommMonoid, e.addCommMonoid
-/
abbrev coalgebra [AddCommMonoid B] [Module R B] [Coalgebra R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    Coalgebra R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { __ := e.coalgebraStruct R
    rTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (f := .id) Function.bijective_id
        (e.linearEquiv R).bijective).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.rTensor] using! Coalgebra.rTensor_counit_comul _
    lTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (g := .id) (e.linearEquiv R).bijective
        Function.bijective_id).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.lTensor] using! Coalgebra.lTensor_counit_comul _
    coassoc := by
      ext
      apply (TensorProduct.map_bijective (e.linearEquiv R).bijective <|
        TensorProduct.map_bijective (e.linearEquiv R).bijective
        (e.linearEquiv R).bijective).injective
      simp +instances [coalgebraStruct, e.tensorProductAssoc_def R, TensorProduct.congr,
        ← LinearMap.comp_assoc, TensorProduct.map_map, ← TensorProduct.map_comp]
      simpa [LinearMap.comp_assoc, -coassoc_apply] using! coassoc_apply (R := R) (A := B) _ }

variable (R) in
/--
lemma `coalgebraIsCocomm` / 引理 `coalgebraIsCocomm`

English:
lemma coalgebraIsCocomm
  given: [AddCommMonoid B] [Module R B] [Coalgebra R B] [IsCocomm R B] (e : A ≃ B)
  proof: e.addCommMonoid
    letI := e.module R
    letI := e.coalgebra R
    IsCocomm R A :=
  letI := e.addCommMonoid
  letI := e.module R
  letI := e.coalgebra R
  { comm_comp_comul := by ext; simp [comul, ← TensorProduct.map_comm] }

中文:
引理 coalgebraIsCocomm
  条件: [加法交换幺半群 B] [模 R B] [余algebra R B] [是余comm R B] (e : A ≃ B)
  证明: e.addCommMonoid
    letI := e.module R
    letI := e.coalgebra R
    IsCocomm R A :=
  letI := e.addCommMonoid
  letI := e.module R
  letI := e.coalgebra R
  { comm_comp_comul := by ext; simp [comul, ← TensorProduct.map_comm] }

Depends on / 依赖: addCommMonoid, e.addCommMonoid
-/
lemma coalgebraIsCocomm [AddCommMonoid B] [Module R B] [Coalgebra R B] [IsCocomm R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    letI := e.coalgebra R
    IsCocomm R A :=
  letI := e.addCommMonoid
  letI := e.module R
  letI := e.coalgebra R
  { comm_comp_comul := by ext; simp [comul, ← TensorProduct.map_comm] }

end Equiv
