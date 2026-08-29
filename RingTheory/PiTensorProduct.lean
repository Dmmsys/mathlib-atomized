/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Data.Finset.NoncommProd

/-!
# Tensor product of `R`-algebras and rings

If `(Aᵢ)` is a family of `R`-algebras then the `R`-tensor product `⨂ᵢ Aᵢ` is an `R`-algebra as well
with structure map defined by `r ↦ r • 1`.

In particular if we take `R` to be `ℤ`, then this collapses into the tensor product of rings.
-/

@[expose] public section

open TensorProduct Function

variable {ι R' R : Type*} {A : ι -> Type*}

namespace PiTensorProduct

noncomputable section AddCommMonoidWithOne

variable [CommSemiring R] [forall i, AddCommMonoidWithOne (A i)] [forall i, Module R (A i)]

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (⨂[R] i, A i) where
  body: tprod R 1

中文:
实例 instOne
  签名: : 幺 (⨂[R] i, A i) where
  定义体: tprod R 1
-/
instance instOne : One (⨂[R] i, A i) where
  one := tprod R 1

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: 1 = tprod R (1 : Π i, A i)
  proof: rfl

中文:
引理 one_def
  结论: 1 = tprod R (1 : Π i, A i)
  证明: rfl
-/
lemma one_def : 1 = tprod R (1 : Π i, A i) := rfl

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: : AddCommMonoidWithOne (⨂[R] i, A i) where
  body: (inferInstance : AddCommMonoid (⨂[R] i, A i))
  __ := instOne

中文:
实例 instAddCommMonoidWithOne
  签名: : 加法交换带幺幺半群 (⨂[R] i, A i) where
  定义体: (inferInstance : AddCommMonoid (⨂[R] i, A i))
  __ := instOne

Depends on / 依赖: AddCommMonoid
-/
instance instAddCommMonoidWithOne : AddCommMonoidWithOne (⨂[R] i, A i) where
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  __ := instOne

end AddCommMonoidWithOne

noncomputable section NonUnitalNonAssocSemiring

variable [CommSemiring R] [forall i, NonUnitalNonAssocSemiring (A i)]
variable [forall i, Module R (A i)] [forall i, SMulCommClass R (A i) (A i)] [forall i, IsScalarTower R (A i) (A i)]

attribute [aesop safe] mul_add mul_smul_comm smul_mul_assoc add_mul in
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i)
  body: PiTensorProduct.piTensorHomMap₂ tprod R fun _ => LinearMap.mul _ _

中文:
定义 mul
  签名: : (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i)
  定义体: PiTensorProduct.piTensorHomMap₂ tprod R fun _ => LinearMap.mul _ _

Depends on / 依赖: LinearMap, LinearMap.mul, PiTensorProduct, PiTensorProduct.piTensorHomMap
-/
def mul : (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i) :=
PiTensorProduct.piTensorHomMap₂ tprod R fun _ => LinearMap.mul _ _

/--
lemma `mul_tprod_tprod` / 引理 `mul_tprod_tprod`

English:
lemma mul_tprod_tprod
  given: (x y : (i : ι) -> A i)
  proof: by
  simp only [mul, piTensorHomMap₂_tprod_tprod_tprod, LinearMap.mul_apply', Pi.mul_def]

中文:
引理 mul_tprod_tprod
  条件: (x y : (i : ι) -> A i)
  证明: by
  simp only [mul, piTensorHomMap₂_tprod_tprod_tprod, LinearMap.mul_apply', Pi.mul_def]
-/
@[simp] lemma mul_tprod_tprod (x y : (i : ι) -> A i) :
    mul (tprod R x) (tprod R y) = tprod R (x * y) := by
  simp only [mul, piTensorHomMap₂_tprod_tprod_tprod, LinearMap.mul_apply', Pi.mul_def]

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (⨂[R] i, A i) where
  body: mul x y

中文:
实例 instMul
  签名: : 乘法 (⨂[R] i, A i) where
  定义体: mul x y
-/
instance instMul : Mul (⨂[R] i, A i) where
  mul x y := mul x y

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (x y : ⨂[R] i, A i)
  statement: x * y = mul x y
  proof: rfl

中文:
引理 mul_def
  条件: (x y : ⨂[R] i, A i)
  结论: x * y = mul x y
  证明: rfl
-/
lemma mul_def (x y : ⨂[R] i, A i) : x * y = mul x y := rfl

/--
lemma `tprod_mul_tprod` / 引理 `tprod_mul_tprod`

English:
lemma tprod_mul_tprod
  given: (x y : (i : ι) -> A i)
  proof: mul_tprod_tprod x y

中文:
引理 tprod_mul_tprod
  条件: (x y : (i : ι) -> A i)
  证明: mul_tprod_tprod x y
-/
@[simp] lemma tprod_mul_tprod (x y : (i : ι) -> A i) :
    tprod R x * tprod R y = tprod R (x * y) :=
  mul_tprod_tprod x y

/--
theorem `_root_.SemiconjBy.tprod` / 定理 `_root_.SemiconjBy.tprod`

English:
theorem _root_.SemiconjBy.tprod
  statement: {a₁ a₂ a₃ : Π i, A i}
  proof: by
  rw [SemiconjBy]; rw [tprod_mul_tprod]; rw [tprod_mul_tprod]; rw [ha]

nonrec theorem _root_.Commute.tprod {a₁ a₂ : Π i, A i} (ha : Commute a₁ a₂) :
    Commute (tprod R a₁) (tprod R a₂) :=
  ha.tprod

中文:
定理 _root_.SemiconjBy.tprod
  结论: {a₁ a₂ a₃ : Π i, A i}
  证明: by
  rw [SemiconjBy]; rw [tprod_mul_tprod]; rw [tprod_mul_tprod]; rw [ha]

nonrec theorem _root_.Commute.tprod {a₁ a₂ : Π i, A i} (ha : Commute a₁ a₂) :
    Commute (tprod R a₁) (tprod R a₂) :=
  ha.tprod

Depends on / 依赖: SemiconjBy, tprod_mul_tprod
-/
theorem _root_.SemiconjBy.tprod {a₁ a₂ a₃ : Π i, A i}
    (ha : SemiconjBy a₁ a₂ a₃) :
    SemiconjBy (tprod R a₁) (tprod R a₂) (tprod R a₃) := by
  rw [SemiconjBy]; rw [tprod_mul_tprod]; rw [tprod_mul_tprod]; rw [ha]

nonrec theorem _root_.Commute.tprod {a₁ a₂ : Π i, A i} (ha : Commute a₁ a₂) :
    Commute (tprod R a₁) (tprod R a₂) :=
  ha.tprod

set_option backward.isDefEq.respectTransparency false in
/--
lemma `smul_tprod_mul_smul_tprod` / 引理 `smul_tprod_mul_smul_tprod`

English:
lemma smul_tprod_mul_smul_tprod
  given: (r s : R) (x y : Π i, A i)
  proof: by
  simp only [mul_def, map_smul, LinearMap.smul_apply, mul_tprod_tprod, mul_comm r s, mul_smul]

中文:
引理 smul_tprod_mul_smul_tprod
  条件: (r s : R) (x y : Π i, A i)
  证明: by
  simp only [mul_def, map_smul, LinearMap.smul_apply, mul_tprod_tprod, mul_comm r s, mul_smul]

Depends on / 依赖: LinearMap, LinearMap.smul_apply, map_smul, mul_comm, mul_def, mul_smul, mul_tprod_tprod, smul_apply
-/
lemma smul_tprod_mul_smul_tprod (r s : R) (x y : Π i, A i) :
    (r • tprod R x) * (s • tprod R y) = (r * s) • tprod R (x * y) := by
  simp only [mul_def, map_smul, LinearMap.smul_apply, mul_tprod_tprod, mul_comm r s, mul_smul]

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: : NonUnitalNonAssocSemiring (⨂[R] i, A i) where
  body: instMul
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  left_distrib _ _ _ := (mul _).map_add _ _
  right_distrib _ _ _ := mul.map_add₂ _ _ _
  zero_mul _ := mul.map_zero₂ _
  mul_zero _ := map_zero (mul _)

中文:
实例 instNonUnitalNonAssocSemiring
  签名: : 非幺非结合半环 (⨂[R] i, A i) where
  定义体: instMul
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  left_distrib _ _ _ := (mul _).map_add _ _
  right_distrib _ _ _ := mul.map_add₂ _ _ _
  zero_mul _ := mul.map_zero₂ _
  mul_zero _ := map_zero (mul _)

Depends on / 依赖: instMul
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (⨂[R] i, A i) where
  __ := instMul
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  left_distrib _ _ _ := (mul _).map_add _ _
  right_distrib _ _ _ := mul.map_add₂ _ _ _
  zero_mul _ := mul.map_zero₂ _
  mul_zero _ := map_zero (mul _)

end NonUnitalNonAssocSemiring

noncomputable section NonAssocSemiring

variable [CommSemiring R] [forall i, NonAssocSemiring (A i)]
variable [forall i, Module R (A i)] [forall i, SMulCommClass R (A i) (A i)] [forall i, IsScalarTower R (A i) (A i)]

/--
lemma `one_mul` / 引理 `one_mul`

English:
lemma one_mul
  given: (x : ⨂[R] i, A i)
  statement: mul (tprod R 1) x = x
  proof: by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [map_add, h1, h2]

中文:
引理 one_mul
  条件: (x : ⨂[R] i, A i)
  结论: mul (tprod R 1) x = x
  证明: by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [map_add, h1, h2]
-/
protected lemma one_mul (x : ⨂[R] i, A i) : mul (tprod R 1) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [map_add, h1, h2]

/--
lemma `mul_one` / 引理 `mul_one`

English:
lemma mul_one
  given: (x : ⨂[R] i, A i)
  statement: mul x (tprod R 1) = x
  proof: by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [h1, h2]

中文:
引理 mul_one
  条件: (x : ⨂[R] i, A i)
  结论: mul x (tprod R 1) = x
  证明: by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [h1, h2]
-/
protected lemma mul_one (x : ⨂[R] i, A i) : mul x (tprod R 1) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [h1, h2]

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: : NonAssocSemiring (⨂[R] i, A i) where
  body: instNonUnitalNonAssocSemiring
  one_mul := PiTensorProduct.one_mul
  mul_one := PiTensorProduct.mul_one

中文:
实例 instNonAssocSemiring
  签名: : 非结合半环 (⨂[R] i, A i) where
  定义体: instNonUnitalNonAssocSemiring
  one_mul := PiTensorProduct.one_mul
  mul_one := PiTensorProduct.mul_one

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring : NonAssocSemiring (⨂[R] i, A i) where
  __ := instNonUnitalNonAssocSemiring
  one_mul := PiTensorProduct.one_mul
  mul_one := PiTensorProduct.mul_one

variable (R) in
/-- `PiTensorProduct.tprod` as a `MonoidHom`. -/
@[simps]
/--
Definition of `tprodMonoidHom` / `tprodMonoidHom` 的定义

English:
definition tprodMonoidHom
  signature: : (Π i, A i) ->* ⨂[R] i, A i where
  body: tprod R
  map_one' := rfl
  map_mul' x y := (tprod_mul_tprod x y).symm

中文:
定义 tprodMonoidHom
  签名: : (Π i, A i) ->* ⨂[R] i, A i where
  定义体: tprod R
  map_one' := rfl
  map_mul' x y := (tprod_mul_tprod x y).symm
-/
def tprodMonoidHom : (Π i, A i) ->* ⨂[R] i, A i where
  toFun := tprod R
  map_one' := rfl
  map_mul' x y := (tprod_mul_tprod x y).symm

end NonAssocSemiring

noncomputable section NonUnitalSemiring

variable [CommSemiring R] [forall i, NonUnitalSemiring (A i)]
variable [forall i, Module R (A i)] [forall i, SMulCommClass R (A i) (A i)] [forall i, IsScalarTower R (A i) (A i)]

/--
lemma `mul_assoc` / 引理 `mul_assoc`

English:
lemma mul_assoc
  given: (x y z : ⨂[R] i, A i)
  statement: mul (mul x y) z = mul x (mul y z)
  proof: by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext x y z
  dsimp [← mul_def]
  simpa only [tprod_mul_tprod] using congr_arg (tprod R) (mul_assoc x y z)

中文:
引理 mul_assoc
  条件: (x y z : ⨂[R] i, A i)
  结论: mul (mul x y) z = mul x (mul y z)
  证明: by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext x y z
  dsimp [← mul_def]
  simpa only [tprod_mul_tprod] using congr_arg (tprod R) (mul_assoc x y z)
-/
protected lemma mul_assoc (x y z : ⨂[R] i, A i) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext x y z
  dsimp [← mul_def]
  simpa only [tprod_mul_tprod] using congr_arg (tprod R) (mul_assoc x y z)

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: : NonUnitalSemiring (⨂[R] i, A i) where
  body: instNonUnitalNonAssocSemiring
  mul_assoc := PiTensorProduct.mul_assoc

中文:
实例 instNonUnitalSemiring
  签名: : 非幺半环 (⨂[R] i, A i) where
  定义体: instNonUnitalNonAssocSemiring
  mul_assoc := PiTensorProduct.mul_assoc

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonUnitalSemiring : NonUnitalSemiring (⨂[R] i, A i) where
  __ := instNonUnitalNonAssocSemiring
  mul_assoc := PiTensorProduct.mul_assoc

end NonUnitalSemiring

noncomputable section Semiring

variable [CommSemiring R'] [CommSemiring R] [forall i, Semiring (A i)]
variable [Algebra R' R] [forall i, Algebra R (A i)] [forall i, Algebra R' (A i)]
variable [forall i, IsScalarTower R' R (A i)]

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (⨂[R] i, A i) where
  body: instNonUnitalSemiring
  __ := instNonAssocSemiring

中文:
实例 instSemiring
  签名: : 半环 (⨂[R] i, A i) where
  定义体: instNonUnitalSemiring
  __ := instNonAssocSemiring

Depends on / 依赖: instNonUnitalSemiring
-/
instance instSemiring : Semiring (⨂[R] i, A i) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra R' (⨂[R] i, A i) where
  body: hasSMul'
  algebraMap :=
  { toFun := (· • 1)
    map_one' := by simp
    map_mul' r s := show (r * s) • 1 = mul (r • 1) (s • 1) by
      rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]; rw [mul_comm]; rw [mul_smul]
      congr
      change (1 : ⨂[R] i, A i) = 1 * 1
      rw [mul_one]
    map_zero' := by simp
    map_add' := by simp [add_smul] }
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change mul _ _ = mul _ _
    rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]
    change r • (1 * x) = r • (x * 1)
    rw [mul_one]; rw [one_mul]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = mul _ _
    rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]
    change _ = r • (1 * x)
    rw [one_mul]

中文:
实例 instAlgebra
  签名: : 代数 R' (⨂[R] i, A i) where
  定义体: hasSMul'
  algebraMap :=
  { toFun := (· • 1)
    map_one' := by simp
    map_mul' r s := show (r * s) • 1 = mul (r • 1) (s • 1) by
      rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]; rw [mul_comm]; rw [mul_smul]
      congr
      change (1 : ⨂[R] i, A i) = 1 * 1
      rw [mul_one]
    map_zero' := by simp
    map_add' := by simp [add_smul] }
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change mul _ _ = mul _ _
    rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]
    change r • (1 * x) = r • (x * 1)
    rw [mul_one]; rw [one_mul]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = mul _ _
    rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]
    change _ = r • (1 * x)
    rw [one_mul]

Depends on / 依赖: hasSMul
-/
instance instAlgebra : Algebra R' (⨂[R] i, A i) where
  __ := hasSMul'
  algebraMap :=
  { toFun := (· • 1)
    map_one' := by simp
    map_mul' r s := show (r * s) • 1 = mul (r • 1) (s • 1) by
      rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]; rw [mul_comm]; rw [mul_smul]
      congr
      change (1 : ⨂[R] i, A i) = 1 * 1
      rw [mul_one]
    map_zero' := by simp
    map_add' := by simp [add_smul] }
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change mul _ _ = mul _ _
    rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]
    change r • (1 * x) = r • (x * 1)
    rw [mul_one]; rw [one_mul]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = mul _ _
    rw [LinearMap.map_smul_of_tower]; rw [LinearMap.smul_apply]
    change _ = r • (1 * x)
    rw [one_mul]

/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (r : R') (i : ι) [DecidableEq ι]
  proof: by
  change r • tprod R 1 = _
  have : Pi.mulSingle i (algebraMap R' (A i) r) = update (fun i => 1) i (r • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [this]; rw [← smul_one_smul R r (1 : A i)]; rw [MultilinearMap.map_update_smul]; rw [update_eq_self]; rw [smul_one_smul]; rw [Pi.one_def]

中文:
引理 algebraMap_apply
  条件: (r : R') (i : ι) [DecidableEq ι]
  证明: by
  change r • tprod R 1 = _
  have : Pi.mulSingle i (algebraMap R' (A i) r) = update (fun i => 1) i (r • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [this]; rw [← smul_one_smul R r (1 : A i)]; rw [MultilinearMap.map_update_smul]; rw [update_eq_self]; rw [smul_one_smul]; rw [Pi.one_def]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, MultilinearMap, MultilinearMap.map_update_smul, Pi.mulSingle, Pi.one_def, algebraMap, algebraMap_eq_smul_one, map_update_smul, mulSingle, one_def, smul_one_smul, update, update_eq_self
-/
lemma algebraMap_apply (r : R') (i : ι) [DecidableEq ι] :
    algebraMap R' (⨂[R] i, A i) r = tprod R (Pi.mulSingle i (algebraMap R' (A i) r)) := by
  change r • tprod R 1 = _
  have : Pi.mulSingle i (algebraMap R' (A i) r) = update (fun i => 1) i (r • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [this]; rw [← smul_one_smul R r (1 : A i)]; rw [MultilinearMap.map_update_smul]; rw [update_eq_self]; rw [smul_one_smul]; rw [Pi.one_def]

/--
The map `Aᵢ ⟶ ⨂ᵢ Aᵢ` given by `a ↦ 1 ⊗ ... ⊗ a ⊗ 1 ⊗ ...`
-/
@[simps]
/--
Definition of `singleAlgHom` / `singleAlgHom` 的定义

English:
definition singleAlgHom
  signature: [DecidableEq ι] (i : ι)
  body: tprod R (MonoidHom.mulSingle _ i a)
  map_one' := by simp only [map_one]; rfl
  map_mul' a a' := by simp [map_mul]
  map_zero' := MultilinearMap.map_update_zero _ _ _
  map_add' _ _ := MultilinearMap.map_update_add _ _ _ _ _
  commutes' r := show tprodCoeff R _ _ = r • tprodCoeff R _ _ by
    rw [Algebra.algebraMap_eq_smul_one]; rw [← Pi.one_apply]; rw [MonoidHom.mulSingle_apply]; rw [Pi.mulSingle]; rw [smul_tprodCoeff]
    rfl

中文:
定义 singleAlgHom
  签名: [DecidableEq ι] (i : ι)
  定义体: tprod R (MonoidHom.mulSingle _ i a)
  map_one' := by simp only [map_one]; rfl
  map_mul' a a' := by simp [map_mul]
  map_zero' := MultilinearMap.map_update_zero _ _ _
  map_add' _ _ := MultilinearMap.map_update_add _ _ _ _ _
  commutes' r := show tprodCoeff R _ _ = r • tprodCoeff R _ _ by
    rw [Algebra.algebraMap_eq_smul_one]; rw [← Pi.one_apply]; rw [MonoidHom.mulSingle_apply]; rw [Pi.mulSingle]; rw [smul_tprodCoeff]
    rfl

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, mulSingle
-/
def singleAlgHom [DecidableEq ι] (i : ι) : A i ->ₐ[R] ⨂[R] i, A i where
  toFun a := tprod R (MonoidHom.mulSingle _ i a)
  map_one' := by simp only [map_one]; rfl
  map_mul' a a' := by simp [map_mul]
  map_zero' := MultilinearMap.map_update_zero _ _ _
  map_add' _ _ := MultilinearMap.map_update_add _ _ _ _ _
  commutes' r := show tprodCoeff R _ _ = r • tprodCoeff R _ _ by
    rw [Algebra.algebraMap_eq_smul_one]; rw [← Pi.one_apply]; rw [MonoidHom.mulSingle_apply]; rw [Pi.mulSingle]; rw [smul_tprodCoeff]
    rfl

/--
Lifting a multilinear map to an algebra homomorphism from tensor product
-/
@[simps!]
/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: {S : Type*} [Semiring S] [Algebra R S]
  body: AlgHom.ofLinearMap (lift f) (show lift f (tprod R 1) = 1 by simp [one])
.mpr by aesop LinearMap.map_mul_iff _

中文:
定义 liftAlgHom
  签名: {S : 类型} [半环 S] [代数 R S]
  定义体: AlgHom.ofLinearMap (lift f) (show lift f (tprod R 1) = 1 by simp [one])
.mpr by aesop LinearMap.map_mul_iff _

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, LinearMap, LinearMap.map_mul_iff, map_mul_iff, ofLinearMap
-/
def liftAlgHom {S : Type*} [Semiring S] [Algebra R S]
    (f : MultilinearMap R A S)
    (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y) : (⨂[R] i, A i) ->ₐ[R] S :=
AlgHom.ofLinearMap (lift f) (show lift f (tprod R 1) = 1 by simp [one])
.mpr by aesop LinearMap.map_mul_iff _

/--
lemma `tprod_noncommProd` / 引理 `tprod_noncommProd`

English:
lemma tprod_noncommProd
  given: {κ : Type*} (s : Finset κ) (x : κ -> Π i, A i) (hx)
  proof: Finset.map_noncommProd s x _ (tprodMonoidHom R)

中文:
引理 tprod_noncommProd
  条件: {κ : 类型} (s : 有限集 κ) (x : κ -> Π i, A i) (hx)
  证明: Finset.map_noncommProd s x _ (tprodMonoidHom R)
-/
@[simp] lemma tprod_noncommProd {κ : Type*} (s : Finset κ) (x : κ -> Π i, A i) (hx) :
    tprod R (s.noncommProd x hx) = s.noncommProd (fun k => tprod R (x k))
      (hx.imp fun _ _ => Commute.tprod) :=
  Finset.map_noncommProd s x _ (tprodMonoidHom R)

/-- To show two algebra morphisms from finite tensor products are equal, it suffices to show that
they agree on elements of the form $1 ⊗ ⋯ ⊗ a ⊗ 1 ⊗ ⋯$. -/
@[ext high]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: {S : Type*} [Finite ι] [DecidableEq ι] [Semiring S] [Algebra R S]
  proof: AlgHom.toLinearMap_injective PiTensorProduct.ext MultilinearMap.ext fun x =>
    suffices f.toMonoidHom.comp (tprodMonoidHom R) = g.toMonoidHom.comp (tprodMonoidHom R) from
      DFunLike.congr_fun this x
    MonoidHom.pi_ext fun i xi => DFunLike.congr_fun (h i) xi

中文:
定理 algHom_ext
  结论: {S : 类型} [有限 ι] [DecidableEq ι] [半环 S] [代数 R S]
  证明: AlgHom.toLinearMap_injective PiTensorProduct.ext MultilinearMap.ext fun x =>
    suffices f.toMonoidHom.comp (tprodMonoidHom R) = g.toMonoidHom.comp (tprodMonoidHom R) from
      DFunLike.congr_fun this x
    MonoidHom.pi_ext fun i xi => DFunLike.congr_fun (h i) xi

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, DFunLike, DFunLike.congr_fun, MonoidHom, MonoidHom.pi_ext, MultilinearMap, MultilinearMap.ext, PiTensorProduct, PiTensorProduct.ext, congr_fun, f.toMonoidHom.comp, g.toMonoidHom.comp, pi_ext, toLinearMap_injective, toMonoidHom, tprodMonoidHom
-/
theorem algHom_ext {S : Type*} [Finite ι] [DecidableEq ι] [Semiring S] [Algebra R S]
    ⦃f g : (⨂[R] i, A i) ->ₐ[R] S⦄ (h : forall i, f.comp (singleAlgHom i) = g.comp (singleAlgHom i)) :
    f = g :=
AlgHom.toLinearMap_injective PiTensorProduct.ext MultilinearMap.ext fun x =>
    suffices f.toMonoidHom.comp (tprodMonoidHom R) = g.toMonoidHom.comp (tprodMonoidHom R) from
      DFunLike.congr_fun this x
    MonoidHom.pi_ext fun i xi => DFunLike.congr_fun (h i) xi

end Semiring

noncomputable section Ring

variable [CommRing R] [forall i, Ring (A i)] [forall i, Algebra R (A i)]

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (⨂[R] i, A i) where
  body: instSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

中文:
实例 instRing
  签名: : 环 (⨂[R] i, A i) where
  定义体: instSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

Depends on / 依赖: instSemiring
-/
instance instRing : Ring (⨂[R] i, A i) where
  __ := instSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

end Ring

noncomputable section CommSemiring

variable [CommSemiring R] [forall i, CommSemiring (A i)] [forall i, Algebra R (A i)]

/--
lemma `mul_comm` / 引理 `mul_comm`

English:
lemma mul_comm
  given: (x y : ⨂[R] i, A i)
  statement: mul x y = mul y x
  proof: by
  suffices mul (R := R) (A := A) = mul.flip from
    DFunLike.congr_fun (DFunLike.congr_fun this x) y
  ext x y
  dsimp
  simp only [mul_tprod_tprod, mul_tprod_tprod, mul_comm x y]

中文:
引理 mul_comm
  条件: (x y : ⨂[R] i, A i)
  结论: mul x y = mul y x
  证明: by
  suffices mul (R := R) (A := A) = mul.flip from
    DFunLike.congr_fun (DFunLike.congr_fun this x) y
  ext x y
  dsimp
  simp only [mul_tprod_tprod, mul_tprod_tprod, mul_comm x y]
-/
protected lemma mul_comm (x y : ⨂[R] i, A i) : mul x y = mul y x := by
  suffices mul (R := R) (A := A) = mul.flip from
    DFunLike.congr_fun (DFunLike.congr_fun this x) y
  ext x y
  dsimp
  simp only [mul_tprod_tprod, mul_tprod_tprod, mul_comm x y]

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: : CommSemiring (⨂[R] i, A i) where
  body: instSemiring
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  mul_comm := PiTensorProduct.mul_comm

中文:
实例 instCommSemiring
  签名: : 交换半环 (⨂[R] i, A i) where
  定义体: instSemiring
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  mul_comm := PiTensorProduct.mul_comm

Depends on / 依赖: instSemiring
-/
instance instCommSemiring : CommSemiring (⨂[R] i, A i) where
  __ := instSemiring
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  mul_comm := PiTensorProduct.mul_comm

/--
lemma `tprod_prod` / 引理 `tprod_prod`

English:
lemma tprod_prod
  given: {κ : Type*} (s : Finset κ) (x : κ -> Π i, A i)
  proof: map_prod (tprodMonoidHom R) x s

中文:
引理 tprod_prod
  条件: {κ : 类型} (s : 有限集 κ) (x : κ -> Π i, A i)
  证明: map_prod (tprodMonoidHom R) x s
-/
@[simp] lemma tprod_prod {κ : Type*} (s : Finset κ) (x : κ -> Π i, A i) :
    tprod R (∏ k in s, x k) = ∏ k in s, tprod R (x k) :=
  map_prod (tprodMonoidHom R) x s

section

variable [Fintype ι]

variable (R ι)

/--
Definition of `constantBaseRingEquiv` / `constantBaseRingEquiv` 的定义

English:
definition constantBaseRingEquiv
  signature: : (⨂[R] _ : ι, R) ≃ₐ[R] R
  body: letI toFun := lift (MultilinearMap.mkPiAlgebra R ι R)
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap
      toFun
      ((lift.tprod _).trans Finset.prod_const_one)
      (by
        -- one of these is required, the other is a performance optimization
        let : IsScalarTower R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          IsScalarTower.right (R := R) (A := ⨂[R] (x : ι), R)
        let : SMulCommClass R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          Algebra.to_smulCommClass (R := R) (A := ⨂[R] x : ι, R)
        rw [LinearMap.map_mul_iff]
        ext
        change toFun (tprod R _ * tprod R _) = toFun (tprod R _) * toFun (tprod R _)
        simp_rw [tprod_mul_tprod, toFun, lift.tprod, MultilinearMap.mkPiAlgebra_apply,
          Pi.mul_apply, Finset.prod_mul_distrib]))
    (Algebra.ofId _ _)
    (by ext)
    (by classical ext)

中文:
定义 constantBaseRingEquiv
  签名: : (⨂[R] _ : ι, R) ≃ₐ[R] R
  定义体: letI toFun := lift (MultilinearMap.mkPiAlgebra R ι R)
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap
      toFun
      ((lift.tprod _).trans Finset.prod_const_one)
      (by
        -- one of these is required, the other is a performance optimization
        let : IsScalarTower R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          IsScalarTower.right (R := R) (A := ⨂[R] (x : ι), R)
        let : SMulCommClass R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          Algebra.to_smulCommClass (R := R) (A := ⨂[R] x : ι, R)
        rw [LinearMap.map_mul_iff]
        ext
        change toFun (tprod R _ * tprod R _) = toFun (tprod R _) * toFun (tprod R _)
        simp_rw [tprod_mul_tprod, toFun, lift.tprod, MultilinearMap.mkPiAlgebra_apply,
          Pi.mul_apply, Finset.prod_mul_distrib]))
    (Algebra.ofId _ _)
    (by ext)
    (by classical ext)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.ofLinearMap, Finset, Finset.prod_const_one, MultilinearMap, MultilinearMap.mkPiAlgebra, lift.tprod, mkPiAlgebra, ofAlgHom, ofLinearMap, prod_const_one
-/
noncomputable def constantBaseRingEquiv : (⨂[R] _ : ι, R) ≃ₐ[R] R :=
  letI toFun := lift (MultilinearMap.mkPiAlgebra R ι R)
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap
      toFun
      ((lift.tprod _).trans Finset.prod_const_one)
      (by
        -- one of these is required, the other is a performance optimization
        let : IsScalarTower R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          IsScalarTower.right (R := R) (A := ⨂[R] (x : ι), R)
        let : SMulCommClass R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          Algebra.to_smulCommClass (R := R) (A := ⨂[R] x : ι, R)
        rw [LinearMap.map_mul_iff]
        ext
        change toFun (tprod R _ * tprod R _) = toFun (tprod R _) * toFun (tprod R _)
        simp_rw [tprod_mul_tprod, toFun, lift.tprod, MultilinearMap.mkPiAlgebra_apply,
          Pi.mul_apply, Finset.prod_mul_distrib]))
    (Algebra.ofId _ _)
    (by ext)
    (by classical ext)

variable {R ι}

@[simp]
/--
theorem `constantBaseRingEquiv_tprod` / 定理 `constantBaseRingEquiv_tprod`

English:
theorem constantBaseRingEquiv_tprod
  given: (x : ι -> R)
  proof: by
  simp [constantBaseRingEquiv]

@[simp]

中文:
定理 constantBaseRingEquiv_tprod
  条件: (x : ι -> R)
  证明: by
  simp [constantBaseRingEquiv]

@[simp]

Depends on / 依赖: constantBaseRingEquiv
-/
theorem constantBaseRingEquiv_tprod (x : ι -> R) :
    constantBaseRingEquiv ι R (tprod R x) = ∏ i, x i := by
  simp [constantBaseRingEquiv]

@[simp]
/--
theorem `constantBaseRingEquiv_symm` / 定理 `constantBaseRingEquiv_symm`

English:
theorem constantBaseRingEquiv_symm
  given: (r : R)
  proof: rfl

中文:
定理 constantBaseRingEquiv_symm
  条件: (r : R)
  证明: rfl
-/
theorem constantBaseRingEquiv_symm (r : R) :
    (constantBaseRingEquiv ι R).symm r = algebraMap _ _ r := rfl

end

end CommSemiring

noncomputable section CommRing

variable [CommRing R] [forall i, CommRing (A i)] [forall i, Algebra R (A i)]
/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing (⨂[R] i, A i) where
  body: instCommSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

中文:
实例 instCommRing
  签名: : 交换环 (⨂[R] i, A i) where
  定义体: instCommSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

Depends on / 依赖: instCommSemiring
-/
instance instCommRing : CommRing (⨂[R] i, A i) where
  __ := instCommSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

end CommRing

end PiTensorProduct
