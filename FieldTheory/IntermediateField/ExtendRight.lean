/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Extending intermediate fields to a larger extension

Given a tower of field extensions `K ⊆ L ⊆ M` and an intermediate field `F` of `L/K`, this file
defines `IntermediateField.extendRight F M`, the image of `F` under the inclusion `L ⊆ M`,
as an intermediate field of `M/K`. It is canonically isomorphic to `F` as a `K`-algebra.

The main motivation is to embed a subextension `F/K` of `L/K` into a larger extension `M/K`.
This is useful for instance when one needs `M/K` to be Galois.

## Main definitions

- `IntermediateField.extendRight F M`: the intermediate field of `M/K` defined as the image of `F`
  under the map `L →ₐ[K] M`.
- `IntermediateField.extendRightEquiv F M`: the `K`-algebra isomorphism `F ≃ₐ[K] extendRight F M`.

## Main instances

- `IntermediateField.extendRight.algebra`: for `S` with `Algebra S F`, `S` acts
  on `extendRight F M`.
- `IntermediateField.extendRight.isFractionRing`: transfers the `IsFractionRing S F` instance.
- `IntermediateField.extendRight.isIntegralClosure`: transfers the
  `IsIntegralClosure S R F` instance.
-/

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/--
Definition of `extendRight` / `extendRight` 的定义

English:
definition extendRight
  signature: : IntermediateField K M
  body: F.map (Algebra.algHom K L M)

中文:
定义 extendRight
  签名: : 中间域 K M
  定义体: F.map (Algebra.algHom K L M)

Depends on / 依赖: Algebra, Algebra.algHom, F.map, algHom
-/
def extendRight : IntermediateField K M := F.map (Algebra.algHom K L M)

/--
Definition of `extendRightEquiv` / `extendRightEquiv` 的定义

English:
definition extendRightEquiv
  signature: : F ≃ₐ[K] (F.extendRight M)
  body: F.equivMap (Algebra.algHom K L M)

@[simp]

中文:
定义 extendRightEquiv
  签名: : F ≃ₐ[K] (F.extendRight M)
  定义体: F.equivMap (Algebra.algHom K L M)

@[simp]

Depends on / 依赖: Algebra, Algebra.algHom, F.equivMap, algHom, equivMap
-/
noncomputable def extendRightEquiv : F ≃ₐ[K] (F.extendRight M) := F.equivMap (Algebra.algHom K L M)

@[simp]
/--
theorem `algebraMap_extendRightEquiv` / 定理 `algebraMap_extendRightEquiv`

English:
theorem algebraMap_extendRightEquiv
  given: (a : F)
  proof: rfl

@[simp]

中文:
定理 algebraMap_extendRightEquiv
  条件: (a : F)
  证明: rfl

@[simp]
-/
theorem algebraMap_extendRightEquiv (a : F) :
    algebraMap (F.extendRight M) M (extendRightEquiv F M a) = algebraMap F M a := rfl

@[simp]
/--
theorem `coe_extendRightEquiv` / 定理 `coe_extendRightEquiv`

English:
theorem coe_extendRightEquiv
  given: (a : F)
  proof: rfl

@[simp]

中文:
定理 coe_extendRightEquiv
  条件: (a : F)
  证明: rfl

@[simp]
-/
theorem coe_extendRightEquiv (a : F) :
    (extendRightEquiv F M a : M) = algebraMap F M a := rfl

@[simp]
/--
theorem `algebraMap_extendRightEquiv_symm` / 定理 `algebraMap_extendRightEquiv_symm`

English:
theorem algebraMap_extendRightEquiv_symm
  given: (a : F.extendRight M)
  proof: by
  rw [← algebraMap_extendRightEquiv]; rw [AlgEquiv.apply_symm_apply]; rw [algebraMap_apply]

中文:
定理 algebraMap_extendRightEquiv_symm
  条件: (a : F.extendRight M)
  证明: by
  rw [← algebraMap_extendRightEquiv]; rw [AlgEquiv.apply_symm_apply]; rw [algebraMap_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, algebraMap_apply, algebraMap_extendRightEquiv, apply_symm_apply
-/
theorem algebraMap_extendRightEquiv_symm (a : F.extendRight M) :
    algebraMap F M ((extendRightEquiv F M).symm a) = a := by
  rw [← algebraMap_extendRightEquiv]; rw [AlgEquiv.apply_symm_apply]; rw [algebraMap_apply]

namespace extendRight

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra S F]

variable [Algebra S M] [IsScalarTower S F M]

/--
theorem `algebraMap_mem` / 定理 `algebraMap_mem`

English:
theorem algebraMap_mem
  given: (s : S)
  statement: algebraMap S M s in F.extendRight M
  proof: by
  rw [IsScalarTower.algebraMap_apply S F M]; rw [IsScalarTower.algebraMap_apply F L M]
  exact ⟨algebraMap F L (algebraMap S F s), by simp, rfl⟩

中文:
定理 algebraMap_mem
  条件: (s : S)
  结论: algebraMap S M s in F.extendRight M
  证明: by
  rw [IsScalarTower.algebraMap_apply S F M]; rw [IsScalarTower.algebraMap_apply F L M]
  exact ⟨algebraMap F L (algebraMap S F s), by simp, rfl⟩

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply
-/
theorem algebraMap_mem (s : S) : algebraMap S M s in F.extendRight M := by
  rw [IsScalarTower.algebraMap_apply S F M]; rw [IsScalarTower.algebraMap_apply F L M]
  exact ⟨algebraMap F L (algebraMap S F s), by simp, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (F.extendRight M)
  body: by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    exact (F.extendRight M).mul_mem (algebraMap_mem F M s) x.prop

@[simp]

中文:
实例 :
  签名: 标量乘法 S (F.extendRight M)
  定义体: by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    exact (F.extendRight M).mul_mem (algebraMap_mem F M s) x.prop

@[simp]

Depends on / 依赖: Algebra, Algebra.smul_def, F.extendRight, algebraMap_mem, extendRight, mul_mem, smul_def, x.prop
-/
instance : SMul S (F.extendRight M) where
  smul s x := by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    exact (F.extendRight M).mul_mem (algebraMap_mem F M s) x.prop

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (s : S) (x : F.extendRight M)
  proof: rfl

中文:
定理 coe_smul
  条件: (s : S) (x : F.extendRight M)
  证明: rfl
-/
theorem coe_smul (s : S) (x : F.extendRight M) :
    (s • x : F.extendRight M) = s • (x : M) := rfl

-- The algebra instance is defined this way to avoid diamonds, see below
/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra S (F.extendRight M) where
  body: (algebraMap S M).codRestrict (F.extendRight M).toSubalgebra (algebraMap_mem F M ·)
commutes' _ _ := Subtype.ext by simp [Algebra.commutes]
smul_def' s x := Subtype.ext by
    convert_to! s • (x : M) = _
    rw [MulMemClass.coe_mul]; rw [RingHom.codRestrict_apply]; rw [← Algebra.smul_def]

中文:
实例 algebra
  签名: : 代数 S (F.extendRight M) where
  定义体: (algebraMap S M).codRestrict (F.extendRight M).toSubalgebra (algebraMap_mem F M ·)
commutes' _ _ := Subtype.ext by simp [Algebra.commutes]
smul_def' s x := Subtype.ext by
    convert_to! s • (x : M) = _
    rw [MulMemClass.coe_mul]; rw [RingHom.codRestrict_apply]; rw [← Algebra.smul_def]

Depends on / 依赖: F.extendRight, algebraMap, algebraMap_mem, codRestrict, extendRight, toSubalgebra
-/
noncomputable instance algebra : Algebra S (F.extendRight M) where
  algebraMap := (algebraMap S M).codRestrict (F.extendRight M).toSubalgebra (algebraMap_mem F M ·)
commutes' _ _ := Subtype.ext by simp [Algebra.commutes]
smul_def' s x := Subtype.ext by
    convert_to! s • (x : M) = _
    rw [MulMemClass.coe_mul]; rw [RingHom.codRestrict_apply]; rw [← Algebra.smul_def]

-- Check there is no diamond
example [Algebra S K] [IsScalarTower S K M] :
    ((F.extendRight M).algebra' : Algebra S (F.extendRight M)) =
      (algebra F M : Algebra S (F.extendRight M)) := by
  with_reducible_and_instances rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower S (F.extendRight M) M
  body: IsScalarTower.of_algebraMap_eq' rfl

中文:
实例 :
  签名: 标量塔 S (F.extendRight M) M
  定义体: IsScalarTower.of_algebraMap_eq' rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower S (F.extendRight M) M := IsScalarTower.of_algebraMap_eq' rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower S F (F.extendRight M)
  body: IsScalarTower.to₁₂₃ S F (F.extendRight M) M

中文:
实例 :
  签名: 标量塔 S F (F.extendRight M)
  定义体: IsScalarTower.to₁₂₃ S F (F.extendRight M) M

Depends on / 依赖: F.extendRight, IsScalarTower, IsScalarTower.to, extendRight
-/
instance : IsScalarTower S F (F.extendRight M) := IsScalarTower.to₁₂₃ S F (F.extendRight M) M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: R S] [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsScalarTower R S M] :
  body: IsScalarTower.to₁₂₃ R S (F.extendRight M) M

中文:
实例 [代数
  签名: R S] [代数 R F] [代数 R M] [标量塔 R F M] [标量塔 R S M] :
  定义体: IsScalarTower.to₁₂₃ R S (F.extendRight M) M

Depends on / 依赖: F.extendRight, IsScalarTower, IsScalarTower.to, extendRight
-/
instance [Algebra R S] [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsScalarTower R S M] :
    IsScalarTower R S (F.extendRight M) :=
  IsScalarTower.to₁₂₃ R S (F.extendRight M) M

variable (S)

/--
Definition of `_root_.IntermediateField.extendRightEquiv'` / `_root_.IntermediateField.extendRightEquiv'` 的定义

English:
definition _root_.IntermediateField.extendRightEquiv'
  signature: : F ≃ₐ[S] (F.extendRight M)
  body: AlgEquiv.ofBijective (Algebra.algHom S F (F.extendRight M)) (extendRightEquiv F M).bijective

@[simp]

中文:
定义 _root_.中间域.extendRightEquiv'
  签名: : F ≃ₐ[S] (F.extendRight M)
  定义体: AlgEquiv.ofBijective (Algebra.algHom S F (F.extendRight M)) (extendRightEquiv F M).bijective

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.algHom, F.extendRight, algHom, bijective, extendRight, extendRightEquiv, ofBijective
-/
noncomputable def _root_.IntermediateField.extendRightEquiv' : F ≃ₐ[S] (F.extendRight M) :=
  AlgEquiv.ofBijective (Algebra.algHom S F (F.extendRight M)) (extendRightEquiv F M).bijective

@[simp]
/--
theorem `coe_extendRightEquiv'` / 定理 `coe_extendRightEquiv'`

English:
theorem coe_extendRightEquiv'
  given: (a : F)
  proof: rfl

@[simp]

中文:
定理 coe_extendRightEquiv'
  条件: (a : F)
  证明: rfl

@[simp]
-/
theorem coe_extendRightEquiv' (a : F) :
    (extendRightEquiv' F M S a : M) = algebraMap F M a := rfl

@[simp]
/--
theorem `algebraMap_extendRightEquiv'` / 定理 `algebraMap_extendRightEquiv'`

English:
theorem algebraMap_extendRightEquiv'
  given: (a : F)
  proof: rfl

@[simp]

中文:
定理 algebraMap_extendRightEquiv'
  条件: (a : F)
  证明: rfl

@[simp]
-/
theorem algebraMap_extendRightEquiv' (a : F) :
    algebraMap (F.extendRight M) M (extendRightEquiv' F M S a) = algebraMap F M a := rfl

@[simp]
/--
theorem `algebraMap_extendRightEquiv'_symm` / 定理 `algebraMap_extendRightEquiv'_symm`

English:
theorem algebraMap_extendRightEquiv'_symm
  given: (a : F.extendRight M)
  proof: by
  rw [← algebraMap_extendRightEquiv' F M S]; rw [AlgEquiv.apply_symm_apply]; rw [algebraMap_apply]

中文:
定理 algebraMap_extendRightEquiv'_symm
  条件: (a : F.extendRight M)
  证明: by
  rw [← algebraMap_extendRightEquiv' F M S]; rw [AlgEquiv.apply_symm_apply]; rw [algebraMap_apply]
-/
theorem algebraMap_extendRightEquiv'_symm (a : F.extendRight M) :
    algebraMap F M ((extendRightEquiv' F M S).symm a) = a := by
  rw [← algebraMap_extendRightEquiv' F M S]; rw [AlgEquiv.apply_symm_apply]; rw [algebraMap_apply]

variable {S}

/--
Instance `isFractionRing` / 实例 `isFractionRing`

English:
instance isFractionRing
  signature: [IsFractionRing S F]
  body: .of_algEquiv (R := S) (L := F.extendRight M) (K := F) F.extendRightEquiv' M S

中文:
实例 isFractionRing
  签名: [IsFractionRing S F]
  定义体: .of_algEquiv (R := S) (L := F.extendRight M) (K := F) F.extendRightEquiv' M S

Depends on / 依赖: F.extendRight, F.extendRightEquiv, extendRight, extendRightEquiv, of_algEquiv
-/
instance isFractionRing [IsFractionRing S F] :
    IsFractionRing S (F.extendRight M) :=
.of_algEquiv (R := S) (L := F.extendRight M) (K := F) F.extendRightEquiv' M S

/--
Instance `isIntegralClosure` / 实例 `isIntegralClosure`

English:
instance isIntegralClosure
  signature: [Algebra R F] [Algebra R M] [IsScalarTower R F M]
  body: by
  refine .of_algEquiv S (F.extendRightEquiv' M R) fun x => ?_
  rw [Subtype.ext_iff]; rw [← algebraMap_apply (F.extendRight M)]; rw [← algebraMap_apply (F.extendRight M)]; rw [algebraMap_extendRightEquiv']; rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]

中文:
实例 is整数egralClosure
  签名: [代数 R F] [代数 R M] [标量塔 R F M]
  定义体: by
  refine .of_algEquiv S (F.extendRightEquiv' M R) fun x => ?_
  rw [Subtype.ext_iff]; rw [← algebraMap_apply (F.extendRight M)]; rw [← algebraMap_apply (F.extendRight M)]; rw [algebraMap_extendRightEquiv']; rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]

Depends on / 依赖: F.extendRight, F.extendRightEquiv, IsScalarTower, IsScalarTower.algebraMap_apply, Subtype, Subtype.ext_iff, algebraMap_apply, algebraMap_extendRightEquiv, ext_iff, extendRight, extendRightEquiv, of_algEquiv
-/
instance isIntegralClosure [Algebra R F] [Algebra R M] [IsScalarTower R F M]
    [IsIntegralClosure S R F] :
    IsIntegralClosure S R (F.extendRight M) := by
  refine .of_algEquiv S (F.extendRightEquiv' M R) fun x => ?_
  rw [Subtype.ext_iff]; rw [← algebraMap_apply (F.extendRight M)]; rw [← algebraMap_apply (F.extendRight M)]; rw [algebraMap_extendRightEquiv']; rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]

end IntermediateField.extendRight
