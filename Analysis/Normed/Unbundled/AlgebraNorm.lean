/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Seminorm

/-!
# Algebra norms

We define algebra norms and multiplicative algebra norms.

## Main Definitions
* `AlgebraNorm` : an algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with
  the action of `R`.
* `MulAlgebraNorm` : a multiplicative algebra norm on an `R`-algebra `S` is a multiplicative
  ring norm on `S` compatible with the action of `R`.

## Tags

norm, algebra norm
-/

@[expose] public section

/--
Definition of `AlgebraNorm` / `AlgebraNorm` 的定义

English:
structure AlgebraNorm
  parameters: (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S]
  (no additional axioms)

中文:
结构 代数范数
  参数: (R : 类型) [SeminormedComm环 R] (S : 类型) [环 S] [代数 R S]
  (无附加公理)
-/
structure AlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S] extends
  RingNorm S, Seminorm R S

attribute [nolint docBlame] AlgebraNorm.toSeminorm AlgebraNorm.toRingNorm

instance (K : Type*) [NormedField K] : Inhabited (AlgebraNorm K K) :=
  ⟨{ toFun := norm
      map_zero' := norm_zero
      add_le' := norm_add_le
      neg' := norm_neg
      smul' := norm_mul
      mul_le' := norm_mul_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/--
Definition of `AlgebraNormClass` / `AlgebraNormClass` 的定义

English:
class AlgebraNormClass
  parameters: (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
  extends: RingNormClass F S Real, SeminormClass F R S
  (no additional axioms)

中文:
类 代数范数类
  参数: (F : 类型) (R : outParam <| 类型) [SeminormedComm环 R]
  继承: 环范数类 F S 实数, 半范数类 F R S
  (无附加公理)
-/
class AlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S Real] : Prop
    extends RingNormClass F S Real, SeminormClass F R S

namespace AlgebraNorm

variable {R : Type*} [SeminormedCommRing R] {S : Type*} [Ring S] [Algebra R S] {f : AlgebraNorm R S}

/--
Definition of `toRingSeminorm'` / `toRingSeminorm'` 的定义

English:
definition toRingSeminorm'
  signature: (f : AlgebraNorm R S)
  body: f.toRingNorm.toRingSeminorm

中文:
定义 toRingSeminorm'
  签名: (f : 代数范数 R S)
  定义体: f.toRingNorm.toRingSeminorm

Depends on / 依赖: f.toRingNorm.toRingSeminorm, toRingNorm, toRingSeminorm
-/
def toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S :=
  f.toRingNorm.toRingSeminorm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (AlgebraNorm R S) S Real
  body: f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr
    simp only at h
    ext s
    erw [h]
    rfl

中文:
实例 :
  签名: 函数状 (代数范数 R S) S 实数
  定义体: f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr
    simp only at h
    ext s
    erw [h]
    rfl

Depends on / 依赖: f.toFun
-/
instance : FunLike (AlgebraNorm R S) S Real where
  coe f := f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr
    simp only at h
    ext s
    erw [h]
    rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `algebraNormClass` / 实例 `algebraNormClass`

English:
instance algebraNormClass
  signature: : AlgebraNormClass (AlgebraNorm R S) R S where
  body: f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

中文:
实例 algebraNormClass
  签名: : 代数范数类 (代数范数 R S) R S where
  定义体: f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

Depends on / 依赖: f.map_zero, map_zero
-/
instance algebraNormClass : AlgebraNormClass (AlgebraNorm R S) R S where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (p : AlgebraNorm R S)
  statement: p.toFun = p
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (p : 代数范数 R S)
  结论: p.toFun = p
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (p : AlgebraNorm R S) : p.toFun = p := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : AlgebraNorm R S}
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  条件: {p q : 代数范数 R S}
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : AlgebraNorm R S} : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

/--
theorem `extends_norm'` / 定理 `extends_norm'`

English:
theorem extends_norm'
  given: (hf1 : f 1 = 1) (a : R)
  statement: f (a • (1 : S)) = ‖a‖
  proof: by
  rw [← mul_one ‖a‖]; rw [← hf1]; exact f.smul' _ _

中文:
定理 extends_norm'
  条件: (hf1 : f 1 = 1) (a : R)
  结论: f (a • (1 : S)) = ‖a‖
  证明: by
  rw [← mul_one ‖a‖]; rw [← hf1]; exact f.smul' _ _

Depends on / 依赖: f.smul, mul_one
-/
theorem extends_norm' (hf1 : f 1 = 1) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖]; rw [← hf1]; exact f.smul' _ _

/--
theorem `extends_norm` / 定理 `extends_norm`

English:
theorem extends_norm
  given: (hf1 : f 1 = 1) (a : R)
  statement: f (algebraMap R S a) = ‖a‖
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

中文:
定理 extends_norm
  条件: (hf1 : f 1 = 1) (a : R)
  结论: f (algebraMap R S a) = ‖a‖
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, extends_norm
-/
theorem extends_norm (hf1 : f 1 = 1) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `restriction` / `restriction` 的定义

English:
definition restriction
  signature: (A : Subalgebra R S) (f : AlgebraNorm R S)
  body: f x.val
  map_zero' := map_zero f
  add_le' x y := map_add_le_add _ _ _
  neg' x := map_neg_eq_map _ _
  mul_le' x y := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' x hx := by
    rw [← ZeroMemClass.coe_eq_zero]; exact eq_zero_of_map_eq_zero f hx
  smul' r x := map_smul_eq_mul _ _ _

中文:
定义 restriction
  签名: (A : 子代数 R S) (f : 代数范数 R S)
  定义体: f x.val
  map_zero' := map_zero f
  add_le' x y := map_add_le_add _ _ _
  neg' x := map_neg_eq_map _ _
  mul_le' x y := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' x hx := by
    rw [← ZeroMemClass.coe_eq_zero]; exact eq_zero_of_map_eq_zero f hx
  smul' r x := map_smul_eq_mul _ _ _

Depends on / 依赖: x.val
-/
def restriction (A : Subalgebra R S) (f : AlgebraNorm R S) : AlgebraNorm R A where
  toFun x := f x.val
  map_zero' := map_zero f
  add_le' x y := map_add_le_add _ _ _
  neg' x := map_neg_eq_map _ _
  mul_le' x y := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' x hx := by
    rw [← ZeroMemClass.coe_eq_zero]; exact eq_zero_of_map_eq_zero f hx
  smul' r x := map_smul_eq_mul _ _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `isScalarTower_restriction` / `isScalarTower_restriction` 的定义

English:
definition isScalarTower_restriction
  signature: {A : Type*} [CommRing A] [Algebra R A] [Algebra A S]
  body: f (algebraMap A S x)
  map_zero' := by simp only [map_zero]
  add_le' x y := by simp only [map_add, map_add_le_add]
  neg' x := by simp only [map_neg, map_neg_eq_map]
  mul_le' x y := by simp only [map_mul, map_mul_le_mul]
  eq_zero_of_map_eq_zero' x hx := by
    rw [← map_eq_zero_iff (algebraMap A 

中文:
定义 isScalarTower_restriction
  签名: {A : 类型} [交换环 A] [代数 R A] [代数 A S]
  定义体: f (algebraMap A S x)
  map_zero' := by simp only [map_zero]
  add_le' x y := by simp only [map_add, map_add_le_add]
  neg' x := by simp only [map_neg, map_neg_eq_map]
  mul_le' x y := by simp only [map_mul, map_mul_le_mul]
  eq_zero_of_map_eq_zero' x hx := by
    rw [← map_eq_zero_iff (algebraMap A 

Depends on / 依赖: algebraMap
-/
def isScalarTower_restriction {A : Type*} [CommRing A] [Algebra R A] [Algebra A S]
    [IsScalarTower R A S] (hinj : Function.Injective (algebraMap A S)) (f : AlgebraNorm R S) :
    AlgebraNorm R A where
  toFun x := f (algebraMap A S x)
  map_zero' := by simp only [map_zero]
  add_le' x y := by simp only [map_add, map_add_le_add]
  neg' x := by simp only [map_neg, map_neg_eq_map]
  mul_le' x y := by simp only [map_mul, map_mul_le_mul]
  eq_zero_of_map_eq_zero' x hx := by
    rw [← map_eq_zero_iff (algebraMap A S) hinj]
    exact eq_zero_of_map_eq_zero f hx
  smul' r x := by
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    simp only [← smul_eq_mul, algebraMap_smul, map_smul_eq_mul]

end AlgebraNorm

/--
Definition of `MulAlgebraNorm` / `MulAlgebraNorm` 的定义

English:
structure MulAlgebraNorm
  parameters: (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S]
  extends: MulRingNorm S, Seminorm R S
  (no additional axioms)

中文:
结构 乘法代数范数
  参数: (R : 类型) [SeminormedComm环 R] (S : 类型) [环 S] [代数 R S]
  继承: 乘法环范数 S, 半范数 R S
  (无附加公理)
-/
structure MulAlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S]
  extends MulRingNorm S, Seminorm R S

attribute [nolint docBlame] MulAlgebraNorm.toSeminorm MulAlgebraNorm.toMulRingNorm

instance (K : Type*) [NormedField K] : Inhabited (MulAlgebraNorm K K) :=
  ⟨{ toFun := norm
      map_zero' := norm_zero
      add_le' := norm_add_le
      neg' := norm_neg
      smul' := norm_mul
      map_one' := norm_one
      map_mul' := norm_mul
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/--
Definition of `MulAlgebraNormClass` / `MulAlgebraNormClass` 的定义

English:
class MulAlgebraNormClass
  parameters: (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
  extends: MulRingNormClass F S Real, SeminormClass F R S
  (no additional axioms)

中文:
类 乘法代数范数类
  参数: (F : 类型) (R : outParam <| 类型) [SeminormedComm环 R]
  继承: 乘法环范数类 F S 实数, 半范数类 F R S
  (无附加公理)
-/
class MulAlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S Real] : Prop
    extends MulRingNormClass F S Real, SeminormClass F R S

namespace MulAlgebraNorm

variable {R S : outParam <| Type*} [SeminormedCommRing R] [Ring S] [Algebra R S]
  {f : AlgebraNorm R S}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (MulAlgebraNorm R S) S Real
  body: f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, DFunLike.coe_fn_eq] at h
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := f'; congr

中文:
实例 :
  签名: 函数状 (乘法代数范数 R S) S 实数
  定义体: f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, DFunLike.coe_fn_eq] at h
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := f'; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (MulAlgebraNorm R S) S Real where
  coe f := f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, DFunLike.coe_fn_eq] at h
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := f'; congr

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `mulAlgebraNormClass` / 实例 `mulAlgebraNormClass`

English:
instance mulAlgebraNormClass
  signature: : MulAlgebraNormClass (MulAlgebraNorm R S) R S where
  body: f.map_zero'
  map_add_le_add f := f.add_le'
  map_one f := f.map_one'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

中文:
实例 mulAlgebraNormClass
  签名: : 乘法代数范数类 (乘法代数范数 R S) R S where
  定义体: f.map_zero'
  map_add_le_add f := f.add_le'
  map_one f := f.map_one'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

Depends on / 依赖: f.map_zero, map_zero
-/
instance mulAlgebraNormClass : MulAlgebraNormClass (MulAlgebraNorm R S) R S where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_one f := f.map_one'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (p : MulAlgebraNorm R S)
  statement: p.toFun = p
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (p : 乘法代数范数 R S)
  结论: p.toFun = p
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (p : MulAlgebraNorm R S) : p.toFun = p := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : MulAlgebraNorm R S}
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  条件: {p q : 乘法代数范数 R S}
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : MulAlgebraNorm R S} : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

/--
theorem `extends_norm'` / 定理 `extends_norm'`

English:
theorem extends_norm'
  given: (f : MulAlgebraNorm R S) (a : R)
  statement: f (a • (1 : S)) = ‖a‖
  proof: by
  rw [← mul_one ‖a‖]; rw [← f.map_one']; rw [← f.smul']; rw [toFun_eq_coe]

中文:
定理 extends_norm'
  条件: (f : 乘法代数范数 R S) (a : R)
  结论: f (a • (1 : S)) = ‖a‖
  证明: by
  rw [← mul_one ‖a‖]; rw [← f.map_one']; rw [← f.smul']; rw [toFun_eq_coe]

Depends on / 依赖: f.map_one, f.smul, map_one, mul_one, toFun_eq_coe
-/
theorem extends_norm' (f : MulAlgebraNorm R S) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖]; rw [← f.map_one']; rw [← f.smul']; rw [toFun_eq_coe]

/--
theorem `extends_norm` / 定理 `extends_norm`

English:
theorem extends_norm
  given: (f : MulAlgebraNorm R S) (a : R)
  statement: f (algebraMap R S a) = ‖a‖
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' _ _

中文:
定理 extends_norm
  条件: (f : 乘法代数范数 R S) (a : R)
  结论: f (algebraMap R S a) = ‖a‖
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' _ _

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, extends_norm
-/
theorem extends_norm (f : MulAlgebraNorm R S) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' _ _

/--
Definition of `toAlgebraNorm` / `toAlgebraNorm` 的定义

English:
definition toAlgebraNorm
  signature: (f : MulAlgebraNorm R S)
  body: f
  mul_le' _ _ := (f.map_mul' _ _).le

中文:
定义 toAlgebraNorm
  签名: (f : 乘法代数范数 R S)
  定义体: f
  mul_le' _ _ := (f.map_mul' _ _).le
-/
def toAlgebraNorm (f : MulAlgebraNorm R S) : AlgebraNorm R S where
  __ := f
  mul_le' _ _ := (f.map_mul' _ _).le

/--
Instance `instCoeAlgebraNorm` / 实例 `instCoeAlgebraNorm`

English:
instance instCoeAlgebraNorm
  signature: : Coe (MulAlgebraNorm R S) (AlgebraNorm R S)
  body: ⟨toAlgebraNorm⟩

@[simp]

中文:
实例 instCoeAlgebraNorm
  签名: : Coe (乘法代数范数 R S) (代数范数 R S)
  定义体: ⟨toAlgebraNorm⟩

@[simp]

Depends on / 依赖: toAlgebraNorm
-/
instance instCoeAlgebraNorm : Coe (MulAlgebraNorm R S) (AlgebraNorm R S) := ⟨toAlgebraNorm⟩

@[simp]
/--
lemma `coe_AlgebraNorm` / 引理 `coe_AlgebraNorm`

English:
lemma coe_AlgebraNorm
  given: (f : MulAlgebraNorm R S)
  statement: ⇑(f : AlgebraNorm R S) = ⇑f
  proof: rfl

中文:
引理 coe_AlgebraNorm
  条件: (f : 乘法代数范数 R S)
  结论: ⇑(f : 代数范数 R S) = ⇑f
  证明: rfl
-/
lemma coe_AlgebraNorm (f : MulAlgebraNorm R S) : ⇑(f : AlgebraNorm R S) = ⇑f := rfl

end MulAlgebraNorm

namespace NormedAlgebra

variable (K L : Type*) [NormedField K] [NormedField L] [NormedAlgebra K L]

/--
Definition of `toMulAlgebraNorm` / `toMulAlgebraNorm` 的定义

English:
definition toMulAlgebraNorm
  signature: : MulAlgebraNorm K L where
  body: NormedField.toMulRingNorm L
  smul' r x := by
    simp only [Algebra.smul_def, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
      map_mul, mul_eq_mul_right_iff, map_eq_zero]
exact Or.inl norm_algebraMap' L r

@[simp]

中文:
定义 toMulAlgebraNorm
  签名: : 乘法代数范数 K L where
  定义体: NormedField.toMulRingNorm L
  smul' r x := by
    simp only [Algebra.smul_def, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
      map_mul, mul_eq_mul_right_iff, map_eq_zero]
exact Or.inl norm_algebraMap' L r

@[simp]

Depends on / 依赖: NormedField, NormedField.toMulRingNorm, toMulRingNorm
-/
def toMulAlgebraNorm : MulAlgebraNorm K L where
  __ := NormedField.toMulRingNorm L
  smul' r x := by
    simp only [Algebra.smul_def, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
      map_mul, mul_eq_mul_right_iff, map_eq_zero]
exact Or.inl norm_algebraMap' L r

@[simp]
/--
lemma `toMulAlgebraNorm_apply` / 引理 `toMulAlgebraNorm_apply`

English:
lemma toMulAlgebraNorm_apply
  given: (x : L)
  statement: toMulAlgebraNorm K L x = ‖x‖
  proof: rfl

中文:
引理 toMulAlgebraNorm_apply
  条件: (x : L)
  结论: toMulAlgebraNorm K L x = ‖x‖
  证明: rfl
-/
lemma toMulAlgebraNorm_apply (x : L) : toMulAlgebraNorm K L x = ‖x‖ := rfl

end NormedAlgebra

namespace MulRingNorm

variable {R : Type*} [NonAssocRing R]

/--
Definition of `toRingNorm` / `toRingNorm` 的定义

English:
definition toRingNorm
  signature: (f : MulRingNorm R)
  body: f
  __ := f
  mul_le' x y := le_of_eq (f.map_mul' x y)

中文:
定义 toRingNorm
  签名: (f : 乘法环范数 R)
  定义体: f
  __ := f
  mul_le' x y := le_of_eq (f.map_mul' x y)
-/
def toRingNorm (f : MulRingNorm R) : RingNorm R where
  toFun := f
  __ := f
  mul_le' x y := le_of_eq (f.map_mul' x y)

/--
theorem `isPowMul` / 定理 `isPowMul`

English:
theorem isPowMul
  given: {A : Type*} [Ring A] (f : MulRingNorm A)
  statement: IsPowMul f
  proof: fun x n hn => by
  cases n
  · lia
  · rw [map_pow]

中文:
定理 isPowMul
  条件: {A : 类型} [环 A] (f : 乘法环范数 A)
  结论: IsPowMul f
  证明: fun x n hn => by
  cases n
  · lia
  · rw [map_pow]

Depends on / 依赖: codiscreteEquiv, codiscreteEquiv.decidableEq, decidableEq, map_pow
-/
theorem isPowMul {A : Type*} [Ring A] (f : MulRingNorm A) : IsPowMul f := fun x n hn => by
  cases n
  · lia
  · rw [map_pow]

end MulRingNorm
