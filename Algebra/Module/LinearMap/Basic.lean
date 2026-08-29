/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Further results on (semi)linear maps
-/

@[expose] public section


assert_not_exists Submonoid Finset TrivialStar

open Function

universe u u' v w x y z

variable {R R' S M M' : Type*}

namespace LinearMap

section toFunAsLinearMap

variable {R M N A : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N] [SMulCommClass R A N]

variable (R M N A) in
/--
Definition of `ltoFun` / `ltoFun` 的定义

English:
definition ltoFun
  signature: : (M ->ₗ[R] N) ->ₗ[A] (M -> N) where
  body: f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 ltoFun
  签名: : (M ->ₗ[R] N) ->ₗ[A] (M -> N) where
  定义体: f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: f.toFun
-/
def ltoFun : (M ->ₗ[R] N) ->ₗ[A] (M -> N) where
  toFun f := f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
lemma `ltoFun_apply` / 引理 `ltoFun_apply`

English:
lemma ltoFun_apply
  given: {f : M ->ₗ[R] N}
  statement: ltoFun R M N A f = f
  proof: rfl

中文:
引理 ltoFun_apply
  条件: {f : M ->ₗ[R] N}
  结论: ltoFun R M N A f = f
  证明: rfl
-/
@[simp] lemma ltoFun_apply {f : M ->ₗ[R] N} : ltoFun R M N A f = f := rfl

end toFunAsLinearMap

section SMul

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R ->+* R'}

variable {S' T' : Type*}
variable [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M]
variable [Monoid T'] [DistribMulAction T' M] [SMulCommClass R T' M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M')
  body: { toFun := a • (f : M -> M')
      map_add' := fun x y => by simp only [DomMulAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x => by simp_rw [DomMulAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }

中文:
实例 :
  签名: SMul S'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M')
  定义体: { toFun := a • (f : M -> M')
      map_add' := fun x y => by simp only [DomMulAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x => by simp_rw [DomMulAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }

Depends on / 依赖: DomMulAct, DomMulAct.smul_apply, f.map_add, f.map_smul, map_add, map_smul, simp_rw, smul_add, smul_apply, smul_comm
-/
instance : SMul S'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M') where
  smul a f :=
    { toFun := a • (f : M -> M')
      map_add' := fun x y => by simp only [DomMulAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x => by simp_rw [DomMulAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }

/--
theorem `_root_.DomMulAct.smul_linearMap_apply` / 定理 `_root_.DomMulAct.smul_linearMap_apply`

English:
theorem _root_.DomMulAct.smul_linearMap_apply
  given: (a : S'ᵈᵐᵃ) (f : M ->ₛₗ[σ₁₂] M') (x : M)
  proof: rfl

@[simp]

中文:
定理 _root_.DomMulAct.smul_linearMap_apply
  条件: (a : S'ᵈᵐᵃ) (f : M ->ₛₗ[σ₁₂] M') (x : M)
  证明: rfl

@[simp]
-/
theorem _root_.DomMulAct.smul_linearMap_apply (a : S'ᵈᵐᵃ) (f : M ->ₛₗ[σ₁₂] M') (x : M) :
    (a • f) x = f (DomMulAct.mk.symm a • x) :=
  rfl

@[simp]
/--
theorem `_root_.DomMulAct.mk_smul_linearMap_apply` / 定理 `_root_.DomMulAct.mk_smul_linearMap_apply`

English:
theorem _root_.DomMulAct.mk_smul_linearMap_apply
  given: (a : S') (f : M ->ₛₗ[σ₁₂] M') (x : M)
  proof: rfl

中文:
定理 _root_.DomMulAct.mk_smul_linearMap_apply
  条件: (a : S') (f : M ->ₛₗ[σ₁₂] M') (x : M)
  证明: rfl
-/
theorem _root_.DomMulAct.mk_smul_linearMap_apply (a : S') (f : M ->ₛₗ[σ₁₂] M') (x : M) :
    (DomMulAct.mk a • f) x = f (a • x) :=
  rfl

/--
theorem `_root_.DomMulAct.coe_smul_linearMap` / 定理 `_root_.DomMulAct.coe_smul_linearMap`

English:
theorem _root_.DomMulAct.coe_smul_linearMap
  given: (a : S'ᵈᵐᵃ) (f : M ->ₛₗ[σ₁₂] M')
  proof: rfl

中文:
定理 _root_.DomMulAct.coe_smul_linearMap
  条件: (a : S'ᵈᵐᵃ) (f : M ->ₛₗ[σ₁₂] M')
  证明: rfl
-/
theorem _root_.DomMulAct.coe_smul_linearMap (a : S'ᵈᵐᵃ) (f : M ->ₛₗ[σ₁₂] M') :
    (a • f : M ->ₛₗ[σ₁₂] M') = a • (f : M -> M') :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S' T' M] : SMulCommClass S'ᵈᵐᵃ T'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M')
  body: ⟨fun s t f => ext fun m => by simp_rw [DomMulAct.smul_linearMap_apply, smul_comm]⟩

中文:
实例 [SMulCommClass
  签名: S' T' M] : SMulCommClass S'ᵈᵐᵃ T'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M')
  定义体: ⟨fun s t f => ext fun m => by simp_rw [DomMulAct.smul_linearMap_apply, smul_comm]⟩

Depends on / 依赖: DomMulAct, DomMulAct.smul_linearMap_apply, simp_rw, smul_comm, smul_linearMap_apply
-/
instance [SMulCommClass S' T' M] : SMulCommClass S'ᵈᵐᵃ T'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M') :=
  ⟨fun s t f => ext fun m => by simp_rw [DomMulAct.smul_linearMap_apply, smul_comm]⟩

end SMul


section Actions

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R ->+* R'}

section SMul

instance {S'} [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M] :
    DistribMulAction S'ᵈᵐᵃ (M ->ₛₗ[σ₁₂] M') where
  one_smul _ := ext fun _ => congr_arg _ (one_smul _ _)
  mul_smul _ _ _ := ext fun _ => congr_arg _ (mul_smul _ _ _)
  smul_add _ _ _ := ext fun _ => rfl
  smul_zero _ := ext fun _ => rfl

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M'] [SMulCommClass R' S M']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.IsTorsionFree
  signature: S M'] : Module.IsTorsionFree S (M ->ₛₗ[σ₁₂] M')
  body: coe_injective.moduleIsTorsionFree _ coe_smul

中文:
实例 [Module.IsTorsionFree
  签名: S M'] : Module.IsTorsionFree S (M ->ₛₗ[σ₁₂] M')
  定义体: coe_injective.moduleIsTorsionFree _ coe_smul

Depends on / 依赖: coe_injective, coe_injective.moduleIsTorsionFree, coe_smul, moduleIsTorsionFree
-/
instance [Module.IsTorsionFree S M'] : Module.IsTorsionFree S (M ->ₛₗ[σ₁₂] M') :=
  coe_injective.moduleIsTorsionFree _ coe_smul

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R S M] : Module Sᵈᵐᵃ (M ->ₛₗ[σ₁₂] M') where
  body: ext fun _ => by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ => by
    simp [DomMulAct.smul_linearMap_apply, DomMulAct.mk, MulOpposite.opEquiv]

中文:
实例 [SMulCommClass
  签名: R S M] : Module Sᵈᵐᵃ (M ->ₛₗ[σ₁₂] M') where
  定义体: ext fun _ => by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ => by
    simp [DomMulAct.smul_linearMap_apply, DomMulAct.mk, MulOpposite.opEquiv]

Depends on / 依赖: DomMulAct, DomMulAct.mk, DomMulAct.smul_linearMap_apply, MulOpposite, MulOpposite.opEquiv, add_apply, add_smul, map_add, opEquiv, simp_rw, smul_linearMap_apply, zero_smul
-/
instance [SMulCommClass R S M] : Module Sᵈᵐᵃ (M ->ₛₗ[σ₁₂] M') where
  add_smul _ _ _ := ext fun _ => by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ => by
    simp [DomMulAct.smul_linearMap_apply, DomMulAct.mk, MulOpposite.opEquiv]

end Module

end Actions

section mulLeftRight
variable {R A : Type*} [Semiring R]

section nonUnitalSemiring
variable (R A) [NonUnitalSemiring A] [Module R A]

@[simp]
/--
theorem `mulLeft_mul` / 定理 `mulLeft_mul`

English:
theorem mulLeft_mul
  given: [SMulCommClass R A A] (a b : A)
  proof: by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]

中文:
定理 mulLeft_mul
  条件: [SMulCommClass R A A] (a b : A)
  证明: by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]

Depends on / 依赖: comp_apply, mulLeft_apply, mul_assoc
-/
theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]
/--
theorem `mulRight_mul` / 定理 `mulRight_mul`

English:
theorem mulRight_mul
  given: [IsScalarTower R A A] (a b : A)
  proof: by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

中文:
定理 mulRight_mul
  条件: [IsScalarTower R A A] (a b : A)
  证明: by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

Depends on / 依赖: comp_apply, mulRight_apply, mul_assoc
-/
theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

end nonUnitalSemiring

section nonAssocSemiring
variable [NonAssocSemiring A] [Module R A]

/--
lemma `mulLeft_inj` / 引理 `mulLeft_inj`

English:
lemma mulLeft_inj
  given: [SMulCommClass R A A] {a b : A}
  proof: ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

中文:
引理 mulLeft_inj
  条件: [SMulCommClass R A A] {a b : A}
  证明: ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩
-/
@[simp] lemma mulLeft_inj [SMulCommClass R A A] {a b : A} :
    mulLeft R a = mulLeft R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

/--
lemma `mulRight_inj` / 引理 `mulRight_inj`

English:
lemma mulRight_inj
  given: [IsScalarTower R A A] {a b : A}
  proof: ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

中文:
引理 mulRight_inj
  条件: [IsScalarTower R A A] {a b : A}
  证明: ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩
-/
@[simp] lemma mulRight_inj [IsScalarTower R A A] {a b : A} :
    mulRight R a = mulRight R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

section
variable (R A)

@[simp]
/--
theorem `mulLeft_one` / 定理 `mulLeft_one`

English:
theorem mulLeft_one
  given: [SMulCommClass R A A]
  statement: mulLeft R (1 : A) = LinearMap.id
  proof: ext one_mul

@[simp]

中文:
定理 mulLeft_one
  条件: [SMulCommClass R A A]
  结论: mulLeft R (1 : A) = LinearMap.id
  证明: ext one_mul

@[simp]

Depends on / 依赖: one_mul
-/
theorem mulLeft_one [SMulCommClass R A A] : mulLeft R (1 : A) = LinearMap.id := ext one_mul

@[simp]
/--
theorem `mulLeft_eq_zero_iff` / 定理 `mulLeft_eq_zero_iff`

English:
theorem mulLeft_eq_zero_iff
  given: [SMulCommClass R A A] (a : A)
  statement: mulLeft R a = 0 ↔ a = 0
  proof: mulLeft_zero_eq_zero R A ▸ mulLeft_inj

@[simp]

中文:
定理 mulLeft_eq_zero_iff
  条件: [SMulCommClass R A A] (a : A)
  结论: mulLeft R a = 0 ↔ a = 0
  证明: mulLeft_zero_eq_zero R A ▸ mulLeft_inj

@[simp]

Depends on / 依赖: mulLeft_inj, mulLeft_zero_eq_zero
-/
theorem mulLeft_eq_zero_iff [SMulCommClass R A A] (a : A) : mulLeft R a = 0 ↔ a = 0 :=
  mulLeft_zero_eq_zero R A ▸ mulLeft_inj

@[simp]
/--
theorem `mulRight_one` / 定理 `mulRight_one`

English:
theorem mulRight_one
  given: [IsScalarTower R A A]
  statement: mulRight R (1 : A) = LinearMap.id
  proof: ext mul_one

@[simp]

中文:
定理 mulRight_one
  条件: [IsScalarTower R A A]
  结论: mulRight R (1 : A) = LinearMap.id
  证明: ext mul_one

@[simp]

Depends on / 依赖: mul_one
-/
theorem mulRight_one [IsScalarTower R A A] : mulRight R (1 : A) = LinearMap.id :=
  ext mul_one

@[simp]
/--
theorem `mulRight_eq_zero_iff` / 定理 `mulRight_eq_zero_iff`

English:
theorem mulRight_eq_zero_iff
  given: [IsScalarTower R A A] (a : A)
  statement: mulRight R a = 0 ↔ a = 0
  proof: mulRight_zero_eq_zero R A ▸ mulRight_inj

中文:
定理 mulRight_eq_zero_iff
  条件: [IsScalarTower R A A] (a : A)
  结论: mulRight R a = 0 ↔ a = 0
  证明: mulRight_zero_eq_zero R A ▸ mulRight_inj

Depends on / 依赖: mulRight_inj, mulRight_zero_eq_zero
-/
theorem mulRight_eq_zero_iff [IsScalarTower R A A] (a : A) : mulRight R a = 0 ↔ a = 0 :=
  mulRight_zero_eq_zero R A ▸ mulRight_inj

end
end nonAssocSemiring
end mulLeftRight

end LinearMap

namespace Sum

variable {ι κ R : Type*} [Semiring R]

/--
Definition of `elimZeroLeft` / `elimZeroLeft` 的定义

English:
definition elimZeroLeft
  signature: : (ι -> R) ->ₗ[R] (κ oplus ι -> R) where
  body: Sum.elim 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp

中文:
定义 elimZeroLeft
  签名: : (ι -> R) ->ₗ[R] (κ oplus ι -> R) where
  定义体: Sum.elim 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp
-/
@[simps] def elimZeroLeft : (ι -> R) ->ₗ[R] (κ oplus ι -> R) where
  toFun := Sum.elim 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp

/--
Definition of `elimZeroRight` / `elimZeroRight` 的定义

English:
definition elimZeroRight
  signature: : (ι -> R) ->ₗ[R] (ι oplus κ -> R) where
  body: fun f => Sum.elim f 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp

中文:
定义 elimZeroRight
  签名: : (ι -> R) ->ₗ[R] (ι oplus κ -> R) where
  定义体: fun f => Sum.elim f 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp
-/
@[simps] def elimZeroRight : (ι -> R) ->ₗ[R] (ι oplus κ -> R) where
  toFun := fun f => Sum.elim f 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp

end Sum
