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
The image of the intermediate field `F` of `L/K` under the inclusion `L ⊆ M`, viewed as an
intermediate field of `M/K`.
-/
/-
**IntermediateField.extendRight** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：extendRight : IntermediateField K M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of the intermediate field `F` of `L/K` under the inclusion `L ⊆ M`, vi
ewed as an
intermediate field of `M/K`.
-/
def extendRight : IntermediateField K M := F.map (Algebra.algHom K L M)

/-- The isomorphism between `F` and its image `F.extendRight M` in `M`. -/
/-
**IntermediateField.extendRightEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFiel
d`。
形式化陈述：extendRightEquiv : F ≃ₐ[K] (F.extendRight M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `F` and its image `F.extendRight M` in `M`.
-/
noncomputable def extendRightEquiv : F ≃ₐ[K] (F.extendRight M) := F.equivMap (Algebra.algHom K L M)

@[simp]
/-
**IntermediateField.algebraMap_extendRightEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：algebraMap_extendRightEquiv (a : F) : algebraMap (F.extendRight M) M (exte
ndRightEquiv F M a) = algebraMap F M a
参数：a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem algebraMap_extendRightEquiv (a : F) :
    algebraMap (F.extendRight M) M (extendRightEquiv F M a) = algebraMap F M a := rfl

@[simp]
/-
**IntermediateField.coe_extendRightEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：coe_extendRightEquiv (a : F) : (extendRightEquiv F M a : M) = algebraMap F
 M a
参数：a : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_extendRightEquiv (a : F) :
    (extendRightEquiv F M a : M) = algebraMap F M a := rfl

@[simp]
/-
**IntermediateField.algebraMap_extendRightEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：algebraMap_extendRightEquiv_symm (a : F.extendRight M) : algebraMap F M ((
extendRightEquiv F M).symm a) = a
参数：a : F.extendRight M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.algebraMap_extendRightEquiv`：algebraMap_extendRightEqu
iv (a : F) : algebraMap (F.extendRight M) M (extendRightEquiv F M a) = algebraMa
p F M a
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `IntermediateField.algebraMap_apply`：∀ {K : Type u_1} {L : Type u_2} [ins
t : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K 
L)   (x : ↥S), (algebraM…
-/
theorem algebraMap_extendRightEquiv_symm (a : F.extendRight M) :
    algebraMap F M ((extendRightEquiv F M).symm a) = a := by
  rw [← algebraMap_extendRightEquiv, AlgEquiv.apply_symm_apply, algebraMap_apply]

namespace extendRight

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra S F]

variable [Algebra S M] [IsScalarTower S F M]

/-
**IntermediateField.extendRight.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField.extendRight`。
形式化陈述：algebraMap_mem (s : S) : algebraMap S M s in F.extendRight M
参数：s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem algebraMap_mem (s : S) : algebraMap S M s ∈ F.extendRight M := by
  rw [IsScalarTower.algebraMap_apply S F M, IsScalarTower.algebraMap_apply F L M]
  exact ⟨algebraMap F L (algebraMap S F s), by simp, rfl⟩
/-
**IntermediateField.extendRight.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.ex
tendRight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (F.extendRight M) where
  smul s x := by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    exact (F.extendRight M).mul_mem (algebraMap_mem F M s) x.prop

@[simp]
/-
**IntermediateField.extendRight.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field.extendRight`。
形式化陈述：coe_smul (s : S) (x : F.extendRight M) : (s • x : F.extendRight M) = s • (
x : M)
参数：s : S；x : F.extendRight M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (s : S) (x : F.extendRight M) :
    (s • x : F.extendRight M) = s • (x : M) := rfl

-- The algebra instance is defined this way to avoid diamonds, see below
/-
**IntermediateField.extendRight.algebra** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateF
ield.extendRight`。
形式化陈述：algebra : Algebra S (F.extendRight M) where algebraMap
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.extendRight.algebraMap_mem`：algebraMap_mem (s : S) : a
lgebraMap S M s in F.extendRight M
-/
noncomputable instance algebra : Algebra S (F.extendRight M) where
  algebraMap := (algebraMap S M).codRestrict (F.extendRight M).toSubalgebra (algebraMap_mem F M ·)
  commutes' _ _ := Subtype.ext <| by simp [Algebra.commutes]
  smul_def' s x := Subtype.ext <| by
    convert_to! s • (x : M) = _
    rw [MulMemClass.coe_mul, RingHom.codRestrict_apply, ← Algebra.smul_def]

-- Check there is no diamond
/-
**IntermediateField.extendRight.** 是 Mathlib 中的一个示例，位于命名空间 `IntermediateField.ex
tendRight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Algebra S K] [IsScalarTower S K M] :
    ((F.extendRight M).algebra' : Algebra S (F.extendRight M)) =
      (algebra F M : Algebra S (F.extendRight M)) := by
  with_reducible_and_instances rfl
/-
**IntermediateField.extendRight.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.ex
tendRight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower S (F.extendRight M) M := IsScalarTower.of_algebraMap_eq' rfl
/-
**IntermediateField.extendRight.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.ex
tendRight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower S F (F.extendRight M) := IsScalarTower.to₁₂₃ S F (F.extendRight M) M
/-
**IntermediateField.extendRight.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.ex
tendRight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra R S] [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsScalarTower R S M] :
    IsScalarTower R S (F.extendRight M) :=
  IsScalarTower.to₁₂₃ R S (F.extendRight M) M

variable (S)

/--
Variant of `extendRightEquiv` giving an `S`-algebra isomorphism `F ≃ₐ[S] F.extendRight M`,
for a commutative ring `S` with `Algebra S F`.
-/
/-
**IntermediateField.extendRight._root_.IntermediateField.extendRightEquiv'** 是 M
athlib 中的一个定义，位于命名空间 `IntermediateField.extendRight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `extendRightEquiv` giving an `S`-algebra isomorphism `F ≃ₐ[S] F.exten
dRight M`,
for a commutative ring `S` with `Algebra S F`.
-/
noncomputable def _root_.IntermediateField.extendRightEquiv' : F ≃ₐ[S] (F.extendRight M) :=
  AlgEquiv.ofBijective (Algebra.algHom S F (F.extendRight M)) (extendRightEquiv F M).bijective

@[simp]
/-
**IntermediateField.extendRight.coe_extendRightEquiv'** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField.extendRight`。
形式化陈述：coe_extendRightEquiv' (a : F) : (extendRightEquiv' F M S a : M) = algebraM
ap F M a
参数：a : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_extendRightEquiv' (a : F) :
    (extendRightEquiv' F M S a : M) = algebraMap F M a := rfl

@[simp]
/-
**IntermediateField.extendRight.algebraMap_extendRightEquiv'** 是 Mathlib 中的一个定理，
位于命名空间 `IntermediateField.extendRight`。
形式化陈述：algebraMap_extendRightEquiv' (a : F) : algebraMap (F.extendRight M) M (ext
endRightEquiv' F M S a) = algebraMap F M a
参数：a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem algebraMap_extendRightEquiv' (a : F) :
    algebraMap (F.extendRight M) M (extendRightEquiv' F M S a) = algebraMap F M a := rfl

@[simp]
/-
**IntermediateField.extendRight.algebraMap_extendRightEquiv'_symm** 是 Mathlib 中的
一个定理，位于命名空间 `IntermediateField.extendRight`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (F : IntermediateField K L)   (M : Type u_3) [inst_3 : Field M]
 [inst_4 : Algebra K M] [inst_5 : Algebra L M] [inst_6 : IsScalarTower K L M]   
(S : Type u_5) [inst_7 : CommRing S] [inst_8 : Algebra S ↥F] [inst_9 : Algebra S
 M] [inst_10 : IsScalarTower S (↥F) M]   (a : ↥(F.extendRight M)), (algebraMap (
↥F) M) ((F.extendRightEquiv' M S).symm a) = ↑a
参数：F : IntermediateField K L；M : Type u_3；S : Type u_5；↥F；a : ↥(F.extendRight M)
；algebraMap (↥F) M；(F.extendRightEquiv' M S).symm a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.extendRight.algebraMap_extendRightEquiv'`：algebraMap_e
xtendRightEquiv' (a : F) : algebraMap (F.extendRight M) M (extendRightEquiv' F M
 S a) = algebraMap F M a
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `IntermediateField.algebraMap_apply`：∀ {K : Type u_1} {L : Type u_2} [ins
t : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K 
L)   (x : ↥S), (algebraM…
-/
theorem algebraMap_extendRightEquiv'_symm (a : F.extendRight M) :
    algebraMap F M ((extendRightEquiv' F M S).symm a) = a := by
  rw [← algebraMap_extendRightEquiv' F M S, AlgEquiv.apply_symm_apply, algebraMap_apply]

variable {S}
/-
**IntermediateField.extendRight.isFractionRing** 是 Mathlib 中的一个实例，位于命名空间 `Interm
ediateField.extendRight`。
形式化陈述：isFractionRing [IsFractionRing S F] : IsFractionRing S (F.extendRight M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsFractionRing.of_algEquiv`：IsFractionRing.of_algEquiv {R : Type*} [Comm
Semiring R] {K L : Type*} [CommSemiring K] [Algebra R K] [CommSemiring L] [Algeb
ra R L] [h : IsF…
-/
instance isFractionRing [IsFractionRing S F] :
    IsFractionRing S (F.extendRight M) :=
  .of_algEquiv (R := S) (L := F.extendRight M) (K := F) <| F.extendRightEquiv' M S
/-
**IntermediateField.extendRight.isIntegralClosure** 是 Mathlib 中的一个实例，位于命名空间 `Int
ermediateField.extendRight`。
形式化陈述：isIntegralClosure [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsInt
egralClosure S R F] : IsIntegralClosure S R (F.extendRight M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.of_algEquiv`：of_algEquiv {S : Type*} [CommRing S] [Alg
ebra A S] [Algebra R S] (f : B ≃ₐ[R] S) (h : forall x, algebraMap A S x = f (alg
ebraMap A B x)) : I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.algebraMap_apply`：∀ {K : Type u_1} {L : Type u_2} [ins
t : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K 
L)   (x : ↥S), (algebraM…
· 使用定理 `IntermediateField.extendRight.algebraMap_extendRightEquiv'`：algebraMap_e
xtendRightEquiv' (a : F) : algebraMap (F.extendRight M) M (extendRightEquiv' F M
 S a) = algebraMap F M a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IntermediateField.extendRight.instIsScalarTowerSubtypeMem`：∀ {K : Type u
_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (F
 : IntermediateField K L)   (M : Type u_3) [ins…
-/
instance isIntegralClosure [Algebra R F] [Algebra R M] [IsScalarTower R F M]
    [IsIntegralClosure S R F] :
    IsIntegralClosure S R (F.extendRight M) := by
  refine .of_algEquiv S (F.extendRightEquiv' M R) fun x ↦ ?_
  rw [Subtype.ext_iff, ← algebraMap_apply (F.extendRight M), ← algebraMap_apply (F.extendRight M),
    algebraMap_extendRightEquiv', ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

end IntermediateField.extendRight

