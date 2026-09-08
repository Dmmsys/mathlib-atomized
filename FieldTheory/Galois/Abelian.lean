/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Galois.Infinite

/-!

# Abelian extensions

In this file, we define the typeclass of abelian extensions and provide some basic API.

-/

public section

variable (K L M : Type*) [Field K] [Field L] [Algebra K L]
variable [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The class of abelian extensions,
defined as galois extensions whose galois group is commutative. -/
/-
**IsAbelianGalois** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_4) → (L : Type u_5) → [inst : Field K] → [inst_1 : Field L] → 
[Algebra K L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of abelian extensions,
defined as galois extensions whose galois group is commutative.
-/
class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, IsMulCommutative Gal(L/K)

open scoped IsMulCommutative in
/-
**IsAbelianGalois.tower_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAbelianGalois.tower_bot [IsAbelianGalois K M] : IsAbelianGalois K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgEquiv.transfer_galois`：AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : Is
Galois F E ↔ IsGalois F E'
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : A ->ₐ[R] 
B) : Function.Surjective (f.rangeRestrict)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InfiniteGalois.normal_iff_isGalois`：normal_iff_isGalois (L : Intermediat
eField k K) [IsGalois k K] : L.fixingSubgroup.Normal ↔ IsGalois k L
· 使用定理 `IsAbelianGalois.toIsGalois`：∀ {K : Type u_4} {L : Type u_5} {inst : Fiel
d K} {inst_1 : Field L} {inst_2 : Algebra K L} [self : IsAbelianGalois K L],   I
sGalois K L
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `IsAbelianGalois.toIsMulCommutative`：∀ {K : Type u_4} {L : Type u_5} {ins
t : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} [self : IsAbelianGalois K
 L],   IsMulCommutative …
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma IsAbelianGalois.tower_bot [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  have : IsGalois K L :=
    ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M).rangeRestrict
      ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩).transfer_galois
        (E' := (IsScalarTower.toAlgHom K L M).fieldRange)).mpr
      ((InfiniteGalois.normal_iff_isGalois _).mp inferInstance)
  { is_comm.comm x y := by
      obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M x
      obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M y
      rw [← map_mul, ← map_mul, mul_comm] }

open scoped IsMulCommutative in
/-
**IsAbelianGalois.tower_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAbelianGalois.tower_top [IsAbelianGalois K M] : IsAbelianGalois L M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.tower_top_of_isGalois`：IsGalois.tower_top_of_isGalois [IsGalois
 F E] : IsGalois K E
· 使用定理 `IsAbelianGalois.toIsGalois`：∀ {K : Type u_4} {L : Type u_5} {inst : Fiel
d K} {inst_1 : Field L} {inst_2 : Algebra K L} [self : IsAbelianGalois K L],   I
sGalois K L
· 使用定理 `AlgEquiv.restrictScalars_injective`：restrictScalars_injective : Function
.Injective (restrictScalars R : (A ≃ₐ[S] B) -> A ≃ₐ[R] B)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsAbelianGalois.toIsMulCommutative`：∀ {K : Type u_4} {L : Type u_5} {ins
t : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} [self : IsAbelianGalois K
 L],   IsMulCommutative …
-/
lemma IsAbelianGalois.tower_top [IsAbelianGalois K M] :
    IsAbelianGalois L M :=
  have : IsGalois L M := .tower_top_of_isGalois K L M
  { is_comm.comm x y := AlgEquiv.restrictScalars_injective K
      (mul_comm (x.restrictScalars K) (y.restrictScalars K)) }

variable {K L M} in
omit [IsScalarTower K L M] [Algebra L M] in
/-
**IsAbelianGalois.of_algHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAbelianGalois.of_algHom (f : L ->ₐ[K] M) [IsAbelianGalois K M] : IsAbeli
anGalois K L
参数：f : L ->ₐ[K] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAbelianGalois.tower_bot`：IsAbelianGalois.tower_bot [IsAbelianGalois K 
M] : IsAbelianGalois K L
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
lemma IsAbelianGalois.of_algHom (f : L →ₐ[K] M) [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  letI := f.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  .tower_bot K L M
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAbelianGalois K L] (K' : IntermediateField K L) : IsAbelianGalois K K' :=
  .tower_bot K K' L
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    (K' : IntermediateField K L) : IsAbelianGalois K' L :=
  .tower_top K _ L
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAbelianGalois K K where
  is_comm.comm _ _ := Subsingleton.elim _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAbelianGalois K (⊥ : IntermediateField K L) :=
  .of_algHom (IntermediateField.botEquiv K L).toAlgHom
/-
**IsAbelianGalois.of_isCyclic** 是 Mathlib 中的一个定理，位于命名空间 `IsAbelianGalois`。
形式化陈述：∀ (K : Type u_1) (L : Type u_2) [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] [IsGalois K L]   [IsCyclic Gal(L/K)], IsAbelianGalois K L
参数：K : Type u_1；L : Type u_2；L/K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsAbelianGalois.of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] : IsAbelianGalois K L where
