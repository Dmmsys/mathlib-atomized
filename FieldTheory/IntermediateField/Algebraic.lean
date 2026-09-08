/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Tower
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Results on finite dimensionality and algebraicity of intermediate fields.
-/

@[expose] public section

open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {S : IntermediateField K L}

/-
**IntermediateField.coe_isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K
] [Algebra R L] [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegra
l R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem IntermediateField.coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
    [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

/-- Turn an algebraic subalgebra into an intermediate field, `Subalgebra.IsAlgebraic` version. -/
/-
**Subalgebra.IsAlgebraic.toIntermediateField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.IsAlgebraic.toIntermediateField {S : Subalgebra K L} (hS : S.Is
Algebraic) : IntermediateField K L where toSubalgebra
参数：hS : S.IsAlgebraic。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an algebraic subalgebra into an intermediate field, `Subalgebra.IsAlgebraic
` version.
-/
def Subalgebra.IsAlgebraic.toIntermediateField {S : Subalgebra K L} (hS : S.IsAlgebraic) :
    IntermediateField K L where
  toSubalgebra := S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin

/-- Turn an algebraic subalgebra into an intermediate field, `Algebra.IsAlgebraic` version. -/
/-
**Algebra.IsAlgebraic.toIntermediateField** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.toIntermediateField (S : Subalgebra K L) [Algebra.IsAl
gebraic K S] : IntermediateField K L
参数：S : Subalgebra K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an algebraic subalgebra into an intermediate field, `Algebra.IsAlgebraic` v
ersion.
-/
abbrev Algebra.IsAlgebraic.toIntermediateField (S : Subalgebra K L) [Algebra.IsAlgebraic K S] :
    IntermediateField K L := (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

namespace IntermediateField

/-
**IntermediateField.isAlgebraic_tower_bot** 是 Mathlib 中的一个实例，位于命名空间 `Intermediat
eField`。
形式化陈述：isAlgebraic_tower_bot [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic K S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.of_injective`：Algebra.IsAlgebraic.of_injective (f : 
A ->ₐ[R] B) (hf : Function.Injective f) [Algebra.IsAlgebraic R B] : Algebra.IsAl
gebraic R A
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
instance isAlgebraic_tower_bot [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic K S :=
  Algebra.IsAlgebraic.of_injective S.val S.val.injective
/-
**IntermediateField.isAlgebraic_tower_top** 是 Mathlib 中的一个实例，位于命名空间 `Intermediat
eField`。
形式化陈述：isAlgebraic_tower_top [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic S L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.tower_top`：Algebra.IsAlgebraic.tower_top [Algebra.Is
Algebraic K A] : Algebra.IsAlgebraic L A
-/
instance isAlgebraic_tower_top [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic S L :=
  Algebra.IsAlgebraic.tower_top (K := K) S

section FiniteDimensional

variable (F E : IntermediateField K L)

/-
**IntermediateField.finiteDimensional_left** 是 Mathlib 中的一个实例，位于命名空间 `Intermedia
teField`。
形式化陈述：finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.left`：∀ (F : Type u) (K : Type v) (A : Type w) [inst :
 Ring F] [inst_1 : Ring K] [inst_2 : _root_.Module F K]   [inst_3 : AddCommGroup
 A] [inst_4 …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F := .left K F L
/-
**IntermediateField.finiteDimensional_right** 是 Mathlib 中的一个实例，位于命名空间 `Intermedi
ateField`。
形式化陈述：finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.right`：∀ (F : Type u) (K : Type v) (A : Type w) [inst 
: Semiring F] [inst_1 : Semiring K] [inst_2 : _root_.Module F K]   [inst_3 : Add
CommMonoid A]…
-/
instance finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L := .right K F L

@[simp]
/-
**IntermediateField.rank_eq_rank_subalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl

@[simp]
/-
**IntermediateField.finrank_eq_finrank_subalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl

variable {F} {E}

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K] ≤ [F : K]` are finite,
then `F = E`. -/
/-
**IntermediateField.eq_of_le_of_finrank_le** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：eq_of_le_of_finrank_le [hfin : FiniteDimensional K E] (h_le : F <= E) (h_f
inrank : finrank K E <= finrank K F) : F = E
参数：h_le : F <= E；h_finrank : finrank K E <= finrank K F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `Subalgebra.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le (h_le : F <= E
) (h_finrank : finrank K E <= finrank K F) : F = E

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K] ≤ [F : K]` 
are finite,
then `F = E`.
-/
theorem eq_of_le_of_finrank_le [hfin : FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  haveI : Module.Finite K E.toSubalgebra := hfin
  toSubalgebra_injective <| Subalgebra.eq_of_le_of_finrank_le h_le h_finrank

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[F : K] = [E : K]` are finite,
then `F = E`. -/
/-
**IntermediateField.eq_of_le_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：eq_of_le_of_finrank_eq [FiniteDimensional K E] (h_le : F <= E) (h_finrank 
: finrank K F = finrank K E) : F = E
参数：h_le : F <= E；h_finrank : finrank K F = finrank K E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le [hfin :
 FiniteDimensional K E] (h_le : F <= E) (h_finrank : finrank K E <= finrank K F)
 : F = E
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K` such that `[F : K] = [E : K]` 
are finite,
then `F = E`.
-/
theorem eq_of_le_of_finrank_eq [FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K]` is finite,
then `F = E` iff `[F : K] = [E : K]`. -/
/-
**IntermediateField.eq_iff_finrank_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：eq_iff_finrank_eq_of_le [FiniteDimensional K E] (h_le : F <= E) : F = E ↔ 
finrank K F = finrank K E
参数：h_le : F <= E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq [Finite
Dimensional K E] (h_le : F <= E) (h_finrank : finrank K F = finrank K E) : F = E

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K]` is finite,
then `F = E` iff `[F : K] = [E : K]`.
-/
theorem eq_iff_finrank_eq_of_le [FiniteDimensional K E] (h_le : F ≤ E) :
    F = E ↔ finrank K F = finrank K E :=
  ⟨fun h ↦ by rw [h], eq_of_le_of_finrank_eq h_le⟩

-- If `F ≤ E` are two intermediate fields of a finite extension `L / K` such that
-- `[L : F] ≤ [L : E]`, then `F = E`. Marked as private since it's a direct corollary of
-- `eq_of_le_of_finrank_le'` (the `FiniteDimensional K L` implies `FiniteDimensional F L`
-- automatically by typeclass resolution).
/-
**IntermediateField.eq_of_le_of_finrank_le''** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eq_of_le_of_finrank_le'' [FiniteDimensional K L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] ≤ [L : E]` are finite,
then `F = E`. -/
/-
**IntermediateField.eq_of_le_of_finrank_le'** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：eq_of_le_of_finrank_le' [FiniteDimensional F L] (h_le : F <= E) (h_finrank
 : finrank F L <= finrank E L) : F = E
参数：h_le : F <= E；h_finrank : finrank F L <= finrank E L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.mem_extendScalars`：mem_extendScalars : x in extendScal
ars h ↔ x in E
· 使用定理 `_private.Mathlib.FieldTheory.IntermediateField.Algebraic.0.IntermediateF
ield.eq_of_le_of_finrank_le''`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] 
[inst_1 : Field L] [inst_2 : Algebra K L] {F E : IntermediateField K L}   [Finit
eDimensiona…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.extendScalars_le_extendScalars_iff`：extendScalars_le_e
xtendScalars_iff : extendScalars h <= extendScalars h' ↔ E <= E'

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] ≤ [L : E]` 
are finite,
then `F = E`.
-/
theorem eq_of_le_of_finrank_le' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  refine le_antisymm h_le (fun l hl ↦ ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] = [L : E]` are finite,
then `F = E`. -/
/-
**IntermediateField.eq_of_le_of_finrank_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：eq_of_le_of_finrank_eq' [FiniteDimensional F L] (h_le : F <= E) (h_finrank
 : finrank F L = finrank E L) : F = E
参数：h_le : F <= E；h_finrank : finrank F L = finrank E L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.eq_of_le_of_finrank_le'`：eq_of_le_of_finrank_le' [Fini
teDimensional F L] (h_le : F <= E) (h_finrank : finrank F L <= finrank E L) : F 
= E
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] = [L : E]` 
are finite,
then `F = E`.
-/
theorem eq_of_le_of_finrank_eq' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L = finrank E L) : F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F]` is finite,
then `F = E` iff `[L : F] = [L : E]`. -/
/-
**IntermediateField.eq_iff_finrank_eq_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：eq_iff_finrank_eq_of_le' [FiniteDimensional F L] (h_le : F <= E) : F = E ↔
 finrank F L = finrank E L
参数：h_le : F <= E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.eq_of_le_of_finrank_eq'`：eq_of_le_of_finrank_eq' [Fini
teDimensional F L] (h_le : F <= E) (h_finrank : finrank F L = finrank E L) : F =
 E

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F]` is finite,
then `F = E` iff `[L : F] = [L : E]`.
-/
theorem eq_iff_finrank_eq_of_le' [FiniteDimensional F L] (h_le : F ≤ E) :
    F = E ↔ finrank F L = finrank E L :=
  ⟨fun h ↦ by rw [h], eq_of_le_of_finrank_eq' h_le⟩
/-
**IntermediateField.finrank_lt_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：finrank_lt_of_gt [FiniteDimensional F L] (H : F < E) : Module.finrank E L 
< Module.finrank F L
参数：H : F < E。
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
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `Module.finrank_top_le_finrank_of_isScalarTower`：Module.finrank_top_le_fi
nrank_of_isScalarTower [Module.Finite R M] [Semiring S] [Module S M] [Module R S
] [IsScalarTower R S S] [FaithfulSMu…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IntermediateField.eq_of_le_of_finrank_eq'`：eq_of_le_of_finrank_eq' [Fini
teDimensional F L] (h_le : F <= E) (h_finrank : finrank F L = finrank E L) : F =
 E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma finrank_lt_of_gt [FiniteDimensional F L] (H : F < E) :
    Module.finrank E L < Module.finrank F L := by
  let := (IntermediateField.inclusion H.le).toAlgebra
  have : IsScalarTower F E L := .of_algebraMap_eq' rfl
  refine lt_of_le_of_ne ?_ ?_
  · exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _
  · exact .symm (mt (eq_of_le_of_finrank_eq' H.le) H.ne)
/-
**IntermediateField.finrank_dvd_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：finrank_dvd_of_le_left (h : F <= E) : finrank E L ∣ finrank F L
参数：h : F <= E。
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
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Module.finrank_dvd_finrank_left`：Module.finrank_dvd_finrank_left : Modul
e.finrank K A ∣ Module.finrank F A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem finrank_dvd_of_le_left (h : F ≤ E) : finrank E L ∣ finrank F L := by
  let _ := (inclusion h).toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  exact Module.finrank_dvd_finrank_left F E L
/-
**IntermediateField.finrank_dvd_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：finrank_dvd_of_le_right (h : F <= E) : finrank K F ∣ finrank K E
参数：h : F <= E。
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
· 使用定理 `Module.finrank_dvd_finrank_right`：Module.finrank_dvd_finrank_right : Mod
ule.finrank F K ∣ Module.finrank F A
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem finrank_dvd_of_le_right (h : F ≤ E) : finrank K F ∣ finrank K E := by
  let _ := (inclusion h).toRingHom.toAlgebra
  exact Module.finrank_dvd_finrank_right K F E
/-
**IntermediateField.finrank_le_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：finrank_le_of_le_left [FiniteDimensional F L] (h : F <= E) : finrank E L <
= finrank F L
参数：h : F <= E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IntermediateField.finrank_dvd_of_le_left`：finrank_dvd_of_le_left (h : F 
<= E) : finrank E L ∣ finrank F L
-/
theorem finrank_le_of_le_left [FiniteDimensional F L] (h : F ≤ E) : finrank E L ≤ finrank F L :=
  Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_left h)
/-
**IntermediateField.finrank_le_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：finrank_le_of_le_right [FiniteDimensional K E] (h : F <= E) : finrank K F 
<= finrank K E
参数：h : F <= E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.finrank_dvd_of_le_right`：finrank_dvd_of_le_right (h : 
F <= E) : finrank K F ∣ finrank K E
-/
theorem finrank_le_of_le_right [FiniteDimensional K E] (h : F ≤ E) : finrank K F ≤ finrank K E :=
  Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_right h)

/-- Mapping a finite-dimensional intermediate field along an algebra equivalence gives
a finite-dimensional intermediate field. -/
/-
**IntermediateField.finiteDimensional_map** 是 Mathlib 中的一个实例，位于命名空间 `Intermediat
eField`。
形式化陈述：finiteDimensional_map (f : L ->ₐ[K] L) [FiniteDimensional K E] : FiniteDim
ensional K (E.map f)
参数：f : L ->ₐ[K] L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…

--- 原说明 ---
Mapping a finite-dimensional intermediate field along an algebra equivalence giv
es
a finite-dimensional intermediate field.
-/
instance finiteDimensional_map (f : L →ₐ[K] L) [FiniteDimensional K E] :
    FiniteDimensional K (E.map f) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap E f).toLinearEquiv

end FiniteDimensional

/-
**IntermediateField.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isAlgebraic_algebraMap_iff`：isAlgebraic_algebraMap_iff {a : S} (h : Func
tion.Injective (algebraMap S A)) : IsAlgebraic R (algebraMap S A a) ↔ IsAlgebrai
c R a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
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
theorem isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L) :=
  (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm
/-
**IntermediateField.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L) :=
  (isIntegral_algHom_iff S.val S.val.injective).symm
/-
**IntermediateField.minpoly_eq** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：minpoly_eq (x : S) : minpoly K x = minpoly K (x : L)
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
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
theorem minpoly_eq (x : S) : minpoly K x = minpoly K (x : L) :=
  (minpoly.algebraMap_eq (algebraMap S L).injective x).symm

end IntermediateField

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields. -/
/-
**subalgebraEquivIntermediateField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] : Subalgebra K 
L ≃o IntermediateField K L where toFun S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `toIntermediateField_toSubalgebra`：toIntermediateField_toSubalgebra (S : 
IntermediateField K L) : (S.toSubalgebra.toIntermediateField fun _ => S.inv_mem)
 = S

--- 原说明 ---
If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.
-/
def subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] :
    Subalgebra K L ≃o IntermediateField K L where
  toFun S := S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl

@[simp]
/-
**mem_subalgebraEquivIntermediateField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] {S : Subalg
ebra K L} {x : L} : x in subalgebraEquivIntermediateField S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
    {x : L} : x ∈ subalgebraEquivIntermediateField S ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**mem_subalgebraEquivIntermediateField_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_subalgebraEquivIntermediateField_symm [Algebra.IsAlgebraic K L] {S : I
ntermediateField K L} {x : L} : x in subalgebraEquivIntermediateField.symm S ↔ x
 in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subalgebraEquivIntermediateField_symm [Algebra.IsAlgebraic K L]
    {S : IntermediateField K L} {x : L} :
    x ∈ subalgebraEquivIntermediateField.symm S ↔ x ∈ S :=
  Iff.rfl
